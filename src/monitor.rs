use crate::{
    CompiledGraph, CompiledRule, DeclaredSacrifice, EPSILON, GovernanceProperty, LegitimacyError,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, VecDeque},
    fs::{self, File},
    io::{BufRead, BufReader, Seek, SeekFrom},
    path::{Path, PathBuf},
    thread,
    time::Duration,
};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct GovernanceMonitoringEvent {
    pub property: GovernanceProperty,
    pub actual_magnitude: f64,
    pub timestamp: String,
    #[serde(default)]
    pub evidence: BTreeMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct GovernanceDriftEvent {
    pub property: GovernanceProperty,
    pub declared_bound: f64,
    pub actual_magnitude: f64,
    pub timestamp: String,
    #[serde(default)]
    pub evidence: BTreeMap<String, String>,
}

#[derive(Debug)]
pub struct MonitorSession {
    pub compiled_graph: CompiledGraph,
    pub declared_sacrifices: Vec<DeclaredSacrifice>,
    pub interval_secs: u64,
    pub event_source: GovernanceEventSource,
}

#[derive(Debug)]
pub enum GovernanceEventSource {
    InMemory(VecDeque<GovernanceMonitoringEvent>),
    JsonlFile(JsonlEventSource),
}

#[derive(Debug)]
pub struct GovernanceDriftMonitor {
    session: MonitorSession,
}

#[derive(Debug)]
pub struct JsonlEventSource {
    path: PathBuf,
    offset: u64,
}

impl GovernanceEventSource {
    pub fn in_memory(
        events: impl IntoIterator<Item = GovernanceMonitoringEvent>,
    ) -> GovernanceEventSource {
        Self::InMemory(events.into_iter().collect())
    }

    pub fn jsonl_file(path: impl Into<PathBuf>) -> Result<GovernanceEventSource, LegitimacyError> {
        let source = JsonlEventSource::new(path.into())?;
        Ok(Self::JsonlFile(source))
    }

    fn next_event(
        &mut self,
        interval_secs: u64,
    ) -> Result<Option<GovernanceMonitoringEvent>, LegitimacyError> {
        match self {
            Self::InMemory(events) => Ok(events.pop_front()),
            Self::JsonlFile(source) => source.next_event(interval_secs).map(Some),
        }
    }
}

impl JsonlEventSource {
    pub fn new(path: PathBuf) -> Result<Self, LegitimacyError> {
        ensure_jsonl_path(&path)?;
        Ok(Self { path, offset: 0 })
    }

    fn next_event(
        &mut self,
        interval_secs: u64,
    ) -> Result<GovernanceMonitoringEvent, LegitimacyError> {
        loop {
            let mut reader = open_jsonl_reader(&self.path, self.offset)?;
            let mut line = String::new();
            let bytes_read = reader
                .read_line(&mut line)
                .map_err(|source| LegitimacyError::Io {
                    context: format!("monitor event source '{}'", self.path.display()),
                    source,
                })?;

            if bytes_read == 0 {
                thread::sleep(Duration::from_secs(interval_secs.max(1)));
                continue;
            }

            self.offset += bytes_read as u64;

            if line.trim().is_empty() {
                continue;
            }

            let event = serde_json::from_str(&line).map_err(|source| LegitimacyError::Json {
                context: format!("monitor event line from '{}'", self.path.display()),
                source,
            })?;
            return Ok(event);
        }
    }
}

impl GovernanceDriftMonitor {
    fn drift_for(
        &self,
        event: GovernanceMonitoringEvent,
    ) -> Result<Option<GovernanceDriftEvent>, LegitimacyError> {
        if !event.actual_magnitude.is_finite() || event.actual_magnitude < 0.0 {
            return Err(LegitimacyError::invalid_input(format!(
                "monitor event for '{}' reported invalid magnitude {}",
                event.property.as_str(),
                event.actual_magnitude
            )));
        }

        let declared_bound = self
            .session
            .declared_sacrifices
            .iter()
            .filter(|sacrifice| sacrifice.sacrificed_property == event.property)
            .map(|sacrifice| sacrifice.impact_bound)
            .min_by(f64::total_cmp);

        let Some(declared_bound) = declared_bound else {
            return Ok(None);
        };

        if event.actual_magnitude > declared_bound + EPSILON {
            return Ok(Some(GovernanceDriftEvent {
                property: event.property,
                declared_bound,
                actual_magnitude: event.actual_magnitude,
                timestamp: event.timestamp,
                evidence: event.evidence,
            }));
        }

        Ok(None)
    }
}

impl Iterator for GovernanceDriftMonitor {
    type Item = Result<GovernanceDriftEvent, LegitimacyError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let event = match self
                .session
                .event_source
                .next_event(self.session.interval_secs)
            {
                Ok(Some(event)) => event,
                Ok(None) => return None,
                Err(error) => return Some(Err(error)),
            };

            match self.drift_for(event) {
                Ok(Some(event)) => return Some(Ok(event)),
                Ok(None) => {}
                Err(error) => return Some(Err(error)),
            }
        }
    }
}

pub fn monitor(session: MonitorSession) -> GovernanceDriftMonitor {
    GovernanceDriftMonitor { session }
}

pub fn compiled_graph_from_rule(compiled: &CompiledRule) -> CompiledGraph {
    CompiledGraph {
        name: compiled.name.clone(),
        version: compiled.version.clone(),
        axiom_verdicts: compiled.axiom_verdicts.clone(),
        strategyproofness: compiled.strategyproofness.clone(),
        family_description: compiled.family_description.clone(),
        compiled_at: compiled.compiled_at.clone(),
    }
}

pub fn default_policy_event_source_path(policy: &Path) -> PathBuf {
    policy.with_extension("events.jsonl")
}

fn ensure_jsonl_path(path: &Path) -> Result<(), LegitimacyError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|source| LegitimacyError::Io {
            context: format!("creating monitor event directory '{}'", parent.display()),
            source,
        })?;
    }

    if !path.exists() {
        File::create(path).map_err(|source| LegitimacyError::Io {
            context: format!("creating monitor event source '{}'", path.display()),
            source,
        })?;
    }

    Ok(())
}

fn open_jsonl_reader(path: &Path, offset: u64) -> Result<BufReader<File>, LegitimacyError> {
    let mut file = File::open(path).map_err(|source| LegitimacyError::Io {
        context: format!("opening monitor event source '{}'", path.display()),
        source,
    })?;
    file.seek(SeekFrom::Start(offset))
        .map_err(|source| LegitimacyError::Io {
            context: format!("seeking monitor event source '{}'", path.display()),
            source,
        })?;
    Ok(BufReader::new(file))
}
