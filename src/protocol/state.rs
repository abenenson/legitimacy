use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use thiserror::Error;

use crate::{
    GovernanceClaim, GovernanceFactorExposure, GovernanceGraph, GovernanceProperty,
    LegitimacyError, MonitoringSpec, Verdict, extract::synthetic_claims,
    mechanism::StrategyproofnessVerdict,
};

use super::formats::{
    GovernanceDeclaration, GovernanceDriftAlert, GovernanceRiskReport, PromotionCertificate,
};

#[derive(Debug, Error)]
pub enum ProtocolError {
    #[error(transparent)]
    Verdict(#[from] LegitimacyError),
    #[error("supervisory directive JSON is malformed: {reason}")]
    MalformedSupervisoryDirectiveJson { reason: String },
    #[error(
        "supervisory directive field '{field}' contains malformed node id '{node_id}': {reason}"
    )]
    MalformedSupervisoryDirectiveNodeId {
        field: &'static str,
        node_id: String,
        reason: String,
    },
    #[error("supervisory directive field '{field}' references unknown graph node '{node_id}'")]
    UnknownSupervisoryDirectiveNodeId {
        field: &'static str,
        node_id: String,
    },
    #[error("protocol state transition requires '{expected}', found '{actual}'")]
    InvalidStateTransition {
        expected: &'static str,
        actual: &'static str,
    },
    #[error("graph has undeclared violations for {properties:?}")]
    UnsacrificedViolations { properties: Vec<GovernanceProperty> },
    #[error(
        "phantom sacrifice rejected for '{property}': the graph does not violate that property"
    )]
    PhantomSacrifice { property: &'static str },
    #[error("claim '{claimant_id}' did not reach a final governance decision")]
    MissingDecision { claimant_id: String },
    #[error("kernel check '{axiom}' was skipped during protocol compilation: {reason}")]
    SkippedKernelCheck { axiom: String, reason: String },
    #[error("protocol state is malformed: {reason}")]
    MalformedState { reason: String },
}

/// Property-level sacrifice declaration attached to a governance graph before
/// compilation. Compiled sacrifice certificates add measured bounds and
/// provenance after the graph is evaluated.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct SacrificeDeclaration {
    pub property: GovernanceProperty,
    pub justification: String,
    #[serde(default)]
    pub monitoring_specs: Vec<MonitoringSpec>,
}

pub type GraphSacrifice = SacrificeDeclaration;
pub type DeclaredSacrifice = SacrificeDeclaration;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct SacrificeCertificate {
    pub property: GovernanceProperty,
    pub impact_bound: f64,
    pub source_axiom: String,
    pub witness: String,
    pub monitoring_specs: Vec<MonitoringSpec>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct CompiledGraph {
    pub name: String,
    pub version: String,
    pub graph: GovernanceGraph,
    pub axiom_verdicts: Vec<Verdict>,
    pub strategyproofness: StrategyproofnessVerdict,
    pub compiled_rule_hash: String,
    pub compiled_at: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct MonitorConfig {
    pub min_interval_seconds: u64,
    pub max_interval_seconds: u64,
    #[serde(default)]
    pub seed: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct MonitorSession {
    pub compiled_graph: CompiledGraph,
    pub sacrifice_certs: Vec<SacrificeCertificate>,
    #[serde(default = "default_monitored_properties")]
    pub monitored_properties: Vec<GovernanceProperty>,
    pub representative_claims: Vec<GovernanceClaim>,
    pub interval_seconds: u64,
    pub monitor_config: MonitorConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Default)]
pub struct ProtocolLedger {
    #[serde(default)]
    pub certificates: Vec<super::formats::PromotionCertificate>,
    #[serde(default)]
    pub drift_alerts: Vec<GovernanceDriftAlert>,
    pub head_hash: Option<String>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SupervisoryAction {
    Pause,
    Deny,
    Sandbox,
    Degrade,
    Rollback,
    Reroute,
    Stop,
}

impl SupervisoryAction {
    pub fn postcondition(self) -> SupervisoryPostcondition {
        match self {
            Self::Pause => SupervisoryPostcondition::ClaimEvaluationPaused,
            Self::Deny => SupervisoryPostcondition::UniversalDeny,
            Self::Sandbox => SupervisoryPostcondition::GovernanceGraphSandboxed,
            Self::Degrade => SupervisoryPostcondition::GovernanceDegraded,
            Self::Rollback => SupervisoryPostcondition::PriorGovernanceStateRestored,
            Self::Reroute => SupervisoryPostcondition::ClaimsRerouted,
            Self::Stop => SupervisoryPostcondition::PermanentlyShutdown,
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SupervisoryPostcondition {
    ClaimEvaluationPaused,
    UniversalDeny,
    GovernanceGraphSandboxed,
    GovernanceDegraded,
    PriorGovernanceStateRestored,
    ClaimsRerouted,
    PermanentlyShutdown,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct SupervisoryIntervention {
    pub action: SupervisoryAction,
    pub postcondition: SupervisoryPostcondition,
    pub issued_at: String,
    pub overlay_graph: GovernanceGraph,
    pub overlay_graph_hash: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(tag = "state", rename_all = "snake_case")]
pub enum ProtocolState {
    Undeclared,
    Declared {
        graph: GovernanceGraph,
        sacrifices: Vec<DeclaredSacrifice>,
        declaration: GovernanceDeclaration,
    },
    Compiled {
        compiled_graph: CompiledGraph,
        sacrifice_certs: Vec<SacrificeCertificate>,
        declaration: GovernanceDeclaration,
    },
    Measured {
        risk_report: GovernanceRiskReport,
        factor_exposure: GovernanceFactorExposure,
        compiled_graph: CompiledGraph,
        sacrifice_certs: Vec<SacrificeCertificate>,
        declaration: GovernanceDeclaration,
        representative_claims: Vec<GovernanceClaim>,
    },
    Live {
        monitor_session: MonitorSession,
        ledger: ProtocolLedger,
        declaration: GovernanceDeclaration,
    },
    Supervised {
        intervention: SupervisoryIntervention,
        monitor_session: MonitorSession,
        ledger: ProtocolLedger,
        declaration: GovernanceDeclaration,
    },
    Drifted {
        drift_report: GovernanceDriftAlert,
        monitor_session: MonitorSession,
        ledger: ProtocolLedger,
        declaration: GovernanceDeclaration,
    },
    Recompiling {
        proposed_graph: GovernanceGraph,
        sacrifices: Vec<DeclaredSacrifice>,
        declaration: GovernanceDeclaration,
    },
}

impl ProtocolState {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Undeclared => "undeclared",
            Self::Declared { .. } => "declared",
            Self::Compiled { .. } => "compiled",
            Self::Measured { .. } => "measured",
            Self::Live { .. } => "live",
            Self::Supervised { .. } => "supervised",
            Self::Drifted { .. } => "drifted",
            Self::Recompiling { .. } => "recompiling",
        }
    }

    pub fn validate(&self) -> Result<(), ProtocolError> {
        self.validate_with_options(false)
    }

    pub fn validate_for_audit(&self) -> Result<(), ProtocolError> {
        self.validate_with_options(true)
    }

    fn validate_with_options(&self, allow_tampered_ledger: bool) -> Result<(), ProtocolError> {
        match self {
            Self::Undeclared => Ok(()),
            Self::Declared {
                graph,
                sacrifices,
                declaration,
            } => {
                validate_declaration_basics(declaration)?;
                if declaration.graph != *graph {
                    return Err(malformed_state(
                        "declared state graph does not match declaration graph",
                    ));
                }
                if declaration.sacrifices != *sacrifices {
                    return Err(malformed_state(
                        "declared sacrifices do not match declaration payload",
                    ));
                }
                Ok(())
            }
            Self::Compiled {
                compiled_graph,
                sacrifice_certs,
                declaration,
            } => {
                validate_declaration_basics(declaration)?;
                validate_compiled_graph(compiled_graph, declaration, true)?;
                validate_sacrifice_alignment(sacrifice_certs, &declaration.sacrifices)
            }
            Self::Measured {
                risk_report,
                factor_exposure,
                compiled_graph,
                sacrifice_certs,
                declaration,
                ..
            } => {
                validate_declaration_basics(declaration)?;
                validate_compiled_graph(compiled_graph, declaration, true)?;
                validate_sacrifice_alignment(sacrifice_certs, &declaration.sacrifices)?;
                if *factor_exposure != risk_report.factor_exposure {
                    return Err(malformed_state(
                        "measured state factor exposure does not match risk report",
                    ));
                }
                validate_risk_report(risk_report)
            }
            Self::Live {
                monitor_session,
                ledger,
                declaration,
            } => {
                validate_declaration_basics(declaration)?;
                validate_monitor_session(monitor_session, declaration, true)?;
                validate_ledger(ledger, allow_tampered_ledger)
            }
            Self::Supervised {
                intervention,
                monitor_session,
                ledger,
                declaration,
            } => {
                validate_declaration_basics(declaration)?;
                validate_monitor_session(monitor_session, declaration, true)?;
                validate_ledger(ledger, allow_tampered_ledger)?;
                if intervention.postcondition != intervention.action.postcondition() {
                    return Err(malformed_state(format!(
                        "supervisory postcondition {:?} does not match action {:?}",
                        intervention.postcondition, intervention.action
                    )));
                }
                validate_supervisory_intervention(intervention)?;
                Ok(())
            }
            Self::Drifted {
                drift_report,
                monitor_session,
                ledger,
                declaration,
            } => {
                validate_declaration_basics(declaration)?;
                validate_monitor_session(monitor_session, declaration, true)?;
                validate_ledger(ledger, allow_tampered_ledger)?;
                validate_drift_alert(drift_report)?;
                if !ledger.drift_alerts.contains(drift_report) {
                    return Err(malformed_state(
                        "drifted state report is not present in the ledger drift history",
                    ));
                }
                Ok(())
            }
            Self::Recompiling {
                sacrifices,
                declaration,
                ..
            } => {
                validate_declaration_basics(declaration)?;
                let current = sacrifices
                    .iter()
                    .map(|item| item.property.as_str())
                    .collect::<BTreeSet<_>>();
                if sacrifices.len() != current.len() {
                    return Err(malformed_state(
                        "recompiling sacrifices must not contain duplicate properties",
                    ));
                }
                Ok(())
            }
        }
    }
}

pub(crate) fn canonical_compiled_rule_hash(
    graph: &GovernanceGraph,
    axiom_verdicts: &[Verdict],
    strategyproofness: &StrategyproofnessVerdict,
) -> Result<String, ProtocolError> {
    stable_hash(&(
        graph,
        synthetic_claims(graph),
        axiom_verdicts,
        strategyproofness,
    ))
}

pub(crate) fn canonical_graph_hash(graph: &GovernanceGraph) -> Result<String, ProtocolError> {
    stable_hash(&(graph, synthetic_claims(graph)))
}

pub(crate) fn default_monitored_properties() -> Vec<GovernanceProperty> {
    vec![
        GovernanceProperty::Consistency,
        GovernanceProperty::Solidarity,
        GovernanceProperty::Monotonicity,
        GovernanceProperty::Strategyproofness,
        GovernanceProperty::Certifiability,
        GovernanceProperty::ObservableDeterminacy,
        GovernanceProperty::Corrigibility,
        GovernanceProperty::CompositionalSafety,
        GovernanceProperty::NonVacuous,
    ]
}

pub(crate) fn non_sacrificed_monitoring_properties(
    sacrifice_certs: &[SacrificeCertificate],
) -> Vec<GovernanceProperty> {
    let sacrificed = sacrifice_certs
        .iter()
        .map(|cert| cert.property.as_str())
        .collect::<BTreeSet<_>>();
    default_monitored_properties()
        .into_iter()
        .filter(|property| !sacrificed.contains(property.as_str()))
        .collect()
}

fn validate_declaration_basics(declaration: &GovernanceDeclaration) -> Result<(), ProtocolError> {
    if declaration.graph_name.trim().is_empty() {
        return Err(malformed_state("declaration graph_name must be non-empty"));
    }
    if declaration.graph_version.trim().is_empty() {
        return Err(malformed_state(
            "declaration graph_version must be non-empty",
        ));
    }
    if !declaration.spectral_gap.is_finite() || declaration.spectral_gap < 0.0 {
        return Err(malformed_state(
            "declaration spectral_gap must be finite and non-negative",
        ));
    }
    if !declaration.cv_bound.is_finite() || declaration.cv_bound < 0.0 {
        return Err(malformed_state(
            "declaration cv_bound must be finite and non-negative",
        ));
    }
    Ok(())
}

fn validate_compiled_graph(
    compiled_graph: &CompiledGraph,
    declaration: &GovernanceDeclaration,
    require_declared_graph_match: bool,
) -> Result<(), ProtocolError> {
    if compiled_graph.name != declaration.graph_name {
        return Err(malformed_state(format!(
            "compiled graph name '{}' does not match declaration '{}'",
            compiled_graph.name, declaration.graph_name
        )));
    }
    if compiled_graph.version != declaration.graph_version {
        return Err(malformed_state(format!(
            "compiled graph version '{}' does not match declaration '{}'",
            compiled_graph.version, declaration.graph_version
        )));
    }
    if require_declared_graph_match && compiled_graph.graph != declaration.graph {
        return Err(malformed_state(
            "compiled graph payload does not match declaration graph",
        ));
    }
    let expected_hash = canonical_compiled_rule_hash(
        &compiled_graph.graph,
        &compiled_graph.axiom_verdicts,
        &compiled_graph.strategyproofness,
    )?;
    if compiled_graph.compiled_rule_hash != expected_hash {
        return Err(malformed_state(
            "compiled_rule_hash does not match the canonical compiled graph hash",
        ));
    }

    const REQUIRED_AXIOMS: [&str; 8] = [
        "graph consistency",
        "graph solidarity",
        "graph monotonicity",
        "graph certifiability",
        "graph observable determinacy",
        "graph corrigibility",
        "graph compositional safety",
        "graph nonvacuity",
    ];
    let seen = compiled_graph
        .axiom_verdicts
        .iter()
        .map(verdict_axiom)
        .collect::<Vec<_>>();
    if seen.len() != REQUIRED_AXIOMS.len() {
        return Err(malformed_state(
            "compiled graph must carry exactly eight non-strategyproof graph axiom verdicts",
        ));
    }
    for axiom in REQUIRED_AXIOMS {
        if seen.iter().filter(|candidate| **candidate == axiom).count() != 1 {
            return Err(malformed_state(format!(
                "compiled graph verdict set must contain exactly one '{axiom}' verdict",
            )));
        }
    }
    Ok(())
}

fn validate_sacrifice_alignment(
    sacrifice_certs: &[SacrificeCertificate],
    declared_sacrifices: &[DeclaredSacrifice],
) -> Result<(), ProtocolError> {
    let declared = declared_sacrifices
        .iter()
        .map(|item| item.property.as_str())
        .collect::<BTreeSet<_>>();
    let certified = sacrifice_certs
        .iter()
        .map(|item| item.property.as_str())
        .collect::<BTreeSet<_>>();
    if declared != certified {
        return Err(malformed_state(
            "sacrifice certificates do not match declared sacrifice properties",
        ));
    }
    if sacrifice_certs.len() != certified.len() {
        return Err(malformed_state(
            "sacrifice certificates must not contain duplicate properties",
        ));
    }
    for cert in sacrifice_certs {
        if !cert.impact_bound.is_finite() || cert.impact_bound < 0.0 {
            return Err(malformed_state(format!(
                "sacrifice certificate for '{}' has invalid impact bound",
                cert.property.as_str()
            )));
        }
    }
    Ok(())
}

fn validate_monitor_session(
    monitor_session: &MonitorSession,
    declaration: &GovernanceDeclaration,
    require_declared_graph_match: bool,
) -> Result<(), ProtocolError> {
    validate_compiled_graph(
        &monitor_session.compiled_graph,
        declaration,
        require_declared_graph_match,
    )?;
    validate_sacrifice_alignment(&monitor_session.sacrifice_certs, &declaration.sacrifices)?;
    validate_monitoring_coverage(
        &monitor_session.monitored_properties,
        &monitor_session.sacrifice_certs,
    )?;
    let min_interval = monitor_session.monitor_config.min_interval_seconds.max(1);
    let max_interval = monitor_session
        .monitor_config
        .max_interval_seconds
        .max(min_interval);
    if monitor_session.interval_seconds < min_interval
        || monitor_session.interval_seconds > max_interval
    {
        return Err(malformed_state(format!(
            "monitor interval {} is outside configured bounds [{min_interval}, {max_interval}]",
            monitor_session.interval_seconds
        )));
    }
    Ok(())
}

fn validate_monitoring_coverage(
    monitored_properties: &[GovernanceProperty],
    sacrifice_certs: &[SacrificeCertificate],
) -> Result<(), ProtocolError> {
    let monitored = monitored_properties
        .iter()
        .map(|property| property.as_str())
        .collect::<BTreeSet<_>>();
    if monitored.len() != monitored_properties.len() {
        return Err(malformed_state(
            "monitoring coverage must not contain duplicate properties",
        ));
    }
    let missing = non_sacrificed_monitoring_properties(sacrifice_certs)
        .into_iter()
        .filter(|property| !monitored.contains(property.as_str()))
        .map(|property| property.as_str())
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        return Err(malformed_state(format!(
            "monitoring coverage missing non-sacrificed properties {missing:?}",
        )));
    }
    Ok(())
}

fn validate_supervisory_intervention(
    intervention: &SupervisoryIntervention,
) -> Result<(), ProtocolError> {
    let expected_hash = canonical_graph_hash(&intervention.overlay_graph)?;
    if intervention.overlay_graph_hash != expected_hash {
        return Err(malformed_state(
            "supervisory overlay graph hash does not match the canonical graph hash",
        ));
    }
    Ok(())
}

fn validate_ledger(
    ledger: &ProtocolLedger,
    allow_tampered_ledger: bool,
) -> Result<(), ProtocolError> {
    let mut prev_hash = None;
    for certificate in &ledger.certificates {
        if certificate.prev_cert_hash != prev_hash {
            if allow_tampered_ledger {
                return Ok(());
            }
            return Err(malformed_state(
                "protocol ledger certificate chain is inconsistent",
            ));
        }
        prev_hash = Some(protocol_certificate_hash(certificate)?);
    }
    if ledger.head_hash != prev_hash {
        if allow_tampered_ledger {
            return Ok(());
        }
        return Err(malformed_state(
            "protocol ledger head_hash does not match the certificate chain tail",
        ));
    }
    for alert in &ledger.drift_alerts {
        validate_drift_alert(alert)?;
    }
    Ok(())
}

fn validate_drift_alert(alert: &GovernanceDriftAlert) -> Result<(), ProtocolError> {
    if !alert.declared_bound.is_finite() || alert.declared_bound < 0.0 {
        return Err(malformed_state(
            "drift alert declared_bound must be finite and non-negative",
        ));
    }
    if !alert.actual_magnitude.is_finite() || alert.actual_magnitude < 0.0 {
        return Err(malformed_state(
            "drift alert actual_magnitude must be finite and non-negative",
        ));
    }
    Ok(())
}

fn validate_risk_report(report: &GovernanceRiskReport) -> Result<(), ProtocolError> {
    if !report.spectral_gap.is_finite() || report.spectral_gap < 0.0 {
        return Err(malformed_state(
            "risk report spectral_gap must be finite and non-negative",
        ));
    }
    if !report.cv_bound.is_finite() || report.cv_bound < 0.0 {
        return Err(malformed_state(
            "risk report cv_bound must be finite and non-negative",
        ));
    }
    if !report.localizability_bound.is_finite() || report.localizability_bound < 0.0 {
        return Err(malformed_state(
            "risk report localizability_bound must be finite and non-negative",
        ));
    }
    Ok(())
}

fn malformed_state(reason: impl Into<String>) -> ProtocolError {
    ProtocolError::MalformedState {
        reason: reason.into(),
    }
}

fn verdict_axiom(verdict: &Verdict) -> &str {
    match verdict {
        Verdict::Admissible { axiom, .. } | Verdict::Rejected { axiom, .. } => axiom,
    }
}

fn protocol_certificate_hash(certificate: &PromotionCertificate) -> Result<String, ProtocolError> {
    stable_hash(certificate)
}

fn stable_hash<T: Serialize>(value: &T) -> Result<String, ProtocolError> {
    let encoded = serde_json::to_vec(value).map_err(|source| LegitimacyError::Serialize {
        context: "protocol hash payload".to_string(),
        source,
    })?;
    Ok(format!("{:x}", Sha256::digest(encoded)))
}
