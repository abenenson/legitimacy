use crate::{commands::CorpusCommand, reporting::pretty_json};
use legitimacy::{
    AstTheoremWitness, ExtractionOptions, GovernanceExtractionReport, GovernanceGraph,
    LegitimacyError, Verdict,
    extract::{
        analyze_extraction_with_review, ast_hash::governance_graph_hash, verify_ast_theorem_witness,
    },
};
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::{Command, ExitCode},
};

const DEFAULT_EXTRACTOR_VERSION: &str = "legitimacy 0.1.0 heuristic";
const THEOREM_BACKED_MODELED_TIER: &str = "theorem-backed-modeled";
const THEOREM_BACKED_SOURCE_WALK_TIER: &str = "theorem-backed-source-walk";
const DEPRECATED_THEOREM_BACKED_TIER: &str = "theorem-backed";
const REVIEWED_TIER: &str = "reviewed";
const HEURISTIC_TIER: &str = "heuristic";
const UNVERIFIED_CLAIM_TIER: &str = "unverified-claim";
const REVIEWED_MIN_KAPPA: f64 = 0.80;
const REVIEWED_MIN_PRECISION_RECALL: f64 = 0.90;

#[derive(Clone, Debug, Serialize, Deserialize)]
struct CorpusManifest {
    corpus: CorpusMetadata,
    #[serde(default)]
    harness: Vec<HarnessManifestEntry>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct CorpusMetadata {
    version: String,
    generated_at: String,
    extractor_version: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct HarnessManifestEntry {
    id: String,
    source_repo: String,
    source_commit: String,
    license: String,
    extraction_mode: String,
    evidence_tier: String,
    coverage_pct: f64,
    unsupported_constructs: Vec<String>,
    verdict_summary: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct SourceLock {
    source: SourceLockEntry,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct SourceLockEntry {
    id: String,
    source_repo: String,
    source_commit: String,
    license: String,
    #[serde(default)]
    extraction_mode: String,
    #[serde(default)]
    extraction_input: Option<String>,
    #[serde(default)]
    allow_partial: bool,
    #[serde(default)]
    license_url: Option<String>,
    #[serde(default)]
    notes: Vec<String>,
}

#[derive(Debug, Serialize)]
struct CorpusEvaluationSummary {
    manifest: String,
    evaluated: usize,
    skipped: usize,
    failed: Vec<CorpusEvaluationFailure>,
}

#[derive(Debug, Serialize)]
struct CorpusEvaluationFailure {
    id: String,
    reason: String,
}

#[derive(Debug, Serialize)]
struct CorpusExtractorReport<'a> {
    harness_id: &'a str,
    source_repo: &'a str,
    source_commit: &'a str,
    extraction_mode: &'a str,
    evidence_tier: &'a str,
    coverage_pct: f64,
    unsupported_constructs: Vec<String>,
    verdict_summary: String,
    report: GovernanceExtractionReport,
}

pub(crate) fn run(command: CorpusCommand) -> Result<ExitCode, LegitimacyError> {
    match command {
        CorpusCommand::Init { corpus_dir } => {
            init_corpus(&corpus_dir)?;
            Ok(ExitCode::SUCCESS)
        }
        CorpusCommand::Add {
            id,
            source_repo,
            source_commit,
            license,
            extraction_input,
            allow_partial,
            corpus_dir,
        } => {
            add_harness(
                &corpus_dir,
                HarnessAddInput {
                    id,
                    source_repo,
                    source_commit,
                    license,
                    extraction_input,
                    allow_partial,
                },
            )?;
            Ok(ExitCode::SUCCESS)
        }
        CorpusCommand::Evaluate { corpus_dir } => evaluate_corpus(&corpus_dir),
        CorpusCommand::Diff { corpus_dir } => diff_corpus(&corpus_dir),
    }
}

struct HarnessAddInput {
    id: String,
    source_repo: Option<String>,
    source_commit: Option<String>,
    license: Option<String>,
    extraction_input: Option<PathBuf>,
    allow_partial: bool,
}

fn init_corpus(corpus_dir: &Path) -> Result<(), LegitimacyError> {
    fs::create_dir_all(corpus_dir).map_err(|source| LegitimacyError::Io {
        context: format!("creating corpus directory '{}'", corpus_dir.display()),
        source,
    })?;
    let manifest = empty_manifest();
    write_manifest(corpus_dir, &manifest)?;
    println!("initialized {}", manifest_path(corpus_dir).display());
    Ok(())
}

fn add_harness(corpus_dir: &Path, input: HarnessAddInput) -> Result<(), LegitimacyError> {
    fs::create_dir_all(corpus_dir).map_err(|source| LegitimacyError::Io {
        context: format!("creating corpus directory '{}'", corpus_dir.display()),
        source,
    })?;
    let mut manifest = load_manifest_or_empty(corpus_dir)?;
    let harness_dir = corpus_dir.join(&input.id);
    fs::create_dir_all(&harness_dir).map_err(|source| LegitimacyError::Io {
        context: format!("creating harness directory '{}'", harness_dir.display()),
        source,
    })?;

    let source_repo = input.source_repo.unwrap_or_else(|| "UNSET".to_string());
    let source_commit = input.source_commit.unwrap_or_else(|| "UNSET".to_string());
    let license = input.license.unwrap_or_else(|| "UNSET".to_string());
    let extraction_input = input
        .extraction_input
        .map(|path| path.display().to_string());
    let source_lock = SourceLock {
        source: SourceLockEntry {
            id: input.id.clone(),
            source_repo: source_repo.clone(),
            source_commit: source_commit.clone(),
            license: license.clone(),
            extraction_mode: "heuristic".to_string(),
            extraction_input,
            allow_partial: input.allow_partial,
            license_url: None,
            notes: vec!["Created by legitimacy corpus add.".to_string()],
        },
    };
    write_source_lock(&harness_dir, &source_lock)?;
    write_if_missing(
        &harness_dir.join("license.md"),
        format!(
            "# License\n\nLicense: `{license}`\n\nSource: {source_repo}\nCommit: `{source_commit}`\n"
        ),
    )?;
    write_if_missing(
        &harness_dir.join("ground_truth.graph.toml"),
        "# Ground truth placeholder\n\n[ground_truth]\nstatus = \"unreviewed\"\n".to_string(),
    )?;
    write_if_missing(
        &harness_dir.join("observed_runtime_claims.jsonl"),
        String::new(),
    )?;
    write_if_missing(
        &harness_dir.join("extractor_report.json"),
        "{\n  \"status\": \"pending\",\n  \"verdict_summary\": \"Not evaluated yet.\"\n}\n"
            .to_string(),
    )?;

    manifest.harness.retain(|entry| entry.id != input.id);
    manifest.harness.push(HarnessManifestEntry {
        id: input.id,
        source_repo,
        source_commit,
        license,
        extraction_mode: "heuristic".to_string(),
        evidence_tier: "heuristic".to_string(),
        coverage_pct: 0.0,
        unsupported_constructs: Vec::new(),
        verdict_summary: "Pending extractor evaluation.".to_string(),
    });
    manifest
        .harness
        .sort_by(|left, right| left.id.cmp(&right.id));
    write_manifest(corpus_dir, &manifest)?;
    println!("added harness");
    Ok(())
}

fn evaluate_corpus(corpus_dir: &Path) -> Result<ExitCode, LegitimacyError> {
    let mut manifest = load_manifest(corpus_dir)?;
    let mut evaluated = 0;
    let mut skipped = 0;
    let mut failed = Vec::new();
    let mut updated_entries = Vec::new();

    for mut entry in std::mem::take(&mut manifest.harness) {
        let harness_dir = corpus_dir.join(&entry.id);
        let lock = load_source_lock(&harness_dir)?;
        let Some(source_path) = lock.source.extraction_input.as_ref() else {
            skipped += 1;
            entry.verdict_summary = "Skipped: source.lock has no extraction_input.".to_string();
            updated_entries.push(entry);
            continue;
        };
        let source_path = PathBuf::from(source_path);
        if !source_path.exists() {
            skipped += 1;
            entry.verdict_summary = format!(
                "Skipped: extraction_input '{}' does not exist.",
                source_path.display()
            );
            updated_entries.push(entry);
            continue;
        }

        let options = ExtractionOptions {
            allow_partial: lock.source.allow_partial,
            ..Default::default()
        };
        match analyze_extraction_with_review(&source_path, options, None) {
            Ok(report) => {
                evaluated += 1;
                let coverage_pct = coverage_pct(&report);
                let unsupported_constructs = unsupported_constructs(&report);
                let verdict_summary = verdict_summary(&report);
                let effective_evidence_tier =
                    effective_evidence_tier(&entry, &harness_dir, Some(&report.artifacts.graph));
                write_extractor_report(
                    &harness_dir,
                    CorpusExtractorReport {
                        harness_id: &entry.id,
                        source_repo: &entry.source_repo,
                        source_commit: &entry.source_commit,
                        extraction_mode: &entry.extraction_mode,
                        evidence_tier: &effective_evidence_tier,
                        coverage_pct,
                        unsupported_constructs: unsupported_constructs.clone(),
                        verdict_summary: verdict_summary.clone(),
                        report,
                    },
                )?;
                entry.coverage_pct = coverage_pct;
                entry.unsupported_constructs = unsupported_constructs;
                entry.verdict_summary = verdict_summary;
            }
            Err(error) => {
                failed.push(CorpusEvaluationFailure {
                    id: entry.id.clone(),
                    reason: error.to_string(),
                });
                entry.verdict_summary = format!("Extractor failed: {error}");
            }
        }
        updated_entries.push(entry);
    }

    updated_entries.sort_by(|left, right| left.id.cmp(&right.id));
    manifest.harness = updated_entries;
    manifest.corpus.generated_at = now_utc_string();
    write_manifest(corpus_dir, &manifest)?;

    let summary = CorpusEvaluationSummary {
        manifest: manifest_path(corpus_dir).display().to_string(),
        evaluated,
        skipped,
        failed,
    };
    let has_failures = !summary.failed.is_empty();
    println!("{}", pretty_json(&summary)?);
    if has_failures {
        Ok(ExitCode::FAILURE)
    } else {
        Ok(ExitCode::SUCCESS)
    }
}

fn effective_evidence_tier(
    entry: &HarnessManifestEntry,
    harness_dir: &Path,
    source_walk_graph: Option<&GovernanceGraph>,
) -> String {
    let validation = match entry.evidence_tier.as_str() {
        THEOREM_BACKED_MODELED_TIER => validate_theorem_backed_evidence(harness_dir).map(drop),
        THEOREM_BACKED_SOURCE_WALK_TIER | DEPRECATED_THEOREM_BACKED_TIER => {
            validate_theorem_backed_source_walk_evidence(harness_dir, source_walk_graph)
        }
        REVIEWED_TIER => validate_reviewed_evidence(harness_dir),
        HEURISTIC_TIER => Ok(()),
        _ => Err(LegitimacyError::invalid_input(format!(
            "unsupported corpus evidence tier '{}'",
            entry.evidence_tier
        ))),
    };

    match validation {
        Ok(()) => entry.evidence_tier.clone(),
        Err(_) => UNVERIFIED_CLAIM_TIER.to_string(),
    }
}

fn validate_theorem_backed_evidence(
    harness_dir: &Path,
) -> Result<GovernanceGraph, LegitimacyError> {
    let theorem_dir = harness_dir.join("theorem");
    require_file(&theorem_dir.join("PythonHookCoreProgram.lean"))?;
    let witness_path = theorem_dir.join("theorem_witness.json");
    let graph_path = theorem_dir.join("graph.json");
    require_file(&witness_path)?;
    require_file(&graph_path)?;

    let witness_input =
        fs::read_to_string(&witness_path).map_err(|source| LegitimacyError::Io {
            context: format!("reading theorem witness '{}'", witness_path.display()),
            source,
        })?;
    let witness: AstTheoremWitness =
        serde_json::from_str(&witness_input).map_err(|source| LegitimacyError::Json {
            context: format!("theorem witness '{}'", witness_path.display()),
            source,
        })?;

    let graph_input = fs::read_to_string(&graph_path).map_err(|source| LegitimacyError::Io {
        context: format!("reading theorem graph '{}'", graph_path.display()),
        source,
    })?;
    let graph: GovernanceGraph =
        serde_json::from_str(&graph_input).map_err(|source| LegitimacyError::Json {
            context: format!("theorem graph '{}'", graph_path.display()),
            source,
        })?;

    let verification = verify_ast_theorem_witness(&witness, &theorem_dir, &graph)?;
    if verification.witness_valid {
        Ok(graph)
    } else {
        Err(LegitimacyError::invalid_input(format!(
            "theorem witness hash mismatch: source expected {} actual {}; graph expected {} actual {}",
            verification.expected_source_ast_hash,
            verification.actual_source_ast_hash,
            verification.expected_governance_graph_hash,
            verification.actual_governance_graph_hash
        )))
    }
}

fn validate_theorem_backed_source_walk_evidence(
    harness_dir: &Path,
    source_walk_graph: Option<&GovernanceGraph>,
) -> Result<(), LegitimacyError> {
    let theorem_graph = validate_theorem_backed_evidence(harness_dir)?;
    let Some(source_walk_graph) = source_walk_graph else {
        return Err(LegitimacyError::invalid_input(
            "theorem-backed-source-walk validation requires the source-walk graph",
        ));
    };

    let theorem_hash = governance_graph_hash(&theorem_graph)?;
    let source_walk_hash = governance_graph_hash(source_walk_graph)?;
    if theorem_hash == source_walk_hash {
        return Ok(());
    }

    let theorem_nodes = graph_node_set(&theorem_graph);
    let source_walk_nodes = graph_node_set(source_walk_graph);
    let theorem_edges = graph_edge_set(&theorem_graph);
    let source_walk_edges = graph_edge_set(source_walk_graph);
    let theorem_decisions = graph_decision_set(&theorem_graph);
    let source_walk_decisions = graph_decision_set(source_walk_graph);
    Err(LegitimacyError::invalid_input(format!(
        "theorem-backed-source-walk graph mismatch: theorem hash {theorem_hash}; source-walk hash {source_walk_hash}; node sets match {}; edge sets match {}; decision sets match {}",
        theorem_nodes == source_walk_nodes,
        theorem_edges == source_walk_edges,
        theorem_decisions == source_walk_decisions
    )))
}

fn graph_node_set(graph: &GovernanceGraph) -> BTreeSet<String> {
    graph.nodes.keys().map(ToString::to_string).collect()
}

fn graph_edge_set(graph: &GovernanceGraph) -> BTreeSet<String> {
    graph.edges.iter().map(|edge| format!("{edge:?}")).collect()
}

fn graph_decision_set(graph: &GovernanceGraph) -> BTreeSet<String> {
    graph
        .nodes
        .values()
        .flat_map(|node| match node {
            legitimacy::GovernanceNode::Binary {
                id, gates, default, ..
            } => {
                let mut decisions = vec![format!("{id}::default::{default:?}")];
                decisions.extend(
                    gates
                        .iter()
                        .enumerate()
                        .filter_map(|(index, gate)| {
                            gate_decision(gate).map(|decision| (index, decision))
                        })
                        .map(|(index, decision)| format!("{id}::gate[{index}]::{decision:?}")),
                );
                decisions
            }
            legitimacy::GovernanceNode::Proportional { .. }
            | legitimacy::GovernanceNode::Threshold { .. } => Vec::new(),
        })
        .collect()
}

fn gate_decision(gate: &legitimacy::Gate) -> Option<&legitimacy::Decision> {
    match gate {
        legitimacy::Gate::PrefixMatch { decision, .. }
        | legitimacy::Gate::ExactMatch { decision, .. }
        | legitimacy::Gate::ContentMatch { decision, .. }
        | legitimacy::Gate::ThresholdGate { decision, .. }
        | legitimacy::Gate::PeerRelative { decision, .. } => Some(decision),
    }
}

fn validate_reviewed_evidence(harness_dir: &Path) -> Result<(), LegitimacyError> {
    let ground_truth_dir = harness_dir.join("ground_truth");
    require_file(&ground_truth_dir.join("reviewer_a.graph.toml"))?;
    require_file(&ground_truth_dir.join("reviewer_b.graph.toml"))?;
    let adjudication_path = ground_truth_dir.join("adjudication.toml");
    require_file(&adjudication_path)?;

    let input = fs::read_to_string(&adjudication_path).map_err(|source| LegitimacyError::Io {
        context: format!("reading adjudication '{}'", adjudication_path.display()),
        source,
    })?;
    let value: toml::Value =
        toml::from_str(&input).map_err(|source| LegitimacyError::PolicyToml {
            context: adjudication_path.display().to_string(),
            source,
        })?;
    let Some(adjudication) = value.get("adjudication") else {
        return Err(LegitimacyError::invalid_input(format!(
            "adjudication '{}' is missing [adjudication]",
            adjudication_path.display()
        )));
    };
    for metric in ["cohen_kappa_nodes", "cohen_kappa_edges"] {
        require_reviewed_metric_at_least(
            adjudication,
            &adjudication_path,
            metric,
            REVIEWED_MIN_KAPPA,
        )?;
    }
    for metric in [
        "node_precision",
        "node_recall",
        "edge_precision",
        "edge_recall",
    ] {
        require_reviewed_metric_greater_than(
            adjudication,
            &adjudication_path,
            metric,
            REVIEWED_MIN_PRECISION_RECALL,
        )?;
    }
    Ok(())
}

fn require_reviewed_metric_at_least(
    adjudication: &toml::Value,
    adjudication_path: &Path,
    metric: &str,
    minimum: f64,
) -> Result<(), LegitimacyError> {
    let value = reviewed_metric(adjudication, adjudication_path, metric)?;
    if value < minimum {
        return Err(LegitimacyError::invalid_input(format!(
            "adjudication '{}' has {metric} {value}, below required minimum {minimum}",
            adjudication_path.display()
        )));
    }
    Ok(())
}

fn require_reviewed_metric_greater_than(
    adjudication: &toml::Value,
    adjudication_path: &Path,
    metric: &str,
    minimum: f64,
) -> Result<(), LegitimacyError> {
    let value = reviewed_metric(adjudication, adjudication_path, metric)?;
    if value <= minimum {
        return Err(LegitimacyError::invalid_input(format!(
            "adjudication '{}' has {metric} {value}, not greater than required minimum {minimum}",
            adjudication_path.display()
        )));
    }
    Ok(())
}

fn reviewed_metric(
    adjudication: &toml::Value,
    adjudication_path: &Path,
    metric: &str,
) -> Result<f64, LegitimacyError> {
    let Some(value) = adjudication.get(metric).and_then(toml_number) else {
        return Err(LegitimacyError::invalid_input(format!(
            "adjudication '{}' is missing finite {metric}",
            adjudication_path.display()
        )));
    };
    if !value.is_finite() {
        return Err(LegitimacyError::invalid_input(format!(
            "adjudication '{}' has non-finite {metric}",
            adjudication_path.display()
        )));
    }
    Ok(value)
}

fn toml_number(value: &toml::Value) -> Option<f64> {
    value
        .as_float()
        .or_else(|| value.as_integer().map(|value| value as f64))
}

fn require_file(path: &Path) -> Result<(), LegitimacyError> {
    if path.is_file() {
        Ok(())
    } else {
        Err(LegitimacyError::invalid_input(format!(
            "required corpus evidence file '{}' is missing",
            path.display()
        )))
    }
}

fn diff_corpus(corpus_dir: &Path) -> Result<ExitCode, LegitimacyError> {
    let output = Command::new("git")
        .args(["diff", "--", &corpus_dir.display().to_string()])
        .output()
        .map_err(|source| LegitimacyError::Io {
            context: "running git diff for corpus".to_string(),
            source,
        })?;
    print!("{}", String::from_utf8_lossy(&output.stdout));
    eprint!("{}", String::from_utf8_lossy(&output.stderr));
    if output.status.success() {
        Ok(ExitCode::SUCCESS)
    } else {
        Ok(ExitCode::FAILURE)
    }
}

fn empty_manifest() -> CorpusManifest {
    CorpusManifest {
        corpus: CorpusMetadata {
            version: "v1".to_string(),
            generated_at: now_utc_string(),
            extractor_version: DEFAULT_EXTRACTOR_VERSION.to_string(),
        },
        harness: Vec::new(),
    }
}

fn load_manifest_or_empty(corpus_dir: &Path) -> Result<CorpusManifest, LegitimacyError> {
    if manifest_path(corpus_dir).exists() {
        load_manifest(corpus_dir)
    } else {
        Ok(empty_manifest())
    }
}

fn load_manifest(corpus_dir: &Path) -> Result<CorpusManifest, LegitimacyError> {
    let path = manifest_path(corpus_dir);
    let input = fs::read_to_string(&path).map_err(|source| LegitimacyError::Io {
        context: format!("reading corpus manifest '{}'", path.display()),
        source,
    })?;
    toml::from_str(&input).map_err(|source| LegitimacyError::PolicyToml {
        context: path.display().to_string(),
        source,
    })
}

fn write_manifest(corpus_dir: &Path, manifest: &CorpusManifest) -> Result<(), LegitimacyError> {
    let path = manifest_path(corpus_dir);
    let encoded = toml::to_string_pretty(manifest).map_err(|source| {
        LegitimacyError::invalid_input(format!("serializing corpus manifest: {source}"))
    })?;
    fs::write(&path, encoded).map_err(|source| LegitimacyError::Io {
        context: format!("writing corpus manifest '{}'", path.display()),
        source,
    })
}

fn load_source_lock(harness_dir: &Path) -> Result<SourceLock, LegitimacyError> {
    let path = harness_dir.join("source.lock");
    let input = fs::read_to_string(&path).map_err(|source| LegitimacyError::Io {
        context: format!("reading source lock '{}'", path.display()),
        source,
    })?;
    toml::from_str(&input).map_err(|source| LegitimacyError::PolicyToml {
        context: path.display().to_string(),
        source,
    })
}

fn write_source_lock(harness_dir: &Path, source_lock: &SourceLock) -> Result<(), LegitimacyError> {
    let path = harness_dir.join("source.lock");
    let encoded = toml::to_string_pretty(source_lock).map_err(|source| {
        LegitimacyError::invalid_input(format!("serializing source lock: {source}"))
    })?;
    fs::write(&path, encoded).map_err(|source| LegitimacyError::Io {
        context: format!("writing source lock '{}'", path.display()),
        source,
    })
}

fn write_extractor_report(
    harness_dir: &Path,
    report: CorpusExtractorReport<'_>,
) -> Result<(), LegitimacyError> {
    let path = harness_dir.join("extractor_report.json");
    let mut encoded =
        serde_json::to_vec_pretty(&report).map_err(|source| LegitimacyError::Serialize {
            context: format!("corpus extractor report '{}'", path.display()),
            source,
        })?;
    encoded.push(b'\n');
    fs::write(&path, encoded).map_err(|source| LegitimacyError::Io {
        context: format!("writing extractor report '{}'", path.display()),
        source,
    })
}

fn write_if_missing(path: &Path, content: String) -> Result<(), LegitimacyError> {
    if path.exists() {
        return Ok(());
    }
    fs::write(path, content).map_err(|source| LegitimacyError::Io {
        context: format!("writing '{}'", path.display()),
        source,
    })
}

fn coverage_pct(report: &GovernanceExtractionReport) -> f64 {
    let discovered = report.artifacts.coverage.files_discovered;
    if discovered == 0 {
        0.0
    } else {
        (report.artifacts.coverage.files_parsed as f64 / discovered as f64) * 100.0
    }
}

fn unsupported_constructs(report: &GovernanceExtractionReport) -> Vec<String> {
    report
        .artifacts
        .resolution_issues
        .iter()
        .map(|issue| format!("{:?}: {}", issue.kind, issue.target_symbol))
        .collect()
}

fn verdict_summary(report: &GovernanceExtractionReport) -> String {
    let graph = &report.artifacts.graph;
    let failed_axioms = report
        .audit
        .axiom_results
        .iter()
        .filter(|result| matches!(result.verdict, Some(Verdict::Rejected { .. })))
        .map(|result| result.axiom.as_str())
        .collect::<Vec<_>>();
    if failed_axioms.is_empty() {
        format!(
            "Synthetic structural probe passed over {} nodes and {} edges.",
            graph.nodes.len(),
            graph.edges.len()
        )
    } else {
        format!(
            "Synthetic structural probe found failures [{}] over {} nodes and {} edges.",
            failed_axioms.join(", "),
            graph.nodes.len(),
            graph.edges.len()
        )
    }
}

fn manifest_path(corpus_dir: &Path) -> PathBuf {
    corpus_dir.join("manifest.toml")
}

fn now_utc_string() -> String {
    Command::new("date")
        .args(["-u", "+%Y-%m-%dT%H:%M:%SZ"])
        .output()
        .ok()
        .and_then(|output| {
            output
                .status
                .success()
                .then(|| String::from_utf8_lossy(&output.stdout).trim().to_string())
        })
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| "1970-01-01T00:00:00Z".to_string())
}

#[cfg(test)]
#[path = "../tests/support/corpus_validator.rs"]
mod tests;
