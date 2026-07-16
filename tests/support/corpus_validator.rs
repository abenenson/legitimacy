use super::*;
use legitimacy::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceEdge, GovernanceNode, NodeId,
    ast_theorem_witness,
};
use std::{
    collections::BTreeMap,
    time::{SystemTime, UNIX_EPOCH},
};

fn unique_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-corpus-{label}-{nanos}"))
}

fn harness_entry(id: &str, evidence_tier: &str) -> HarnessManifestEntry {
    HarnessManifestEntry {
        id: id.to_string(),
        source_repo: "https://example.invalid/repo".to_string(),
        source_commit: "abc123".to_string(),
        license: "MIT".to_string(),
        extraction_mode: HEURISTIC_TIER.to_string(),
        evidence_tier: evidence_tier.to_string(),
        coverage_pct: 0.0,
        unsupported_constructs: Vec::new(),
        verdict_summary: "Pending.".to_string(),
    }
}

fn write_policy_source(source_dir: &Path) {
    fs::create_dir_all(source_dir).unwrap();
    fs::write(
        source_dir.join("policy.ts"),
        r#"
export function approvalGate(action: string): boolean {
  if (action === "read") {
    return true;
  }
  return action !== "delete";
}
"#,
    )
    .unwrap();
}

fn write_single_harness_corpus(corpus_dir: &Path, id: &str, tier: &str, source_dir: &Path) {
    fs::create_dir_all(corpus_dir.join(id)).unwrap();
    write_manifest(
        corpus_dir,
        &CorpusManifest {
            corpus: CorpusMetadata {
                version: "v1".to_string(),
                generated_at: "2026-05-04T00:00:00Z".to_string(),
                extractor_version: DEFAULT_EXTRACTOR_VERSION.to_string(),
            },
            harness: vec![harness_entry(id, tier)],
        },
    )
    .unwrap();
    write_source_lock(
        &corpus_dir.join(id),
        &SourceLock {
            source: SourceLockEntry {
                id: id.to_string(),
                source_repo: "https://example.invalid/repo".to_string(),
                source_commit: "abc123".to_string(),
                license: "MIT".to_string(),
                extraction_mode: HEURISTIC_TIER.to_string(),
                extraction_input: Some(source_dir.display().to_string()),
                allow_partial: false,
                license_url: None,
                notes: Vec::new(),
            },
        },
    )
    .unwrap();
}

fn report_tier(harness_dir: &Path) -> String {
    let input = fs::read_to_string(harness_dir.join("extractor_report.json")).unwrap();
    let value: serde_json::Value = serde_json::from_str(&input).unwrap();
    value["evidence_tier"].as_str().unwrap().to_string()
}

fn manifest_tier(corpus_dir: &Path, id: &str) -> String {
    load_manifest(corpus_dir)
        .unwrap()
        .harness
        .into_iter()
        .find(|entry| entry.id == id)
        .unwrap()
        .evidence_tier
}

fn write_reviewed_evidence(harness_dir: &Path, metrics: Option<&[(&str, f64)]>) {
    let ground_truth = harness_dir.join("ground_truth");
    fs::create_dir_all(&ground_truth).unwrap();
    fs::write(ground_truth.join("reviewer_a.graph.toml"), "").unwrap();
    fs::write(ground_truth.join("reviewer_b.graph.toml"), "").unwrap();
    let metrics = metrics
        .unwrap_or_default()
        .iter()
        .map(|(name, value)| format!("\n{name} = {value}"))
        .collect::<String>();
    fs::write(
        ground_truth.join("adjudication.toml"),
        format!("[adjudication]\nstatus = \"resolved\"{metrics}"),
    )
    .unwrap();
}

fn write_theorem_evidence(harness_dir: &Path, valid: bool) {
    write_theorem_evidence_with_graph(
        harness_dir,
        &GovernanceGraph {
            nodes: BTreeMap::new(),
            edges: Vec::new(),
        },
        valid,
    );
}

fn write_theorem_evidence_with_graph(harness_dir: &Path, graph: &GovernanceGraph, valid: bool) {
    let theorem_dir = harness_dir.join("theorem");
    fs::create_dir_all(&theorem_dir).unwrap();
    fs::write(
        theorem_dir.join("PythonHookCoreProgram.lean"),
        "def witness := 1\n",
    )
    .unwrap();
    fs::write(
        theorem_dir.join("python_hook_core_model.py"),
        r#"
from typing import Literal, NotRequired, TypedDict

class PreToolUseHookSpecificOutput(TypedDict):
    hookEventName: Literal["PreToolUse"]
    permissionDecision: NotRequired[Literal["allow", "deny"]]
"#,
    )
    .unwrap();
    fs::write(
        theorem_dir.join("graph.json"),
        serde_json::to_vec_pretty(graph).unwrap(),
    )
    .unwrap();
    let mut witness =
        ast_theorem_witness(&theorem_dir, graph, "test_python_hook_core_witness").unwrap();
    if !valid {
        witness.governance_graph_hash = "sha256:invalid".to_string();
    }
    fs::write(
        theorem_dir.join("theorem_witness.json"),
        serde_json::to_vec_pretty(&witness).unwrap(),
    )
    .unwrap();
}

#[test]
fn heuristic_tier_needs_no_extra_evidence() {
    let harness_dir = unique_dir("heuristic");
    fs::create_dir_all(&harness_dir).unwrap();
    let entry = harness_entry("heuristic", HEURISTIC_TIER);

    assert_eq!(
        effective_evidence_tier(&entry, &harness_dir, None),
        HEURISTIC_TIER
    );
}

#[test]
fn reviewed_tier_requires_reviewer_files_and_agreement_metrics() {
    let harness_dir = unique_dir("reviewed");
    fs::create_dir_all(&harness_dir).unwrap();
    let entry = harness_entry("reviewed", REVIEWED_TIER);

    write_reviewed_evidence(&harness_dir, Some(&reviewed_passing_metrics()));
    assert_eq!(
        effective_evidence_tier(&entry, &harness_dir, None),
        REVIEWED_TIER
    );

    fs::remove_dir_all(harness_dir.join("ground_truth")).unwrap();
    write_reviewed_evidence(&harness_dir, None);
    assert_eq!(
        effective_evidence_tier(&entry, &harness_dir, None),
        UNVERIFIED_CLAIM_TIER
    );
}

fn reviewed_passing_metrics() -> Vec<(&'static str, f64)> {
    vec![
        ("cohen_kappa_nodes", 1.0),
        ("cohen_kappa_edges", 1.0),
        ("node_precision", 1.0),
        ("node_recall", 1.0),
        ("edge_precision", 1.0),
        ("edge_recall", 1.0),
    ]
}

#[test]
fn reviewed_tier_rejects_weak_kappa() {
    let harness_dir = unique_dir("reviewed-weak-kappa");
    fs::create_dir_all(&harness_dir).unwrap();
    let entry = harness_entry("reviewed", REVIEWED_TIER);
    let mut metrics = reviewed_passing_metrics();
    metrics[0] = ("cohen_kappa_nodes", 0.79);

    write_reviewed_evidence(&harness_dir, Some(&metrics));

    assert_eq!(
        effective_evidence_tier(&entry, &harness_dir, None),
        UNVERIFIED_CLAIM_TIER
    );
}

#[test]
fn reviewed_tier_rejects_low_precision() {
    let harness_dir = unique_dir("reviewed-low-precision");
    fs::create_dir_all(&harness_dir).unwrap();
    let entry = harness_entry("reviewed", REVIEWED_TIER);
    let mut metrics = reviewed_passing_metrics();
    metrics[2] = ("node_precision", 0.90);

    write_reviewed_evidence(&harness_dir, Some(&metrics));

    assert_eq!(
        effective_evidence_tier(&entry, &harness_dir, None),
        UNVERIFIED_CLAIM_TIER
    );
}

#[test]
fn reviewed_tier_accepts_protocol_compliant_metrics() {
    let harness_dir = unique_dir("reviewed-compliant");
    fs::create_dir_all(&harness_dir).unwrap();
    let entry = harness_entry("reviewed", REVIEWED_TIER);

    write_reviewed_evidence(&harness_dir, Some(&reviewed_passing_metrics()));

    assert_eq!(
        effective_evidence_tier(&entry, &harness_dir, None),
        REVIEWED_TIER
    );
}

#[test]
fn theorem_backed_tier_requires_lean_file_and_matching_witness_hashes() {
    let harness_dir = unique_dir("theorem");
    fs::create_dir_all(&harness_dir).unwrap();
    let entry = harness_entry("theorem", THEOREM_BACKED_MODELED_TIER);

    write_theorem_evidence(&harness_dir, true);
    assert_eq!(
        effective_evidence_tier(&entry, &harness_dir, None),
        THEOREM_BACKED_MODELED_TIER
    );

    fs::remove_file(harness_dir.join("theorem/theorem_witness.json")).unwrap();
    write_theorem_evidence(&harness_dir, false);
    assert_eq!(
        effective_evidence_tier(&entry, &harness_dir, None),
        UNVERIFIED_CLAIM_TIER
    );
}

fn source_walk_graph(default: Decision, include_edge: bool) -> GovernanceGraph {
    let source = NodeId::new("policy.ts::source").unwrap();
    let sink = NodeId::new("policy.ts::sink").unwrap();
    let mut nodes = BTreeMap::new();
    nodes.insert(
        source.clone(),
        GovernanceNode::Binary {
            id: source.clone(),
            name: "source".to_string(),
            gates: vec![Gate::ExactMatch {
                value: "read".to_string(),
                decision: Decision::Permit,
            }],
            default,
            combination: GateLogic::FirstMatch,
        },
    );
    nodes.insert(
        sink.clone(),
        GovernanceNode::Binary {
            id: sink.clone(),
            name: "sink".to_string(),
            gates: Vec::new(),
            default: Decision::Permit,
            combination: GateLogic::AllMustPass,
        },
    );
    let edges = include_edge
        .then(|| GovernanceEdge::new(source, sink, EdgeTransform::PassThrough).unwrap())
        .into_iter()
        .collect();
    GovernanceGraph { nodes, edges }
}

#[test]
fn source_walk_tier_compares_edges_decisions_and_graph_hash() {
    let harness_dir = unique_dir("source-walk");
    fs::create_dir_all(&harness_dir).unwrap();
    let entry = harness_entry("source-walk", THEOREM_BACKED_SOURCE_WALK_TIER);
    let graph = source_walk_graph(Decision::Deny, true);
    write_theorem_evidence_with_graph(&harness_dir, &graph, true);

    assert_eq!(
        effective_evidence_tier(&entry, &harness_dir, Some(&graph)),
        THEOREM_BACKED_SOURCE_WALK_TIER
    );

    let missing_edge = source_walk_graph(Decision::Deny, false);
    assert_eq!(
        effective_evidence_tier(&entry, &harness_dir, Some(&missing_edge)),
        UNVERIFIED_CLAIM_TIER
    );

    let decision_drift = source_walk_graph(Decision::Permit, true);
    assert_eq!(
        effective_evidence_tier(&entry, &harness_dir, Some(&decision_drift)),
        UNVERIFIED_CLAIM_TIER
    );
}

#[test]
fn evaluate_corpus_reports_effective_tier_without_downgrading_manifest() {
    let root = unique_dir("evaluate");
    let corpus_dir = root.join("corpus");
    let source_dir = root.join("source");
    write_policy_source(&source_dir);
    write_single_harness_corpus(&corpus_dir, "sample", REVIEWED_TIER, &source_dir);
    write_reviewed_evidence(&corpus_dir.join("sample"), None);

    let exit = evaluate_corpus(&corpus_dir).unwrap();

    assert_eq!(exit, ExitCode::SUCCESS);
    assert_eq!(
        report_tier(&corpus_dir.join("sample")),
        UNVERIFIED_CLAIM_TIER
    );
    assert_eq!(manifest_tier(&corpus_dir, "sample"), REVIEWED_TIER);
}
