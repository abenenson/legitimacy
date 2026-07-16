use legitimacy::{
    BoundaryCausalSafetyAssessment, ClaimCorpusProvenance, Decision, ExtractionOptions, Gate,
    GateLogic, GovernanceGraph, GovernanceNode, NodeId, audit_extracted_graph_with_review,
    audit_governance_graph, build_codex_oss_story_corpus_pack, import_codex_oss_story_corpus_pack,
    load_observed_runtime_corpus_pack,
};
use std::{
    fs,
    path::{Path, PathBuf},
    time::{SystemTime, UNIX_EPOCH},
};

const CODEX_OSS_STORY_FIXTURE: &str = "audits/fixtures/corpora/codex-oss-story.jsonl";
const CODEX_TUI_RUNTIME_SLICE_FIXTURE: &str =
    "audits/fixtures/sources/observed-runtime/codex-tui-runtime-slice";

fn fixture_path(path: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(path)
}

#[test]
fn codex_oss_story_import_is_deterministic() {
    let input = fixture_path(CODEX_OSS_STORY_FIXTURE);
    let first = build_codex_oss_story_corpus_pack(&input).unwrap();
    let second = build_codex_oss_story_corpus_pack(&input).unwrap();

    assert_eq!(first, second);
    assert_eq!(first.manifest.claim_count, 9);
    assert!(
        first
            .claims
            .iter()
            .all(|record| record.claim.claimant_id.starts_with("turn_"))
    );
    assert!(first.claims.iter().all(|record| {
        record
            .source_event_id
            .as_deref()
            .unwrap_or("")
            .starts_with("evt_")
    }));
}

#[test]
fn codex_oss_story_import_binary_writes_corpus_pack() {
    let input = fixture_path(CODEX_OSS_STORY_FIXTURE);
    let output_dir = unique_dir("codex-observed-runtime-pack");

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_import_codex_observed_runtime"))
        .args([
            "--input",
            input.to_str().unwrap(),
            "--output",
            output_dir.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");

    let pack = load_observed_runtime_corpus_pack(&output_dir).unwrap();
    assert_eq!(pack.manifest.claim_count, 9);
    assert_eq!(pack.claims.len(), 9);
}

#[test]
fn codex_oss_story_import_library_writes_pack_to_disk() {
    let input = fixture_path(CODEX_OSS_STORY_FIXTURE);
    let output_dir = unique_dir("codex-observed-runtime-library-pack");

    import_codex_oss_story_corpus_pack(&input, &output_dir).unwrap();
    let pack = load_observed_runtime_corpus_pack(&output_dir).unwrap();

    assert_eq!(pack.claims.len(), 9);
}

#[test]
fn observed_runtime_claims_zero_fill_missing_numeric_metrics() {
    let input = fixture_path(CODEX_OSS_STORY_FIXTURE);
    let pack = build_codex_oss_story_corpus_pack(&input).unwrap();
    let graph = GovernanceGraph {
        nodes: [(
            NodeId::new("gate").unwrap(),
            GovernanceNode::Binary {
                id: NodeId::new("gate").unwrap(),
                name: "gate".to_string(),
                gates: vec![Gate::ThresholdGate {
                    field: "permissions".to_string(),
                    min: 1.0,
                    decision: Decision::Escalate,
                }],
                default: Decision::Permit,
                combination: GateLogic::FirstMatch,
            },
        )]
        .into_iter()
        .collect(),
        edges: Vec::new(),
    };

    let observed = audit_governance_graph(
        &graph,
        pack.governance_claims(),
        ClaimCorpusProvenance::ObservedRuntime,
        BoundaryCausalSafetyAssessment::default(),
    )
    .unwrap();
    assert_eq!(observed.claims.len(), 9);
    assert!(
        observed
            .claims
            .iter()
            .all(|claim| claim.metrics.contains_key("permissions"))
    );

    let err = audit_governance_graph(
        &graph,
        pack.governance_claims(),
        ClaimCorpusProvenance::UserSupplied,
        BoundaryCausalSafetyAssessment::default(),
    )
    .unwrap_err();
    assert!(
        err.to_string()
            .contains("does not provide metric 'permissions'")
    );
}

#[test]
fn codex_tui_observed_runtime_audit_succeeds_end_to_end() {
    let runtime_slice = fixture_path(CODEX_TUI_RUNTIME_SLICE_FIXTURE);
    let input = fixture_path(CODEX_OSS_STORY_FIXTURE);

    let pack = build_codex_oss_story_corpus_pack(&input).unwrap();
    let report = audit_extracted_graph_with_review(
        runtime_slice.as_path(),
        pack.governance_claims(),
        ExtractionOptions {
            allow_partial: false,
            ..ExtractionOptions::default()
        },
        ClaimCorpusProvenance::ObservedRuntime,
        None,
    )
    .unwrap();

    assert_eq!(
        report.audit.corpus_provenance,
        ClaimCorpusProvenance::ObservedRuntime
    );
    assert_eq!(report.audit.claims.len(), 9);
    assert_eq!(report.artifacts.graph.nodes.len(), 9);
    assert!(
        report
            .audit
            .axiom_results
            .iter()
            .any(|result| result.axiom == "graph monotonicity"
                && matches!(result.verdict, Some(legitimacy::Verdict::Rejected { .. })))
    );
    assert!(
        report
            .audit
            .axiom_results
            .iter()
            .any(|result| result.axiom == "graph nonvacuity"
                && matches!(result.verdict, Some(legitimacy::Verdict::Admissible { .. })))
    );
}

fn unique_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}"));
    fs::create_dir_all(&dir).unwrap();
    dir
}
