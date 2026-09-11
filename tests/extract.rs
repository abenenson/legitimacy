use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use legitimacy::{
    ClaimCorpusProvenance, ExtractionOptions, analyze_extraction, audit_extracted_graph,
    detect_cycles, extract_governance, extract_governance_artifacts,
};

const CODEX_EVENTS_ROOT: &str = "audits/fixtures/sources/leaderboard/codex-hooks";
const OPENCLAW_INFRA_ROOT: &str = "audits/fixtures/sources/leaderboard/openclaw-infra";

fn fixture_path(path: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(path)
}

#[test]
#[ignore = "slow tree-sitter extraction (~11min in dev / ~2min release); cargo test --test extract -- --ignored to run, included in release-gate"]
fn extract_codex_hooks_discovers_pre_tool_use_governance() {
    let source_dir = fixture_path(CODEX_EVENTS_ROOT);

    let report = analyze_extraction(&source_dir).expect("codex hook extraction should succeed");
    let discovered_nodes = report
        .artifacts
        .graph
        .nodes
        .keys()
        .map(ToString::to_string)
        .collect::<Vec<_>>();

    assert!(
        !report.artifacts.graph.nodes.is_empty(),
        "expected at least one governance node from {}",
        source_dir.display()
    );
    assert!(
        discovered_nodes
            .iter()
            .any(|node_id| node_id.contains("pre_tool_use.rs::run")
                || node_id.contains("pre_tool_use.rs::parse_completed")),
        "expected extractor to discover pre_tool_use governance, got {discovered_nodes:?}"
    );
    let axiom_names = report
        .audit
        .axiom_results
        .iter()
        .map(|result| result.axiom.as_str())
        .collect::<BTreeSet<_>>();
    for axiom in [
        "graph consistency",
        "graph solidarity",
        "graph monotonicity",
        "graph strategyproofness",
        "graph certifiability",
        "graph observable determinacy",
        "graph corrigibility",
        "graph compositional safety",
        "graph nonvacuity",
    ] {
        assert!(
            axiom_names.contains(axiom),
            "graph extraction should run all kernel + diagnostic graph axioms; missing '{axiom}', got {axiom_names:?}"
        );
    }
    assert!(
        report.artifacts.graph.nodes.len() < 30,
        "expected <30 Codex hook governance nodes after filtering, got {}",
        report.artifacts.graph.nodes.len()
    );
    assert!(
        report.artifacts.graph.nodes.len() >= 10,
        "expected the tightened extractor to retain the core Codex governance surfaces, got {} nodes",
        report.artifacts.graph.nodes.len()
    );
    assert!(
        report.artifacts.graph.edges.len() >= 5,
        "expected the tightened extractor to preserve Codex callback connectivity, got {} edges",
        report.artifacts.graph.edges.len()
    );
    assert_eq!(
        report.audit.paradox_results.len(),
        3,
        "graph extraction should run the graph paradox suite"
    );
    assert!(
        !report.audit.claims.is_empty(),
        "graph extraction should synthesize evaluation claims"
    );
    assert_eq!(
        report.audit.corpus_provenance,
        ClaimCorpusProvenance::SyntheticStructuralProbe
    );
}

#[test]
fn extract_codex_hooks_connects_run_to_callback_governance() {
    let source_dir = fixture_path(CODEX_EVENTS_ROOT);

    let graph = extract_governance(&source_dir).expect("codex hook graph should extract");
    let edges = graph
        .edges
        .iter()
        .map(|edge| (edge.from.to_string(), edge.to.to_string()))
        .collect::<Vec<_>>();

    assert!(
        edges.iter().any(|(from, to)| {
            from.contains("pre_tool_use.rs::run") && to.contains("pre_tool_use.rs::parse_completed")
        }),
        "expected callback edge from run to parse_completed, got {edges:?}"
    );
}

#[test]
fn extract_openclaw_exec_approvals_discovers_typescript_governance() {
    let source_dir = fixture_path(OPENCLAW_INFRA_ROOT);
    assert_non_empty_graph(&source_dir);
}

#[test]
fn extract_local_typescript_fixture_discovers_typescript_governance() {
    let source_dir = unique_source_dir("typescript-governance");
    fs::create_dir_all(&source_dir).unwrap();
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

    assert_non_empty_graph(&source_dir);
}

#[test]
fn extraction_reports_boundary_relative_ungoverned_dependencies() {
    let source_dir = unique_source_dir("boundary-causal-safety");
    fs::create_dir_all(&source_dir).unwrap();
    fs::write(
        source_dir.join("policy.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn policy_gate(action: &str) -> Decision {
    if external_risk_check(action) {
        return Decision::Deny;
    }
    if action == "read" {
        return Decision::Permit;
    }
    Decision::Deny
}

fn external_risk_check(action: &str) -> bool {
    action.contains("delete")
}
"#,
    )
    .unwrap();

    let report = analyze_extraction(&source_dir).expect("fixture should extract governance");
    let boundary = &report.artifacts.boundary_causal_safety;

    assert_eq!(boundary.affected_governance_nodes(), Some(1));
    assert_eq!(boundary.external_dependency_count(), Some(1));
    assert_eq!(
        boundary.summary(),
        "1 governance nodes have 1 transitive external dependencies not in the governance graph (causal boundary analysis)"
    );
    assert!(
        boundary
            .ungoverned_dependencies()
            .expect("source dependency analysis must have run")
            .iter()
            .any(|dependency| dependency.dependency == "external_risk_check")
    );
    assert!(
        report
            .audit
            .protocol_assessment
            .blocking_issues
            .iter()
            .any(|issue| issue == boundary.summary())
    );
}

#[test]
fn extraction_reports_transitive_boundary_dependencies() {
    let source_dir = unique_source_dir("boundary-causal-reach");
    fs::create_dir_all(&source_dir).unwrap();
    fs::write(
        source_dir.join("policy.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn policy_gate(action: &str) -> Decision {
    if nested_risk_check(action) {
        return Decision::Deny;
    }
    if action == "read" {
        return Decision::Permit;
    }
    Decision::Deny
}

fn nested_risk_check(action: &str) -> bool {
    deep_risk_check(action)
}

fn deep_risk_check(action: &str) -> bool {
    action.contains("delete")
}
"#,
    )
    .unwrap();

    let report = analyze_extraction(&source_dir).expect("fixture should extract governance");
    let boundary = &report.artifacts.boundary_causal_safety;

    assert_eq!(boundary.affected_governance_nodes(), Some(1));
    assert_eq!(boundary.external_dependency_count(), Some(2));
    assert!(
        boundary
            .ungoverned_dependencies()
            .expect("source dependency analysis must have run")
            .iter()
            .any(|dependency| dependency.dependency == "nested_risk_check")
    );
    assert!(
        boundary
            .ungoverned_dependencies()
            .expect("source dependency analysis must have run")
            .iter()
            .any(|dependency| dependency.dependency == "deep_risk_check")
    );
}

#[test]
fn extract_output_is_byte_stable_for_multi_violation_fixture() {
    let source_dir = unique_source_dir("extract-determinism");
    fs::create_dir_all(&source_dir).unwrap();
    fs::write(
        source_dir.join("sample_governance.py"),
        r#"@requires_permission("delete")
def guard_file_delete(action, user):
    if user.is_admin or action == "read":
        return "approve"
    return "deny"


def permission_review_write(permission, user):
    if permission == "write":
        return "approve"
    if permission == "restricted":
        return "review"
    return "deny"


def sandbox_policy_gate(command, user):
    if command == "cat":
        return "approve"
    if command == "rm":
        return "deny"
    return "review"
"#,
    )
    .unwrap();

    let first = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("extract")
        .arg("--synthetic")
        .arg(&source_dir)
        .output()
        .unwrap();
    assert!(first.status.success(), "{first:?}");

    let second = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("extract")
        .arg("--synthetic")
        .arg(&source_dir)
        .output()
        .unwrap();
    assert!(second.status.success(), "{second:?}");

    let stdout = String::from_utf8(first.stdout.clone()).unwrap();
    assert!(
        stdout.contains("graph monotonicity: REJECTED"),
        "fixture should expose a monotonicity rejection"
    );
    assert!(
        stdout.contains("compositional Alabama:"),
        "fixture should report the compositional Alabama diagnostic"
    );
    assert!(
        stdout.contains("graph nonvacuity (implements NON-VACUOUS axiom):"),
        "fixture should report the nonvacuity diagnostic"
    );
    assert_eq!(
        first.stdout, second.stdout,
        "extract output drifted across runs"
    );
    assert_eq!(
        first.stderr, second.stderr,
        "extract stderr drifted across runs"
    );
}

#[test]
fn extraction_fails_closed_on_partial_parse_by_default() {
    let source_dir = unique_source_dir("extract-partial-default");
    fs::create_dir_all(&source_dir).unwrap();
    fs::write(
        source_dir.join("good.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn approval_gate(action: &str) -> Decision {
    if action == "read" {
        return Decision::Permit;
    }
    Decision::Deny
}
"#,
    )
    .unwrap();
    fs::write(
        source_dir.join("broken.py"),
        r#"
def approval_gate(action):
    if action == "read"
        return "approve"
"#,
    )
    .unwrap();

    let error = extract_governance(&source_dir).unwrap_err();
    assert!(error.to_string().contains("parse"), "{error}");
}

#[test]
fn extraction_can_continue_with_explicit_partial_opt_in() {
    let source_dir = unique_source_dir("extract-partial-allow");
    fs::create_dir_all(&source_dir).unwrap();
    fs::write(
        source_dir.join("good.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn approval_gate(action: &str) -> Decision {
    if action == "read" {
        return Decision::Permit;
    }
    Decision::Deny
}
"#,
    )
    .unwrap();
    fs::write(
        source_dir.join("broken.py"),
        "def approval_gate(action):\n  if ",
    )
    .unwrap();

    let artifacts = extract_governance_artifacts(
        &source_dir,
        ExtractionOptions {
            allow_partial: true,
            ..ExtractionOptions::default()
        },
    )
    .unwrap();

    assert!(!artifacts.coverage.complete);
    assert_eq!(artifacts.coverage.files_discovered, 2);
    assert!(artifacts.coverage.files_errored + artifacts.coverage.files_skipped >= 1);
    assert!(!artifacts.graph.nodes.is_empty());
}

#[cfg(unix)]
#[test]
fn extraction_skips_symlinked_directories() {
    use std::os::unix::fs::symlink;

    let source_dir = unique_source_dir("extract-symlink-root");
    let outside_dir = unique_source_dir("extract-symlink-outside");
    fs::create_dir_all(&source_dir).unwrap();
    fs::create_dir_all(&outside_dir).unwrap();
    fs::write(
        source_dir.join("policy.rs"),
        r#"
pub fn local_approval(action: &str) -> bool {
    if action == "approve" {
        return true;
    }
    false
}
"#,
    )
    .unwrap();
    fs::write(
        outside_dir.join("outside_policy.rs"),
        r#"
pub fn outside_approval(action: &str) -> bool {
    if action == "delete" {
        return false;
    }
    true
}
"#,
    )
    .unwrap();
    symlink(&outside_dir, source_dir.join("linked-outside")).unwrap();

    let artifacts = extract_governance_artifacts(&source_dir, ExtractionOptions::default())
        .expect("local extraction should ignore symlinked directories");

    assert_eq!(artifacts.coverage.files_discovered, 1);
    assert!(
        artifacts
            .recognized_nodes
            .iter()
            .all(|node| !node.relative_path.contains("outside_policy")),
        "{:#?}",
        artifacts.recognized_nodes
    );

    let _ = fs::remove_dir_all(source_dir);
    let _ = fs::remove_dir_all(outside_dir);
}

#[test]
fn extracted_graph_can_be_audited_against_explicit_claim_corpus() {
    let source_dir = unique_source_dir("extract-explicit-claims");
    fs::create_dir_all(&source_dir).unwrap();
    fs::write(
        source_dir.join("policy.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn approval_gate(action: &str) -> Decision {
    if action == "read" {
        return Decision::Permit;
    }
    if action == "delete" {
        return Decision::Deny;
    }
    Decision::Deny
}
"#,
    )
    .unwrap();

    let claims = vec![
        legitimacy::GovernanceClaim {
            claimant_id: "read".to_string(),
            strength: 1.0,
            priority_class: None,
            path: None,
            action: Some("read".to_string()),
            content: None,
            metrics: Default::default(),
        },
        legitimacy::GovernanceClaim {
            claimant_id: "delete".to_string(),
            strength: 1.0,
            priority_class: None,
            path: None,
            action: Some("delete".to_string()),
            content: None,
            metrics: Default::default(),
        },
    ];

    let report = audit_extracted_graph(
        &source_dir,
        claims.clone(),
        ExtractionOptions {
            allow_partial: false,
            ..ExtractionOptions::default()
        },
    )
    .unwrap();

    assert_eq!(
        report.audit.corpus_provenance,
        ClaimCorpusProvenance::UserSupplied
    );
    assert_eq!(report.audit.claims, claims);
}

fn assert_non_empty_graph(source_dir: &Path) {
    assert!(
        source_dir.exists(),
        "fixture missing: {}",
        source_dir.display()
    );

    let graph = extract_governance(source_dir).expect("governance graph should extract");
    assert!(
        !graph.nodes.is_empty(),
        "expected at least one governance node from {}",
        source_dir.display()
    );
    if source_dir == fixture_path(OPENCLAW_INFRA_ROOT) {
        let cycles = detect_cycles(&graph).expect("OpenClaw cycle detection should succeed");
        assert!(
            graph.nodes.len() < 200,
            "expected <200 OpenClaw governance nodes after filtering, got {}",
            graph.nodes.len()
        );
        assert!(
            cycles.is_empty(),
            "expected tightened OpenClaw extraction to remove the earlier reflexive false-positive cycles, got {cycles:?}"
        );
    }
}

fn unique_source_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}"))
}

#[test]
fn measured_zero_source_dependencies_are_distinct_from_unassessed_boundary() {
    let source_dir = unique_source_dir("boundary-measured-zero");
    fs::create_dir_all(&source_dir).unwrap();
    fs::write(
        source_dir.join("policy.rs"),
        r#"
enum Decision { Permit, Deny }
pub fn approval_gate(action: &str) -> Decision {
    if action == "read" { return Decision::Permit; }
    Decision::Deny
}
"#,
    )
    .unwrap();
    let report = analyze_extraction(&source_dir).unwrap();
    let measured = &report.artifacts.boundary_causal_safety;
    assert_eq!(measured.external_dependency_count(), Some(0));
    assert_eq!(measured.live_blocker(), None);
    let measured_json = serde_json::to_value(measured).unwrap();
    assert_eq!(measured_json["status"], "assessed");
    assert_eq!(measured_json["external_dependency_count"], 0);

    let missing = legitimacy::BoundaryCausalSafetyAssessment::default();
    assert_eq!(missing.external_dependency_count(), None);
    assert_eq!(missing.affected_governance_nodes(), None);
    assert!(missing.ungoverned_dependencies().is_none());
    let missing_json = serde_json::to_value(&missing).unwrap();
    assert_eq!(missing_json["status"], "unassessed");
    for field in [
        "external_dependency_count",
        "affected_governance_nodes",
        "ungoverned_dependencies",
    ] {
        assert!(
            missing_json.get(field).is_none(),
            "missing evidence must not fabricate {field}: {missing_json}"
        );
    }
    let blocker = missing.live_blocker().unwrap().to_string();
    let audit = legitimacy::audit_governance_graph(
        &report.artifacts.graph,
        legitimacy::extract::synthetic_claims(&report.artifacts.graph),
        legitimacy::ClaimCorpusProvenance::SyntheticStructuralProbe,
        missing,
    )
    .unwrap();
    assert!(audit.protocol_assessment.blocking_issues.contains(&blocker));
    fs::remove_dir_all(source_dir).unwrap();
}
