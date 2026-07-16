use legitimacy::{ExtractionOptions, extract_governance_artifacts};
use std::{
    collections::BTreeSet,
    fs,
    path::PathBuf,
    time::{SystemTime, UNIX_EPOCH},
};

struct BenchmarkCase<'a> {
    label: &'a str,
    files: &'a [(&'a str, &'a str)],
    expected_nodes: &'a [&'a str],
    expected_edges: &'a [(&'a str, &'a str)],
    min_node_precision: f64,
    min_node_recall: f64,
    min_edge_precision: f64,
    min_edge_recall: f64,
}

#[test]
fn extractor_meets_local_benchmark_thresholds() {
    let cases = [
        BenchmarkCase {
            label: "single-rust-gate",
            files: &[(
                "policy.rs",
                r#"
enum Decision {
    Permit,
    Deny,
}

fn format_action(action: &str) -> String {
    action.to_string()
}

pub fn approval_gate(action: &str) -> Decision {
    let normalized = format_action(action);
    if normalized == "read" {
        return Decision::Permit;
    }
    Decision::Deny
}
"#,
            )],
            expected_nodes: &["policy.rs::approval_gate"],
            expected_edges: &[],
            min_node_precision: 1.0,
            min_node_recall: 1.0,
            min_edge_precision: 1.0,
            min_edge_recall: 1.0,
        },
        BenchmarkCase {
            label: "callback-chain",
            files: &[(
                "policy.rs",
                r#"
enum Decision {
    Permit,
    Deny,
}

pub fn approval_gate(action: &str) -> Decision {
    if action == "read" {
        return Decision::Permit;
    }
    review_guard(action)
}

pub fn review_guard(action: &str) -> Decision {
    if action == "delete" {
        return Decision::Deny;
    }
    Decision::Permit
}
"#,
            )],
            expected_nodes: &["policy.rs::approval_gate", "policy.rs::review_guard"],
            expected_edges: &[("policy.rs::approval_gate", "policy.rs::review_guard")],
            min_node_precision: 1.0,
            min_node_recall: 1.0,
            min_edge_precision: 1.0,
            min_edge_recall: 1.0,
        },
        BenchmarkCase {
            label: "rust-import-alias",
            files: &[
                (
                    "policy.rs",
                    r#"
use review::review_guard as reviewed_gate;

enum Decision {
    Permit,
    Deny,
}

pub fn approval_gate(action: &str) -> Decision {
    if action == "read" {
        return Decision::Permit;
    }
    reviewed_gate(action)
}
"#,
                ),
                (
                    "review.rs",
                    r#"
enum Decision {
    Permit,
    Deny,
}

pub fn review_guard(action: &str) -> Decision {
    if action == "delete" {
        return Decision::Deny;
    }
    Decision::Permit
}
"#,
                ),
            ],
            expected_nodes: &["policy.rs::approval_gate", "review.rs::review_guard"],
            expected_edges: &[("policy.rs::approval_gate", "review.rs::review_guard")],
            min_node_precision: 1.0,
            min_node_recall: 1.0,
            min_edge_precision: 1.0,
            min_edge_recall: 1.0,
        },
        BenchmarkCase {
            label: "python-import-alias",
            files: &[
                (
                    "policy.py",
                    r#"
from review import review_write_access as rg

@requires_permission("delete")
def approval_gate(action):
    if action == "read":
        return "approve"
    return rg(action)
"#,
                ),
                (
                    "review.py",
                    r#"
def review_write_access(permission):
    allowed = permission == "write"
    if allowed:
        return "approve"
    return "deny"
"#,
                ),
            ],
            expected_nodes: &["policy.py::approval_gate", "review.py::review_write_access"],
            expected_edges: &[("policy.py::approval_gate", "review.py::review_write_access")],
            min_node_precision: 1.0,
            min_node_recall: 1.0,
            min_edge_precision: 1.0,
            min_edge_recall: 1.0,
        },
        BenchmarkCase {
            label: "typescript-import-alias",
            files: &[
                (
                    "policy.ts",
                    r#"
import { reviewGuard as rg } from "./review";

export function approvalGate(action: string): boolean {
  if (action === "read") {
    return true;
  }
  return rg(action);
}
"#,
                ),
                (
                    "review.ts",
                    r#"
export function reviewGuard(action: string): boolean {
  if (action === "delete") {
    return false;
  }
  return true;
}
"#,
                ),
            ],
            expected_nodes: &["policy.ts::approvalgate", "review.ts::reviewguard"],
            expected_edges: &[("policy.ts::approvalgate", "review.ts::reviewguard")],
            min_node_precision: 1.0,
            min_node_recall: 1.0,
            min_edge_precision: 1.0,
            min_edge_recall: 1.0,
        },
    ];

    for case in cases {
        run_benchmark_case(&case);
    }
}

#[test]
fn reviewed_overlay_upgrades_ambiguous_benchmark_edge() {
    let source_dir = unique_source_dir("benchmark-reviewed-overlay");
    fs::create_dir_all(source_dir.join("a")).unwrap();
    fs::create_dir_all(source_dir.join("b")).unwrap();
    fs::write(
        source_dir.join("policy.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn approval_gate(action: &str) -> Decision {
    if action == "read" {
        return review_guard(action);
    } else if action == "write" {
        return Decision::Permit;
    }
    Decision::Deny
}
"#,
    )
    .unwrap();
    fs::write(
        source_dir.join("a/review.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn review_guard(action: &str) -> Decision {
    if action == "delete" {
        return Decision::Deny;
    } else if action == "read" {
        return Decision::Permit;
    }
    Decision::Deny
}
"#,
    )
    .unwrap();
    fs::write(
        source_dir.join("b/review.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn review_guard(action: &str) -> Decision {
    if action == "delete" {
        return Decision::Deny;
    } else if action == "read" {
        return Decision::Permit;
    }
    Decision::Deny
}
"#,
    )
    .unwrap();

    let overlay = legitimacy::ExtractionReviewOverlay {
        reviewed_nodes: Vec::new(),
        reviewed_edges: Vec::new(),
        alias_hints: vec![legitimacy::AliasHintOverlay {
            caller: "policy.rs::approval_gate".to_string(),
            target_symbol: "review_guard".to_string(),
            callee: "a/review.rs::review_guard".to_string(),
            note: "reviewed ambiguous import binding".to_string(),
        }],
    };

    let artifacts = legitimacy::extract_governance_artifacts_with_review(
        &source_dir,
        ExtractionOptions {
            allow_partial: false,
            ..ExtractionOptions::default()
        },
        Some(&overlay),
    )
    .unwrap();

    assert!(artifacts.resolution_issues.iter().all(|issue| {
        issue.caller != "policy.rs::approval_gate" || issue.target_symbol != "review_guard"
    }));
    assert!(artifacts.recognized_edges.iter().any(|edge| {
        edge.from == "policy.rs::approval_gate"
            && edge.to == "a/review.rs::review_guard"
            && edge.tier == legitimacy::ExtractionEvidenceTier::Reviewed
    }));
}

#[test]
fn extractor_reports_ambiguous_symbol_resolution_in_benchmark_fixture() {
    let source_dir = unique_source_dir("benchmark-ambiguity");
    fs::create_dir_all(source_dir.join("a")).unwrap();
    fs::create_dir_all(source_dir.join("b")).unwrap();
    fs::write(
        source_dir.join("policy.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn approval_gate(action: &str) -> Decision {
    if action == "read" {
        return review_guard(action);
    } else if action == "write" {
        return Decision::Permit;
    } else {
        return Decision::Deny;
    }
}
"#,
    )
    .unwrap();
    fs::write(
        source_dir.join("a/review.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn review_guard(action: &str) -> Decision {
    if action == "delete" {
        return Decision::Deny;
    } else if action == "read" {
        return Decision::Permit;
    } else {
        return Decision::Deny;
    }
}
"#,
    )
    .unwrap();
    fs::write(
        source_dir.join("b/review.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn review_guard(action: &str) -> Decision {
    if action == "delete" {
        return Decision::Deny;
    } else if action == "read" {
        return Decision::Permit;
    } else {
        return Decision::Deny;
    }
}
"#,
    )
    .unwrap();

    let artifacts = extract_governance_artifacts(
        &source_dir,
        ExtractionOptions {
            allow_partial: false,
            ..ExtractionOptions::default()
        },
    )
    .unwrap();

    assert!(
        artifacts
            .resolution_issues
            .iter()
            .any(|issue| issue.target_symbol == "review_guard" && issue.candidates.len() == 2),
        "expected ambiguous resolution issue, got {:?}",
        artifacts.resolution_issues
    );
    assert!(
        !artifacts
            .recognized_edges
            .iter()
            .any(|edge| edge.target_symbol == "review_guard"),
        "ambiguous edge should not be silently materialized"
    );
}

fn run_benchmark_case(case: &BenchmarkCase<'_>) {
    let source_dir = unique_source_dir(case.label);
    fs::create_dir_all(&source_dir).unwrap();
    for (relative_path, contents) in case.files {
        let full_path = source_dir.join(relative_path);
        if let Some(parent) = full_path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(full_path, contents).unwrap();
    }

    let artifacts = extract_governance_artifacts(
        &source_dir,
        ExtractionOptions {
            allow_partial: false,
            ..ExtractionOptions::default()
        },
    )
    .unwrap();

    let actual_nodes = artifacts
        .recognized_nodes
        .iter()
        .map(|node| node.node_id.clone())
        .collect::<BTreeSet<_>>();
    let expected_nodes = case
        .expected_nodes
        .iter()
        .map(|node| node.to_string())
        .collect::<BTreeSet<_>>();
    let actual_edges = artifacts
        .recognized_edges
        .iter()
        .map(|edge| (edge.from.clone(), edge.to.clone()))
        .collect::<BTreeSet<_>>();
    let expected_edges = case
        .expected_edges
        .iter()
        .map(|(from, to)| (from.to_string(), to.to_string()))
        .collect::<BTreeSet<_>>();

    let node_precision = precision(&actual_nodes, &expected_nodes);
    let node_recall = recall(&actual_nodes, &expected_nodes);
    let edge_precision = precision(&actual_edges, &expected_edges);
    let edge_recall = recall(&actual_edges, &expected_edges);

    assert!(
        node_precision >= case.min_node_precision,
        "{} node precision {} < {} (actual {:?}, expected {:?})",
        case.label,
        node_precision,
        case.min_node_precision,
        actual_nodes,
        expected_nodes
    );
    assert!(
        node_recall >= case.min_node_recall,
        "{} node recall {} < {} (actual {:?}, expected {:?})",
        case.label,
        node_recall,
        case.min_node_recall,
        actual_nodes,
        expected_nodes
    );
    assert!(
        edge_precision >= case.min_edge_precision,
        "{} edge precision {} < {} (actual {:?}, expected {:?})",
        case.label,
        edge_precision,
        case.min_edge_precision,
        actual_edges,
        expected_edges
    );
    assert!(
        edge_recall >= case.min_edge_recall,
        "{} edge recall {} < {} (actual {:?}, expected {:?})",
        case.label,
        edge_recall,
        case.min_edge_recall,
        actual_edges,
        expected_edges
    );
}

fn precision<T: Ord>(actual: &BTreeSet<T>, expected: &BTreeSet<T>) -> f64 {
    if actual.is_empty() {
        return if expected.is_empty() { 1.0 } else { 0.0 };
    }
    actual.intersection(expected).count() as f64 / actual.len() as f64
}

fn recall<T: Ord>(actual: &BTreeSet<T>, expected: &BTreeSet<T>) -> f64 {
    if expected.is_empty() {
        return 1.0;
    }
    actual.intersection(expected).count() as f64 / expected.len() as f64
}

fn unique_source_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-extraction-benchmark-{label}-{nanos}"))
}
