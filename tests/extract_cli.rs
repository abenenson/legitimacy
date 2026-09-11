use std::{
    fs,
    path::PathBuf,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

fn unique_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}"))
}

#[test]
fn synthetic_extract_respects_allow_partial() {
    let source_dir = unique_dir("extract-synthetic-partial");
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
    Decision::Deny
}
"#,
    )
    .unwrap();
    fs::write(
        source_dir.join("broken.py"),
        "class {{ template_syntax }}:\n    pass\n",
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args([
            "extract",
            source_dir.to_str().unwrap(),
            "--synthetic",
            "--allow-partial",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "synthetic extract should honor --allow-partial: {output:?}"
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("EXTRACTION REPORT"), "{stdout}");
    assert!(stdout.contains("coverage:"), "{stdout}");
}

#[test]
fn extract_cli_accepts_theorem_backed_python_hook_core_mode() {
    let source_dir = unique_dir("extract-theorem-backed");
    fs::create_dir_all(&source_dir).unwrap();
    fs::write(
        source_dir.join("hooks.py"),
        r#"
from typing import Literal, NotRequired, TypedDict

class PreToolUseHookSpecificOutput(TypedDict):
    hookEventName: Literal["PreToolUse"]
    permissionDecision: NotRequired[Literal["allow", "deny", "ask"]]
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args([
            "extract",
            source_dir.to_str().unwrap(),
            "--mode",
            "theorem-backed",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "theorem-backed extract should succeed: {output:?}"
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("PreToolUseHookSpecificOutput"), "{stdout}");
}

#[test]
fn exported_graph_cannot_turn_missing_source_boundary_evidence_into_zero_dependencies() {
    let directory = unique_dir("boundary-evidence-roundtrip");
    fs::create_dir_all(&directory).unwrap();
    let graph_path = directory.join("exported.graph.json");
    let binary = env!("CARGO_BIN_EXE_legitimacy");
    let extracted = Command::new(binary)
        .args([
            "extract",
            "tests/fixtures",
            "--emit-graph",
            graph_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(extracted.status.success(), "{extracted:?}");
    let extraction_text = String::from_utf8(extracted.stdout).unwrap();
    assert!(
        extraction_text.contains("requires_permission"),
        "{extraction_text}"
    );
    assert!(
        extraction_text.contains("1 transitive external dependencies"),
        "{extraction_text}"
    );

    let source_audit = Command::new(binary)
        .args([
            "audit-graph",
            "--source-dir",
            "tests/fixtures",
            "--claims",
            "tests/fixtures/sample_governance_claims.jsonl",
        ])
        .output()
        .unwrap();
    assert!(source_audit.status.success(), "{source_audit:?}");
    let source_text = String::from_utf8(source_audit.stdout).unwrap();
    let source_blockers = source_text
        .split("- blocking for LIVE:")
        .nth(1)
        .expect("source audit must state its LIVE blockers");
    assert!(
        source_blockers.contains("1 transitive external dependencies"),
        "{source_text}"
    );

    let graph_audit = Command::new(binary)
        .args([
            "audit-graph",
            "--graph",
            graph_path.to_str().unwrap(),
            "--claims",
            "tests/fixtures/sample_governance_claims.jsonl",
        ])
        .output()
        .unwrap();
    // Exit success means diagnostics ran, not that source-level promotion is safe.
    assert!(graph_audit.status.success(), "{graph_audit:?}");
    let graph_text = String::from_utf8(graph_audit.stdout).unwrap();
    assert!(graph_text.contains("DIAGNOSTIC CHECKS"), "{graph_text}");
    assert!(
        !graph_text.contains("0 transitive external dependencies"),
        "{graph_text}"
    );
    let graph_blockers = graph_text
        .split("- blocking for LIVE:")
        .nth(1)
        .expect("missing source evidence must be a LIVE blocker");
    assert!(
        graph_blockers
            .contains("UNASSESSED: source boundary/dependency analysis was not performed"),
        "{graph_text}"
    );
    fs::remove_dir_all(directory).unwrap();
}
