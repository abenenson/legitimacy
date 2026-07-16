use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

fn unique_path(label: &str, extension: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}.{extension}"))
}

fn unique_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}"))
}

fn repo_path(path: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(path)
}

fn run_success(args: &[&str]) -> Vec<u8> {
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args(args)
        .output()
        .unwrap();
    assert!(output.status.success(), "{args:?}: {output:?}");
    output.stdout
}

#[test]
fn readme_quickstart_commands_are_executable() {
    let extract_dir = unique_dir("readme-extract");
    fs::create_dir_all(&extract_dir).unwrap();
    fs::copy(
        repo_path("tests/fixtures/sample_governance.py"),
        extract_dir.join("sample_governance.py"),
    )
    .unwrap();

    let graph_path = unique_path("readme-extract-graph", "json");
    let extract_stdout = run_success(&[
        "extract",
        extract_dir.to_str().unwrap(),
        "--emit-graph",
        graph_path.to_str().unwrap(),
    ]);
    let extract_text = String::from_utf8(extract_stdout).unwrap();
    assert!(
        extract_text.contains("EXTRACTION ARTIFACTS"),
        "{extract_text}"
    );

    let audit_stdout = run_success(&[
        "audit-graph",
        "--graph",
        graph_path.to_str().unwrap(),
        "--claims",
        "tests/fixtures/sample_governance_claims.jsonl",
    ]);
    let audit_text = String::from_utf8(audit_stdout).unwrap();
    assert!(audit_text.contains("EXTRACTION REPORT"), "{audit_text}");

    let synthetic_stdout = run_success(&["extract", extract_dir.to_str().unwrap(), "--synthetic"]);
    let synthetic_text = String::from_utf8(synthetic_stdout).unwrap();
    assert!(
        synthetic_text.contains("claim corpus: SyntheticStructuralProbe"),
        "{synthetic_text}"
    );

    let review_dir = unique_dir("readme-reviewed-extract");
    fs::create_dir_all(review_dir.join("a")).unwrap();
    fs::write(
        review_dir.join("policy.rs"),
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
"#,
    )
    .unwrap();
    fs::write(
        review_dir.join("a/review.rs"),
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
    )
    .unwrap();
    let reviewed_stdout = run_success(&[
        "extract",
        review_dir.to_str().unwrap(),
        "--review-overlay",
        "tests/fixtures/sample_governance_review_overlay.json",
        "--claims",
        "tests/fixtures/sample_governance_runtime_claims.jsonl",
        "--claims-provenance",
        "observed-runtime",
    ]);
    let reviewed_text = String::from_utf8(reviewed_stdout).unwrap();
    assert!(
        reviewed_text.contains("review overlay: applied"),
        "{reviewed_text}"
    );
    assert!(
        reviewed_text.contains("claim corpus: ObservedRuntime"),
        "{reviewed_text}"
    );

    run_success(&["compile", "examples/claude-agent-sdk-permissions.rule.toml"]);
    run_success(&["paradox", "examples/claude-agent-sdk-hooks.rule.toml"]);

    let certificate_stdout = run_success(&[
        "certify",
        "examples/claude-agent-sdk-permissions.rule.toml",
        "--claimant",
        "Read",
        "--outcome",
        "1",
    ]);
    let certificate: serde_json::Value = serde_json::from_slice(&certificate_stdout).unwrap();
    assert_eq!(certificate["claimant_id"], "Read");

    let compiled_path = unique_path("readme-compiled", "json");
    let measured_path = unique_path("readme-measured", "json");
    let live_path = unique_path("readme-live", "json");

    let compiled_stdout = run_success(&[
        "protocol",
        "init",
        "examples/protocol-gate-graph.graph.toml",
    ]);
    fs::write(&compiled_path, &compiled_stdout).unwrap();

    let measured_stdout = run_success(&["protocol", "measure", compiled_path.to_str().unwrap()]);
    fs::write(&measured_path, &measured_stdout).unwrap();

    let live_stdout = run_success(&["protocol", "activate", measured_path.to_str().unwrap()]);
    fs::write(&live_path, &live_stdout).unwrap();

    let status_stdout = run_success(&["protocol", "status", live_path.to_str().unwrap()]);
    let status_text = String::from_utf8(status_stdout).unwrap();
    assert!(status_text.contains("state: live"), "{status_text}");

    let audit_stdout = run_success(&["protocol", "audit", live_path.to_str().unwrap()]);
    let audit: serde_json::Value = serde_json::from_slice(&audit_stdout).unwrap();
    assert_eq!(audit["state"], "live");
    assert_eq!(audit["certificate_chain_valid"], true);
}
