use std::{
    fs,
    path::PathBuf,
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

#[test]
fn v1_policy_with_nodes_marker_in_string_is_not_misdetected_as_graph() {
    let policy_path = unique_path("policy-format-v1-marker", "rule.toml");
    fs::write(
        &policy_path,
        r#"[rule]
name = "contains [[nodes]] marker"
version = "1.0"

[claimants]
type = "SubAgent"
id_field = "agent_id"

[estate]
type = "AutonomyTier"
total = 100.0
unit = "compute"

[claims]
ordering = "reliability_score"

[priority_classes]
standard = { level = 1 }

[family]
reductions = "remove_any_single_claimant"
shocks = [0.5]
strengthening = [0.1]
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("compile")
        .arg(&policy_path)
        .output()
        .unwrap();

    assert!(output.status.success(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("contains [[nodes]] marker"));
}

#[test]
fn graph_policy_with_real_nodes_array_is_detected_as_graph() {
    let policy_path = unique_path("policy-format-graph", "graph.toml");
    fs::write(
        &policy_path,
        r#"[graph]
name = "graph-fixture"
version = "1.0"

[[nodes]]
id = "entry"
type = "binary"
default = "deny"
combination = "first_match"

[[nodes.gates]]
type = "exact_match"
value = "Read"
decision = "permit"
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("protocol")
        .arg("init")
        .arg(&policy_path)
        .output()
        .unwrap();

    assert!(output.status.success(), "{output:?}");
    let stdout: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(stdout["state"], "compiled");
}

#[test]
fn malformed_policy_returns_clean_parse_error() {
    let policy_path = unique_path("policy-format-malformed", "toml");
    fs::write(&policy_path, "[rule\nname = \"broken\"").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("compile")
        .arg(&policy_path)
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("failed to parse policy"));
}
