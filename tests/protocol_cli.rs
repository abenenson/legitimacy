use std::{
    collections::BTreeMap,
    fs,
    path::PathBuf,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use legitimacy::{
    Decision, Gate, GateLogic, GovernanceDriftAlert, GovernanceNode, GraphBuilder, NodeId,
    ProtocolState, StrategyproofnessVerdict,
    protocol::{
        MonitorConfig, SupervisoryAction, activate, compile as compile_protocol, declare, measure,
        report_drift, supervise,
    },
};

fn unique_path(label: &str, extension: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}.{extension}"))
}

fn write_graph_policy() -> PathBuf {
    let path = unique_path("protocol-policy", "graph.toml");
    fs::write(
        &path,
        r#"[graph]
name = "protocol-fixture"
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
    path
}

fn admissible_graph() -> legitimacy::GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Binary {
                id: NodeId::new("entry").unwrap(),
                name: "entry".to_string(),
                gates: vec![Gate::ExactMatch {
                    value: "Read".to_string(),
                    decision: Decision::Permit,
                }],
                default: Decision::Deny,
                combination: GateLogic::FirstMatch,
            })
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}

#[test]
fn protocol_init_measure_and_activate_commands_emit_state_json() {
    let policy = write_graph_policy();
    let init = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("protocol")
        .arg("init")
        .arg(&policy)
        .output()
        .unwrap();
    assert!(init.status.success(), "{init:?}");
    let compiled: ProtocolState = serde_json::from_slice(&init.stdout).unwrap();
    let ProtocolState::Compiled { compiled_graph, .. } = compiled else {
        panic!("expected compiled state");
    };
    assert_eq!(compiled_graph.name, "protocol-fixture");
    assert_eq!(compiled_graph.version, "1.0");

    let state_path = unique_path("protocol-compiled", "json");
    fs::write(&state_path, &init.stdout).unwrap();
    let measured = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("protocol")
        .arg("measure")
        .arg(&state_path)
        .output()
        .unwrap();
    assert!(measured.status.success(), "{measured:?}");
    let measured_state: ProtocolState = serde_json::from_slice(&measured.stdout).unwrap();
    assert!(matches!(measured_state, ProtocolState::Measured { .. }));

    let measured_path = unique_path("protocol-measured", "json");
    fs::write(&measured_path, &measured.stdout).unwrap();
    let activated = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("protocol")
        .arg("activate")
        .arg(&measured_path)
        .output()
        .unwrap();
    assert!(activated.status.success(), "{activated:?}");
    let activated_state: ProtocolState = serde_json::from_slice(&activated.stdout).unwrap();
    assert!(matches!(activated_state, ProtocolState::Live { .. }));
}

#[test]
fn protocol_activate_rejects_inverted_interval_bounds() {
    let measured = measure(
        compile_protocol(declare(admissible_graph(), Vec::new()).unwrap()).unwrap(),
        legitimacy::extract::synthetic_claims(&admissible_graph()),
    )
    .unwrap();
    let state_path = unique_path("protocol-measured-bad-interval", "json");
    fs::write(&state_path, serde_json::to_vec_pretty(&measured).unwrap()).unwrap();

    let activated = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("protocol")
        .arg("activate")
        .arg(&state_path)
        .arg("--min-interval-seconds")
        .arg("10")
        .arg("--max-interval-seconds")
        .arg("5")
        .output()
        .unwrap();
    assert!(!activated.status.success(), "{activated:?}");
    let stderr = String::from_utf8(activated.stderr).unwrap();
    assert!(stderr.contains("min_interval_seconds <= max_interval_seconds"));
}

#[test]
fn protocol_status_and_audit_commands_report_live_state() {
    let measured = measure(
        compile_protocol(declare(admissible_graph(), Vec::new()).unwrap()).unwrap(),
        legitimacy::extract::synthetic_claims(&admissible_graph()),
    )
    .unwrap();
    let live = activate(
        measured,
        MonitorConfig {
            min_interval_seconds: 5,
            max_interval_seconds: 10,
            seed: 11,
        },
    )
    .unwrap();
    let drifted = report_drift(
        live,
        GovernanceDriftAlert {
            alert_type: "manual".to_string(),
            property: legitimacy::GovernanceProperty::Consistency,
            declared_bound: 0.0,
            actual_magnitude: 0.4,
            evidence: BTreeMap::from([("source".to_string(), "test".to_string())]),
            recommended_action: "recompile".to_string(),
        },
    )
    .unwrap();

    let state_path = unique_path("protocol-live", "json");
    fs::write(&state_path, serde_json::to_vec_pretty(&drifted).unwrap()).unwrap();

    let status = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("protocol")
        .arg("status")
        .arg(&state_path)
        .output()
        .unwrap();
    assert!(status.status.success(), "{status:?}");
    let status_stdout = String::from_utf8(status.stdout).unwrap();
    assert!(status_stdout.contains("state: drifted"));
    assert!(status_stdout.contains("drift_property: consistency"));

    let audit = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("protocol")
        .arg("audit")
        .arg(&state_path)
        .output()
        .unwrap();
    assert!(audit.status.success(), "{audit:?}");
    let audit_json: serde_json::Value = serde_json::from_slice(&audit.stdout).unwrap();
    assert_eq!(audit_json["state"], "drifted");
    assert_eq!(audit_json["drift_alerts"], 1);
}

#[test]
fn protocol_audit_accepts_supervised_state() {
    let measured = measure(
        compile_protocol(declare(admissible_graph(), Vec::new()).unwrap()).unwrap(),
        legitimacy::extract::synthetic_claims(&admissible_graph()),
    )
    .unwrap();
    let live = activate(
        measured,
        MonitorConfig {
            min_interval_seconds: 5,
            max_interval_seconds: 10,
            seed: 13,
        },
    )
    .unwrap();
    let supervised = supervise(
        live,
        SupervisoryAction::Pause,
        Some("operator request".to_string()),
    )
    .unwrap();

    let state_path = unique_path("protocol-supervised", "json");
    fs::write(&state_path, serde_json::to_vec_pretty(&supervised).unwrap()).unwrap();

    let audit = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("protocol")
        .arg("audit")
        .arg(&state_path)
        .output()
        .unwrap();
    assert!(audit.status.success(), "{audit:?}");

    let audit_json: serde_json::Value = serde_json::from_slice(&audit.stdout).unwrap();
    assert_eq!(audit_json["state"], "supervised");
    assert_eq!(audit_json["drift_alerts"], 0);
}

#[test]
fn protocol_status_rejects_malformed_supervised_state() {
    let measured = measure(
        compile_protocol(declare(admissible_graph(), Vec::new()).unwrap()).unwrap(),
        legitimacy::extract::synthetic_claims(&admissible_graph()),
    )
    .unwrap();
    let live = activate(
        measured,
        MonitorConfig {
            min_interval_seconds: 5,
            max_interval_seconds: 10,
            seed: 17,
        },
    )
    .unwrap();
    let supervised = supervise(
        live,
        SupervisoryAction::Pause,
        Some("operator request".to_string()),
    )
    .unwrap();

    let mut payload = serde_json::to_value(&supervised).unwrap();
    payload["intervention"]["postcondition"] = serde_json::json!("universal_deny");

    let state_path = unique_path("protocol-malformed-supervised", "json");
    fs::write(&state_path, serde_json::to_vec_pretty(&payload).unwrap()).unwrap();

    let status = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("protocol")
        .arg("status")
        .arg(&state_path)
        .output()
        .unwrap();
    assert!(!status.status.success(), "{status:?}");
    let stderr = String::from_utf8(status.stderr).unwrap();
    assert!(stderr.contains("protocol state is malformed"), "{stderr}");
    assert!(stderr.contains("postcondition"), "{stderr}");
}

#[test]
fn protocol_measure_rejects_compiled_state_with_noncanonical_hash() {
    let compiled = compile_protocol(declare(admissible_graph(), Vec::new()).unwrap()).unwrap();
    let mut payload = serde_json::to_value(&compiled).unwrap();
    payload["compiled_graph"]["compiled_rule_hash"] = serde_json::json!("not-the-canonical-hash");

    let state_path = unique_path("protocol-bad-hash", "json");
    fs::write(&state_path, serde_json::to_vec_pretty(&payload).unwrap()).unwrap();

    let measured = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("protocol")
        .arg("measure")
        .arg(&state_path)
        .output()
        .unwrap();
    assert!(!measured.status.success(), "{measured:?}");
    let stderr = String::from_utf8(measured.stderr).unwrap();
    assert!(stderr.contains("compiled_rule_hash"), "{stderr}");
    assert!(stderr.contains("malformed"), "{stderr}");
}

#[test]
fn protocol_measure_rejects_compiled_state_with_tampered_strategyproofness() {
    let compiled = compile_protocol(declare(admissible_graph(), Vec::new()).unwrap()).unwrap();
    let mut payload = serde_json::to_value(&compiled).unwrap();
    payload["compiled_graph"]["strategyproofness"] =
        serde_json::to_value(StrategyproofnessVerdict::Manipulable {
            claimant: "mallory".to_string(),
            true_strength: 1.0,
            reported: 2.0,
            true_alloc: 0.0,
            manipulated_alloc: 1.0,
        })
        .unwrap();

    let state_path = unique_path("protocol-tampered-strategyproofness", "json");
    fs::write(&state_path, serde_json::to_vec_pretty(&payload).unwrap()).unwrap();

    let measured = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("protocol")
        .arg("measure")
        .arg(&state_path)
        .output()
        .unwrap();
    assert!(!measured.status.success(), "{measured:?}");
    let stderr = String::from_utf8(measured.stderr).unwrap();
    assert!(stderr.contains("compiled_rule_hash"), "{stderr}");
    assert!(stderr.contains("malformed"), "{stderr}");
}
