use std::{
    fs,
    path::PathBuf,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use legitimacy::{
    Decision, Gate, GateLogic, GovernanceNode, GraphBuilder, NodeId, ProtocolState,
    protocol::{MonitorConfig, activate, compile as compile_protocol, declare, measure},
};

fn unique_path(label: &str, extension: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}.{extension}"))
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
fn protocol_audit_returns_non_zero_for_tampered_certificate_chain() {
    let measured = measure(
        compile_protocol(declare(admissible_graph(), Vec::new()).unwrap()).unwrap(),
        legitimacy::extract::synthetic_claims(&admissible_graph()),
    )
    .unwrap();
    let mut live = activate(
        measured,
        MonitorConfig {
            min_interval_seconds: 5,
            max_interval_seconds: 10,
            seed: 7,
        },
    )
    .unwrap();

    assert!(matches!(live, ProtocolState::Live { .. }));
    if let ProtocolState::Live { ledger, .. } = &mut live {
        ledger.head_hash = Some("tampered-head-hash".to_string());
    }

    let state_path = unique_path("protocol-audit-tampered", "json");
    fs::write(&state_path, serde_json::to_vec_pretty(&live).unwrap()).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .arg("protocol")
        .arg("audit")
        .arg(&state_path)
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(2), "{output:?}");

    let stdout: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(stdout["certificate_chain_valid"], false);

    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("certificate_chain_valid: false"));
}
