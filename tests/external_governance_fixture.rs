use std::{collections::BTreeMap, fmt};

use legitimacy::{
    Decision, EdgeTransform, GovernanceClaim, GovernanceGraph, GovernanceNode, GraphBuilder,
    NodeId, Verdict,
    axioms::{
        binary::{BinaryDelta, BinaryShock},
        graph::{
            consistency::check_graph_consistency, monotonicity::check_graph_monotonicity,
            solidarity::check_graph_solidarity,
        },
    },
    graph::{Gate, GateLogic},
    paradox::compositional_alabama,
    traverse,
};

#[derive(Clone, Debug)]
struct SourceSpan {
    relative_path: &'static str,
    start_line: usize,
    end_line: usize,
}

impl fmt::Display for SourceSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.start_line == self.end_line {
            write!(f, "{}#L{}", self.relative_path, self.start_line)
        } else {
            write!(
                f,
                "{}#L{}-L{}",
                self.relative_path, self.start_line, self.end_line
            )
        }
    }
}

#[derive(Clone, Debug)]
struct ExternalGovernanceFixture {
    graph: GovernanceGraph,
    claims: Vec<GovernanceClaim>,
    deltas: Vec<BinaryDelta>,
    shocks: Vec<BinaryShock>,
    source_spans: Vec<(&'static str, SourceSpan)>,
}

#[test]
fn external_governance_fixture_matches_permission_and_stdout_outcomes() {
    let fixture = external_governance_fixture();
    let decisions = final_decisions(&fixture.graph, &fixture.claims);

    println!(
        "External governance fixture source trace: {}",
        join_spans(&fixture.source_spans)
    );

    assert_eq!(decisions["safe-bash"], Decision::Permit);
    assert_eq!(decisions["dangerous-no-ui"], Decision::Deny);
    assert_eq!(decisions["dangerous-user-rejected"], Decision::Deny);
    assert_eq!(decisions["dangerous-user-approved"], Decision::Permit);
    assert_eq!(decisions["non-bash-tool"], Decision::Permit);
    assert_eq!(decisions["stdout-unguarded"], Decision::Deny);
    assert_eq!(decisions["invalid-tool-call"], Decision::Deny);
}

#[test]
fn external_governance_graph_is_consistent_on_audited_fixture() {
    let fixture = external_governance_fixture();
    let verdict = check_graph_consistency(&fixture.graph, &fixture.claims).unwrap();

    println!(
        "External governance consistency check source trace: {}",
        join_spans(&fixture.source_spans)
    );

    assert!(
        matches!(verdict, Verdict::Admissible { .. }),
        "external governance graph should remain consistent on the audit fixture: {verdict:?}"
    );
}

#[test]
fn external_governance_graph_is_solidary_under_common_strength_shocks() {
    let fixture = external_governance_fixture();
    let verdict = check_graph_solidarity(&fixture.graph, &fixture.claims, &fixture.shocks).unwrap();

    println!(
        "External governance solidarity check source trace: {}",
        join_spans(&fixture.source_spans)
    );

    assert!(
        matches!(verdict, Verdict::Admissible { .. }),
        "external governance graph should stay solidary under common strength shocks: {verdict:?}"
    );
}

#[test]
fn external_governance_graph_is_monotone_in_readiness_and_approval_evidence() {
    let fixture = external_governance_fixture();
    let verdict =
        check_graph_monotonicity(&fixture.graph, &fixture.claims, &fixture.deltas).unwrap();

    println!(
        "External governance monotonicity check source trace: {}",
        join_spans(&fixture.source_spans)
    );

    assert!(
        matches!(verdict, Verdict::Admissible { .. }),
        "external governance graph should stay monotone in positive approval evidence: {verdict:?}"
    );
}

#[test]
fn external_governance_graph_has_no_compositional_alabama_witness() {
    let fixture = external_governance_fixture();
    let violation = compositional_alabama(&fixture.graph, &fixture.claims).unwrap();

    println!(
        "External governance Alabama check source trace: {}",
        join_spans(&fixture.source_spans)
    );

    assert!(
        violation.is_none(),
        "external governance graph should not expose a compositional Alabama witness: {violation:?}"
    );
}

fn external_governance_fixture() -> ExternalGovernanceFixture {
    ExternalGovernanceFixture {
        graph: external_governance_graph(),
        claims: audited_claims(),
        deltas: vec![
            BinaryDelta {
                field: "tool_ready".to_string(),
                delta: 1.0,
            },
            BinaryDelta {
                field: "dangerous_user_approved".to_string(),
                delta: 1.0,
            },
            BinaryDelta {
                field: "stdout_taken_over".to_string(),
                delta: 1.0,
            },
        ],
        shocks: vec![
            BinaryShock {
                field: "strength".to_string(),
                delta: 0.20,
            },
            BinaryShock {
                field: "strength".to_string(),
                delta: -0.20,
            },
        ],
        source_spans: vec![
            ("prepare-tool-call", prepare_tool_call_span()),
            ("permission-gate", permission_gate_span()),
            ("stdout-guard", stdout_guard_span()),
        ],
    }
}

fn external_governance_graph() -> GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| builder.add_node(prepare_tool_call_node()))
        .and_then(|builder| builder.add_node(permission_gate_node()))
        .and_then(|builder| builder.add_node(stdout_guard_node()))
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("prepare-tool-call").unwrap(),
                NodeId::new("permission-gate").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("permission-gate").unwrap(),
                NodeId::new("stdout-guard").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}

fn prepare_tool_call_node() -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new("prepare-tool-call").unwrap(),
        name: "prepare-tool-call".to_string(),
        gates: vec![Gate::ThresholdGate {
            field: "tool_ready".to_string(),
            min: 1.0,
            decision: Decision::Escalate,
        }],
        default: Decision::Deny,
        combination: GateLogic::FirstMatch,
    }
}

fn permission_gate_node() -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new("permission-gate").unwrap(),
        name: "permission-gate".to_string(),
        gates: vec![
            Gate::ThresholdGate {
                field: "dangerous_without_ui".to_string(),
                min: 1.0,
                decision: Decision::Deny,
            },
            Gate::ThresholdGate {
                field: "dangerous_user_rejected".to_string(),
                min: 1.0,
                decision: Decision::Deny,
            },
            Gate::ThresholdGate {
                field: "dangerous_user_approved".to_string(),
                min: 1.0,
                decision: Decision::Escalate,
            },
            Gate::ExactMatch {
                value: "bash".to_string(),
                decision: Decision::Escalate,
            },
        ],
        default: Decision::Escalate,
        combination: GateLogic::FirstMatch,
    }
}

fn stdout_guard_node() -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new("stdout-guard").unwrap(),
        name: "stdout-guard".to_string(),
        gates: vec![Gate::ThresholdGate {
            field: "stdout_taken_over".to_string(),
            min: 1.0,
            decision: Decision::Permit,
        }],
        default: Decision::Deny,
        combination: GateLogic::FirstMatch,
    }
}

fn audited_claims() -> Vec<GovernanceClaim> {
    vec![
        claim(
            "safe-bash",
            "bash",
            Some("echo ok"),
            metrics([
                ("tool_ready", 1.0),
                ("dangerous_without_ui", 0.0),
                ("dangerous_user_rejected", 0.0),
                ("dangerous_user_approved", 0.0),
                ("stdout_taken_over", 1.0),
            ]),
        ),
        claim(
            "dangerous-no-ui",
            "bash",
            Some("rm -rf /tmp/demo"),
            metrics([
                ("tool_ready", 1.0),
                ("dangerous_without_ui", 1.0),
                ("dangerous_user_rejected", 0.0),
                ("dangerous_user_approved", 0.0),
                ("stdout_taken_over", 1.0),
            ]),
        ),
        claim(
            "dangerous-user-rejected",
            "bash",
            Some("sudo ls /root"),
            metrics([
                ("tool_ready", 1.0),
                ("dangerous_without_ui", 0.0),
                ("dangerous_user_rejected", 1.0),
                ("dangerous_user_approved", 0.0),
                ("stdout_taken_over", 1.0),
            ]),
        ),
        claim(
            "dangerous-user-approved",
            "bash",
            Some("chmod 777 /tmp/demo"),
            metrics([
                ("tool_ready", 1.0),
                ("dangerous_without_ui", 0.0),
                ("dangerous_user_rejected", 0.0),
                ("dangerous_user_approved", 1.0),
                ("stdout_taken_over", 1.0),
            ]),
        ),
        claim(
            "non-bash-tool",
            "readFile",
            None,
            metrics([
                ("tool_ready", 1.0),
                ("dangerous_without_ui", 0.0),
                ("dangerous_user_rejected", 0.0),
                ("dangerous_user_approved", 0.0),
                ("stdout_taken_over", 1.0),
            ]),
        ),
        claim(
            "stdout-unguarded",
            "bash",
            Some("echo bypass"),
            metrics([
                ("tool_ready", 1.0),
                ("dangerous_without_ui", 0.0),
                ("dangerous_user_rejected", 0.0),
                ("dangerous_user_approved", 0.0),
                ("stdout_taken_over", 0.0),
            ]),
        ),
        claim(
            "invalid-tool-call",
            "bash",
            Some("echo schema mismatch"),
            metrics([
                ("tool_ready", 0.0),
                ("dangerous_without_ui", 0.0),
                ("dangerous_user_rejected", 0.0),
                ("dangerous_user_approved", 0.0),
                ("stdout_taken_over", 1.0),
            ]),
        ),
    ]
}

fn claim(
    claimant_id: &str,
    action: &str,
    content: Option<&str>,
    metrics: BTreeMap<String, f64>,
) -> GovernanceClaim {
    GovernanceClaim {
        claimant_id: claimant_id.to_string(),
        strength: 1.0,
        priority_class: Some("tool-call".to_string()),
        path: Some("/workspace/session.ts".to_string()),
        action: Some(action.to_string()),
        content: content.map(str::to_string),
        metrics,
    }
}

fn metrics<const N: usize>(pairs: [(&str, f64); N]) -> BTreeMap<String, f64> {
    pairs
        .into_iter()
        .map(|(field, value)| (field.to_string(), value))
        .collect()
}

fn final_decisions(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> BTreeMap<String, Decision> {
    traverse(graph, claims)
        .unwrap()
        .final_decisions
        .into_iter()
        .collect()
}

fn join_spans(spans: &[(&'static str, SourceSpan)]) -> String {
    spans
        .iter()
        .map(|(label, span)| format!("{label}: {span}"))
        .collect::<Vec<_>>()
        .join("; ")
}

fn prepare_tool_call_span() -> SourceSpan {
    SourceSpan {
        relative_path: "packages/agent/src/agent-loop.ts",
        start_line: 479,
        end_line: 505,
    }
}

fn permission_gate_span() -> SourceSpan {
    SourceSpan {
        relative_path: "packages/coding-agent/examples/extensions/permission-gate.ts",
        start_line: 11,
        end_line: 29,
    }
}

fn stdout_guard_span() -> SourceSpan {
    SourceSpan {
        relative_path: "packages/coding-agent/src/core/output-guard.ts",
        start_line: 9,
        end_line: 70,
    }
}
