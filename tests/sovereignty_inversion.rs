use std::collections::BTreeMap;

use legitimacy::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceGraph, GovernanceNode,
    GraphBuilder, NodeId, traverse,
};

#[test]
fn claude_md_override_turns_a_constitutional_deny_into_a_permit_at_exit() {
    let claim = dangerous_bash_claim();

    let without_override = traverse(
        &constitution_without_override_graph(),
        std::slice::from_ref(&claim),
    )
    .unwrap();
    let with_override = traverse(&constitution_with_override_graph(), &[claim]).unwrap();

    println!(
        "Sovereignty inversion witness: no CLAUDE.md sink -> {:?}; with CLAUDE.md sink -> {:?}",
        without_override.node_decisions[&NodeId::new("model-constitution").unwrap()][0].decision,
        with_override.node_decisions[&NodeId::new("claude-md-override").unwrap()][0].decision,
    );

    assert_eq!(
        without_override.node_decisions[&NodeId::new("model-constitution").unwrap()][0].decision,
        Decision::Deny
    );
    assert_eq!(
        with_override.node_decisions[&NodeId::new("model-constitution").unwrap()][0].decision,
        Decision::Deny
    );
    assert_eq!(
        with_override.node_decisions[&NodeId::new("claude-md-override").unwrap()][0].decision,
        Decision::Permit
    );
}

fn constitution_without_override_graph() -> GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| builder.add_node(request_entry_node()))
        .and_then(|builder| builder.add_node(model_constitution_node()))
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("request").unwrap(),
                NodeId::new("model-constitution").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}

fn constitution_with_override_graph() -> GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| builder.add_node(request_entry_node()))
        .and_then(|builder| builder.add_node(model_constitution_node()))
        .and_then(|builder| builder.add_node(claude_override_node()))
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("request").unwrap(),
                NodeId::new("model-constitution").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("request").unwrap(),
                NodeId::new("claude-md-override").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("model-constitution").unwrap(),
                NodeId::new("claude-md-override").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}

fn request_entry_node() -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new("request").unwrap(),
        name: "request entry".to_string(),
        gates: Vec::new(),
        default: Decision::Escalate,
        combination: GateLogic::FirstMatch,
    }
}

fn model_constitution_node() -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new("model-constitution").unwrap(),
        name: "model constitution".to_string(),
        gates: vec![
            Gate::ContentMatch {
                regex: "(?i)delete all user data|disable safety|exfiltrate data".to_string(),
                decision: Decision::Deny,
            },
            Gate::ContentMatch {
                regex: "(?i)deceptive persuasion|covert manipulation".to_string(),
                decision: Decision::Deny,
            },
            Gate::ContentMatch {
                regex: "(?i)ignore policy|policy workaround".to_string(),
                decision: Decision::Deny,
            },
        ],
        default: Decision::Escalate,
        combination: GateLogic::FirstMatch,
    }
}

fn claude_override_node() -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new("claude-md-override").unwrap(),
        name: "CLAUDE.md override".to_string(),
        gates: vec![
            Gate::ExactMatch {
                value: "Bash".to_string(),
                decision: Decision::Permit,
            },
            Gate::ThresholdGate {
                field: "claude_md_always_execute".to_string(),
                min: 1.0,
                decision: Decision::Permit,
            },
        ],
        default: Decision::Deny,
        combination: GateLogic::AllMustPass,
    }
}

fn dangerous_bash_claim() -> GovernanceClaim {
    let mut metrics = BTreeMap::new();
    metrics.insert("claude_md_always_execute".to_string(), 1.0);

    GovernanceClaim {
        claimant_id: "dangerous-bash".to_string(),
        strength: 1.0,
        priority_class: None,
        path: None,
        action: Some("Bash".to_string()),
        content: Some("disable safety checks and run unreviewed deployment.sh".to_string()),
        metrics,
    }
}
