use std::collections::BTreeMap;

use legitimacy::{
    Decision, EdgeTransform, GovernanceClaim, GovernanceNode, GraphBuilder, NodeId,
    graph::{Gate, GateLogic},
    paradox::{GraphParadoxType, compositional_alabama, feedback_monotonicity, path_dependence},
};

#[test]
fn compositional_alabama_disappears_when_sink_permits_are_terminal() {
    let graph = composition_fixture_graph();

    let violation = compositional_alabama(&graph, &graph_claims()).unwrap();

    assert!(
        violation.is_none(),
        "unexpected compositional Alabama witness"
    );
}

#[test]
fn feedback_monotonicity_detects_cycle_regression_on_composition_fixture() {
    let graph = GraphBuilder::new()
        .and_then(|builder| builder.add_node(threshold_entry("a")))
        .and_then(|builder| builder.add_node(peer_exit("b")))
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("a").unwrap(),
                NodeId::new("b").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("b").unwrap(),
                NodeId::new("a").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap();

    let violation = feedback_monotonicity(&graph, &graph_claims())
        .unwrap()
        .expect("expected feedback monotonicity witness");

    assert_eq!(
        violation.paradox_type,
        GraphParadoxType::FeedbackMonotonicity
    );
    assert!(violation.description.contains("alice"));
    assert!(violation.description.contains("bob"));
    assert_eq!(violation.original_decisions["bob"], Decision::Permit);
    assert_eq!(violation.perturbed_decisions["bob"], Decision::Deny);
}

#[test]
fn path_dependence_disappears_with_most_restrictive_merge() {
    let graph = GraphBuilder::new()
        .and_then(|builder| builder.add_node(threshold_entry("a")))
        .and_then(|builder| builder.add_node(peer_exit("b")))
        .and_then(|builder| builder.add_node(strict_exit("c")))
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("a").unwrap(),
                NodeId::new("b").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("a").unwrap(),
                NodeId::new("c").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap();

    let violation = path_dependence(&graph, &graph_claims()).unwrap();

    assert!(violation.is_none(), "unexpected path dependence witness");
}

fn composition_fixture_graph() -> legitimacy::GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| builder.add_node(threshold_entry("a")))
        .and_then(|builder| builder.add_node(peer_exit("b")))
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("a").unwrap(),
                NodeId::new("b").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}

fn threshold_entry(id: &str) -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new(id).unwrap(),
        name: id.to_string(),
        gates: vec![Gate::ThresholdGate {
            field: "strength".to_string(),
            min: 0.5,
            decision: Decision::Escalate,
        }],
        default: Decision::Deny,
        combination: GateLogic::FirstMatch,
    }
}

fn peer_exit(id: &str) -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new(id).unwrap(),
        name: id.to_string(),
        gates: vec![Gate::PeerRelative {
            field: "strength".to_string(),
            percentile: 0.5,
            decision: Decision::Permit,
        }],
        default: Decision::Deny,
        combination: GateLogic::AnyMustPass,
    }
}

fn strict_exit(id: &str) -> GovernanceNode {
    GovernanceNode::Threshold {
        id: NodeId::new(id).unwrap(),
        name: id.to_string(),
        threshold: 0.8,
        field: "strength".to_string(),
    }
}

fn graph_claims() -> Vec<GovernanceClaim> {
    vec![claim("alice", 0.4), claim("bob", 0.55), claim("carol", 0.9)]
}

fn claim(claimant_id: &str, strength: f64) -> GovernanceClaim {
    GovernanceClaim {
        claimant_id: claimant_id.to_string(),
        strength,
        priority_class: None,
        path: None,
        action: None,
        content: None,
        metrics: BTreeMap::new(),
    }
}
