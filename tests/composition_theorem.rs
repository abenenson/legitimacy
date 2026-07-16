use std::collections::BTreeMap;

use legitimacy::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceNode, GraphBuilder,
    NodeId, Verdict,
    axioms::{
        binary::{BinaryDelta, check_binary_monotonicity},
        graph::monotonicity::check_graph_monotonicity,
    },
};

#[test]
fn composition_theorem_counterexample_breaks_graph_monotonicity() {
    // Node A is individually monotone: crossing the 0.5 threshold escalates the
    // strengthened claimant downstream, but does not hurt that claimant in isolation.
    let a = GovernanceNode::Binary {
        id: NodeId::new("a").unwrap(),
        name: "threshold-entry".to_string(),
        gates: vec![Gate::ThresholdGate {
            field: "strength".to_string(),
            min: 0.5,
            decision: Decision::Escalate,
        }],
        default: Decision::Deny,
        combination: GateLogic::FirstMatch,
    };

    // Node B is also individually monotone on a fixed claimant set: increasing your own
    // strength cannot lower your own peer-relative rank.
    let b = GovernanceNode::Binary {
        id: NodeId::new("b").unwrap(),
        name: "peer-relative-exit".to_string(),
        gates: vec![Gate::PeerRelative {
            field: "strength".to_string(),
            percentile: 0.5,
            decision: Decision::Permit,
        }],
        default: Decision::Deny,
        combination: GateLogic::AnyMustPass,
    };

    let deltas = [BinaryDelta {
        field: "strength".to_string(),
        delta: 0.2,
    }];

    assert!(matches!(
        check_binary_monotonicity(&a, &a_claims(), &deltas),
        Ok(Verdict::Admissible { .. })
    ));
    assert!(matches!(
        check_binary_monotonicity(&b, &b_claims(), &deltas),
        Ok(Verdict::Admissible { .. })
    ));

    let graph = GraphBuilder::new()
        .and_then(|builder| builder.add_node(a))
        .and_then(|builder| builder.add_node(b))
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("a").unwrap(),
                NodeId::new("b").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap();

    let verdict = check_graph_monotonicity(&graph, &graph_claims(), &deltas).unwrap();

    // Baseline:
    // - Alice is too weak for A, so she never reaches B.
    // - Bob (0.55) and Carol (0.90) do reach B, and Bob is still above the 50th percentile.
    //
    // After strengthening Alice from 0.40 -> 0.60:
    // - A now forwards Alice into B's competition set.
    // - Alice enters above Bob, so Bob's peer-relative rank drops from 1/2 to 1/3.
    // - Bob flips from Permit to Deny at the graph exit.
    //
    // That is the composition failure: each node is monotone on its own, but composing
    // them makes monotonicity fail because A changes who is allowed to compete inside B.
    assert!(matches!(verdict, Verdict::Rejected { .. }));
}

fn a_claims() -> Vec<GovernanceClaim> {
    vec![claim("alice", 0.4), claim("bob", 0.55), claim("carol", 0.9)]
}

fn b_claims() -> Vec<GovernanceClaim> {
    vec![claim("bob", 0.55), claim("carol", 0.9)]
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
