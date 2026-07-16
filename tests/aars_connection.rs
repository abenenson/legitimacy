//! Regression tests for the AARS decomposition example: a denied direct solve
//! can be decomposed into permitted lookup/submit steps, exposing the
//! monotonicity pressure the governance graph is meant to catch.

use std::collections::BTreeMap;

use legitimacy::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceGraph, GovernanceNode,
    GraphBuilder, NodeId, Verdict,
    axioms::{binary::BinaryDelta, graph::monotonicity::check_graph_monotonicity},
    traverse,
};

#[test]
fn aars_decomposition_turns_denied_solve_goal_into_permitted_lookup_plan() {
    let graph = aars_reward_hacking_graph();

    let monolithic = traverse(&graph, &[solve_the_problem_claim()]).unwrap();
    let decomposed = traverse(&graph, &lookup_most_common_plan()).unwrap();

    assert_eq!(
        monolithic.final_decisions["solve-the-problem"],
        Decision::Deny
    );
    assert_eq!(
        monolithic.node_decisions[&NodeId::new("task-evaluator").unwrap()][0].decision,
        Decision::Deny
    );

    assert_eq!(
        decomposed.final_decisions["lookup-most-common-answer"],
        Decision::Permit
    );
    assert_eq!(
        decomposed.final_decisions["submit-most-common-answer"],
        Decision::Permit
    );
    assert_eq!(
        decomposed.node_decisions[&NodeId::new("task-evaluator").unwrap()]
            .iter()
            .map(|decision| decision.decision.clone())
            .collect::<Vec<_>>(),
        vec![Decision::Escalate, Decision::Escalate]
    );
    assert_eq!(
        decomposed.node_decisions[&NodeId::new("method-validator").unwrap()]
            .iter()
            .map(|decision| decision.decision.clone())
            .collect::<Vec<_>>(),
        vec![Decision::Permit, Decision::Permit]
    );
}

#[test]
fn aars_lookup_heuristic_is_a_compositional_monotonicity_violation() {
    let graph = aars_reward_hacking_graph();
    let weak_claim = lookup_claim("lookup-most-common-answer");
    let strong_claim = solve_like_lookup_claim("lookup-most-common-answer");
    let deltas = [BinaryDelta {
        field: "solve_directly".to_string(),
        delta: 1.0,
    }];

    let weak_result = traverse(&graph, std::slice::from_ref(&weak_claim)).unwrap();
    let strong_result = traverse(&graph, std::slice::from_ref(&strong_claim)).unwrap();
    let verdict = check_graph_monotonicity(&graph, &[weak_claim], &deltas).unwrap();

    assert_eq!(
        weak_result.final_decisions["lookup-most-common-answer"],
        Decision::Permit
    );
    assert_eq!(
        strong_result.final_decisions["lookup-most-common-answer"],
        Decision::Deny
    );
    assert!(
        matches!(verdict, Verdict::Rejected { .. }),
        "strengthening the claim back toward actually solving the task should worsen the outcome"
    );
}

fn aars_reward_hacking_graph() -> GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Binary {
                id: NodeId::new("task-evaluator").unwrap(),
                name: "task evaluator".to_string(),
                gates: vec![Gate::ThresholdGate {
                    field: "most_common_answer_score".to_string(),
                    min: 0.8,
                    decision: Decision::Escalate,
                }],
                default: Decision::Deny,
                combination: GateLogic::FirstMatch,
            })
        })
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Binary {
                id: NodeId::new("method-validator").unwrap(),
                name: "method validator".to_string(),
                gates: vec![Gate::ThresholdGate {
                    field: "solve_directly".to_string(),
                    min: 0.8,
                    decision: Decision::Deny,
                }],
                default: Decision::Permit,
                combination: GateLogic::FirstMatch,
            })
        })
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("task-evaluator").unwrap(),
                NodeId::new("method-validator").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}

fn solve_the_problem_claim() -> GovernanceClaim {
    claim("solve-the-problem", 0.0, 1.0)
}

fn lookup_most_common_plan() -> Vec<GovernanceClaim> {
    vec![
        lookup_claim("lookup-most-common-answer"),
        lookup_claim("submit-most-common-answer"),
    ]
}

fn lookup_claim(id: &str) -> GovernanceClaim {
    claim(id, 1.0, 0.0)
}

fn solve_like_lookup_claim(id: &str) -> GovernanceClaim {
    claim(id, 1.0, 1.0)
}

fn claim(id: &str, most_common_answer_score: f64, solve_directly: f64) -> GovernanceClaim {
    GovernanceClaim {
        claimant_id: id.to_string(),
        strength: 1.0,
        priority_class: Some("research".to_string()),
        path: None,
        action: Some("Research".to_string()),
        content: None,
        metrics: BTreeMap::from([
            (
                "most_common_answer_score".to_string(),
                most_common_answer_score,
            ),
            ("solve_directly".to_string(), solve_directly),
        ]),
    }
}
