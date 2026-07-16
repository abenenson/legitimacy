use super::analyze_graph;
use crate::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceNode, GraphBuilder, NodeId, Verdict,
    axioms::kernel::{AxiomVerdict, KernelAxiom},
    extract::audit::kernel_axiom_result,
};
use std::path::Path;

#[test]
fn analyze_graph_reports_cycles_as_findings_instead_of_crashing() {
    let graph = GraphBuilder::new()
        .and_then(|builder| builder.add_node(threshold_entry("spawn")))
        .and_then(|builder| builder.add_node(peer_gate("spawn_internal")))
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("spawn").unwrap(),
                NodeId::new("spawn_internal").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("spawn_internal").unwrap(),
                NodeId::new("spawn").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap();

    let report = analyze_graph(Path::new("/tmp/cycle"), graph)
        .expect("cyclic extraction should return a report");

    assert_eq!(report.audit.cycles.len(), 1);
    assert!(
        report
            .audit
            .cycles
            .iter()
            .any(|finding| finding.nodes.iter().any(|node| node == "spawn")
                && finding.nodes.iter().any(|node| node == "spawn_internal"))
    );
    assert!(
        report
            .audit
            .axiom_results
            .iter()
            .any(|result| result.axiom == "graph nonvacuity")
    );
    assert!(report.audit.axiom_results.iter().all(|result| {
        result.axiom == "graph nonvacuity"
            || (result.verdict.is_none() && result.skipped_reason.is_some())
    }));
    assert!(
        report
            .audit
            .cycles
            .iter()
            .all(|finding| matches!(finding.verdict, Verdict::Rejected { .. }))
    );
    assert_eq!(report.audit.paradox_results.len(), 3);
    assert!(report.audit.spectral.is_some());
    assert_eq!(report.audit.protocol_assessment.current_state, "UNDECLARED");
    assert!(report.audit.protocol_assessment.can_declare);
    assert!(!report.audit.protocol_assessment.can_extract_compile);
}

#[test]
fn analyze_graph_includes_spectral_and_factor_exposure() {
    let graph = GraphBuilder::new()
        .and_then(|builder| builder.add_node(threshold_entry("entry")))
        .and_then(|builder| builder.add_node(peer_gate("review")))
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("entry").unwrap(),
                NodeId::new("review").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap();

    let report = analyze_graph(Path::new("/tmp/spectral-test"), graph)
        .expect("acyclic extraction should return a report");

    assert!(report.audit.spectral.is_some());
    let spectral = report.audit.spectral.unwrap();
    assert_eq!(spectral.node_count, 2);
    assert!(spectral.is_connected);
    assert!(spectral.spectral_gap.is_some());
    assert!(report.audit.factor_exposure.consistency >= 0.0);
    assert!(report.audit.factor_exposure.solidarity >= 0.0);
    assert!(report.audit.factor_exposure.monotonicity >= 0.0);
    assert!(report.audit.factor_exposure.strategyproofness >= 0.0);
    assert!(report.audit.factor_exposure.nonvacuity >= 0.0);
    assert_eq!(report.audit.protocol_assessment.current_state, "UNDECLARED");
    assert!(report.audit.protocol_assessment.can_declare);
    assert!(report.audit.protocol_assessment.can_extract_compile);
}

#[test]
fn analyze_graph_rejects_mixed_permit_and_escalate_nonvacuity() {
    let graph = GraphBuilder::new()
        .and_then(|builder| builder.add_node(mixed_nonvacuity_entry("entry")))
        .and_then(GraphBuilder::build)
        .unwrap();

    let report =
        analyze_graph(Path::new("/tmp/nonvacuity-escalate"), graph).expect("graph should analyze");
    let result = report
        .audit
        .axiom_results
        .iter()
        .find(|result| result.axiom == "graph nonvacuity")
        .and_then(|result| result.verdict.as_ref())
        .expect("nonvacuity verdict should be present");

    let Verdict::Rejected { counterexample, .. } = result else {
        panic!("mixed permit/escalate graph should fail nonvacuity");
    };
    assert!(counterexample.description.contains("Escalate"));
}

#[test]
fn kernel_skipped_axiom_populates_extraction_skip_reason() {
    let result = kernel_axiom_result(AxiomVerdict::skipped(
        KernelAxiom::Observable,
        "graph has no branching decision surface",
    ));

    assert_eq!(result.axiom, "graph observable determinacy");
    assert!(result.verdict.is_none());
    assert_eq!(
        result.skipped_reason.as_deref(),
        Some("graph has no branching decision surface")
    );
}

#[test]
fn skipped_axiom_serializes_without_pass_zero_verdict() {
    let result = kernel_axiom_result(AxiomVerdict::skipped(
        KernelAxiom::Observable,
        "graph has no branching decision surface",
    ));

    let encoded = serde_json::to_value(&result).unwrap();

    assert_eq!(encoded["axiom"], "graph observable determinacy");
    assert!(encoded.get("verdict").is_none());
    assert_eq!(
        encoded["skipped_reason"],
        "graph has no branching decision surface"
    );
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

fn peer_gate(id: &str) -> GovernanceNode {
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

fn mixed_nonvacuity_entry(id: &str) -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new(id).unwrap(),
        name: id.to_string(),
        gates: vec![
            Gate::ExactMatch {
                value: "safe_action".to_string(),
                decision: Decision::Permit,
            },
            Gate::ExactMatch {
                value: "needs_review".to_string(),
                decision: Decision::Escalate,
            },
        ],
        default: Decision::Deny,
        combination: GateLogic::FirstMatch,
    }
}
