//! Canonical implementation of the `graph corrigibility` axiom.
//!
//! Operational definition: the extracted graph remains evaluable under the
//! emergency supervisory override fragment used by the protocol surface
//! (`pause`, `deny`, and `permit`). This is the graph-side faithful projection of
//! kernel `Corrigible`: the kernel predicate proves algebra preservation over a
//! state/action space, while the runtime graph projection checks that the graph
//! can actually be overridden into bounded pause/deny/permit control surfaces.
//!
//! Canonical wire string: `"graph corrigibility"`.
//!
//! Cyclic graphs are skipped here and handled by the dedicated cycle and
//! nonvacuity probes.

use super::{AxiomVerdict, KernelAxiom};
use crate::{
    Counterexample, Decision, EdgeTransform, GateLogic, GovernanceClaim, GovernanceGraph,
    GovernanceNode, LegitimacyError,
    axioms::diagnostics::graph::{convert_claims, decision_allocation, graph_estate},
    graph::{cycle::detect_cycles, traverse::traverse},
};

pub fn check_graph_corrigibility(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<AxiomVerdict, LegitimacyError> {
    if !detect_cycles(graph)?.is_empty() {
        return Ok(AxiomVerdict::skipped(
            KernelAxiom::Corrigible,
            "cyclic graphs are handled by cycle and nonvacuity probes",
        ));
    }
    if graph.nodes.is_empty() {
        return corrigibility_rejection(
            claims,
            "graph has no governance nodes for supervisory override",
            "CORRIGIBLE requires a nonempty graph surface that can be paused, denied, or permitted",
        );
    }

    let pause_graph = constant_override_graph(graph, Decision::Escalate);
    traverse(&pause_graph, claims)?;
    let deny_graph = constant_override_graph(graph, Decision::Deny);
    traverse(&deny_graph, claims)?;
    let permit_graph = constant_override_graph(graph, Decision::Permit);
    traverse(&permit_graph, claims)?;

    Ok(AxiomVerdict::pass(KernelAxiom::Corrigible, 3))
}

fn constant_override_graph(graph: &GovernanceGraph, decision: Decision) -> GovernanceGraph {
    let nodes = graph
        .nodes
        .keys()
        .map(|node_id| {
            (
                node_id.clone(),
                GovernanceNode::Binary {
                    id: node_id.clone(),
                    name: format!("supervisory-override-{node_id}"),
                    gates: Vec::new(),
                    default: decision.clone(),
                    combination: GateLogic::FirstMatch,
                },
            )
        })
        .collect();
    let edges = graph
        .edges
        .iter()
        .map(|edge| crate::GovernanceEdge {
            from: edge.from.clone(),
            to: edge.to.clone(),
            transform: EdgeTransform::PassThrough,
        })
        .collect();
    GovernanceGraph { nodes, edges }
}

fn corrigibility_rejection(
    claims: &[GovernanceClaim],
    description: &str,
    violation: &str,
) -> Result<AxiomVerdict, LegitimacyError> {
    Ok(AxiomVerdict::fail(
        KernelAxiom::Corrigible,
        description,
        Counterexample {
            description: description.to_string(),
            original_claims: convert_claims(claims)?,
            original_estate: graph_estate()?,
            original_allocation: decision_allocation(claims, &Default::default())?,
            perturbed_claims: convert_claims(claims)?,
            perturbed_estate: graph_estate()?,
            perturbed_allocation: decision_allocation(claims, &Default::default())?,
            violation: violation.to_string(),
        },
    ))
}
