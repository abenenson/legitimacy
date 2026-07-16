//! Canonical implementation of the `graph compositional safety` axiom.
//!
//! Operational definition: a claim denied by the audited graph remains denied
//! after appending an additional permissive governance stage. This is the
//! graph-side executable projection of kernel `CompositionalSafety`: Lean names
//! the structural deny-bottom invariant of final-decision merging and proves the
//! richer no-new-entry suffix corollary under an explicit suffix-merge traversal
//! contract, while this runtime check exercises the canonical one-stage
//! permissive suffix that could otherwise revive a denial.
//!
//! Canonical wire string: `"graph compositional safety"`.
//!
//! Skip convention: this check returns `AxiomVerdict::Skipped` for inputs that
//! were skipped rather than exhaustively exercised. Cyclic graphs are skipped
//! and handled by the
//! dedicated cycle and nonvacuity probes. Empty graphs are also skipped because
//! there is no denial surface to extend with the permissive suffix; only
//! nonempty acyclic graphs with positive `perturbations_tested` have been
//! mechanically checked for denial preservation under extension.

use super::{AxiomVerdict, KernelAxiom};
use crate::{
    Counterexample, Decision, EdgeTransform, GateLogic, GovernanceClaim, GovernanceEdge,
    GovernanceGraph, GovernanceNode, LegitimacyError, NodeId,
    axioms::diagnostics::graph::{
        convert_claims, decision_allocation, final_decisions, graph_estate,
    },
    graph::cycle::detect_cycles,
};
use std::collections::BTreeSet;

pub fn check_graph_compositional_safety(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<AxiomVerdict, LegitimacyError> {
    if !detect_cycles(graph)?.is_empty() {
        return Ok(AxiomVerdict::skipped(
            KernelAxiom::CompositionalSafety,
            "cyclic graphs are handled by cycle and nonvacuity probes",
        ));
    }
    if graph.nodes.is_empty() {
        return Ok(AxiomVerdict::skipped(
            KernelAxiom::CompositionalSafety,
            "empty graph has no denied decision surface to extend",
        ));
    }

    let original = final_decisions(graph, claims)?;
    let appended_graph = append_permissive_stage(graph)?;
    let appended = final_decisions(&appended_graph, claims)?;

    for claim in claims {
        let before = original
            .get(&claim.claimant_id)
            .unwrap_or(&Decision::Escalate);
        let after = appended
            .get(&claim.claimant_id)
            .unwrap_or(&Decision::Escalate);
        if matches!(before, Decision::Deny) && !matches!(after, Decision::Deny) {
            return compositional_rejection(
                claims,
                &original,
                &appended,
                &format!(
                    "appending a permissive governance stage changed '{}' from Deny to {:?}",
                    claim.claimant_id, after
                ),
                "COMPOSITIONAL SAFETY requires denied claims to remain denied under graph extension",
            );
        }
    }

    Ok(AxiomVerdict::pass(
        KernelAxiom::CompositionalSafety,
        claims.len(),
    ))
}

fn append_permissive_stage(graph: &GovernanceGraph) -> Result<GovernanceGraph, LegitimacyError> {
    let sink = fresh_sink_id(graph)?;
    let mut appended = graph.clone();
    appended.nodes.insert(
        sink.clone(),
        GovernanceNode::Binary {
            id: sink.clone(),
            name: "kernel-compositional-permit-suffix".to_string(),
            gates: Vec::new(),
            default: Decision::Permit,
            combination: GateLogic::FirstMatch,
        },
    );

    let sources = terminal_nodes(graph);
    for source in sources {
        appended.edges.push(GovernanceEdge {
            from: source,
            to: sink.clone(),
            transform: EdgeTransform::PassThrough,
        });
    }

    Ok(appended)
}

fn terminal_nodes(graph: &GovernanceGraph) -> Vec<NodeId> {
    let nonterminals = graph
        .edges
        .iter()
        .map(|edge| edge.from.clone())
        .collect::<BTreeSet<_>>();
    graph
        .nodes
        .keys()
        .filter(|node_id| !nonterminals.contains(*node_id))
        .cloned()
        .collect()
}

fn fresh_sink_id(graph: &GovernanceGraph) -> Result<NodeId, LegitimacyError> {
    for index in 0..=graph.nodes.len() {
        let candidate = NodeId::new(format!("__kernel_compositional_append_{index}"))?;
        if !graph.nodes.contains_key(&candidate) {
            return Ok(candidate);
        }
    }
    NodeId::new("__kernel_compositional_append_fallback")
}

fn compositional_rejection(
    claims: &[GovernanceClaim],
    original: &std::collections::BTreeMap<String, Decision>,
    appended: &std::collections::BTreeMap<String, Decision>,
    description: &str,
    violation: &str,
) -> Result<AxiomVerdict, LegitimacyError> {
    Ok(AxiomVerdict::fail(
        KernelAxiom::CompositionalSafety,
        description,
        Counterexample {
            description: description.to_string(),
            original_claims: convert_claims(claims)?,
            original_estate: graph_estate()?,
            original_allocation: decision_allocation(claims, original)?,
            perturbed_claims: convert_claims(claims)?,
            perturbed_estate: graph_estate()?,
            perturbed_allocation: decision_allocation(claims, appended)?,
            violation: violation.to_string(),
        },
    ))
}
