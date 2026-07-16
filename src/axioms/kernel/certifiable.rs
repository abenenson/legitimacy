//! Canonical implementation of the `graph certifiability` axiom.
//!
//! Operational definition: every audited graph decision has a replayable
//! finite certificate, namely the concrete node-decision trace produced by
//! traversal. This is the graph-side faithful projection of the kernel
//! `Certifiable` predicate, not the bare kernel predicate itself: the Lean
//! predicate quantifies over arbitrary certificate systems, while this runtime
//! projection checks that the extracted governance graph exposes a bounded
//! replay witness for each governed claim.
//!
//! Canonical wire string: `"graph certifiability"`.
//!
//! Cycle handling mirrors `observable`: cyclic graphs are skipped by the graph
//! projection because cycle behavior is witnessed by the dedicated cycle and
//! nonvacuity probes.

use super::{AxiomVerdict, KernelAxiom};
use crate::{
    Counterexample, Decision, GovernanceClaim, GovernanceGraph, LegitimacyError,
    axioms::diagnostics::graph::{convert_claims, decision_allocation, graph_estate},
    graph::{cycle::detect_cycles, node::validate_governance_graph, traverse::traverse},
};
use std::collections::BTreeMap;

pub fn check_graph_certifiability(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<AxiomVerdict, LegitimacyError> {
    if !detect_cycles(graph)?.is_empty() {
        return Ok(AxiomVerdict::skipped(
            KernelAxiom::Certifiable,
            "cyclic graphs are handled by cycle and nonvacuity probes",
        ));
    }
    if graph.nodes.is_empty() {
        return certifiability_rejection(
            claims,
            &BTreeMap::new(),
            "graph has no governance nodes to replay",
            "CERTIFIABLE requires a finite replay certificate for audited graph decisions",
        );
    }

    validate_governance_graph(graph)?;
    let traversal = traverse(graph, claims)?;
    let missing = claims
        .iter()
        .filter(|claim| !traversal.final_decisions.contains_key(&claim.claimant_id))
        .map(|claim| claim.claimant_id.clone())
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        return certifiability_rejection(
            claims,
            &traversal.final_decisions,
            &format!(
                "graph traversal produced no replayable final decision for {}",
                missing.join(", ")
            ),
            "CERTIFIABLE requires every governed claim to have a replayable final decision",
        );
    }

    let replay_steps = traversal
        .node_decisions
        .values()
        .map(Vec::len)
        .sum::<usize>();
    Ok(AxiomVerdict::pass(
        KernelAxiom::Certifiable,
        replay_steps + claims.len(),
    ))
}

fn certifiability_rejection(
    claims: &[GovernanceClaim],
    decisions: &BTreeMap<String, Decision>,
    description: &str,
    violation: &str,
) -> Result<AxiomVerdict, LegitimacyError> {
    Ok(AxiomVerdict::fail(
        KernelAxiom::Certifiable,
        description,
        Counterexample {
            description: description.to_string(),
            original_claims: convert_claims(claims)?,
            original_estate: graph_estate()?,
            original_allocation: decision_allocation(claims, decisions)?,
            perturbed_claims: convert_claims(claims)?,
            perturbed_estate: graph_estate()?,
            perturbed_allocation: decision_allocation(claims, decisions)?,
            violation: violation.to_string(),
        },
    ))
}
