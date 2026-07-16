//! Canonical implementation of the `graph nonvacuity` (liveness) axiom.
//!
//! This is the single canonical implementation: both `crate::extract::audit`
//! and `crate::protocol::transitions` re-export this entry through
//! `crate::axioms::kernel::check_graph_nonvacuity`. The pre-existing
//! `src/extract/nonvacuity.rs` and `src/protocol/nonvacuity.rs` modules
//! were consolidated into this module to eliminate the split-brain.
//!
//! Liveness contract: at least one synthetic claim reaches a terminal
//! `Permit` disposition (or, when the graph has cycles, the iterated cycle
//! probe converges to a non-escalation fixed point) and no examined claim
//! remains in `Escalate` after traversal.

use super::{AxiomVerdict, KernelAxiom};
use crate::{
    Allocation, Claim, Counterexample, Decision, Estate, GovernanceClaim, GovernanceGraph,
    LegitimacyError, ValidAllocation,
    extract::audit::{synthetic_claims_for_cycle, synthetic_claims_for_cycles},
    graph::{iterate_cycle, traverse},
};
use std::collections::{BTreeMap, BTreeSet};

pub fn check_graph_nonvacuity(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    cycles: &[Vec<crate::NodeId>],
) -> Result<AxiomVerdict, LegitimacyError> {
    if graph.nodes.is_empty() {
        return nonvacuity_rejection(
            claims,
            "graph has no governance nodes",
            "NON-VACUOUS requires a nonempty governance graph with at least one permitting disposition",
            &[],
        );
    }

    let mut permit_found = false;
    let mut perturbations_tested = claims.len();

    if cycles.is_empty() {
        let traversal = traverse(graph, claims)?;
        let nonterminal = nonterminal_claimants(claims, &traversal.final_decisions);
        if !nonterminal.is_empty() {
            return nonvacuity_rejection(
                claims,
                &format!(
                    "{} examined claims remained in Escalate after traversal: {}",
                    nonterminal.len(),
                    nonterminal.join(", ")
                ),
                "NON-VACUOUS requires every governed claim to reach a terminal Permit or Deny disposition",
                &nonterminal,
            );
        }
        permit_found = claims.iter().any(|claim| {
            traversal
                .final_decisions
                .get(&claim.claimant_id)
                .is_some_and(|decision| matches!(decision, Decision::Permit))
        });
    } else {
        for cycle in cycles {
            let cycle_claims = synthetic_claims_for_cycle(graph, cycle);
            let result = iterate_cycle(graph, cycle, &cycle_claims, 32, crate::EPSILON)?;
            perturbations_tested += result.iterations;
            if !result.converged {
                let deadlocked = cycle_claims
                    .iter()
                    .map(|claim| claim.claimant_id.clone())
                    .collect::<Vec<_>>();
                return nonvacuity_rejection(
                    &cycle_claims,
                    &format!(
                        "cycle {:?} deadlocked before reaching terminal dispositions",
                        cycle
                    ),
                    "NON-VACUOUS rejects deadlocked governance cycles",
                    &deadlocked,
                );
            }

            let fixed_point_decisions = result
                .fixed_point_decisions
                .iter()
                .map(|(claimant_id, decision)| (claimant_id.clone(), decision.clone()))
                .collect::<BTreeMap<_, _>>();
            let nonterminal = nonterminal_claimants(&cycle_claims, &fixed_point_decisions);
            if !nonterminal.is_empty() {
                return nonvacuity_rejection(
                    &cycle_claims,
                    &format!(
                        "cycle {:?} left {} synthetic claims in Escalate: {}",
                        cycle,
                        nonterminal.len(),
                        nonterminal.join(", ")
                    ),
                    "NON-VACUOUS rejects permanent escalation loops",
                    &nonterminal,
                );
            }

            if cycle_claims.iter().any(|claim| {
                fixed_point_decisions
                    .get(&claim.claimant_id)
                    .is_some_and(|decision| matches!(decision, Decision::Permit))
            }) {
                permit_found = true;
            }
        }
    }

    if permit_found {
        return Ok(AxiomVerdict::pass(
            KernelAxiom::NonVacuous,
            perturbations_tested,
        ));
    }

    let refusal_claims = if cycles.is_empty() {
        claims.to_vec()
    } else {
        synthetic_claims_for_cycles(graph, cycles)
    };
    nonvacuity_rejection(
        &refusal_claims,
        if cycles.is_empty() {
            "all examined claims reached Deny; the graph refused every governed claim"
        } else {
            "all synthetic cycle probes reached Deny; the graph refused every governed claim"
        },
        if cycles.is_empty() {
            "NON-VACUOUS requires at least one examined claim to reach Permit"
        } else {
            "NON-VACUOUS requires at least one synthetic cycle probe to reach Permit"
        },
        &[],
    )
}

fn nonvacuity_rejection(
    claims: &[GovernanceClaim],
    description: &str,
    violation: &str,
    nonterminal_claimants: &[String],
) -> Result<AxiomVerdict, LegitimacyError> {
    Ok(AxiomVerdict::fail(
        KernelAxiom::NonVacuous,
        description,
        Counterexample {
            description: description.to_string(),
            original_claims: convert_governance_claims(claims)?,
            original_estate: Estate::new(1.0, "decision")?,
            original_allocation: zero_decision_allocation(claims)?,
            perturbed_claims: convert_governance_claims(claims)?,
            perturbed_estate: Estate::new(1.0, "decision")?,
            perturbed_allocation: nonvacuity_liveness_allocation(claims, nonterminal_claimants)?,
            violation: violation.to_string(),
        },
    ))
}

fn nonterminal_claimants(
    claims: &[GovernanceClaim],
    decisions: &BTreeMap<String, Decision>,
) -> Vec<String> {
    let mut nonterminal = claims
        .iter()
        .filter_map(|claim| match decisions.get(&claim.claimant_id) {
            Some(Decision::Permit | Decision::Deny) => None,
            Some(Decision::Escalate) | None => Some(claim.claimant_id.clone()),
        })
        .collect::<Vec<_>>();
    nonterminal.sort();
    nonterminal
}

fn nonvacuity_liveness_allocation(
    claims: &[GovernanceClaim],
    nonterminal_claimants: &[String],
) -> Result<ValidAllocation, LegitimacyError> {
    let nonterminal = nonterminal_claimants.iter().collect::<BTreeSet<_>>();
    let stuck_fraction = if claims.is_empty() {
        0.0
    } else {
        nonterminal.len() as f64 / claims.len() as f64
    };

    ValidAllocation::new(
        claims
            .iter()
            .map(|claim| {
                let value = if nonterminal.contains(&claim.claimant_id) {
                    stuck_fraction
                } else {
                    0.0
                };
                (claim.claimant_id.clone(), value)
            })
            .collect::<Allocation>(),
        &convert_governance_claims(claims)?,
    )
}

fn convert_governance_claims(claims: &[GovernanceClaim]) -> Result<Vec<Claim>, LegitimacyError> {
    claims
        .iter()
        .map(|claim| {
            let mut converted = Claim::new(&claim.claimant_id, claim.strength)?;
            for (field, value) in &claim.metrics {
                converted = converted.with_metric(field, *value);
            }
            Ok(converted)
        })
        .collect()
}

fn zero_decision_allocation(
    claims: &[GovernanceClaim],
) -> Result<ValidAllocation, LegitimacyError> {
    ValidAllocation::new(
        claims
            .iter()
            .map(|claim| (claim.claimant_id.clone(), 0.0))
            .collect::<Allocation>(),
        &convert_governance_claims(claims)?,
    )
}
