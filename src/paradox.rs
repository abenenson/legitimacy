//! Paradox diagnostics for allocation rules.
//!
//! This module owns rule-level finite-search diagnostics such as claimant
//! addition, population, and priority perturbations. `paradox::graph` owns the
//! graph-level probes such as the append-peer-review compositional-Alabama
//! detector, feedback monotonicity, and path dependence. Both are operational
//! witness finders, not members of the canonical Lean/Rust axiom inventory.

pub mod graph;
pub use graph::{
    GraphParadoxType, GraphParadoxViolation, compositional_alabama, feedback_monotonicity,
    path_dependence,
};

use std::{cmp::Ordering, collections::BTreeMap};

use serde::{Deserialize, Serialize};

use crate::{
    Claim, Claimant, EPSILON, Estate, LegitimacyError, PositiveStrength, Rule, ValidAllocation,
    evaluate_rule, ledger::Ledger,
};

const POPULATION_DELTAS: [f64; 4] = [0.05, 0.10, 0.20, 0.40];

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ParadoxType {
    ClaimantAddition,
    Population,
    Priority,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ParadoxViolation {
    pub paradox_type: ParadoxType,
    pub description: String,
    pub original_allocation: ValidAllocation,
    pub perturbed_allocation: ValidAllocation,
}

#[tracing::instrument(
    skip(rule, claims, estate, claimants),
    fields(rule_name = %rule.name, violations = tracing::field::Empty)
)]
pub fn run_paradox_suite(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    claimants: &[Claimant],
) -> Result<Vec<ParadoxViolation>, LegitimacyError> {
    let original_allocation = evaluate_rule(rule, claims, estate, "paradox suite baseline")?;
    let entrants = entrant_candidates(claims, claimants)?;
    let mut violations = Vec::new();

    if let Some(violation) =
        detect_claimant_addition(rule, claims, estate, &original_allocation, &entrants)?
    {
        violations.push(violation);
    }

    if let Some(violation) = detect_population(rule, claims, estate, &original_allocation)? {
        violations.push(violation);
    }

    if let Some(violation) = detect_priority(rule, claims, estate, &original_allocation, &entrants)?
    {
        violations.push(violation);
    }

    Ledger::open_default()?.record_paradox_results(rule, &violations)?;
    tracing::Span::current().record("violations", tracing::field::display(violations.len()));

    Ok(violations)
}

#[derive(Debug, Clone)]
struct EntrantCandidate {
    label: String,
    claim: Claim,
}

#[tracing::instrument(
    skip(rule, claims, estate, original_allocation, entrants),
    fields(paradox_type = "claimant_addition", found = tracing::field::Empty)
)]
fn detect_claimant_addition(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    original_allocation: &ValidAllocation,
    entrants: &[EntrantCandidate],
) -> Result<Option<ParadoxViolation>, LegitimacyError> {
    for entrant in entrants {
        let perturbed_claims = claims_with_entrant(claims, &entrant.claim);
        let perturbed_allocation =
            evaluate_rule(rule, &perturbed_claims, estate, "claimant-addition paradox")?;

        for existing in claims {
            let original = allocation_of(
                original_allocation,
                &existing.claimant_id,
                "claimant-addition original",
            )?;
            let perturbed = allocation_of(
                &perturbed_allocation,
                &existing.claimant_id,
                "claimant-addition perturbed",
            )?;

            if perturbed + EPSILON < original {
                tracing::Span::current().record("found", tracing::field::display(true));
                return Ok(Some(ParadoxViolation {
                    paradox_type: ParadoxType::ClaimantAddition,
                    description: format!(
                        "Adding claimant {} reduced {} from {:.6} to {:.6}",
                        entrant.label, existing.claimant_id, original, perturbed
                    ),
                    original_allocation: original_allocation.clone(),
                    perturbed_allocation,
                }));
            }
        }
    }

    tracing::Span::current().record("found", tracing::field::display(false));
    Ok(None)
}

#[tracing::instrument(
    skip(rule, claims, estate, original_allocation),
    fields(paradox_type = "population", found = tracing::field::Empty)
)]
fn detect_population(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    original_allocation: &ValidAllocation,
) -> Result<Option<ParadoxViolation>, LegitimacyError> {
    for (index, claim) in claims.iter().enumerate() {
        for delta in POPULATION_DELTAS {
            let mut perturbed_claims = claims.to_vec();
            perturbed_claims[index].strength =
                PositiveStrength::new(perturbed_claims[index].strength.value() + delta)?;
            let perturbed_allocation =
                evaluate_rule(rule, &perturbed_claims, estate, "population paradox")?;

            for other in claims {
                if other.claimant_id == claim.claimant_id {
                    continue;
                }

                let Some(original_pair_share) = pair_share(
                    original_allocation,
                    &claim.claimant_id,
                    &other.claimant_id,
                    "population original",
                )?
                else {
                    continue;
                };
                let Some(perturbed_pair_share) = pair_share(
                    &perturbed_allocation,
                    &claim.claimant_id,
                    &other.claimant_id,
                    "population perturbed",
                )?
                else {
                    continue;
                };

                if perturbed_pair_share + EPSILON < original_pair_share {
                    tracing::Span::current().record("found", tracing::field::display(true));
                    return Ok(Some(ParadoxViolation {
                        paradox_type: ParadoxType::Population,
                        description: format!(
                            "Strengthening {} by {:.2} lowered its pairwise share against {} from {:.6} to {:.6}",
                            claim.claimant_id,
                            delta,
                            other.claimant_id,
                            original_pair_share,
                            perturbed_pair_share
                        ),
                        original_allocation: original_allocation.clone(),
                        perturbed_allocation,
                    }));
                }
            }
        }
    }

    tracing::Span::current().record("found", tracing::field::display(false));
    Ok(None)
}

#[tracing::instrument(
    skip(rule, claims, estate, original_allocation, entrants),
    fields(paradox_type = "priority", found = tracing::field::Empty)
)]
fn detect_priority(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    original_allocation: &ValidAllocation,
    entrants: &[EntrantCandidate],
) -> Result<Option<ParadoxViolation>, LegitimacyError> {
    for entrant in entrants {
        let perturbed_claims = claims_with_entrant(claims, &entrant.claim);
        let perturbed_allocation =
            evaluate_rule(rule, &perturbed_claims, estate, "priority paradox")?;

        for (left_index, left) in claims.iter().enumerate() {
            for right in claims.iter().skip(left_index + 1) {
                let original_order = allocation_order(
                    original_allocation,
                    &left.claimant_id,
                    &right.claimant_id,
                    "priority original",
                )?;
                let perturbed_order = allocation_order(
                    &perturbed_allocation,
                    &left.claimant_id,
                    &right.claimant_id,
                    "priority perturbed",
                )?;

                if original_order != Ordering::Equal
                    && perturbed_order != Ordering::Equal
                    && original_order != perturbed_order
                {
                    tracing::Span::current().record("found", tracing::field::display(true));
                    return Ok(Some(ParadoxViolation {
                        paradox_type: ParadoxType::Priority,
                        description: format!(
                            "Adding stakeholder {} flipped the relative treatment of {} and {}",
                            entrant.label, left.claimant_id, right.claimant_id
                        ),
                        original_allocation: original_allocation.clone(),
                        perturbed_allocation,
                    }));
                }
            }
        }
    }

    tracing::Span::current().record("found", tracing::field::display(false));
    Ok(None)
}

fn entrant_candidates(
    claims: &[Claim],
    claimants: &[Claimant],
) -> Result<Vec<EntrantCandidate>, LegitimacyError> {
    let _ = claimants.first();
    let mut entrants = Vec::new();

    for claim in claims {
        let mut clone = Claim::new(
            format!("{}_clone", claim.claimant_id),
            claim.strength.value(),
        )?;
        clone.metrics = claim.metrics.clone();
        entrants.push(EntrantCandidate {
            label: format!("clone of {}", claim.claimant_id),
            claim: clone,
        });

        if claim.strength.value() > EPSILON {
            let mut half_clone = Claim::new(
                format!("{}_half_clone", claim.claimant_id),
                claim.strength.value() / 2.0,
            )?;
            half_clone.metrics = claim.metrics.clone();
            entrants.push(EntrantCandidate {
                label: format!("half-strength clone of {}", claim.claimant_id),
                claim: half_clone,
            });
        }
    }

    if !claims.is_empty() {
        entrants.push(EntrantCandidate {
            label: "average entrant".to_string(),
            claim: average_claim(claims)?,
        });
    }

    Ok(entrants)
}

fn average_claim(claims: &[Claim]) -> Result<Claim, LegitimacyError> {
    let mut metric_totals = BTreeMap::<String, f64>::new();

    for claim in claims {
        for (metric, value) in &claim.metrics {
            *metric_totals.entry(metric.clone()).or_insert(0.0) += value;
        }
    }

    let metrics = metric_totals
        .into_iter()
        .map(|(metric, total)| (metric, total / claims.len() as f64))
        .collect();

    let mut claim = Claim::new(
        "average_entrant",
        claims
            .iter()
            .map(|claim| claim.strength.value())
            .sum::<f64>()
            / claims.len() as f64,
    )?;
    claim.metrics = metrics;
    Ok(claim)
}

fn claims_with_entrant(claims: &[Claim], entrant: &Claim) -> Vec<Claim> {
    let mut perturbed = claims.to_vec();
    perturbed.push(entrant.clone());
    perturbed
}

fn pair_share(
    allocation: &ValidAllocation,
    left: &str,
    right: &str,
    context: &str,
) -> Result<Option<f64>, LegitimacyError> {
    let left_share = allocation_of(allocation, left, context)?;
    let right_share = allocation_of(allocation, right, context)?;
    let total = left_share + right_share;

    if total <= EPSILON {
        Ok(None)
    } else {
        Ok(Some(left_share / total))
    }
}

fn allocation_order(
    allocation: &ValidAllocation,
    left: &str,
    right: &str,
    context: &str,
) -> Result<Ordering, LegitimacyError> {
    let delta =
        allocation_of(allocation, left, context)? - allocation_of(allocation, right, context)?;

    if delta.abs() <= EPSILON {
        Ok(Ordering::Equal)
    } else if delta.is_sign_negative() {
        Ok(Ordering::Less)
    } else {
        Ok(Ordering::Greater)
    }
}

fn allocation_of(
    allocation: &ValidAllocation,
    claimant_id: &str,
    context: &str,
) -> Result<f64, LegitimacyError> {
    allocation.share_for(claimant_id, context)
}
