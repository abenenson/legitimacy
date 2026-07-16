pub mod consistency;
pub mod monotonicity;
pub mod solidarity;
pub mod strategyproofness;

use crate::{
    Allocation, Claim, ClaimantId, Decision, Estate, GovernanceClaim, GovernanceGraph,
    LegitimacyError, ValidAllocation,
    graph::{node::decision_rank, traverse::traverse_final_decisions},
};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn apply_field_delta(
    claim: &GovernanceClaim,
    field: &str,
    delta: f64,
) -> Result<GovernanceClaim, LegitimacyError> {
    let mut updated = claim.clone();
    if field == "strength" {
        updated.strength += delta;
        if !updated.strength.is_finite() || updated.strength <= 0.0 {
            return Err(LegitimacyError::InvalidGovernanceStrength {
                claimant_id: updated.claimant_id.clone(),
                strength: updated.strength,
            });
        }
        return Ok(updated);
    }

    let value = updated.metrics.get(field).copied().unwrap_or(0.0) + delta;
    if !value.is_finite() {
        return Err(LegitimacyError::InvalidGate {
            gate: field.to_string(),
            message: format!(
                "delta produced non-finite value for '{}'",
                claim.claimant_id
            ),
        });
    }
    updated.metrics.insert(field.to_string(), value);
    Ok(updated)
}

pub(crate) fn convert_claims(claims: &[GovernanceClaim]) -> Result<Vec<Claim>, LegitimacyError> {
    claims
        .iter()
        .map(|claim| {
            let mut converted = Claim::new(claim.claimant_id.clone(), claim.strength)?;
            converted.metrics = claim.metrics.clone();
            Ok(converted)
        })
        .collect()
}

pub(crate) fn decision_allocation(
    claims: &[GovernanceClaim],
    decisions: &BTreeMap<ClaimantId, Decision>,
) -> Result<ValidAllocation, LegitimacyError> {
    let mut allocation = Allocation::default();
    for claim in claims {
        let decision = decisions
            .get(&claim.claimant_id)
            .cloned()
            .unwrap_or(Decision::Escalate);
        allocation.insert(
            claim.claimant_id.clone(),
            f64::from(decision_rank(&decision)),
        );
    }
    ValidAllocation::new(allocation, &convert_claims(claims)?)
}

pub(crate) fn graph_estate() -> Result<Estate, LegitimacyError> {
    Estate::new(2.0, "binary-decision-rank")
}

pub(crate) fn final_decisions(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<BTreeMap<ClaimantId, Decision>, LegitimacyError> {
    traverse_final_decisions(graph, claims)
}

pub(super) fn same_class_groups(claims: &[GovernanceClaim]) -> Vec<Vec<ClaimantId>> {
    let mut groups = BTreeMap::<String, Vec<ClaimantId>>::new();
    for claim in claims {
        let class = claim
            .priority_class
            .clone()
            .unwrap_or_else(|| claim.claimant_id.clone());
        groups
            .entry(class)
            .or_default()
            .push(claim.claimant_id.clone());
    }

    groups
        .into_values()
        .filter(|group| group.len() > 1)
        .collect()
}

pub(super) fn decision_direction(before: &Decision, after: &Decision) -> i8 {
    let before_rank = decision_rank(before) as i16;
    let after_rank = decision_rank(after) as i16;
    match after_rank.cmp(&before_rank) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

pub(super) fn claimant_ids(claims: &[GovernanceClaim]) -> BTreeSet<ClaimantId> {
    claims
        .iter()
        .map(|claim| claim.claimant_id.clone())
        .collect()
}
