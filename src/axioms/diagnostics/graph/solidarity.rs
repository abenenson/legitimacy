use crate::{
    Counterexample, GovernanceClaim, GovernanceGraph, LegitimacyError, Verdict,
    axioms::{
        binary::BinaryShock,
        graph::{
            apply_field_delta, claimant_ids, convert_claims, decision_allocation,
            decision_direction, final_decisions, graph_estate, same_class_groups,
        },
    },
};

pub fn check_graph_solidarity(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    shocks: &[BinaryShock],
) -> Result<Verdict, LegitimacyError> {
    let original_decisions = final_decisions(graph, claims)?;
    let original_allocation = decision_allocation(claims, &original_decisions)?;
    let original_claims = convert_claims(claims)?;
    let original_estate = graph_estate()?;
    let claimant_ids = claimant_ids(claims);
    let groups = same_class_groups(claims);
    let mut perturbations_tested = 0usize;

    for shock in shocks {
        if !shock.delta.is_finite() || shock.delta == 0.0 {
            continue;
        }

        let shocked_claims = claims
            .iter()
            .map(|claim| apply_field_delta(claim, &shock.field, shock.delta))
            .collect::<Result<Vec<_>, _>>()?;
        let shocked_decisions = final_decisions(graph, &shocked_claims)?;
        let shocked_allocation = decision_allocation(&shocked_claims, &shocked_decisions)?;
        perturbations_tested += 1;

        for group in &groups {
            let mut saw_improvement = false;
            let mut saw_worsening = false;
            for claimant_id in group {
                if !claimant_ids.contains(claimant_id) {
                    continue;
                }
                let before = original_decisions.get(claimant_id).ok_or_else(|| {
                    LegitimacyError::missing_allocation_share(
                        claimant_id.clone(),
                        "graph solidarity original lookup",
                    )
                })?;
                let after = shocked_decisions.get(claimant_id).ok_or_else(|| {
                    LegitimacyError::missing_allocation_share(
                        claimant_id.clone(),
                        "graph solidarity shocked lookup",
                    )
                })?;
                match decision_direction(before, after) {
                    -1 => saw_worsening = true,
                    1 => saw_improvement = true,
                    _ => {}
                }
            }

            if saw_improvement && saw_worsening {
                return Ok(Verdict::Rejected {
                    axiom: "graph solidarity".to_string(),
                    counterexample: Counterexample {
                        description: format!(
                            "Common shock on '{}' split priority class {:?} into winners and losers",
                            shock.field, group
                        ),
                        original_claims: original_claims.clone(),
                        original_estate: original_estate.clone(),
                        original_allocation: original_allocation.clone(),
                        perturbed_claims: convert_claims(&shocked_claims)?,
                        perturbed_estate: original_estate.clone(),
                        perturbed_allocation: shocked_allocation,
                        violation: "A shared entry shock produced opposite exit movements inside one priority class. The composed graph created accidental winners and losers.".to_string(),
                    },
                });
            }
        }
    }

    Ok(Verdict::Admissible {
        axiom: "graph solidarity".to_string(),
        perturbations_tested,
    })
}
