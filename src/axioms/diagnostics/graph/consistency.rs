use crate::{
    Counterexample, GovernanceClaim, GovernanceGraph, LegitimacyError, Verdict,
    axioms::graph::{convert_claims, decision_allocation, final_decisions, graph_estate},
};

pub fn check_graph_consistency(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<Verdict, LegitimacyError> {
    let original_decisions = final_decisions(graph, claims)?;
    let original_allocation = decision_allocation(claims, &original_decisions)?;
    let original_claims = convert_claims(claims)?;
    let original_estate = graph_estate()?;
    let mut perturbations_tested = 0usize;

    for removed_index in 0..claims.len() {
        let removed_claimant = claims[removed_index].claimant_id.clone();
        let reduced_claims = claims
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != removed_index)
            .map(|(_, claim)| claim.clone())
            .collect::<Vec<_>>();
        let reduced_decisions = final_decisions(graph, &reduced_claims)?;
        let reduced_allocation = decision_allocation(&reduced_claims, &reduced_decisions)?;
        perturbations_tested += 1;

        for reduced_claim in &reduced_claims {
            let claimant_id = &reduced_claim.claimant_id;
            let before = original_decisions.get(claimant_id).ok_or_else(|| {
                LegitimacyError::missing_allocation_share(
                    claimant_id.clone(),
                    "graph consistency original lookup",
                )
            })?;
            let after = reduced_decisions.get(claimant_id).ok_or_else(|| {
                LegitimacyError::missing_allocation_share(
                    claimant_id.clone(),
                    "graph consistency reduced lookup",
                )
            })?;

            if before != after {
                return Ok(Verdict::Rejected {
                    axiom: "graph consistency".to_string(),
                    counterexample: Counterexample {
                        description: format!(
                            "Removing claimant '{}' changed '{}' from {:?} to {:?}",
                            removed_claimant, claimant_id, before, after
                        ),
                        original_claims: original_claims.clone(),
                        original_estate: original_estate.clone(),
                        original_allocation: original_allocation.clone(),
                        perturbed_claims: convert_claims(&reduced_claims)?,
                        perturbed_estate: original_estate.clone(),
                        perturbed_allocation: reduced_allocation,
                        violation: format!(
                            "The composed graph depends on '{}' being present. Removing one claimant changed an unrelated claimant's final exit decision.",
                            removed_claimant
                        ),
                    },
                });
            }
        }
    }

    Ok(Verdict::Admissible {
        axiom: "graph consistency".to_string(),
        perturbations_tested,
    })
}

#[cfg(test)]
mod tests {
    use super::check_graph_consistency;
    use crate::{
        Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceNode, GraphBuilder,
        NodeId, Verdict,
    };
    use std::collections::BTreeMap;

    #[test]
    fn peer_relative_graph_is_inconsistent_at_exit() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(entry_node("entry")))
            .and_then(|builder| builder.add_node(peer_gate("peer")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("entry").unwrap(),
                    NodeId::new("peer").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();
        let claims = vec![claim("alice", 0.6), claim("bob", 0.55), claim("carol", 0.9)];

        let verdict = check_graph_consistency(&graph, &claims).unwrap();

        assert!(matches!(verdict, Verdict::Rejected { .. }));
    }

    fn entry_node(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: Vec::new(),
            default: Decision::Escalate,
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
}
