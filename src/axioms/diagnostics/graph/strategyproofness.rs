use crate::{
    Counterexample, GovernanceClaim, GovernanceGraph, LegitimacyError, Verdict,
    axioms::graph::{convert_claims, decision_allocation, final_decisions, graph_estate},
    graph::node::decision_rank,
};

const MISREPORT_DELTAS: [f64; 5] = [-0.3, -0.1, 0.1, 0.3, 0.5];

pub fn check_graph_strategyproofness(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<Verdict, LegitimacyError> {
    let original_decisions = final_decisions(graph, claims)?;
    let original_allocation = decision_allocation(claims, &original_decisions)?;
    let original_claims = convert_claims(claims)?;
    let original_estate = graph_estate()?;
    let mut perturbations_tested = 0usize;

    for index in 0..claims.len() {
        let misreporter = &claims[index];
        let true_decision = original_decisions
            .get(&misreporter.claimant_id)
            .ok_or_else(|| {
                LegitimacyError::missing_allocation_share(
                    misreporter.claimant_id.clone(),
                    "graph strategyproofness original lookup",
                )
            })?;
        let true_rank = decision_rank(true_decision);

        for delta in MISREPORT_DELTAS {
            let reported_strength = misreporter.strength + delta;
            if !reported_strength.is_finite() || reported_strength <= 0.0 {
                continue;
            }

            let misreported_claims = claims
                .iter()
                .enumerate()
                .map(|(claim_index, claim)| {
                    if claim_index == index {
                        let mut modified = claim.clone();
                        modified.strength = reported_strength;
                        Ok(modified)
                    } else {
                        Ok(claim.clone())
                    }
                })
                .collect::<Result<Vec<_>, LegitimacyError>>()?;

            let misreported_decisions = final_decisions(graph, &misreported_claims)?;
            let misreported_allocation =
                decision_allocation(&misreported_claims, &misreported_decisions)?;
            perturbations_tested += 1;

            let misreported_decision = misreported_decisions
                .get(&misreporter.claimant_id)
                .ok_or_else(|| {
                    LegitimacyError::missing_allocation_share(
                        misreporter.claimant_id.clone(),
                        "graph strategyproofness misreported lookup",
                    )
                })?;
            let misreported_rank = decision_rank(misreported_decision);

            if misreported_rank > true_rank {
                return Ok(Verdict::Rejected {
                    axiom: "graph strategyproofness".to_string(),
                    counterexample: Counterexample {
                        description: format!(
                            "Claimant '{}' improved from {:?} to {:?} by misreporting strength {:.2} -> {:.2}",
                            misreporter.claimant_id,
                            true_decision,
                            misreported_decision,
                            misreporter.strength,
                            reported_strength,
                        ),
                        original_claims: original_claims.clone(),
                        original_estate: original_estate.clone(),
                        original_allocation: original_allocation.clone(),
                        perturbed_claims: convert_claims(&misreported_claims)?,
                        perturbed_estate: original_estate.clone(),
                        perturbed_allocation: misreported_allocation,
                        violation: format!(
                            "Claimant '{}' can strategically misreport claim strength to achieve a better governance outcome. The composed graph is manipulable.",
                            misreporter.claimant_id
                        ),
                    },
                });
            }
        }
    }

    Ok(Verdict::Admissible {
        axiom: "graph strategyproofness".to_string(),
        perturbations_tested,
    })
}

#[cfg(test)]
mod tests {
    use super::check_graph_strategyproofness;
    use crate::{
        Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceNode, GraphBuilder,
        NodeId, Verdict,
    };
    use std::collections::BTreeMap;

    #[test]
    fn peer_relative_graph_is_manipulable() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(threshold_entry("a")))
            .and_then(|builder| builder.add_node(peer_gate("b")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("a").unwrap(),
                    NodeId::new("b").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();
        let claims = vec![claim("alice", 0.4), claim("bob", 0.55), claim("carol", 0.9)];

        let verdict = check_graph_strategyproofness(&graph, &claims).unwrap();

        assert!(
            matches!(verdict, Verdict::Rejected { .. }),
            "peer-relative graph should be manipulable; got: {verdict:?}"
        );
    }

    #[test]
    fn threshold_only_graph_all_above_threshold_is_strategyproof() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(threshold_entry("gate")))
            .and_then(GraphBuilder::build)
            .unwrap();
        // All claims above the 0.5 threshold — no misreport can improve outcome
        let claims = vec![claim("alice", 0.6), claim("bob", 0.7)];

        let verdict = check_graph_strategyproofness(&graph, &claims).unwrap();

        assert!(
            matches!(verdict, Verdict::Admissible { .. }),
            "threshold-only graph with all above threshold should be strategyproof; got: {verdict:?}"
        );
    }

    #[test]
    fn threshold_graph_below_threshold_is_manipulable() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(threshold_entry("gate")))
            .and_then(GraphBuilder::build)
            .unwrap();
        // Bob at 0.3 below 0.5 threshold can misreport to cross it
        let claims = vec![claim("alice", 0.6), claim("bob", 0.3)];

        let verdict = check_graph_strategyproofness(&graph, &claims).unwrap();

        assert!(
            matches!(verdict, Verdict::Rejected { .. }),
            "claimant below threshold should be able to manipulate; got: {verdict:?}"
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
