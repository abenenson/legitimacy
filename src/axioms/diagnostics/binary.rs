use crate::{
    Allocation, Claim, Counterexample, Decision, Estate, GovernanceClaim, GovernanceNode,
    LegitimacyError, ValidAllocation, Verdict,
    graph::node::{decision_rank, evaluate_node},
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct BinaryShock {
    pub field: String,
    pub delta: f64,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct BinaryDelta {
    pub field: String,
    pub delta: f64,
}

pub fn check_binary_consistency(
    node: &GovernanceNode,
    claims: &[GovernanceClaim],
) -> Result<Verdict, LegitimacyError> {
    let original_decisions = evaluate_node(node, claims)?;
    let original_allocation = decision_allocation(claims, &original_decisions)?;
    let original_claims = convert_claims(claims)?;
    let original_estate = binary_estate()?;
    let mut perturbations_tested = 0usize;

    for removed_index in 0..claims.len() {
        let removed_claimant = claims[removed_index].claimant_id.clone();
        let reduced_claims = claims
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != removed_index)
            .map(|(_, claim)| claim.clone())
            .collect::<Vec<_>>();
        let reduced_decisions = evaluate_node(node, &reduced_claims)?;
        let reduced_allocation = decision_allocation(&reduced_claims, &reduced_decisions)?;
        perturbations_tested += 1;

        for reduced_decision in &reduced_decisions {
            let original_decision = original_decisions
                .iter()
                .find(|decision| decision.claimant_id == reduced_decision.claimant_id)
                .map(|decision| &decision.decision)
                .ok_or_else(|| LegitimacyError::MissingAllocationShare {
                    claimant_id: reduced_decision.claimant_id.clone(),
                    context: "binary consistency original lookup".to_string(),
                })?;

            if original_decision != &reduced_decision.decision {
                return Ok(Verdict::Rejected {
                    axiom: "binary consistency".to_string(),
                    counterexample: Counterexample {
                        description: format!(
                            "Removing claimant '{}' changed '{}' from {:?} to {:?}",
                            removed_claimant,
                            reduced_decision.claimant_id,
                            original_decision,
                            reduced_decision.decision
                        ),
                        original_claims: original_claims.clone(),
                        original_estate: original_estate.clone(),
                        original_allocation: original_allocation.clone(),
                        perturbed_claims: convert_claims(&reduced_claims)?,
                        perturbed_estate: original_estate.clone(),
                        perturbed_allocation: reduced_allocation,
                        violation: format!(
                            "Binary node decisions depend on claimant '{}' being present. \
                             Removing one claimant changed another claimant's gate outcome.",
                            removed_claimant
                        ),
                    },
                });
            }
        }
    }

    Ok(Verdict::Admissible {
        axiom: "binary consistency".to_string(),
        perturbations_tested,
    })
}

pub fn check_binary_solidarity(
    node: &GovernanceNode,
    claims: &[GovernanceClaim],
    shocks: &[BinaryShock],
) -> Result<Verdict, LegitimacyError> {
    let original_decisions = evaluate_node(node, claims)?;
    let original_allocation = decision_allocation(claims, &original_decisions)?;
    let original_claims = convert_claims(claims)?;
    let original_estate = binary_estate()?;
    let mut perturbations_tested = 0usize;

    for shock in shocks {
        if !shock.delta.is_finite() || shock.delta == 0.0 {
            continue;
        }

        let shocked_claims = claims
            .iter()
            .map(|claim| apply_field_delta(claim, &shock.field, shock.delta))
            .collect::<Result<Vec<_>, _>>()?;
        let shocked_decisions = evaluate_node(node, &shocked_claims)?;
        let shocked_allocation = decision_allocation(&shocked_claims, &shocked_decisions)?;
        perturbations_tested += 1;

        for shocked_decision in &shocked_decisions {
            let original_decision = original_decisions
                .iter()
                .find(|decision| decision.claimant_id == shocked_decision.claimant_id)
                .map(|decision| &decision.decision)
                .ok_or_else(|| LegitimacyError::MissingAllocationShare {
                    claimant_id: shocked_decision.claimant_id.clone(),
                    context: "binary solidarity original lookup".to_string(),
                })?;

            let before = decision_rank(original_decision);
            let after = decision_rank(&shocked_decision.decision);
            let wrong_way = if shock.delta < 0.0 {
                after > before
            } else {
                after < before
            };

            if wrong_way {
                let direction = if shock.delta < 0.0 {
                    "negative"
                } else {
                    "positive"
                };

                return Ok(Verdict::Rejected {
                    axiom: "binary solidarity".to_string(),
                    counterexample: Counterexample {
                        description: format!(
                            "{} common shock on '{}' changed '{}' from {:?} to {:?}",
                            direction,
                            shock.field,
                            shocked_decision.claimant_id,
                            original_decision,
                            shocked_decision.decision
                        ),
                        original_claims: original_claims.clone(),
                        original_estate: original_estate.clone(),
                        original_allocation: original_allocation.clone(),
                        perturbed_claims: convert_claims(&shocked_claims)?,
                        perturbed_estate: original_estate.clone(),
                        perturbed_allocation: shocked_allocation,
                        violation: format!(
                            "A common {} shock improved or worsened '{}' in the wrong direction. \
                             Binary gate logic produced an accidental winner/loser under a shared perturbation.",
                            direction, shocked_decision.claimant_id
                        ),
                    },
                });
            }
        }
    }

    Ok(Verdict::Admissible {
        axiom: "binary solidarity".to_string(),
        perturbations_tested,
    })
}

pub fn check_binary_monotonicity(
    node: &GovernanceNode,
    claims: &[GovernanceClaim],
    deltas: &[BinaryDelta],
) -> Result<Verdict, LegitimacyError> {
    let original_decisions = evaluate_node(node, claims)?;
    let original_allocation = decision_allocation(claims, &original_decisions)?;
    let original_claims = convert_claims(claims)?;
    let original_estate = binary_estate()?;
    let mut perturbations_tested = 0usize;

    for delta in deltas {
        if !delta.delta.is_finite() || delta.delta <= 0.0 {
            continue;
        }

        for index in 0..claims.len() {
            let strengthened_claims = claims
                .iter()
                .enumerate()
                .map(|(claim_index, claim)| {
                    if claim_index == index {
                        apply_field_delta(claim, &delta.field, delta.delta)
                    } else {
                        Ok(claim.clone())
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            let strengthened_decisions = evaluate_node(node, &strengthened_claims)?;
            let strengthened_allocation =
                decision_allocation(&strengthened_claims, &strengthened_decisions)?;
            perturbations_tested += 1;

            let claimant_id = &claims[index].claimant_id;
            let before = original_decisions
                .iter()
                .find(|decision| decision.claimant_id == *claimant_id)
                .map(|decision| &decision.decision)
                .ok_or_else(|| LegitimacyError::MissingAllocationShare {
                    claimant_id: claimant_id.clone(),
                    context: "binary monotonicity baseline lookup".to_string(),
                })?;
            let after = strengthened_decisions
                .iter()
                .find(|decision| decision.claimant_id == *claimant_id)
                .map(|decision| &decision.decision)
                .ok_or_else(|| LegitimacyError::MissingAllocationShare {
                    claimant_id: claimant_id.clone(),
                    context: "binary monotonicity strengthened lookup".to_string(),
                })?;

            if matches!(before, Decision::Permit) && matches!(after, Decision::Deny) {
                return Ok(Verdict::Rejected {
                    axiom: "binary monotonicity".to_string(),
                    counterexample: Counterexample {
                        description: format!(
                            "Strengthening '{}' on '{}' by {:.2} flipped Permit to Deny",
                            claimant_id, delta.field, delta.delta
                        ),
                        original_claims: original_claims.clone(),
                        original_estate: original_estate.clone(),
                        original_allocation: original_allocation.clone(),
                        perturbed_claims: convert_claims(&strengthened_claims)?,
                        perturbed_estate: original_estate.clone(),
                        perturbed_allocation: strengthened_allocation,
                        violation: format!(
                            "Strengthening '{}' should not flip a permitted claim to denial. \
                             The binary gate stack punishes the very strengthening it claims to reward.",
                            claimant_id
                        ),
                    },
                });
            }
        }
    }

    Ok(Verdict::Admissible {
        axiom: "binary monotonicity".to_string(),
        perturbations_tested,
    })
}

fn apply_field_delta(
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

fn convert_claims(claims: &[GovernanceClaim]) -> Result<Vec<Claim>, LegitimacyError> {
    claims
        .iter()
        .map(|claim| {
            let mut converted = Claim::new(claim.claimant_id.clone(), claim.strength)?;
            converted.metrics = claim.metrics.clone();
            Ok(converted)
        })
        .collect()
}

fn decision_allocation(
    claims: &[GovernanceClaim],
    decisions: &[crate::graph::node::ClaimDecision],
) -> Result<ValidAllocation, LegitimacyError> {
    let mut allocation = Allocation::default();
    for decision in decisions {
        allocation.insert(
            decision.claimant_id.clone(),
            f64::from(decision_rank(&decision.decision)),
        );
    }
    ValidAllocation::new(allocation, &convert_claims(claims)?)
}

fn binary_estate() -> Result<Estate, LegitimacyError> {
    Estate::new(2.0, "binary-decision-rank")
}

#[cfg(test)]
mod tests {
    use super::{
        BinaryDelta, BinaryShock, apply_field_delta, check_binary_consistency,
        check_binary_monotonicity, check_binary_solidarity,
    };
    use crate::{
        Decision, Gate, GateLogic, GovernanceClaim, GovernanceNode, LegitimacyError, NodeId,
        Verdict,
    };
    use std::collections::BTreeMap;

    #[test]
    fn peer_relative_binary_node_is_inconsistent() {
        let node = GovernanceNode::Binary {
            id: NodeId::new("peer").unwrap(),
            name: "peer".to_string(),
            gates: vec![Gate::PeerRelative {
                field: "strength".to_string(),
                percentile: 0.75,
                decision: Decision::Permit,
            }],
            default: Decision::Deny,
            combination: GateLogic::AnyMustPass,
        };
        let claims = vec![claim("alice", 1.0), claim("bob", 2.0), claim("carol", 3.0)];

        let verdict = check_binary_consistency(&node, &claims);

        assert!(matches!(verdict, Ok(Verdict::Rejected { .. })));
    }

    #[test]
    fn binary_consistency_counts_every_single_removal() {
        let node = GovernanceNode::Binary {
            id: NodeId::new("consistent").unwrap(),
            name: "consistent".to_string(),
            gates: vec![Gate::ThresholdGate {
                field: "strength".to_string(),
                min: 1.0,
                decision: Decision::Permit,
            }],
            default: Decision::Deny,
            combination: GateLogic::AnyMustPass,
        };
        let claims = vec![claim("alice", 2.0), claim("bob", 3.0), claim("carol", 4.0)];

        let verdict = check_binary_consistency(&node, &claims).unwrap();

        match verdict {
            Verdict::Admissible {
                axiom,
                perturbations_tested,
            } => {
                assert_eq!(axiom, "binary consistency");
                assert_eq!(perturbations_tested, claims.len());
            }
            other => panic!("expected admissible binary consistency verdict, got: {other:?}"),
        }
    }

    #[test]
    fn binary_consistency_names_removed_claimant_and_affected_survivor() {
        let node = GovernanceNode::Binary {
            id: NodeId::new("peer-ordered").unwrap(),
            name: "peer-ordered".to_string(),
            gates: vec![Gate::PeerRelative {
                field: "strength".to_string(),
                percentile: 0.75,
                decision: Decision::Permit,
            }],
            default: Decision::Deny,
            combination: GateLogic::AnyMustPass,
        };
        let claims = vec![claim("carol", 3.0), claim("bob", 2.0), claim("alice", 1.0)];

        let verdict = check_binary_consistency(&node, &claims).unwrap();

        match verdict {
            Verdict::Rejected { counterexample, .. } => {
                assert_eq!(
                    counterexample.description,
                    "Removing claimant 'carol' changed 'bob' from Deny to Permit"
                );
                assert!(
                    counterexample
                        .violation
                        .contains("Binary node decisions depend on claimant 'carol'"),
                    "unexpected violation text: {}",
                    counterexample.violation
                );
            }
            other => panic!("expected rejected binary consistency verdict, got: {other:?}"),
        }
    }

    #[test]
    fn binary_solidarity_ignores_zero_shocks_and_counts_real_ones() {
        let node = GovernanceNode::Binary {
            id: NodeId::new("solidary").unwrap(),
            name: "solidary".to_string(),
            gates: vec![Gate::ThresholdGate {
                field: "strength".to_string(),
                min: 1.0,
                decision: Decision::Permit,
            }],
            default: Decision::Deny,
            combination: GateLogic::AnyMustPass,
        };
        let claims = vec![claim("alice", 1.5), claim("bob", 2.0)];
        let shocks = [
            BinaryShock {
                field: "strength".to_string(),
                delta: 0.0,
            },
            BinaryShock {
                field: "strength".to_string(),
                delta: 0.5,
            },
            BinaryShock {
                field: "strength".to_string(),
                delta: -0.25,
            },
        ];

        let verdict = check_binary_solidarity(&node, &claims, &shocks).unwrap();

        match verdict {
            Verdict::Admissible {
                axiom,
                perturbations_tested,
            } => {
                assert_eq!(axiom, "binary solidarity");
                assert_eq!(perturbations_tested, 2);
            }
            other => panic!("expected admissible binary solidarity verdict, got: {other:?}"),
        }
    }

    #[test]
    fn binary_solidarity_reports_negative_wrong_way_shock_exactly() {
        let node = GovernanceNode::Binary {
            id: NodeId::new("shock").unwrap(),
            name: "shock".to_string(),
            gates: vec![
                Gate::ThresholdGate {
                    field: "strength".to_string(),
                    min: 5.0,
                    decision: Decision::Deny,
                },
                Gate::ThresholdGate {
                    field: "strength".to_string(),
                    min: 1.0,
                    decision: Decision::Permit,
                },
            ],
            default: Decision::Deny,
            combination: GateLogic::FirstMatch,
        };
        let claims = vec![claim("alice", 6.0), claim("bob", 3.0)];
        let shocks = [BinaryShock {
            field: "strength".to_string(),
            delta: -2.0,
        }];

        let verdict = check_binary_solidarity(&node, &claims, &shocks);

        match verdict.unwrap() {
            Verdict::Rejected { counterexample, .. } => {
                assert_eq!(
                    counterexample.description,
                    "negative common shock on 'strength' changed 'alice' from Deny to Permit"
                );
                assert!(
                    counterexample.violation.contains("wrong direction"),
                    "unexpected violation text: {}",
                    counterexample.violation
                );
            }
            other => panic!("expected rejected binary solidarity verdict, got: {other:?}"),
        }
    }

    #[test]
    fn binary_solidarity_reports_positive_wrong_way_shock_exactly() {
        let node = GovernanceNode::Binary {
            id: NodeId::new("positive-shock").unwrap(),
            name: "positive-shock".to_string(),
            gates: vec![
                Gate::ThresholdGate {
                    field: "strength".to_string(),
                    min: 5.0,
                    decision: Decision::Deny,
                },
                Gate::ThresholdGate {
                    field: "strength".to_string(),
                    min: 1.0,
                    decision: Decision::Permit,
                },
            ],
            default: Decision::Deny,
            combination: GateLogic::FirstMatch,
        };
        let claims = vec![claim("alice", 4.0), claim("bob", 2.0)];
        let shocks = [BinaryShock {
            field: "strength".to_string(),
            delta: 2.0,
        }];

        let verdict = check_binary_solidarity(&node, &claims, &shocks).unwrap();

        match verdict {
            Verdict::Rejected { counterexample, .. } => {
                assert_eq!(
                    counterexample.description,
                    "positive common shock on 'strength' changed 'alice' from Permit to Deny"
                );
                assert!(
                    counterexample.violation.contains("wrong direction"),
                    "unexpected violation text: {}",
                    counterexample.violation
                );
            }
            other => panic!("expected rejected binary solidarity verdict, got: {other:?}"),
        }
    }

    #[test]
    fn binary_node_catches_permit_to_deny_flip() {
        let node = GovernanceNode::Binary {
            id: NodeId::new("mono").unwrap(),
            name: "mono".to_string(),
            gates: vec![
                Gate::ThresholdGate {
                    field: "strength".to_string(),
                    min: 5.0,
                    decision: Decision::Deny,
                },
                Gate::ThresholdGate {
                    field: "strength".to_string(),
                    min: 1.0,
                    decision: Decision::Permit,
                },
            ],
            default: Decision::Deny,
            combination: GateLogic::FirstMatch,
        };
        let claims = vec![claim("alice", 4.0), claim("bob", 2.0)];
        let deltas = [BinaryDelta {
            field: "strength".to_string(),
            delta: 2.0,
        }];

        let verdict = check_binary_monotonicity(&node, &claims, &deltas);

        assert!(matches!(verdict, Ok(Verdict::Rejected { .. })));
    }

    #[test]
    fn binary_monotonicity_ignores_zero_deltas_and_counts_real_ones() {
        let node = GovernanceNode::Binary {
            id: NodeId::new("mono-count").unwrap(),
            name: "mono-count".to_string(),
            gates: vec![Gate::ThresholdGate {
                field: "strength".to_string(),
                min: 1.0,
                decision: Decision::Permit,
            }],
            default: Decision::Deny,
            combination: GateLogic::AnyMustPass,
        };
        let claims = vec![claim("alice", 2.0), claim("bob", 3.0)];
        let deltas = [
            BinaryDelta {
                field: "strength".to_string(),
                delta: 0.0,
            },
            BinaryDelta {
                field: "strength".to_string(),
                delta: 0.5,
            },
        ];

        let verdict = check_binary_monotonicity(&node, &claims, &deltas).unwrap();

        match verdict {
            Verdict::Admissible {
                axiom,
                perturbations_tested,
            } => {
                assert_eq!(axiom, "binary monotonicity");
                assert_eq!(perturbations_tested, claims.len());
            }
            other => panic!("expected admissible binary monotonicity verdict, got: {other:?}"),
        }
    }

    #[test]
    fn binary_monotonicity_reports_exact_claimant_flip() {
        let node = GovernanceNode::Binary {
            id: NodeId::new("mono-exact").unwrap(),
            name: "mono-exact".to_string(),
            gates: vec![
                Gate::ThresholdGate {
                    field: "strength".to_string(),
                    min: 5.0,
                    decision: Decision::Deny,
                },
                Gate::ThresholdGate {
                    field: "strength".to_string(),
                    min: 1.0,
                    decision: Decision::Permit,
                },
            ],
            default: Decision::Deny,
            combination: GateLogic::FirstMatch,
        };
        let claims = vec![claim("alice", 4.0), claim("bob", 2.0)];
        let deltas = [BinaryDelta {
            field: "strength".to_string(),
            delta: 2.0,
        }];

        let verdict = check_binary_monotonicity(&node, &claims, &deltas).unwrap();

        match verdict {
            Verdict::Rejected { counterexample, .. } => {
                assert_eq!(
                    counterexample.description,
                    "Strengthening 'alice' on 'strength' by 2.00 flipped Permit to Deny"
                );
                assert!(
                    counterexample
                        .violation
                        .contains("Strengthening 'alice' should not flip a permitted claim"),
                    "unexpected violation text: {}",
                    counterexample.violation
                );
            }
            other => panic!("expected rejected binary monotonicity verdict, got: {other:?}"),
        }
    }

    #[test]
    fn apply_field_delta_rejects_non_positive_strength() {
        let error = apply_field_delta(&claim("alice", 1.0), "strength", -2.0).unwrap_err();
        assert!(matches!(
            error,
            LegitimacyError::InvalidGovernanceStrength {
                claimant_id,
                strength
            } if claimant_id == "alice" && strength == -1.0
        ));
    }

    #[test]
    fn apply_field_delta_adds_metric_delta() {
        let mut alice = claim("alice", 1.0);
        alice.metrics.insert("risk".to_string(), 1.5);

        let updated = apply_field_delta(&alice, "risk", 0.25).unwrap();

        assert_eq!(updated.metrics.get("risk"), Some(&1.75));
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
