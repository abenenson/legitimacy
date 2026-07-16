//! Mutation guard tests: catch axiom checker mutations that other tests miss.
//! Written after manual mutation testing on 2026-04-14.

use legitimacy::axioms::binary::{BinaryDelta, check_binary_monotonicity};
use legitimacy::*;
use std::collections::BTreeMap;

#[test]
fn consistency_tolerance_guard() {
    let rule = Rule {
        name: "near-miss-consistency".to_string(),
        version: "0.1.0".to_string(),
        rule_spec: RuleSpec::programmatic(|claims: &[Claim], estate: &Estate| {
            let mut allocation = Allocation::default();

            if claims.len() == 2 {
                let half = estate.total.value() / 2.0;
                allocation.insert(claims[0].claimant_id.clone(), half + 0.01);
                allocation.insert(claims[1].claimant_id.clone(), half - 0.01);
            } else {
                let equal_share = estate.total.value() / claims.len() as f64;
                for claim in claims {
                    allocation.insert(claim.claimant_id.clone(), equal_share);
                }
            }

            Ok(allocation)
        }),
        priority_classes: vec!["standard".to_string()],
    };

    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 1.0).unwrap(),
        Claim::new("carol", 1.0).unwrap(),
    ];
    let estate = Estate::new(1.0, "units").unwrap();

    let verdict = axioms::consistency::check_consistency(&rule, &claims, &estate).unwrap();
    assert!(
        matches!(verdict, Verdict::Rejected { .. }),
        "near-miss pair reductions must fail at the real consistency tolerance"
    );
}

#[test]
fn triple_only_consistency_violation_proves_legacy_bound_is_weaker() {
    let rule = Rule {
        name: "triple-only-consistency".to_string(),
        version: "0.1.0".to_string(),
        rule_spec: RuleSpec::programmatic(|claims: &[Claim], estate: &Estate| {
            let mut allocation = Allocation::default();

            if claims.len() == 2 {
                allocation.insert(claims[0].claimant_id.clone(), estate.total.value() * 0.75);
                allocation.insert(claims[1].claimant_id.clone(), estate.total.value() * 0.25);
            } else {
                let total_strength: f64 = claims.iter().map(|claim| claim.strength.value()).sum();
                for claim in claims {
                    allocation.insert(
                        claim.claimant_id.clone(),
                        estate.total.value() * claim.strength.value() / total_strength,
                    );
                }
            }

            Ok(allocation)
        }),
        priority_classes: vec!["standard".to_string()],
    };
    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 2.0).unwrap(),
        Claim::new("carol", 3.0).unwrap(),
        Claim::new("dave", 4.0).unwrap(),
        Claim::new("erin", 5.0).unwrap(),
    ];
    let estate = Estate::new(15.0, "units").unwrap();

    let bounded =
        axioms::consistency::check_singles_pairs_consistency(&rule, &claims, &estate).unwrap();
    assert!(
        matches!(
            bounded,
            Verdict::Admissible {
                perturbations_tested: 15,
                ..
            }
        ),
        "legacy singles+pairs checker should miss the triple-only violation: {bounded:?}"
    );

    let full = axioms::consistency::check_full_consistency(
        &rule,
        &claims,
        &estate,
        axioms::consistency::FullConsistencyOptions::default(),
    )
    .unwrap();
    match full {
        Verdict::Rejected {
            axiom,
            counterexample,
        } => {
            assert_eq!(axiom, "consistency (Young full sub-coalition)");
            assert!(
                counterexample
                    .description
                    .contains("Coalition witness [alice, bob, carol]"),
                "{counterexample:?}"
            );
        }
        other => panic!("full Young consistency must reject the triple-only violation: {other:?}"),
    }
}

#[test]
fn binary_gate_permit_guard() {
    let node = GovernanceNode::Binary {
        id: NodeId::new("guard").unwrap(),
        name: "permit-guard".to_string(),
        gates: vec![Gate::ThresholdGate {
            field: "strength".to_string(),
            min: 0.5,
            decision: Decision::Permit,
        }],
        default: Decision::Deny,
        combination: GateLogic::FirstMatch,
    };
    let claims = vec![GovernanceClaim {
        claimant_id: "strong".to_string(),
        strength: 1.0,
        priority_class: None,
        path: None,
        action: None,
        content: None,
        metrics: BTreeMap::new(),
    }];
    let deltas = [BinaryDelta {
        field: "strength".to_string(),
        delta: 0.5,
    }];
    let result = check_binary_monotonicity(&node, &claims, &deltas).unwrap();
    assert!(
        matches!(result, Verdict::Admissible { .. }),
        "threshold gate must be monotone"
    );
}
