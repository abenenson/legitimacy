//! Solidarity axiom: within a declared priority class, a common shock
//! to the estate should not produce accidental winners.
//!
//! Formally: if the estate shrinks (or grows), all claimants in the same
//! priority class should move in the same direction. No claimant in a
//! priority class should gain when the class as a whole is losing.
//!
//! Lean proves the single-class/global form of this axiom. Rust applies that
//! same constraint separately within each declared priority class, which is the
//! operational refinement Verdict uses for multi-class governance rules.

use crate::{
    Claim, Claimant, Counterexample, EPSILON, Estate, LegitimacyError, Rule, Verdict, evaluate_rule,
};

/// Check solidarity by scaling the estate up and down, then verifying
/// that within each priority class, all claimants move in the same direction.
#[tracing::instrument(
    skip(rule, claims, estate, claimants, scale_factors),
    fields(axiom_name = "solidarity", result = tracing::field::Empty)
)]
pub fn check_solidarity(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    claimants: &[Claimant],
    scale_factors: &[f64],
) -> Result<Verdict, LegitimacyError> {
    let original_allocation = evaluate_rule(rule, claims, estate, "solidarity baseline")?;
    let mut perturbations_tested = 0;
    let baseline = ShockBaseline {
        claims,
        estate,
        original_allocation: &original_allocation,
    };

    for &scale in scale_factors {
        if (scale - 1.0).abs() < EPSILON {
            continue; // skip identity
        }

        let shocked_estate = Estate {
            total: estate.total.scale(scale)?,
            unit: estate.unit.clone(),
        };

        let shocked_allocation =
            evaluate_rule(rule, claims, &shocked_estate, "solidarity shocked")?;
        perturbations_tested += 1;

        let is_loss = scale < 1.0;

        // Group claimants by priority class
        for priority_class in &rule.priority_classes {
            let class_members: Vec<&Claimant> = claimants
                .iter()
                .filter(|c| c.priority_class == *priority_class)
                .collect();

            if class_members.len() < 2 {
                continue; // need at least 2 to compare
            }

            // Check: all members should move in the same direction
            let mut gained = Vec::new();
            let mut lost = Vec::new();

            for member in &class_members {
                let before =
                    original_allocation.share_for(&member.id, "solidarity baseline share")?;
                let after = shocked_allocation.share_for(&member.id, "solidarity shocked share")?;

                let tol = EPSILON + EPSILON * (after.abs() + before.abs());
                if after > before + tol {
                    gained.push(member.id.clone());
                } else if after < before - tol {
                    lost.push(member.id.clone());
                }
            }

            // Solidarity violation: no member should move against the common shock direction.
            //
            // Loss case: estate shrank → anyone gaining is a violation (whether or not
            // others also lost).  This includes the degenerate case where *all* members
            // gain while the estate shrinks (e.g. by raiding other classes).
            //
            // Gain case: estate grew → anyone losing is a violation (whether or not
            // others also gained).  This includes the case where *all* members lose while
            // the estate grows — a genuine false-admissible in the prior code.
            if is_loss && !gained.is_empty() {
                let description = if !lost.is_empty() {
                    format!(
                        "Estate shrank by {:.0}% but in priority class '{}': {:?} gained while {:?} lost",
                        (1.0 - scale) * 100.0,
                        priority_class,
                        gained,
                        lost
                    )
                } else {
                    format!(
                        "Estate shrank by {:.0}% but all members of priority class '{}' gained: {:?}",
                        (1.0 - scale) * 100.0,
                        priority_class,
                        gained,
                    )
                };
                tracing::Span::current().record("result", tracing::field::display("rejected"));
                return Ok(Verdict::Rejected {
                    axiom: "solidarity".to_string(),
                    counterexample: Counterexample {
                        description,
                        original_claims: claims.to_vec(),
                        original_estate: estate.clone(),
                        original_allocation: original_allocation.clone(),
                        perturbed_claims: claims.to_vec(),
                        perturbed_estate: shocked_estate,
                        perturbed_allocation: shocked_allocation,
                        violation: format!(
                            "Common loss produced an accidental winner in class '{}'. \
                             The rule distributes common losses through accidents of implementation.",
                            priority_class
                        ),
                    },
                });
            }

            if !is_loss && !lost.is_empty() {
                let description = if !gained.is_empty() {
                    format!(
                        "Estate grew by {:.0}% but in priority class '{}': {:?} lost while {:?} gained",
                        (scale - 1.0) * 100.0,
                        priority_class,
                        lost,
                        gained
                    )
                } else {
                    format!(
                        "Estate grew by {:.0}% but all members of priority class '{}' lost: {:?}",
                        (scale - 1.0) * 100.0,
                        priority_class,
                        lost,
                    )
                };
                tracing::Span::current().record("result", tracing::field::display("rejected"));
                return Ok(Verdict::Rejected {
                    axiom: "solidarity".to_string(),
                    counterexample: Counterexample {
                        description,
                        original_claims: claims.to_vec(),
                        original_estate: estate.clone(),
                        original_allocation: original_allocation.clone(),
                        perturbed_claims: claims.to_vec(),
                        perturbed_estate: shocked_estate,
                        perturbed_allocation: shocked_allocation,
                        violation: format!(
                            "Common gain produced an accidental loser in class '{}'. \
                             The rule distributes common gains through accidents of implementation.",
                            priority_class
                        ),
                    },
                });
            }

            let shocked = ShockedState {
                shocked_estate: &shocked_estate,
                shocked_allocation: &shocked_allocation,
            };
            if let Some(counterexample) = class_evenness_violation(
                &baseline,
                &shocked,
                priority_class,
                &class_members,
                is_loss,
            )? {
                tracing::Span::current().record("result", tracing::field::display("rejected"));
                return Ok(Verdict::Rejected {
                    axiom: "solidarity".to_string(),
                    counterexample,
                });
            }
        }
    }

    let verdict = Verdict::Admissible {
        axiom: "solidarity".to_string(),
        perturbations_tested,
    };
    tracing::Span::current().record("result", tracing::field::display("admissible"));
    Ok(verdict)
}

struct ShockBaseline<'a> {
    claims: &'a [Claim],
    estate: &'a Estate,
    original_allocation: &'a crate::ValidAllocation,
}

struct ShockedState<'a> {
    shocked_estate: &'a Estate,
    shocked_allocation: &'a crate::ValidAllocation,
}

fn class_evenness_violation(
    baseline: &ShockBaseline<'_>,
    shocked: &ShockedState<'_>,
    priority_class: &str,
    class_members: &[&Claimant],
    is_loss: bool,
) -> Result<Option<Counterexample>, LegitimacyError> {
    let mut changed_members = Vec::new();

    for member in class_members {
        let before = baseline
            .original_allocation
            .share_for(&member.id, "solidarity class baseline share")?;
        let after = shocked
            .shocked_allocation
            .share_for(&member.id, "solidarity class shocked share")?;

        if before > EPSILON
            && (before - after).abs() > EPSILON + EPSILON * (before.abs() + after.abs())
        {
            changed_members.push((member.id.clone(), after / before));
        }
    }

    if changed_members.len() < 2 {
        return Ok(None);
    }

    let (_, reference_ratio) = &changed_members[0];
    if changed_members
        .iter()
        .skip(1)
        .all(|(_, ratio)| (*ratio - *reference_ratio).abs() <= EPSILON)
    {
        return Ok(None);
    }

    let direction = if is_loss { "loss" } else { "gain" };
    let ratio_summary = changed_members
        .iter()
        .map(|(id, ratio)| format!("{id}: {:.4}x", ratio))
        .collect::<Vec<_>>()
        .join(", ");

    Ok(Some(Counterexample {
        description: format!(
            "Priority class '{}' absorbed a common {} unevenly: {}",
            priority_class, direction, ratio_summary
        ),
        original_claims: baseline.claims.to_vec(),
        original_estate: baseline.estate.clone(),
        original_allocation: baseline.original_allocation.clone(),
        perturbed_claims: baseline.claims.to_vec(),
        perturbed_estate: shocked.shocked_estate.clone(),
        perturbed_allocation: shocked.shocked_allocation.clone(),
        violation: format!(
            "Priority class '{}' moved in the same direction, but not by the same proportion. \
             Solidarity requires common shocks to be shared evenly within a class.",
            priority_class
        ),
    }))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::{
        Claim, Claimant, Estate, RuleSpec, Verdict, axioms::solidarity::check_solidarity,
        rules::proportional_rule,
    };

    #[test]
    fn proportional_rule_is_solidary() {
        let claimants = vec![
            Claimant {
                id: "alice".to_string(),
                priority_class: "standard".to_string(),
                attributes: BTreeMap::new(),
            },
            Claimant {
                id: "bob".to_string(),
                priority_class: "standard".to_string(),
                attributes: BTreeMap::new(),
            },
        ];
        let claims = vec![
            Claim::new("alice", 1.0).unwrap(),
            Claim::new("bob", 2.0).unwrap(),
        ];
        let estate = Estate::new(9.0, "units").unwrap();

        let verdict = check_solidarity(
            &proportional_rule(),
            &claims,
            &estate,
            &claimants,
            &[0.5, 1.5],
        );
        assert!(matches!(verdict, Ok(Verdict::Admissible { .. })));
    }

    /// Regression test for REVIEW.md C2: universal loss under common gain was a false admissible.
    ///
    /// A rule that always halves every allocation, regardless of estate size, means that
    /// when the estate grows, all class members still lose allocation.  The prior code
    /// required both gainers AND losers to fire; this case (all lose) was silently admitted.
    #[test]
    fn universal_loss_under_common_gain_is_rejected() {
        use crate::Rule;
        use std::collections::BTreeMap;

        // A rule that always allocates a fixed fraction regardless of estate size.
        // When the estate grows (scale > 1), all members' allocations are unchanged
        // but if we use a rule that actively shrinks allocations on growth, we get
        // universal loss.  Here: allocate 1/(2*n) * original_estate for all claims,
        // ignoring the new estate — so growing the estate still pays the old halved amount.
        let _fixed_rule = Rule {
            name: "fixed-halved".to_string(),
            version: "0.1.0".to_string(),
            rule_spec: RuleSpec::programmatic(|claims: &[Claim], _estate: &Estate| {
                // Always pay 0.5 regardless of estate
                Ok(claims
                    .iter()
                    .map(|c| (c.claimant_id.clone(), 0.5))
                    .collect())
            }),
            priority_classes: vec!["standard".to_string()],
        };

        let claimants = vec![
            Claimant {
                id: "alice".to_string(),
                priority_class: "standard".to_string(),
                attributes: BTreeMap::new(),
            },
            Claimant {
                id: "bob".to_string(),
                priority_class: "standard".to_string(),
                attributes: BTreeMap::new(),
            },
        ];
        // With estate=2.0 and fixed allocation 0.5 each, baseline is 0.5.
        // When estate grows to 4.0 (scale=2.0), allocation stays 0.5 for both —
        // neither gained.  Use a rule that actively decreases on growth instead.
        //
        // Simpler: a rule that allocates estate/4 per claimant (so at estate=4.0
        // each gets 1.0, but at estate=8.0 each still gets 1.0 because the rule
        // caps at estate_original/4).  Actually just hardcode: if estate>5, pay 0.4.
        let _estate_dependent_rule = Rule {
            name: "capped-pay".to_string(),
            version: "0.1.0".to_string(),
            rule_spec: RuleSpec::programmatic(|claims: &[Claim], estate: &Estate| {
                // Pay less per claimant when estate is large (e.g. austerity model):
                // share = min(0.8, estate.total * 0.1) / claims.len()
                let per_head = (estate.total.value() * 0.05).min(0.4);
                Ok(claims
                    .iter()
                    .map(|c| (c.claimant_id.clone(), per_head))
                    .collect())
            }),
            priority_classes: vec!["standard".to_string()],
        };

        let claims = vec![
            Claim::new("alice", 1.0).unwrap(),
            Claim::new("bob", 2.0).unwrap(),
        ];
        let estate = Estate::new(6.0, "units").unwrap(); // per_head = min(0.3, 0.4) = 0.3 each
        // At scale=2.0 (estate=12.0): per_head = min(0.6, 0.4) = 0.4 each → gain
        // At scale=0.5 (estate=3.0): per_head = min(0.15, 0.4) = 0.15 each → loss
        // This rule is admissible (proportional-ish direction).
        //
        // For the BUG test, we need: estate grows, all members LOSE.
        // Use a rule where per_head = estate.total / (estate.total + 10): always <1,
        // starts at 6/16=0.375, but we want it to drop on growth.
        // Instead, invert: per_head = 1 - (estate.total / 20).clamp(0,1)
        let inverting_rule = Rule {
            name: "inverting-pay".to_string(),
            version: "0.1.0".to_string(),
            rule_spec: RuleSpec::programmatic(|claims: &[Claim], estate: &Estate| {
                // Pay MORE when estate is SMALL (scarce resource premium).
                // per_head decreases as estate grows → universal loss under gain.
                let per_head = (1.0_f64 - estate.total.value() / 20.0_f64).max(0.0_f64);
                Ok(claims
                    .iter()
                    .map(|c| (c.claimant_id.clone(), per_head))
                    .collect())
            }),
            priority_classes: vec!["standard".to_string()],
        };

        // estate=6: per_head = 1 - 6/20 = 0.7
        // estate=9 (scale=1.5): per_head = 1 - 9/20 = 0.55 → both alice and bob lose
        // This is universal loss under common gain — C2 bug: was admitted, should reject.
        let verdict = check_solidarity(
            &inverting_rule,
            &claims,
            &estate,
            &claimants,
            &[1.5], // estate grows
        );
        assert!(
            matches!(verdict, Ok(Verdict::Rejected { .. })),
            "universal loss under common gain must be rejected; got: {verdict:?}"
        );

        // Verify the counterexample description mentions all losers
        if let Ok(Verdict::Rejected { counterexample, .. }) = verdict {
            assert!(
                counterexample.description.contains("all members"),
                "description should note that all members lost; got: {}",
                counterexample.description
            );
        }
    }

    #[test]
    fn uneven_universal_loss_within_a_class_is_rejected() {
        use crate::Rule;

        let claimants = vec![
            Claimant {
                id: "alice".to_string(),
                priority_class: "standard".to_string(),
                attributes: BTreeMap::new(),
            },
            Claimant {
                id: "bob".to_string(),
                priority_class: "standard".to_string(),
                attributes: BTreeMap::new(),
            },
        ];
        let claims = vec![
            Claim::new("alice", 1.0).unwrap(),
            Claim::new("bob", 1.0).unwrap(),
        ];
        let estate = Estate::new(10.0, "units").unwrap();
        let rule = Rule {
            name: "uneven-austerity".to_string(),
            version: "0.1.0".to_string(),
            rule_spec: RuleSpec::programmatic(|claims: &[Claim], estate: &Estate| {
                let mut allocation = crate::Allocation::default();
                if estate.total.value() >= 10.0 {
                    allocation.insert(claims[0].claimant_id.clone(), 6.0);
                    allocation.insert(claims[1].claimant_id.clone(), 4.0);
                } else {
                    allocation.insert(claims[0].claimant_id.clone(), 4.0);
                    allocation.insert(claims[1].claimant_id.clone(), 3.8);
                }
                Ok(allocation)
            }),
            priority_classes: vec!["standard".to_string()],
        };

        let verdict = check_solidarity(&rule, &claims, &estate, &claimants, &[0.8]);

        assert!(
            matches!(verdict, Ok(Verdict::Rejected { .. })),
            "uneven universal loss within a class must be rejected; got: {verdict:?}"
        );
        if let Ok(Verdict::Rejected { counterexample, .. }) = verdict {
            assert!(
                counterexample
                    .description
                    .contains("absorbed a common loss unevenly")
            );
        }
    }
}
