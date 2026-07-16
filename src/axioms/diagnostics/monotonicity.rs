//! Monotonicity axiom: strengthening a valid claim should never produce
//! a worse outcome for that claimant.
//!
//! Formally: if claimant i's claim strength increases (all else equal),
//! claimant i's allocation should not decrease.
//!
//! # Safety-clearance inversion
//!
//! Some rules are deliberately *anti-monotone*: higher claim strength signals
//! greater danger and should produce *less* access.  A content-moderation hook
//! that blocks a request when its context score crosses a threshold is a canonical
//! example — richer context that confirms a dangerous intent should not increase
//! the allocation.
//!
//! When `inversion = true`, the checker enforces the opposite contract:
//! strengthening a claim must never *increase* its allocation.  A rule that
//! satisfies this is "inverted-monotone" (or "safety-clearance monotone").

use crate::{
    Claim, Counterexample, EPSILON, Estate, LegitimacyError, PositiveStrength, Rule, Verdict,
    evaluate_rule,
};

/// Check monotonicity by strengthening each claimant's claim and verifying
/// their allocation does not decrease.
///
/// When `inversion` is `true`, the check is inverted: strengthening must never
/// *increase* allocation.  Use this for safety-clearance rules where higher
/// context strength signals greater risk.
#[tracing::instrument(
    skip(rule, claims, estate, strength_deltas),
    fields(axiom_name = "monotonicity", result = tracing::field::Empty)
)]
pub fn check_monotonicity(
    rule: &Rule,
    claims: &[Claim],
    estate: &Estate,
    strength_deltas: &[PositiveStrength],
    inversion: bool,
) -> Result<Verdict, LegitimacyError> {
    let original_allocation = evaluate_rule(rule, claims, estate, "monotonicity baseline")?;
    let mut perturbations_tested = 0;

    for i in 0..claims.len() {
        for delta in strength_deltas {
            let delta = delta.value();
            let mut strengthened_claims = claims.to_vec();
            strengthened_claims[i].strength =
                PositiveStrength::new(strengthened_claims[i].strength.value() + delta)?;

            let strengthened_allocation = evaluate_rule(
                rule,
                &strengthened_claims,
                estate,
                "monotonicity strengthening",
            )?;
            perturbations_tested += 1;

            let id = &claims[i].claimant_id;
            let before = original_allocation.share_for(id, "monotonicity baseline share")?;
            let after = strengthened_allocation.share_for(id, "monotonicity strengthened share")?;

            let tol = EPSILON + EPSILON * (after.abs() + before.abs());
            let violation = if inversion {
                // Inverted: strengthening must not *increase* allocation.
                after > before + tol
            } else {
                // Standard: strengthening must not *decrease* allocation.
                after < before - tol
            };

            if violation {
                let axiom_label = if inversion {
                    "monotonicity (inverted)"
                } else {
                    "monotonicity"
                };

                let description = if inversion {
                    format!(
                        "Strengthening '{}' claim by {:.2} increased allocation from {:.4} to {:.4}",
                        id, delta, before, after
                    )
                } else {
                    format!(
                        "Strengthening '{}' claim by {:.2} decreased allocation from {:.4} to {:.4}",
                        id, delta, before, after
                    )
                };

                let violation_msg = if inversion {
                    format!(
                        "More evidence of '{}' danger increased its allocation. \
                         The safety-clearance rule rewards the very risk it is meant to suppress.",
                        id
                    )
                } else {
                    format!(
                        "More evidence of '{}' strength lowered its allocation. \
                         The rule punishes the very thing it claims to reward.",
                        id
                    )
                };

                tracing::Span::current().record("result", tracing::field::display("rejected"));
                return Ok(Verdict::Rejected {
                    axiom: axiom_label.to_string(),
                    counterexample: Counterexample {
                        description,
                        original_claims: claims.to_vec(),
                        original_estate: estate.clone(),
                        original_allocation: original_allocation.clone(),
                        perturbed_claims: strengthened_claims,
                        perturbed_estate: estate.clone(),
                        perturbed_allocation: strengthened_allocation,
                        violation: violation_msg,
                    },
                });
            }
        }
    }

    let axiom_label = if inversion {
        "monotonicity (inverted)"
    } else {
        "monotonicity"
    };

    let verdict = Verdict::Admissible {
        axiom: axiom_label.to_string(),
        perturbations_tested,
    };
    tracing::Span::current().record("result", tracing::field::display("admissible"));
    Ok(verdict)
}

#[cfg(test)]
mod tests {
    use crate::{
        Claim, Estate, Verdict, axioms::monotonicity::check_monotonicity, rules::proportional_rule,
    };

    #[test]
    fn proportional_rule_is_monotone() {
        use crate::PositiveStrength;

        let claims = vec![
            Claim::new("alice", 1.0).unwrap(),
            Claim::new("bob", 2.0).unwrap(),
            Claim::new("carol", 3.0).unwrap(),
        ];
        let estate = Estate::new(12.0, "units").unwrap();
        let deltas = [
            PositiveStrength::new(0.25).unwrap(),
            PositiveStrength::new(1.0).unwrap(),
        ];

        let verdict = check_monotonicity(&proportional_rule(), &claims, &estate, &deltas, false);
        assert!(matches!(verdict, Ok(Verdict::Admissible { .. })));
    }
}
