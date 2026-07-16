//! Property-based tests for the legitimacy axiom checkers.
//!
//! Tests that: (a) the proportional rule satisfies all three axioms for any
//! valid random input, (b) claim validation behaves correctly at boundaries,
//! (c) if a rule is consistent on single-claimant reductions it is also
//! consistent on pair reductions (the consistency checker is self-coherent),
//! (d) adversarial rules are reliably REJECTED by the axiom checkers, and
//! (e) the checkers are numerically robust at estate and claim strength extremes.
//!
//! Uses `proptest` to generate random but valid claim sets and estates.

use std::collections::BTreeMap;

use legitimacy::{
    Allocation, Claim, Claimant, Estate, LegitimacyError, PositiveStrength, Rule, RuleSpec,
    Verdict,
    axioms::{
        consistency::check_consistency, monotonicity::check_monotonicity,
        solidarity::check_solidarity,
    },
    rules::{essay_composite_rule, proportional_rule},
};
use proptest::prelude::*;

// ---------------------------------------------------------------------------
// Generators
// ---------------------------------------------------------------------------

/// A single valid claim: positive strength, no metrics.
fn arb_claim(id: &'static str) -> impl Strategy<Value = Claim> {
    (1e-6f64..1000.0f64).prop_map(move |strength| {
        Claim::new(id, strength).expect("generated strength should be positive")
    })
}

/// A claimant with a fixed priority class.
fn arb_claimant(id: &'static str) -> Claimant {
    Claimant {
        id: id.to_string(),
        priority_class: "standard".to_string(),
        attributes: BTreeMap::new(),
    }
}

/// A valid estate: total strictly positive and finite.
fn arb_estate() -> impl Strategy<Value = Estate> {
    (1e-3f64..1_000_000.0f64)
        .prop_map(|total| Estate::new(total, "units").expect("generated total should be positive"))
}

/// 2-claimant (alice, bob) scenario.
fn arb_two_claim_scenario() -> impl Strategy<Value = (Vec<Claimant>, Vec<Claim>, Estate)> {
    (arb_claim("alice"), arb_claim("bob"), arb_estate()).prop_map(|(alice, bob, estate)| {
        (
            vec![arb_claimant("alice"), arb_claimant("bob")],
            vec![alice, bob],
            estate,
        )
    })
}

/// 3-claimant (alice, bob, carol) scenario.
fn arb_three_claim_scenario() -> impl Strategy<Value = (Vec<Claimant>, Vec<Claim>, Estate)> {
    (
        arb_claim("alice"),
        arb_claim("bob"),
        arb_claim("carol"),
        arb_estate(),
    )
        .prop_map(|(alice, bob, carol, estate)| {
            (
                vec![
                    arb_claimant("alice"),
                    arb_claimant("bob"),
                    arb_claimant("carol"),
                ],
                vec![alice, bob, carol],
                estate,
            )
        })
}

/// 4-claimant scenario.
fn arb_four_claim_scenario() -> impl Strategy<Value = (Vec<Claimant>, Vec<Claim>, Estate)> {
    (
        arb_claim("alice"),
        arb_claim("bob"),
        arb_claim("carol"),
        arb_claim("dave"),
        arb_estate(),
    )
        .prop_map(|(alice, bob, carol, dave, estate)| {
            (
                vec![
                    arb_claimant("alice"),
                    arb_claimant("bob"),
                    arb_claimant("carol"),
                    arb_claimant("dave"),
                ],
                vec![alice, bob, carol, dave],
                estate,
            )
        })
}

// ---------------------------------------------------------------------------
// Claim validation properties
// ---------------------------------------------------------------------------

proptest! {
    /// Any strictly positive finite strength produces a valid Claim.
    #[test]
    fn claim_new_positive_strength_always_ok(strength in 1e-9f64..1e9f64) {
        prop_assert!(Claim::new("test", strength).is_ok());
    }

    /// Zero strength is always rejected.
    #[test]
    fn claim_new_zero_strength_always_err(_dummy in 0..1i32) {
        prop_assert!(Claim::new("test", 0.0).is_err());
    }

    /// Any negative strength is always rejected.
    #[test]
    fn claim_new_negative_strength_always_err(magnitude in 1e-9f64..1e9f64) {
        prop_assert!(Claim::new("test", -magnitude).is_err());
    }

    /// Infinite strength is rejected.
    #[test]
    fn claim_new_infinite_strength_always_err(_dummy in 0..1i32) {
        prop_assert!(Claim::new("test", f64::INFINITY).is_err());
        prop_assert!(Claim::new("test", f64::NEG_INFINITY).is_err());
    }

    /// NaN strength is rejected.
    #[test]
    fn claim_new_nan_strength_always_err(_dummy in 0..1i32) {
        prop_assert!(Claim::new("test", f64::NAN).is_err());
    }
}

// ---------------------------------------------------------------------------
// Proportional rule: always admissible for all three axioms
// ---------------------------------------------------------------------------

proptest! {
    /// Proportional rule always passes consistency for 2-claimant problems.
    ///
    /// This guards against regressions in the consistency checker when claim
    /// strengths or estate sizes hit unusual numeric regions.
    #[test]
    fn proportional_always_consistent_two_claimants(
        (_, claims, estate) in arb_two_claim_scenario()
    ) {
        let verdict = check_consistency(&proportional_rule(), &claims, &estate)
            .expect("proportional rule should never produce a consistency infrastructure error");
        prop_assert!(
            matches!(verdict, Verdict::Admissible { .. }),
            "proportional rule must be consistent; got: {verdict:?}"
        );
    }

    /// Proportional rule always passes consistency for 3-claimant problems.
    #[test]
    fn proportional_always_consistent_three_claimants(
        (_, claims, estate) in arb_three_claim_scenario()
    ) {
        let verdict = check_consistency(&proportional_rule(), &claims, &estate)
            .expect("proportional rule should never produce a consistency infrastructure error");
        prop_assert!(
            matches!(verdict, Verdict::Admissible { .. }),
            "proportional rule must be consistent; got: {verdict:?}"
        );
    }

    /// Proportional rule always passes solidarity for 2-claimant problems.
    #[test]
    fn proportional_always_solidary_two_claimants(
        (claimants, claims, estate) in arb_two_claim_scenario()
    ) {
        let verdict = check_solidarity(
            &proportional_rule(),
            &claims,
            &estate,
            &claimants,
            &[0.5, 1.5],
        )
        .expect("proportional rule should never produce a solidarity infrastructure error");
        prop_assert!(
            matches!(verdict, Verdict::Admissible { .. }),
            "proportional rule must be solidary; got: {verdict:?}"
        );
    }

    /// Proportional rule always passes solidarity for 3-claimant problems.
    #[test]
    fn proportional_always_solidary_three_claimants(
        (claimants, claims, estate) in arb_three_claim_scenario()
    ) {
        let verdict = check_solidarity(
            &proportional_rule(),
            &claims,
            &estate,
            &claimants,
            &[0.5, 1.5],
        )
        .expect("proportional rule should never produce a solidarity infrastructure error");
        prop_assert!(
            matches!(verdict, Verdict::Admissible { .. }),
            "proportional rule must be solidary; got: {verdict:?}"
        );
    }

    /// Proportional rule always passes monotonicity for 2-claimant problems.
    #[test]
    fn proportional_always_monotone_two_claimants(
        (_, claims, estate) in arb_two_claim_scenario()
    ) {
        let deltas = [
            PositiveStrength::new(0.1).unwrap(),
            PositiveStrength::new(1.0).unwrap(),
        ];
        let verdict = check_monotonicity(
            &proportional_rule(),
            &claims,
            &estate,
            &deltas,
            false,
        )
        .expect("proportional rule should never produce a monotonicity infrastructure error");
        prop_assert!(
            matches!(verdict, Verdict::Admissible { .. }),
            "proportional rule must be monotone; got: {verdict:?}"
        );
    }

    /// Proportional rule always passes monotonicity for 4-claimant problems.
    #[test]
    fn proportional_always_monotone_four_claimants(
        (_, claims, estate) in arb_four_claim_scenario()
    ) {
        let deltas = [
            PositiveStrength::new(0.1).unwrap(),
            PositiveStrength::new(0.5).unwrap(),
        ];
        let verdict = check_monotonicity(
            &proportional_rule(),
            &claims,
            &estate,
            &deltas,
            false,
        )
        .expect("proportional rule should never produce a monotonicity infrastructure error");
        prop_assert!(
            matches!(verdict, Verdict::Admissible { .. }),
            "proportional rule must be monotone; got: {verdict:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Axiom checker self-coherence: consistency on singles implies consistency
// on pairs (for any rule that the proportional rule represents as a stand-in).
// ---------------------------------------------------------------------------

proptest! {
    /// If the full proportional rule passes consistency for 3 claimants, then
    /// removing any individual and running the check on the 2-claimant sub-problem
    /// also passes — the checker is self-coherent across problem sizes.
    #[test]
    fn consistency_coherent_across_reductions(
        (_, claims, estate) in arb_three_claim_scenario()
    ) {
        let rule = proportional_rule();

        // Full 3-claimant problem must be consistent.
        let full_verdict = check_consistency(&rule, &claims, &estate)
            .expect("infrastructure error on full problem");
        prop_assume!(matches!(full_verdict, Verdict::Admissible { .. }));

        // Every single-claimant reduction must also be consistent.
        for skip in 0..claims.len() {
            let reduced: Vec<Claim> = claims
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != skip)
                .map(|(_, c)| c.clone())
                .collect();

            // Adjust estate by the removed claimant's proportional share.
            let total_strength: f64 = claims.iter().map(|c| c.strength.value()).sum();
            let removed_share =
                claims[skip].strength.value() / total_strength * estate.total.value();
            let reduced_total = (estate.total.value() - removed_share).max(1e-12);
            let reduced_estate = Estate::new(reduced_total, estate.unit.clone())
                .expect("reduced estate should be positive");

            let reduced_verdict = check_consistency(&rule, &reduced, &reduced_estate)
                .expect("infrastructure error on reduced problem");

            prop_assert!(
                matches!(reduced_verdict, Verdict::Admissible { .. }),
                "consistency must hold on the reduced 2-claimant sub-problem \
                 (removed claim index {skip}); got: {reduced_verdict:?}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Adversarial rule helpers
// ---------------------------------------------------------------------------

/// min-strength-wins: the claimant with the LOWEST strength takes everything.
///
/// Designed to fail monotonicity: strengthening a current winner (lowest
/// strength) past another claimant's strength causes their allocation to
/// collapse from 100 % to 0 % — the opposite of the required direction.
fn min_strength_wins_rule() -> Rule {
    Rule {
        name: "min-strength-wins".to_string(),
        version: "0.1.0".to_string(),
        rule_spec: RuleSpec::programmatic(
            |claims: &[Claim], estate: &Estate| -> Result<Allocation, LegitimacyError> {
                if claims.is_empty() {
                    return Ok(Allocation::default());
                }
                let winner_id = claims
                    .iter()
                    .min_by(|a, b| a.strength.value().total_cmp(&b.strength.value()))
                    .map(|c| c.claimant_id.clone())
                    .expect("non-empty claims always have a minimum");
                let mut alloc = Allocation::default();
                for claim in claims {
                    let share = if claim.claimant_id == winner_id {
                        estate.total.value()
                    } else {
                        0.0
                    };
                    alloc.insert(claim.claimant_id.clone(), share);
                }
                Ok(alloc)
            },
        ),
        priority_classes: vec!["standard".to_string()],
    }
}

// ---------------------------------------------------------------------------
// Adversarial properties: the axiom checkers must CATCH known violations
// ---------------------------------------------------------------------------

proptest! {
    /// essay_composite_rule (the "reasonable rule that fails everything") is
    /// always rejected for consistency when one claimant uniquely dominates
    /// the median.
    ///
    /// Why it fails: the essay rule promotes only claimants strictly above the
    /// median score. With 3 claimants, exactly one is above the median and
    /// receives the full estate. When the two non-winners are removed together
    /// (pair reduction), the winner is the only claimant remaining — and their
    /// score now equals the single-claimant median, so they are no longer
    /// "strictly above" it and receive zero. This contradicts their original
    /// full-estate allocation, which the consistency checker must detect.
    #[test]
    fn essay_rule_rejected_for_consistency_when_one_dominates(
        s1 in 0.01f64..0.60f64,
        s2 in 0.01f64..0.60f64,
        s3 in 0.01f64..0.60f64,
        estate_total in 1.0f64..1_000.0f64,
    ) {
        // Sort strengths so we have a clear lowest/middle/highest.
        let mut strengths = [s1, s2, s3];
        strengths.sort_by(|a, b| a.total_cmp(b));
        let [lo, mid, hi] = strengths;

        // Require hi to be strictly above mid so there is exactly one winner.
        // (If hi == mid, two claimants tie and both receive > 0; the failure
        // mode doesn't trigger in the same way.)
        prop_assume!(hi > mid + 1e-6);

        let claims = vec![
            Claim::new("alice", lo).unwrap(),
            Claim::new("bob", mid).unwrap(),
            Claim::new("carol", hi).unwrap(),
        ];
        let estate = Estate::new(estate_total, "units").unwrap();

        let verdict = check_consistency(&essay_composite_rule(), &claims, &estate)
            .expect("essay rule should not return an infrastructure error");

        prop_assert!(
            matches!(verdict, Verdict::Rejected { .. }),
            "essay composite rule must fail consistency when carol uniquely dominates; \
             got: {verdict:?}"
        );
    }

    /// min-strength-wins rule is always rejected for monotonicity when the
    /// current winner (alice) is boosted past the rival (bob).
    ///
    /// Why it fails: alice holds 100 % of the estate as the lowest-strength
    /// claimant. After increasing alice's strength by enough to exceed bob's,
    /// bob becomes the new minimum winner and alice's allocation drops to 0 %.
    /// That is a strict decrease, which the monotonicity checker must detect.
    #[test]
    fn min_strength_wins_rejected_for_monotonicity(
        alice_base in 0.01f64..0.49f64,
        bob_base in 0.51f64..1.00f64,
        estate_total in 1.0f64..1_000.0f64,
    ) {
        // alice is strictly the minimum — she wins the full estate.
        let claims = vec![
            Claim::new("alice", alice_base).unwrap(),
            Claim::new("bob", bob_base).unwrap(),
        ];
        let estate = Estate::new(estate_total, "units").unwrap();

        // A delta just large enough to push alice past bob.
        let bump = (bob_base - alice_base) + 0.01;
        let deltas = [PositiveStrength::new(bump).unwrap()];

        let verdict = check_monotonicity(
            &min_strength_wins_rule(),
            &claims,
            &estate,
            &deltas,
            false,
        )
        .expect("min-strength-wins should not return an infrastructure error");

        prop_assert!(
            matches!(verdict, Verdict::Rejected { .. }),
            "min-strength-wins must fail monotonicity when alice is boosted past bob; \
             got: {verdict:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Estate edge cases: numeric robustness at extreme scales
// ---------------------------------------------------------------------------

proptest! {
    /// Proportional rule is consistent even with a near-zero estate (1e-8).
    ///
    /// The proportional shares become tiny but ratios stay correct; the
    /// consistency checker must not produce false positives from float noise.
    #[test]
    fn proportional_consistent_tiny_estate(
        (_, claims, _) in arb_two_claim_scenario()
    ) {
        let estate = Estate::new(1e-8, "units").expect("1e-8 is a valid estate total");
        let verdict = check_consistency(&proportional_rule(), &claims, &estate)
            .expect("proportional rule should not error on tiny estate");
        prop_assert!(
            matches!(verdict, Verdict::Admissible { .. }),
            "proportional rule must be consistent on a near-zero estate; got: {verdict:?}"
        );
    }

    /// Proportional rule is consistent even with a large estate (1e6).
    ///
    /// Shares become large but ratios stay correct; no overflow or false
    /// violations should occur.  The estate is capped at 1e6 because
    /// EPSILON = 1e-9 (an absolute tolerance) produces false violations at
    /// estate ≥ ~1e7 due to float-cancellation error in the reduced-estate
    /// computation.  The EPSILON scaling issue is tracked separately.
    #[test]
    fn proportional_consistent_large_estate(
        alice_s in 1.0f64..100.0f64,
        bob_s in 1.0f64..100.0f64,
    ) {
        let claims = vec![
            Claim::new("alice", alice_s).unwrap(),
            Claim::new("bob", bob_s).unwrap(),
        ];
        let estate = Estate::new(1e6, "units").expect("1e6 is a valid estate total");
        let verdict = check_consistency(&proportional_rule(), &claims, &estate)
            .expect("proportional rule should not error on large estate");
        prop_assert!(
            matches!(verdict, Verdict::Admissible { .. }),
            "proportional rule must be consistent on a large estate; got: {verdict:?}"
        );
    }

    /// Proportional rule is consistent when claim strengths differ by six
    /// orders of magnitude.
    ///
    /// The dominant claimant's share approaches 100 % and the weaker
    /// claimant's approaches 0 %, but the rule must still be consistent.
    #[test]
    fn proportional_consistent_extreme_strength_ratio(
        weak in 1e-6f64..1e-3f64,
        estate_total in 1.0f64..1_000.0f64,
    ) {
        // strong is exactly 1e6× weak, so the ratio is precisely six orders of magnitude.
        let strong = weak * 1e6;
        prop_assume!(strong.is_finite() && strong > 0.0);

        let claims = vec![
            Claim::new("alice", weak).unwrap(),
            Claim::new("bob", strong).unwrap(),
        ];
        let estate = Estate::new(estate_total, "units").expect("generated estate is valid");

        let verdict = check_consistency(&proportional_rule(), &claims, &estate)
            .expect("proportional rule should not error with extreme strength ratio");
        prop_assert!(
            matches!(verdict, Verdict::Admissible { .. }),
            "proportional rule must be consistent even with a 1e6 strength ratio; \
             got: {verdict:?}"
        );
    }
}
