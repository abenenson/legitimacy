use std::collections::BTreeMap;

use legitimacy::{
    Allocation, Claim, Claimant, Estate, LegitimacyError, PositiveStrength, Rule, RuleSpec,
    Verdict,
    axioms::{
        consistency::check_consistency, monotonicity::check_monotonicity,
        solidarity::check_solidarity,
    },
    rules::proportional_rule,
};
use proptest::{prelude::*, test_runner::Config as ProptestConfig};

fn standard_claimant(id: &str) -> Claimant {
    Claimant {
        id: id.to_string(),
        priority_class: "standard".to_string(),
        attributes: BTreeMap::new(),
    }
}

fn decade_value(min_exp: i32, max_exp: i32, exact_max: f64) -> impl Strategy<Value = f64> {
    prop_oneof![
        Just(10f64.powi(min_exp)),
        Just(exact_max),
        (min_exp..max_exp, 0u32..1_000_000u32).prop_map(|(exp, bucket)| {
            let low = 10f64.powi(exp);
            let high = 10f64.powi(exp + 1);
            let fraction = bucket as f64 / 1_000_000.0;
            low + (high - low) * fraction
        }),
    ]
}

fn arb_scaled_estate() -> impl Strategy<Value = Estate> {
    decade_value(0, 12, 1e12)
        .prop_map(|total| Estate::new(total, "units").expect("generated estate should be valid"))
}

fn arb_scaled_claim(id: &'static str) -> impl Strategy<Value = Claim> {
    decade_value(-6, 6, 1e6).prop_map(move |strength| {
        Claim::new(id, strength).expect("generated claim should be valid")
    })
}

fn arb_scaled_three_claim_scenario() -> impl Strategy<Value = (Vec<Claimant>, Vec<Claim>, Estate)> {
    (
        arb_scaled_claim("alice"),
        arb_scaled_claim("bob"),
        arb_scaled_claim("carol"),
        arb_scaled_estate(),
    )
        .prop_map(|(alice, bob, carol, estate)| {
            (
                vec![
                    standard_claimant("alice"),
                    standard_claimant("bob"),
                    standard_claimant("carol"),
                ],
                vec![alice, bob, carol],
                estate,
            )
        })
}

fn count_dependent_rule() -> Rule {
    Rule {
        name: "count-dependent".to_string(),
        version: "0.1.0".to_string(),
        rule_spec: RuleSpec::programmatic(
            |claims: &[Claim], estate: &Estate| -> Result<Allocation, LegitimacyError> {
                let mut allocation = Allocation::default();

                if claims.is_empty() {
                    return Ok(allocation);
                }

                if claims.len() == 3 {
                    let share = estate.total.value() / 3.0;
                    for claim in claims {
                        allocation.insert(claim.claimant_id.clone(), share);
                    }
                    return Ok(allocation);
                }

                let total_strength: f64 = claims.iter().map(|claim| claim.strength.value()).sum();
                for claim in claims {
                    allocation.insert(
                        claim.claimant_id.clone(),
                        estate.total.value() * claim.strength.value() / total_strength,
                    );
                }

                Ok(allocation)
            },
        ),
        priority_classes: vec!["standard".to_string()],
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn proportional_axioms_hold_across_large_estate_scales(
        (claimants, claims, estate) in arb_scaled_three_claim_scenario()
    ) {
        let consistency = check_consistency(&proportional_rule(), &claims, &estate)
            .expect("proportional consistency check should not error at scale");
        prop_assert!(
            matches!(consistency, Verdict::Admissible { .. }),
            "proportional consistency must remain admissible at scale; got: {consistency:?}"
        );

        let solidarity = check_solidarity(
            &proportional_rule(),
            &claims,
            &estate,
            &claimants,
            &[0.1, 0.5, 2.0, 10.0],
        )
        .expect("proportional solidarity check should not error at scale");
        prop_assert!(
            matches!(solidarity, Verdict::Admissible { .. }),
            "proportional solidarity must remain admissible at scale; got: {solidarity:?}"
        );

        let monotonicity = check_monotonicity(
            &proportional_rule(),
            &claims,
            &estate,
            &[
                PositiveStrength::new(1e-6).unwrap(),
                PositiveStrength::new(1.0).unwrap(),
                PositiveStrength::new(1e6).unwrap(),
            ],
            false,
        )
        .expect("proportional monotonicity check should not error at scale");
        prop_assert!(
            matches!(monotonicity, Verdict::Admissible { .. }),
            "proportional monotonicity must remain admissible at scale; got: {monotonicity:?}"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn count_dependent_rule_still_fails_consistency_at_extreme_scales(
        low in decade_value(-6, 6, 1e6),
        middle in decade_value(-6, 6, 1e6),
        high in decade_value(-6, 6, 1e6),
        estate in arb_scaled_estate(),
    ) {
        let mut strengths = [low, middle, high];
        strengths.sort_by(|left, right| left.total_cmp(right));
        prop_assume!(strengths[1] + 1e-12 < strengths[2]);

        let claims = vec![
            Claim::new("alice", strengths[0]).unwrap(),
            Claim::new("bob", strengths[1]).unwrap(),
            Claim::new("carol", strengths[2]).unwrap(),
        ];

        let verdict = check_consistency(&count_dependent_rule(), &claims, &estate)
            .expect("count-dependent consistency check should not infrastructure-fail");
        prop_assert!(
            matches!(verdict, Verdict::Rejected { .. }),
            "count-dependent rule must still be rejected at scale; got: {verdict:?}"
        );
    }
}
