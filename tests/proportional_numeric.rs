use legitimacy::{Claim, Estate, rules::proportional_rule};

fn shares(strengths: &[f64], total: f64) -> Vec<f64> {
    let claims: Vec<_> = strengths
        .iter()
        .enumerate()
        .map(|(i, strength)| Claim::new(format!("claim-{i}"), *strength).unwrap())
        .collect();
    let estate = Estate {
        total: total.try_into().unwrap(),
        unit: "allocation".into(),
    };
    let allocation = proportional_rule().allocate(&claims, &estate).unwrap();
    claims
        .iter()
        .map(|claim| {
            allocation
                .share_for(&claim.claimant_id, "numeric regression")
                .unwrap()
        })
        .collect()
}

#[test]
fn overflowing_finite_strength_total_preserves_equal_nonzero_shares() {
    assert_eq!(shares(&[3e307; 8], 1.0), vec![0.125; 8]);
}

#[test]
fn unequal_large_strengths_preserve_their_ratios() {
    assert_eq!(
        shares(&[f64::MAX, f64::MAX / 2.0, f64::MAX / 2.0], 1.0),
        [0.5, 0.25, 0.25]
    );
    assert_eq!(shares(&[4.0, 2.0, 2.0], 1.0), [0.5, 0.25, 0.25]);
}

#[test]
fn subnormal_strengths_do_not_underflow_the_normalized_allocation() {
    let unit = f64::from_bits(1);
    assert_eq!(shares(&[unit, unit * 2.0, unit], 1.0), [0.25, 0.5, 0.25]);
}

#[test]
fn large_estate_recovers_representable_tiny_claim_share() {
    let unit = f64::from_bits(1);
    let actual = shares(&[f64::MAX, unit], f64::MAX);
    assert_eq!(actual, [f64::MAX, unit]);
}

#[test]
fn tiny_estate_preserves_representable_subnormal_results() {
    let unit = f64::from_bits(1);
    assert_eq!(shares(&[f64::MAX, f64::MAX], unit * 2.0), [unit, unit]);
}

#[test]
fn maximum_estate_and_single_claim_remain_finite() {
    assert_eq!(shares(&[f64::from_bits(1)], f64::MAX), [f64::MAX]);
    assert_eq!(shares(&[f64::MAX], f64::MAX), [f64::MAX]);
    assert!(Estate::new(0.0, "allocation").is_err());
    assert!(shares(&[], 1.0).is_empty());
}
