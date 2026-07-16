use std::collections::BTreeMap;

use legitimacy::{
    Claim, Claimant, Estate, compute_factor_exposure,
    factor::compute_factor_exposure_with_family,
    rules::{essay_composite_rule, proportional_rule},
};

fn claimant(id: &str, priority_class: &str) -> Claimant {
    Claimant {
        id: id.to_string(),
        priority_class: priority_class.to_string(),
        attributes: BTreeMap::new(),
    }
}

fn essay_claim(
    id: &str,
    strength: f64,
    diversity: f64,
    peer_relative: f64,
    scarcity_bonus: f64,
    specialization_floor: f64,
    specialization_penalty: f64,
) -> Claim {
    Claim::new(id, strength)
        .unwrap()
        .with_metric("diversity", diversity)
        .with_metric("peer_relative", peer_relative)
        .with_metric("scarcity_bonus", scarcity_bonus)
        .with_metric("specialization_floor", specialization_floor)
        .with_metric("specialization_penalty", specialization_penalty)
}

#[test]
fn essay_rule_has_high_exposure_on_all_five_factors() {
    let claims = vec![
        essay_claim("alpha", 0.35, 0.20, 0.25, 1.0, 1.0, 0.0),
        essay_claim("bravo", 0.65, 0.65, 0.70, -0.5, 0.55, 2.0),
        essay_claim("charlie", 0.45, 0.30, 0.47, -1.0, 1.0, 0.0),
        essay_claim("delta", 0.10, 0.00, 0.10, 0.0, 1.0, 0.0),
    ];
    let estate = Estate::new(100.0, "compute").unwrap();

    let exposure = compute_factor_exposure(&essay_composite_rule(), &claims, &estate).unwrap();

    assert!(exposure.consistency >= 0.75);
    assert!(exposure.solidarity >= 0.75);
    assert!(exposure.monotonicity >= 0.75);
    assert!(exposure.strategyproofness >= 0.75);
    assert_eq!(exposure.nonvacuity, 0.0);
}

#[test]
fn proportional_rule_has_zero_axiom_exposure_but_nonzero_strategyproofness() {
    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 2.0).unwrap(),
        Claim::new("carol", 3.0).unwrap(),
    ];
    let claimants = vec![
        claimant("alice", "standard"),
        claimant("bob", "standard"),
        claimant("carol", "standard"),
    ];
    let estate = Estate::new(12.0, "units").unwrap();
    let family = legitimacy::Family {
        reductions: true,
        shocks: vec![0.5, 1.5],
        strengthening_deltas: vec![
            legitimacy::PositiveStrength::new(0.1).unwrap(),
            legitimacy::PositiveStrength::new(0.5).unwrap(),
        ],
        monotonicity_inversion: false,
    };

    let exposure = compute_factor_exposure_with_family(
        &proportional_rule(),
        &claims,
        &claimants,
        &estate,
        &family,
    )
    .unwrap();

    assert_eq!(exposure.consistency, 0.0);
    assert_eq!(exposure.solidarity, 0.0);
    assert_eq!(exposure.monotonicity, 0.0);
    assert!(exposure.strategyproofness > 0.0);
    assert_eq!(exposure.nonvacuity, 0.0);
}
