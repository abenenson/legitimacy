//! Regression tests for the essay-composite example rule and its named
//! consistency, solidarity, and monotonicity counterexamples.

use std::collections::BTreeMap;

use legitimacy::{
    Claim, Claimant, Estate, Verdict,
    axioms::{
        consistency::check_consistency, monotonicity::check_monotonicity,
        solidarity::check_solidarity,
    },
    rules::essay_composite_rule,
};

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

fn standard_claimants(ids: &[&str]) -> Vec<Claimant> {
    ids.iter()
        .map(|id| Claimant {
            id: (*id).to_string(),
            priority_class: "standard".to_string(),
            attributes: BTreeMap::new(),
        })
        .collect()
}

fn approx_eq(left: f64, right: f64) {
    assert!(
        (left - right).abs() < 1e-9,
        "expected {left:.12} ~= {right:.12}"
    );
}

#[test]
fn essay_examples_consistency_violation_names_claimants_and_allocations() {
    let rule = essay_composite_rule();
    let claims = vec![
        essay_claim("alpha", 0.95, 0.80, 0.80, 0.0, 1.0, 0.0),
        essay_claim("bravo", 0.70, 0.60, 0.70, 0.0, 1.0, 0.0),
        essay_claim("charlie", 0.50, 0.50, 0.55, 0.0, 1.0, 0.0),
        essay_claim("delta", 0.10, 0.10, 0.10, 0.0, 1.0, 0.0),
    ];
    let estate = Estate {
        total: 100.0.try_into().unwrap(),
        unit: "compute".to_string(),
    };

    let verdict = check_consistency(&rule, &claims, &estate);
    let Ok(Verdict::Rejected { counterexample, .. }) = verdict else {
        panic!("essay rule should fail consistency");
    };

    assert!(counterexample.description.contains("charlie"));
    assert!(counterexample.description.contains("alpha"));

    approx_eq(
        counterexample.original_allocation["bravo"],
        43.790849673202615,
    );
    approx_eq(counterexample.perturbed_allocation["bravo"], 0.0);
    approx_eq(
        counterexample.original_allocation["alpha"],
        56.20915032679739,
    );
    approx_eq(counterexample.perturbed_allocation["alpha"], 100.0);
}

#[test]
fn essay_examples_solidarity_violation_names_claimants_and_allocations() {
    let rule = essay_composite_rule();
    let claims = vec![
        essay_claim("alpha", 0.35, 0.20, 0.25, 1.0, 1.0, 0.0),
        essay_claim("bravo", 0.65, 0.65, 0.70, -0.5, 1.0, 0.0),
        essay_claim("charlie", 0.45, 0.30, 0.47, -1.0, 1.0, 0.0),
        essay_claim("delta", 0.10, 0.00, 0.10, 0.0, 1.0, 0.0),
    ];
    let claimants = standard_claimants(&["alpha", "bravo", "charlie", "delta"]);
    let estate = Estate {
        total: 100.0.try_into().unwrap(),
        unit: "compute".to_string(),
    };

    let verdict = check_solidarity(&rule, &claims, &estate, &claimants, &[0.6]);
    let Ok(Verdict::Rejected { counterexample, .. }) = verdict else {
        panic!("essay rule should fail solidarity");
    };

    assert!(counterexample.description.contains("alpha"));
    assert!(counterexample.description.contains("charlie"));

    approx_eq(counterexample.original_allocation["alpha"], 0.0);
    approx_eq(counterexample.perturbed_allocation["alpha"], 23.7);
    approx_eq(
        counterexample.original_allocation["charlie"],
        38.19702602230483,
    );
    approx_eq(counterexample.perturbed_allocation["charlie"], 0.0);
}

#[test]
fn essay_examples_monotonicity_violation_names_claimants_and_allocations() {
    let rule = essay_composite_rule();
    let claims = vec![
        essay_claim("alpha", 0.70, 0.95, 0.50, 0.0, 0.60, 2.0),
        essay_claim("bravo", 0.75, 0.70, 0.70, 0.0, 1.0, 0.0),
        essay_claim("charlie", 0.50, 0.50, 0.55, 0.0, 1.0, 0.0),
        essay_claim("delta", 0.10, 0.10, 0.10, 0.0, 1.0, 0.0),
    ];
    let estate = Estate {
        total: 100.0.try_into().unwrap(),
        unit: "compute".to_string(),
    };

    let deltas = [legitimacy::PositiveStrength::new(0.20).unwrap()];
    let verdict = check_monotonicity(&rule, &claims, &estate, &deltas, false);
    let Ok(Verdict::Rejected { counterexample, .. }) = verdict else {
        panic!("essay rule should fail monotonicity");
    };

    assert!(counterexample.description.contains("alpha"));

    approx_eq(
        counterexample.original_allocation["alpha"],
        47.63636363636363,
    );
    approx_eq(
        counterexample.perturbed_allocation["alpha"],
        46.06741573033708,
    );
    approx_eq(
        counterexample.original_allocation["bravo"],
        52.36363636363637,
    );
    approx_eq(
        counterexample.perturbed_allocation["bravo"],
        53.93258426966292,
    );
}
