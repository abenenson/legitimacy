use std::collections::BTreeMap;

use legitimacy::{
    Allocation, Claim, Claimant, Estate, Rule, RuleSpec,
    paradox::{ParadoxType, run_paradox_suite},
    rules::{essay_composite_rule, jefferson_rule, proportional_rule, webster_rule},
};

fn standard_claimant(id: &str) -> Claimant {
    Claimant {
        id: id.to_string(),
        priority_class: "standard".to_string(),
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

fn mean_proximity_rule() -> Rule {
    Rule {
        name: "mean-proximity".to_string(),
        version: "0.1.0".to_string(),
        rule_spec: RuleSpec::programmatic(mean_proximity_allocate),
        priority_classes: vec!["standard".to_string()],
    }
}

fn mean_proximity_allocate(
    claims: &[Claim],
    estate: &Estate,
) -> Result<Allocation, legitimacy::LegitimacyError> {
    let mean = claims
        .iter()
        .map(|claim| claim.strength.value())
        .sum::<f64>()
        / claims.len() as f64;
    let weights: Vec<(String, f64)> = claims
        .iter()
        .map(|claim| {
            let proximity = 1.0 / (1.0 + (claim.strength.value() - mean).abs());
            let tie_break = claim.strength.value() * 0.01;
            (claim.claimant_id.clone(), proximity + tie_break)
        })
        .collect();
    let total_weight: f64 = weights.iter().map(|(_, weight)| *weight).sum();

    Ok(weights
        .into_iter()
        .map(|(claimant_id, weight)| (claimant_id, estate.total.value() * weight / total_weight))
        .collect())
}

#[test]
fn paradox_essay_rule_reports_claimant_addition_violation() {
    let rule = essay_composite_rule();
    let claims = vec![
        essay_claim("alpha", 0.95, 0.80, 0.80, 0.0, 1.0, 0.0),
        essay_claim("bravo", 0.70, 0.60, 0.70, 0.0, 1.0, 0.0),
        essay_claim("charlie", 0.50, 0.50, 0.55, 0.0, 1.0, 0.0),
        essay_claim("delta", 0.10, 0.10, 0.10, 0.0, 1.0, 0.0),
    ];
    let claimants = vec![
        standard_claimant("alpha"),
        standard_claimant("bravo"),
        standard_claimant("charlie"),
        standard_claimant("delta"),
    ];
    let estate = Estate {
        total: 100.0.try_into().unwrap(),
        unit: "compute".to_string(),
    };

    let violations = run_paradox_suite(&rule, &claims, &estate, &claimants).unwrap();

    assert!(violations.iter().any(|violation| {
        violation.paradox_type == ParadoxType::ClaimantAddition
            && violation.description.contains("Adding claimant")
    }));
}

#[test]
fn paradox_essay_rule_reports_population_violation() {
    let rule = essay_composite_rule();
    let claims = vec![
        essay_claim("alpha", 0.70, 0.95, 0.50, 0.0, 0.60, 2.0),
        essay_claim("bravo", 0.75, 0.70, 0.70, 0.0, 1.0, 0.0),
        essay_claim("charlie", 0.50, 0.50, 0.55, 0.0, 1.0, 0.0),
        essay_claim("delta", 0.10, 0.10, 0.10, 0.0, 1.0, 0.0),
    ];
    let claimants = vec![
        standard_claimant("alpha"),
        standard_claimant("bravo"),
        standard_claimant("charlie"),
        standard_claimant("delta"),
    ];
    let estate = Estate {
        total: 100.0.try_into().unwrap(),
        unit: "compute".to_string(),
    };

    let violations = run_paradox_suite(&rule, &claims, &estate, &claimants).unwrap();

    assert!(violations.iter().any(|violation| {
        violation.paradox_type == ParadoxType::Population
            && violation.description.contains("Strengthening alpha")
    }));
}

#[test]
fn paradox_suite_reports_priority_violation() {
    let rule = mean_proximity_rule();
    let claims = vec![
        Claim::new("alpha", 0.9).unwrap(),
        Claim::new("bravo", 0.4).unwrap(),
    ];
    let claimants = vec![standard_claimant("alpha"), standard_claimant("bravo")];
    let estate = Estate {
        total: 1.0.try_into().unwrap(),
        unit: "attention".to_string(),
    };

    let violations = run_paradox_suite(&rule, &claims, &estate, &claimants).unwrap();

    assert!(violations.iter().any(|violation| {
        violation.paradox_type == ParadoxType::Priority
            && violation.description.contains("alpha and bravo")
    }));
}

fn dominant_one_seat_problem() -> (Vec<Claim>, Vec<Claimant>, Estate) {
    let claims = vec![
        Claim::new("alpha", 100.0).unwrap(),
        Claim::new("bravo", 10.0).unwrap(),
    ];
    let claimants = vec![standard_claimant("alpha"), standard_claimant("bravo")];
    let estate = Estate::new(1.0, "seat").unwrap();
    (claims, claimants, estate)
}

#[test]
fn divisor_rules_avoid_claimant_addition_on_dominant_one_seat_problem() {
    let (claims, claimants, estate) = dominant_one_seat_problem();

    for rule in [jefferson_rule(), webster_rule()] {
        let violations = run_paradox_suite(&rule, &claims, &estate, &claimants).unwrap();

        assert!(
            !violations
                .iter()
                .any(|violation| violation.paradox_type == ParadoxType::ClaimantAddition),
            "{} should avoid claimant-addition on the dominant one-seat problem; got {violations:?}",
            rule.name,
        );
    }
}

#[test]
fn proportional_rule_still_reports_claimant_addition_on_dominant_one_seat_problem() {
    let (claims, claimants, estate) = dominant_one_seat_problem();

    let violations = run_paradox_suite(&proportional_rule(), &claims, &estate, &claimants).unwrap();

    assert!(violations.iter().any(|violation| {
        violation.paradox_type == ParadoxType::ClaimantAddition
            && violation.description.contains("Adding claimant")
    }));
}
