use std::collections::BTreeMap;

use legitimacy::{
    Allocation, Claim, Claimant, Estate, Rule, RuleSpec, Verdict,
    axioms::{
        consistency::check_consistency, monotonicity::check_monotonicity,
        solidarity::check_solidarity,
    },
};

fn action_proof_rule() -> Rule {
    Rule {
        name: "action-proof".to_string(),
        version: "0.2.0".to_string(),
        rule_spec: RuleSpec::programmatic(action_proof_allocate),
        priority_classes: vec!["routine".to_string(), "consequential".to_string()],
    }
}

fn action_proof_allocate(
    claims: &[Claim],
    estate: &Estate,
) -> Result<Allocation, legitimacy::LegitimacyError> {
    let weights: Vec<(String, f64)> = claims
        .iter()
        .map(|claim| {
            let consequential = claim.metric("consequential") >= 0.5;
            let explicit_justification = claim.metric("explicit_justification") >= 0.5;

            let weight = if !consequential {
                1.0
            } else if explicit_justification && claim.strength >= 1.0 {
                claim.strength.value()
            } else {
                0.0
            };

            (claim.claimant_id.clone(), weight)
        })
        .collect();

    let total_weight: f64 = weights.iter().map(|(_, weight)| *weight).sum();
    let mut allocation = Allocation::default();

    if total_weight <= 1e-12 {
        for claim in claims {
            allocation.insert(claim.claimant_id.clone(), 0.0);
        }
        return Ok(allocation);
    }

    for (claimant_id, weight) in weights {
        let share = if weight <= 0.0 {
            0.0
        } else {
            estate.total * weight / total_weight
        };
        allocation.insert(claimant_id, share);
    }

    Ok(allocation)
}

fn action_claimant(id: &str, priority_class: &str) -> Claimant {
    Claimant {
        id: id.to_string(),
        priority_class: priority_class.to_string(),
        attributes: BTreeMap::new(),
    }
}

fn action_claim(
    id: &str,
    consequential: bool,
    explicit_justification: bool,
    strength: f64,
) -> Claim {
    Claim::new(id, strength)
        .unwrap()
        .with_metric("consequential", if consequential { 1.0 } else { 0.0 })
        .with_metric(
            "explicit_justification",
            if explicit_justification { 1.0 } else { 0.0 },
        )
}

fn approx_eq(left: f64, right: f64) {
    assert!(
        (left - right).abs() < 1e-9,
        "expected {left:.12} ~= {right:.12}"
    );
}

#[test]
fn action_proof_rule_models_routine_and_consequential_actions() {
    let claims = vec![
        action_claim("write_local_notes", false, false, 0.1),
        action_claim("git_push", true, true, 1.4),
        action_claim("delete_prod_table", true, false, 2.0),
    ];
    let estate = Estate {
        total: 1.0.try_into().unwrap(),
        unit: "authorization".to_string(),
    };

    let allocation = action_proof_rule().allocate(&claims, &estate).unwrap();

    approx_eq(allocation["write_local_notes"], 1.0 / 2.4);
    approx_eq(allocation["git_push"], 1.4 / 2.4);
    approx_eq(allocation["delete_prod_table"], 0.0);
}

#[test]
fn action_proof_rule_passes_consistency() {
    let claims = vec![
        action_claim("write_local_notes", false, false, 0.1),
        action_claim("git_push", true, true, 1.2),
        action_claim("rm_rf_workspace", true, false, 0.8),
    ];
    let estate = Estate {
        total: 1.0.try_into().unwrap(),
        unit: "authorization".to_string(),
    };

    let verdict = check_consistency(&action_proof_rule(), &claims, &estate);
    assert!(
        matches!(verdict, Ok(Verdict::Admissible { .. })),
        "modeled action-proof rule should be consistent; got: {verdict:?}"
    );
}

#[test]
fn action_proof_rule_passes_solidarity() {
    let claimants = vec![
        action_claimant("read_repo", "routine"),
        action_claimant("write_local_notes", "routine"),
        action_claimant("git_push", "consequential"),
        action_claimant("send_message", "consequential"),
    ];
    let claims = vec![
        action_claim("read_repo", false, false, 0.1),
        action_claim("write_local_notes", false, false, 0.1),
        action_claim("git_push", true, true, 1.4),
        action_claim("send_message", true, true, 1.1),
    ];
    let estate = Estate {
        total: 1.0.try_into().unwrap(),
        unit: "authorization".to_string(),
    };

    let verdict = check_solidarity(
        &action_proof_rule(),
        &claims,
        &estate,
        &claimants,
        &[0.5, 1.5],
    );
    assert!(
        matches!(verdict, Ok(Verdict::Admissible { .. })),
        "modeled action-proof rule should be solidary; got: {verdict:?}"
    );
}

#[test]
fn action_proof_rule_passes_monotonicity() {
    let claims = vec![
        action_claim("write_local_notes", false, false, 0.1),
        action_claim("git_push", true, true, 1.0),
        action_claim("send_message", true, true, 1.2),
        action_claim("dangerous_delete", true, false, 2.0),
    ];
    let estate = Estate {
        total: 1.0.try_into().unwrap(),
        unit: "authorization".to_string(),
    };

    let deltas = vec![
        legitimacy::PositiveStrength::new(0.1).unwrap(),
        legitimacy::PositiveStrength::new(0.5).unwrap(),
        legitimacy::PositiveStrength::new(1.0).unwrap(),
    ];
    let verdict = check_monotonicity(&action_proof_rule(), &claims, &estate, &deltas, false);
    assert!(
        matches!(verdict, Ok(Verdict::Admissible { .. })),
        "modeled action-proof rule should be monotone; got: {verdict:?}"
    );
}
