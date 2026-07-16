//! Integration tests for the three graph-diagnostic axiom checkers.
//!
//! Each test uses `proportional_rule` as a positive control — a rule that
//! satisfies all three axioms by construction. The goal is to verify that
//! the checkers accept a correct rule before they are used to reject bad ones.

use std::collections::BTreeMap;

use legitimacy::{
    Claim, Claimant, Estate, PositiveStrength, RuleSpec, Verdict,
    axioms::{
        consistency::check_consistency, monotonicity::check_monotonicity,
        solidarity::check_solidarity,
    },
    rules::proportional_rule,
};

fn standard_problem() -> (Vec<Claimant>, Vec<Claim>, Estate) {
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
        Claimant {
            id: "carol".to_string(),
            priority_class: "standard".to_string(),
            attributes: BTreeMap::new(),
        },
    ];
    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 2.0).unwrap(),
        Claim::new("carol", 3.0).unwrap(),
    ];
    let estate = Estate {
        total: 6.0.try_into().unwrap(),
        unit: "units".to_string(),
    };
    (claimants, claims, estate)
}

#[test]
fn proportional_passes_consistency() {
    let (_, claims, estate) = standard_problem();
    let rule = proportional_rule();
    let v = check_consistency(&rule, &claims, &estate);
    assert!(
        matches!(v, Ok(Verdict::Admissible { .. })),
        "proportional rule must be consistent; got: {v:?}"
    );
}

#[test]
fn proportional_passes_solidarity() {
    let (claimants, claims, estate) = standard_problem();
    let rule = proportional_rule();
    let scale_factors = [0.25, 0.5, 0.75, 1.5, 2.0];
    let v = check_solidarity(&rule, &claims, &estate, &claimants, &scale_factors);
    assert!(
        matches!(v, Ok(Verdict::Admissible { .. })),
        "proportional rule must be solidary; got: {v:?}"
    );
}

#[test]
fn proportional_passes_monotonicity() {
    let (_, claims, estate) = standard_problem();
    let rule = proportional_rule();
    let deltas = [0.1, 0.5, 1.0, 5.0];
    let deltas = deltas.map(|delta| PositiveStrength::new(delta).unwrap());
    let v = check_monotonicity(&rule, &claims, &estate, &deltas, false);
    assert!(
        matches!(v, Ok(Verdict::Admissible { .. })),
        "proportional rule must be monotone; got: {v:?}"
    );
}

/// A rule that uses equal split for exactly 3 claimants, proportional otherwise.
/// This violates consistency: removing one claimant changes the allocation rule
/// that applies to the remaining two, so their shares shift.
#[test]
fn count_dependent_rule_fails_consistency() {
    use legitimacy::Rule;

    let rule = Rule {
        name: "count-dependent".to_string(),
        version: "0.1.0".to_string(),
        rule_spec: RuleSpec::programmatic(|claims: &[Claim], estate: &Estate| {
            let mut out = legitimacy::Allocation::default();
            if claims.len() == 3 {
                // Equal split when exactly three claimants are present.
                let share = estate.total / 3.0;
                for c in claims {
                    out.insert(c.claimant_id.clone(), share);
                }
            } else {
                // Proportional otherwise.
                let total: f64 = claims.iter().map(|c| c.strength).sum();
                for c in claims {
                    out.insert(
                        c.claimant_id.clone(),
                        if total < 1e-12 {
                            estate.total.value() / claims.len().max(1) as f64
                        } else {
                            estate.total.value() * (c.strength.value() / total)
                        },
                    );
                }
            }
            Ok(out)
        }),
        priority_classes: vec!["standard".to_string()],
    };

    let (_, claims, estate) = standard_problem();
    // With 3 claimants (alice/1, bob/2, carol/3), estate=6:
    //   original: equal split → each gets 2.0
    // Remove alice (share=2.0): reduced estate=4.0, 2 remaining.
    //   reduced: proportional → bob gets 2/5*4=1.6, carol gets 3/5*4=2.4
    //   bob's original=2.0, reduced=1.6 → violation detected.
    let v = check_consistency(&rule, &claims, &estate);
    assert!(
        matches!(v, Ok(Verdict::Rejected { .. })),
        "count-dependent rule must fail consistency; got: {v:?}"
    );
}

#[test]
fn claim_try_new_rejects_non_positive_strength() {
    assert!(Claim::try_new("zero", 0.0).is_err());
    assert!(Claim::try_new("negative", -1.0).is_err());
}

#[test]
fn claims_reject_empty_and_duplicate_claimant_ids() {
    assert!(Claim::try_new("   ", 1.0).is_err());
    let duplicate = vec![
        Claim::try_new("alice", 1.0).unwrap(),
        Claim::try_new("alice", 2.0).unwrap(),
    ];

    assert!(Claim::validate_all(&duplicate).is_err());
}

#[test]
fn positive_strength_rejects_zero_even_before_claim_construction() {
    assert!(PositiveStrength::new(0.0).is_err());
}
