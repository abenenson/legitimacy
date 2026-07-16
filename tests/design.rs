//! Core API design regression tests for allocation validation, stateful
//! programmatic rules, and compiler rejection of malformed allocations.

use std::collections::BTreeMap;

use legitimacy::{Allocation, Claim, Claimant, Estate, Family, Rule, RuleSpec, compiler::compile};

#[test]
fn allocation_validate_rejects_missing_or_negative_entries() {
    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 2.0).unwrap(),
    ];

    let mut missing = Allocation::default();
    missing.insert("alice".to_string(), 1.0);
    assert!(
        missing
            .validate(&claims)
            .expect_err("missing claimant coverage must fail")
            .to_string()
            .contains("missing claimant 'bob'")
    );

    let mut negative = Allocation::default();
    negative.insert("alice".to_string(), 1.0);
    negative.insert("bob".to_string(), -0.5);
    assert!(
        negative
            .validate(&claims)
            .expect_err("negative allocations must fail")
            .to_string()
            .contains("must be non-negative and finite")
    );
}

#[test]
fn rule_supports_stateful_allocator_closures() {
    let multiplier = 0.5;
    let rule = Rule {
        name: "capturing-closure".to_string(),
        version: "0.1.0".to_string(),
        rule_spec: RuleSpec::programmatic(move |claims: &[Claim], estate: &Estate| {
            let per_claim = estate.total * multiplier / claims.len() as f64;
            Ok(claims
                .iter()
                .map(|claim| (claim.claimant_id.clone(), per_claim))
                .collect())
        }),
        priority_classes: vec!["standard".to_string()],
    };
    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 1.0).unwrap(),
    ];
    let estate = Estate {
        total: 10.0.try_into().unwrap(),
        unit: "units".to_string(),
    };

    let allocation = rule.allocate(&claims, &estate).unwrap();

    assert_eq!(allocation["alice"], 2.5);
    assert_eq!(allocation["bob"], 2.5);
}

#[test]
fn compiler_rejects_partial_allocations() {
    let rule = Rule {
        name: "partial".to_string(),
        version: "0.1.0".to_string(),
        rule_spec: RuleSpec::programmatic(|claims: &[Claim], _estate: &Estate| {
            let mut allocation = Allocation::default();
            allocation.insert(claims[0].claimant_id.clone(), 1.0);
            Ok(allocation)
        }),
        priority_classes: vec!["standard".to_string()],
    };
    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 1.0).unwrap(),
    ];
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
    let estate = Estate {
        total: 1.0.try_into().unwrap(),
        unit: "units".to_string(),
    };
    let family = Family {
        reductions: true,
        shocks: vec![0.5],
        strengthening_deltas: vec![legitimacy::PositiveStrength::new(0.1).unwrap()],
        monotonicity_inversion: false,
    };

    let error = compile(&rule, &claims, &estate, &claimants, &family)
        .expect_err("partial allocations must fail closed");
    assert!(
        error
            .to_string()
            .contains("allocation is missing claimant 'bob'")
    );
}

#[test]
fn rule_rejects_allocations_that_exceed_estate() {
    let rule = Rule {
        name: "over-allocate".to_string(),
        version: "0.1.0".to_string(),
        rule_spec: RuleSpec::programmatic(|claims: &[Claim], _estate: &Estate| {
            Ok(claims
                .iter()
                .map(|claim| (claim.claimant_id.clone(), 10.0))
                .collect())
        }),
        priority_classes: vec!["standard".to_string()],
    };
    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 1.0).unwrap(),
    ];
    let estate = Estate {
        total: 10.0.try_into().unwrap(),
        unit: "units".to_string(),
    };

    let error = rule
        .allocate(&claims, &estate)
        .expect_err("allocations above the estate total must fail closed");

    assert!(error.to_string().contains("exceeds estate total"));
}
