use std::{collections::BTreeMap, path::PathBuf};

use legitimacy::{
    Allocation, Claim, Claimant, Estate, PositiveStrength, Rule, RuleSpec,
    compiler::{Family, compile},
    mechanism::StrategyproofnessVerdict,
    policy::{compile_policy, load_policy_file},
    rules::{essay_composite_rule, proportional_rule},
};

fn example_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join(name)
}

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
fn compile_rejects_essay_rule_on_all_three_axioms() {
    let rule = essay_composite_rule();
    let claims = vec![
        essay_claim("alpha", 0.35, 0.20, 0.25, 1.0, 1.0, 0.0),
        essay_claim("bravo", 0.65, 0.65, 0.70, -0.5, 0.55, 2.0),
        essay_claim("charlie", 0.45, 0.30, 0.47, -1.0, 1.0, 0.0),
        essay_claim("delta", 0.10, 0.00, 0.10, 0.0, 1.0, 0.0),
    ];
    let claimants = vec![
        claimant("alpha", "standard"),
        claimant("bravo", "standard"),
        claimant("charlie", "standard"),
        claimant("delta", "standard"),
    ];
    let estate = Estate {
        total: 100.0.try_into().unwrap(),
        unit: "compute".to_string(),
    };
    let family = Family {
        reductions: true,
        shocks: vec![0.6],
        strengthening_deltas: vec![PositiveStrength::new(0.2).unwrap()],
        monotonicity_inversion: false,
    };

    let compiled = compile(&rule, &claims, &estate, &claimants, &family).unwrap();

    assert!(!compiled.is_admissible());
    assert_eq!(compiled.axiom_verdicts.len(), 3);
    assert!(
        compiled
            .axiom_verdicts
            .iter()
            .all(|verdict| matches!(verdict, legitimacy::Verdict::Rejected { .. }))
    );
}

#[test]
fn compile_flags_proportional_rule_as_axiom_clean_but_manipulable() {
    let rule = proportional_rule();
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
    let estate = Estate {
        total: 12.0.try_into().unwrap(),
        unit: "units".to_string(),
    };
    let family = Family {
        reductions: true,
        shocks: vec![0.5, 1.5],
        strengthening_deltas: vec![
            PositiveStrength::new(0.1).unwrap(),
            PositiveStrength::new(0.5).unwrap(),
        ],
        monotonicity_inversion: false,
    };

    let compiled = compile(&rule, &claims, &estate, &claimants, &family).unwrap();

    assert!(!compiled.is_admissible());
    assert!(
        compiled
            .axiom_verdicts
            .iter()
            .all(|verdict| matches!(verdict, legitimacy::Verdict::Admissible { .. }))
    );
    assert!(compiled.axiom_verdicts.iter().any(|verdict| matches!(
        verdict,
        legitimacy::Verdict::Admissible { axiom, .. } if axiom.contains("consistency")
    )));
    assert!(matches!(
        compiled.strategyproofness,
        StrategyproofnessVerdict::Manipulable { .. }
    ));
}

#[test]
fn compile_short_circuits_after_bilateral_rejection() {
    let rule = Rule {
        name: "first-claimant-wins".to_string(),
        version: "0.1.0".to_string(),
        rule_spec: RuleSpec::programmatic(
            |claims: &[Claim],
             estate: &Estate|
             -> Result<Allocation, legitimacy::LegitimacyError> {
                if claims.len() == 2 {
                    panic!(
                        "compiler should not evaluate two-claimant reductions after bilateral failure"
                    );
                }

                let mut allocation = Allocation::default();
                if let Some(first) = claims.first() {
                    allocation.insert(first.claimant_id.clone(), estate.total.value() / 2.0);
                    if let Some(second) = claims.get(1) {
                        allocation.insert(second.claimant_id.clone(), estate.total.value() / 2.0);
                    }
                    for claim in &claims[2..] {
                        allocation.insert(claim.claimant_id.clone(), 0.0);
                    }
                }
                Ok(allocation)
            },
        ),
        priority_classes: vec!["standard".to_string()],
    };
    let claims = vec![
        Claim::new("alpha", 1.0).unwrap(),
        Claim::new("bravo", 2.0).unwrap(),
        Claim::new("charlie", 3.0).unwrap(),
        Claim::new("delta", 4.0).unwrap(),
    ];
    let claimants = vec![
        claimant("alpha", "standard"),
        claimant("bravo", "standard"),
        claimant("charlie", "standard"),
        claimant("delta", "standard"),
    ];
    let estate = Estate {
        total: 12.0.try_into().unwrap(),
        unit: "units".to_string(),
    };
    let family = Family {
        reductions: true,
        shocks: vec![0.5, 1.5],
        strengthening_deltas: vec![PositiveStrength::new(0.1).unwrap()],
        monotonicity_inversion: false,
    };

    let compiled = compile(&rule, &claims, &estate, &claimants, &family).unwrap();

    assert!(!compiled.is_admissible());
    assert!(matches!(
        compiled.axiom_verdicts.first(),
        Some(legitimacy::Verdict::Rejected { axiom, .. })
            if axiom == "consistency (Young full sub-coalition)"
    ));
}

#[test]
fn compile_policy_compiles_promotion_gate_end_to_end() {
    let compiled = compile_policy(example_path("promotion-gate.rule.toml"))
        .expect("promotion_gate example should compile");

    assert_eq!(compiled.name, "subagent-promotion");
    assert_eq!(compiled.version, "1.0");
    assert!(!compiled.is_admissible());
    assert_eq!(compiled.axiom_verdicts.len(), 3);
    assert!(compiled.family_description.contains("reductions=true"));
    assert!(compiled.family_description.contains("0.5"));
    assert!(compiled.family_description.contains("1"));
    assert!(!compiled.compiled_at.is_empty());
    assert!(matches!(
        compiled.strategyproofness,
        StrategyproofnessVerdict::Manipulable { .. }
    ));
}

#[test]
fn compile_skips_consistency_when_reductions_are_disabled() {
    let rule = proportional_rule();
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
    let estate = Estate {
        total: 12.0.try_into().unwrap(),
        unit: "units".to_string(),
    };
    let family = Family {
        reductions: false,
        shocks: vec![0.5, 1.5],
        strengthening_deltas: vec![
            PositiveStrength::new(0.1).unwrap(),
            PositiveStrength::new(0.5).unwrap(),
        ],
        monotonicity_inversion: false,
    };

    let compiled = compile(&rule, &claims, &estate, &claimants, &family).unwrap();

    assert!(!compiled.is_admissible());
    assert_eq!(compiled.axiom_verdicts.len(), 2);
    assert!(
        compiled
            .axiom_verdicts
            .iter()
            .all(|verdict| !matches!(verdict, legitimacy::Verdict::Admissible { axiom, .. } if axiom.contains("consistency")))
    );
    assert!(compiled.family_description.contains("reductions=false"));
    assert!(matches!(
        compiled.strategyproofness,
        StrategyproofnessVerdict::Manipulable { .. }
    ));
}

#[test]
fn compile_policy_accepts_strategyproof_permissions_example() {
    let parsed = load_policy_file(example_path("claude-agent-sdk-permissions.rule.toml"))
        .expect("permissions example should parse");
    let compiled = compile(
        &parsed.rule,
        &parsed.claims,
        &parsed.estate,
        &parsed.claimants,
        &parsed.family,
    )
    .expect("permissions example should compile");

    assert!(compiled.is_admissible(), "{compiled:#?}");
    assert!(matches!(
        compiled.strategyproofness,
        StrategyproofnessVerdict::Strategyproof
    ));
}
