use std::collections::BTreeMap;

use legitimacy::{
    Allocation, Claim, Estate, GovernanceClaim, GovernanceNode, NodeId, Rule, RuleSpec,
    check_binary_strategyproofness, check_strategyproofness,
    graph::{Decision, GateLogic},
    mechanism::StrategyproofnessVerdict,
};

fn threshold_rule() -> Rule {
    Rule {
        name: "threshold-like".to_string(),
        version: "0.1.0".to_string(),
        rule_spec: RuleSpec::programmatic(|claims: &[Claim], _estate: &Estate| {
            Ok(claims
                .iter()
                .map(|claim| {
                    (
                        claim.claimant_id.clone(),
                        if claim.strength.value() >= 0.7 {
                            1.0
                        } else {
                            0.0
                        },
                    )
                })
                .collect::<Allocation>())
        }),
        priority_classes: vec!["standard".to_string()],
    }
}

fn governance_claim(id: &str, strength: f64) -> GovernanceClaim {
    GovernanceClaim {
        claimant_id: id.to_string(),
        strength,
        priority_class: None,
        path: None,
        action: None,
        content: None,
        metrics: BTreeMap::new(),
    }
}

#[test]
fn proportional_rule_is_manipulable() {
    let estate = Estate::new(12.0, "units").unwrap();
    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 2.0).unwrap(),
        Claim::new("carol", 3.0).unwrap(),
    ];

    let verdict =
        check_strategyproofness(&legitimacy::rules::proportional_rule(), &claims, &estate).unwrap();

    match verdict {
        StrategyproofnessVerdict::Manipulable {
            claimant,
            true_strength,
            reported,
            true_alloc,
            manipulated_alloc,
        } => {
            assert_eq!(claimant, "alice");
            assert_eq!(true_strength, 1.0);
            assert_eq!(reported, 1.2);
            assert_eq!(true_alloc, 2.0);
            assert!(manipulated_alloc > true_alloc);
        }
        StrategyproofnessVerdict::Strategyproof => {
            panic!("proportional rule should be manipulable on this instance")
        }
    }
}

#[test]
fn threshold_rule_can_be_strategyproof_on_a_safe_instance() {
    let estate = Estate::new(2.0, "permits").unwrap();
    let claims = vec![
        Claim::new("alice", 0.8).unwrap(),
        Claim::new("bob", 0.9).unwrap(),
    ];

    let verdict = check_strategyproofness(&threshold_rule(), &claims, &estate).unwrap();

    assert_eq!(verdict, StrategyproofnessVerdict::Strategyproof);
}

#[test]
fn threshold_node_is_strategyproof_on_a_safe_instance() {
    let node = GovernanceNode::Threshold {
        id: NodeId::new("gate").unwrap(),
        name: "gate".to_string(),
        threshold: 0.7,
        field: "strength".to_string(),
    };
    let claims = vec![governance_claim("alice", 0.8), governance_claim("bob", 0.9)];

    let verdict = check_binary_strategyproofness(&node, &claims).unwrap();

    assert_eq!(verdict, StrategyproofnessVerdict::Strategyproof);
}

#[test]
fn binary_threshold_node_detects_upward_misreports() {
    let node = GovernanceNode::Threshold {
        id: NodeId::new("gate").unwrap(),
        name: "gate".to_string(),
        threshold: 0.7,
        field: "strength".to_string(),
    };
    let claims = vec![governance_claim("alice", 0.6), governance_claim("bob", 0.9)];

    let verdict = check_binary_strategyproofness(&node, &claims).unwrap();

    match verdict {
        StrategyproofnessVerdict::Manipulable {
            claimant,
            true_strength,
            reported,
            true_alloc,
            manipulated_alloc,
        } => {
            assert_eq!(claimant, "alice");
            assert_eq!(true_strength, 0.6);
            assert_eq!(reported, 0.72);
            assert_eq!(true_alloc, 0.0);
            assert_eq!(manipulated_alloc, 2.0);
        }
        StrategyproofnessVerdict::Strategyproof => {
            panic!("upward threshold misreport should be detected")
        }
    }
}

#[test]
fn threshold_binary_fixture_uses_terminal_ranks() {
    let node = GovernanceNode::Binary {
        id: NodeId::new("binary").unwrap(),
        name: "binary".to_string(),
        gates: Vec::new(),
        default: Decision::Permit,
        combination: GateLogic::FirstMatch,
    };

    let verdict = check_binary_strategyproofness(&node, &[governance_claim("alice", 1.0)]).unwrap();

    assert_eq!(verdict, StrategyproofnessVerdict::Strategyproof);
}
