use std::collections::BTreeMap;

use legitimacy::{
    Claim, Claimant, Estate, PositiveStrength,
    certificate::{CertificationContext, certify},
    compiler::{Family, compile},
    rules::{claude_agent_sdk_permissions_rule, essay_composite_rule},
};

fn claimant(id: &str) -> Claimant {
    Claimant {
        id: id.to_string(),
        priority_class: "standard".to_string(),
        attributes: BTreeMap::new(),
    }
}

fn claimant_with_class(id: &str, priority_class: &str) -> Claimant {
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

fn permission_claim(id: &str, base_authorization: f64) -> Claim {
    Claim::new(id, 1.0)
        .unwrap()
        .with_metric("available", 1.0)
        .with_metric("listed", 1.0)
        .with_metric(
            "denied",
            if base_authorization <= f64::EPSILON {
                1.0
            } else {
                0.0
            },
        )
        .with_metric("base_authorization", base_authorization)
}

fn permissions_runtime() -> (legitimacy::Rule, Vec<Claim>, Vec<Claimant>, Estate, Family) {
    let rule = claude_agent_sdk_permissions_rule();
    let claims = vec![
        permission_claim("Read", 1.0),
        permission_claim("Bash", 0.5),
        permission_claim("WebFetch", 0.0),
    ];
    let claimants = vec![
        claimant_with_class("Read", "always_allow"),
        claimant_with_class("Bash", "ask_user"),
        claimant_with_class("WebFetch", "always_deny"),
    ];
    let estate = Estate {
        total: 1.0.try_into().unwrap(),
        unit: "authorization".to_string(),
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
    (rule, claims, claimants, estate, family)
}

#[test]
fn certificate_certify_returns_ok_for_admissible_rule() {
    let (rule, claims, claimants, estate, family) = permissions_runtime();
    let compiled = compile(&rule, &claims, &estate, &claimants, &family).unwrap();

    let mut evidence = BTreeMap::new();
    evidence.insert("audit_log".to_string(), "run-42".to_string());

    let certificate = certify(
        &CertificationContext {
            compiled_rule: &compiled,
            rule: &rule,
            claims: &claims,
            estate: &estate,
        },
        "Permit Read without further review",
        "Read",
        1.0,
        evidence.clone(),
    )
    .expect("admissible rule should certify");

    assert_eq!(certificate.rule_name, "claude-agent-sdk-permissions");
    assert_eq!(certificate.rule_version, "1.0.0");
    assert_eq!(
        certificate.compiled_rule_hash,
        compiled.content_hash().unwrap()
    );
    assert_eq!(
        certificate.act_description,
        "Permit Read without further review"
    );
    assert_eq!(certificate.claimant_id, "Read");
    assert_eq!(certificate.outcome, 1.0);
    assert_eq!(certificate.evidence, evidence);
    assert!(certificate.admissible);
    assert!(certificate.issued_at.contains('T'));
}

#[test]
fn certificate_certify_returns_err_for_rejected_rule() {
    let rule = essay_composite_rule();
    let claims = vec![
        essay_claim("alpha", 0.35, 0.20, 0.25, 1.0, 1.0, 0.0),
        essay_claim("bravo", 0.65, 0.65, 0.70, -0.5, 0.55, 2.0),
        essay_claim("charlie", 0.45, 0.30, 0.47, -1.0, 1.0, 0.0),
        essay_claim("delta", 0.10, 0.00, 0.10, 0.0, 1.0, 0.0),
    ];
    let claimants = vec![
        claimant("alpha"),
        claimant("bravo"),
        claimant("charlie"),
        claimant("delta"),
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

    let error = certify(
        &CertificationContext {
            compiled_rule: &compiled,
            rule: &rule,
            claims: &claims,
            estate: &estate,
        },
        "Promote bravo to unrestricted execution",
        "bravo",
        0.0,
        BTreeMap::new(),
    )
    .expect_err("rejected rule should not certify");

    assert!(error.to_string().contains("not admissible"));
}

#[test]
fn certificate_certify_rejects_claimed_outcome_that_does_not_match_rule_output() {
    let (rule, claims, claimants, estate, family) = permissions_runtime();
    let compiled = compile(&rule, &claims, &estate, &claimants, &family).unwrap();

    let error = certify(
        &CertificationContext {
            compiled_rule: &compiled,
            rule: &rule,
            claims: &claims,
            estate: &estate,
        },
        "Escalate Bash to autonomous execution",
        "Bash",
        1.0,
        BTreeMap::new(),
    )
    .expect_err("claimed outcomes must match the rule output");

    assert!(error.to_string().contains("outcome mismatch"));
}

#[test]
fn certificate_certify_rejects_wrong_claude_permissions_outcome() {
    let (rule, claims, claimants, estate, family) = permissions_runtime();
    let compiled = compile(&rule, &claims, &estate, &claimants, &family).unwrap();

    let error = certify(
        &CertificationContext {
            compiled_rule: &compiled,
            rule: &rule,
            claims: &claims,
            estate: &estate,
        },
        "Escalate Bash to autonomous execution",
        "Bash",
        1.0,
        BTreeMap::new(),
    )
    .expect_err("wrong claude-agent-sdk-permissions outcome must not certify");

    assert!(error.to_string().contains("outcome mismatch"));
}
