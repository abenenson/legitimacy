use std::path::PathBuf;

use legitimacy::{
    Verdict,
    axioms::monotonicity::check_monotonicity,
    paradox::{ParadoxType, run_paradox_suite},
    policy::{compile_policy, load_policy_file},
};

fn example_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join(name)
}

#[test]
fn claude_agent_sdk_permissions_policy_is_admissible() {
    let compiled = compile_policy(example_path("claude-agent-sdk-permissions.rule.toml"))
        .expect("permissions example should compile");

    assert!(
        compiled.is_admissible(),
        "expected admissible: {compiled:#?}"
    );
    assert!(
        compiled
            .axiom_verdicts
            .iter()
            .all(|verdict| matches!(verdict, Verdict::Admissible { .. }))
    );
}

#[test]
fn claude_agent_sdk_permissions_policy_has_no_paradox_violations() {
    let parsed = load_policy_file(example_path("claude-agent-sdk-permissions.rule.toml"))
        .expect("permissions example should parse");

    let violations = run_paradox_suite(
        &parsed.rule,
        &parsed.claims,
        &parsed.estate,
        &parsed.claimants,
    )
    .unwrap();

    assert!(
        violations.is_empty(),
        "unexpected paradoxes: {violations:#?}"
    );
}

#[test]
fn claude_agent_sdk_hooks_policy_exposes_monotonicity_failure() {
    let compiled = compile_policy(example_path("claude-agent-sdk-hooks.rule.toml"))
        .expect("hooks example should compile");

    let monotonicity = compiled
        .axiom_verdicts
        .iter()
        .find(
            |verdict| matches!(verdict, Verdict::Rejected { axiom, .. } if axiom == "monotonicity"),
        )
        .expect("hooks policy should fail monotonicity");

    match monotonicity {
        Verdict::Rejected { counterexample, .. } => {
            assert!(counterexample.description.contains("Bash:cat_/etc/passwd"));
            assert!(counterexample.violation.contains("punishes"));
        }
        _ => unreachable!(),
    }
}

/// With monotonicity_inversion = true, the hooks rule is admissible:
/// higher context strength (danger signal) can reduce access without violating the axiom.
#[test]
fn claude_agent_sdk_hooks_inverted_policy_is_admissible() {
    let compiled = compile_policy(example_path("claude-agent-sdk-hooks-inverted.rule.toml"))
        .expect("inverted hooks example should compile");

    assert!(
        compiled.is_admissible(),
        "expected admissible with inversion: {compiled:#?}"
    );

    // Inverted monotonicity check is the one that passes now.
    let mono = compiled
        .axiom_verdicts
        .iter()
        .find(|v| matches!(v, Verdict::Admissible { axiom, .. } if axiom.contains("monotonicity")))
        .expect("should have an admissible monotonicity verdict");

    match mono {
        Verdict::Admissible {
            axiom,
            perturbations_tested,
        } => {
            assert!(
                axiom.contains("inverted"),
                "axiom label should note inversion; got: {axiom}"
            );
            assert!(*perturbations_tested > 0);
        }
        _ => unreachable!(),
    }
}

/// Direct API: inverted check_monotonicity admits the hooks rule.
#[test]
fn hooks_rule_passes_inverted_monotonicity_directly() {
    use legitimacy::rules::claude_agent_sdk_hooks_rule;

    let claims = vec![
        legitimacy::Claim::new("safe", 0.3)
            .unwrap()
            .with_metric("baseline_allow", 1.0)
            .with_metric("dangerous_pattern", 0.0)
            .with_metric("sensitive_path", 0.0)
            .with_metric("block_threshold", 0.8),
        legitimacy::Claim::new("risky", 0.7)
            .unwrap()
            .with_metric("baseline_allow", 1.0)
            .with_metric("dangerous_pattern", 0.0)
            .with_metric("sensitive_path", 1.0)
            .with_metric("block_threshold", 0.8),
    ];
    let estate = legitimacy::Estate {
        total: 1.0.try_into().unwrap(),
        unit: "pass_block".to_string(),
    };

    // Standard direction: fails (risky claim crosses threshold after strengthening).
    let deltas = [legitimacy::PositiveStrength::new(0.15).unwrap()];
    let standard = check_monotonicity(
        &claude_agent_sdk_hooks_rule(),
        &claims,
        &estate,
        &deltas,
        false,
    );
    assert!(
        matches!(standard, Ok(Verdict::Rejected { .. })),
        "standard monotonicity should reject hooks; got: {standard:?}"
    );

    // Inverted direction: passes (higher risk → less access is the expected contract).
    let inverted = check_monotonicity(
        &claude_agent_sdk_hooks_rule(),
        &claims,
        &estate,
        &deltas,
        true,
    );
    assert!(
        matches!(inverted, Ok(Verdict::Admissible { .. })),
        "inverted monotonicity should admit hooks; got: {inverted:?}"
    );
}

#[test]
fn claude_agent_sdk_hooks_policy_trips_population_paradox() {
    let parsed = load_policy_file(example_path("claude-agent-sdk-hooks.rule.toml"))
        .expect("hooks example should parse");

    let violations = run_paradox_suite(
        &parsed.rule,
        &parsed.claims,
        &parsed.estate,
        &parsed.claimants,
    )
    .unwrap();

    assert!(
        violations
            .iter()
            .any(|violation| violation.paradox_type == ParadoxType::Population),
        "expected population paradox, got: {violations:#?}"
    );
}
