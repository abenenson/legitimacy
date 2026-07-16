use std::path::PathBuf;

use legitimacy::{
    PositiveStrength,
    policy::{load_policy_file, load_policy_str, parse_policy_file},
};

fn example_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join(name)
}

#[test]
fn parser_loads_promotion_gate_example() {
    let policy = load_policy_file(example_path("promotion-gate.rule.toml"))
        .expect("promotion_gate example should parse");

    assert_eq!(policy.rule.name, "subagent-promotion");
    assert_eq!(policy.rule.version, "1.0");
    assert_eq!(
        policy.rule.priority_classes,
        vec!["safety_critical".to_string(), "standard".to_string()]
    );
    assert_eq!(policy.estate.total.value(), 100.0);
    assert_eq!(policy.estate.unit, "compute");
    assert_eq!(policy.family.shocks, vec![0.5, 0.7, 1.3, 1.5]);
    assert_eq!(
        policy.family.strengthening_deltas,
        vec![
            PositiveStrength::new(0.1).unwrap(),
            PositiveStrength::new(0.5).unwrap(),
            PositiveStrength::new(1.0).unwrap(),
        ]
    );
    assert_eq!(policy.spec.claims.ordering, "reliability_score");
}

#[test]
fn parser_loads_memory_consolidation_example() {
    let policy = load_policy_file(example_path("memory-consolidation.rule.toml"))
        .expect("memory_consolidation example should parse");

    assert_eq!(policy.rule.name, "memory-consolidation");
    assert_eq!(policy.rule.version, "1.0");
    assert_eq!(
        policy.rule.priority_classes,
        vec!["episodic".to_string(), "semantic".to_string()]
    );
    assert_eq!(policy.estate.total.value(), 24.0);
    assert_eq!(policy.estate.unit, "slots");
    assert_eq!(policy.family.shocks, vec![0.5, 0.9, 1.1, 1.5]);
    assert_eq!(
        policy.family.strengthening_deltas,
        vec![
            PositiveStrength::new(0.05).unwrap(),
            PositiveStrength::new(0.2).unwrap(),
            PositiveStrength::new(0.8).unwrap(),
        ]
    );
    assert_eq!(policy.spec.claims.ordering, "retention_score");
}

#[test]
fn parser_reads_examples_as_raw_specs() {
    let spec = parse_policy_file(example_path("promotion-gate.rule.toml"))
        .expect("promotion_gate raw spec should parse");

    assert_eq!(spec.rule.name, "subagent-promotion");
    assert_eq!(spec.claimants.r#type, "SubAgent");
    assert_eq!(spec.claimants.id_field, "agent_id");
}

#[test]
fn parser_reports_clear_validation_errors() {
    let invalid = r#"
[rule]
name = "broken"
version = "1.0"

[claimants]
type = "SubAgent"
id_field = "agent_id"

[estate]
type = "AutonomyTier"
total = 100.0
unit = "compute"

[claims]
ordering = "reliability_score"

[priority_classes]
standard = { level = 1 }

[family]
reductions = "drop_everyone"
shocks = [0.5]
strengthening = [0.1]
"#;

    let error = match load_policy_str(invalid) {
        Ok(_) => panic!("invalid reductions should fail"),
        Err(error) => error,
    };
    let message = error.to_string();

    assert!(message.contains("family.reductions"));
    assert!(message.contains("remove_any_single_claimant"));
}

#[test]
fn parser_rejects_non_positive_instance_strengths() {
    let invalid = r#"
[rule]
name = "broken"
version = "1.0"

[claimants]
type = "SubAgent"
id_field = "agent_id"

[estate]
type = "AutonomyTier"
total = 100.0
unit = "compute"

[claims]
ordering = "reliability_score"

[priority_classes]
standard = { level = 1 }

[[instances]]
id = "alpha"
priority_class = "standard"
strength = 0.0

[family]
reductions = "remove_any_single_claimant"
shocks = [0.5]
strengthening = [0.1]
"#;

    let error = match load_policy_str(invalid) {
        Ok(_) => panic!("zero-strength instance should fail"),
        Err(error) => error,
    };
    let message = error.to_string();

    assert!(message.contains("strictly positive finite number"));
    assert!(message.contains("alpha"));
}
