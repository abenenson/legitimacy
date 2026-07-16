//! Integration tests for the `HarnessPolicy` trait and its SDK implementations.

use legitimacy::{
    Verdict,
    harness::HarnessPolicy,
    harness_impls::{ClaudeAgentSDKHooksHarness, ClaudeAgentSDKPermissionsHarness},
};

#[test]
fn agent_sdk_permissions_harness_is_admissible() {
    let harness = ClaudeAgentSDKPermissionsHarness::standard();
    let compiled = harness.compile().unwrap();

    assert!(
        compiled.is_admissible(),
        "SDK permissions harness should be axiomatically admissible; got: {compiled:#?}"
    );
    assert_eq!(compiled.name, "claude-agent-sdk-permissions");
}

#[test]
fn agent_sdk_permissions_harness_has_no_paradoxes() {
    let harness = ClaudeAgentSDKPermissionsHarness::standard();
    let paradoxes = harness.paradoxes().unwrap();
    assert!(
        paradoxes.is_empty(),
        "SDK permissions harness should have no paradoxes; got: {paradoxes:#?}"
    );
}

#[test]
fn agent_sdk_hooks_standard_fails_monotonicity() {
    let harness = ClaudeAgentSDKHooksHarness::standard();
    let compiled = harness.compile().unwrap();

    assert!(
        !compiled.is_admissible(),
        "SDK hooks harness should fail standard monotonicity"
    );

    let monotonicity_rejected = compiled
        .axiom_verdicts
        .iter()
        .any(|v| matches!(v, Verdict::Rejected { axiom, .. } if axiom.contains("monotonicity")));

    assert!(
        monotonicity_rejected,
        "should have a monotonicity rejection"
    );
}

#[test]
fn agent_sdk_hooks_inverted_is_admissible() {
    let harness = ClaudeAgentSDKHooksHarness::inverted();
    let compiled = harness.compile().unwrap();

    assert!(
        compiled.is_admissible(),
        "SDK hooks harness with inversion should be admissible; got: {compiled:#?}"
    );
    assert_eq!(compiled.name, "claude-agent-sdk-hooks");
}

#[test]
fn harness_policy_name_is_accessible() {
    let perm = ClaudeAgentSDKPermissionsHarness::standard();
    let hooks = ClaudeAgentSDKHooksHarness::standard();
    let hooks_inv = ClaudeAgentSDKHooksHarness::inverted();

    assert_eq!(perm.name(), "claude-agent-sdk-permissions");
    assert_eq!(hooks.name(), "claude-agent-sdk-hooks");
    assert_eq!(hooks_inv.name(), "claude-agent-sdk-hooks-inverted");
}
