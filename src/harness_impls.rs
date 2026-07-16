//! Concrete `HarnessPolicy` implementations for known agent harnesses.
//!
//! Each struct holds the instances (tool invocations / agent actions) that
//! define the concrete problem.  The `HarnessPolicy` trait is implemented to
//! provide a uniform compile/paradox interface.
//!
//! These implementations mirror the canonical policy example files in `examples/`
//! and can be used programmatically without parsing TOML.

use std::collections::BTreeMap;

use crate::{
    Claim, Claimant, Estate, LegitimacyError, PositiveStrength, Rule,
    compiler::Family,
    harness::HarnessPolicy,
    rules::{claude_agent_sdk_hooks_rule, claude_agent_sdk_permissions_rule},
};

/// Claude Agent SDK permission modes as a `HarnessPolicy`.
///
/// Models the three permission tiers (always_allow, ask_user, always_deny)
/// and the tool invocations that fall into each tier.
///
/// The permissions rule is axiomatically admissible: adding or removing one
/// tool does not affect any other tool's authorization.
pub struct ClaudeAgentSDKPermissionsHarness {
    /// Tool invocations declared in this harness.
    pub instances: Vec<PermissionInstance>,
}

/// A single tool-invocation instance for the permissions harness.
pub struct PermissionInstance {
    pub id: String,
    pub priority_class: String,
    /// 1.0 = auto-approve, 0.5 = ask-user, 0.0 = always-deny
    pub base_authorization: f64,
}

impl ClaudeAgentSDKPermissionsHarness {
    /// Standard Claude Agent SDK permission model (mirrors `claude-agent-sdk-permissions`).
    #[tracing::instrument]
    pub fn standard() -> Self {
        Self {
            instances: vec![
                PermissionInstance {
                    id: "Read:file".to_string(),
                    priority_class: "always_allow".to_string(),
                    base_authorization: 1.0,
                },
                PermissionInstance {
                    id: "Write:file".to_string(),
                    priority_class: "ask_user".to_string(),
                    base_authorization: 0.5,
                },
                PermissionInstance {
                    id: "Bash:exec".to_string(),
                    priority_class: "ask_user".to_string(),
                    base_authorization: 0.5,
                },
                PermissionInstance {
                    id: "Bash:network".to_string(),
                    priority_class: "always_deny".to_string(),
                    base_authorization: 0.0,
                },
            ],
        }
    }
}

impl HarnessPolicy for ClaudeAgentSDKPermissionsHarness {
    fn name(&self) -> &str {
        "claude-agent-sdk-permissions"
    }

    fn estate(&self) -> Result<Estate, LegitimacyError> {
        Estate::new(1.0, "authorization_budget")
    }

    fn claimants(&self) -> Vec<Claimant> {
        self.instances
            .iter()
            .map(|inst| Claimant {
                id: inst.id.clone(),
                priority_class: inst.priority_class.clone(),
                attributes: BTreeMap::new(),
            })
            .collect()
    }

    fn claims(&self) -> Result<Vec<Claim>, LegitimacyError> {
        self.instances
            .iter()
            .map(|inst| {
                let claim_strength = if inst.base_authorization > 0.0 {
                    inst.base_authorization
                } else {
                    0.1
                };

                Ok(Claim::new(inst.id.clone(), claim_strength)?
                    .with_metric("available", 1.0)
                    .with_metric("listed", 1.0)
                    .with_metric(
                        "denied",
                        if inst.base_authorization == 0.0 {
                            1.0
                        } else {
                            0.0
                        },
                    )
                    .with_metric("base_authorization", inst.base_authorization))
            })
            .collect()
    }

    fn rule(&self) -> Rule {
        claude_agent_sdk_permissions_rule()
    }

    fn family(&self) -> Result<Family, LegitimacyError> {
        Ok(Family {
            reductions: true,
            shocks: vec![0.5, 0.75, 1.25, 1.5],
            strengthening_deltas: vec![
                PositiveStrength::new(0.1)?,
                PositiveStrength::new(0.25)?,
                PositiveStrength::new(0.5)?,
            ],
            monotonicity_inversion: false,
        })
    }
}

/// Claude Agent SDK pre-tool-use hooks as a `HarnessPolicy`.
///
/// Models content-sensitive pass/block gates.  This harness intentionally
/// violates standard monotonicity (higher context strength can trigger a
/// safety block), so it should be checked with `monotonicity_inversion = true`.
pub struct ClaudeAgentSDKHooksHarness {
    /// Tool invocations declared in this harness.
    pub instances: Vec<HookInstance>,
    /// Whether to use inverted monotonicity checking.
    ///
    /// When `true`, the checker enforces that higher context strength never
    /// *increases* access (the correct contract for safety-clearance gates).
    pub inversion: bool,
}

/// A single tool-invocation instance for the hooks harness.
pub struct HookInstance {
    pub id: String,
    pub strength: f64,
    pub baseline_allow: f64,
    pub dangerous_pattern: f64,
    pub sensitive_path: f64,
    pub block_threshold: f64,
}

impl ClaudeAgentSDKHooksHarness {
    /// Standard hooks model from `claude-agent-sdk-hooks`.
    ///
    /// Note: this harness fails standard monotonicity.  Use `inverted()` for
    /// a version that is admissible under inverted-monotonicity semantics.
    #[tracing::instrument]
    pub fn standard() -> Self {
        Self {
            instances: Self::default_instances(),
            inversion: false,
        }
    }

    /// Safety-clearance variant from `claude-agent-sdk-hooks-inverted`.
    ///
    /// Admissible under inverted monotonicity: higher danger context → less access.
    #[tracing::instrument]
    pub fn inverted() -> Self {
        Self {
            instances: Self::default_instances(),
            inversion: true,
        }
    }

    fn default_instances() -> Vec<HookInstance> {
        vec![
            HookInstance {
                id: "Read:README.md".to_string(),
                strength: 0.3,
                baseline_allow: 1.0,
                dangerous_pattern: 0.0,
                sensitive_path: 0.0,
                block_threshold: 0.8,
            },
            HookInstance {
                id: "Bash:pwd".to_string(),
                strength: 0.4,
                baseline_allow: 1.0,
                dangerous_pattern: 0.0,
                sensitive_path: 0.0,
                block_threshold: 0.8,
            },
            HookInstance {
                id: "Bash:cat_docs".to_string(),
                strength: 0.5,
                baseline_allow: 1.0,
                dangerous_pattern: 0.0,
                sensitive_path: 0.0,
                block_threshold: 0.8,
            },
            HookInstance {
                id: "Bash:cat_/etc/passwd".to_string(),
                strength: 0.7,
                baseline_allow: 1.0,
                dangerous_pattern: 0.0,
                sensitive_path: 1.0,
                block_threshold: 0.8,
            },
            HookInstance {
                id: "Bash:rm_-rf".to_string(),
                strength: 1.0,
                baseline_allow: 1.0,
                dangerous_pattern: 1.0,
                sensitive_path: 1.0,
                block_threshold: 0.8,
            },
        ]
    }
}

impl HarnessPolicy for ClaudeAgentSDKHooksHarness {
    fn name(&self) -> &str {
        if self.inversion {
            "claude-agent-sdk-hooks-inverted"
        } else {
            "claude-agent-sdk-hooks"
        }
    }

    fn estate(&self) -> Result<Estate, LegitimacyError> {
        Estate::new(1.0, "pass_block")
    }

    fn claimants(&self) -> Vec<Claimant> {
        self.instances
            .iter()
            .map(|inst| Claimant {
                id: inst.id.clone(),
                priority_class: "tool_invocation".to_string(),
                attributes: BTreeMap::new(),
            })
            .collect()
    }

    fn claims(&self) -> Result<Vec<Claim>, LegitimacyError> {
        self.instances
            .iter()
            .map(|inst| {
                Ok(Claim::new(inst.id.clone(), inst.strength)?
                    .with_metric("baseline_allow", inst.baseline_allow)
                    .with_metric("dangerous_pattern", inst.dangerous_pattern)
                    .with_metric("sensitive_path", inst.sensitive_path)
                    .with_metric("block_threshold", inst.block_threshold))
            })
            .collect()
    }

    fn rule(&self) -> Rule {
        claude_agent_sdk_hooks_rule()
    }

    fn family(&self) -> Result<Family, LegitimacyError> {
        Ok(Family {
            reductions: true,
            shocks: vec![0.5, 0.75, 1.25, 1.5],
            strengthening_deltas: vec![
                PositiveStrength::new(0.1)?,
                PositiveStrength::new(0.2)?,
                PositiveStrength::new(0.5)?,
            ],
            monotonicity_inversion: self.inversion,
        })
    }
}
