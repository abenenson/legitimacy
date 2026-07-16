//! Built-in allocation rules for testing and bootstrapping.
//!
//! `proportional_rule` is the canonical positive control: it satisfies
//! all three graph-diagnostic axioms (consistency, solidarity, monotonicity) by
//! construction. Use it to verify that the axiom checkers accept a
//! well-behaved rule before testing anything adversarial.

pub mod divisor;

use crate::{
    Allocation, Claim, DeclarativeRuleKind, EPSILON, Estate, LegitimacyError, Rule, RuleSpec,
    validate_claims,
};

pub use divisor::{jefferson_allocate, jefferson_rule, webster_allocate, webster_rule};

const DEFAULT_APPROVAL_THRESHOLD: f64 = 0.8;

/// Allocate the estate proportionally to claim strength.
///
/// Each claimant receives `(strength / total_strength) * estate.total`.
/// Claims must have strictly positive strength; with an empty claimant set, the
/// allocation is empty.
///
/// Graph-diagnostic axioms:
/// - Consistency: proportional is path-independent; removing a claimant
///   and adjusting the estate leaves everyone else's share unchanged.
/// - Solidarity: a uniform estate shock moves all shares in the same
///   direction (all scale with the estate).
/// - Monotonicity: increasing one claimant's strength increases their share.
#[tracing::instrument]
pub fn proportional_rule() -> Rule {
    Rule {
        name: "proportional".to_string(),
        version: "1.0.0".to_string(),
        rule_spec: RuleSpec::Declarative(DeclarativeRuleKind::Proportional),
        priority_classes: vec!["standard".to_string()],
    }
}

pub(crate) fn proportional_allocate(
    claims: &[Claim],
    estate: &Estate,
) -> Result<Allocation, LegitimacyError> {
    validate_claims(claims, "proportional rule")?;
    let total_strength: f64 = claims.iter().map(|c| c.strength.value()).sum();
    let mut allocation = Allocation::default();

    if claims.is_empty() {
        return Ok(allocation);
    }

    for claim in claims {
        let share = (claim.strength.value() / total_strength) * estate.total.value();
        allocation.insert(claim.claimant_id.clone(), share);
    }

    Ok(allocation)
}

/// Dispatch allocator for [`crate::DeclarativeRuleKind::Custom`].
///
/// Matches known built-in rule names and delegates to their concrete
/// allocators.  Unknown names return an `InvalidInput` error at allocation
/// time rather than at parse time, keeping the enum open.
///
/// New application-specific allocators should be registered here rather than
/// added as enum variants on `DeclarativeRuleKind`, preserving the core
/// library's independence from any particular application domain.
pub(crate) fn custom_allocate(
    name: &str,
    claims: &[Claim],
    estate: &Estate,
) -> Result<Allocation, LegitimacyError> {
    match name {
        "claude_agent_sdk_permissions" => claude_agent_sdk_permissions_allocate(claims, estate),
        "claude_agent_sdk_hooks" => claude_agent_sdk_hooks_allocate(claims, estate),
        _ => Err(LegitimacyError::invalid_input(format!(
            "unknown custom declarative rule kind '{name}'"
        ))),
    }
}

/// The composite-score promotion rule from the essay.
///
/// Score = `0.4 * reliability + 0.3 * diversity + 0.3 * peer_relative`.
/// Claimants strictly above the cohort median are "promoted" and split the
/// estate proportionally to their composite scores. Everyone else gets zero.
///
/// The rule is intentionally plausible and intentionally bad:
/// - consistency fails because the median depends on who else is present
/// - solidarity fails because peer-relative scores can move with budget pressure
/// - monotonicity fails because the diversity term can penalize overspecialization
#[tracing::instrument]
pub fn essay_composite_rule() -> Rule {
    Rule {
        name: "essay-composite-median".to_string(),
        version: "0.1.0".to_string(),
        rule_spec: RuleSpec::programmatic(essay_composite_allocate),
        priority_classes: vec!["standard".to_string()],
    }
}

/// Claude Agent SDK permission modes modeled as independent per-tool authorizations.
///
/// Expected metrics on each claim:
/// - `available`: 1.0 when the tool exists in the current mode, else 0.0
/// - `listed`: 1.0 when the tool is explicitly classified by policy, else 0.0
/// - `base_authorization`: 1.0 for auto-approve, 0.5 for ask-user, 0.0 for deny
///
/// The rule is intentionally independent across tools: adding or removing one
/// tool should not affect another tool's authorization requirement.
#[tracing::instrument]
pub fn claude_agent_sdk_permissions_rule() -> Rule {
    Rule {
        name: "claude-agent-sdk-permissions".to_string(),
        version: "1.0.0".to_string(),
        rule_spec: RuleSpec::Declarative(DeclarativeRuleKind::Custom(
            "claude_agent_sdk_permissions".to_string(),
        )),
        priority_classes: vec![
            "always_allow".to_string(),
            "ask_user".to_string(),
            "always_deny".to_string(),
        ],
    }
}

pub(crate) fn claude_agent_sdk_permissions_allocate(
    claims: &[Claim],
    estate: &Estate,
) -> Result<Allocation, LegitimacyError> {
    let _ = estate;
    validate_claims(claims, "claude-agent-sdk permissions rule")?;
    Ok(claims
        .iter()
        .map(|claim| {
            let listed = claim.metric("listed") >= 0.5;
            let available = claim.metric("available") >= 0.5;
            let denied = claim.metric("denied") >= 0.5;
            let base_authorization = claim.metric("base_authorization").clamp(0.0, 1.0);

            let share = if available && listed && !denied {
                base_authorization
            } else {
                0.0
            };

            (claim.claimant_id.clone(), share)
        })
        .collect())
}

/// Claude Agent SDK pre-tool-use hooks modeled as content-sensitive pass/block gates.
///
/// Expected metrics on each claim:
/// - `baseline_allow`: 1.0 when the invocation is otherwise permitted
/// - `sensitive_path`: 1.0 when extra context names a guarded path
/// - `dangerous_pattern`: 1.0 for unconditional block patterns
/// - `block_threshold`: context/specificity score above which the hook blocks
///
/// This rule is designed to expose a monotonicity edge case: more context can
/// decrease approval once the invocation crosses a sensitive-pattern threshold.
#[tracing::instrument]
pub fn claude_agent_sdk_hooks_rule() -> Rule {
    Rule {
        name: "claude-agent-sdk-hooks".to_string(),
        version: "1.0.0".to_string(),
        rule_spec: RuleSpec::Declarative(DeclarativeRuleKind::Custom(
            "claude_agent_sdk_hooks".to_string(),
        )),
        priority_classes: vec!["tool_invocation".to_string()],
    }
}

pub(crate) fn claude_agent_sdk_hooks_allocate(
    claims: &[Claim],
    estate: &Estate,
) -> Result<Allocation, LegitimacyError> {
    let _ = estate;
    validate_claims(claims, "claude-agent-sdk hooks rule")?;
    Ok(claims
        .iter()
        .map(|claim| {
            let baseline_allow = claim.metric("baseline_allow").clamp(0.0, 1.0);
            let dangerous_pattern = claim.metric("dangerous_pattern") >= 0.5;
            let sensitive_path = claim.metric("sensitive_path") >= 0.5;
            let block_threshold = if claim.metric("block_threshold") > 0.0 {
                claim.metric("block_threshold")
            } else {
                DEFAULT_APPROVAL_THRESHOLD
            };

            let blocked =
                dangerous_pattern || (sensitive_path && claim.strength.value() >= block_threshold);
            let share = if blocked { 0.0 } else { baseline_allow };

            (claim.claimant_id.clone(), share)
        })
        .collect())
}

fn essay_composite_allocate(
    claims: &[Claim],
    estate: &Estate,
) -> Result<Allocation, LegitimacyError> {
    validate_claims(claims, "essay composite rule")?;
    let scored: Vec<(String, f64)> = claims
        .iter()
        .map(|claim| {
            (
                claim.claimant_id.clone(),
                essay_composite_score(claim, estate),
            )
        })
        .collect();

    let median = median_score(scored.iter().map(|(_, score)| *score).collect());
    let promoted: Vec<(String, f64)> = scored
        .iter()
        .filter(|(_, score)| *score > median + EPSILON)
        .map(|(id, score)| (id.clone(), *score))
        .collect();

    let promoted_total: f64 = promoted.iter().map(|(_, score)| *score).sum();
    let mut allocation = zero_allocation(claims);

    if promoted_total <= EPSILON {
        return Ok(allocation);
    }

    for (claimant_id, score) in promoted {
        allocation.insert(claimant_id, estate.total.value() * score / promoted_total);
    }

    Ok(allocation)
}

fn essay_composite_score(claim: &Claim, estate: &Estate) -> f64 {
    let reliability = clamp01(claim.strength.value());
    let diversity = diversity_score(claim);
    let peer_relative = peer_relative_score(claim, estate);

    0.4 * reliability + 0.3 * diversity + 0.3 * peer_relative
}

fn diversity_score(claim: &Claim) -> f64 {
    let base_diversity = claim.metric("diversity");
    let specialization_floor = claim.metric("specialization_floor");
    let specialization_penalty = claim.metric("specialization_penalty");
    let overspecialization = (claim.strength.value() - specialization_floor).max(0.0);

    clamp01(base_diversity - specialization_penalty * overspecialization)
}

fn peer_relative_score(claim: &Claim, estate: &Estate) -> f64 {
    let base_peer_relative = claim.metric("peer_relative");
    let scarcity_bonus = claim.metric("scarcity_bonus");
    let scarcity = (100.0 - estate.total.value()).max(0.0) / 100.0;

    clamp01(base_peer_relative + scarcity_bonus * scarcity)
}

fn median_score(mut scores: Vec<f64>) -> f64 {
    if scores.is_empty() {
        return 0.0;
    }

    scores.sort_by(|left, right| left.total_cmp(right));
    let middle = scores.len() / 2;

    if scores.len() % 2 == 1 {
        scores[middle]
    } else {
        (scores[middle - 1] + scores[middle]) / 2.0
    }
}

fn zero_allocation(claims: &[Claim]) -> Allocation {
    let mut allocation = Allocation::default();
    for claim in claims {
        allocation.insert(claim.claimant_id.clone(), 0.0);
    }
    allocation
}

fn clamp01(value: f64) -> f64 {
    value.clamp(0.0, 1.0)
}
