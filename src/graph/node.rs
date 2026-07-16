use crate::{ClaimantId, DeclarativeRuleKind, EdgeTransform, LegitimacyError};
use regex::Regex;
use serde::{Deserialize, Deserializer, Serialize};
use std::{
    borrow::Borrow,
    collections::{BTreeMap, HashMap},
    sync::{Arc, OnceLock, RwLock},
};

static CONTENT_REGEX_CACHE: OnceLock<RwLock<HashMap<String, Arc<Regex>>>> = OnceLock::new();

#[derive(Clone, Debug, Serialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[serde(transparent)]
pub struct NodeId(String);

impl NodeId {
    pub fn new(value: impl Into<String>) -> Result<Self, LegitimacyError> {
        let value = value.into();
        if value.trim().is_empty() {
            return Err(LegitimacyError::InvalidNodeId { value });
        }

        Ok(Self(value))
    }

    pub(crate) fn as_str(&self) -> &str {
        &self.0
    }
}

impl<'de> Deserialize<'de> for NodeId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = String::deserialize(deserializer)?;
        Self::new(value).map_err(serde::de::Error::custom)
    }
}

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum Decision {
    Permit,
    Deny,
    Escalate,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum Gate {
    PrefixMatch {
        pattern: String,
        decision: Decision,
    },
    ExactMatch {
        value: String,
        decision: Decision,
    },
    ContentMatch {
        regex: String,
        decision: Decision,
    },
    ThresholdGate {
        field: String,
        min: f64,
        decision: Decision,
    },
    PeerRelative {
        field: String,
        percentile: f64,
        decision: Decision,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum GateLogic {
    AllMustPass,
    AnyMustPass,
    FirstMatch,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct GovernanceClaim {
    pub claimant_id: ClaimantId,
    #[serde(default = "default_governance_strength")]
    pub strength: f64,
    #[serde(default)]
    pub priority_class: Option<String>,
    #[serde(default)]
    pub path: Option<String>,
    #[serde(default)]
    pub action: Option<String>,
    #[serde(default)]
    pub content: Option<String>,
    #[serde(default)]
    pub metrics: BTreeMap<String, f64>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ClaimDecision {
    pub claimant_id: ClaimantId,
    pub decision: Decision,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum GovernanceNode {
    Binary {
        id: NodeId,
        name: String,
        gates: Vec<Gate>,
        default: Decision,
        combination: GateLogic,
    },
    Proportional {
        id: NodeId,
        name: String,
        rule: DeclarativeRuleKind,
        priority_classes: Vec<String>,
    },
    Threshold {
        id: NodeId,
        name: String,
        threshold: f64,
        field: String,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct GovernanceGraph {
    pub nodes: BTreeMap<NodeId, GovernanceNode>,
    pub edges: Vec<crate::graph::edge::GovernanceEdge>,
}

fn default_governance_strength() -> f64 {
    1.0
}

pub(crate) fn validate_governance_claim(claim: &GovernanceClaim) -> Result<(), LegitimacyError> {
    if claim.claimant_id.trim().is_empty() {
        return Err(LegitimacyError::InvalidClaimantId {
            claimant_id: claim.claimant_id.clone(),
        });
    }

    if !claim.strength.is_finite() || claim.strength <= 0.0 {
        return Err(LegitimacyError::InvalidGovernanceStrength {
            claimant_id: claim.claimant_id.clone(),
            strength: claim.strength,
        });
    }

    if claim
        .priority_class
        .as_deref()
        .is_some_and(|class| class.trim().is_empty())
    {
        return Err(LegitimacyError::InvalidInput {
            message: format!(
                "claim '{}' priority_class must be non-empty when provided",
                claim.claimant_id
            ),
        });
    }

    for (field, value) in &claim.metrics {
        if !value.is_finite() {
            return Err(LegitimacyError::InvalidGate {
                gate: field.clone(),
                message: format!(
                    "claim '{}' has non-finite metric value {}",
                    claim.claimant_id, value
                ),
            });
        }
    }

    Ok(())
}

pub(crate) fn validate_governance_claims<T>(claims: &[T]) -> Result<(), LegitimacyError>
where
    T: Borrow<GovernanceClaim>,
{
    let mut seen = std::collections::BTreeSet::new();
    for claim in claims {
        let claim = claim.borrow();
        validate_governance_claim(claim)?;
        if !seen.insert(claim.claimant_id.as_str()) {
            return Err(LegitimacyError::DuplicateClaimantId {
                claimant_id: claim.claimant_id.clone(),
            });
        }
    }
    Ok(())
}

pub fn validate_governance_graph(graph: &GovernanceGraph) -> Result<(), LegitimacyError> {
    for (node_id, node) in &graph.nodes {
        if node_id != node_id_for_node(node) {
            return Err(LegitimacyError::invalid_input(format!(
                "graph node map key '{}' does not match embedded node id '{}'",
                node_id,
                node_id_for_node(node)
            )));
        }
        validate_governance_node(node)?;
    }

    for edge in &graph.edges {
        if !graph.nodes.contains_key(&edge.from) {
            return Err(LegitimacyError::InvalidEdgeReference {
                node_id: edge.from.to_string(),
            });
        }
        if !graph.nodes.contains_key(&edge.to) {
            return Err(LegitimacyError::InvalidEdgeReference {
                node_id: edge.to.to_string(),
            });
        }
        if let EdgeTransform::ClaimModification { delta } = &edge.transform
            && !delta.is_finite()
        {
            return Err(LegitimacyError::invalid_input(format!(
                "claim-modification delta must be finite, got {delta}"
            )));
        }
    }

    Ok(())
}

pub(crate) fn validate_governance_node(node: &GovernanceNode) -> Result<(), LegitimacyError> {
    match node {
        GovernanceNode::Binary { gates, .. } => {
            for gate in gates {
                validate_gate(gate)?;
            }
            Ok(())
        }
        GovernanceNode::Proportional {
            priority_classes, ..
        } => {
            if priority_classes.iter().any(|class| class.trim().is_empty()) {
                return Err(LegitimacyError::InvalidInput {
                    message: "priority classes must be non-empty".to_string(),
                });
            }
            Ok(())
        }
        GovernanceNode::Threshold {
            threshold, field, ..
        } => {
            if !threshold.is_finite() {
                return Err(LegitimacyError::InvalidInput {
                    message: "threshold values must be finite".to_string(),
                });
            }
            if field.trim().is_empty() {
                return Err(LegitimacyError::InvalidInput {
                    message: "threshold field must be non-empty".to_string(),
                });
            }
            Ok(())
        }
    }
}

pub(crate) fn evaluate_node<T>(
    node: &GovernanceNode,
    claims: &[T],
) -> Result<Vec<ClaimDecision>, LegitimacyError>
where
    T: Borrow<GovernanceClaim>,
{
    validate_governance_claims(claims)?;
    evaluate_node_validated(node, claims)
}

pub(crate) fn evaluate_node_validated<T>(
    node: &GovernanceNode,
    claims: &[T],
) -> Result<Vec<ClaimDecision>, LegitimacyError>
where
    T: Borrow<GovernanceClaim>,
{
    if matches!(node, GovernanceNode::Proportional { .. }) {
        return Err(LegitimacyError::UnsupportedNodeType {
            node_id: node_id(node).as_str().to_string(),
            node_type: node_kind(node).to_string(),
        });
    }

    match node {
        GovernanceNode::Binary {
            gates,
            default,
            combination,
            ..
        } => evaluate_binary_node(gates, default, combination, claims),
        GovernanceNode::Threshold {
            threshold, field, ..
        } => evaluate_threshold_node(*threshold, field, claims),
        GovernanceNode::Proportional { .. } => Err(LegitimacyError::InvalidInput {
            message: "proportional nodes should have been rejected before evaluation".to_string(),
        }),
    }
}

pub(crate) fn merge_claim_batches(
    node_id: &NodeId,
    incoming: &[GovernanceClaim],
    additional: &[GovernanceClaim],
) -> Result<Vec<GovernanceClaim>, LegitimacyError> {
    let mut merged = BTreeMap::<String, GovernanceClaim>::new();

    for claim in incoming.iter().chain(additional.iter()) {
        match merged.get(&claim.claimant_id) {
            Some(existing) if existing != claim => {
                return Err(LegitimacyError::ConflictingClaimFeed {
                    node_id: node_id.to_string(),
                    claimant_id: claim.claimant_id.clone(),
                });
            }
            Some(_) => {}
            None => {
                merged.insert(claim.claimant_id.clone(), claim.clone());
            }
        }
    }

    Ok(merged.into_values().collect())
}

pub(crate) fn decision_rank(decision: &Decision) -> u8 {
    match decision {
        Decision::Deny => 0,
        Decision::Escalate => 1,
        Decision::Permit => 2,
    }
}

pub(crate) fn node_id(node: &GovernanceNode) -> &NodeId {
    node_id_for_node(node)
}

fn node_id_for_node(node: &GovernanceNode) -> &NodeId {
    match node {
        GovernanceNode::Binary { id, .. }
        | GovernanceNode::Proportional { id, .. }
        | GovernanceNode::Threshold { id, .. } => id,
    }
}

pub(crate) fn node_kind(node: &GovernanceNode) -> &'static str {
    match node {
        GovernanceNode::Binary { .. } => "Binary",
        GovernanceNode::Proportional { .. } => "Proportional",
        GovernanceNode::Threshold { .. } => "Threshold",
    }
}

fn validate_gate(gate: &Gate) -> Result<(), LegitimacyError> {
    match gate {
        Gate::PrefixMatch { pattern, .. } => validate_gate_string("PrefixMatch", pattern),
        Gate::ExactMatch { value, .. } => validate_gate_string("ExactMatch", value),
        Gate::ContentMatch { regex, .. } => {
            validate_gate_string("ContentMatch", regex)?;
            let _ = cached_content_regex(regex)?;
            Ok(())
        }
        Gate::ThresholdGate { field, min, .. } => {
            validate_gate_string("ThresholdGate", field)?;
            if !min.is_finite() {
                return Err(LegitimacyError::InvalidGate {
                    gate: "ThresholdGate".to_string(),
                    message: "min must be finite".to_string(),
                });
            }
            Ok(())
        }
        Gate::PeerRelative {
            field, percentile, ..
        } => {
            validate_gate_string("PeerRelative", field)?;
            if !percentile.is_finite() || !(0.0..=1.0).contains(percentile) {
                return Err(LegitimacyError::InvalidGate {
                    gate: "PeerRelative".to_string(),
                    message: format!("percentile must be within [0, 1], got {percentile}"),
                });
            }
            Ok(())
        }
    }
}

fn validate_gate_string(gate: &str, value: &str) -> Result<(), LegitimacyError> {
    if value.trim().is_empty() {
        return Err(LegitimacyError::InvalidGate {
            gate: gate.to_string(),
            message: "value must be non-empty".to_string(),
        });
    }
    Ok(())
}

fn evaluate_binary_node<T>(
    gates: &[Gate],
    default: &Decision,
    combination: &GateLogic,
    claims: &[T],
) -> Result<Vec<ClaimDecision>, LegitimacyError>
where
    T: Borrow<GovernanceClaim>,
{
    claims
        .iter()
        .map(|claim| {
            let claim = claim.borrow();
            let decision = match combination {
                GateLogic::FirstMatch => evaluate_first_match(gates, claim, claims, default)?,
                GateLogic::AnyMustPass => evaluate_any_must_pass(gates, claim, claims, default)?,
                GateLogic::AllMustPass => evaluate_all_must_pass(gates, claim, claims, default)?,
            };

            Ok(ClaimDecision {
                claimant_id: claim.claimant_id.clone(),
                decision,
            })
        })
        .collect()
}

fn evaluate_threshold_node<T>(
    threshold: f64,
    field: &str,
    claims: &[T],
) -> Result<Vec<ClaimDecision>, LegitimacyError>
where
    T: Borrow<GovernanceClaim>,
{
    claims
        .iter()
        .map(|claim| {
            let claim = claim.borrow();
            let decision = if numeric_field(claim, field)? >= threshold {
                Decision::Permit
            } else {
                Decision::Deny
            };

            Ok(ClaimDecision {
                claimant_id: claim.claimant_id.clone(),
                decision,
            })
        })
        .collect()
}

fn evaluate_first_match(
    gates: &[Gate],
    claim: &GovernanceClaim,
    claims: &[impl Borrow<GovernanceClaim>],
    default: &Decision,
) -> Result<Decision, LegitimacyError> {
    for gate in gates {
        if gate_matches(gate, claim, claims)? {
            return Ok(gate_decision(gate).clone());
        }
    }

    Ok(default.clone())
}

fn evaluate_any_must_pass(
    gates: &[Gate],
    claim: &GovernanceClaim,
    claims: &[impl Borrow<GovernanceClaim>],
    default: &Decision,
) -> Result<Decision, LegitimacyError> {
    let mut matched = Vec::new();

    for gate in gates {
        if gate_matches(gate, claim, claims)? {
            matched.push(gate_decision(gate).clone());
        }
    }

    if matched
        .iter()
        .any(|decision| matches!(decision, Decision::Permit))
    {
        return Ok(Decision::Permit);
    }
    if matched
        .iter()
        .any(|decision| matches!(decision, Decision::Escalate))
    {
        return Ok(Decision::Escalate);
    }
    if matched
        .iter()
        .any(|decision| matches!(decision, Decision::Deny))
    {
        return Ok(Decision::Deny);
    }

    Ok(default.clone())
}

fn evaluate_all_must_pass(
    gates: &[Gate],
    claim: &GovernanceClaim,
    claims: &[impl Borrow<GovernanceClaim>],
    default: &Decision,
) -> Result<Decision, LegitimacyError> {
    let mut matched_count = 0usize;
    let mut saw_escalate = false;

    for gate in gates {
        if gate_matches(gate, claim, claims)? {
            matched_count += 1;
            match gate_decision(gate) {
                Decision::Deny => return Ok(Decision::Deny),
                Decision::Escalate => saw_escalate = true,
                Decision::Permit => {}
            }
        }
    }

    if matched_count == gates.len() && !gates.is_empty() {
        if saw_escalate {
            return Ok(Decision::Escalate);
        }
        return Ok(Decision::Permit);
    }

    if saw_escalate {
        return Ok(Decision::Escalate);
    }

    Ok(default.clone())
}

fn gate_matches(
    gate: &Gate,
    claim: &GovernanceClaim,
    claims: &[impl Borrow<GovernanceClaim>],
) -> Result<bool, LegitimacyError> {
    match gate {
        Gate::PrefixMatch { pattern, .. } => Ok(claim
            .path
            .as_deref()
            .is_some_and(|path| path.starts_with(pattern))),
        Gate::ExactMatch { value, .. } => Ok(claim.action.as_deref() == Some(value.as_str())),
        Gate::ContentMatch { regex, .. } => {
            let compiled = cached_content_regex(regex)?;
            Ok(claim
                .content
                .as_deref()
                .is_some_and(|content| compiled.is_match(content)))
        }
        Gate::ThresholdGate { field, min, .. } => Ok(numeric_field(claim, field)? >= *min),
        Gate::PeerRelative {
            field, percentile, ..
        } => evaluate_peer_relative(claim, claims, field, *percentile),
    }
}

fn gate_decision(gate: &Gate) -> &Decision {
    match gate {
        Gate::PrefixMatch { decision, .. }
        | Gate::ExactMatch { decision, .. }
        | Gate::ContentMatch { decision, .. }
        | Gate::ThresholdGate { decision, .. }
        | Gate::PeerRelative { decision, .. } => decision,
    }
}

fn evaluate_peer_relative(
    current: &GovernanceClaim,
    claims: &[impl Borrow<GovernanceClaim>],
    field: &str,
    percentile: f64,
) -> Result<bool, LegitimacyError> {
    let current_value = numeric_field(current, field)?;
    let mut values = claims
        .iter()
        .map(|claim| numeric_field(claim.borrow(), field))
        .collect::<Result<Vec<_>, _>>()?;

    values.sort_by(|left, right| left.total_cmp(right));
    let less_or_equal = values
        .iter()
        .filter(|value| **value <= current_value)
        .count();
    let rank = less_or_equal as f64 / values.len() as f64;
    Ok(rank >= percentile)
}

fn numeric_field(claim: &GovernanceClaim, field: &str) -> Result<f64, LegitimacyError> {
    if field == "strength" {
        return Ok(claim.strength);
    }

    claim
        .metrics
        .get(field)
        .copied()
        .ok_or_else(|| LegitimacyError::InvalidGate {
            gate: field.to_string(),
            message: format!(
                "claim '{}' does not provide metric '{}'",
                claim.claimant_id, field
            ),
        })
}

fn cached_content_regex(pattern: &str) -> Result<Arc<Regex>, LegitimacyError> {
    let cache = CONTENT_REGEX_CACHE.get_or_init(|| RwLock::new(HashMap::new()));

    if let Some(compiled) = cache
        .read()
        .map_err(regex_cache_lock_error)?
        .get(pattern)
        .cloned()
    {
        return Ok(compiled);
    }

    let compiled =
        Arc::new(
            Regex::new(pattern).map_err(|source| LegitimacyError::InvalidRegex {
                pattern: pattern.to_string(),
                source,
            })?,
        );

    let mut write = cache.write().map_err(regex_cache_lock_error)?;
    Ok(write
        .entry(pattern.to_string())
        .or_insert_with(|| compiled.clone())
        .clone())
}

fn regex_cache_lock_error<T>(_: std::sync::PoisonError<T>) -> LegitimacyError {
    LegitimacyError::InvalidInput {
        message: "content regex cache lock poisoned".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Decision, Gate, GateLogic, GovernanceClaim, GovernanceNode, NodeId, evaluate_node,
    };
    use std::collections::BTreeMap;

    #[test]
    fn binary_first_match_uses_gate_order() {
        let node = GovernanceNode::Binary {
            id: NodeId::new("sandbox").unwrap(),
            name: "sandbox".to_string(),
            gates: vec![
                Gate::ContentMatch {
                    regex: "rm -rf".to_string(),
                    decision: Decision::Deny,
                },
                Gate::PrefixMatch {
                    pattern: "/tmp".to_string(),
                    decision: Decision::Permit,
                },
            ],
            default: Decision::Escalate,
            combination: GateLogic::FirstMatch,
        };
        let claim = GovernanceClaim {
            claimant_id: "alice".to_string(),
            strength: 1.0,
            priority_class: None,
            path: Some("/tmp/file".to_string()),
            action: Some("Write".to_string()),
            content: Some("rm -rf /tmp/file".to_string()),
            metrics: BTreeMap::new(),
        };

        let decisions = evaluate_node(&node, &[claim]).unwrap();

        assert_eq!(decisions[0].decision, Decision::Deny);
    }

    #[test]
    fn all_must_pass_preserves_matching_escalation() {
        let node = GovernanceNode::Binary {
            id: NodeId::new("review").unwrap(),
            name: "review".to_string(),
            gates: vec![
                Gate::ExactMatch {
                    value: "Write".to_string(),
                    decision: Decision::Permit,
                },
                Gate::ThresholdGate {
                    field: "risk".to_string(),
                    min: 1.0,
                    decision: Decision::Escalate,
                },
            ],
            default: Decision::Deny,
            combination: GateLogic::AllMustPass,
        };
        let claim = GovernanceClaim {
            claimant_id: "alice".to_string(),
            strength: 1.0,
            priority_class: None,
            path: None,
            action: Some("Write".to_string()),
            content: None,
            metrics: BTreeMap::from([("risk".to_string(), 1.0)]),
        };

        let decisions = evaluate_node(&node, &[claim]).unwrap();

        assert_eq!(decisions[0].decision, Decision::Escalate);
    }
}
