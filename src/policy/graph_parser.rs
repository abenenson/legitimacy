//! TOML-based graph policy parser for `*.graph.toml` files.
//!
//! Extends the rule policy format with `[graph]`, `[[nodes]]`, and `[[edges]]`
//! sections. Parses into a `GovernanceGraph` with full validation.

use std::{collections::HashSet, fs, path::Path};

use serde::Deserialize;

use crate::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceGraph, GovernanceNode, GraphBuilder,
    LegitimacyError, NodeId,
};

// ---------------------------------------------------------------------------
// Raw TOML spec types
// ---------------------------------------------------------------------------

/// Top-level `*.graph.toml` policy file.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct GraphPolicySpec {
    pub graph: GraphMetaSpec,
    #[serde(default)]
    pub nodes: Vec<NodeSpec>,
    #[serde(default)]
    pub edges: Vec<EdgeSpec>,
}

/// `[graph]` section: name and version metadata.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct GraphMetaSpec {
    pub name: String,
    pub version: String,
}

/// `[[nodes]]` entry — all fields are present/absent based on `type`.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct NodeSpec {
    pub id: String,
    #[serde(rename = "type")]
    pub node_type: String,
    // Binary fields
    pub default: Option<String>,
    pub combination: Option<String>,
    #[serde(default)]
    pub gates: Vec<GateSpec>,
    // Threshold fields
    pub threshold: Option<f64>,
    pub field: Option<String>,
    // Name is optional (defaults to id)
    pub name: Option<String>,
}

/// `[[nodes.gates]]` entry within a binary node.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct GateSpec {
    #[serde(rename = "type")]
    pub gate_type: String,
    // PrefixMatch
    pub pattern: Option<String>,
    // ExactMatch
    pub value: Option<String>,
    // ContentMatch
    pub regex: Option<String>,
    // ThresholdGate + PeerRelative
    pub field: Option<String>,
    pub min: Option<f64>,
    pub percentile: Option<f64>,
    // All gates
    pub decision: String,
}

/// `[[edges]]` entry.
#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct EdgeSpec {
    pub from: String,
    pub to: String,
    pub transform: String,
    #[serde(default)]
    pub delta: Option<f64>,
}

// ---------------------------------------------------------------------------
// Parse functions
// ---------------------------------------------------------------------------

/// Parse a raw graph policy string into `GraphPolicySpec`.
pub fn parse_graph_str(input: &str) -> Result<GraphPolicySpec, LegitimacyError> {
    parse_graph_str_with_context(input, "<inline graph policy>")
}

/// Parse a `*.graph.toml` file into `GraphPolicySpec`.
pub fn parse_graph_file(path: impl AsRef<Path>) -> Result<GraphPolicySpec, LegitimacyError> {
    let path = path.as_ref();
    let context = path.display().to_string();
    let input = fs::read_to_string(path).map_err(|source| LegitimacyError::PolicyRead {
        path: context.clone(),
        source,
    })?;
    parse_graph_str_with_context(&input, context)
}

/// Parse and validate a raw graph policy string into a `GovernanceGraph`.
pub fn load_graph_str(input: &str) -> Result<GovernanceGraph, LegitimacyError> {
    let spec = parse_graph_str(input)?;
    spec.try_into_graph("<inline graph policy>")
}

/// Parse and validate a `*.graph.toml` file into a `GovernanceGraph`.
pub fn load_graph_file(path: impl AsRef<Path>) -> Result<GovernanceGraph, LegitimacyError> {
    let path = path.as_ref();
    let context = path.display().to_string();
    let spec = parse_graph_file(path)?;
    spec.try_into_graph(context)
}

fn parse_graph_str_with_context(
    input: &str,
    context: impl Into<String>,
) -> Result<GraphPolicySpec, LegitimacyError> {
    let context = context.into();
    toml::from_str(input).map_err(|source| LegitimacyError::PolicyToml { context, source })
}

// ---------------------------------------------------------------------------
// Spec → GovernanceGraph conversion
// ---------------------------------------------------------------------------

impl GraphPolicySpec {
    /// Validate and convert into a `GovernanceGraph`.
    pub fn try_into_graph(
        self,
        context: impl Into<String>,
    ) -> Result<GovernanceGraph, LegitimacyError> {
        let ctx = context.into();
        validate_graph_spec(&self, &ctx)?;

        let mut builder = GraphBuilder::new()?;
        for node_spec in &self.nodes {
            let node = compile_node(node_spec, &ctx)?;
            builder = builder.add_node(node)?;
        }
        for edge_spec in &self.edges {
            let from = NodeId::new(edge_spec.from.clone())
                .map_err(|e| LegitimacyError::invalid_policy(&ctx, e.to_string()))?;
            let to = NodeId::new(edge_spec.to.clone())
                .map_err(|e| LegitimacyError::invalid_policy(&ctx, e.to_string()))?;
            let transform = compile_transform(edge_spec, &ctx)?;
            builder = builder.add_edge(from, to, transform)?;
        }
        builder.build()
    }
}

fn validate_graph_spec(spec: &GraphPolicySpec, ctx: &str) -> Result<(), LegitimacyError> {
    if spec.graph.name.trim().is_empty() {
        return Err(LegitimacyError::invalid_policy(
            ctx,
            "graph.name must not be empty",
        ));
    }
    if spec.graph.version.trim().is_empty() {
        return Err(LegitimacyError::invalid_policy(
            ctx,
            "graph.version must not be empty",
        ));
    }
    // Check for duplicate node ids
    let mut seen_ids = HashSet::new();
    for node in &spec.nodes {
        if node.id.trim().is_empty() {
            return Err(LegitimacyError::invalid_policy(
                ctx,
                "node id must not be empty",
            ));
        }
        if !seen_ids.insert(node.id.clone()) {
            return Err(LegitimacyError::invalid_policy(
                ctx,
                format!("duplicate node id '{}'", node.id),
            ));
        }
    }
    // Check edge endpoints reference declared nodes
    for edge in &spec.edges {
        if !seen_ids.contains(&edge.from) {
            return Err(LegitimacyError::invalid_policy(
                ctx,
                format!("edge from='{}' references undeclared node", edge.from),
            ));
        }
        if !seen_ids.contains(&edge.to) {
            return Err(LegitimacyError::invalid_policy(
                ctx,
                format!("edge to='{}' references undeclared node", edge.to),
            ));
        }
    }
    Ok(())
}

fn compile_node(spec: &NodeSpec, ctx: &str) -> Result<GovernanceNode, LegitimacyError> {
    let id = NodeId::new(spec.id.clone())
        .map_err(|e| LegitimacyError::invalid_policy(ctx, e.to_string()))?;
    let name = spec.name.clone().unwrap_or_else(|| spec.id.clone());

    match spec.node_type.as_str() {
        "binary" => compile_binary_node(id, name, spec, ctx),
        "threshold" => compile_threshold_node(id, name, spec, ctx),
        other => Err(LegitimacyError::invalid_policy(
            ctx,
            format!(
                "unsupported node type '{}'; expected 'binary' or 'threshold'",
                other
            ),
        )),
    }
}

fn compile_binary_node(
    id: NodeId,
    name: String,
    spec: &NodeSpec,
    ctx: &str,
) -> Result<GovernanceNode, LegitimacyError> {
    let default_str = spec.default.as_deref().unwrap_or("deny");
    let default = compile_decision(default_str, ctx)?;
    let combination_str = spec.combination.as_deref().unwrap_or("first_match");
    let combination = compile_gate_logic(combination_str, ctx)?;
    let gates = spec
        .gates
        .iter()
        .map(|g| compile_gate(g, ctx))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(GovernanceNode::Binary {
        id,
        name,
        gates,
        default,
        combination,
    })
}

fn compile_threshold_node(
    id: NodeId,
    name: String,
    spec: &NodeSpec,
    ctx: &str,
) -> Result<GovernanceNode, LegitimacyError> {
    let threshold = spec.threshold.ok_or_else(|| {
        LegitimacyError::invalid_policy(
            ctx,
            format!("threshold node '{}' requires 'threshold' field", spec.id),
        )
    })?;
    let field = spec.field.clone().ok_or_else(|| {
        LegitimacyError::invalid_policy(
            ctx,
            format!("threshold node '{}' requires 'field'", spec.id),
        )
    })?;
    if field.trim().is_empty() {
        return Err(LegitimacyError::invalid_policy(
            ctx,
            format!("threshold node '{}' field must not be empty", spec.id),
        ));
    }
    Ok(GovernanceNode::Threshold {
        id,
        name,
        threshold,
        field,
    })
}

fn compile_gate(spec: &GateSpec, ctx: &str) -> Result<Gate, LegitimacyError> {
    let decision = compile_decision(&spec.decision, ctx)?;
    match spec.gate_type.as_str() {
        "prefix_match" => {
            let pattern = spec.pattern.clone().ok_or_else(|| {
                LegitimacyError::invalid_policy(ctx, "prefix_match gate requires 'pattern'")
            })?;
            Ok(Gate::PrefixMatch { pattern, decision })
        }
        "exact_match" => {
            let value = spec.value.clone().ok_or_else(|| {
                LegitimacyError::invalid_policy(ctx, "exact_match gate requires 'value'")
            })?;
            Ok(Gate::ExactMatch { value, decision })
        }
        "content_match" => {
            let regex = spec.regex.clone().ok_or_else(|| {
                LegitimacyError::invalid_policy(ctx, "content_match gate requires 'regex'")
            })?;
            Ok(Gate::ContentMatch { regex, decision })
        }
        "threshold_gate" => {
            let field = spec.field.clone().ok_or_else(|| {
                LegitimacyError::invalid_policy(ctx, "threshold_gate requires 'field'")
            })?;
            let min = spec.min.ok_or_else(|| {
                LegitimacyError::invalid_policy(ctx, "threshold_gate requires 'min'")
            })?;
            Ok(Gate::ThresholdGate {
                field,
                min,
                decision,
            })
        }
        "peer_relative" => {
            let field = spec.field.clone().ok_or_else(|| {
                LegitimacyError::invalid_policy(ctx, "peer_relative gate requires 'field'")
            })?;
            let percentile = spec.percentile.ok_or_else(|| {
                LegitimacyError::invalid_policy(ctx, "peer_relative gate requires 'percentile'")
            })?;
            Ok(Gate::PeerRelative {
                field,
                percentile,
                decision,
            })
        }
        other => Err(LegitimacyError::invalid_policy(
            ctx,
            format!(
                "unsupported gate type '{}'; expected prefix_match, exact_match, content_match, threshold_gate, or peer_relative",
                other
            ),
        )),
    }
}

fn compile_decision(s: &str, ctx: &str) -> Result<Decision, LegitimacyError> {
    match s {
        "permit" => Ok(Decision::Permit),
        "deny" => Ok(Decision::Deny),
        "escalate" => Ok(Decision::Escalate),
        other => Err(LegitimacyError::invalid_policy(
            ctx,
            format!(
                "unknown decision '{}'; expected permit, deny, or escalate",
                other
            ),
        )),
    }
}

fn compile_gate_logic(s: &str, ctx: &str) -> Result<GateLogic, LegitimacyError> {
    match s {
        "first_match" => Ok(GateLogic::FirstMatch),
        "all_must_pass" => Ok(GateLogic::AllMustPass),
        "any_must_pass" => Ok(GateLogic::AnyMustPass),
        other => Err(LegitimacyError::invalid_policy(
            ctx,
            format!(
                "unknown combination '{}'; expected first_match, all_must_pass, or any_must_pass",
                other
            ),
        )),
    }
}

fn compile_transform(spec: &EdgeSpec, ctx: &str) -> Result<EdgeTransform, LegitimacyError> {
    match spec.transform.as_str() {
        "pass_through" => Ok(EdgeTransform::PassThrough),
        "claim_modification" => {
            let delta = spec.delta.ok_or_else(|| {
                LegitimacyError::invalid_policy(ctx, "claim_modification requires 'delta'")
            })?;
            if !delta.is_finite() {
                return Err(LegitimacyError::invalid_policy(
                    ctx,
                    format!("claim_modification delta must be finite, got {delta}"),
                ));
            }
            Ok(EdgeTransform::ClaimModification { delta })
        }
        other => Err(LegitimacyError::invalid_policy(
            ctx,
            format!(
                "unknown transform '{}'; expected pass_through or claim_modification",
                other
            ),
        )),
    }
}
