use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::{
    ClaimantId, Decision, EdgeTransform, GovernanceClaim, GovernanceEdge, GovernanceGraph,
    GovernanceNode, LegitimacyError, NodeId,
    graph::{
        Gate, GateLogic,
        cycle::detect_cycles,
        node::{decision_rank, evaluate_node, merge_claim_batches},
        traverse::{
            apply_transform, forwarded_claims, merge_final_decision, traverse_final_decisions,
        },
    },
};

const DEFAULT_STRENGTH_DELTAS: [f64; 4] = [0.05, 0.10, 0.20, 0.40];
const REVIEW_PERCENTILES: [f64; 4] = [0.60, 2.0 / 3.0, 0.75, 0.90];

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum GraphParadoxType {
    CompositionalAlabama,
    FeedbackMonotonicity,
    PathDependence,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct GraphParadoxViolation {
    pub paradox_type: GraphParadoxType,
    pub description: String,
    pub original_decisions: BTreeMap<ClaimantId, Decision>,
    pub perturbed_decisions: BTreeMap<ClaimantId, Decision>,
}

/// Detect the scoped "compositional Alabama" graph witness used by the
/// extractor diagnostics.
///
/// This is not a generic Balinski-Young apportionment checker. It tests one
/// hardcoded governance-graph perturbation family: append a synthetic
/// peer-review node after each sink, with a small fixed percentile grid over
/// the `strength` field, then report the first claimant whose final decision
/// worsens relative to the original acyclic traversal.
pub fn compositional_alabama(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<Option<GraphParadoxViolation>, LegitimacyError> {
    let baseline = traverse_final_decisions(graph, claims)?;

    for sink in sink_nodes(graph) {
        for percentile in REVIEW_PERCENTILES {
            let mut perturbed = graph.clone();
            let review_id = fresh_node_id(&perturbed, &format!("{}-review", sink))?;
            let review_node = GovernanceNode::Binary {
                id: review_id.clone(),
                name: format!("peer-review-{sink}-{percentile:.2}"),
                gates: vec![Gate::PeerRelative {
                    field: "strength".to_string(),
                    percentile,
                    decision: Decision::Permit,
                }],
                default: Decision::Deny,
                combination: GateLogic::AnyMustPass,
            };
            perturbed.nodes.insert(review_id.clone(), review_node);
            perturbed.edges.push(GovernanceEdge::new(
                sink.clone(),
                review_id.clone(),
                EdgeTransform::PassThrough,
            )?);

            let candidate = traverse_final_decisions(&perturbed, claims)?;
            if let Some((claimant_id, before, after)) =
                first_worsening(&baseline, &candidate, claims)
            {
                return Ok(Some(GraphParadoxViolation {
                    paradox_type: GraphParadoxType::CompositionalAlabama,
                    description: format!(
                        "Appending peer-review node '{}' after '{}' at percentile {:.2} worsened '{}' from {:?} to {:?}",
                        review_id, sink, percentile, claimant_id, before, after
                    ),
                    original_decisions: baseline,
                    perturbed_decisions: candidate,
                }));
            }
        }
    }

    Ok(None)
}

pub fn feedback_monotonicity(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<Option<GraphParadoxViolation>, LegitimacyError> {
    for cycle in detect_cycles(graph)? {
        let baseline = stabilize_cycle(graph, &cycle, claims, 32, crate::EPSILON)?;
        if !baseline.converged {
            continue;
        }

        for (index, claim) in claims.iter().enumerate() {
            for delta in DEFAULT_STRENGTH_DELTAS {
                let strengthened = claims
                    .iter()
                    .enumerate()
                    .map(|(claim_index, current)| {
                        if claim_index == index {
                            strengthen_claim(current, delta)
                        } else {
                            Ok(current.clone())
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let candidate = stabilize_cycle(graph, &cycle, &strengthened, 32, crate::EPSILON)?;
                if !candidate.converged {
                    continue;
                }

                if let Some((claimant_id, before, after)) = first_worsening(
                    &baseline.fixed_point_decisions,
                    &candidate.fixed_point_decisions,
                    claims,
                ) {
                    return Ok(Some(GraphParadoxViolation {
                        paradox_type: GraphParadoxType::FeedbackMonotonicity,
                        description: format!(
                            "Strengthening '{}' by {:.2} made cycle {:?} settle to a worse outcome for '{}' from {:?} to {:?}",
                            claim.claimant_id, delta, cycle, claimant_id, before, after
                        ),
                        original_decisions: baseline.fixed_point_decisions,
                        perturbed_decisions: candidate.fixed_point_decisions,
                    }));
                }
            }
        }
    }

    Ok(None)
}

pub fn path_dependence(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<Option<GraphParadoxViolation>, LegitimacyError> {
    if !detect_cycles(graph)?.is_empty() {
        return Ok(None);
    }

    let ascending = topological_order_with_tiebreak(graph, TieBreak::Ascending)?;
    let descending = topological_order_with_tiebreak(graph, TieBreak::Descending)?;
    if ascending == descending {
        return Ok(None);
    }

    let left = evaluate_with_order(graph, claims, &ascending)?;
    let right = evaluate_with_order(graph, claims, &descending)?;
    if let Some((claimant_id, first, second)) =
        first_difference(&left.final_decisions, &right.final_decisions, claims)
    {
        return Ok(Some(GraphParadoxViolation {
            paradox_type: GraphParadoxType::PathDependence,
            description: format!(
                "Evaluating the same DAG in orders {} and {} changed '{}' from {:?} to {:?}",
                format_order(&ascending),
                format_order(&descending),
                claimant_id,
                first,
                second
            ),
            original_decisions: left.final_decisions,
            perturbed_decisions: right.final_decisions,
        }));
    }

    Ok(None)
}

#[derive(Debug, Clone)]
struct StabilizedCycle {
    converged: bool,
    fixed_point_decisions: BTreeMap<ClaimantId, Decision>,
}

fn stabilize_cycle(
    graph: &GovernanceGraph,
    cycle: &[NodeId],
    claims: &[GovernanceClaim],
    max_iterations: usize,
    epsilon: f64,
) -> Result<StabilizedCycle, LegitimacyError> {
    if cycle.is_empty() {
        return Err(LegitimacyError::invalid_input(
            "feedback monotonicity requires at least one node in the cycle",
        ));
    }

    let edge_map = cycle_edge_map(graph, cycle);
    let positions = cycle
        .iter()
        .enumerate()
        .map(|(index, node_id)| (node_id.clone(), index))
        .collect::<HashMap<_, _>>();
    let entry = cycle[0].clone();
    let mut queued_claims = HashMap::from([(entry, claims.to_vec())]);
    let mut last_decisions = BTreeMap::new();

    for _ in 0..max_iterations {
        let prior_state = queued_claims.clone();
        let mut current_queued = queued_claims;
        let mut next_iteration = HashMap::<NodeId, Vec<GovernanceClaim>>::new();
        let mut decisions = last_decisions.clone();

        for (index, node_id) in cycle.iter().enumerate() {
            let node =
                graph
                    .nodes
                    .get(node_id)
                    .ok_or_else(|| LegitimacyError::InvalidEdgeReference {
                        node_id: node_id.to_string(),
                    })?;
            let current_claims = current_queued.remove(node_id).unwrap_or_default();
            let current_decisions = evaluate_node(node, &current_claims)?;
            for decision in &current_decisions {
                decisions.insert(decision.claimant_id.clone(), decision.decision.clone());
            }
            let forwarded = forwarded_claims(&current_claims, &current_decisions);

            for edge in edge_map.get(node_id).into_iter().flatten() {
                let transformed = apply_transform(&edge.transform, &forwarded, &current_decisions)?;
                let target_index = positions.get(&edge.to).copied().ok_or_else(|| {
                    LegitimacyError::InvalidEdgeReference {
                        node_id: edge.to.to_string(),
                    }
                })?;
                if target_index > index {
                    let existing = current_queued.get(&edge.to).cloned().unwrap_or_default();
                    let merged = merge_claim_batches(&edge.to, &existing, &transformed)?;
                    current_queued.insert(edge.to.clone(), merged);
                } else {
                    let existing = next_iteration.get(&edge.to).cloned().unwrap_or_default();
                    let merged = merge_claim_batches(&edge.to, &existing, &transformed)?;
                    next_iteration.insert(edge.to.clone(), merged);
                }
            }
        }

        last_decisions = decisions;
        if state_matches(&prior_state, &next_iteration, epsilon) {
            return Ok(StabilizedCycle {
                converged: true,
                fixed_point_decisions: last_decisions,
            });
        }
        queued_claims = next_iteration;
    }

    Ok(StabilizedCycle {
        converged: false,
        fixed_point_decisions: last_decisions,
    })
}

fn cycle_edge_map(
    graph: &GovernanceGraph,
    cycle: &[NodeId],
) -> HashMap<NodeId, Vec<GovernanceEdge>> {
    let cycle_set = cycle.iter().cloned().collect::<BTreeSet<_>>();
    let mut edges = HashMap::<NodeId, Vec<GovernanceEdge>>::new();
    for edge in &graph.edges {
        if cycle_set.contains(&edge.from) && cycle_set.contains(&edge.to) {
            edges
                .entry(edge.from.clone())
                .or_default()
                .push(edge.clone());
        }
    }
    edges
}

fn strengthen_claim(
    claim: &GovernanceClaim,
    delta: f64,
) -> Result<GovernanceClaim, LegitimacyError> {
    let mut strengthened = claim.clone();
    strengthened.strength += delta;
    if !strengthened.strength.is_finite() || strengthened.strength <= 0.0 {
        return Err(LegitimacyError::InvalidGovernanceStrength {
            claimant_id: strengthened.claimant_id.clone(),
            strength: strengthened.strength,
        });
    }
    Ok(strengthened)
}

#[derive(Clone, Copy)]
enum TieBreak {
    Ascending,
    Descending,
}

fn topological_order_with_tiebreak(
    graph: &GovernanceGraph,
    tiebreak: TieBreak,
) -> Result<Vec<NodeId>, LegitimacyError> {
    let mut incoming = HashMap::<NodeId, usize>::new();
    for node_id in graph.nodes.keys() {
        incoming.insert(node_id.clone(), 0);
    }
    for edge in &graph.edges {
        *incoming.entry(edge.to.clone()).or_insert(0) += 1;
    }

    let mut ready = graph
        .nodes
        .keys()
        .filter(|node_id| incoming.get(*node_id).copied().unwrap_or(0) == 0)
        .cloned()
        .collect::<Vec<_>>();
    let mut order = Vec::with_capacity(graph.nodes.len());

    while !ready.is_empty() {
        ready.sort_by(|left, right| left.as_str().cmp(right.as_str()));
        let node_id = match tiebreak {
            TieBreak::Ascending => ready.remove(0),
            TieBreak::Descending => ready.pop().ok_or_else(|| {
                LegitimacyError::invalid_input("topological sort: ready queue unexpectedly empty")
            })?,
        };
        order.push(node_id.clone());

        for edge in graph.edges.iter().filter(|edge| edge.from == node_id) {
            let remaining = incoming.get_mut(&edge.to).ok_or_else(|| {
                LegitimacyError::InvalidEdgeReference {
                    node_id: edge.to.to_string(),
                }
            })?;
            *remaining -= 1;
            if *remaining == 0 {
                ready.push(edge.to.clone());
            }
        }
    }

    if order.len() != graph.nodes.len() {
        return Err(LegitimacyError::CycleError {
            cycle: detect_cycles(graph)?
                .into_iter()
                .next()
                .unwrap_or_default()
                .into_iter()
                .map(|node_id| node_id.to_string())
                .collect(),
        });
    }

    Ok(order)
}

#[derive(Debug, Clone)]
struct OrderedTraversal {
    final_decisions: BTreeMap<ClaimantId, Decision>,
}

fn evaluate_with_order(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    order: &[NodeId],
) -> Result<OrderedTraversal, LegitimacyError> {
    validate_topological_order(graph, order)?;

    let mut incoming = HashMap::<NodeId, usize>::new();
    for node_id in graph.nodes.keys() {
        incoming.insert(node_id.clone(), 0);
    }
    for edge in &graph.edges {
        *incoming.entry(edge.to.clone()).or_insert(0) += 1;
    }
    let entry_nodes = graph
        .nodes
        .keys()
        .filter(|node_id| incoming.get(*node_id).copied().unwrap_or(0) == 0)
        .cloned()
        .collect::<Vec<_>>();
    let mut queued_claims = HashMap::<NodeId, Vec<GovernanceClaim>>::new();
    for node_id in entry_nodes {
        queued_claims.insert(node_id, claims.to_vec());
    }
    let mut final_decisions = BTreeMap::<ClaimantId, Decision>::new();
    let outgoing = graph.edges.iter().fold(
        HashMap::<NodeId, Vec<crate::GovernanceEdge>>::new(),
        |mut acc, edge| {
            acc.entry(edge.from.clone()).or_default().push(edge.clone());
            acc
        },
    );

    for node_id in order {
        let node =
            graph
                .nodes
                .get(node_id)
                .ok_or_else(|| LegitimacyError::InvalidEdgeReference {
                    node_id: node_id.to_string(),
                })?;
        let current_claims = queued_claims.remove(node_id).unwrap_or_default();
        let decisions = evaluate_node(node, &current_claims)?;
        let has_outgoing = outgoing.get(node_id).is_some_and(|edges| !edges.is_empty());
        for decision in &decisions {
            if matches!(decision.decision, Decision::Escalate) && has_outgoing {
                continue;
            }
            let claimant_id = decision.claimant_id.clone();
            let merged = final_decisions
                .get(&claimant_id)
                .map(|existing| merge_final_decision(existing, &decision.decision))
                .unwrap_or_else(|| decision.decision.clone());
            final_decisions.insert(claimant_id, merged);
        }
        let forwarded = forwarded_claims(&current_claims, &decisions);
        for edge in outgoing.get(node_id).into_iter().flatten() {
            let transformed = apply_transform(&edge.transform, &forwarded, &decisions)?;
            let existing = queued_claims.get(&edge.to).cloned().unwrap_or_default();
            let merged = merge_claim_batches(&edge.to, &existing, &transformed)?;
            queued_claims.insert(edge.to.clone(), merged);
        }
    }

    Ok(OrderedTraversal { final_decisions })
}

fn validate_topological_order(
    graph: &GovernanceGraph,
    order: &[NodeId],
) -> Result<(), LegitimacyError> {
    if order.len() != graph.nodes.len() {
        return Err(LegitimacyError::invalid_input(
            "topological order must include every node exactly once",
        ));
    }

    let mut seen = BTreeSet::new();
    let positions = order
        .iter()
        .enumerate()
        .map(|(index, node_id)| {
            if !graph.nodes.contains_key(node_id) {
                return Err(LegitimacyError::InvalidEdgeReference {
                    node_id: node_id.to_string(),
                });
            }
            if !seen.insert(node_id.clone()) {
                return Err(LegitimacyError::invalid_input(format!(
                    "node '{}' appears more than once in evaluation order",
                    node_id
                )));
            }
            Ok((node_id.clone(), index))
        })
        .collect::<Result<HashMap<_, _>, _>>()?;

    for edge in &graph.edges {
        let from = positions.get(&edge.from).copied().ok_or_else(|| {
            LegitimacyError::InvalidEdgeReference {
                node_id: edge.from.to_string(),
            }
        })?;
        let to = positions.get(&edge.to).copied().ok_or_else(|| {
            LegitimacyError::InvalidEdgeReference {
                node_id: edge.to.to_string(),
            }
        })?;
        if from >= to {
            return Err(LegitimacyError::invalid_input(format!(
                "order {} violates edge {} -> {}",
                format_order(order),
                edge.from,
                edge.to
            )));
        }
    }

    Ok(())
}

fn state_matches(
    left: &HashMap<NodeId, Vec<GovernanceClaim>>,
    right: &HashMap<NodeId, Vec<GovernanceClaim>>,
    epsilon: f64,
) -> bool {
    if left.len() != right.len() {
        return false;
    }

    left.iter().all(|(node_id, left_claims)| {
        right
            .get(node_id)
            .is_some_and(|right_claims| claims_match(left_claims, right_claims, epsilon))
    })
}

fn claims_match(left: &[GovernanceClaim], right: &[GovernanceClaim], epsilon: f64) -> bool {
    if left.len() != right.len() {
        return false;
    }

    let left = left
        .iter()
        .cloned()
        .map(|claim| (claim.claimant_id.clone(), claim))
        .collect::<BTreeMap<_, _>>();
    let right = right
        .iter()
        .cloned()
        .map(|claim| (claim.claimant_id.clone(), claim))
        .collect::<BTreeMap<_, _>>();
    if left.keys().collect::<Vec<_>>() != right.keys().collect::<Vec<_>>() {
        return false;
    }

    left.iter().all(|(claimant_id, before)| {
        right
            .get(claimant_id)
            .is_some_and(|after| claim_matches(before, after, epsilon))
    })
}

fn claim_matches(left: &GovernanceClaim, right: &GovernanceClaim, epsilon: f64) -> bool {
    left.claimant_id == right.claimant_id
        && left.priority_class == right.priority_class
        && left.path == right.path
        && left.action == right.action
        && left.content == right.content
        && (left.strength - right.strength).abs() <= epsilon
        && metrics_match(&left.metrics, &right.metrics, epsilon)
}

fn metrics_match(
    left: &BTreeMap<String, f64>,
    right: &BTreeMap<String, f64>,
    epsilon: f64,
) -> bool {
    if left.len() != right.len() {
        return false;
    }
    left.iter().all(|(field, left_value)| {
        right
            .get(field)
            .is_some_and(|right_value| (left_value - right_value).abs() <= epsilon)
    })
}

fn sink_nodes(graph: &GovernanceGraph) -> Vec<NodeId> {
    let mut sinks = graph
        .nodes
        .keys()
        .filter(|node_id| !graph.edges.iter().any(|edge| edge.from == **node_id))
        .cloned()
        .collect::<Vec<_>>();
    sinks.sort();
    sinks
}

fn first_worsening(
    before: &BTreeMap<ClaimantId, Decision>,
    after: &BTreeMap<ClaimantId, Decision>,
    claims: &[GovernanceClaim],
) -> Option<(ClaimantId, Decision, Decision)> {
    // When multiple witnesses exist, use the lexicographically smallest
    // claimant ID so diagnostics stay stable across runs.
    claims
        .iter()
        .map(|claim| claim.claimant_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .find_map(|claimant_id| {
            let original = before
                .get(&claimant_id)
                .cloned()
                .unwrap_or(Decision::Escalate);
            let perturbed = after
                .get(&claimant_id)
                .cloned()
                .unwrap_or(Decision::Escalate);
            (decision_rank(&perturbed) < decision_rank(&original)).then_some((
                claimant_id.clone(),
                original,
                perturbed,
            ))
        })
}

fn first_difference(
    left: &BTreeMap<ClaimantId, Decision>,
    right: &BTreeMap<ClaimantId, Decision>,
    claims: &[GovernanceClaim],
) -> Option<(ClaimantId, Decision, Decision)> {
    claims
        .iter()
        .map(|claim| claim.claimant_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .find_map(|claimant_id| {
            let first = left
                .get(&claimant_id)
                .cloned()
                .unwrap_or(Decision::Escalate);
            let second = right
                .get(&claimant_id)
                .cloned()
                .unwrap_or(Decision::Escalate);
            (first != second).then_some((claimant_id.clone(), first, second))
        })
}

fn fresh_node_id(graph: &GovernanceGraph, prefix: &str) -> Result<NodeId, LegitimacyError> {
    let base = sanitize_node_id(prefix);
    let mut suffix = 0usize;
    loop {
        let candidate = if suffix == 0 {
            base.clone()
        } else {
            format!("{base}-{suffix}")
        };
        let node_id = NodeId::new(candidate.clone())?;
        if !graph.nodes.contains_key(&node_id) {
            return Ok(node_id);
        }
        suffix += 1;
    }
}

fn sanitize_node_id(value: &str) -> String {
    let mut sanitized = value
        .chars()
        .map(|ch| match ch {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '-' | '_' => ch,
            _ => '-',
        })
        .collect::<String>();
    if sanitized.trim_matches('-').is_empty() {
        sanitized = "graph-review".to_string();
    }
    sanitized
}

fn format_order(order: &[NodeId]) -> String {
    order
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" -> ")
}
