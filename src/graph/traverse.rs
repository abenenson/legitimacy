use crate::{
    ClaimantId, Decision, EdgeTransform, GovernanceClaim, GovernanceGraph, LegitimacyError, NodeId,
    graph::{
        ClaimDecision,
        node::{
            decision_rank, evaluate_node_validated, validate_governance_claim,
            validate_governance_claims,
        },
    },
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    sync::Arc,
};

pub(crate) type SharedClaim = Arc<GovernanceClaim>;
type TraversalClaimsState = (
    Vec<NodeId>,
    BTreeMap<ClaimantId, Decision>,
    Option<BTreeMap<NodeId, Vec<ClaimDecision>>>,
);

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct TraversalResult {
    pub entry_nodes: Vec<NodeId>,
    pub node_decisions: BTreeMap<NodeId, Vec<ClaimDecision>>,
    pub final_decisions: BTreeMap<ClaimantId, Decision>,
    pub cycles: Vec<Vec<NodeId>>,
}

pub use crate::graph::cycle::detect_cycles;

pub(crate) fn traverse_final_decisions(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<BTreeMap<ClaimantId, Decision>, LegitimacyError> {
    let (_, final_decisions, _) = traverse_claims(graph, claims, false)?;
    Ok(final_decisions)
}

pub fn traverse(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<TraversalResult, LegitimacyError> {
    let (entry_nodes, final_decisions, node_decisions) = traverse_claims(graph, claims, true)?;

    Ok(TraversalResult {
        entry_nodes,
        node_decisions: node_decisions.unwrap_or_default(),
        final_decisions,
        cycles: Vec::new(),
    })
}

fn traverse_claims(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    capture_node_decisions: bool,
) -> Result<TraversalClaimsState, LegitimacyError> {
    validate_governance_claims(claims)?;

    let cycles = detect_cycles(graph)?;
    if let Some(cycle) = cycles.first() {
        return Err(LegitimacyError::CycleError {
            cycle: cycle.iter().map(ToString::to_string).collect(),
        });
    }

    let incoming_counts = incoming_counts(graph);
    let entry_nodes = graph
        .nodes
        .keys()
        .filter(|node_id| incoming_counts.get(*node_id).copied().unwrap_or(0) == 0)
        .cloned()
        .collect::<Vec<_>>();
    let mut entry_nodes = entry_nodes;
    entry_nodes.sort();
    if graph.nodes.is_empty() || entry_nodes.is_empty() {
        return Err(LegitimacyError::NoEntryNodes);
    }

    let order = topological_order(graph, &incoming_counts)?;
    let shared_claims = claims.iter().cloned().map(Arc::new).collect::<Vec<_>>();
    let mut queued_claims = HashMap::<NodeId, Vec<SharedClaim>>::new();
    for node_id in &entry_nodes {
        queued_claims.insert(node_id.clone(), shared_claims.clone());
    }
    let mut node_decisions =
        capture_node_decisions.then(BTreeMap::<NodeId, Vec<ClaimDecision>>::new);
    let mut final_decisions = BTreeMap::<ClaimantId, Decision>::new();
    let outgoing = outgoing_edges(graph);

    for node_id in order {
        let node =
            graph
                .nodes
                .get(&node_id)
                .ok_or_else(|| LegitimacyError::InvalidEdgeReference {
                    node_id: node_id.to_string(),
                })?;
        let current_claims = queued_claims.remove(&node_id).unwrap_or_default();
        let decisions = evaluate_node_validated(node, &current_claims)?;
        let has_outgoing = outgoing
            .get(&node_id)
            .is_some_and(|edges| !edges.is_empty());
        record_final_decisions(&mut final_decisions, &decisions, has_outgoing);
        let forwarded_claims = forwarded_shared_claims(&current_claims, &decisions);

        if let Some(node_decisions) = node_decisions.as_mut() {
            node_decisions.insert(node_id.clone(), decisions.clone());
        }

        if let Some(edges) = outgoing.get(&node_id) {
            for edge in edges {
                let transformed =
                    apply_transform_shared(&edge.transform, &forwarded_claims, &decisions)?;
                let existing = queued_claims.entry(edge.to.clone()).or_default();
                merge_shared_claim_batches(&edge.to, existing, transformed)?;
            }
        }
    }

    Ok((entry_nodes, final_decisions, node_decisions))
}

pub(crate) fn apply_transform_shared(
    transform: &EdgeTransform,
    claims: &[SharedClaim],
    decisions: &[ClaimDecision],
) -> Result<Vec<SharedClaim>, LegitimacyError> {
    match transform {
        EdgeTransform::PassThrough => Ok(claims.to_vec()),
        EdgeTransform::ClaimModification { delta } => claims
            .iter()
            .zip(decisions.iter())
            .map(|claim| {
                let (claim, decision) = claim;
                if decision.claimant_id == claim.claimant_id
                    && matches!(decision.decision, Decision::Permit)
                {
                    let mut transformed = claim.as_ref().clone();
                    transformed.strength += delta;
                    validate_governance_claim(&transformed)?;
                    Ok(Arc::new(transformed))
                } else {
                    Ok(Arc::clone(claim))
                }
            })
            .collect(),
    }
}

pub(crate) fn apply_transform(
    transform: &EdgeTransform,
    claims: &[GovernanceClaim],
    decisions: &[ClaimDecision],
) -> Result<Vec<GovernanceClaim>, LegitimacyError> {
    match transform {
        EdgeTransform::PassThrough => Ok(claims.to_vec()),
        EdgeTransform::ClaimModification { delta } => claims
            .iter()
            .zip(decisions.iter())
            .map(|claim| {
                let (claim, decision) = claim;
                let mut transformed = claim.clone();
                if decision.claimant_id == transformed.claimant_id
                    && matches!(decision.decision, Decision::Permit)
                {
                    transformed.strength += delta;
                    validate_governance_claim(&transformed)?;
                }
                Ok(transformed)
            })
            .collect(),
    }
}

pub(crate) fn forwarded_shared_claims(
    claims: &[SharedClaim],
    decisions: &[ClaimDecision],
) -> Vec<SharedClaim> {
    claims
        .iter()
        .zip(decisions.iter())
        .filter(|(claim, decision)| {
            decision.claimant_id == claim.claimant_id
                && matches!(decision.decision, Decision::Escalate)
        })
        .map(|(claim, _)| Arc::clone(claim))
        .collect()
}

pub(crate) fn forwarded_claims(
    claims: &[GovernanceClaim],
    decisions: &[ClaimDecision],
) -> Vec<GovernanceClaim> {
    claims
        .iter()
        .zip(decisions.iter())
        .filter(|(claim, decision)| {
            decision.claimant_id == claim.claimant_id
                && matches!(decision.decision, Decision::Escalate)
        })
        .map(|(claim, _)| claim)
        .cloned()
        .collect()
}

pub(crate) fn merge_shared_claim_batches(
    node_id: &NodeId,
    incoming: &mut Vec<SharedClaim>,
    additional: Vec<SharedClaim>,
) -> Result<(), LegitimacyError> {
    let mut merged =
        HashMap::<String, usize>::with_capacity(incoming.len().saturating_add(additional.len()));
    for (index, claim) in incoming.iter().enumerate() {
        merged.insert(claim.claimant_id.clone(), index);
    }

    for claim in additional {
        if let Some(index) = merged.get(&claim.claimant_id).copied() {
            if incoming[index].as_ref() != claim.as_ref() {
                return Err(LegitimacyError::ConflictingClaimFeed {
                    node_id: node_id.to_string(),
                    claimant_id: claim.claimant_id.clone(),
                });
            }
        } else {
            merged.insert(claim.claimant_id.clone(), incoming.len());
            incoming.push(claim);
        }
    }

    Ok(())
}

fn incoming_counts(graph: &GovernanceGraph) -> HashMap<NodeId, usize> {
    let mut counts = HashMap::<NodeId, usize>::new();
    for node_id in graph.nodes.keys() {
        counts.insert(node_id.clone(), 0);
    }
    for edge in &graph.edges {
        *counts.entry(edge.to.clone()).or_insert(0) += 1;
    }
    counts
}

fn outgoing_edges(graph: &GovernanceGraph) -> HashMap<NodeId, Vec<crate::GovernanceEdge>> {
    let mut outgoing = HashMap::<NodeId, Vec<crate::GovernanceEdge>>::new();
    for edge in &graph.edges {
        outgoing
            .entry(edge.from.clone())
            .or_default()
            .push(edge.clone());
    }
    outgoing
}

fn topological_order(
    graph: &GovernanceGraph,
    incoming_counts: &HashMap<NodeId, usize>,
) -> Result<Vec<NodeId>, LegitimacyError> {
    let mut counts = incoming_counts.clone();
    let mut queue = BTreeSet::new();
    for node_id in graph.nodes.keys() {
        if counts.get(node_id).copied().unwrap_or(0) == 0 {
            queue.insert(node_id.clone());
        }
    }

    let mut order = Vec::with_capacity(graph.nodes.len());
    while let Some(node_id) = queue.pop_first() {
        order.push(node_id.clone());
        for edge in graph.edges.iter().filter(|edge| edge.from == node_id) {
            let count =
                counts
                    .get_mut(&edge.to)
                    .ok_or_else(|| LegitimacyError::InvalidEdgeReference {
                        node_id: edge.to.to_string(),
                    })?;
            *count -= 1;
            if *count == 0 {
                queue.insert(edge.to.clone());
            }
        }
    }

    if order.len() != graph.nodes.len() {
        let cycles = detect_cycles(graph)?;
        if let Some(cycle) = cycles.first() {
            return Err(LegitimacyError::CycleError {
                cycle: cycle.iter().map(ToString::to_string).collect(),
            });
        }
    }

    Ok(order)
}

fn record_final_decisions(
    final_decisions: &mut BTreeMap<ClaimantId, Decision>,
    decisions: &[ClaimDecision],
    has_outgoing: bool,
) {
    for decision in decisions {
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
}

pub(crate) fn merge_final_decision(left: &Decision, right: &Decision) -> Decision {
    if decision_rank(left) <= decision_rank(right) {
        left.clone()
    } else {
        right.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::{
        detect_cycles, incoming_counts, merge_final_decision, topological_order, traverse,
    };
    use crate::{
        Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceNode, GraphBuilder,
        LegitimacyError, NodeId,
    };
    use std::collections::BTreeMap;

    #[test]
    fn traverse_passes_escalated_claims_to_next_node() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(escalate_node("entry")))
            .and_then(|builder| builder.add_node(deny_rm_node("approval")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("entry").unwrap(),
                    NodeId::new("approval").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();
        let claims = vec![GovernanceClaim {
            claimant_id: "alice".to_string(),
            strength: 1.0,
            priority_class: None,
            path: Some("/tmp/file".to_string()),
            action: Some("Write".to_string()),
            content: Some("rm -rf /tmp/file".to_string()),
            metrics: BTreeMap::new(),
        }];

        let result = traverse(&graph, &claims).unwrap();

        assert_eq!(result.entry_nodes, vec![NodeId::new("entry").unwrap()]);
        assert_eq!(
            result.node_decisions[&NodeId::new("entry").unwrap()][0].decision,
            Decision::Escalate
        );
        assert_eq!(
            result.node_decisions[&NodeId::new("approval").unwrap()][0].decision,
            Decision::Deny
        );
        assert_eq!(result.final_decisions["alice"], Decision::Deny);
    }

    #[test]
    fn claim_modification_only_strengthens_permitted_claimants() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(selective_entry_node("entry")))
            .and_then(|builder| builder.add_node(review_node("review")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("entry").unwrap(),
                    NodeId::new("review").unwrap(),
                    EdgeTransform::ClaimModification { delta: 0.2 },
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();
        let claims = vec![
            GovernanceClaim {
                claimant_id: "alice".to_string(),
                strength: 0.7,
                priority_class: None,
                path: None,
                action: None,
                content: None,
                metrics: BTreeMap::new(),
            },
            GovernanceClaim {
                claimant_id: "bob".to_string(),
                strength: 0.6,
                priority_class: None,
                path: None,
                action: None,
                content: None,
                metrics: BTreeMap::new(),
            },
        ];

        let result = traverse(&graph, &claims).unwrap();

        assert_eq!(result.final_decisions["alice"], Decision::Permit);
        assert_eq!(result.final_decisions["bob"], Decision::Deny);
        let review_decisions = &result.node_decisions[&NodeId::new("review").unwrap()];
        assert_eq!(review_decisions.len(), 1);
        assert_eq!(review_decisions[0].claimant_id, "bob");
    }

    #[test]
    fn detect_cycles_returns_strongly_connected_components() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(escalate_node("a")))
            .and_then(|builder| builder.add_node(escalate_node("b")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("a").unwrap(),
                    NodeId::new("b").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("b").unwrap(),
                    NodeId::new("a").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();

        let cycles = detect_cycles(&graph).unwrap();

        assert_eq!(cycles.len(), 1);
        assert_eq!(cycles[0].len(), 2);
    }

    #[test]
    fn topological_order_is_sorted_for_independent_entries() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(escalate_node("z-entry")))
            .and_then(|builder| builder.add_node(escalate_node("a-entry")))
            .and_then(GraphBuilder::build)
            .unwrap();

        let order = topological_order(&graph, &incoming_counts(&graph)).unwrap();

        assert_eq!(
            order,
            vec![
                NodeId::new("a-entry").unwrap(),
                NodeId::new("z-entry").unwrap()
            ]
        );
    }

    #[test]
    fn parallel_exits_merge_to_most_restrictive_decision() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(escalate_node("entry")))
            .and_then(|builder| builder.add_node(permit_node("allow")))
            .and_then(|builder| builder.add_node(deny_node("deny")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("entry").unwrap(),
                    NodeId::new("allow").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("entry").unwrap(),
                    NodeId::new("deny").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();
        let claims = vec![GovernanceClaim {
            claimant_id: "alice".to_string(),
            strength: 1.0,
            priority_class: None,
            path: None,
            action: None,
            content: None,
            metrics: BTreeMap::new(),
        }];

        let result = traverse(&graph, &claims).unwrap();

        assert_eq!(result.final_decisions["alice"], Decision::Deny);
        assert_eq!(
            merge_final_decision(&Decision::Permit, &Decision::Escalate),
            Decision::Escalate
        );
    }

    #[test]
    fn traverse_rejects_cycles_without_convergence_handling() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(escalate_node("a")))
            .and_then(|builder| builder.add_node(escalate_node("b")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("a").unwrap(),
                    NodeId::new("b").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("b").unwrap(),
                    NodeId::new("a").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();
        let claims = vec![GovernanceClaim {
            claimant_id: "alice".to_string(),
            strength: 1.0,
            priority_class: None,
            path: None,
            action: None,
            content: None,
            metrics: BTreeMap::new(),
        }];

        let result = traverse(&graph, &claims);

        assert!(matches!(result, Err(LegitimacyError::CycleError { .. })));
    }

    fn escalate_node(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: Vec::new(),
            default: Decision::Escalate,
            combination: GateLogic::FirstMatch,
        }
    }

    fn deny_rm_node(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: vec![Gate::ContentMatch {
                regex: "rm -rf".to_string(),
                decision: Decision::Deny,
            }],
            default: Decision::Permit,
            combination: GateLogic::FirstMatch,
        }
    }

    fn selective_entry_node(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: vec![Gate::ThresholdGate {
                field: "strength".to_string(),
                min: 0.65,
                decision: Decision::Permit,
            }],
            default: Decision::Escalate,
            combination: GateLogic::FirstMatch,
        }
    }

    fn review_node(id: &str) -> GovernanceNode {
        GovernanceNode::Threshold {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            threshold: 0.75,
            field: "strength".to_string(),
        }
    }

    fn permit_node(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: Vec::new(),
            default: Decision::Permit,
            combination: GateLogic::FirstMatch,
        }
    }

    fn deny_node(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: Vec::new(),
            default: Decision::Deny,
            combination: GateLogic::FirstMatch,
        }
    }
}
