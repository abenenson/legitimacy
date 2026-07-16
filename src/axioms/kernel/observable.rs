//! Canonical implementation of the `graph observable determinacy` axiom.
//!
//! Operational definition: for every claim, the final per-claimant decision
//! produced by traversing the graph is invariant across every legal
//! topological order. This is the graph-side projection of the kernel
//! observable predicate — it is **not** the kernel observable predicate
//! itself; the canonical Lean predicate `GovernanceObservable` and its
//! semantic dependencies live upstream.
//!
//! Canonical wire string: `"graph observable determinacy"`. The bare
//! `"observable"` would overclaim the underlying predicate. Naming matches
//! the existing `"graph consistency"` / `"graph nonvacuity"` family.
//!
//! Skip convention: this check returns `AxiomVerdict::Skipped` to indicate
//! that the input was not exhaustively verified. Three classes are skipped
//! under this convention: (1) cyclic graphs, where cycles are reported
//! separately via the audit pipeline's cycle-finding surface and the
//! `iterate_cycle` probe; (2) empty graphs; (3) acyclic graphs that
//! exceed `EXHAUSTIVE_OBSERVABLE_NODE_LIMIT` nodes or whose topological-
//! order count exceeds `EXHAUSTIVE_OBSERVABLE_ORDER_LIMIT`. Only inputs
//! that return `Pass` with `perturbations_tested > 0` have been
//! mechanically order-independence-checked by exhaustive enumeration.
//!
//! Implementation note: feasible graphs are checked by exhaustive
//! topological-order enumeration. Lean now also proves
//! `auditTraversalDeterministic_of_acyclic_passthrough` for the
//! passthrough-only acyclic class. This Rust runtime still uses
//! `Skipped` for over-limit graphs because it does not yet verify that an
//! arbitrary over-limit input belongs to that Lean structural class before
//! returning.
//!
//! Lean audit fixtures: `auditTraversalDeterministic_of_acyclic_passthrough`
//! proves the structural passthrough-only acyclic predicate, and
//! `audit_traversal_confluence` proves the concrete compiler-audit
//! traversal-confluence slice.

use super::{AxiomVerdict, KernelAxiom};
use crate::{
    Allocation, Claim, ClaimantId, Counterexample, Decision, Estate, GovernanceClaim,
    GovernanceEdge, GovernanceGraph, LegitimacyError, NodeId, ValidAllocation,
    graph::{
        cycle::detect_cycles,
        node::{evaluate_node, merge_claim_batches},
        traverse::{apply_transform, forwarded_claims, merge_final_decision},
    },
};
use std::collections::{BTreeMap, BTreeSet, HashMap};

const EXHAUSTIVE_OBSERVABLE_ORDER_LIMIT: usize = 100_000;
const EXHAUSTIVE_OBSERVABLE_NODE_LIMIT: usize = 10;

#[derive(Debug, Clone)]
struct OrderedTraversal {
    final_decisions: BTreeMap<ClaimantId, Decision>,
}

pub fn check_graph_observable_determinacy(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<AxiomVerdict, LegitimacyError> {
    check_graph_traversal_order_invariance(graph, claims)
}

fn check_graph_traversal_order_invariance(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
) -> Result<AxiomVerdict, LegitimacyError> {
    if !detect_cycles(graph)?.is_empty() {
        return Ok(AxiomVerdict::skipped(
            KernelAxiom::Observable,
            "cyclic graphs are handled by cycle and nonvacuity probes",
        ));
    }
    if graph.nodes.is_empty() {
        return Ok(AxiomVerdict::skipped(
            KernelAxiom::Observable,
            "empty graph has no order-dependent decision surface",
        ));
    }

    let canonical_order = topological_order(graph)?;
    let _canonical = evaluate_with_order(graph, claims, &canonical_order)?;
    if graph.nodes.len() > EXHAUSTIVE_OBSERVABLE_NODE_LIMIT {
        return Ok(AxiomVerdict::skipped(
            KernelAxiom::Observable,
            format!(
                "graph has {} nodes, above exhaustive observable-determinacy limit {EXHAUSTIVE_OBSERVABLE_NODE_LIMIT}",
                graph.nodes.len()
            ),
        ));
    }

    let order_count = count_topological_orders_up_to(graph, EXHAUSTIVE_OBSERVABLE_ORDER_LIMIT)?;
    if order_count > EXHAUSTIVE_OBSERVABLE_ORDER_LIMIT {
        return Ok(AxiomVerdict::skipped(
            KernelAxiom::Observable,
            format!(
                "graph has more than {EXHAUSTIVE_OBSERVABLE_ORDER_LIMIT} legal topological orders"
            ),
        ));
    }

    let canonical = _canonical;

    let orders = all_topological_orders(graph)?;
    let mut tested = 1usize;

    for order in orders {
        if order == canonical_order {
            continue;
        }
        let candidate = evaluate_with_order(graph, claims, &order)?;
        tested += 1;
        if let Some((claimant_id, first, second)) = first_difference(
            &canonical.final_decisions,
            &candidate.final_decisions,
            claims,
        ) {
            return observable_rejection(
                KernelAxiom::Observable,
                claims,
                &format!(
                    "Evaluating graph orders {} and {} changed '{}' from {:?} to {:?}",
                    format_order(&canonical_order),
                    format_order(&order),
                    claimant_id,
                    first,
                    second
                ),
                &canonical.final_decisions,
                &candidate.final_decisions,
            );
        }
    }

    Ok(AxiomVerdict::pass(KernelAxiom::Observable, tested))
}

fn count_topological_orders_up_to(
    graph: &GovernanceGraph,
    limit: usize,
) -> Result<usize, LegitimacyError> {
    let mut incoming = incoming_counts(graph);
    let ready = graph
        .nodes
        .keys()
        .filter(|node_id| incoming.get(*node_id).copied().unwrap_or(0) == 0)
        .cloned()
        .collect::<BTreeSet<_>>();
    count_orders(graph, &mut incoming, ready, 0, limit)
}

fn count_orders(
    graph: &GovernanceGraph,
    incoming: &mut HashMap<NodeId, usize>,
    ready: BTreeSet<NodeId>,
    prefix_len: usize,
    limit: usize,
) -> Result<usize, LegitimacyError> {
    if prefix_len == graph.nodes.len() {
        return Ok(1);
    }
    if ready.is_empty() {
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

    let mut total = 0usize;
    for node_id in ready.iter().cloned().collect::<Vec<_>>() {
        let mut next_ready = ready.clone();
        next_ready.remove(&node_id);
        for edge in graph.edges.iter().filter(|edge| edge.from == node_id) {
            let remaining = incoming.get_mut(&edge.to).ok_or_else(|| {
                LegitimacyError::InvalidEdgeReference {
                    node_id: edge.to.to_string(),
                }
            })?;
            *remaining -= 1;
            if *remaining == 0 {
                next_ready.insert(edge.to.clone());
            }
        }

        let branch = count_orders(graph, incoming, next_ready, prefix_len + 1, limit)?;

        for edge in graph.edges.iter().filter(|edge| edge.from == node_id) {
            let remaining = incoming.get_mut(&edge.to).ok_or_else(|| {
                LegitimacyError::InvalidEdgeReference {
                    node_id: edge.to.to_string(),
                }
            })?;
            *remaining += 1;
        }

        total = total.saturating_add(branch);
        if total > limit {
            return Ok(total);
        }
    }

    Ok(total)
}

fn topological_order(graph: &GovernanceGraph) -> Result<Vec<NodeId>, LegitimacyError> {
    let mut incoming = incoming_counts(graph);
    let mut ready = graph
        .nodes
        .keys()
        .filter(|node_id| incoming.get(*node_id).copied().unwrap_or(0) == 0)
        .cloned()
        .collect::<Vec<_>>();
    let mut order = Vec::with_capacity(graph.nodes.len());

    while !ready.is_empty() {
        ready.sort();
        let node_id = ready.remove(0);
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

    validate_topological_order(graph, &order)?;
    Ok(order)
}

fn all_topological_orders(graph: &GovernanceGraph) -> Result<Vec<Vec<NodeId>>, LegitimacyError> {
    let mut incoming = incoming_counts(graph);
    let ready = graph
        .nodes
        .keys()
        .filter(|node_id| incoming.get(*node_id).copied().unwrap_or(0) == 0)
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut orders = Vec::new();
    enumerate_orders(
        graph,
        &mut incoming,
        ready,
        Vec::with_capacity(graph.nodes.len()),
        &mut orders,
    )?;

    Ok(orders)
}

fn enumerate_orders(
    graph: &GovernanceGraph,
    incoming: &mut HashMap<NodeId, usize>,
    ready: BTreeSet<NodeId>,
    prefix: Vec<NodeId>,
    orders: &mut Vec<Vec<NodeId>>,
) -> Result<(), LegitimacyError> {
    if prefix.len() == graph.nodes.len() {
        orders.push(prefix);
        return Ok(());
    }
    if ready.is_empty() {
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

    for node_id in ready.iter().cloned().collect::<Vec<_>>() {
        let mut next_ready = ready.clone();
        next_ready.remove(&node_id);
        for edge in graph.edges.iter().filter(|edge| edge.from == node_id) {
            let remaining = incoming.get_mut(&edge.to).ok_or_else(|| {
                LegitimacyError::InvalidEdgeReference {
                    node_id: edge.to.to_string(),
                }
            })?;
            *remaining -= 1;
            if *remaining == 0 {
                next_ready.insert(edge.to.clone());
            }
        }

        let mut next_prefix = prefix.clone();
        next_prefix.push(node_id.clone());
        enumerate_orders(graph, incoming, next_ready, next_prefix, orders)?;

        for edge in graph.edges.iter().filter(|edge| edge.from == node_id) {
            let remaining = incoming.get_mut(&edge.to).ok_or_else(|| {
                LegitimacyError::InvalidEdgeReference {
                    node_id: edge.to.to_string(),
                }
            })?;
            *remaining += 1;
        }
    }

    Ok(())
}

fn evaluate_with_order(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    order: &[NodeId],
) -> Result<OrderedTraversal, LegitimacyError> {
    validate_topological_order(graph, order)?;

    let incoming = incoming_counts(graph);
    let entry_nodes = graph
        .nodes
        .keys()
        .filter(|node_id| incoming.get(*node_id).copied().unwrap_or(0) == 0)
        .cloned()
        .collect::<Vec<_>>();
    if graph.nodes.is_empty() || entry_nodes.is_empty() {
        return Err(LegitimacyError::NoEntryNodes);
    }

    let mut queued_claims = HashMap::<NodeId, Vec<GovernanceClaim>>::new();
    for node_id in entry_nodes {
        queued_claims.insert(node_id, claims.to_vec());
    }
    let mut final_decisions = BTreeMap::<ClaimantId, Decision>::new();
    let outgoing = outgoing_edges(graph);

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

fn outgoing_edges(graph: &GovernanceGraph) -> HashMap<NodeId, Vec<GovernanceEdge>> {
    let mut outgoing = HashMap::<NodeId, Vec<GovernanceEdge>>::new();
    for edge in &graph.edges {
        outgoing
            .entry(edge.from.clone())
            .or_default()
            .push(edge.clone());
    }
    outgoing
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

fn observable_rejection(
    axiom: KernelAxiom,
    claims: &[GovernanceClaim],
    description: &str,
    original_decisions: &BTreeMap<ClaimantId, Decision>,
    perturbed_decisions: &BTreeMap<ClaimantId, Decision>,
) -> Result<AxiomVerdict, LegitimacyError> {
    Ok(AxiomVerdict::fail(
        axiom,
        description,
        Counterexample {
            description: description.to_string(),
            original_claims: convert_governance_claims(claims)?,
            original_estate: Estate::new(2.0, "binary-decision-rank")?,
            original_allocation: decision_allocation(claims, original_decisions)?,
            perturbed_claims: convert_governance_claims(claims)?,
            perturbed_estate: Estate::new(2.0, "binary-decision-rank")?,
            perturbed_allocation: decision_allocation(claims, perturbed_decisions)?,
            violation: format!(
                "{} requires claimant decisions to be invariant across legal traversal orders",
                axiom.graph_axiom_name()
            ),
        },
    ))
}

fn decision_allocation(
    claims: &[GovernanceClaim],
    decisions: &BTreeMap<ClaimantId, Decision>,
) -> Result<ValidAllocation, LegitimacyError> {
    let mut allocation = Allocation::default();
    for claim in claims {
        let decision = decisions
            .get(&claim.claimant_id)
            .cloned()
            .unwrap_or(Decision::Escalate);
        allocation.insert(claim.claimant_id.clone(), decision_rank(&decision));
    }
    ValidAllocation::new(allocation, &convert_governance_claims(claims)?)
}

fn decision_rank(decision: &Decision) -> f64 {
    match decision {
        Decision::Deny => 0.0,
        Decision::Escalate => 1.0,
        Decision::Permit => 2.0,
    }
}

fn convert_governance_claims(claims: &[GovernanceClaim]) -> Result<Vec<Claim>, LegitimacyError> {
    claims
        .iter()
        .map(|claim| {
            let mut converted = Claim::new(&claim.claimant_id, claim.strength)?;
            for (field, value) in &claim.metrics {
                converted = converted.with_metric(field, *value);
            }
            Ok(converted)
        })
        .collect()
}

fn format_order(order: &[NodeId]) -> String {
    order
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" -> ")
}

#[cfg(test)]
mod tests {
    use super::{
        all_topological_orders, check_graph_observable_determinacy, count_topological_orders_up_to,
    };
    use crate::{
        Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceGraph, GovernanceNode,
        GraphBuilder, NodeId, Verdict,
    };
    use std::collections::{BTreeMap, BTreeSet};

    #[test]
    fn exhaustive_order_enumerator_covers_more_than_legacy_sample_window() {
        let graph = independent_nodes_graph(5);
        let orders = all_topological_orders(&graph).unwrap();

        assert_eq!(orders.len(), 120);
        assert_eq!(
            orders.into_iter().collect::<BTreeSet<_>>().len(),
            120,
            "topological-order enumeration should not duplicate orders"
        );
    }

    #[test]
    fn order_counter_stops_after_feasibility_limit() {
        let graph = independent_nodes_graph(5);

        let counted = count_topological_orders_up_to(&graph, 8).unwrap();
        assert!(counted > 8);
        assert!(counted <= 120);
    }

    #[test]
    fn observable_determinacy_passes_order_independent_fixture() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(escalate_node("entry")))
            .and_then(|builder| builder.add_node(permit_node("review")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("entry").unwrap(),
                    NodeId::new("review").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();
        let claims = vec![claim("alice")];

        let verdict = check_graph_observable_determinacy(&graph, &claims).unwrap();

        assert!(matches!(
            Verdict::try_from(verdict).unwrap(),
            Verdict::Admissible { .. }
        ));
    }

    fn independent_nodes_graph(count: usize) -> GovernanceGraph {
        let mut builder = GraphBuilder::new().unwrap();
        for index in 0..count {
            builder = builder
                .add_node(permit_node(&format!("node-{index}")))
                .unwrap();
        }
        builder.build().unwrap()
    }

    fn permit_node(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: format!("{id}-permit"),
            gates: Vec::new(),
            default: Decision::Permit,
            combination: GateLogic::FirstMatch,
        }
    }

    fn escalate_node(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: format!("{id}-escalate"),
            gates: vec![Gate::ThresholdGate {
                field: "strength".to_string(),
                min: 1.0,
                decision: Decision::Escalate,
            }],
            default: Decision::Deny,
            combination: GateLogic::FirstMatch,
        }
    }

    fn claim(id: &str) -> GovernanceClaim {
        GovernanceClaim {
            claimant_id: id.to_string(),
            strength: 1.0,
            priority_class: None,
            path: None,
            action: None,
            content: None,
            metrics: BTreeMap::new(),
        }
    }
}
