use crate::{
    Allocation, Claim, ClaimantId, Counterexample, Decision, Estate, GovernanceClaim,
    GovernanceGraph, LegitimacyError, NodeId, ValidAllocation, Verdict,
    graph::{
        ClaimDecision, GovernanceEdge,
        node::{decision_rank, evaluate_node, merge_claim_batches},
        traverse::{apply_transform, forwarded_claims},
    },
};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct CycleResult {
    pub converged: bool,
    pub iterations: usize,
    pub fixed_point_decisions: BTreeMap<ClaimantId, Decision>,
}

pub fn detect_cycles(graph: &GovernanceGraph) -> Result<Vec<Vec<NodeId>>, LegitimacyError> {
    let mut state = TarjanState::default();
    let mut node_ids = graph.nodes.keys().cloned().collect::<Vec<_>>();
    node_ids.sort();
    for node_id in &node_ids {
        if !state.indices.contains_key(node_id) {
            strong_connect(node_id, graph, &mut state)?;
        }
    }

    state.cycles.sort();
    Ok(state.cycles)
}

pub fn iterate_cycle(
    graph: &GovernanceGraph,
    cycle: &[NodeId],
    claims: &[GovernanceClaim],
    max_iterations: usize,
    epsilon: f64,
) -> Result<CycleResult, LegitimacyError> {
    if cycle.is_empty() {
        return Err(LegitimacyError::invalid_input(
            "cycle iteration requires at least one node",
        ));
    }
    if max_iterations == 0 {
        return Err(LegitimacyError::invalid_input(
            "cycle iteration requires max_iterations > 0",
        ));
    }
    if !epsilon.is_finite() || epsilon < 0.0 {
        return Err(LegitimacyError::invalid_input(format!(
            "cycle iteration epsilon must be finite and non-negative, got {epsilon}"
        )));
    }

    let cycle_set = cycle.iter().cloned().collect::<BTreeSet<_>>();
    for node_id in cycle {
        if !graph.nodes.contains_key(node_id) {
            return Err(LegitimacyError::InvalidEdgeReference {
                node_id: node_id.to_string(),
            });
        }
    }

    let cycle_edges = cycle_edges(graph, &cycle_set);
    let entry_node = cycle[0].clone();
    let mut queued_claims = HashMap::from([(entry_node.clone(), claims.to_vec())]);
    let mut fixed_point_decisions = BTreeMap::<ClaimantId, Decision>::new();

    for iteration in 1..=max_iterations {
        let mut current_queued = queued_claims;
        let mut next_iteration = HashMap::<NodeId, Vec<GovernanceClaim>>::new();
        fixed_point_decisions.clear();

        for (index, node_id) in cycle.iter().enumerate() {
            let node =
                graph
                    .nodes
                    .get(node_id)
                    .ok_or_else(|| LegitimacyError::InvalidEdgeReference {
                        node_id: node_id.to_string(),
                    })?;
            let current_claims = current_queued.remove(node_id).unwrap_or_default();
            let decisions = evaluate_node(node, &current_claims)?;
            record_decisions(&mut fixed_point_decisions, &decisions);
            let forwarded = forwarded_claims(&current_claims, &decisions);

            for edge in cycle_edges.get(node_id).into_iter().flatten() {
                let transformed = apply_transform(&edge.transform, &forwarded, &decisions)?;
                let target_index = cycle
                    .iter()
                    .position(|candidate| *candidate == edge.to)
                    .ok_or_else(|| LegitimacyError::InvalidEdgeReference {
                        node_id: edge.to.to_string(),
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

        if next_iteration.is_empty() {
            return Ok(CycleResult {
                converged: true,
                iterations: iteration,
                fixed_point_decisions: fixed_point_decisions.clone(),
            });
        }

        if queue_matches_baseline(&next_iteration, &entry_node, claims, epsilon)? {
            return Ok(CycleResult {
                converged: false,
                iterations: iteration,
                fixed_point_decisions: fixed_point_decisions.clone(),
            });
        }

        queued_claims = next_iteration;
    }

    Ok(CycleResult {
        converged: false,
        iterations: max_iterations,
        fixed_point_decisions,
    })
}

pub fn check_cycle_admissibility(
    graph: &GovernanceGraph,
    cycle: &[NodeId],
    claims: &[GovernanceClaim],
) -> Result<Verdict, LegitimacyError> {
    let result = iterate_cycle(graph, cycle, claims, 32, crate::EPSILON)?;
    let fixed_point_alloc = decision_allocation(claims, &result.fixed_point_decisions)?;

    if !result.converged {
        return Ok(Verdict::Rejected {
            axiom: "cycle admissibility".to_string(),
            counterexample: Counterexample {
                description: format!(
                    "Cycle {:?} did not converge within {} iterations",
                    cycle, result.iterations
                ),
                original_claims: convert_claims(claims)?,
                original_estate: binary_estate()?,
                original_allocation: decision_allocation(claims, &BTreeMap::new())?,
                perturbed_claims: convert_claims(claims)?,
                perturbed_estate: binary_estate()?,
                perturbed_allocation: fixed_point_alloc,
                violation: "reflexive inadmissibility: the cycle kept feeding itself instead of settling to an admissible fixed point".to_string(),
            },
        });
    }

    if result
        .fixed_point_decisions
        .values()
        .any(|decision| matches!(decision, Decision::Escalate))
    {
        return Ok(Verdict::Rejected {
            axiom: "cycle admissibility".to_string(),
            counterexample: Counterexample {
                description: format!(
                    "Cycle {:?} converged to a non-terminal Escalate state",
                    cycle
                ),
                original_claims: convert_claims(claims)?,
                original_estate: binary_estate()?,
                original_allocation: decision_allocation(claims, &BTreeMap::new())?,
                perturbed_claims: convert_claims(claims)?,
                perturbed_estate: binary_estate()?,
                perturbed_allocation: fixed_point_alloc,
                violation: "reflexive inadmissibility: the cycle stabilized only by preserving non-terminal escalation inside the loop".to_string(),
            },
        });
    }

    Ok(Verdict::Admissible {
        axiom: "cycle admissibility".to_string(),
        perturbations_tested: result.iterations,
    })
}

fn cycle_edges(
    graph: &GovernanceGraph,
    cycle_set: &BTreeSet<NodeId>,
) -> HashMap<NodeId, Vec<GovernanceEdge>> {
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

fn queue_matches_baseline(
    queued_claims: &HashMap<NodeId, Vec<GovernanceClaim>>,
    entry_node: &NodeId,
    baseline_claims: &[GovernanceClaim],
    epsilon: f64,
) -> Result<bool, LegitimacyError> {
    if queued_claims.len() != 1 {
        return Ok(false);
    }

    let Some(queued_for_entry) = queued_claims.get(entry_node) else {
        return Ok(false);
    };
    if queued_for_entry.len() != baseline_claims.len() {
        return Ok(false);
    }

    let baseline = claims_by_id(baseline_claims);
    let observed = claims_by_id(queued_for_entry);
    if baseline.keys().collect::<BTreeSet<_>>() != observed.keys().collect::<BTreeSet<_>>() {
        return Ok(false);
    }

    for claimant_id in baseline.keys() {
        let left = baseline.get(claimant_id).ok_or_else(|| {
            LegitimacyError::missing_allocation_share(claimant_id.clone(), "cycle baseline queue")
        })?;
        let right = observed.get(claimant_id).ok_or_else(|| {
            LegitimacyError::missing_allocation_share(claimant_id.clone(), "cycle observed queue")
        })?;
        if !claims_within_epsilon(left, right, epsilon) {
            return Ok(false);
        }
    }

    Ok(true)
}

fn claims_within_epsilon(left: &GovernanceClaim, right: &GovernanceClaim, epsilon: f64) -> bool {
    left.claimant_id == right.claimant_id
        && left.priority_class == right.priority_class
        && left.path == right.path
        && left.action == right.action
        && left.content == right.content
        && (left.strength - right.strength).abs() <= epsilon
        && metrics_within_epsilon(&left.metrics, &right.metrics, epsilon)
}

fn metrics_within_epsilon(
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

fn claims_by_id(claims: &[GovernanceClaim]) -> BTreeMap<ClaimantId, GovernanceClaim> {
    claims
        .iter()
        .cloned()
        .map(|claim| (claim.claimant_id.clone(), claim))
        .collect()
}

fn record_decisions(
    fixed_point_decisions: &mut BTreeMap<ClaimantId, Decision>,
    decisions: &[ClaimDecision],
) {
    for decision in decisions {
        fixed_point_decisions.insert(decision.claimant_id.clone(), decision.decision.clone());
    }
}

fn convert_claims(claims: &[GovernanceClaim]) -> Result<Vec<Claim>, LegitimacyError> {
    claims
        .iter()
        .map(|claim| {
            let mut converted = Claim::new(claim.claimant_id.clone(), claim.strength)?;
            converted.metrics = claim.metrics.clone();
            Ok(converted)
        })
        .collect()
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
        allocation.insert(
            claim.claimant_id.clone(),
            f64::from(decision_rank(&decision)),
        );
    }
    ValidAllocation::new(allocation, &convert_claims(claims)?)
}

fn binary_estate() -> Result<Estate, LegitimacyError> {
    Estate::new(2.0, "binary-decision-rank")
}

#[derive(Default)]
struct TarjanState {
    index: usize,
    stack: Vec<NodeId>,
    on_stack: HashMap<NodeId, bool>,
    indices: HashMap<NodeId, usize>,
    lowlinks: HashMap<NodeId, usize>,
    cycles: Vec<Vec<NodeId>>,
}

fn strong_connect(
    node_id: &NodeId,
    graph: &GovernanceGraph,
    state: &mut TarjanState,
) -> Result<(), LegitimacyError> {
    state.indices.insert(node_id.clone(), state.index);
    state.lowlinks.insert(node_id.clone(), state.index);
    state.index += 1;
    state.stack.push(node_id.clone());
    state.on_stack.insert(node_id.clone(), true);

    let mut successors = graph
        .edges
        .iter()
        .filter(|edge| edge.from == *node_id)
        .map(|edge| edge.to.clone())
        .collect::<Vec<_>>();
    successors.sort();

    for successor in successors {
        if !state.indices.contains_key(&successor) {
            strong_connect(&successor, graph, state)?;
            let successor_lowlink = state.lowlinks.get(&successor).copied().ok_or_else(|| {
                LegitimacyError::InvalidEdgeReference {
                    node_id: successor.to_string(),
                }
            })?;
            let node_lowlink = state.lowlinks.get(node_id).copied().ok_or_else(|| {
                LegitimacyError::InvalidEdgeReference {
                    node_id: node_id.to_string(),
                }
            })?;
            state
                .lowlinks
                .insert(node_id.clone(), node_lowlink.min(successor_lowlink));
        } else if state.on_stack.get(&successor).copied().unwrap_or(false) {
            let successor_index = state.indices.get(&successor).copied().ok_or_else(|| {
                LegitimacyError::InvalidEdgeReference {
                    node_id: successor.to_string(),
                }
            })?;
            let node_lowlink = state.lowlinks.get(node_id).copied().ok_or_else(|| {
                LegitimacyError::InvalidEdgeReference {
                    node_id: node_id.to_string(),
                }
            })?;
            state
                .lowlinks
                .insert(node_id.clone(), node_lowlink.min(successor_index));
        }
    }

    if state.lowlinks.get(node_id) == state.indices.get(node_id) {
        let mut component = Vec::new();
        while let Some(stack_node) = state.stack.pop() {
            state.on_stack.insert(stack_node.clone(), false);
            component.push(stack_node.clone());
            if stack_node == *node_id {
                break;
            }
        }

        if component.len() > 1 || has_self_loop(node_id, graph) {
            // Tarjan component discovery order depends on traversal order; normalize
            // cycles lexicographically before any caller uses the "first" cycle.
            component.sort();
            state.cycles.push(component);
        }
    }

    Ok(())
}

fn has_self_loop(node_id: &NodeId, graph: &GovernanceGraph) -> bool {
    graph
        .edges
        .iter()
        .any(|edge| edge.from == *node_id && edge.to == *node_id)
}

#[cfg(test)]
mod tests {
    use super::{check_cycle_admissibility, detect_cycles, iterate_cycle};
    use crate::{
        Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceNode, GraphBuilder,
        NodeId, Verdict,
    };
    use std::collections::BTreeMap;

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
    fn iterate_cycle_reports_reflexive_non_convergence() {
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

        let cycle = vec![NodeId::new("a").unwrap(), NodeId::new("b").unwrap()];
        let result =
            iterate_cycle(&graph, &cycle, &[claim("alice", 1.0)], 4, crate::EPSILON).unwrap();

        assert!(!result.converged);
        assert_eq!(result.iterations, 1);
    }

    #[test]
    fn iterate_cycle_drops_terminal_snapshot_when_permits_do_not_forward() {
        let graph = trust_escalation_graph();
        let cycle = vec![
            NodeId::new("threshold").unwrap(),
            NodeId::new("peer").unwrap(),
        ];
        let result = iterate_cycle(&graph, &cycle, &trust_claims(), 4, crate::EPSILON).unwrap();

        assert!(!result.converged);
        assert_eq!(result.iterations, 4);
        assert!(result.fixed_point_decisions.is_empty());
    }

    #[test]
    fn cycle_admissibility_rejects_non_convergent_feedback_loop() {
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

        let cycle = vec![NodeId::new("a").unwrap(), NodeId::new("b").unwrap()];
        let verdict = check_cycle_admissibility(&graph, &cycle, &[claim("alice", 1.0)]).unwrap();

        assert!(matches!(verdict, Verdict::Rejected { .. }));
    }

    #[test]
    fn cycle_admissibility_still_rejects_inert_trust_escalation_cycle() {
        let graph = trust_escalation_graph();
        let cycle = vec![
            NodeId::new("threshold").unwrap(),
            NodeId::new("peer").unwrap(),
        ];
        let verdict = check_cycle_admissibility(&graph, &cycle, &trust_claims()).unwrap();

        match verdict {
            Verdict::Rejected {
                axiom,
                counterexample,
            } => {
                assert_eq!(axiom, "cycle admissibility");
                assert!(
                    counterexample
                        .violation
                        .contains("reflexive inadmissibility")
                );
                assert!(counterexample.description.contains("did not converge"));
            }
            Verdict::Admissible { .. } => {
                panic!("trust-escalation cycle should remain reflexively inadmissible")
            }
        }
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

    fn claim(claimant_id: &str, strength: f64) -> GovernanceClaim {
        GovernanceClaim {
            claimant_id: claimant_id.to_string(),
            strength,
            priority_class: None,
            path: None,
            action: None,
            content: None,
            metrics: BTreeMap::new(),
        }
    }

    fn trust_escalation_graph() -> crate::GovernanceGraph {
        GraphBuilder::new()
            .and_then(|builder| builder.add_node(threshold_node("threshold")))
            .and_then(|builder| builder.add_node(peer_relative_node("peer")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("threshold").unwrap(),
                    NodeId::new("peer").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("peer").unwrap(),
                    NodeId::new("threshold").unwrap(),
                    EdgeTransform::ClaimModification { delta: 0.1 },
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap()
    }

    fn trust_claims() -> Vec<GovernanceClaim> {
        vec![claim("alice", 0.4), claim("bob", 0.55), claim("carol", 0.9)]
    }

    fn threshold_node(id: &str) -> GovernanceNode {
        GovernanceNode::Threshold {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            threshold: 0.5,
            field: "strength".to_string(),
        }
    }

    fn peer_relative_node(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: vec![Gate::PeerRelative {
                field: "strength".to_string(),
                percentile: 1.0,
                decision: Decision::Permit,
            }],
            default: Decision::Deny,
            combination: GateLogic::AnyMustPass,
        }
    }
}
