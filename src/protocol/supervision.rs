use super::{
    formats::GovernanceDeclaration,
    state::{
        ProtocolError, ProtocolState, SupervisoryAction, SupervisoryIntervention,
        canonical_graph_hash,
    },
    transitions::iso8601_timestamp,
};
use crate::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceEdge, GovernanceGraph, GovernanceNode,
    NodeId,
};
use serde::Deserialize;
use std::collections::{BTreeSet, HashMap};

const DEFAULT_DEGRADATION_FACTOR: f64 = 1.5;
const REROUTE_NODE_ID: &str = "__supervision_reroute__";

#[derive(Debug, Default, Deserialize)]
struct SupervisoryDirective {
    #[serde(default)]
    sandbox_nodes: Vec<String>,
    #[serde(default)]
    degradation_factor: Option<f64>,
    #[serde(default)]
    reroute_to: Vec<String>,
}

pub fn supervise(
    live: ProtocolState,
    action: SupervisoryAction,
    reason: Option<String>,
) -> Result<ProtocolState, ProtocolError> {
    live.validate()?;
    let (monitor_session, ledger, declaration, mut overlay_graph) = match live {
        ProtocolState::Live {
            monitor_session,
            ledger,
            declaration,
        } => {
            let overlay_graph = monitor_session.compiled_graph.graph.clone();
            (monitor_session, ledger, declaration, overlay_graph)
        }
        ProtocolState::Supervised {
            intervention,
            monitor_session,
            ledger,
            declaration,
        } => (
            monitor_session,
            ledger,
            declaration,
            intervention.overlay_graph,
        ),
        other => {
            return Err(ProtocolError::InvalidStateTransition {
                expected: "live|supervised",
                actual: other.name(),
            });
        }
    };

    let directive = parse_directive(reason.as_deref())?;
    apply_supervisory_action(&mut overlay_graph, &declaration, action, &directive)?;
    let overlay_graph_hash = canonical_graph_hash(&overlay_graph)?;

    let state = ProtocolState::Supervised {
        intervention: SupervisoryIntervention {
            action,
            postcondition: action.postcondition(),
            issued_at: iso8601_timestamp()?,
            overlay_graph,
            overlay_graph_hash,
            reason,
        },
        monitor_session,
        ledger,
        declaration,
    };
    state.validate()?;
    Ok(state)
}

fn parse_directive(reason: Option<&str>) -> Result<SupervisoryDirective, ProtocolError> {
    reason
        .and_then(|value| value.trim_start().starts_with('{').then_some(value))
        .map(|value| {
            serde_json::from_str(value).map_err(|error| {
                ProtocolError::MalformedSupervisoryDirectiveJson {
                    reason: error.to_string(),
                }
            })
        })
        .transpose()
        .map(|directive| directive.unwrap_or_default())
}

fn apply_supervisory_action(
    graph: &mut GovernanceGraph,
    declaration: &GovernanceDeclaration,
    action: SupervisoryAction,
    directive: &SupervisoryDirective,
) -> Result<(), ProtocolError> {
    match action {
        SupervisoryAction::Pause => rewrite_as_constant(graph, Decision::Escalate),
        SupervisoryAction::Deny | SupervisoryAction::Stop => {
            rewrite_as_constant(graph, Decision::Deny)
        }
        SupervisoryAction::Sandbox => sandbox_graph(graph, directive)?,
        SupervisoryAction::Degrade => degrade_graph(graph, directive),
        SupervisoryAction::Rollback => {
            *graph = declaration.graph.clone();
        }
        SupervisoryAction::Reroute => reroute_graph(graph, directive)?,
    }
    Ok(())
}

fn rewrite_as_constant(graph: &mut GovernanceGraph, decision: Decision) {
    for node in graph.nodes.values_mut() {
        let (id, name) = node_identity(node);
        *node = GovernanceNode::Binary {
            id,
            name,
            gates: Vec::new(),
            default: decision.clone(),
            combination: GateLogic::FirstMatch,
        };
    }
}

fn sandbox_graph(
    graph: &mut GovernanceGraph,
    directive: &SupervisoryDirective,
) -> Result<(), ProtocolError> {
    let mut allowed = parse_existing_node_ids(graph, &directive.sandbox_nodes, "sandbox_nodes")?;
    if allowed.is_empty() {
        allowed = entry_nodes(graph).into_iter().collect();
    }

    graph.nodes.retain(|node_id, _| allowed.contains(node_id));
    graph
        .edges
        .retain(|edge| allowed.contains(&edge.from) && allowed.contains(&edge.to));
    Ok(())
}

fn degrade_graph(graph: &mut GovernanceGraph, directive: &SupervisoryDirective) {
    let factor = directive
        .degradation_factor
        .filter(|factor| factor.is_finite() && *factor > 0.0)
        .unwrap_or(DEFAULT_DEGRADATION_FACTOR);

    for node in graph.nodes.values_mut() {
        match node {
            GovernanceNode::Binary { gates, .. } => {
                for gate in gates {
                    if let Gate::ThresholdGate { min, .. } = gate {
                        *min *= factor;
                    }
                }
            }
            GovernanceNode::Threshold { threshold, .. } => *threshold *= factor,
            GovernanceNode::Proportional { .. } => {}
        }
    }
}

fn reroute_graph(
    graph: &mut GovernanceGraph,
    directive: &SupervisoryDirective,
) -> Result<(), ProtocolError> {
    let current_entries = entry_nodes(graph);
    let mut targets = parse_existing_node_ids(graph, &directive.reroute_to, "reroute_to")?
        .into_iter()
        .filter(|node_id| !current_entries.contains(node_id))
        .collect::<BTreeSet<_>>();
    if targets.is_empty() {
        targets = downstream_targets(graph, &current_entries);
    }
    if targets.is_empty() {
        targets = graph
            .nodes
            .keys()
            .filter(|node_id| !current_entries.contains(node_id))
            .cloned()
            .collect();
    }
    if targets.is_empty() {
        rewrite_as_constant(graph, Decision::Deny);
        return Ok(());
    }

    graph
        .nodes
        .retain(|node_id, _| !current_entries.contains(node_id));
    graph.edges.retain(|edge| {
        !current_entries.contains(&edge.from) && !current_entries.contains(&edge.to)
    });

    let reroute_id = next_available_node_id(graph, REROUTE_NODE_ID)?;
    graph.nodes.insert(
        reroute_id.clone(),
        GovernanceNode::Binary {
            id: reroute_id.clone(),
            name: "supervision-reroute".to_string(),
            gates: Vec::new(),
            default: Decision::Escalate,
            combination: GateLogic::FirstMatch,
        },
    );
    graph
        .edges
        .extend(targets.into_iter().map(|target| GovernanceEdge {
            from: reroute_id.clone(),
            to: target,
            transform: EdgeTransform::PassThrough,
        }));

    Ok(())
}

fn entry_nodes(graph: &GovernanceGraph) -> Vec<NodeId> {
    let mut incoming = HashMap::<NodeId, usize>::new();
    for node_id in graph.nodes.keys() {
        incoming.insert(node_id.clone(), 0);
    }
    for edge in &graph.edges {
        *incoming.entry(edge.to.clone()).or_insert(0) += 1;
    }

    let mut entries = graph
        .nodes
        .keys()
        .filter(|node_id| incoming.get(*node_id).copied().unwrap_or(0) == 0)
        .cloned()
        .collect::<Vec<_>>();
    entries.sort();
    entries
}

fn downstream_targets(graph: &GovernanceGraph, entries: &[NodeId]) -> BTreeSet<NodeId> {
    graph
        .edges
        .iter()
        .filter(|edge| entries.contains(&edge.from) && !entries.contains(&edge.to))
        .map(|edge| edge.to.clone())
        .collect()
}

fn parse_existing_node_ids(
    graph: &GovernanceGraph,
    raw_ids: &[String],
    field: &'static str,
) -> Result<BTreeSet<NodeId>, ProtocolError> {
    raw_ids
        .iter()
        .map(|raw| {
            let node_id = NodeId::new(raw).map_err(|error| {
                ProtocolError::MalformedSupervisoryDirectiveNodeId {
                    field,
                    node_id: raw.clone(),
                    reason: error.to_string(),
                }
            })?;
            if !graph.nodes.contains_key(&node_id) {
                return Err(ProtocolError::UnknownSupervisoryDirectiveNodeId {
                    field,
                    node_id: node_id.to_string(),
                });
            }
            Ok(node_id)
        })
        .collect()
}

fn next_available_node_id(graph: &GovernanceGraph, base: &str) -> Result<NodeId, ProtocolError> {
    for suffix in 0.. {
        let candidate = if suffix == 0 {
            base.to_string()
        } else {
            format!("{base}_{suffix}")
        };
        let node_id = NodeId::new(candidate)?;
        if !graph.nodes.contains_key(&node_id) {
            return Ok(node_id);
        }
    }

    // SAFETY: the loop ranges over every usize suffix and returns as soon as it
    // finds a node id absent from the finite graph.
    unreachable!("unbounded reroute id search should always terminate")
}

fn node_identity(node: &GovernanceNode) -> (NodeId, String) {
    match node {
        GovernanceNode::Binary { id, name, .. }
        | GovernanceNode::Proportional { id, name, .. }
        | GovernanceNode::Threshold { id, name, .. } => (id.clone(), name.clone()),
    }
}

#[cfg(test)]
mod tests {
    use super::supervise;
    use crate::protocol::{
        MonitorConfig, ProtocolError, ProtocolState, SupervisoryAction, activate, compile, declare,
        measure,
    };
    use crate::{Decision, EdgeTransform, GateLogic, GovernanceNode, GraphBuilder, NodeId};

    #[test]
    fn supervise_rejects_malformed_directive_json() {
        let live = live_protocol_state();
        let error = supervise(
            live,
            SupervisoryAction::Sandbox,
            Some("{not-json".to_string()),
        )
        .unwrap_err();

        assert!(matches!(
            error,
            ProtocolError::MalformedSupervisoryDirectiveJson { .. }
        ));
    }

    #[test]
    fn supervise_rejects_unknown_sandbox_node_ids() {
        let live = live_protocol_state();
        let error = supervise(
            live,
            SupervisoryAction::Sandbox,
            Some(r#"{"sandbox_nodes":["missing"]}"#.to_string()),
        )
        .unwrap_err();

        assert!(matches!(
            error,
            ProtocolError::UnknownSupervisoryDirectiveNodeId {
                field: "sandbox_nodes",
                ..
            }
        ));
    }

    #[test]
    fn supervise_rejects_malformed_reroute_node_ids() {
        let live = live_protocol_state();
        let error = supervise(
            live,
            SupervisoryAction::Reroute,
            Some(r#"{"reroute_to":[" "]}"#.to_string()),
        )
        .unwrap_err();

        assert!(matches!(
            error,
            ProtocolError::MalformedSupervisoryDirectiveNodeId {
                field: "reroute_to",
                ..
            }
        ));
    }

    fn live_protocol_state() -> ProtocolState {
        let graph = GraphBuilder::new()
            .and_then(|builder| {
                builder.add_node(GovernanceNode::Binary {
                    id: NodeId::new("entry").unwrap(),
                    name: "entry".to_string(),
                    gates: Vec::new(),
                    default: Decision::Escalate,
                    combination: GateLogic::FirstMatch,
                })
            })
            .and_then(|builder| {
                builder.add_node(GovernanceNode::Binary {
                    id: NodeId::new("terminal").unwrap(),
                    name: "terminal".to_string(),
                    gates: Vec::new(),
                    default: Decision::Permit,
                    combination: GateLogic::FirstMatch,
                })
            })
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("entry").unwrap(),
                    NodeId::new("terminal").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();

        let declared = declare(graph, Vec::new()).unwrap();
        let compiled = compile(declared).unwrap();
        let measured = measure(compiled, Vec::new()).unwrap();
        activate(
            measured,
            MonitorConfig {
                min_interval_seconds: 60,
                max_interval_seconds: 120,
                seed: 0,
            },
        )
        .unwrap()
    }
}
