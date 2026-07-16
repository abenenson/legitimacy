use crate::{Gate, GovernanceGraph, GovernanceNode};

pub fn is_non_peer_relative(graph: &GovernanceGraph) -> bool {
    graph.nodes.values().all(node_is_non_peer_relative)
}

pub fn is_threshold_structured(graph: &GovernanceGraph) -> bool {
    graph.nodes.values().all(node_is_threshold_structured)
}

pub fn is_claimant_constant(graph: &GovernanceGraph) -> bool {
    graph.nodes.values().all(node_is_claimant_constant)
}

fn node_is_non_peer_relative(node: &GovernanceNode) -> bool {
    match node {
        GovernanceNode::Binary { gates, .. } => gates
            .iter()
            .all(|gate| !matches!(gate, Gate::PeerRelative { .. })),
        GovernanceNode::Threshold { .. } => true,
        GovernanceNode::Proportional { .. } => false,
    }
}

fn node_is_threshold_structured(node: &GovernanceNode) -> bool {
    match node {
        GovernanceNode::Binary { gates, .. } => gates
            .iter()
            .all(|gate| matches!(gate, Gate::ThresholdGate { field, .. } if field == "strength")),
        GovernanceNode::Threshold { field, .. } => field == "strength",
        GovernanceNode::Proportional { .. } => false,
    }
}

fn node_is_claimant_constant(node: &GovernanceNode) -> bool {
    match node {
        GovernanceNode::Binary { gates, default, .. } => {
            gates.iter().all(|gate| gate_decision(gate) == default)
        }
        GovernanceNode::Threshold { .. } => false,
        GovernanceNode::Proportional { .. } => false,
    }
}

fn gate_decision(gate: &Gate) -> &crate::Decision {
    match gate {
        Gate::PrefixMatch { decision, .. }
        | Gate::ExactMatch { decision, .. }
        | Gate::ContentMatch { decision, .. }
        | Gate::ThresholdGate { decision, .. }
        | Gate::PeerRelative { decision, .. } => decision,
    }
}

#[cfg(test)]
mod tests {
    use super::{is_claimant_constant, is_non_peer_relative, is_threshold_structured};
    use crate::{Decision, EdgeTransform, Gate, GateLogic, GovernanceNode, GraphBuilder, NodeId};

    #[test]
    fn peer_relative_graph_is_not_non_peer_relative() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(threshold_node("entry")))
            .and_then(|builder| builder.add_node(peer_relative_node("peer")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("entry").unwrap(),
                    NodeId::new("peer").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();

        assert!(!is_non_peer_relative(&graph));
        assert!(!is_threshold_structured(&graph));
    }

    #[test]
    fn threshold_only_graph_is_threshold_structured() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(threshold_node("entry")))
            .and_then(GraphBuilder::build)
            .unwrap();

        assert!(is_non_peer_relative(&graph));
        assert!(is_threshold_structured(&graph));
        assert!(!is_claimant_constant(&graph));
    }

    #[test]
    fn constant_decision_graph_is_claimant_constant() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(constant_node("entry", Decision::Permit)))
            .and_then(GraphBuilder::build)
            .unwrap();

        assert!(is_non_peer_relative(&graph));
        assert!(is_claimant_constant(&graph));
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
                percentile: 0.5,
                decision: Decision::Permit,
            }],
            default: Decision::Deny,
            combination: GateLogic::AnyMustPass,
        }
    }

    fn constant_node(id: &str, decision: Decision) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: Vec::new(),
            default: decision,
            combination: GateLogic::FirstMatch,
        }
    }
}
