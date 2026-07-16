use crate::{
    EdgeTransform, GovernanceEdge, GovernanceGraph, GovernanceNode, LegitimacyError, NodeId,
    graph::node::{node_id, validate_governance_node},
};
use std::collections::BTreeMap;

#[derive(Clone, Debug, Default)]
pub struct GraphBuilder {
    nodes: BTreeMap<NodeId, GovernanceNode>,
    edges: Vec<GovernanceEdge>,
}

impl GraphBuilder {
    pub fn new() -> Result<Self, LegitimacyError> {
        Ok(Self::default())
    }

    pub fn add_node(mut self, node: GovernanceNode) -> Result<Self, LegitimacyError> {
        validate_governance_node(&node)?;
        let id = node_id(&node).clone();
        if self.nodes.contains_key(&id) {
            return Err(LegitimacyError::DuplicateNodeId {
                node_id: id.to_string(),
            });
        }

        self.nodes.insert(id, node);
        Ok(self)
    }

    pub fn add_edge(
        mut self,
        from: NodeId,
        to: NodeId,
        transform: EdgeTransform,
    ) -> Result<Self, LegitimacyError> {
        self.edges.push(GovernanceEdge::new(from, to, transform)?);
        Ok(self)
    }

    pub fn build(self) -> Result<GovernanceGraph, LegitimacyError> {
        for edge in &self.edges {
            if !self.nodes.contains_key(&edge.from) {
                return Err(LegitimacyError::InvalidEdgeReference {
                    node_id: edge.from.to_string(),
                });
            }
            if !self.nodes.contains_key(&edge.to) {
                return Err(LegitimacyError::InvalidEdgeReference {
                    node_id: edge.to.to_string(),
                });
            }
        }

        Ok(GovernanceGraph {
            nodes: self.nodes,
            edges: self.edges,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::GraphBuilder;
    use crate::{Decision, EdgeTransform, GateLogic, GovernanceNode, LegitimacyError, NodeId};

    #[test]
    fn builder_rejects_duplicate_node_ids() {
        let node = binary_node("root");

        let result = GraphBuilder::new()
            .and_then(|builder| builder.add_node(node.clone()))
            .and_then(|builder| builder.add_node(node));

        assert!(matches!(
            result,
            Err(LegitimacyError::DuplicateNodeId { .. })
        ));
    }

    #[test]
    fn builder_rejects_missing_edge_endpoints() {
        let result = GraphBuilder::new()
            .and_then(|builder| builder.add_node(binary_node("root")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("root").unwrap(),
                    NodeId::new("missing").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build);

        assert!(matches!(
            result,
            Err(LegitimacyError::InvalidEdgeReference { .. })
        ));
    }

    fn binary_node(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: Vec::new(),
            default: Decision::Permit,
            combination: GateLogic::FirstMatch,
        }
    }
}
