use crate::{
    Decision, EdgeTransform, GateLogic, GovernanceGraph, GovernanceNode, GraphBuilder,
    LegitimacyError, NodeId,
    spectral::{Rational, SignalSignature},
};

pub fn uni_tri_graph() -> GovernanceGraph {
    triangle_graph(
        ("0", "1", EdgeTransform::PassThrough),
        ("0", "2", EdgeTransform::PassThrough),
        ("1", "2", EdgeTransform::PassThrough),
    )
}

pub fn asym_tri_graph() -> GovernanceGraph {
    triangle_graph(
        ("0", "1", EdgeTransform::PassThrough),
        ("0", "2", EdgeTransform::PassThrough),
        ("1", "2", EdgeTransform::ClaimModification { delta: 2.0 }),
    )
}

pub fn near_path_graph() -> GovernanceGraph {
    triangle_graph(
        ("0", "1", EdgeTransform::PassThrough),
        (
            "0",
            "2",
            EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
        ),
        ("1", "2", EdgeTransform::PassThrough),
    )
}

pub fn strongly_connected_graph() -> GovernanceGraph {
    triangle_graph(
        ("0", "1", EdgeTransform::ClaimModification { delta: 10.0 }),
        ("0", "2", EdgeTransform::ClaimModification { delta: 10.0 }),
        ("1", "2", EdgeTransform::ClaimModification { delta: 10.0 }),
    )
}

pub fn bottleneck_graph() -> GovernanceGraph {
    triangle_graph(
        ("0", "1", EdgeTransform::PassThrough),
        (
            "0",
            "2",
            EdgeTransform::ClaimModification {
                delta: 1.0 / 10_000.0,
            },
        ),
        ("1", "2", EdgeTransform::PassThrough),
    )
}

pub fn five_graph_lattice() -> [GovernanceGraph; 5] {
    [
        uni_tri_graph(),
        asym_tri_graph(),
        near_path_graph(),
        strongly_connected_graph(),
        bottleneck_graph(),
    ]
}

pub fn uni_k5() -> GovernanceGraph {
    complete_graph(5, &[("0", "1", EdgeTransform::PassThrough)])
}

pub fn asym_k5() -> GovernanceGraph {
    complete_graph(
        5,
        &[("0", "1", EdgeTransform::ClaimModification { delta: 2.0 })],
    )
}

pub fn near_path5() -> GovernanceGraph {
    five_node_graph(&[
        ("0", "1", EdgeTransform::PassThrough),
        (
            "0",
            "2",
            EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
        ),
        (
            "0",
            "3",
            EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
        ),
        (
            "0",
            "4",
            EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
        ),
        ("1", "2", EdgeTransform::PassThrough),
        (
            "1",
            "3",
            EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
        ),
        (
            "1",
            "4",
            EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
        ),
        ("2", "3", EdgeTransform::PassThrough),
        (
            "2",
            "4",
            EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
        ),
        ("3", "4", EdgeTransform::PassThrough),
    ])
}

pub fn bottleneck5() -> GovernanceGraph {
    five_node_graph(&[
        ("0", "1", EdgeTransform::PassThrough),
        (
            "0",
            "2",
            EdgeTransform::ClaimModification {
                delta: 1.0 / 10_000.0,
            },
        ),
        (
            "1",
            "2",
            EdgeTransform::ClaimModification {
                delta: 1.0 / 10_000.0,
            },
        ),
        (
            "2",
            "3",
            EdgeTransform::ClaimModification {
                delta: 1.0 / 10_000.0,
            },
        ),
        (
            "2",
            "4",
            EdgeTransform::ClaimModification {
                delta: 1.0 / 10_000.0,
            },
        ),
        ("3", "4", EdgeTransform::PassThrough),
    ])
}

pub fn wheel5() -> GovernanceGraph {
    five_node_graph(&[
        ("0", "1", EdgeTransform::PassThrough),
        ("0", "2", EdgeTransform::PassThrough),
        ("0", "3", EdgeTransform::PassThrough),
        ("0", "4", EdgeTransform::PassThrough),
        (
            "1",
            "2",
            EdgeTransform::ClaimModification { delta: 1.0 / 10.0 },
        ),
        (
            "2",
            "3",
            EdgeTransform::ClaimModification { delta: 1.0 / 10.0 },
        ),
        (
            "3",
            "4",
            EdgeTransform::ClaimModification { delta: 1.0 / 10.0 },
        ),
        (
            "1",
            "4",
            EdgeTransform::ClaimModification { delta: 1.0 / 10.0 },
        ),
    ])
}

pub fn five_node_lattice() -> [GovernanceGraph; 5] {
    [uni_k5(), asym_k5(), near_path5(), bottleneck5(), wheel5()]
}

pub fn uni_k7() -> GovernanceGraph {
    complete_graph(7, &[])
}

pub fn asym_k7() -> GovernanceGraph {
    complete_graph(
        7,
        &[("0", "1", EdgeTransform::ClaimModification { delta: 2.0 })],
    )
}

pub fn near_path7() -> GovernanceGraph {
    node_graph(
        7,
        &[
            ("0", "1", EdgeTransform::PassThrough),
            (
                "0",
                "2",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            (
                "0",
                "3",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            (
                "0",
                "4",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            (
                "0",
                "5",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            (
                "0",
                "6",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            ("1", "2", EdgeTransform::PassThrough),
            (
                "1",
                "3",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            (
                "1",
                "4",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            (
                "1",
                "5",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            (
                "1",
                "6",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            ("2", "3", EdgeTransform::PassThrough),
            (
                "2",
                "4",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            (
                "2",
                "5",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            (
                "2",
                "6",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            ("3", "4", EdgeTransform::PassThrough),
            (
                "3",
                "5",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            (
                "3",
                "6",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            ("4", "5", EdgeTransform::PassThrough),
            (
                "4",
                "6",
                EdgeTransform::ClaimModification { delta: 1.0 / 50.0 },
            ),
            ("5", "6", EdgeTransform::PassThrough),
        ],
    )
}

pub fn bottleneck7_bi() -> GovernanceGraph {
    node_graph(
        7,
        &[
            ("0", "1", EdgeTransform::PassThrough),
            ("0", "2", EdgeTransform::PassThrough),
            (
                "0",
                "3",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "0",
                "4",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "0",
                "5",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "0",
                "6",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            ("1", "2", EdgeTransform::PassThrough),
            (
                "1",
                "3",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "1",
                "4",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "1",
                "5",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "1",
                "6",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "2",
                "3",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "2",
                "4",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "2",
                "5",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "2",
                "6",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            ("3", "4", EdgeTransform::PassThrough),
            ("3", "5", EdgeTransform::PassThrough),
            ("3", "6", EdgeTransform::PassThrough),
            ("4", "5", EdgeTransform::PassThrough),
            ("4", "6", EdgeTransform::PassThrough),
            ("5", "6", EdgeTransform::PassThrough),
        ],
    )
}

pub fn bottleneck7_tri() -> GovernanceGraph {
    node_graph(
        7,
        &[
            ("0", "1", EdgeTransform::PassThrough),
            ("0", "2", EdgeTransform::PassThrough),
            (
                "0",
                "3",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "0",
                "4",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "0",
                "5",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "0",
                "6",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            ("1", "2", EdgeTransform::PassThrough),
            (
                "1",
                "3",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "1",
                "4",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "1",
                "5",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "1",
                "6",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "2",
                "3",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "2",
                "4",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "2",
                "5",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "2",
                "6",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            ("3", "4", EdgeTransform::PassThrough),
            (
                "3",
                "5",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "3",
                "6",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "4",
                "5",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            (
                "4",
                "6",
                EdgeTransform::ClaimModification {
                    delta: 1.0 / 70_000.0,
                },
            ),
            ("5", "6", EdgeTransform::PassThrough),
        ],
    )
}

pub fn hub_spoke_hierarchy7() -> GovernanceGraph {
    node_graph(
        7,
        &[
            ("0", "1", EdgeTransform::PassThrough),
            ("0", "2", EdgeTransform::PassThrough),
            ("0", "3", EdgeTransform::PassThrough),
            ("0", "4", EdgeTransform::PassThrough),
            (
                "1",
                "5",
                EdgeTransform::ClaimModification { delta: 1.0 / 10.0 },
            ),
            (
                "1",
                "6",
                EdgeTransform::ClaimModification { delta: 1.0 / 10.0 },
            ),
        ],
    )
}

pub fn nested_hierarchy7() -> GovernanceGraph {
    node_graph(
        7,
        &[
            ("0", "1", EdgeTransform::PassThrough),
            ("0", "2", EdgeTransform::PassThrough),
            (
                "0",
                "3",
                EdgeTransform::ClaimModification { delta: 1.0 / 5.0 },
            ),
            (
                "0",
                "4",
                EdgeTransform::ClaimModification { delta: 1.0 / 5.0 },
            ),
            ("1", "2", EdgeTransform::PassThrough),
            (
                "1",
                "3",
                EdgeTransform::ClaimModification { delta: 1.0 / 5.0 },
            ),
            (
                "1",
                "4",
                EdgeTransform::ClaimModification { delta: 1.0 / 5.0 },
            ),
            (
                "2",
                "3",
                EdgeTransform::ClaimModification { delta: 1.0 / 5.0 },
            ),
            (
                "2",
                "4",
                EdgeTransform::ClaimModification { delta: 1.0 / 5.0 },
            ),
            (
                "3",
                "4",
                EdgeTransform::ClaimModification { delta: 1.0 / 2.0 },
            ),
            (
                "3",
                "5",
                EdgeTransform::ClaimModification { delta: 1.0 / 20.0 },
            ),
            (
                "3",
                "6",
                EdgeTransform::ClaimModification { delta: 1.0 / 20.0 },
            ),
            (
                "4",
                "5",
                EdgeTransform::ClaimModification { delta: 1.0 / 20.0 },
            ),
            (
                "4",
                "6",
                EdgeTransform::ClaimModification { delta: 1.0 / 20.0 },
            ),
        ],
    )
}

pub fn seven_node_lattice() -> [GovernanceGraph; 7] {
    [
        uni_k7(),
        asym_k7(),
        near_path7(),
        bottleneck7_bi(),
        bottleneck7_tri(),
        hub_spoke_hierarchy7(),
        nested_hierarchy7(),
    ]
}

pub fn signal_signature() -> SignalSignature {
    vec![
        Rational::from_integer(1),
        Rational::from_integer(2),
        Rational::from_integer(3),
    ]
}

pub fn signal_signature5() -> SignalSignature {
    vec![
        Rational::from_integer(1),
        Rational::from_integer(2),
        Rational::from_integer(3),
        Rational::from_integer(4),
        Rational::from_integer(5),
    ]
}

pub fn signal_signature7() -> SignalSignature {
    vec![
        Rational::from_integer(1),
        Rational::from_integer(2),
        Rational::from_integer(3),
        Rational::from_integer(4),
        Rational::from_integer(5),
        Rational::from_integer(6),
        Rational::from_integer(7),
    ]
}

fn triangle_graph(
    first: (&str, &str, EdgeTransform),
    second: (&str, &str, EdgeTransform),
    third: (&str, &str, EdgeTransform),
) -> GovernanceGraph {
    // SAFETY: triangle fixtures use the fixed ids 0, 1, and 2 plus finite
    // edge transforms, so node construction, edge validation, and build
    // reference checks cannot fail.
    GraphBuilder::new()
        .and_then(|builder| builder.add_node(node("0")))
        .and_then(|builder| builder.add_node(node("1")))
        .and_then(|builder| builder.add_node(node("2")))
        .and_then(|builder| add_edge(builder, first))
        .and_then(|builder| add_edge(builder, second))
        .and_then(|builder| add_edge(builder, third))
        .and_then(GraphBuilder::build)
        .unwrap()
}

fn complete_graph(node_count: usize, overrides: &[(&str, &str, EdgeTransform)]) -> GovernanceGraph {
    // SAFETY: GraphBuilder::new currently returns an empty builder without
    // validating caller data.
    let mut builder = GraphBuilder::new().unwrap();
    for index in 0..node_count {
        // SAFETY: decimal usize ids are non-empty and unique across this range.
        builder = builder.add_node(node(&index.to_string())).unwrap();
    }

    for left in 0..node_count {
        for right in (left + 1)..node_count {
            let from = left.to_string();
            let to = right.to_string();
            let transform = overrides
                .iter()
                .find_map(|(override_from, override_to, transform)| {
                    if (*override_from == from && *override_to == to)
                        || (*override_from == to && *override_to == from)
                    {
                        Some(transform.clone())
                    } else {
                        None
                    }
                })
                .unwrap_or(EdgeTransform::PassThrough);
            // SAFETY: complete_graph only connects ids inserted by the loop
            // above, and all caller-provided override transforms are finite.
            builder = add_edge(builder, (&from, &to, transform)).unwrap();
        }
    }

    // SAFETY: every edge endpoint was inserted before the edge was added.
    builder.build().unwrap()
}

fn five_node_graph(edges: &[(&str, &str, EdgeTransform)]) -> GovernanceGraph {
    node_graph(5, edges)
}

fn node_graph(node_count: usize, edges: &[(&str, &str, EdgeTransform)]) -> GovernanceGraph {
    // SAFETY: GraphBuilder::new currently returns an empty builder without
    // validating caller data.
    let mut builder = GraphBuilder::new().unwrap();
    for index in 0..node_count {
        // SAFETY: decimal usize ids are non-empty and unique across this range.
        builder = builder.add_node(node(&index.to_string())).unwrap();
    }
    for edge in edges {
        // SAFETY: all production callers pass fixed fixture edges whose
        // endpoints are within 0..node_count and whose transforms are finite.
        builder = add_edge(builder, (edge.0, edge.1, edge.2.clone())).unwrap();
    }
    // SAFETY: node_graph callers provide fixture edges over the inserted ids.
    builder.build().unwrap()
}

fn add_edge(
    builder: GraphBuilder,
    edge: (&str, &str, EdgeTransform),
) -> Result<GraphBuilder, LegitimacyError> {
    // SAFETY: fixture edge endpoints are non-empty literal or decimal ids.
    let from = NodeId::new(edge.0).unwrap();
    // SAFETY: fixture edge endpoints are non-empty literal or decimal ids.
    let to = NodeId::new(edge.1).unwrap();
    builder.add_edge(from, to, edge.2)
}

fn node(id: &str) -> GovernanceNode {
    GovernanceNode::Binary {
        // SAFETY: fixture node ids are non-empty literals or decimal strings.
        id: NodeId::new(id).unwrap(),
        name: id.to_string(),
        gates: Vec::new(),
        default: Decision::Escalate,
        combination: GateLogic::FirstMatch,
    }
}
