use legitimacy::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceEdge, GovernanceGraph,
    GovernanceNode, NodeId, Verdict,
    axioms::{
        binary::{BinaryDelta, check_binary_monotonicity},
        graph::monotonicity::check_graph_monotonicity,
    },
    traverse,
};
use proptest::{
    collection::vec,
    prelude::*,
    strategy::BoxedStrategy,
    test_runner::{Config as ProptestConfig, TestCaseError, TestRunner},
};
use std::{
    collections::{BTreeMap, BTreeSet},
    env,
};

const PROPTEST_CASES: u32 = 1000;
const MAX_LOCAL_REJECTS: u32 = 10_000;
const PATHS: [&str; 5] = ["/alpha", "/alpha/review", "/beta", "/gamma", "/tmp"];
const GRAPH_PROPTEST_CASES_ENV: &str = "VERDICT_GRAPH_PROPTEST_CASES";

#[derive(Clone, Debug)]
struct BinaryNodeSpec {
    gates: Vec<Gate>,
    default: Decision,
    combination: GateLogic,
}

fn decision_strategy() -> BoxedStrategy<Decision> {
    prop_oneof![
        Just(Decision::Permit),
        Just(Decision::Deny),
        Just(Decision::Escalate),
    ]
    .boxed()
}

fn gate_logic_strategy() -> BoxedStrategy<GateLogic> {
    prop_oneof![
        Just(GateLogic::FirstMatch),
        Just(GateLogic::AnyMustPass),
        Just(GateLogic::AllMustPass),
    ]
    .boxed()
}

fn positive_decision_strategy() -> BoxedStrategy<Decision> {
    prop_oneof![Just(Decision::Permit), Just(Decision::Escalate),].boxed()
}

fn prefix_pattern_strategy() -> BoxedStrategy<String> {
    prop_oneof![
        Just("/alpha".to_string()),
        Just("/alpha/review".to_string()),
        Just("/beta".to_string()),
        Just("/gamma".to_string()),
        Just("/tmp".to_string()),
    ]
    .boxed()
}

fn gate_strategy(include_peer_relative: bool) -> BoxedStrategy<Gate> {
    let prefix = (prefix_pattern_strategy(), decision_strategy())
        .prop_map(|(pattern, decision)| Gate::PrefixMatch { pattern, decision });
    let threshold =
        (0.2f64..1.2f64, decision_strategy()).prop_map(|(min, decision)| Gate::ThresholdGate {
            field: "strength".to_string(),
            min,
            decision,
        });

    if include_peer_relative {
        let peer = (0.34f64..1.0f64, decision_strategy()).prop_map(|(percentile, decision)| {
            Gate::PeerRelative {
                field: "strength".to_string(),
                percentile,
                decision,
            }
        });
        prop_oneof![prefix, threshold, peer].boxed()
    } else {
        prop_oneof![prefix, threshold].boxed()
    }
}

fn random_binary_node_with(include_peer_relative: bool) -> BoxedStrategy<BinaryNodeSpec> {
    (
        vec(gate_strategy(include_peer_relative), 1..=5),
        decision_strategy(),
        gate_logic_strategy(),
    )
        .prop_map(|(gates, default, combination)| BinaryNodeSpec {
            gates,
            default,
            combination,
        })
        .boxed()
}

fn random_binary_node() -> BoxedStrategy<BinaryNodeSpec> {
    random_binary_node_with(true)
}

fn random_binary_node_without_peer_relative() -> BoxedStrategy<BinaryNodeSpec> {
    let prefix = (prefix_pattern_strategy(), positive_decision_strategy())
        .prop_map(|(pattern, decision)| Gate::PrefixMatch { pattern, decision });
    let threshold = (0.2f64..1.2f64, positive_decision_strategy()).prop_map(|(min, decision)| {
        Gate::ThresholdGate {
            field: "strength".to_string(),
            min,
            decision,
        }
    });

    (
        vec(prop_oneof![prefix, threshold], 1..=5),
        Just(Decision::Deny),
        prop_oneof![Just(GateLogic::AnyMustPass), Just(GateLogic::AllMustPass)],
    )
        .prop_map(|(gates, default, combination)| BinaryNodeSpec {
            gates,
            default,
            combination,
        })
        .boxed()
}

fn all_forward_pairs(node_count: usize) -> Vec<(usize, usize)> {
    let mut pairs = Vec::new();
    for from in 0..node_count {
        for to in from + 1..node_count {
            pairs.push((from, to));
        }
    }
    pairs
}

fn connected_edge_mask(node_count: usize) -> BoxedStrategy<Vec<bool>> {
    let pairs = all_forward_pairs(node_count);
    (
        vec(any::<usize>(), node_count.saturating_sub(1)),
        vec(any::<bool>(), pairs.len()),
    )
        .prop_map(move |(parents, mut edge_mask)| {
            for (offset, raw_parent) in parents.into_iter().enumerate() {
                let to = offset + 1;
                let from = raw_parent % to;
                let pair_index = pairs
                    .iter()
                    .position(|pair| *pair == (from, to))
                    .expect("connected edge must exist among forward pairs");
                edge_mask[pair_index] = true;
            }
            edge_mask
        })
        .boxed()
}

fn node_from_spec(index: usize, spec: BinaryNodeSpec) -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new(format!("n{index}")).unwrap(),
        name: format!("node-{index}"),
        gates: spec.gates,
        default: spec.default,
        combination: spec.combination,
    }
}

fn graph_from_specs(specs: Vec<BinaryNodeSpec>, edge_mask: Vec<bool>) -> GovernanceGraph {
    let pairs = all_forward_pairs(specs.len());
    let mut nodes = BTreeMap::new();
    for (index, spec) in specs.into_iter().enumerate() {
        let node = node_from_spec(index, spec);
        let node_id = match &node {
            GovernanceNode::Binary { id, .. } => id.clone(),
            _ => unreachable!("graph-property strategies only build binary nodes"),
        };
        nodes.insert(node_id, node);
    }

    let edges = pairs
        .into_iter()
        .zip(edge_mask)
        .filter(|(_, include)| *include)
        .map(|((from, to), _)| {
            GovernanceEdge::new(
                NodeId::new(format!("n{from}")).unwrap(),
                NodeId::new(format!("n{to}")).unwrap(),
                EdgeTransform::PassThrough,
            )
            .unwrap()
        })
        .collect();

    GovernanceGraph { nodes, edges }
}

fn arbitrary_random_graph(include_peer_relative: bool) -> BoxedStrategy<GovernanceGraph> {
    (2usize..=5)
        .prop_flat_map(move |node_count| {
            let node_strategy = if include_peer_relative {
                random_binary_node()
            } else {
                random_binary_node_without_peer_relative()
            };
            (
                vec(node_strategy, node_count),
                connected_edge_mask(node_count),
            )
                .prop_map(|(specs, edge_mask)| graph_from_specs(specs, edge_mask))
        })
        .boxed()
}

fn composition_biased_graph() -> BoxedStrategy<GovernanceGraph> {
    (
        0.35f64..0.8f64,
        0.5f64..0.9f64,
        0.8f64..1.2f64,
        random_binary_node(),
        prop::option::of(random_binary_node()),
    )
        .prop_map(|(threshold, percentile, booster_min, extra, sink)| {
            let mut nodes = BTreeMap::new();
            nodes.insert(
                NodeId::new("n0").unwrap(),
                GovernanceNode::Binary {
                    id: NodeId::new("n0").unwrap(),
                    name: "entry-threshold".to_string(),
                    gates: vec![Gate::ThresholdGate {
                        field: "strength".to_string(),
                        min: threshold,
                        decision: Decision::Escalate,
                    }],
                    default: Decision::Deny,
                    combination: GateLogic::FirstMatch,
                },
            );
            nodes.insert(
                NodeId::new("n1").unwrap(),
                GovernanceNode::Binary {
                    id: NodeId::new("n1").unwrap(),
                    name: "peer-relative-exit".to_string(),
                    gates: vec![Gate::PeerRelative {
                        field: "strength".to_string(),
                        percentile,
                        decision: Decision::Permit,
                    }],
                    default: Decision::Deny,
                    combination: GateLogic::AnyMustPass,
                },
            );
            nodes.insert(
                NodeId::new("n2").unwrap(),
                GovernanceNode::Binary {
                    id: NodeId::new("n2").unwrap(),
                    name: "booster".to_string(),
                    gates: vec![Gate::ThresholdGate {
                        field: "strength".to_string(),
                        min: booster_min,
                        decision: Decision::Escalate,
                    }],
                    default: Decision::Deny,
                    combination: GateLogic::FirstMatch,
                },
            );
            nodes.insert(NodeId::new("n3").unwrap(), node_from_spec(3, extra));
            if let Some(spec) = sink {
                nodes.insert(NodeId::new("n4").unwrap(), node_from_spec(4, spec));
            }

            let mut edges = vec![
                GovernanceEdge::new(
                    NodeId::new("n0").unwrap(),
                    NodeId::new("n1").unwrap(),
                    EdgeTransform::PassThrough,
                )
                .unwrap(),
                GovernanceEdge::new(
                    NodeId::new("n0").unwrap(),
                    NodeId::new("n2").unwrap(),
                    EdgeTransform::PassThrough,
                )
                .unwrap(),
                GovernanceEdge::new(
                    NodeId::new("n2").unwrap(),
                    NodeId::new("n1").unwrap(),
                    EdgeTransform::PassThrough,
                )
                .unwrap(),
            ];
            if nodes.contains_key(&NodeId::new("n4").unwrap()) {
                edges.push(
                    GovernanceEdge::new(
                        NodeId::new("n1").unwrap(),
                        NodeId::new("n4").unwrap(),
                        EdgeTransform::PassThrough,
                    )
                    .unwrap(),
                );
            }

            GovernanceGraph { nodes, edges }
        })
        .boxed()
}

fn random_graph() -> BoxedStrategy<GovernanceGraph> {
    prop_oneof![
        3 => arbitrary_random_graph(true),
        2 => composition_biased_graph(),
    ]
    .boxed()
}

fn random_graph_without_peer_relative() -> BoxedStrategy<GovernanceGraph> {
    arbitrary_random_graph(false)
}

fn random_claims() -> BoxedStrategy<Vec<GovernanceClaim>> {
    (
        0.05f64..0.45f64,
        0.65f64..1.5f64,
        0usize..PATHS.len(),
        0usize..PATHS.len(),
        vec((0.05f64..1.5f64, 0usize..PATHS.len()), 0..=8),
    )
        .prop_map(
            |(low_strength, high_strength, left_path, right_path, extras)| {
                let right_path = if right_path == left_path {
                    (right_path + 1) % PATHS.len()
                } else {
                    right_path
                };

                let mut claims = vec![
                    GovernanceClaim {
                        claimant_id: "c0".to_string(),
                        strength: low_strength,
                        priority_class: None,
                        path: Some(PATHS[left_path].to_string()),
                        action: None,
                        content: None,
                        metrics: BTreeMap::new(),
                    },
                    GovernanceClaim {
                        claimant_id: "c1".to_string(),
                        strength: high_strength,
                        priority_class: None,
                        path: Some(PATHS[right_path].to_string()),
                        action: None,
                        content: None,
                        metrics: BTreeMap::new(),
                    },
                ];

                claims.extend(extras.into_iter().enumerate().map(
                    |(offset, (strength, path_index))| {
                        let index = offset + 2;
                        GovernanceClaim {
                            claimant_id: format!("c{index}"),
                            strength: strength + index as f64 * 1e-4,
                            priority_class: None,
                            path: Some(PATHS[path_index].to_string()),
                            action: None,
                            content: None,
                            metrics: BTreeMap::new(),
                        }
                    },
                ));

                claims
            },
        )
        .boxed()
}

fn monotonicity_deltas() -> [BinaryDelta; 2] {
    [
        BinaryDelta {
            field: "strength".to_string(),
            delta: 0.1,
        },
        BinaryDelta {
            field: "strength".to_string(),
            delta: 0.25,
        },
    ]
}

fn contains_peer_relative(graph: &GovernanceGraph) -> bool {
    graph.nodes.values().any(|node| match node {
        GovernanceNode::Binary { gates, .. } => gates
            .iter()
            .any(|gate| matches!(gate, Gate::PeerRelative { .. })),
        _ => false,
    })
}

fn individually_monotone_nodes(
    graph: &GovernanceGraph,
    claims: &[GovernanceClaim],
    deltas: &[BinaryDelta],
) -> bool {
    let traversal = traverse(graph, claims).unwrap();

    traversal.node_decisions.iter().all(|(node_id, decisions)| {
        let claimant_ids = decisions
            .iter()
            .map(|decision| decision.claimant_id.clone())
            .collect::<BTreeSet<_>>();
        let node_claims = claims
            .iter()
            .filter(|claim| claimant_ids.contains(&claim.claimant_id))
            .cloned()
            .collect::<Vec<_>>();
        let node = graph.nodes.get(node_id).unwrap();

        matches!(
            check_binary_monotonicity(node, &node_claims, deltas).unwrap(),
            Verdict::Admissible { .. }
        )
    })
}

fn reordered_graph(graph: &GovernanceGraph) -> GovernanceGraph {
    let mut node_ids = graph.nodes.keys().cloned().collect::<Vec<_>>();
    node_ids.sort();
    node_ids.reverse();

    let mut nodes = BTreeMap::new();
    for node_id in node_ids {
        nodes.insert(node_id.clone(), graph.nodes[&node_id].clone());
    }

    let mut edges = graph.edges.clone();
    edges.reverse();

    GovernanceGraph { nodes, edges }
}

fn configured_case_count() -> u32 {
    env::var(GRAPH_PROPTEST_CASES_ENV)
        .ok()
        .and_then(|value| value.parse::<u32>().ok())
        .filter(|value| *value > 0)
        .unwrap_or(PROPTEST_CASES)
}

fn proptest_runner(cases: u32) -> TestRunner {
    TestRunner::new(ProptestConfig {
        cases,
        max_local_rejects: MAX_LOCAL_REJECTS,
        failure_persistence: None,
        ..ProptestConfig::default()
    })
}

#[test]
fn proptest_finds_graph_level_composition_counterexamples() {
    let mut runner = proptest_runner(PROPTEST_CASES);

    let result = runner.run(&(random_graph(), random_claims()), |(graph, claims)| {
        let deltas = monotonicity_deltas();
        let graph_fails = matches!(
            check_graph_monotonicity(&graph, &claims, &deltas).unwrap(),
            Verdict::Rejected { .. }
        );

        if contains_peer_relative(&graph)
            && !graph.edges.is_empty()
            && individually_monotone_nodes(&graph, &claims, &deltas)
            && graph_fails
        {
            return Err(TestCaseError::fail(
                "found a graph-level monotonicity counterexample",
            ));
        }

        Ok(())
    });

    assert!(
        result.is_err(),
        "expected proptest to find a composition counterexample within {PROPTEST_CASES} cases"
    );
}

#[test]
fn peer_relative_free_graphs_are_graph_monotone() {
    let cases = configured_case_count();
    let mut runner = proptest_runner(cases);

    runner
        .run(
            &(random_graph_without_peer_relative(), random_claims()),
            |(graph, claims)| {
                let deltas = monotonicity_deltas();
                let verdict = check_graph_monotonicity(&graph, &claims, &deltas).unwrap();

                if matches!(verdict, Verdict::Admissible { .. }) {
                    Ok(())
                } else {
                    Err(TestCaseError::fail(format!(
                        "threshold/prefix-only connected DAGs should compose monotonically; got {verdict:?}"
                    )))
                }
            },
        )
        .unwrap();
}

#[test]
fn graph_traversal_is_deterministic() {
    let cases = configured_case_count();
    let mut runner = proptest_runner(cases);

    runner
        .run(&(random_graph(), random_claims()), |(graph, claims)| {
            let left = traverse(&graph, &claims).unwrap();
            let right = traverse(&graph, &claims).unwrap();

            if left == right {
                Ok(())
            } else {
                Err(TestCaseError::fail(format!(
                    "graph traversal should be deterministic; left={left:?}, right={right:?}"
                )))
            }
        })
        .unwrap();
}

#[test]
fn graph_results_ignore_hash_map_insertion_order() {
    let cases = configured_case_count();
    let mut runner = proptest_runner(cases);

    runner
        .run(&(random_graph(), random_claims()), |(graph, claims)| {
            let reordered = reordered_graph(&graph);
            let left = traverse(&graph, &claims).unwrap();
            let right = traverse(&reordered, &claims).unwrap();

            if left == right {
                Ok(())
            } else {
                Err(TestCaseError::fail(format!(
                    "hash-map insertion order should not matter; left={left:?}, right={right:?}"
                )))
            }
        })
        .unwrap();
}
