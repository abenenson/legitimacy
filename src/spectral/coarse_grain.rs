use crate::{
    Decision, EdgeTransform, GateLogic, GovernanceGraph, GovernanceNode, GraphBuilder, NodeId,
    spectral::{Partition, Rational, rational, safe_div},
};

use super::{WeightedGovernanceGraph, critical::c_star};

pub fn coarse_grain(graph: &GovernanceGraph, partition: &Partition) -> GovernanceGraph {
    let weighted = WeightedGovernanceGraph::from_graph(graph);
    let normalized = normalize_partition(&weighted, partition);
    // SAFETY: GraphBuilder::new currently returns an empty builder without
    // validating caller data.
    let mut builder = GraphBuilder::new().unwrap();

    for block in &normalized {
        // SAFETY: normalize_partition removes duplicate blocks and coarse_node
        // preserves valid ids already present in the source graph.
        builder = builder
            .add_node(coarse_node(&weighted.node_ids[block[0]]))
            .unwrap();
    }

    for left in 0..normalized.len() {
        for right in (left + 1)..normalized.len() {
            let weight = coarse_weight(&weighted, &normalized[left], &normalized[right]);
            if weight == Rational::from_integer(0) {
                continue;
            }

            // SAFETY: both coarse endpoints were added from normalized blocks,
            // and edge_transform receives finite weights from finite inputs.
            builder = builder
                .add_edge(
                    coarse_node_id(&weighted.node_ids[normalized[left][0]]),
                    coarse_node_id(&weighted.node_ids[normalized[right][0]]),
                    edge_transform(weight),
                )
                .unwrap();
        }
    }

    // SAFETY: coarse_grain only emits edges between normalized blocks that
    // were inserted as nodes above.
    builder.build().unwrap()
}

pub fn preserves_solidarity(graph: &GovernanceGraph, partition: &Partition) -> bool {
    let weighted = WeightedGovernanceGraph::from_graph(graph);
    let normalized = normalize_partition(&weighted, partition);

    for (block_index, block) in normalized.iter().enumerate() {
        for left_index in 0..block.len() {
            for right_index in (left_index + 1)..block.len() {
                if co_block_pair_splits_external_order(
                    &weighted,
                    &normalized,
                    block_index,
                    block[left_index],
                    block[right_index],
                ) {
                    return false;
                }
            }
        }
    }

    true
}

pub(crate) fn greedy_max_weight_partition(graph: &GovernanceGraph) -> Option<Partition> {
    let weighted = WeightedGovernanceGraph::from_graph(graph);
    let mut best_pair = None;
    let mut best_weight = Rational::from_integer(0);

    for left in 0..weighted.node_count() {
        for right in (left + 1)..weighted.node_count() {
            let weight = weighted.weights[left][right];
            if best_pair.is_none() || best_weight < weight {
                best_pair = Some((left, right));
                best_weight = weight;
            }
        }
    }

    best_pair.map(|(left, right)| {
        Partition::new(vec![vec![
            weighted.node_ids[left].clone(),
            weighted.node_ids[right].clone(),
        ]])
    })
}

pub(crate) fn cheeger_min_conductance_partition(graph: &GovernanceGraph) -> Option<Partition> {
    let weighted = WeightedGovernanceGraph::from_graph(graph);
    if weighted.node_count() == 0 {
        return None;
    }

    best_subset(&nontrivial_subsets(weighted.node_count()), |cand, best| {
        let cand_score = conductance_score(&weighted, cand);
        let best_score = conductance_score(&weighted, best);
        let cand_side = canonical_merged_side(weighted.node_count(), cand);
        let best_side = canonical_merged_side(weighted.node_count(), best);

        cand_score < best_score
            || (cand_score == best_score
                && subset_lex_lt(weighted.node_count(), &cand_side, &best_side))
    })
    .map(|side| {
        partition_from_indices(
            &weighted,
            merge_side_partition_indices(
                weighted.node_count(),
                &canonical_merged_side(weighted.node_count(), &side),
            ),
        )
    })
}

pub(crate) fn modularity_maximizing_partition(graph: &GovernanceGraph) -> Option<Partition> {
    let weighted = WeightedGovernanceGraph::from_graph(graph);
    if weighted.node_count() == 0 {
        return None;
    }

    best_subset(&nontrivial_subsets(weighted.node_count()), |cand, best| {
        let cand_score = modularity_score(&weighted, cand);
        let best_score = modularity_score(&weighted, best);
        let cand_side = canonical_merged_side(weighted.node_count(), cand);
        let best_side = canonical_merged_side(weighted.node_count(), best);

        cand_score > best_score
            || (cand_score == best_score
                && subset_lex_lt(weighted.node_count(), &cand_side, &best_side))
    })
    .map(|side| {
        partition_from_indices(
            &weighted,
            merge_side_partition_indices(
                weighted.node_count(),
                &canonical_merged_side(weighted.node_count(), &side),
            ),
        )
    })
}

pub(crate) fn signal_preserving_partition(
    graph: &GovernanceGraph,
    signal: &[Rational],
) -> Option<Partition> {
    let weighted = WeightedGovernanceGraph::from_graph(graph);
    if weighted.node_count() == 0 {
        return None;
    }

    let block_count = weighted.node_count().div_ceil(2);
    let candidates = all_set_partitions(weighted.node_count())
        .into_iter()
        .filter(|partition| partition.len() == block_count)
        .collect::<Vec<_>>();

    best_partition(&candidates, |cand, best| {
        let cand_score = signal_variance_score(signal, cand);
        let best_score = signal_variance_score(signal, best);

        cand_score < best_score
            || (cand_score == best_score && partition_lex_lt(weighted.node_count(), cand, best))
    })
    .map(|partition| {
        partition_from_indices(
            &weighted,
            canonicalize_partition(weighted.node_count(), partition),
        )
    })
}

pub fn breaks_monotonicity(
    graph: &GovernanceGraph,
    signal: &[Rational],
    delta: Rational,
    partition: &Partition,
) -> bool {
    let coarse_graph = coarse_grain(graph, partition);
    let coarse_signal = coarse_signal(graph, signal, partition);

    c_star(&coarse_graph, &coarse_signal, delta) < c_star(graph, signal, delta)
}

pub(crate) fn coarse_signal(
    graph: &GovernanceGraph,
    signal: &[Rational],
    partition: &Partition,
) -> Vec<Rational> {
    let weighted = WeightedGovernanceGraph::from_graph(graph);
    normalize_partition(&weighted, partition)
        .into_iter()
        .map(|block| block.into_iter().map(|index| signal[index]).sum())
        .collect()
}

fn normalize_partition(
    weighted: &WeightedGovernanceGraph,
    partition: &Partition,
) -> Vec<Vec<usize>> {
    let mut seen = vec![false; weighted.node_count()];
    let mut blocks = partition
        .blocks
        .iter()
        .map(|block| {
            let mut indices = block
                .iter()
                .filter_map(|node_id| weighted.index_by_node.get(node_id).copied())
                .filter(|index| {
                    if seen[*index] {
                        false
                    } else {
                        seen[*index] = true;
                        true
                    }
                })
                .collect::<Vec<_>>();
            indices.sort_unstable();
            indices
        })
        .filter(|block| !block.is_empty())
        .collect::<Vec<_>>();

    for (index, was_seen) in seen.iter().enumerate().take(weighted.node_count()) {
        if !*was_seen {
            blocks.push(vec![index]);
        }
    }

    blocks.sort_by_key(|block| block[0]);
    blocks
}

fn best_subset(
    candidates: &[Vec<usize>],
    better: impl Fn(&[usize], &[usize]) -> bool,
) -> Option<Vec<usize>> {
    let (first, rest) = candidates.split_first()?;
    let mut best = first.clone();

    for candidate in rest {
        if better(candidate, &best) {
            best = candidate.clone();
        }
    }

    Some(best)
}

fn best_partition(
    candidates: &[Vec<Vec<usize>>],
    better: impl Fn(&[Vec<usize>], &[Vec<usize>]) -> bool,
) -> Option<Vec<Vec<usize>>> {
    let (first, rest) = candidates.split_first()?;
    let mut best = first.clone();

    for candidate in rest {
        if better(candidate, &best) {
            best = candidate.clone();
        }
    }

    Some(best)
}

fn nontrivial_subsets(node_count: usize) -> Vec<Vec<usize>> {
    all_subsets(node_count)
        .into_iter()
        .filter(|subset| !subset.is_empty() && subset.len() < node_count)
        .collect()
}

fn all_subsets(node_count: usize) -> Vec<Vec<usize>> {
    let mut subsets = vec![Vec::new()];

    for node in 0..node_count {
        let with_node = subsets
            .iter()
            .map(|subset| {
                let mut next = subset.clone();
                next.push(node);
                next
            })
            .collect::<Vec<_>>();
        subsets.extend(with_node);
    }

    subsets
}

fn canonical_merged_side(node_count: usize, side: &[usize]) -> Vec<usize> {
    let other = complement(node_count, side);

    match side.len().cmp(&other.len()) {
        std::cmp::Ordering::Less => side.to_vec(),
        std::cmp::Ordering::Greater => other,
        std::cmp::Ordering::Equal => {
            if subset_lex_lt(node_count, side, &other) {
                side.to_vec()
            } else {
                other
            }
        }
    }
}

fn merge_side_partition_indices(node_count: usize, side: &[usize]) -> Vec<Vec<usize>> {
    let mut blocks = vec![side.to_vec()];

    for node in 0..node_count {
        if !contains(side, node) {
            blocks.push(vec![node]);
        }
    }

    canonicalize_partition(node_count, blocks)
}

fn canonicalize_partition(node_count: usize, mut partition: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    for block in &mut partition {
        block.sort_unstable();
    }

    partition.sort_by(|left, right| {
        if left == right {
            std::cmp::Ordering::Equal
        } else if subset_lex_lt(node_count, left, right) {
            std::cmp::Ordering::Less
        } else {
            std::cmp::Ordering::Greater
        }
    });

    partition
}

fn partition_from_indices(
    weighted: &WeightedGovernanceGraph,
    blocks: Vec<Vec<usize>>,
) -> Partition {
    Partition::new(
        blocks
            .into_iter()
            .map(|block| {
                block
                    .into_iter()
                    .map(|index| weighted.node_ids[index].clone())
                    .collect()
            })
            .collect(),
    )
}

fn subset_lex_lt(node_count: usize, left: &[usize], right: &[usize]) -> bool {
    for node in 0..node_count {
        let in_left = contains(left, node);
        let in_right = contains(right, node);
        if in_left != in_right {
            return in_left;
        }
    }

    false
}

fn partition_lex_lt(node_count: usize, left: &[Vec<usize>], right: &[Vec<usize>]) -> bool {
    let left = canonicalize_partition(node_count, left.to_vec());
    let right = canonicalize_partition(node_count, right.to_vec());

    for (left_block, right_block) in left.iter().zip(&right) {
        if left_block == right_block {
            continue;
        }
        return subset_lex_lt(node_count, left_block, right_block);
    }

    left.len() < right.len()
}

fn all_set_partitions(node_count: usize) -> Vec<Vec<Vec<usize>>> {
    let mut partitions = vec![Vec::new()];

    for node in 0..node_count {
        let mut next = Vec::new();
        for partition in &partitions {
            next.extend(insert_into_blocks(node, partition));
        }
        partitions = next;
    }

    partitions
}

fn insert_into_blocks(node: usize, partition: &[Vec<usize>]) -> Vec<Vec<Vec<usize>>> {
    if partition.is_empty() {
        return vec![vec![vec![node]]];
    }

    let mut results = Vec::with_capacity(partition.len() + 1);

    for block_index in 0..partition.len() {
        let mut next = partition.to_vec();
        next[block_index].push(node);
        next[block_index].sort_unstable();
        results.push(next);
    }

    let mut singleton_extension = partition.to_vec();
    singleton_extension.push(vec![node]);
    results.push(singleton_extension);
    results
}

fn conductance_score(weighted: &WeightedGovernanceGraph, side: &[usize]) -> Rational {
    let other = complement(weighted.node_count(), side);
    let denominator = side_volume(weighted, side).min(side_volume(weighted, &other));
    safe_div(block_weight(weighted, side, &other), denominator)
}

fn modularity_score(weighted: &WeightedGovernanceGraph, side: &[usize]) -> Rational {
    let other = complement(weighted.node_count(), side);
    let mass = total_edge_mass(weighted);
    let inner = (0..weighted.node_count())
        .flat_map(|left| (0..weighted.node_count()).map(move |right| (left, right)))
        .map(|(left, right)| {
            let same_block = (contains(side, left) && contains(side, right))
                || (contains(&other, left) && contains(&other, right));
            if same_block {
                weighted.weights[left][right]
                    - safe_div(
                        weighted.degree(left) * weighted.degree(right),
                        rational(2, 1) * mass,
                    )
            } else {
                Rational::from_integer(0)
            }
        })
        .sum();

    safe_div(inner, rational(2, 1) * mass)
}

fn signal_variance_score(signal: &[Rational], partition: &[Vec<usize>]) -> Rational {
    canonicalize_partition(signal.len(), partition.to_vec())
        .into_iter()
        .map(|block| block_variance(signal, &block))
        .sum()
}

fn block_variance(signal: &[Rational], block: &[usize]) -> Rational {
    let mean = block_mean(signal, block);
    let numerator = block
        .iter()
        .map(|&index| {
            let delta = signal[index] - mean;
            delta * delta
        })
        .sum();
    safe_div(numerator, Rational::from_integer(block.len() as i64))
}

fn block_mean(signal: &[Rational], block: &[usize]) -> Rational {
    let sum = block.iter().map(|&index| signal[index]).sum();
    safe_div(sum, Rational::from_integer(block.len() as i64))
}

fn total_edge_mass(weighted: &WeightedGovernanceGraph) -> Rational {
    weighted.weights.iter().flatten().cloned().sum()
}

fn side_volume(weighted: &WeightedGovernanceGraph, side: &[usize]) -> Rational {
    side.iter().map(|&node| weighted.degree(node)).sum()
}

fn block_weight(weighted: &WeightedGovernanceGraph, left: &[usize], right: &[usize]) -> Rational {
    left.iter()
        .flat_map(|&left_node| right.iter().map(move |&right_node| (left_node, right_node)))
        .map(|(left_node, right_node)| weighted.weights[left_node][right_node])
        .sum()
}

fn co_block_pair_splits_external_order(
    weighted: &WeightedGovernanceGraph,
    partition: &[Vec<usize>],
    own_block: usize,
    left_node: usize,
    right_node: usize,
) -> bool {
    for left_block in 0..partition.len() {
        if left_block == own_block {
            continue;
        }
        for right_block in (left_block + 1)..partition.len() {
            if right_block == own_block {
                continue;
            }

            let left_direction = block_order_direction(
                weighted,
                left_node,
                &partition[left_block],
                &partition[right_block],
            );
            let right_direction = block_order_direction(
                weighted,
                right_node,
                &partition[left_block],
                &partition[right_block],
            );

            if directions_conflict(left_direction, right_direction) {
                return true;
            }
        }
    }

    false
}

fn block_order_direction(
    weighted: &WeightedGovernanceGraph,
    node: usize,
    left_block: &[usize],
    right_block: &[usize],
) -> std::cmp::Ordering {
    node_block_weight(weighted, node, left_block).cmp(&node_block_weight(
        weighted,
        node,
        right_block,
    ))
}

fn node_block_weight(weighted: &WeightedGovernanceGraph, node: usize, block: &[usize]) -> Rational {
    block
        .iter()
        .map(|&block_node| weighted.weights[node][block_node])
        .sum()
}

fn directions_conflict(left: std::cmp::Ordering, right: std::cmp::Ordering) -> bool {
    matches!(
        (left, right),
        (std::cmp::Ordering::Less, std::cmp::Ordering::Greater)
            | (std::cmp::Ordering::Greater, std::cmp::Ordering::Less)
    )
}

fn complement(node_count: usize, side: &[usize]) -> Vec<usize> {
    (0..node_count)
        .filter(|&node| !contains(side, node))
        .collect()
}

fn contains(side: &[usize], node: usize) -> bool {
    side.binary_search(&node).is_ok()
}

fn coarse_weight(
    weighted: &WeightedGovernanceGraph,
    left_block: &[usize],
    right_block: &[usize],
) -> Rational {
    left_block
        .iter()
        .flat_map(|left| right_block.iter().map(move |right| (*left, *right)))
        .map(|(left, right)| weighted.weights[left][right])
        .sum()
}

fn coarse_node(original: &NodeId) -> GovernanceNode {
    GovernanceNode::Binary {
        id: coarse_node_id(original),
        name: format!("merged({original})"),
        gates: Vec::new(),
        default: Decision::Escalate,
        combination: GateLogic::FirstMatch,
    }
}

fn coarse_node_id(original: &NodeId) -> NodeId {
    original.clone()
}

fn edge_transform(weight: Rational) -> EdgeTransform {
    if weight == Rational::from_integer(1) {
        EdgeTransform::PassThrough
    } else {
        EdgeTransform::ClaimModification {
            delta: rational_to_f64(weight),
        }
    }
}

fn rational_to_f64(value: Rational) -> f64 {
    *value.numer() as f64 / *value.denom() as f64
}

#[cfg(test)]
mod tests {
    use super::{breaks_monotonicity, coarse_grain, coarse_signal, preserves_solidarity};
    use crate::{
        Decision, EdgeTransform, GateLogic, GovernanceGraph, GovernanceNode, GraphBuilder,
        LegitimacyError, NodeId,
        spectral::{
            Partition, Rational, critical::c_star, rational, stackelberg::default_signal_signature,
        },
    };

    #[test]
    fn coarse_grain_matches_uniform_triangle_rg_value() {
        let graph = uniform_triangle_graph();
        let partition = merge_zero_one_partition();
        let signal = default_signal_signature();
        let coarse = coarse_grain(&graph, &partition);
        let coarse_sig = coarse_signal(&graph, &signal, &partition);

        assert_eq!(
            coarse_sig,
            vec![Rational::from_integer(3), Rational::from_integer(3)]
        );
        assert_eq!(
            c_star(&coarse, &coarse_sig, rational(1, 10)),
            rational(1, 30)
        );
    }

    #[test]
    fn coarse_grain_breaks_monotonicity_on_uniform_triangle() {
        let graph = uniform_triangle_graph();
        let partition = merge_zero_one_partition();
        let signal = default_signal_signature();

        assert!(preserves_solidarity(&graph, &partition));
        assert!(breaks_monotonicity(
            &graph,
            &signal,
            rational(1, 10),
            &partition
        ));
    }

    #[test]
    fn preserves_solidarity_rejects_split_external_block_ordering() {
        let graph = split_external_ordering_graph();
        let partition = Partition::new(vec![
            vec![NodeId::new("0").unwrap(), NodeId::new("1").unwrap()],
            vec![NodeId::new("2").unwrap()],
            vec![NodeId::new("3").unwrap()],
        ]);

        assert!(!preserves_solidarity(&graph, &partition));
    }

    fn merge_zero_one_partition() -> Partition {
        Partition::new(vec![vec![
            NodeId::new("0").unwrap(),
            NodeId::new("1").unwrap(),
        ]])
    }

    fn uniform_triangle_graph() -> GovernanceGraph {
        GraphBuilder::new()
            .and_then(|builder| builder.add_node(node("0")))
            .and_then(|builder| builder.add_node(node("1")))
            .and_then(|builder| builder.add_node(node("2")))
            .and_then(|builder| add_edge(builder, "0", "1", EdgeTransform::PassThrough))
            .and_then(|builder| add_edge(builder, "0", "2", EdgeTransform::PassThrough))
            .and_then(|builder| add_edge(builder, "1", "2", EdgeTransform::PassThrough))
            .and_then(GraphBuilder::build)
            .unwrap()
    }

    fn split_external_ordering_graph() -> GovernanceGraph {
        GraphBuilder::new()
            .and_then(|builder| builder.add_node(node("0")))
            .and_then(|builder| builder.add_node(node("1")))
            .and_then(|builder| builder.add_node(node("2")))
            .and_then(|builder| builder.add_node(node("3")))
            .and_then(|builder| add_edge(builder, "0", "2", EdgeTransform::PassThrough))
            .and_then(|builder| add_edge(builder, "1", "3", EdgeTransform::PassThrough))
            .and_then(GraphBuilder::build)
            .unwrap()
    }

    fn add_edge(
        builder: GraphBuilder,
        from: &str,
        to: &str,
        transform: EdgeTransform,
    ) -> Result<GraphBuilder, LegitimacyError> {
        builder.add_edge(
            NodeId::new(from).unwrap(),
            NodeId::new(to).unwrap(),
            transform,
        )
    }

    fn node(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: Vec::new(),
            default: Decision::Escalate,
            combination: GateLogic::FirstMatch,
        }
    }
}
