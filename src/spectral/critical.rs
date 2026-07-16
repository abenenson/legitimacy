use crate::{
    GovernanceGraph,
    spectral::{
        Rational, WeightedGovernanceGraph,
        coarse_grain::{
            cheeger_min_conductance_partition, coarse_grain, coarse_signal,
            greedy_max_weight_partition, modularity_maximizing_partition,
            signal_preserving_partition,
        },
        safe_div,
    },
};

pub fn sp_violation(graph: &GovernanceGraph, signal: &[Rational], tolerance: Rational) -> bool {
    let weighted = WeightedGovernanceGraph::from_graph(graph);
    let node_count = weighted.node_count();

    (0..node_count)
        .flat_map(|removed| (0..node_count).map(move |observer| (removed, observer)))
        .any(|(removed, observer)| tolerance <= weighted.perturbation(signal, removed, observer))
}

/// Inverse Laplace-mechanism noise scale for delta-DP release
/// (Nissim-Raskhodnikova-Smith 2007).
pub fn c_star(graph: &GovernanceGraph, signal: &[Rational], delta: Rational) -> Rational {
    let weighted = WeightedGovernanceGraph::from_graph(graph);
    safe_div(delta, weighted.cv(signal))
}

pub fn rg_trajectory(
    graph: &GovernanceGraph,
    signal: &[Rational],
    delta: Rational,
    k: usize,
) -> (Rational, Rational) {
    rg_trajectory_with(graph, signal, delta, k, |current_graph, _| {
        greedy_max_weight_partition(current_graph)
    })
}

pub fn rg_trajectory_cheeger(
    graph: &GovernanceGraph,
    signal: &[Rational],
    delta: Rational,
    k: usize,
) -> (Rational, Rational) {
    rg_trajectory_with(graph, signal, delta, k, |current_graph, _| {
        cheeger_min_conductance_partition(current_graph)
    })
}

pub fn rg_trajectory_modularity(
    graph: &GovernanceGraph,
    signal: &[Rational],
    delta: Rational,
    k: usize,
) -> (Rational, Rational) {
    rg_trajectory_with(graph, signal, delta, k, |current_graph, _| {
        modularity_maximizing_partition(current_graph)
    })
}

pub fn rg_trajectory_signal_preserving(
    graph: &GovernanceGraph,
    signal: &[Rational],
    delta: Rational,
    k: usize,
) -> (Rational, Rational) {
    rg_trajectory_with(graph, signal, delta, k, |current_graph, current_signal| {
        signal_preserving_partition(current_graph, current_signal)
    })
}

fn rg_trajectory_with(
    graph: &GovernanceGraph,
    signal: &[Rational],
    delta: Rational,
    k: usize,
    partition_fn: impl Fn(&GovernanceGraph, &[Rational]) -> Option<crate::spectral::Partition>,
) -> (Rational, Rational) {
    let mut current_graph = graph.clone();
    let mut current_signal = signal.to_vec();

    for _ in 0..k {
        let Some(partition) = partition_fn(&current_graph, &current_signal) else {
            break;
        };
        let next_signal = coarse_signal(&current_graph, &current_signal, &partition);
        current_graph = coarse_grain(&current_graph, &partition);
        current_signal = next_signal;
    }

    let weighted = WeightedGovernanceGraph::from_graph(&current_graph);
    let cv = weighted.cv(&current_signal);
    (cv, safe_div(delta, cv))
}

#[cfg(test)]
mod tests {
    use super::{c_star, rg_trajectory, sp_violation};
    use crate::{
        Decision, EdgeTransform, GateLogic, GovernanceGraph, GovernanceNode, GraphBuilder, NodeId,
        spectral::{Rational, rational},
    };

    #[test]
    fn consistency_vulnerability_tracks_cv_threshold() {
        let graph = uniform_triangle_graph();
        let signal = vec![
            Rational::from_integer(1),
            Rational::from_integer(2),
            Rational::from_integer(3),
        ];

        assert!(sp_violation(&graph, &signal, Rational::from_integer(1)));
        assert!(!sp_violation(&graph, &signal, rational(4, 3)));
    }

    #[test]
    fn critical_capability_matches_reciprocal_cv_on_uniform_triangle() {
        let graph = uniform_triangle_graph();
        let signal = vec![
            Rational::from_integer(1),
            Rational::from_integer(2),
            Rational::from_integer(3),
        ];

        assert_eq!(c_star(&graph, &signal, rational(1, 10)), rational(1, 10));
    }

    #[test]
    fn critical_capability_matches_reciprocal_cv_on_asymmetric_triangle() {
        let graph = asymmetric_triangle_graph();
        let signal = vec![
            Rational::from_integer(1),
            Rational::from_integer(2),
            Rational::from_integer(3),
        ];

        assert_eq!(c_star(&graph, &signal, rational(1, 10)), rational(3, 40));
    }

    #[test]
    fn rg_trajectory_matches_single_step_uniform_triangle_value() {
        let graph = uniform_triangle_graph();
        let signal = vec![
            Rational::from_integer(1),
            Rational::from_integer(2),
            Rational::from_integer(3),
        ];

        assert_eq!(
            rg_trajectory(&graph, &signal, rational(1, 10), 1),
            (rational(3, 1), rational(1, 30))
        );
    }

    fn uniform_triangle_graph() -> GovernanceGraph {
        GraphBuilder::new()
            .and_then(|builder| builder.add_node(node("0")))
            .and_then(|builder| builder.add_node(node("1")))
            .and_then(|builder| builder.add_node(node("2")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("0").unwrap(),
                    NodeId::new("1").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("1").unwrap(),
                    NodeId::new("2").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("0").unwrap(),
                    NodeId::new("2").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap()
    }

    fn asymmetric_triangle_graph() -> GovernanceGraph {
        GraphBuilder::new()
            .and_then(|builder| builder.add_node(node("0")))
            .and_then(|builder| builder.add_node(node("1")))
            .and_then(|builder| builder.add_node(node("2")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("0").unwrap(),
                    NodeId::new("1").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("1").unwrap(),
                    NodeId::new("2").unwrap(),
                    EdgeTransform::ClaimModification { delta: 2.0 },
                )
            })
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("0").unwrap(),
                    NodeId::new("2").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap()
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
