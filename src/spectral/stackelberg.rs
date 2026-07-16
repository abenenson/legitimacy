use crate::{
    GovernanceGraph,
    spectral::{Rational, SignalSignature},
};
use std::cmp;

use super::{
    concrete_graphs::{five_graph_lattice, signal_signature},
    critical::c_star,
};

pub fn stackelberg_value(delta: Rational) -> Rational {
    let signal = default_signal_signature();
    five_graph_lattice()
        .into_iter()
        .map(|graph| c_star(&graph, &signal, delta))
        .max()
        .unwrap_or_else(|| Rational::from_integer(0))
}

pub fn stackelberg_asymmetry_cost(
    graph_asym: &GovernanceGraph,
    graphs_sym: &[GovernanceGraph],
    signal: &[Rational],
    delta: Rational,
) -> Rational {
    let asym = c_star(graph_asym, signal, delta);
    let symmetric_floor = graphs_sym
        .iter()
        .map(|graph| c_star(graph, signal, delta))
        .min()
        .unwrap_or_else(|| Rational::from_integer(0));
    cmp::max(Rational::from_integer(0), symmetric_floor - asym)
}

pub fn default_signal_signature() -> SignalSignature {
    signal_signature()
}

#[cfg(test)]
mod tests {
    use super::{default_signal_signature, stackelberg_asymmetry_cost, stackelberg_value};
    use crate::spectral::{
        concrete_graphs::{
            asym_tri_graph, bottleneck_graph, near_path_graph, strongly_connected_graph,
            uni_tri_graph,
        },
        rational,
    };

    #[test]
    fn stackelberg_value_matches_lean_concrete_result() {
        assert_eq!(stackelberg_value(rational(1, 10)), rational(1, 10));
    }

    #[test]
    fn stackelberg_asymmetry_cost_matches_gap_to_symmetric_floor() {
        let signal = default_signal_signature();
        let symmetric = vec![
            uni_tri_graph(),
            near_path_graph(),
            strongly_connected_graph(),
            bottleneck_graph(),
        ];

        assert_eq!(
            stackelberg_asymmetry_cost(&asym_tri_graph(), &symmetric, &signal, rational(1, 10),),
            rational(1, 40)
        );
    }
}
