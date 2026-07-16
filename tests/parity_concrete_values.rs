pub use legitimacy::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceGraph, GovernanceNode, GraphBuilder,
    LegitimacyError, NodeId,
};

#[allow(dead_code)]
#[path = "../src/spectral/mod.rs"]
mod spectral;

use legitimacy::spectral::{
    Rational, capacity,
    concrete_graphs::{
        asym_k5, asym_tri_graph, bottleneck_graph, bottleneck5, near_path_graph, near_path5,
        signal_signature, signal_signature5, strongly_connected_graph, uni_k5, uni_tri_graph,
        wheel5,
    },
    critical::{c_star, rg_trajectory, sp_violation},
    cv,
};

fn rational(numerator: i64, denominator: i64) -> Rational {
    Rational::new(numerator, denominator)
}

fn localizability(graph: &GovernanceGraph, signal: &[Rational]) -> Rational {
    let weighted = spectral::WeightedGovernanceGraph::from_graph(graph);
    let zero = Rational::from_integer(0);
    let min_cv_i = (0..weighted.node_count())
        .map(|removed| {
            (0..weighted.node_count())
                .map(|observer| weighted.perturbation(signal, removed, observer))
                .max()
                .unwrap_or(zero)
        })
        .min()
        .unwrap_or(zero);
    let max_governance = (0..weighted.node_count())
        .map(|observer| spectral::abs_ratio(weighted.governance(signal, observer)))
        .max()
        .unwrap_or(zero);

    Rational::from_integer(1) - spectral::safe_div(min_cv_i, max_governance)
}

fn entropy_rat(graph: &GovernanceGraph) -> Rational {
    let weighted = spectral::WeightedGovernanceGraph::from_graph(graph);
    let node_count = i64::try_from(weighted.node_count()).unwrap();
    let n = Rational::from_integer(node_count);
    let mut off_diagonal = Rational::from_integer(0);
    for left in 0..weighted.node_count() {
        for right in 0..weighted.node_count() {
            if left == right {
                continue;
            }
            let numerator = weighted.weights[left][right] * weighted.weights[left][right];
            let denominator = weighted.degree(left) * weighted.degree(right);
            off_diagonal += spectral::safe_div(numerator, denominator);
        }
    }
    let trace = n + off_diagonal;

    Rational::from_integer(1) - spectral::safe_div(trace, n * n)
}

fn below_bifurcation_boundary(
    graph: &GovernanceGraph,
    signal: &[Rational],
    delta: Rational,
    capability: Rational,
) -> bool {
    let zero = Rational::from_integer(0);
    capacity(graph, signal, delta)
        && cv(graph, signal) > zero
        && capability > zero
        && capability < c_star(graph, signal, delta)
}

fn asi_spectral_signature(delta: Rational, target: (Rational, Rational)) -> bool {
    delta > Rational::from_integer(0) && target == (Rational::from_integer(10), delta / 10)
}

#[test]
fn concrete_localizability_values() {
    let signal = signal_signature();

    for (name, graph, expected) in [
        ("uniTriGraph", uni_tri_graph(), rational(4, 5)),
        ("asymTriGraph", asym_tri_graph(), rational(11, 15)),
        ("nearPathGraph", near_path_graph(), rational(53, 103)),
        (
            "stronglyConnectedGraph",
            strongly_connected_graph(),
            rational(4, 5),
        ),
        (
            "bottleneckGraph",
            bottleneck_graph(),
            rational(10003, 20003),
        ),
    ] {
        assert_eq!(localizability(&graph, &signal), expected, "{name}");
    }
}

#[test]
fn concrete_bifurcation_n5() {
    let signal = signal_signature5();
    let delta = Rational::from_integer(80);
    let capability = Rational::from_integer(1);

    for (name, graph, expected) in [
        ("uniK5", uni_k5(), true),
        ("asymK5", asym_k5(), true),
        ("nearPath5", near_path5(), false),
        ("wheel5", wheel5(), true),
        ("bottleneck5", bottleneck5(), false),
    ] {
        let actual = below_bifurcation_boundary(&graph, &signal, delta, capability);
        let stable = capability > Rational::from_integer(0)
            && !sp_violation(&graph, &signal, delta / capability);

        assert_eq!(actual, expected, "{name}");
        assert_eq!(
            actual,
            capacity(&graph, &signal, delta)
                && cv(&graph, &signal) > Rational::from_integer(0)
                && stable,
            "{name} spectral diagnostic"
        );
    }
}

#[test]
fn concrete_entropy_values_n5() {
    for (name, graph, expected) in [
        ("uniK5", uni_k5(), rational(3, 4)),
        ("asymK5", asym_k5(), rational(3741, 5000)),
        ("nearPath5", near_path5(), rational(83712841, 121770150)),
        ("wheel5", wheel5(), rational(329, 450)),
        (
            "bottleneck5",
            bottleneck5(),
            rational(1600380018, 2500500025),
        ),
    ] {
        assert_eq!(entropy_rat(&graph), expected, "{name}");
    }
}

#[test]
fn concrete_entropy_order_n5() {
    let bottleneck = entropy_rat(&bottleneck5());
    let near_path = entropy_rat(&near_path5());
    let wheel = entropy_rat(&wheel5());
    let asym = entropy_rat(&asym_k5());
    let uni = entropy_rat(&uni_k5());

    assert!(bottleneck < near_path);
    assert!(near_path < wheel);
    assert!(wheel < asym);
    assert!(asym < uni);
}

#[test]
fn concrete_iterated_rg_n5_parametric_signature() {
    let signal = signal_signature5();
    let delta = rational(1, 10);

    for (name, graph, expected) in [
        ("uniK5", uni_k5(), true),
        ("asymK5", asym_k5(), true),
        ("nearPath5", near_path5(), true),
        ("bottleneck5", bottleneck5(), false),
        ("wheel5", wheel5(), true),
    ] {
        let actual = asi_spectral_signature(delta, rg_trajectory(&graph, &signal, delta, 3));
        assert_eq!(actual, expected, "{name}");
    }
}
