use crate::{
    GovernanceGraph,
    spectral::{
        Partition, Rational, SignalSignature, capacity_bound, coarse_grain::coarse_grain,
        coarse_grain::coarse_signal, concrete_graphs::*, critical::c_star, critical::rg_trajectory,
        critical::rg_trajectory_cheeger, critical::rg_trajectory_modularity,
        critical::rg_trajectory_signal_preserving, cv, spectral_well_connected,
        stackelberg::stackelberg_value,
    },
};
use serde::Deserialize;
use std::{collections::BTreeMap, sync::OnceLock};

#[derive(Debug, Deserialize)]
struct SpectralFixtures {
    delta: String,
    capacity_bounds: BTreeMap<String, String>,
    cv_values: BTreeMap<String, String>,
    critical_capability: BTreeMap<String, String>,
    stackelberg: ScalarFixture,
    coarse_grain: CoarseFixture,
    spectral_well_connected_n3: BTreeMap<String, bool>,
    spectral_well_connected_n5: BTreeMap<String, bool>,
    rg_n5: BTreeMap<String, Vec<[String; 2]>>,
    rg_n7: BTreeMap<String, Vec<[String; 2]>>,
    rg_cheeger_n5: BTreeMap<String, Vec<[String; 2]>>,
    rg_modularity_n5: BTreeMap<String, Vec<[String; 2]>>,
    rg_signal_preserving_n5: BTreeMap<String, Vec<[String; 2]>>,
}

#[derive(Debug, Deserialize)]
struct ScalarFixture {
    value: String,
}

#[derive(Debug, Deserialize)]
struct CoarseFixture {
    signal: Vec<String>,
    cv: String,
    c_star: String,
}

fn fixtures() -> &'static SpectralFixtures {
    static FIXTURES: OnceLock<SpectralFixtures> = OnceLock::new();
    FIXTURES.get_or_init(|| {
        toml::from_str(include_str!(
            "../../tests/fixtures/spectral_expectations.toml"
        ))
        .expect("spectral fixture TOML should parse")
    })
}

fn parse_ratio(value: &str) -> Rational {
    let value = value.trim();
    if let Some((numerator, denominator)) = value.split_once('/') {
        return Rational::new(
            numerator.parse().expect("fixture numerator should parse"),
            denominator
                .parse()
                .expect("fixture denominator should parse"),
        );
    }

    Rational::from_integer(value.parse().expect("fixture integer should parse"))
}

fn parse_pair(value: &[String; 2]) -> (Rational, Rational) {
    (parse_ratio(&value[0]), parse_ratio(&value[1]))
}

fn delta() -> Rational {
    parse_ratio(&fixtures().delta)
}

fn assert_cv_matches(graph_name: &str, graph: &GovernanceGraph, signal: &[Rational]) {
    let expected = fixtures()
        .cv_values
        .get(graph_name)
        .unwrap_or_else(|| panic!("missing cv fixture for {graph_name}"));
    assert_eq!(cv(graph, signal), parse_ratio(expected));
}

fn assert_spectral_well_connected_matches(
    section: &BTreeMap<String, bool>,
    graph_name: &str,
    graph: &GovernanceGraph,
    signal: &[Rational],
) {
    let expected = section
        .get(graph_name)
        .unwrap_or_else(|| panic!("missing spectral well-connected fixture for {graph_name}"));

    assert_eq!(
        spectral_well_connected(graph, signal),
        *expected,
        "{graph_name}: spectral well-connected drift",
    );
}

fn assert_trajectory_matches<F>(
    section: &BTreeMap<String, Vec<[String; 2]>>,
    graph: &GovernanceGraph,
    graph_name: &str,
    signal: &SignalSignature,
    actual: F,
) where
    F: Fn(&GovernanceGraph, &[Rational], Rational, usize) -> (Rational, Rational),
{
    let expected = section
        .get(graph_name)
        .unwrap_or_else(|| panic!("missing fixture section for {graph_name}"));

    for (step, value) in expected.iter().enumerate() {
        assert_eq!(actual(graph, signal, delta(), step), parse_pair(value));
    }
}

#[test]
fn concrete_capacity_values_match_lean_exact_values() {
    let signal = signal_signature();
    for (graph_name, graph) in [
        ("uni_tri", uni_tri_graph()),
        ("asym_tri", asym_tri_graph()),
        ("near_path", near_path_graph()),
        ("strongly_connected", strongly_connected_graph()),
        ("bottleneck", bottleneck_graph()),
    ] {
        let expected = fixtures()
            .capacity_bounds
            .get(graph_name)
            .unwrap_or_else(|| panic!("missing capacity fixture for {graph_name}"));
        assert_eq!(capacity_bound(&graph, &signal), parse_ratio(expected));
    }
}

#[test]
fn concrete_cv_value_for_uniform_triangle_matches_lean() {
    assert_cv_matches("uni_tri", &uni_tri_graph(), &signal_signature());
}

#[test]
fn concrete_cv_value_for_asymmetric_triangle_matches_lean() {
    assert_cv_matches("asym_tri", &asym_tri_graph(), &signal_signature());
}

#[test]
fn concrete_cv_value_for_near_path_matches_lean() {
    assert_cv_matches("near_path", &near_path_graph(), &signal_signature());
}

#[test]
fn concrete_cv_value_for_strongly_connected_triangle_matches_lean() {
    assert_cv_matches(
        "strongly_connected",
        &strongly_connected_graph(),
        &signal_signature(),
    );
}

#[test]
fn concrete_cv_value_for_bottleneck_triangle_matches_lean() {
    assert_cv_matches("bottleneck", &bottleneck_graph(), &signal_signature());
}

#[test]
fn concrete_critical_capability_values_match_lean() {
    let signal = signal_signature();
    for (graph_name, graph) in [
        ("uni_tri", uni_tri_graph()),
        ("asym_tri", asym_tri_graph()),
        ("near_path", near_path_graph()),
        ("strongly_connected", strongly_connected_graph()),
        ("bottleneck", bottleneck_graph()),
    ] {
        let expected = fixtures()
            .critical_capability
            .get(graph_name)
            .unwrap_or_else(|| panic!("missing critical capability fixture for {graph_name}"));
        assert_eq!(c_star(&graph, &signal, delta()), parse_ratio(expected));
    }
}

#[test]
fn stackelberg_value_matches_lean() {
    assert_eq!(
        stackelberg_value(delta()),
        parse_ratio(&fixtures().stackelberg.value)
    );
}

#[test]
fn coarse_grain_matches_five_graph_rg_flow_values() {
    let signal = signal_signature();
    let partition = Partition::new(vec![vec![node("0"), node("1")]]);
    let coarse_fixture = &fixtures().coarse_grain;
    let expected_signal = coarse_fixture
        .signal
        .iter()
        .map(|value| parse_ratio(value))
        .collect::<Vec<_>>();

    for graph in five_graph_lattice() {
        let coarse = coarse_grain(&graph, &partition);
        let coarse_sig = coarse_signal(&graph, &signal, &partition);

        assert_eq!(coarse_sig, expected_signal);
        assert_eq!(cv(&coarse, &coarse_sig), parse_ratio(&coarse_fixture.cv));
        assert_eq!(
            c_star(&coarse, &coarse_sig, delta()),
            parse_ratio(&coarse_fixture.c_star)
        );
    }
}

#[test]
fn concrete_n3_spectral_well_connected_matches_lean_fixture() {
    let signal = signal_signature();
    for (graph_name, graph) in [
        ("uni_tri", uni_tri_graph()),
        ("asym_tri", asym_tri_graph()),
        ("near_path", near_path_graph()),
        ("strongly_connected", strongly_connected_graph()),
        ("bottleneck", bottleneck_graph()),
    ] {
        assert_spectral_well_connected_matches(
            &fixtures().spectral_well_connected_n3,
            graph_name,
            &graph,
            &signal,
        );
    }
}

#[test]
fn concrete_n5_spectral_well_connected_matches_lean_fixture() {
    let signal = signal_signature5();
    for (graph_name, graph) in [
        ("uni_k5", uni_k5()),
        ("asym_k5", asym_k5()),
        ("near_path5", near_path5()),
        ("bottleneck5", bottleneck5()),
        ("wheel5", wheel5()),
    ] {
        assert_spectral_well_connected_matches(
            &fixtures().spectral_well_connected_n5,
            graph_name,
            &graph,
            &signal,
        );
    }
}

#[test]
fn concrete_iterated_rg_n5_matches_lean() {
    let signal = signal_signature5();
    for (graph_name, graph) in [
        ("uni_k5", uni_k5()),
        ("asym_k5", asym_k5()),
        ("near_path5", near_path5()),
        ("bottleneck5", bottleneck5()),
        ("wheel5", wheel5()),
    ] {
        assert_trajectory_matches(
            &fixtures().rg_n5,
            &graph,
            graph_name,
            &signal,
            rg_trajectory,
        );
    }
}

#[test]
fn concrete_iterated_rg_n7_matches_lean() {
    let signal = signal_signature7();
    for (graph_name, graph) in [
        ("uni_k7", uni_k7()),
        ("asym_k7", asym_k7()),
        ("near_path7", near_path7()),
        ("bottleneck7_bi", bottleneck7_bi()),
        ("bottleneck7_tri", bottleneck7_tri()),
        ("hub_spoke_hierarchy7", hub_spoke_hierarchy7()),
        ("nested_hierarchy7", nested_hierarchy7()),
    ] {
        assert_trajectory_matches(
            &fixtures().rg_n7,
            &graph,
            graph_name,
            &signal,
            rg_trajectory,
        );
    }
}

#[test]
fn cheeger_iterated_rg_n5_matches_lean() {
    let signal = signal_signature5();
    for (graph_name, graph) in [
        ("uni_k5", uni_k5()),
        ("asym_k5", asym_k5()),
        ("near_path5", near_path5()),
        ("bottleneck5", bottleneck5()),
        ("wheel5", wheel5()),
    ] {
        assert_trajectory_matches(
            &fixtures().rg_cheeger_n5,
            &graph,
            graph_name,
            &signal,
            rg_trajectory_cheeger,
        );
    }
}

#[test]
fn modularity_iterated_rg_n5_matches_lean() {
    let signal = signal_signature5();
    for (graph_name, graph) in [
        ("uni_k5", uni_k5()),
        ("asym_k5", asym_k5()),
        ("near_path5", near_path5()),
        ("bottleneck5", bottleneck5()),
        ("wheel5", wheel5()),
    ] {
        assert_trajectory_matches(
            &fixtures().rg_modularity_n5,
            &graph,
            graph_name,
            &signal,
            rg_trajectory_modularity,
        );
    }
}

#[test]
fn signal_preserving_iterated_rg_n5_matches_lean() {
    let signal = signal_signature5();
    for (graph_name, graph) in [
        ("uni_k5", uni_k5()),
        ("asym_k5", asym_k5()),
        ("near_path5", near_path5()),
        ("bottleneck5", bottleneck5()),
        ("wheel5", wheel5()),
    ] {
        assert_trajectory_matches(
            &fixtures().rg_signal_preserving_n5,
            &graph,
            graph_name,
            &signal,
            rg_trajectory_signal_preserving,
        );
    }
}

fn node(id: &str) -> crate::NodeId {
    crate::NodeId::new(id).unwrap()
}
