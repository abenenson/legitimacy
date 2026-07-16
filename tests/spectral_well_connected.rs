use legitimacy::{
    Decision, EdgeTransform, GateLogic, GovernanceGraph, GovernanceNode, GraphBuilder, NodeId,
    spectral::{
        Rational,
        concrete_graphs::{asym_k5, bottleneck5, near_path5, signal_signature5, uni_k5, wheel5},
        connected_component_count, cv, spectral_gap, weights,
    },
};
use std::{
    fs,
    path::PathBuf,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

fn unique_path(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}.graph.toml"))
}

fn ratio_to_f64(value: Rational) -> f64 {
    *value.numer() as f64 / *value.denom() as f64
}

fn graph_toml(graph: &GovernanceGraph, name: &str) -> String {
    let mut node_ids = graph
        .nodes
        .keys()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    node_ids.sort();

    let mut edges = graph
        .edges
        .iter()
        .map(|edge| {
            (
                edge.from.to_string(),
                edge.to.to_string(),
                match &edge.transform {
                    EdgeTransform::PassThrough => ("pass_through".to_string(), None),
                    EdgeTransform::ClaimModification { delta } => {
                        ("claim_modification".to_string(), Some(*delta))
                    }
                },
            )
        })
        .collect::<Vec<_>>();
    edges.sort_by(|left, right| left.0.cmp(&right.0).then(left.1.cmp(&right.1)));

    let mut document = format!("[graph]\nname = \"{name}\"\nversion = \"1.0\"\n\n");
    for node_id in node_ids {
        document.push_str("[[nodes]]\n");
        document.push_str(&format!("id = \"{node_id}\"\n"));
        document.push_str("type = \"binary\"\n");
        document.push_str("default = \"deny\"\n");
        document.push_str("combination = \"first_match\"\n\n");
    }
    for (from, to, (transform, delta)) in edges {
        document.push_str("[[edges]]\n");
        document.push_str(&format!("from = \"{from}\"\n"));
        document.push_str(&format!("to = \"{to}\"\n"));
        document.push_str(&format!("transform = \"{transform}\"\n"));
        if let Some(delta) = delta {
            document.push_str(&format!("delta = {delta}\n"));
        }
        document.push('\n');
    }

    document
}

fn write_graph_policy(graph: &GovernanceGraph, name: &str) -> PathBuf {
    let path = unique_path(name);
    fs::write(&path, graph_toml(graph, name)).unwrap();
    path
}

fn single_node_graph() -> GovernanceGraph {
    GraphBuilder::new()
        .unwrap()
        .add_node(GovernanceNode::Binary {
            id: NodeId::new("solo").unwrap(),
            name: "solo".to_string(),
            gates: Vec::new(),
            default: Decision::Deny,
            combination: GateLogic::FirstMatch,
        })
        .unwrap()
        .build()
        .unwrap()
}

fn disconnected_two_pairs() -> GovernanceGraph {
    GraphBuilder::new()
        .unwrap()
        .add_node(simple_node("a"))
        .unwrap()
        .add_node(simple_node("b"))
        .unwrap()
        .add_node(simple_node("c"))
        .unwrap()
        .add_node(simple_node("d"))
        .unwrap()
        .add_edge(
            NodeId::new("a").unwrap(),
            NodeId::new("b").unwrap(),
            EdgeTransform::PassThrough,
        )
        .unwrap()
        .add_edge(
            NodeId::new("c").unwrap(),
            NodeId::new("d").unwrap(),
            EdgeTransform::PassThrough,
        )
        .unwrap()
        .build()
        .unwrap()
}

fn simple_node(id: &str) -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new(id).unwrap(),
        name: id.to_string(),
        gates: Vec::new(),
        default: Decision::Deny,
        combination: GateLogic::FirstMatch,
    }
}

fn run_cli(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args(args)
        .output()
        .unwrap()
}

#[test]
fn n5_probe_archetypes_match_reference_s_delta_values() {
    let signal = signal_signature5();
    for (name, graph, expected_lambda_2, expected_s_delta, expected_pass) in [
        ("uniK5", uni_k5(), 5.0, 3.75, true),
        ("asymK5", asym_k5(), 5.0, 6.0, true),
        (
            "nearPath5",
            near_path5(),
            0.474_326_691_0,
            0.894_956_020_8,
            true,
        ),
        ("wheel5", wheel5(), 1.2, 3.0, true),
        ("bottleneck5", bottleneck5(), 0.000_1, 0.000_199_98, false),
    ] {
        let lambda_2 = spectral_gap(&weights(&graph));
        let cv_value = cv(&graph, &signal);
        let s_delta = lambda_2 * ratio_to_f64(cv_value);

        assert!(
            (lambda_2 - expected_lambda_2).abs() <= 1e-6,
            "{name}: lambda_2 expected {expected_lambda_2}, got {lambda_2}",
        );
        assert!(
            (s_delta - expected_s_delta).abs() <= 1e-6,
            "{name}: S_delta expected {expected_s_delta}, got {s_delta}",
        );
        assert_eq!(s_delta >= 17.0 / 20.0, expected_pass, "{name}");
    }
}

#[test]
fn disconnected_carrier_reports_true_zero_fiedler_value() {
    let graph = disconnected_two_pairs();
    let graph_weights = weights(&graph);

    assert_eq!(connected_component_count(&graph_weights), 2);
    assert_eq!(spectral_gap(&graph_weights), 0.0);
}

#[test]
fn cli_spectral_well_connected_mode_uses_exit_code_two_on_failure() {
    let path = write_graph_policy(&bottleneck5(), "bottleneck5");
    let output = run_cli(&[
        "audit-graph",
        "--spectral-well-connected",
        path.to_str().unwrap(),
    ]);

    assert_eq!(output.status.code(), Some(2), "{output:?}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("SPECTRAL WELL CONNECTED"), "{stdout}");
    assert!(
        stdout.contains("SpectralWellConnected(G, s): false"),
        "{stdout}"
    );

    let _ = fs::remove_file(path);
}

#[test]
fn cli_interpret_and_normalized_gap_flags_render_new_captions() {
    let path = write_graph_policy(&near_path5(), "nearPath5");
    let output = run_cli(&[
        "audit-graph",
        "--spectral-well-connected",
        path.to_str().unwrap(),
        "--interpret",
        "--normalized-spectral-gap",
    ]);

    assert!(output.status.success(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("(= Cook's 1977 influence sup-norm over single-node deletion)"),
        "{stdout}"
    );
    assert!(
        stdout.contains("(= inverse Laplace-mechanism noise scale for delta-DP release of gov(s))"),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "(S_delta = lambda_2 x cv; >= 17/20 is cross-scale classifier cut on n=5/7/9/11/13 probe archetypes)"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("lambda_2(L_tilde):"), "{stdout}");

    let _ = fs::remove_file(path);
}

#[test]
fn cli_regular_audit_graph_can_append_paper_diagnostics() {
    let graph_path = unique_path("audit-graph-json");
    fs::write(&graph_path, serde_json::to_vec_pretty(&wheel5()).unwrap()).unwrap();

    let output = run_cli(&[
        "audit-graph",
        "--graph",
        graph_path.to_str().unwrap(),
        "--claims",
        "tests/fixtures/sample_governance_claims.jsonl",
        "--interpret",
        "--normalized-spectral-gap",
    ]);

    assert!(output.status.success(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("EXTRACTION REPORT"), "{stdout}");
    assert!(
        stdout.contains("probe signal s: ordinal node-id signature 1..5"),
        "{stdout}"
    );
    assert!(
        stdout.contains("SpectralWellConnected(G, s): true"),
        "{stdout}"
    );
    assert!(stdout.contains("lambda_2(L_tilde):"), "{stdout}");

    let _ = fs::remove_file(graph_path);
}

#[test]
fn cli_paper_diagnostics_marks_c_star_undefined_when_cv_is_zero() {
    let graph_path = unique_path("zero-cv-graph-json");
    fs::write(
        &graph_path,
        serde_json::to_vec_pretty(&single_node_graph()).unwrap(),
    )
    .unwrap();

    let output = run_cli(&[
        "audit-graph",
        "--graph",
        graph_path.to_str().unwrap(),
        "--claims",
        "tests/fixtures/sample_governance_claims.jsonl",
        "--interpret",
    ]);

    assert!(output.status.success(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("C*(G, delta=0.100): N/A"), "{stdout}");
    assert!(
        stdout.contains("undefined because the positive-CV hypothesis for C* is not met"),
        "{stdout}"
    );

    let _ = fs::remove_file(graph_path);
}

#[test]
fn cli_interpret_reports_disconnected_components_and_zero_lambda_2() {
    let path = write_graph_policy(&disconnected_two_pairs(), "twoPairs");
    let output = run_cli(&[
        "audit-graph",
        "--spectral-well-connected",
        path.to_str().unwrap(),
        "--interpret",
    ]);

    assert_eq!(output.status.code(), Some(2), "{output:?}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("connected components: 2"), "{stdout}");
    assert!(stdout.contains("lambda_2: 0.000000"), "{stdout}");
    assert!(
        stdout.contains("connected-carrier positive-gap hypothesis for C* is not met"),
        "{stdout}"
    );

    let _ = fs::remove_file(path);
}
