//! Tests for the graph policy parser.

use legitimacy::GovernanceClaim;
use legitimacy::{
    Decision, EdgeTransform, GateLogic, GovernanceNode, NodeId,
    policy::{load_graph_str, parse_graph_str},
    traverse,
};
use std::collections::BTreeMap;

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

const CODEX_GOVERNANCE_V2: &str = r#"
[graph]
name = "codex-governance"
version = "1.0"

[[nodes]]
id = "exec-policy"
type = "binary"
default = "permit"
combination = "first_match"

[[nodes.gates]]
type = "threshold_gate"
field = "policy_strictness"
min = 0.7
decision = "deny"

[[nodes.gates]]
type = "threshold_gate"
field = "policy_strictness"
min = 0.3
decision = "escalate"

[[nodes]]
id = "guardian"
type = "binary"
default = "permit"
combination = "first_match"

[[nodes.gates]]
type = "content_match"
regex = "rm\\s+-rf|sudo\\s"
decision = "deny"

[[edges]]
from = "exec-policy"
to = "guardian"
transform = "pass_through"
"#;

const THRESHOLD_GRAPH_V2: &str = r#"
[graph]
name = "trust-gate"
version = "0.1"

[[nodes]]
id = "trust"
type = "threshold"
threshold = 0.6
field = "strength"
"#;

fn claim(id: &str, policy_strictness: f64, content: Option<&str>) -> GovernanceClaim {
    let mut metrics = BTreeMap::new();
    metrics.insert("policy_strictness".to_string(), policy_strictness);
    GovernanceClaim {
        claimant_id: id.to_string(),
        strength: 1.0,
        priority_class: None,
        path: None,
        action: None,
        content: content.map(|s| s.to_string()),
        metrics,
    }
}

// ---------------------------------------------------------------------------
// Parsing tests
// ---------------------------------------------------------------------------

#[test]
fn parse_codex_graph_from_toml() {
    let spec = parse_graph_str(CODEX_GOVERNANCE_V2).unwrap();
    assert_eq!(spec.graph.name, "codex-governance");
    assert_eq!(spec.graph.version, "1.0");
    assert_eq!(spec.nodes.len(), 2);
    assert_eq!(spec.edges.len(), 1);

    let exec = &spec.nodes[0];
    assert_eq!(exec.id, "exec-policy");
    assert_eq!(exec.node_type, "binary");
    assert_eq!(exec.gates.len(), 2);

    let guardian = &spec.nodes[1];
    assert_eq!(guardian.id, "guardian");
    assert_eq!(guardian.gates.len(), 1);

    let edge = &spec.edges[0];
    assert_eq!(edge.from, "exec-policy");
    assert_eq!(edge.to, "guardian");
    assert_eq!(edge.transform, "pass_through");
}

#[test]
fn parse_threshold_node() {
    let spec = parse_graph_str(THRESHOLD_GRAPH_V2).unwrap();
    assert_eq!(spec.nodes.len(), 1);
    let node = &spec.nodes[0];
    assert_eq!(node.node_type, "threshold");
    assert_eq!(node.threshold, Some(0.6));
    assert_eq!(node.field, Some("strength".to_string()));
}

#[test]
fn load_graph_parses_claim_modification_edges() {
    let graph = load_graph_str(
        r#"
[graph]
name = "trust-loop"
version = "0.1"

[[nodes]]
id = "a"
type = "threshold"
threshold = 0.5
field = "strength"

[[nodes]]
id = "b"
type = "binary"
default = "deny"
combination = "first_match"

[[edges]]
from = "a"
to = "b"
transform = "claim_modification"
delta = 0.1
"#,
    )
    .unwrap();

    assert_eq!(graph.edges.len(), 1);
    assert_eq!(
        graph.edges[0].transform,
        EdgeTransform::ClaimModification { delta: 0.1 }
    );
}

// ---------------------------------------------------------------------------
// Compilation / validation tests
// ---------------------------------------------------------------------------

#[test]
fn load_codex_graph_produces_valid_governance_graph() {
    let graph = load_graph_str(CODEX_GOVERNANCE_V2).unwrap();
    assert_eq!(graph.nodes.len(), 2);
    assert_eq!(graph.edges.len(), 1);

    assert!(
        graph
            .nodes
            .contains_key(&NodeId::new("exec-policy").unwrap())
    );
    assert!(graph.nodes.contains_key(&NodeId::new("guardian").unwrap()));

    let exec = &graph.nodes[&NodeId::new("exec-policy").unwrap()];
    assert!(matches!(
        exec,
        GovernanceNode::Binary {
            combination: GateLogic::FirstMatch,
            ..
        }
    ));
}

#[test]
fn load_graph_rejects_undeclared_edge_endpoint() {
    let bad = r#"
[graph]
name = "bad"
version = "1.0"

[[nodes]]
id = "a"
type = "binary"
default = "permit"
combination = "first_match"

[[edges]]
from = "a"
to = "b-does-not-exist"
transform = "pass_through"
"#;
    let result = load_graph_str(bad);
    assert!(
        result.is_err(),
        "Expected error for undeclared edge endpoint"
    );
}

#[test]
fn load_graph_rejects_duplicate_node_ids() {
    let bad = r#"
[graph]
name = "bad"
version = "1.0"

[[nodes]]
id = "dupe"
type = "binary"
default = "permit"
combination = "first_match"

[[nodes]]
id = "dupe"
type = "binary"
default = "deny"
combination = "first_match"
"#;
    let result = load_graph_str(bad);
    assert!(result.is_err(), "Expected error for duplicate node id");
}

#[test]
fn load_graph_rejects_unknown_node_type() {
    let bad = r#"
[graph]
name = "bad"
version = "1.0"

[[nodes]]
id = "x"
type = "proportional"
default = "permit"
combination = "first_match"
"#;
    let result = load_graph_str(bad);
    assert!(result.is_err(), "Expected error for unsupported node type");
}

#[test]
fn load_graph_rejects_unknown_transform() {
    let bad = r#"
[graph]
name = "bad"
version = "1.0"

[[nodes]]
id = "a"
type = "binary"
default = "permit"
combination = "first_match"

[[nodes]]
id = "b"
type = "binary"
default = "permit"
combination = "first_match"

[[edges]]
from = "a"
to = "b"
transform = "teleportation"
"#;
    let result = load_graph_str(bad);
    assert!(result.is_err(), "Expected error for unknown transform");
}

#[test]
fn load_graph_rejects_unknown_gate_type() {
    let bad = r#"
[graph]
name = "bad"
version = "1.0"

[[nodes]]
id = "x"
type = "binary"
default = "permit"
combination = "first_match"

[[nodes.gates]]
type = "magic_gate"
decision = "permit"
"#;
    let result = load_graph_str(bad);
    assert!(result.is_err(), "Expected error for unknown gate type");
}

// ---------------------------------------------------------------------------
// End-to-end: traverse the loaded graph
// ---------------------------------------------------------------------------

#[test]
fn codex_graph_from_toml_traversal_matches_hand_built() {
    let graph = load_graph_str(CODEX_GOVERNANCE_V2).unwrap();
    let claims = vec![
        claim("auto_permit", 0.1, None),
        claim("escalate_safe", 0.5, Some("ls /tmp")),
        claim("escalate_dangerous", 0.5, Some("rm -rf /tmp")),
        claim("forbidden", 0.9, None),
    ];
    let result = traverse(&graph, &claims).unwrap();

    assert_eq!(result.final_decisions["auto_permit"], Decision::Permit);
    assert_eq!(result.final_decisions["escalate_safe"], Decision::Permit);
    assert_eq!(result.final_decisions["escalate_dangerous"], Decision::Deny);
    assert_eq!(result.final_decisions["forbidden"], Decision::Deny);
}

#[test]
fn threshold_graph_from_toml_permits_above_threshold() {
    let graph = load_graph_str(THRESHOLD_GRAPH_V2).unwrap();
    let claims = vec![
        GovernanceClaim {
            claimant_id: "strong".to_string(),
            strength: 0.8,
            priority_class: None,
            path: None,
            action: None,
            content: None,
            metrics: BTreeMap::new(),
        },
        GovernanceClaim {
            claimant_id: "weak".to_string(),
            strength: 0.3,
            priority_class: None,
            path: None,
            action: None,
            content: None,
            metrics: BTreeMap::new(),
        },
    ];
    let result = traverse(&graph, &claims).unwrap();
    assert_eq!(result.final_decisions["strong"], Decision::Permit);
    assert_eq!(result.final_decisions["weak"], Decision::Deny);
}
