use legitimacy::{
    Decision, ExtractionOptions, Gate, GovernanceGraph, GovernanceNode, RecognizedNodeProvenance,
    extract::{ExtractionMode, parse_python_hook_core},
    extract_governance_artifacts,
};
use std::{
    fs,
    path::{Path, PathBuf},
    time::{SystemTime, UNIX_EPOCH},
};

const CLAUDE_TYPES: &str = "audits/fixtures/sources/leaderboard/claude-agent-sdk-hooks/claude-agent-sdk-python/src/claude_agent_sdk/types.py";

fn unique_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-python-hook-core-{label}-{nanos}"))
}

fn write_source(root: &Path, source: &str) {
    fs::create_dir_all(root).unwrap();
    fs::write(root.join("hooks.py"), source).unwrap();
}

fn theorem_options() -> ExtractionOptions {
    ExtractionOptions {
        allow_partial: false,
        mode: ExtractionMode::TheoremBacked,
    }
}

#[test]
fn theorem_backed_python_core_ignores_misleading_comments_and_docstrings() {
    let root = unique_dir("misleading-literals");
    write_source(
        &root,
        r#"
"""This docstring mentions "block" and "deny" but is not a typed decision."""
# A comment saying "allow" must not produce a decision gate.
from typing import Literal, NotRequired, TypedDict

PermissionBehavior = Literal["allow", "deny", "ask"]

class PreToolUseHookSpecificOutput(TypedDict):
    hookEventName: Literal["PreToolUse"]
    permissionDecision: NotRequired[Literal["allow", "deny", "ask"]]
"#,
    );

    let graph = extract_governance_artifacts(&root, theorem_options())
        .expect("typed literals should extract")
        .graph;
    let gate_values = exact_gate_values(&graph);
    assert!(gate_values.contains(&"allow".to_string()));
    assert!(gate_values.contains(&"deny".to_string()));
    assert!(gate_values.contains(&"ask".to_string()));
    assert!(
        !gate_values.contains(&"block".to_string()),
        "docstring/comment literals must not become graph gates: {gate_values:?}"
    );
}

#[test]
fn theorem_backed_python_core_rejects_substring_class_markers() {
    for source in [
        r#"
# dataclass appears only in a comment, not as an anchored decorator.
class Plain:
    decision: str
"#,
        r#"
class Plain(NotTypedDict):
    decision: str
"#,
        r#"
class Plain(NotBaseModel):
    decision: str
"#,
        r#"
class Plain(NotEnum):
    ALLOW = "allow"
"#,
    ] {
        let error = parse_python_hook_core(source).expect_err("substring marker must reject");
        assert!(error.to_string().contains("is not a dataclass"), "{error}");
    }
}

#[test]
fn theorem_backed_python_core_rejects_substring_decision_annotations() {
    let source = r#"
def guard(action: str) -> NotLiteral["allow", "deny"]:
    return "allow"
"#;

    let error = parse_python_hook_core(source).expect_err("NotLiteral must not type decisions");
    assert!(
        error
            .to_string()
            .contains("without a typed decision annotation"),
        "{error}"
    );
}

#[test]
fn theorem_backed_python_core_rejects_substring_registration_decorators() {
    let source = r#"
from typing import Literal

@not_register("PreToolUse")
def guard(action: str) -> Literal["allow", "deny"]:
    return "deny"
"#;

    let ast = parse_python_hook_core(source).expect("typed callback should parse");
    assert!(
        ast.registrations.is_empty(),
        "substring decorator must not create registrations: {:?}",
        ast.registrations
    );
}

#[test]
fn theorem_backed_python_core_discovers_renamed_decision_fields_from_types() {
    let source = r#"
from typing import Literal, NotRequired, TypedDict

PermissionBehavior = Literal["allow", "deny"]

class PreToolUseHookSpecificOutput(TypedDict):
    hookEventName: Literal["PreToolUse"]
    permission_choice: NotRequired[PermissionBehavior]
"#;

    let ast = parse_python_hook_core(source).expect("decision alias field should parse");
    let field = ast
        .schemas
        .iter()
        .find(|schema| schema.name == "PreToolUseHookSpecificOutput")
        .and_then(|schema| {
            schema
                .fields
                .iter()
                .find(|field| field.name == "permission_choice")
        })
        .expect("renamed decision field should be present");
    assert!(
        field.decision_position,
        "renamed decision field should be auto-discovered"
    );
}

#[test]
fn theorem_backed_python_core_discovers_new_registration_events_from_structure() {
    let source = r#"
from typing import Literal

FORMAL_REGISTRY = {"NewAuditEvent": [guard]}

def guard(action: str) -> Literal["allow", "deny"]:
    return "deny"
"#;

    let ast = parse_python_hook_core(source).expect("structured registry should parse");
    assert!(
        ast.registrations
            .iter()
            .any(|registration| registration.event == "NewAuditEvent"
                && registration.callback == "guard"),
        "new event should be discovered from registration structure: {:?}",
        ast.registrations
    );
}

#[test]
fn theorem_backed_python_core_supports_unicode_registration_identifiers() {
    let source = r#"
from typing import Literal

HOOKS = {"PreToolUse": [φύλακας]}

def φύλακας(action: str) -> Literal["allow", "deny"]:
    return "allow"
"#;

    let ast = parse_python_hook_core(source).expect("Unicode callback should parse");
    assert!(
        ast.callbacks
            .iter()
            .any(|callback| callback.name == "φύλακας"),
        "Unicode callback should be collected: {:?}",
        ast.callbacks
    );
    assert!(
        ast.registrations
            .iter()
            .any(|registration| registration.callback == "φύλακας"),
        "Unicode callback registration should be collected: {:?}",
        ast.registrations
    );
}

#[test]
fn theorem_backed_python_core_ignores_semantically_dead_returns() {
    let root = unique_dir("dead-code");
    write_source(
        &root,
        r#"
from typing import Literal

HOOKS = {"PreToolUse": [guard]}

def guard(action: str) -> Literal["allow", "deny"]:
    return "allow"
    return "deny"
"#,
    );

    let graph = extract_governance_artifacts(&root, theorem_options())
        .expect("dead code after return should extract")
        .graph;
    let callback = binary_node(&graph, "hooks.py::guard");
    let gate_values = callback
        .iter()
        .filter_map(|gate| match gate {
            Gate::ExactMatch { value, .. } => Some(value.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(gate_values, vec!["allow".to_string()]);
}

#[test]
fn theorem_backed_python_core_rejects_shadowed_registered_callbacks() {
    let source = r#"
from typing import Literal

def guard(action: str) -> Literal["allow", "deny"]:
    return "deny"

guard = "not a callback"
HOOKS = {"PreToolUse": [guard]}
"#;

    let error = parse_python_hook_core(source).expect_err("shadowed callback must reject");
    assert!(error.to_string().contains("shadowed"), "{error}");
}

#[test]
fn theorem_backed_python_core_equivalent_refactors_have_the_same_graph() {
    let left = unique_dir("refactor-left");
    let right = unique_dir("refactor-right");
    write_source(
        &left,
        r#"
from typing import Literal
HOOKS = {"PreToolUse": [guard]}
def guard(action: str) -> Literal["allow", "deny"]:
    if action == "read":
        return "allow"
    return "deny"
"#,
    );
    write_source(
        &right,
        r#"
from typing import Literal
HOOKS = {"PreToolUse": [guard]}
def guard(action: str) -> Literal["allow", "deny"]:
    if action != "read":
        return "deny"
    else:
        return "allow"
"#,
    );

    let left_graph = extract_governance_artifacts(&left, theorem_options())
        .expect("left refactor should extract")
        .graph;
    let right_graph = extract_governance_artifacts(&right, theorem_options())
        .expect("right refactor should extract")
        .graph;
    assert_eq!(left_graph, right_graph);
}

#[test]
fn theorem_backed_python_core_materializes_direct_callback_edges() {
    let root = unique_dir("callback-edges");
    write_source(
        &root,
        r#"
from typing import Literal
HOOKS = {"PreToolUse": [outer, inner]}

def inner(action: str) -> Literal["allow", "deny"]:
    return "deny"

def outer(action: str) -> Literal["allow", "deny"]:
    if inner(action) == "deny":
        return "deny"
    return "allow"
"#,
    );

    let graph = extract_governance_artifacts(&root, theorem_options())
        .expect("registered callbacks should extract")
        .graph;
    assert!(
        graph
            .edges
            .iter()
            .any(|edge| edge.from.to_string() == "hooks.py::outer"
                && edge.to.to_string() == "hooks.py::inner"),
        "expected direct callback edge, got {:?}",
        graph.edges
    );
}

#[test]
fn theorem_backed_python_core_reports_real_source_spans() {
    let root = unique_dir("source-spans");
    write_source(
        &root,
        r#"from typing import Literal, NotRequired, TypedDict

PermissionBehavior = Literal[
    "allow",
    "deny",
]

HOOKS = {
    "PreToolUse": [
        guard,
    ],
}

class PreToolUseHookSpecificOutput(TypedDict):
    hookEventName: Literal["PreToolUse"]
    permissionDecision: NotRequired[
        Literal["allow", "deny", "ask"]
    ]

def guard(action: str) -> Literal["allow", "deny"]:
    if action == "write":
        return "deny"
    return "allow"
"#,
    );

    let artifacts =
        extract_governance_artifacts(&root, theorem_options()).expect("spans should extract");

    assert_eq!(
        node_span(&artifacts.recognized_nodes, "hooks.py::PermissionBehavior"),
        Some((3, 6))
    );
    assert_eq!(
        node_span(
            &artifacts.recognized_nodes,
            "hooks.py::PreToolUseHookSpecificOutput"
        ),
        Some((14, 18))
    );
    assert_eq!(
        node_span(
            &artifacts.recognized_nodes,
            "hooks.py::registration::PreToolUse::guard"
        ),
        Some((8, 12))
    );
    assert_eq!(
        node_span(&artifacts.recognized_nodes, "hooks.py::guard"),
        Some((20, 23))
    );
}

#[test]
fn theorem_backed_python_core_registration_span_ignores_misleading_assignment_text() {
    let root = unique_dir("source-span-misleading-text");
    write_source(
        &root,
        r#"from typing import Literal

SPAN_NOTE = "PreToolUse guard appears here only as text"

HOOKS = {
    "PreToolUse": [guard],
}

def guard(action: str) -> Literal["allow", "deny"]:
    return "allow"
"#,
    );

    let artifacts =
        extract_governance_artifacts(&root, theorem_options()).expect("spans should extract");

    assert_eq!(
        node_span(
            &artifacts.recognized_nodes,
            "hooks.py::registration::PreToolUse::guard"
        ),
        Some((5, 7))
    );
}

#[test]
fn theorem_backed_python_core_covers_claude_agent_sdk_types_fixture() {
    let root = unique_dir("claude-types");
    fs::create_dir_all(&root).unwrap();
    fs::copy(CLAUDE_TYPES, root.join("types.py")).unwrap();

    let artifacts = extract_governance_artifacts(&root, theorem_options())
        .expect("Claude Agent SDK types.py should fit PythonHookCore");
    let nodes = artifacts
        .graph
        .nodes
        .keys()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    assert!(
        nodes
            .iter()
            .any(|node| node == "types.py::PreToolUseHookSpecificOutput"),
        "expected verified PreToolUse schema node, got {nodes:?}"
    );
    assert!(
        artifacts.recognized_nodes.iter().any(|node| node
            .rationale
            .iter()
            .any(|line| line.contains("extractPythonHookCore_decision_equivalent"))),
        "expected theorem-backed rationale, got {:?}",
        artifacts.recognized_nodes
    );
    let pre_tool_use = binary_node(&artifacts.graph, "types.py::PreToolUseHookSpecificOutput");
    let ask_decision = pre_tool_use.iter().find_map(|gate| match gate {
        Gate::ExactMatch { value, decision } if value == "ask" => Some(decision),
        _ => None,
    });
    assert_eq!(
        ask_decision,
        Some(&Decision::Escalate),
        "Claude SDK ask must normalize to canonical escalation semantics"
    );
}

fn exact_gate_values(graph: &GovernanceGraph) -> Vec<String> {
    graph
        .nodes
        .values()
        .flat_map(|node| match node {
            GovernanceNode::Binary { gates, .. } => gates
                .iter()
                .filter_map(|gate| match gate {
                    Gate::ExactMatch { value, .. } => Some(value.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>(),
            _ => Vec::new(),
        })
        .collect()
}

fn binary_node<'a>(graph: &'a GovernanceGraph, id: &str) -> &'a [Gate] {
    let node = graph
        .nodes
        .iter()
        .find(|(node_id, _)| node_id.to_string() == id)
        .map(|(_, node)| node)
        .unwrap_or_else(|| panic!("missing node {id}: {:?}", graph.nodes.keys()));
    match node {
        GovernanceNode::Binary { gates, .. } => gates,
        _ => panic!("expected binary node"),
    }
}

fn node_span(nodes: &[RecognizedNodeProvenance], node_id: &str) -> Option<(usize, usize)> {
    nodes
        .iter()
        .find(|node| node.node_id == node_id)
        .map(|node| (node.line_start, node.line_end))
}
