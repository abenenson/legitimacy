use legitimacy::{
    Decision, ExtractionOptions, Gate, GovernanceGraph, GovernanceNode, RecognizedNodeProvenance,
    extract::ExtractionMode, extract_governance_artifacts,
};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    time::{SystemTime, UNIX_EPOCH},
};

fn unique_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-decision-conformance-{label}-{nanos}"))
}

fn write_source(root: &Path, name: &str, source: &str) {
    fs::create_dir_all(root).unwrap();
    fs::write(root.join(name), source).unwrap();
}

fn theorem_options() -> ExtractionOptions {
    ExtractionOptions {
        allow_partial: false,
        mode: ExtractionMode::TheoremBacked,
    }
}

#[test]
fn python_hook_core_conformance_maps_supported_escalation_literals() {
    let root = unique_dir("python-hook-core");
    write_source(
        &root,
        "hooks.py",
        r#"
from typing import Literal, NotRequired, TypedDict

PermissionBehavior = Literal["allow", "deny", "ask", "defer", "review"]

class PreToolUseHookSpecificOutput(TypedDict):
    hookEventName: Literal["PreToolUse"]
    permissionDecision: NotRequired[PermissionBehavior]
"#,
    );

    let artifacts = extract_governance_artifacts(&root, theorem_options())
        .expect("PythonHookCore conformance fixture should extract");
    assert_has_lean_rationale(
        &artifacts.recognized_nodes,
        "hooks.py::PermissionBehavior",
        "extractPythonHookCore_decision_equivalent",
    );
    let decisions = exact_gate_decisions(&artifacts.graph, "hooks.py::PermissionBehavior");

    assert_eq!(decisions.get("allow"), Some(&Decision::Permit));
    assert_eq!(decisions.get("deny"), Some(&Decision::Deny));
    assert_eq!(decisions.get("ask"), Some(&Decision::Escalate));
    assert_eq!(decisions.get("defer"), Some(&Decision::Escalate));
    assert!(
        !decisions.contains_key("review"),
        "PythonHookCore does not currently expose 'review' as a core decision literal; \
         follow-up implementation work is needed before asserting review -> Escalate: {decisions:?}"
    );
}

#[test]
fn typescript_approval_core_conformance_maps_escalation_literals() {
    let root = unique_dir("typescript-approval-core");
    write_source(
        &root,
        "approval.ts",
        r#"
export type Approval = "allow" | "deny" | "ask" | "review" | "defer" | "escalate";
"#,
    );

    let artifacts = extract_governance_artifacts(&root, theorem_options())
        .expect("TypeScriptApprovalCore conformance fixture should extract");
    assert_has_lean_rationale(
        &artifacts.recognized_nodes,
        "approval.ts::Approval",
        "extractTypeScriptApprovalCore_decision_equivalent",
    );
    let decisions = exact_gate_decisions(&artifacts.graph, "approval.ts::Approval");

    assert_eq!(decisions.get("allow"), Some(&Decision::Permit));
    assert_eq!(decisions.get("deny"), Some(&Decision::Deny));
    for literal in ["ask", "review", "defer", "escalate"] {
        assert_eq!(
            decisions.get(literal),
            Some(&Decision::Escalate),
            "TypeScriptApprovalCore should normalize {literal:?} to Escalate: {decisions:?}"
        );
    }
}

#[test]
fn generic_heuristic_conformance_maps_python_protocol_schema_literals() {
    let root = unique_dir("generic-heuristic");
    write_source(
        &root,
        "policy.py",
        r#"
from typing import Literal, TypedDict

class PermissionDecisionOptions(TypedDict):
    permissionDecision: Literal["allow", "deny", "ask", "review", "defer", "escalate"]
"#,
    );

    let artifacts = extract_governance_artifacts(&root, ExtractionOptions::default())
        .expect("generic heuristic conformance fixture should extract");
    let decisions = exact_gate_decisions(&artifacts.graph, "policy.py::PermissionDecisionOptions");

    assert_eq!(decisions.get("allow"), Some(&Decision::Permit));
    assert_eq!(decisions.get("deny"), Some(&Decision::Deny));
    for literal in ["ask", "review", "defer", "escalate"] {
        assert_eq!(
            decisions.get(literal),
            Some(&Decision::Escalate),
            "generic heuristic extractor should normalize {literal:?} to Escalate: {decisions:?}"
        );
    }
}

fn exact_gate_decisions(graph: &GovernanceGraph, node_id: &str) -> BTreeMap<String, Decision> {
    let node = graph
        .nodes
        .iter()
        .find(|(id, _)| id.to_string() == node_id)
        .map(|(_, node)| node)
        .unwrap_or_else(|| panic!("missing node {node_id}: {:?}", graph.nodes.keys()));
    let GovernanceNode::Binary { gates, .. } = node else {
        panic!("expected binary node {node_id}");
    };

    gates
        .iter()
        .filter_map(|gate| match gate {
            Gate::ExactMatch { value, decision } => Some((value.clone(), decision.clone())),
            _ => None,
        })
        .collect()
}

fn assert_has_lean_rationale(nodes: &[RecognizedNodeProvenance], node_id: &str, theorem: &str) {
    let node = nodes
        .iter()
        .find(|node| node.node_id == node_id)
        .unwrap_or_else(|| panic!("missing recognized node {node_id}: {nodes:?}"));
    assert!(
        node.rationale.iter().any(|line| line.contains(theorem)),
        "expected {node_id} rationale to cite {theorem}: {:?}",
        node.rationale
    );
}
