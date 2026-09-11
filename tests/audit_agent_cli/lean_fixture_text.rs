//! Text-level fixture correspondence helpers; evaluated parity is checked separately.

use super::{audit_agent_bundle, committed_graph_value};
use serde_json::Value;
use std::fs;

fn assert_theorem_file_text_matches_graph(
    lean_path: &str,
    theorem_lean_path: &str,
    graph_constant: &str,
    graph_bound_theorems: &[&str],
    graph: &Value,
) {
    let lean = fs::read_to_string(lean_path).unwrap();
    let theorem_lean = if theorem_lean_path == lean_path {
        lean.clone()
    } else {
        fs::read_to_string(theorem_lean_path).unwrap()
    };
    for theorem in graph_bound_theorems {
        assert_theorem_statement_mentions_graph(
            theorem_lean_path,
            &theorem_lean,
            theorem,
            graph_constant,
        );
    }

    let nodes = graph["nodes"].as_object().unwrap();
    for (node_id, node) in nodes {
        let binary = node["Binary"].as_object().unwrap();
        assert!(
            lean.contains(&format!(".binary {node_id:?}")),
            "Lean fixture {lean_path} is missing binary node {node_id}"
        );
        let name = binary["name"].as_str().unwrap();
        assert!(
            lean.contains(&format!("{name:?}")),
            "Lean fixture {lean_path} is missing node name {name}"
        );
        for gate in binary["gates"].as_array().unwrap() {
            assert_lean_contains_gate(lean_path, &lean, gate);
        }
    }

    for edge in graph["edges"].as_array().unwrap() {
        let from = edge["from"].as_str().unwrap();
        let to = edge["to"].as_str().unwrap();
        let snippet =
            format!("{{ fromNode := {from:?}, toNode := {to:?}, transform := .passThrough }}");
        assert!(
            lean.contains(&snippet),
            "Lean fixture {lean_path} is missing edge {from} -> {to}"
        );
    }
}

fn assert_theorem_statement_mentions_graph(
    lean_path: &str,
    lean: &str,
    theorem: &str,
    graph_constant: &str,
) {
    let statement = theorem_statement(lean, theorem)
        .unwrap_or_else(|| panic!("Lean fixture {lean_path} is missing theorem {theorem}"));
    assert!(
        statement.contains(graph_constant),
        "theorem {theorem} in {lean_path} does not mention graph constant {graph_constant}"
    );
}

fn theorem_statement<'a>(lean: &'a str, theorem: &str) -> Option<&'a str> {
    let declaration = format!("theorem {theorem}");
    let start = lean.find(&declaration)?;
    let rest = &lean[start..];
    let end = rest.find(":= by")?;
    Some(&rest[..end])
}

fn assert_lean_contains_gate(lean_path: &str, lean: &str, gate: &Value) {
    let gate = gate.as_object().unwrap();
    let (kind, payload) = gate.iter().next().unwrap();
    let snippet = match kind.as_str() {
        "ExactMatch" => {
            let value = payload["value"].as_str().unwrap();
            let decision = lean_decision(payload["decision"].as_str().unwrap());
            format!(".exactMatch {value:?} {decision}")
        }
        "ThresholdGate" => {
            let field = payload["field"].as_str().unwrap();
            let min = payload["min"].as_f64().unwrap();
            let min = if min.fract() == 0.0 {
                format!("{}", min as i64)
            } else {
                min.to_string()
            };
            let decision = lean_decision(payload["decision"].as_str().unwrap());
            format!(".thresholdGate {field:?} {min} {decision}")
        }
        other => panic!("binding test does not yet render {other} gates"),
    };
    assert!(
        lean.contains(&snippet),
        "Lean fixture {lean_path} is missing gate {snippet}"
    );
}

fn lean_decision(decision: &str) -> &'static str {
    match decision {
        "Permit" => ".permit",
        "Deny" => ".deny",
        "Escalate" => ".escalate",
        other => panic!("unknown graph decision {other}"),
    }
}

pub(super) fn assert_audit_agent_graph_text_matches_lean_fixture_constant(
    target: &str,
    source_path: &str,
    graph_path: &str,
    lean_path: &str,
    graph_constant: &str,
    graph_bound_theorems: &[&str],
) {
    let bundle = audit_agent_bundle(target, source_path);
    let emitted = bundle["extracted_governance_graph"].clone();
    let committed = committed_graph_value(graph_path);
    assert_eq!(
        emitted, committed,
        "audit-agent extract-mode graph for {target} drifted from committed fixture"
    );
    let theorem_lean_path = bundle["lean"]["file_path"]
        .as_str()
        .expect("audit-agent bundle should include lean.file_path");
    assert_theorem_file_text_matches_graph(
        lean_path,
        theorem_lean_path,
        graph_constant,
        graph_bound_theorems,
        &committed,
    );
}
