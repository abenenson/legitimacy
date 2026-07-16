use legitimacy::{
    Decision, GateLogic, GovernanceGraph, GovernanceNode, NodeId, ast_theorem_witness,
    canonical_ast_fingerprint, verify_ast_theorem_witness,
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
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}"))
}

fn write_source(root: &Path, body: &str) {
    fs::create_dir_all(root).unwrap();
    fs::write(root.join("policy.py"), body).unwrap();
}

fn graph_with_node(id: &str) -> GovernanceGraph {
    let node_id = NodeId::new(id).unwrap();
    let mut nodes = BTreeMap::new();
    nodes.insert(
        node_id.clone(),
        GovernanceNode::Binary {
            id: node_id,
            name: id.to_string(),
            gates: Vec::new(),
            default: Decision::Permit,
            combination: GateLogic::FirstMatch,
        },
    );
    GovernanceGraph {
        nodes,
        edges: Vec::new(),
    }
}

#[test]
fn canonical_ast_hash_changes_when_the_parsed_tree_changes() {
    let root = unique_dir("ast-hash");
    write_source(&root, "def approve(claim):\n    return True\n");
    let (first, files) = canonical_ast_fingerprint(&root).unwrap();
    assert_eq!(files.len(), 1);
    assert_eq!(files[0].path, "policy.py");

    write_source(
        &root,
        "def approve(claim):\n    if claim:\n        return True\n    return False\n",
    );
    let (second, _) = canonical_ast_fingerprint(&root).unwrap();
    assert_ne!(first, second);

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn canonical_ast_hash_changes_when_bound_tokens_change() {
    let root = unique_dir("ast-token-hash");
    write_source(&root, "def approve(claim):\n    return claim == 'permit'\n");
    let (first, _) = canonical_ast_fingerprint(&root).unwrap();

    write_source(
        &root,
        "def approve(request):\n    return request == 'permit'\n",
    );
    let (renamed_identifier, _) = canonical_ast_fingerprint(&root).unwrap();
    assert_ne!(first, renamed_identifier);

    write_source(&root, "def approve(claim):\n    return claim == 'deny'\n");
    let (changed_literal, _) = canonical_ast_fingerprint(&root).unwrap();
    assert_ne!(first, changed_literal);

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn canonical_ast_hash_ignores_whitespace_and_comment_only_changes() {
    let root = unique_dir("ast-whitespace-hash");
    write_source(&root, "def approve(claim):\n    return claim == 'permit'\n");
    let (first, _) = canonical_ast_fingerprint(&root).unwrap();

    write_source(
        &root,
        "# explanatory comment changed\r\ndef approve(claim):  \r\n    return claim == 'permit'\t\r\n",
    );
    let (whitespace_and_comment, _) = canonical_ast_fingerprint(&root).unwrap();
    assert_eq!(first, whitespace_and_comment);

    fs::remove_dir_all(root).unwrap();
}

#[test]
fn theorem_witness_verification_binds_source_ast_and_graph_hashes() {
    let root = unique_dir("ast-witness");
    write_source(&root, "def approve(claim):\n    return True\n");

    let graph = graph_with_node("review");
    let witness = ast_theorem_witness(&root, &graph, "review_witness").unwrap();
    let verification = verify_ast_theorem_witness(&witness, &root, &graph).unwrap();
    assert!(verification.witness_valid);

    let drifted_graph = graph_with_node("other_review");
    let drifted = verify_ast_theorem_witness(&witness, &root, &drifted_graph).unwrap();
    assert!(!drifted.witness_valid);
    assert_ne!(
        drifted.expected_governance_graph_hash,
        drifted.actual_governance_graph_hash
    );

    fs::remove_dir_all(root).unwrap();
}
