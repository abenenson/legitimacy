use super::{PolicyFormat, policy_format_for_input};
use crate::input::{
    ClaimCorpusInputProvenance, load_claim_corpus, load_governance_graph, load_review_overlay,
};
use legitimacy::{
    ClaimCorpusProvenance, Decision, Gate, GateLogic, GovernanceGraph, GovernanceNode,
    GraphBuilder, NodeId, OBSERVED_RUNTIME_CORPUS_SCHEMA_VERSION, ObservedRuntimeClaimRecord,
    ObservedRuntimeCorpusManifest, ObservedRuntimeCorpusPack, ObservedRuntimeRedactionMetadata,
    write_observed_runtime_corpus_pack,
};
use std::{collections::BTreeMap, fs, path::PathBuf};

fn temp_file(name: &str) -> PathBuf {
    let unique = format!(
        "legitimacy-cli-{}-{}-{}",
        std::process::id(),
        name,
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    );
    std::env::temp_dir().join(unique)
}

#[test]
fn detects_rule_files_without_graph_sections() {
    let input = r#"
[rule]
name = "promotion"
version = "1.0"
"#;

    assert_eq!(policy_format_for_input(input).unwrap(), PolicyFormat::Rule);
}

#[test]
fn detects_rule_files_when_node_markers_only_appear_in_string_values() {
    let input = r#"
[rule]
name = "contains [[nodes]] marker"
version = "1.0"
"#;

    assert_eq!(policy_format_for_input(input).unwrap(), PolicyFormat::Rule);
}

#[test]
fn detects_graph_files_from_node_sections() {
    let input = r#"
[graph]
name = "codex"
version = "1.0"

[[nodes]]
id = "entry"
type = "binary"
"#;

    assert_eq!(policy_format_for_input(input).unwrap(), PolicyFormat::Graph);
}

#[test]
fn detects_graph_files_from_graph_metadata_without_nodes() {
    let input = r#"
[graph]
name = "empty"
version = "1.0"
"#;

    assert_eq!(policy_format_for_input(input).unwrap(), PolicyFormat::Graph);
}

#[test]
fn reports_parse_errors_for_malformed_policy_input() {
    let input = "[rule\nname = \"broken\"";
    let error = policy_format_for_input(input).unwrap_err();

    assert!(error.to_string().contains("failed to parse policy"));
}

#[test]
fn loads_claim_corpus_from_json_array() {
    let path = temp_file("claims-array.json");
    fs::write(
        &path,
        r#"[{"claimant_id":"a","strength":1.0,"metrics":{"risk":1.0}}]"#,
    )
    .unwrap();

    let claims = load_claim_corpus(&path).unwrap();
    assert_eq!(claims.len(), 1);
    assert_eq!(claims[0].claimant_id, "a");

    let _ = fs::remove_file(path);
}

#[test]
fn loads_claim_corpus_from_jsonl() {
    let path = temp_file("claims.jsonl");
    fs::write(
        &path,
        "{\"claimant_id\":\"a\",\"strength\":1.0}\n{\"claimant_id\":\"b\",\"strength\":2.0,\"path\":\"/tmp/x\"}\n",
    )
    .unwrap();

    let claims = load_claim_corpus(&path).unwrap();
    assert_eq!(claims.len(), 2);
    assert_eq!(claims[1].claimant_id, "b");

    let _ = fs::remove_file(path);
}

#[test]
fn loads_claim_corpus_from_observed_runtime_records() {
    let path = temp_file("observed-runtime-claims.jsonl");
    fs::write(
        &path,
        "{\"source_kind\":\"task_complete\",\"source_event_id\":\"evt_1\",\"claim\":{\"claimant_id\":\"a\",\"strength\":1.0}}\n",
    )
    .unwrap();

    let claims = load_claim_corpus(&path).unwrap();
    assert_eq!(claims.len(), 1);
    assert_eq!(claims[0].claimant_id, "a");

    let _ = fs::remove_file(path);
}

#[test]
fn loads_claim_corpus_from_observed_runtime_pack_directory() {
    let path = temp_file("observed-runtime-pack");
    fs::create_dir_all(&path).unwrap();
    write_observed_runtime_corpus_pack(
        &path,
        &ObservedRuntimeCorpusPack {
            manifest: ObservedRuntimeCorpusManifest {
                schema_version: OBSERVED_RUNTIME_CORPUS_SCHEMA_VERSION,
                source_descriptor: "fixture".to_string(),
                source_sha256: "abc".to_string(),
                capture_timestamp: "2025-08-10T03:24:02Z".to_string(),
                redaction: ObservedRuntimeRedactionMetadata {
                    redacted_fields: vec!["claim.claimant_id".to_string()],
                    method: "sha256-truncate-12".to_string(),
                },
                claim_count: 1,
            },
            claims: vec![ObservedRuntimeClaimRecord {
                source_kind: "task_complete".to_string(),
                source_event_id: Some("evt_1".to_string()),
                observed_at: Some("2025-08-10T03:24:02Z".to_string()),
                claim: legitimacy::GovernanceClaim {
                    claimant_id: "a".to_string(),
                    strength: 1.0,
                    priority_class: Some("observed-runtime".to_string()),
                    path: None,
                    action: Some("task_complete".to_string()),
                    content: None,
                    metrics: BTreeMap::new(),
                },
            }],
        },
    )
    .unwrap();

    let claims = load_claim_corpus(&path).unwrap();
    assert_eq!(claims.len(), 1);
    assert_eq!(claims[0].claimant_id, "a");

    let _ = fs::remove_dir_all(path);
}

#[test]
fn loads_governance_graph_from_json() {
    let path = temp_file("graph.json");
    let graph: GovernanceGraph = GraphBuilder::new()
        .unwrap()
        .add_node(GovernanceNode::Binary {
            id: NodeId::new("entry").unwrap(),
            name: "entry".to_string(),
            gates: vec![Gate::ExactMatch {
                value: "approve".to_string(),
                decision: Decision::Permit,
            }],
            default: Decision::Deny,
            combination: GateLogic::FirstMatch,
        })
        .unwrap()
        .build()
        .unwrap();
    fs::write(&path, serde_json::to_vec_pretty(&graph).unwrap()).unwrap();

    let loaded = load_governance_graph(&path).unwrap();
    assert_eq!(loaded.nodes.len(), 1);

    let _ = fs::remove_file(path);
}

#[test]
fn rejects_invalid_governance_graph_json() {
    let path = temp_file("invalid-graph.json");
    fs::write(
        &path,
        r#"{
  "nodes": {
    "entry": {
      "Binary": {
        "id": "other",
        "name": "mismatched",
        "gates": [],
        "default": "Permit",
        "combination": "FirstMatch"
      }
    }
  },
  "edges": []
}"#,
    )
    .unwrap();

    let error = load_governance_graph(&path).expect_err("mismatched node ids must fail");
    assert!(
        error
            .to_string()
            .contains("does not match embedded node id")
    );

    let _ = fs::remove_file(path);
}

#[test]
fn loads_review_overlay_from_json() {
    let path = temp_file("review-overlay.json");
    fs::write(
        &path,
        r#"{"reviewed_nodes":[{"node_id":"policy.rs::approval_gate","note":"reviewed"}],"reviewed_edges":[],"alias_hints":[]}"#,
    )
    .unwrap();

    let overlay = load_review_overlay(&path).unwrap();
    assert_eq!(overlay.reviewed_nodes.len(), 1);

    let _ = fs::remove_file(path);
}

#[test]
fn claim_corpus_input_provenance_maps_to_library_provenance() {
    assert_eq!(
        ClaimCorpusProvenance::from(ClaimCorpusInputProvenance::ObservedRuntime),
        ClaimCorpusProvenance::ObservedRuntime
    );
    assert_eq!(
        ClaimCorpusProvenance::from(ClaimCorpusInputProvenance::Fixture),
        ClaimCorpusProvenance::Fixture
    );
}
