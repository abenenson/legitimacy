use legitimacy::{
    GovernanceClaim, OBSERVED_RUNTIME_CORPUS_SCHEMA_VERSION, ObservedRuntimeClaimRecord,
    ObservedRuntimeCorpusManifest, ObservedRuntimeCorpusPack, ObservedRuntimeRedactionMetadata,
    load_observed_runtime_corpus_pack, observed_runtime_claims_path,
    observed_runtime_manifest_path, write_observed_runtime_corpus_pack,
};
use std::{
    collections::BTreeMap,
    fs,
    time::{SystemTime, UNIX_EPOCH},
};

#[test]
fn observed_runtime_corpus_pack_round_trips_through_disk() {
    let dir = unique_dir("observed-runtime-pack");
    let pack = sample_pack();

    write_observed_runtime_corpus_pack(&dir, &pack).unwrap();
    let loaded = load_observed_runtime_corpus_pack(&dir).unwrap();

    assert_eq!(loaded, pack);
    assert_eq!(loaded.governance_claims().len(), 2);
    assert!(observed_runtime_manifest_path(&dir).exists());
    assert!(observed_runtime_claims_path(&dir).exists());
}

#[test]
fn observed_runtime_corpus_pack_serializes_with_expected_schema_version() {
    let pack = sample_pack();
    let encoded = serde_json::to_string(&pack.manifest).unwrap();
    let decoded: ObservedRuntimeCorpusManifest = serde_json::from_str(&encoded).unwrap();

    assert_eq!(
        decoded.schema_version,
        OBSERVED_RUNTIME_CORPUS_SCHEMA_VERSION
    );
    assert_eq!(decoded.redaction.method, "sha256-truncate-12");
}

fn sample_pack() -> ObservedRuntimeCorpusPack {
    ObservedRuntimeCorpusPack {
        manifest: ObservedRuntimeCorpusManifest {
            schema_version: OBSERVED_RUNTIME_CORPUS_SCHEMA_VERSION,
            source_descriptor: "codex oss-story fixture".to_string(),
            source_sha256: "9e8d49f5a4c18d8c0d7c7d6a7808f5f6f54d5ee76689b4c9d8531c2f4ab0a91a"
                .to_string(),
            capture_timestamp: "2025-08-10T03:24:02Z".to_string(),
            redaction: ObservedRuntimeRedactionMetadata {
                redacted_fields: vec![
                    "claim.claimant_id".to_string(),
                    "claim.path".to_string(),
                    "claim.content".to_string(),
                ],
                method: "sha256-truncate-12".to_string(),
            },
            claim_count: 2,
        },
        claims: vec![
            ObservedRuntimeClaimRecord {
                source_kind: "turn.completed".to_string(),
                source_event_id: Some("evt_0001".to_string()),
                observed_at: Some("2025-08-10T03:24:02Z".to_string()),
                claim: GovernanceClaim {
                    claimant_id: "actor_c3f1da20d4b2".to_string(),
                    strength: 1.0,
                    priority_class: Some("interactive".to_string()),
                    path: Some("path_2becc457b73a".to_string()),
                    action: Some("agent_message".to_string()),
                    content: Some("content_8270fbc93b2e".to_string()),
                    metrics: BTreeMap::from([(String::from("token_count"), 42.0)]),
                },
            },
            ObservedRuntimeClaimRecord {
                source_kind: "turn.completed".to_string(),
                source_event_id: Some("evt_0002".to_string()),
                observed_at: Some("2025-08-10T03:24:03Z".to_string()),
                claim: GovernanceClaim {
                    claimant_id: "actor_a6d22011b9fe".to_string(),
                    strength: 0.5,
                    priority_class: Some("interactive".to_string()),
                    path: None,
                    action: Some("task_complete".to_string()),
                    content: None,
                    metrics: BTreeMap::from([(String::from("completion_tokens"), 84.0)]),
                },
            },
        ],
    }
}

fn unique_dir(label: &str) -> std::path::PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}"));
    fs::create_dir_all(&dir).unwrap();
    dir
}
