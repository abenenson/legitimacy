use crate::{
    GovernanceClaim, LegitimacyError, OBSERVED_RUNTIME_CORPUS_SCHEMA_VERSION,
    ObservedRuntimeClaimRecord, ObservedRuntimeCorpusManifest, ObservedRuntimeCorpusPack,
    ObservedRuntimeRedactionMetadata, write_observed_runtime_corpus_pack,
};
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::Path};

const CODEX_OSS_STORY_DESCRIPTOR: &str = "codex-rs tui oss-story fixture";
const REDACTION_METHOD: &str = "sha256-truncate-12";

#[derive(Debug, Deserialize)]
struct StoryEvent {
    ts: String,
    kind: String,
    #[serde(default)]
    payload: Option<StoryPayload>,
}

#[derive(Debug, Deserialize)]
struct StoryPayload {
    #[serde(default)]
    id: Option<String>,
    #[serde(default)]
    msg: Option<StoryMessage>,
}

#[derive(Debug, Deserialize)]
struct StoryMessage {
    #[serde(rename = "type")]
    message_type: String,
    #[serde(default)]
    message: Option<String>,
    #[serde(default)]
    last_agent_message: Option<String>,
}

pub fn import_codex_oss_story_corpus_pack(
    input_path: &Path,
    output_dir: &Path,
) -> Result<ObservedRuntimeCorpusPack, LegitimacyError> {
    let pack = build_codex_oss_story_corpus_pack(input_path)?;
    write_observed_runtime_corpus_pack(output_dir, &pack)?;
    Ok(pack)
}

pub fn build_codex_oss_story_corpus_pack(
    input_path: &Path,
) -> Result<ObservedRuntimeCorpusPack, LegitimacyError> {
    let input = fs::read_to_string(input_path).map_err(|source| LegitimacyError::Io {
        context: format!("reading codex oss-story trace '{}'", input_path.display()),
        source,
    })?;
    let source_sha256 = sha256_hex(input.as_bytes());

    let mut claims = Vec::new();
    let mut capture_timestamp = None;
    for (index, line) in input.lines().enumerate() {
        let line_number = index + 1;
        if line.trim().is_empty() {
            continue;
        }
        let event: StoryEvent =
            serde_json::from_str(line).map_err(|source| LegitimacyError::Json {
                context: format!(
                    "codex oss-story trace '{}' line {line_number}",
                    input_path.display()
                ),
                source,
            })?;
        capture_timestamp = Some(event.ts.clone());
        if let Some(record) = event_to_claim_record(event) {
            claims.push(record);
        }
    }

    if claims.is_empty() {
        return Err(LegitimacyError::invalid_input(format!(
            "codex oss-story trace '{}' did not yield any observed-runtime claims",
            input_path.display()
        )));
    }

    Ok(ObservedRuntimeCorpusPack {
        manifest: ObservedRuntimeCorpusManifest {
            schema_version: OBSERVED_RUNTIME_CORPUS_SCHEMA_VERSION,
            source_descriptor: CODEX_OSS_STORY_DESCRIPTOR.to_string(),
            source_sha256,
            capture_timestamp: capture_timestamp.unwrap_or_default(),
            redaction: ObservedRuntimeRedactionMetadata {
                redacted_fields: vec![
                    "source_event_id".to_string(),
                    "claim.claimant_id".to_string(),
                    "claim.content".to_string(),
                ],
                method: REDACTION_METHOD.to_string(),
            },
            claim_count: claims.len(),
        },
        claims,
    })
}

fn event_to_claim_record(event: StoryEvent) -> Option<ObservedRuntimeClaimRecord> {
    if event.kind != "codex_event" {
        return None;
    }
    let payload = event.payload?;
    let message = payload.msg?;
    let source_kind = message.message_type;
    let content = match source_kind.as_str() {
        "agent_message" => message.message,
        "task_complete" => message.last_agent_message,
        "task_started" => None,
        _ => return None,
    };
    let source_id = payload.id.unwrap_or_else(|| "missing".to_string());
    let event_identity = format!("{source_id}::{source_kind}::{}", event.ts);

    let content_length = content
        .as_ref()
        .map(|value| value.chars().count())
        .unwrap_or(0);
    let word_count = content
        .as_ref()
        .map(|value| value.split_whitespace().count())
        .unwrap_or(0);
    let hashed_content = content
        .as_ref()
        .map(|value| format!("content_{}", sha256_prefix(value.as_bytes())));

    let mut metrics = BTreeMap::new();
    metrics.insert("content_length".to_string(), content_length as f64);
    metrics.insert("word_count".to_string(), word_count as f64);
    metrics.insert(
        "completed_turn".to_string(),
        if source_kind == "task_complete" {
            1.0
        } else {
            0.0
        },
    );

    Some(ObservedRuntimeClaimRecord {
        source_kind: source_kind.clone(),
        source_event_id: Some(format!("evt_{}", sha256_prefix(event_identity.as_bytes()))),
        observed_at: Some(event.ts),
        claim: GovernanceClaim {
            claimant_id: format!("turn_{}", sha256_prefix(event_identity.as_bytes())),
            strength: 1.0,
            priority_class: Some("observed-runtime".to_string()),
            path: None,
            action: Some(source_kind),
            content: hashed_content,
            metrics,
        },
    })
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}

fn sha256_prefix(bytes: &[u8]) -> String {
    let full = sha256_hex(bytes);
    full[..12].to_string()
}
