use crate::{GovernanceClaim, LegitimacyError};
use serde::{Deserialize, Serialize};
use std::{
    fs,
    path::{Path, PathBuf},
};

pub const OBSERVED_RUNTIME_CORPUS_SCHEMA_VERSION: u32 = 1;
pub const OBSERVED_RUNTIME_MANIFEST_FILENAME: &str = "manifest.json";
pub const OBSERVED_RUNTIME_CLAIMS_FILENAME: &str = "claims.jsonl";

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ObservedRuntimeRedactionMetadata {
    pub redacted_fields: Vec<String>,
    pub method: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ObservedRuntimeCorpusManifest {
    pub schema_version: u32,
    pub source_descriptor: String,
    pub source_sha256: String,
    pub capture_timestamp: String,
    pub redaction: ObservedRuntimeRedactionMetadata,
    pub claim_count: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct ObservedRuntimeClaimRecord {
    pub source_kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_event_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub observed_at: Option<String>,
    pub claim: GovernanceClaim,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct ObservedRuntimeCorpusPack {
    pub manifest: ObservedRuntimeCorpusManifest,
    pub claims: Vec<ObservedRuntimeClaimRecord>,
}

impl ObservedRuntimeCorpusPack {
    pub fn governance_claims(&self) -> Vec<GovernanceClaim> {
        self.claims
            .iter()
            .map(|record| record.claim.clone())
            .collect()
    }
}

pub fn write_observed_runtime_corpus_pack(
    output_dir: &Path,
    pack: &ObservedRuntimeCorpusPack,
) -> Result<(), LegitimacyError> {
    fs::create_dir_all(output_dir).map_err(|source| LegitimacyError::Io {
        context: format!(
            "creating observed-runtime corpus pack directory '{}'",
            output_dir.display()
        ),
        source,
    })?;

    let manifest_path = output_dir.join(OBSERVED_RUNTIME_MANIFEST_FILENAME);
    let manifest_bytes =
        serde_json::to_vec_pretty(&pack.manifest).map_err(|source| LegitimacyError::Serialize {
            context: format!(
                "observed-runtime corpus manifest '{}'",
                manifest_path.display()
            ),
            source,
        })?;
    fs::write(&manifest_path, manifest_bytes).map_err(|source| LegitimacyError::Io {
        context: format!(
            "writing observed-runtime corpus manifest '{}'",
            manifest_path.display()
        ),
        source,
    })?;

    let claims_path = output_dir.join(OBSERVED_RUNTIME_CLAIMS_FILENAME);
    let mut encoded_claims = Vec::new();
    for record in &pack.claims {
        let line = serde_json::to_vec(record).map_err(|source| LegitimacyError::Serialize {
            context: format!(
                "observed-runtime corpus claim record '{}'",
                claims_path.display()
            ),
            source,
        })?;
        encoded_claims.extend(line);
        encoded_claims.push(b'\n');
    }
    fs::write(&claims_path, encoded_claims).map_err(|source| LegitimacyError::Io {
        context: format!(
            "writing observed-runtime corpus claims '{}'",
            claims_path.display()
        ),
        source,
    })?;

    Ok(())
}

pub fn load_observed_runtime_corpus_pack(
    input_dir: &Path,
) -> Result<ObservedRuntimeCorpusPack, LegitimacyError> {
    let manifest_path = input_dir.join(OBSERVED_RUNTIME_MANIFEST_FILENAME);
    let manifest_input =
        fs::read_to_string(&manifest_path).map_err(|source| LegitimacyError::Io {
            context: format!(
                "reading observed-runtime corpus manifest '{}'",
                manifest_path.display()
            ),
            source,
        })?;
    let manifest =
        serde_json::from_str(&manifest_input).map_err(|source| LegitimacyError::Json {
            context: format!(
                "observed-runtime corpus manifest '{}'",
                manifest_path.display()
            ),
            source,
        })?;

    let claims_path = input_dir.join(OBSERVED_RUNTIME_CLAIMS_FILENAME);
    let claims_input = fs::read_to_string(&claims_path).map_err(|source| LegitimacyError::Io {
        context: format!(
            "reading observed-runtime corpus claims '{}'",
            claims_path.display()
        ),
        source,
    })?;
    let mut claims = Vec::new();
    for (index, line) in claims_input.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let line_number = index + 1;
        let record = serde_json::from_str(line).map_err(|source| LegitimacyError::Json {
            context: format!(
                "observed-runtime corpus claim '{}' line {line_number}",
                claims_path.display()
            ),
            source,
        })?;
        claims.push(record);
    }

    Ok(ObservedRuntimeCorpusPack { manifest, claims })
}

pub fn observed_runtime_manifest_path(root: &Path) -> PathBuf {
    root.join(OBSERVED_RUNTIME_MANIFEST_FILENAME)
}

pub fn observed_runtime_claims_path(root: &Path) -> PathBuf {
    root.join(OBSERVED_RUNTIME_CLAIMS_FILENAME)
}
