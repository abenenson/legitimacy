//! Versioned contract for an offline, single-stream trajectory certificate.
//!
//! The base trace/replay contract freezes representation and validation;
//! `composition` is its narrow replay-bound policy-evaluation extension. Both
//! remain independent of the observed-runtime importer and SQLite ledger chain.

mod authority;
mod canonical;
pub mod codex_exec_v0;
mod composition;
mod duplicate_json;
mod interchange;
mod replay;
mod validation;

pub use authority::{
    MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0,
    MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0, REPLAY_AUTHORITY_ALGORITHM_ED25519_V0,
    ReplayAuthorityErrorCodeV0, ReplayAuthorityErrorV0, ReplayAuthoritySigningKeyV0,
    ReplayAuthorityTrustPolicyV0, SignedReplayAuthorityReceiptV0,
    TRAJECTORY_REPLAY_AUTHORITY_ANCHOR_FORMAT_V0, TRAJECTORY_REPLAY_AUTHORITY_ANCHOR_VERSION_V0,
    TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_FORMAT_V0, TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_VERSION_V0,
    TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_FORMAT_V0,
    TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_VERSION_V0, UnverifiedReplayAuthorityReceiptV0,
    VerifiedReplayAuthorityReceiptV0, issue_trajectory_replay_authority_receipt_v0,
    verify_replay_authority_receipt_v0,
};
pub use composition::{
    BinaryPolicyDecisionV0, EncodedOccurrenceClaimV0, EventPolicyReceiptV0,
    HISTORICAL_PROPERTY_ID_V0, HISTORICAL_PROPERTY_VERSION_V0,
    MAX_TRAJECTORY_COMPOSITION_POLICY_BYTES_V0, MAX_TRAJECTORY_COMPOSITION_RESULT_BYTES_V0,
    OCCURRENCE_ENCODER_ID_V0, OCCURRENCE_ENCODER_VERSION_V0, ObservedPrefixReceiptV0,
    TRAJECTORY_COMPOSITION_POLICY_BYTES_V0, TRAJECTORY_COMPOSITION_POLICY_FORMAT_V0,
    TRAJECTORY_COMPOSITION_POLICY_FORMAT_VERSION_V0, TRAJECTORY_COMPOSITION_POLICY_ID_V0,
    TRAJECTORY_COMPOSITION_POLICY_VERSION_V0, TRAJECTORY_COMPOSITION_RESULT_FORMAT_V0,
    TRAJECTORY_COMPOSITION_RESULT_VERSION_V0, TemporalCompositionKindV0,
    TemporalCompositionResultV0, TrajectoryCompositionErrorCodeV0, TrajectoryCompositionErrorV0,
    TrajectoryCompositionPolicyArtifactV0, TrajectoryCompositionResultV0,
    evaluate_replay_bound_composition_v0,
};
pub use replay::{
    DeclaredTrajectoryValidationContextV0, EXACT_RAW_RECORD_SET_FORMAT_V0,
    EXACT_RAW_RECORD_SET_VERSION_V0, ExactRawRecordSetV0, InspectedTrajectoryReplayCandidateV0,
    MAX_EXACT_RAW_RECORD_SET_JSON_BYTES_V0,
    MAX_TRAJECTORY_DECLARED_VALIDATION_CONTEXT_JSON_BYTES_V0, MAX_TRAJECTORY_REPLAY_BYTES_V0,
    MAX_VERIFIED_TRAJECTORY_REPLAY_BYTES_V0, ReplayErrorCodeV0, ReplayErrorV0, ReplayRecordV0,
    TRAJECTORY_DECLARED_VALIDATION_CONTEXT_FORMAT_V0,
    TRAJECTORY_DECLARED_VALIDATION_CONTEXT_VERSION_V0, TRAJECTORY_REPLAY_FORMAT_V0,
    TRAJECTORY_REPLAY_VERIFICATION_FORMAT_V0, TRAJECTORY_REPLAY_VERIFICATION_VERSION_V0,
    TRAJECTORY_REPLAY_VERSION_V0, TrajectoryReplayCandidateV0, VerifiedTrajectoryReplayV0,
    trajectory_replay_candidate_v0, verify_trajectory_replay_v0,
};

use crate::LegitimacyError;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

pub const TRAJECTORY_SCHEMA_ID_V0: &str = "legitimacy.trajectory.trace";
pub const TRAJECTORY_SCHEMA_VERSION_V0: &str = "0";
pub const TRAJECTORY_SCHEMA_BYTES_V0: &[u8] =
    include_bytes!("../../schemas/trajectory-v0.schema.json");

/// Maximum exact untrusted JSON wire accepted by `TrajectoryTraceV0::from_json_slice` (8 MiB).
pub const MAX_TRACE_JSON_INPUT_BYTES_V0: usize = 8 * 1024 * 1024;
/// Maximum official deterministic compact JSON export for a validated trace (8 MiB).
pub const MAX_TRACE_COMPACT_JSON_BYTES_V0: usize = 8 * 1024 * 1024;
/// Maximum decoded keys retained for one JSON object during duplicate-key preflight.
pub const MAX_JSON_KEYS_PER_OBJECT_V0: usize = 1_024;
/// Maximum cumulative decoded UTF-8 key bytes for one object during duplicate-key preflight.
pub const MAX_JSON_KEY_BYTES_PER_OBJECT_V0: usize = 64 * 1_024;
/// Maximum total bytes in the ordered raw capture supplied to validation (64 MiB).
pub const MAX_RAW_CAPTURE_BYTES_V0: usize = 64 * 1024 * 1024;
/// Maximum bytes in one raw JSON record (8 MiB).
pub const MAX_RAW_RECORD_BYTES_V0: usize = 8 * 1024 * 1024;
/// Maximum raw records in one sterile single-stream capture.
pub const MAX_RAW_RECORDS_V0: usize = 10_000;
/// Maximum normalized events in one trace.
pub const MAX_EVENTS_V0: usize = 10_000;
/// Maximum payload fields on one event or nested normalized object.
pub const MAX_PAYLOAD_FIELDS_PER_OBJECT_V0: usize = 256;
/// Maximum payload object fields across the complete trace.
pub const MAX_PAYLOAD_FIELDS_TOTAL_V0: usize = 50_000;
/// Maximum normalized string, integer, and payload-key bytes across the trace (8 MiB).
pub const MAX_PAYLOAD_CONTENT_BYTES_TOTAL_V0: usize = 8 * 1024 * 1024;
/// Maximum normalized value nodes across the complete trace.
pub const MAX_NORMALIZED_NODES_V0: usize = 100_000;
/// Maximum normalized value nesting depth, counting the root as depth one.
pub const MAX_NORMALIZED_DEPTH_V0: usize = 32;
/// Maximum elements in one normalized array.
pub const MAX_NORMALIZED_ARRAY_ITEMS_V0: usize = 1_024;
/// Maximum evidence locators, including repeated citations.
pub const MAX_EVIDENCE_LOCATORS_V0: usize = 100_000;
/// Maximum locators in one deterministic derivation.
pub const MAX_DERIVATION_INPUTS_V0: usize = 1_024;
/// Maximum sum of byte lengths for distinct cited ranges (16 MiB).
pub const MAX_DISTINCT_CITED_BYTES_V0: u64 = 16 * 1024 * 1024;
/// Maximum bytes in an occurrence or source-item identifier.
pub const MAX_IDENTIFIER_BYTES_V0: usize = 128;
/// Maximum Unicode scalar values in a normalized string.
pub const MAX_NORMALIZED_STRING_SCALARS_V0: usize = 16_384;
/// Maximum UTF-8 bytes in a normalized string.
pub const MAX_NORMALIZED_STRING_BYTES_V0: usize = 65_536;
/// Maximum decimal digits in a normalized integer.
pub const MAX_INTEGER_DIGITS_V0: usize = 1_024;
/// Maximum UTF-8 bytes in an unavailable-evidence reason.
pub const MAX_EVIDENCE_REASON_BYTES_V0: usize = 1_024;

const HASH_ENVELOPE_V0: &[u8] = b"legitimacy.trajectory.hash.v0\0";
const ARTIFACT_DOMAIN_V0: &str = "legitimacy.trajectory.artifact.v0";
const RAW_CAPTURE_DOMAIN_V0: &str = "legitimacy.trajectory.raw-capture.v0";
const RAW_RECORD_DOMAIN_V0: &str = "legitimacy.trajectory.raw-record.v0";
const SOURCE_LOCATOR_DOMAIN_V0: &str = "legitimacy.trajectory.source-locator.v0";
const TRACE_DOMAIN_V0: &str = "legitimacy.trajectory.trace.v0";

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(deny_unknown_fields)]
pub struct ArtifactBindingV0 {
    pub identity: String,
    pub version: String,
    pub hash: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RawCaptureSealV0 {
    pub record_count: u64,
    pub digest: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct SourceLocatorV0 {
    pub record_index: u64,
    pub byte_offset: u64,
    pub byte_length: u64,
    pub digest: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "classification", rename_all = "kebab-case", deny_unknown_fields)]
pub enum EvidenceV0 {
    /// Cites exact bytes without claiming they decode to or entail the normalized value.
    CitesRawRange {
        locator: SourceLocatorV0,
    },
    /// Declares an allowlisted derivation binding without claiming execution or output checking.
    DeclaredDerivationBinding {
        rule: ArtifactBindingV0,
        source_inputs: Vec<SourceLocatorV0>,
    },
    Unavailable {
        reason: String,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields, bound(deserialize = "T: Deserialize<'de>"))]
pub struct EvidencedV0<T> {
    #[serde(deserialize_with = "deserialize_required_option")]
    pub value: Option<T>,
    pub evidence: EvidenceV0,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum NormalizedEventKindV0 {
    ActionRequest,
    ActionResult,
    Observation,
    Message,
    Lifecycle,
}

impl NormalizedEventKindV0 {
    pub(super) fn label(&self) -> &'static str {
        match self {
            Self::ActionRequest => "action-request",
            Self::ActionResult => "action-result",
            Self::Observation => "observation",
            Self::Message => "message",
            Self::Lifecycle => "lifecycle",
        }
    }
}

/// Float-free JSON-like values for policy-relevant normalized payload fields.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(
    tag = "type",
    content = "value",
    rename_all = "kebab-case",
    deny_unknown_fields
)]
pub enum NormalizedValueV0 {
    Null,
    Boolean(bool),
    Integer(String),
    String(String),
    Array(Vec<NormalizedValueV0>),
    Object(
        #[serde(deserialize_with = "duplicate_json::deserialize_unique_map")]
        BTreeMap<String, NormalizedValueV0>,
    ),
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RawRecordReferenceV0 {
    pub record_index: u64,
    pub digest: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct AgentActionEventV0 {
    pub event_id: EvidencedV0<String>,
    pub sequence_index: EvidencedV0<u64>,
    pub kind: EvidencedV0<NormalizedEventKindV0>,
    pub source_item_id: Option<EvidencedV0<String>>,
    pub raw_record: RawRecordReferenceV0,
    #[serde(deserialize_with = "duplicate_json::deserialize_unique_map")]
    pub payload: BTreeMap<String, EvidencedV0<NormalizedValueV0>>,
}

/// A constructible trajectory awaiting validation.
///
/// Generic [`Serialize`] output is available for inspection and integration,
/// but only [`ValidatedTrajectoryTraceV0::to_compact_json`] is the official
/// bounded JSON interchange export.
///
/// `TrajectoryTraceV0` intentionally cannot be decoded through generic Serde:
///
/// ```compile_fail
/// use legitimacy::TrajectoryTraceV0;
///
/// fn main() {
///     let _: TrajectoryTraceV0 =
///         serde_json::from_slice(b"{}").expect("generic decoding must remain unavailable");
/// }
/// ```
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TrajectoryTraceV0 {
    pub schema: ArtifactBindingV0,
    pub run_id: EvidencedV0<String>,
    pub adapter: ArtifactBindingV0,
    pub policy: ArtifactBindingV0,
    pub raw_capture: RawCaptureSealV0,
    pub events: Vec<AgentActionEventV0>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TrajectoryTraceWireV0 {
    schema: ArtifactBindingV0,
    run_id: EvidencedV0<String>,
    adapter: ArtifactBindingV0,
    policy: ArtifactBindingV0,
    raw_capture: RawCaptureSealV0,
    events: Vec<AgentActionEventV0>,
}

impl From<TrajectoryTraceWireV0> for TrajectoryTraceV0 {
    fn from(wire: TrajectoryTraceWireV0) -> Self {
        Self {
            schema: wire.schema,
            run_id: wire.run_id,
            adapter: wire.adapter,
            policy: wire.policy,
            raw_capture: wire.raw_capture,
            events: wire.events,
        }
    }
}

/// Separate declarations against which a trace is validated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrajectoryValidationContextV0 {
    pub adapter: ArtifactBindingV0,
    pub policy: ArtifactBindingV0,
    pub raw_capture: RawCaptureSealV0,
    pub allowed_derivations: BTreeSet<ArtifactBindingV0>,
}

/// Proof token returned only after an immutable trace passes v0 validation.
#[derive(Clone, Copy, Debug)]
pub struct ValidatedTrajectoryTraceV0<'trace> {
    trace: &'trace TrajectoryTraceV0,
}

impl TrajectoryTraceV0 {
    /// Sole supported untrusted JSON decoder.
    ///
    /// Enforces the exact input-wire cap, rejects duplicate keys at every
    /// object depth, and decodes the closed v0 shape through a private wire type.
    pub fn from_json_slice(input: &[u8]) -> Result<Self, LegitimacyError> {
        if input.len() > MAX_TRACE_JSON_INPUT_BYTES_V0 {
            return invalid(format!(
                "trajectory trace JSON input exceeds v0 byte limit of {MAX_TRACE_JSON_INPUT_BYTES_V0}"
            ));
        }
        duplicate_json::reject_duplicate_json_keys(input, "trajectory trace")?;
        serde_json::from_slice::<TrajectoryTraceWireV0>(input)
            .map(Into::into)
            .map_err(|source| LegitimacyError::Json {
                context: "trajectory trace".to_string(),
                source,
            })
    }

    /// Validates the contract against exact raw JSON-record bytes and separate declarations.
    pub fn validate<'trace>(
        &'trace self,
        raw_records: &[&[u8]],
        declarations: &TrajectoryValidationContextV0,
    ) -> Result<ValidatedTrajectoryTraceV0<'trace>, LegitimacyError> {
        validation::validate_trace(self, raw_records, declarations)?;
        Ok(ValidatedTrajectoryTraceV0 { trace: self })
    }
}

pub fn trajectory_digest_v0(validated: &ValidatedTrajectoryTraceV0<'_>) -> String {
    validated.trajectory_digest()
}

pub fn trajectory_schema_binding_v0() -> ArtifactBindingV0 {
    ArtifactBindingV0 {
        identity: TRAJECTORY_SCHEMA_ID_V0.to_string(),
        version: TRAJECTORY_SCHEMA_VERSION_V0.to_string(),
        hash: artifact_digest_v0(TRAJECTORY_SCHEMA_BYTES_V0),
    }
}

pub fn artifact_digest_v0(bytes: &[u8]) -> String {
    framed_sha256(ARTIFACT_DOMAIN_V0, &[bytes])
}

pub fn raw_record_digest_v0(bytes: &[u8]) -> String {
    framed_sha256(RAW_RECORD_DOMAIN_V0, &[bytes])
}

pub fn source_locator_digest_v0(bytes: &[u8]) -> String {
    framed_sha256(SOURCE_LOCATOR_DOMAIN_V0, &[bytes])
}

pub fn raw_capture_seal_v0(raw_records: &[&[u8]]) -> RawCaptureSealV0 {
    RawCaptureSealV0 {
        record_count: u64::try_from(raw_records.len())
            .expect("slice length always fits u64 on supported targets"),
        digest: framed_sha256(RAW_CAPTURE_DOMAIN_V0, raw_records),
    }
}

pub(super) fn framed_sha256(domain: &str, components: &[&[u8]]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(HASH_ENVELOPE_V0);
    hash_frame(&mut hasher, domain.as_bytes());
    hasher.update(
        u64::try_from(components.len())
            .expect("slice length always fits u64 on supported targets")
            .to_be_bytes(),
    );
    for component in components {
        hash_frame(&mut hasher, component);
    }
    format!("sha256:{:x}", hasher.finalize())
}

fn hash_frame(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update(
        u64::try_from(bytes.len())
            .expect("slice length always fits u64 on supported targets")
            .to_be_bytes(),
    );
    hasher.update(bytes);
}

fn deserialize_required_option<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

pub(super) fn invalid<T>(message: impl Into<String>) -> Result<T, LegitimacyError> {
    Err(LegitimacyError::invalid_input(message))
}

/// Shared bounded wire preflight for sibling artifact readers. Reuses the
/// trajectory scanner so nested duplicate keys cannot be erased by Value.
pub(crate) fn preflight_executed_artifact(input: &[u8]) -> Result<(), String> {
    duplicate_json::scan_json_with_limits(
        input,
        "executed composition",
        duplicate_json::JsonScanLimits {
            max_depth: 20,
            max_nodes: 100_000,
            max_total_keys: 50_000,
            max_decoded_string_bytes: 1024 * 1024,
        },
    )
    .map(|_| ())
    .map_err(|_| "invalid, duplicate, or over-budget JSON".into())
}
