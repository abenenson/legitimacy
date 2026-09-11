use super::{
    ArtifactBindingV0, MAX_EVENTS_V0, MAX_RAW_CAPTURE_BYTES_V0, MAX_RAW_RECORD_BYTES_V0,
    MAX_RAW_RECORDS_V0, RawCaptureSealV0, TrajectoryValidationContextV0,
    ValidatedTrajectoryTraceV0, VerifiedReplayAuthorityReceiptV0,
    duplicate_json::{self, JsonRootKind, JsonScanLimits},
    framed_sha256, validation,
};
use serde::{Deserialize, Serialize};
use std::fmt;

pub const TRAJECTORY_REPLAY_FORMAT_V0: &str = "legitimacy.trajectory.replay";
pub const TRAJECTORY_REPLAY_VERSION_V0: &str = "0";
pub const TRAJECTORY_REPLAY_VERIFICATION_FORMAT_V0: &str =
    "legitimacy.trajectory.replay-verification";
pub const TRAJECTORY_REPLAY_VERIFICATION_VERSION_V0: &str = "0";

/// Maximum exact canonical replay-candidate JSON line accepted or emitted (16 MiB).
pub const MAX_TRAJECTORY_REPLAY_BYTES_V0: usize = 16 * 1024 * 1024;
/// Maximum exact verified replay JSON line emitted (17 MiB).
pub const MAX_VERIFIED_TRAJECTORY_REPLAY_BYTES_V0: usize = 17 * 1024 * 1024;
/// Maximum exact JSON input carrying escaped exact raw-record strings (128 MiB).
pub const MAX_EXACT_RAW_RECORD_SET_JSON_BYTES_V0: usize = 128 * 1024 * 1024;
/// Maximum exact JSON input carrying declared validation bindings (4 MiB).
pub const MAX_TRAJECTORY_DECLARED_VALIDATION_CONTEXT_JSON_BYTES_V0: usize = 4 * 1024 * 1024;

pub const EXACT_RAW_RECORD_SET_FORMAT_V0: &str = "legitimacy.trajectory.exact-raw-record-set";
pub const EXACT_RAW_RECORD_SET_VERSION_V0: &str = "0";
pub const TRAJECTORY_DECLARED_VALIDATION_CONTEXT_FORMAT_V0: &str =
    "legitimacy.trajectory.validation-declarations";
pub const TRAJECTORY_DECLARED_VALIDATION_CONTEXT_VERSION_V0: &str = "0";

const REPLAY_GENESIS_DOMAIN_V0: &str = "legitimacy.trajectory.replay.genesis.v0";
const REPLAY_CANONICAL_EVENT_DOMAIN_V0: &str = "legitimacy.trajectory.replay.canonical-event.v0";
const REPLAY_CHAIN_STEP_DOMAIN_V0: &str = "legitimacy.trajectory.replay.chain-step.v0";

const REPLAY_SCAN_LIMITS: JsonScanLimits = JsonScanLimits {
    max_depth: 8,
    max_nodes: 8 + (MAX_EVENTS_V0 * 8),
    max_total_keys: 24 + (MAX_EVENTS_V0 * 6),
    max_decoded_string_bytes: MAX_TRAJECTORY_REPLAY_BYTES_V0,
};

const RAW_RECORD_SET_SCAN_LIMITS: JsonScanLimits = JsonScanLimits {
    max_depth: 4,
    max_nodes: 8 + MAX_RAW_RECORDS_V0,
    max_total_keys: 16,
    max_decoded_string_bytes: MAX_EXACT_RAW_RECORD_SET_JSON_BYTES_V0,
};

const VALIDATION_CONTEXT_SCAN_LIMITS: JsonScanLimits = JsonScanLimits {
    max_depth: 6,
    max_nodes: 32 + (MAX_EVENTS_V0 * 4),
    max_total_keys: 32 + (MAX_EVENTS_V0 * 3),
    max_decoded_string_bytes: MAX_TRAJECTORY_DECLARED_VALIDATION_CONTEXT_JSON_BYTES_V0,
};

/// Closed, attacker-independent failures for replay decoding and verification.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum ReplayErrorCodeV0 {
    InputTooLarge,
    JsonFraming,
    JsonSyntax,
    JsonShape,
    UnsupportedFormat,
    CandidateMismatch,
    AuthorityBindingMismatch,
    Serialization,
}

impl ReplayErrorCodeV0 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::InputTooLarge => "input-too-large",
            Self::JsonFraming => "json-framing",
            Self::JsonSyntax => "json-syntax",
            Self::JsonShape => "json-shape",
            Self::UnsupportedFormat => "unsupported-format",
            Self::CandidateMismatch => "replay-candidate-mismatch",
            Self::AuthorityBindingMismatch => "authority-receipt-binding-mismatch",
            Self::Serialization => "serialization",
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub struct ReplayErrorV0 {
    code: ReplayErrorCodeV0,
}

impl ReplayErrorV0 {
    pub(super) const fn new(code: ReplayErrorCodeV0) -> Self {
        Self { code }
    }

    pub const fn code(&self) -> ReplayErrorCodeV0 {
        self.code
    }
}

impl fmt::Display for ReplayErrorV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.code.as_str())
    }
}

impl fmt::Debug for ReplayErrorV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ReplayErrorV0")
            .field("code", &self.code)
            .finish()
    }
}

impl std::error::Error for ReplayErrorV0 {}

pub(super) type ReplayResultV0<T> = Result<T, ReplayErrorV0>;

/// Exact ordered raw JSON-record bytes decoded from a bounded vendor-neutral carrier.
#[derive(Clone, Debug)]
pub struct ExactRawRecordSetV0 {
    records: Vec<Vec<u8>>,
}

impl ExactRawRecordSetV0 {
    pub fn from_json_slice(input: &[u8]) -> ReplayResultV0<Self> {
        let body = preflight_json_object(
            input,
            MAX_EXACT_RAW_RECORD_SET_JSON_BYTES_V0,
            RAW_RECORD_SET_SCAN_LIMITS,
        )?;
        let wire: ExactRawRecordSetWireV0 = serde_json::from_slice(body)
            .map_err(|_| ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape))?;
        if wire.record_set_format != EXACT_RAW_RECORD_SET_FORMAT_V0
            || wire.record_set_version != EXACT_RAW_RECORD_SET_VERSION_V0
        {
            return Err(ReplayErrorV0::new(ReplayErrorCodeV0::UnsupportedFormat));
        }
        if wire.records.is_empty() || wire.records.len() > MAX_RAW_RECORDS_V0 {
            return Err(ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape));
        }
        let mut total = 0usize;
        let mut records = Vec::with_capacity(wire.records.len());
        for record in wire.records {
            let bytes = record.into_bytes();
            if bytes.len() > MAX_RAW_RECORD_BYTES_V0 {
                return Err(ReplayErrorV0::new(ReplayErrorCodeV0::InputTooLarge));
            }
            total = total
                .checked_add(bytes.len())
                .ok_or_else(|| ReplayErrorV0::new(ReplayErrorCodeV0::InputTooLarge))?;
            if total > MAX_RAW_CAPTURE_BYTES_V0 {
                return Err(ReplayErrorV0::new(ReplayErrorCodeV0::InputTooLarge));
            }
            records.push(bytes);
        }
        Ok(Self { records })
    }

    pub fn record_slices(&self) -> Vec<&[u8]> {
        self.records.iter().map(Vec::as_slice).collect()
    }
}

/// Separately decoded adapter, policy, capture, and derivation declarations.
#[derive(Clone, Debug)]
pub struct DeclaredTrajectoryValidationContextV0 {
    declarations: TrajectoryValidationContextV0,
}

impl DeclaredTrajectoryValidationContextV0 {
    pub fn from_json_slice(input: &[u8]) -> ReplayResultV0<Self> {
        let body = preflight_json_object(
            input,
            MAX_TRAJECTORY_DECLARED_VALIDATION_CONTEXT_JSON_BYTES_V0,
            VALIDATION_CONTEXT_SCAN_LIMITS,
        )?;
        let wire: TrajectoryValidationDeclarationsWireV0 = serde_json::from_slice(body)
            .map_err(|_| ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape))?;
        if wire.declarations_format != TRAJECTORY_DECLARED_VALIDATION_CONTEXT_FORMAT_V0
            || wire.declarations_version != TRAJECTORY_DECLARED_VALIDATION_CONTEXT_VERSION_V0
        {
            return Err(ReplayErrorV0::new(ReplayErrorCodeV0::UnsupportedFormat));
        }
        validation::validate_binding("declared adapter", &wire.adapter)
            .map_err(|_| ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape))?;
        validation::validate_binding("declared policy", &wire.policy)
            .map_err(|_| ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape))?;
        ReplayDigestV0::parse(wire.raw_capture.digest.clone())?;
        if wire.raw_capture.record_count == 0
            || wire.raw_capture.record_count > MAX_RAW_RECORDS_V0 as u64
            || wire.allowed_derivations.len() > MAX_EVENTS_V0
        {
            return Err(ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape));
        }
        let mut allowed_derivations = std::collections::BTreeSet::new();
        for binding in wire.allowed_derivations {
            validation::validate_binding("declared derivation", &binding)
                .map_err(|_| ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape))?;
            if !allowed_derivations.insert(binding) {
                return Err(ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape));
            }
        }
        Ok(Self {
            declarations: TrajectoryValidationContextV0 {
                adapter: wire.adapter,
                policy: wire.policy,
                raw_capture: wire.raw_capture,
                allowed_derivations,
            },
        })
    }

    pub fn declarations(&self) -> &TrajectoryValidationContextV0 {
        &self.declarations
    }
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
#[serde(transparent)]
pub(super) struct ReplayDigestV0(String);

impl ReplayDigestV0 {
    fn from_validated(value: &str) -> Self {
        debug_assert!(is_digest(value));
        Self(value.to_string())
    }

    fn hash(domain: &str, components: &[&[u8]]) -> Self {
        Self(framed_sha256(domain, components))
    }

    pub(super) fn parse(value: String) -> ReplayResultV0<Self> {
        if is_digest(&value) {
            Ok(Self(value))
        } else {
            Err(ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape))
        }
    }

    pub(super) fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub(super) struct ReplayArtifactBindingV0 {
    pub(super) identity: String,
    pub(super) version: String,
    pub(super) hash: ReplayDigestV0,
}

impl ReplayArtifactBindingV0 {
    fn from_validated(binding: &ArtifactBindingV0) -> Self {
        Self {
            identity: binding.identity.clone(),
            version: binding.version.clone(),
            hash: ReplayDigestV0::from_validated(&binding.hash),
        }
    }
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub(super) struct ReplayRawCaptureSealV0 {
    pub(super) record_count: u64,
    pub(super) digest: ReplayDigestV0,
}

impl ReplayRawCaptureSealV0 {
    fn from_validated(seal: &RawCaptureSealV0) -> Self {
        Self {
            record_count: seal.record_count,
            digest: ReplayDigestV0::from_validated(&seal.digest),
        }
    }
}

/// One deterministic link in a v0 trajectory replay candidate.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ReplayRecordV0 {
    sequence_index: u64,
    event_id: String,
    raw_record_digest: ReplayDigestV0,
    canonical_event_digest: ReplayDigestV0,
    previous_head: ReplayDigestV0,
    resulting_head: ReplayDigestV0,
}

impl ReplayRecordV0 {
    pub fn sequence_index(&self) -> u64 {
        self.sequence_index
    }

    pub fn event_id(&self) -> &str {
        &self.event_id
    }

    pub fn raw_record_digest(&self) -> &str {
        self.raw_record_digest.as_str()
    }

    pub fn canonical_event_digest(&self) -> &str {
        self.canonical_event_digest.as_str()
    }

    pub fn previous_head(&self) -> &str {
        self.previous_head.as_str()
    }

    pub fn resulting_head(&self) -> &str {
        self.resulting_head.as_str()
    }
}

/// Deterministic replay material that has not been accepted against external authority.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct TrajectoryReplayCandidateV0 {
    replay_format: &'static str,
    replay_version: &'static str,
    schema: ReplayArtifactBindingV0,
    adapter: ReplayArtifactBindingV0,
    policy: ReplayArtifactBindingV0,
    raw_capture: ReplayRawCaptureSealV0,
    trajectory_digest: ReplayDigestV0,
    record_count: u64,
    genesis_head: ReplayDigestV0,
    records: Vec<ReplayRecordV0>,
    final_head: ReplayDigestV0,
}

impl TrajectoryReplayCandidateV0 {
    /// Emits the sole deterministic replay-candidate JSON encoding with one trailing LF.
    pub fn to_json_line(&self) -> ReplayResultV0<Vec<u8>> {
        serialize_json_line(self, MAX_TRAJECTORY_REPLAY_BYTES_V0)
    }

    pub fn trajectory_digest(&self) -> &str {
        self.trajectory_digest.as_str()
    }

    pub fn record_count(&self) -> u64 {
        self.record_count
    }

    pub fn genesis_head(&self) -> &str {
        self.genesis_head.as_str()
    }

    pub fn records(&self) -> &[ReplayRecordV0] {
        &self.records
    }

    pub fn final_head(&self) -> &str {
        self.final_head.as_str()
    }
}

/// Complete replay tuple signed by the independent replay authority.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub(super) struct ReplayAuthorityAnchorV0 {
    pub(super) anchor_format: &'static str,
    pub(super) anchor_version: &'static str,
    pub(super) replay_format: &'static str,
    pub(super) replay_version: &'static str,
    pub(super) schema: ReplayArtifactBindingV0,
    pub(super) adapter: ReplayArtifactBindingV0,
    pub(super) policy: ReplayArtifactBindingV0,
    pub(super) raw_capture: ReplayRawCaptureSealV0,
    pub(super) trajectory_digest: ReplayDigestV0,
    pub(super) record_count: u64,
    pub(super) genesis_head: ReplayDigestV0,
    pub(super) expected_final_head: ReplayDigestV0,
}

impl ReplayAuthorityAnchorV0 {
    pub(super) fn from_replay_candidate(candidate: &TrajectoryReplayCandidateV0) -> Self {
        Self {
            anchor_format: super::authority::TRAJECTORY_REPLAY_AUTHORITY_ANCHOR_FORMAT_V0,
            anchor_version: super::authority::TRAJECTORY_REPLAY_AUTHORITY_ANCHOR_VERSION_V0,
            replay_format: TRAJECTORY_REPLAY_FORMAT_V0,
            replay_version: TRAJECTORY_REPLAY_VERSION_V0,
            schema: candidate.schema.clone(),
            adapter: candidate.adapter.clone(),
            policy: candidate.policy.clone(),
            raw_capture: candidate.raw_capture.clone(),
            trajectory_digest: candidate.trajectory_digest.clone(),
            record_count: candidate.record_count,
            genesis_head: candidate.genesis_head.clone(),
            expected_final_head: candidate.final_head.clone(),
        }
    }
}

/// A strictly decoded replay candidate. This type is still not verification success.
#[derive(Clone, Debug)]
pub struct InspectedTrajectoryReplayCandidateV0 {
    candidate: TrajectoryReplayCandidateV0,
}

impl InspectedTrajectoryReplayCandidateV0 {
    pub fn from_json_slice(input: &[u8]) -> ReplayResultV0<Self> {
        let body = preflight_json_line(input, MAX_TRAJECTORY_REPLAY_BYTES_V0, REPLAY_SCAN_LIMITS)?;
        let wire: ReplayCandidateWireV0 = serde_json::from_slice(body)
            .map_err(|_| ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape))?;
        let candidate = wire.try_into_candidate()?;
        Ok(Self { candidate })
    }

    pub fn replay(&self) -> &TrajectoryReplayCandidateV0 {
        &self.candidate
    }
}

/// Success artifact minted only after recomputation and receipt authorization.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct VerifiedTrajectoryReplayV0 {
    verification_format: &'static str,
    verification_version: &'static str,
    replay: TrajectoryReplayCandidateV0,
    authority_receipt: super::authority::SignedReplayAuthorityReceiptV0,
}

impl VerifiedTrajectoryReplayV0 {
    pub fn replay(&self) -> &TrajectoryReplayCandidateV0 {
        &self.replay
    }

    pub fn to_json_line(&self) -> ReplayResultV0<Vec<u8>> {
        serialize_json_line(self, MAX_VERIFIED_TRAJECTORY_REPLAY_BYTES_V0)
    }
}

/// Recomputes the candidate and requires a separately verified authority receipt.
pub fn verify_trajectory_replay_v0(
    validated: &ValidatedTrajectoryTraceV0<'_>,
    supplied: &InspectedTrajectoryReplayCandidateV0,
    authority_receipt: &VerifiedReplayAuthorityReceiptV0,
) -> ReplayResultV0<VerifiedTrajectoryReplayV0> {
    let recomputed = trajectory_replay_candidate_v0(validated);
    if supplied.candidate != recomputed {
        return Err(ReplayErrorV0::new(ReplayErrorCodeV0::CandidateMismatch));
    }
    let expected_anchor = ReplayAuthorityAnchorV0::from_replay_candidate(&recomputed);
    if authority_receipt.anchor() != &expected_anchor {
        return Err(ReplayErrorV0::new(
            ReplayErrorCodeV0::AuthorityBindingMismatch,
        ));
    }
    Ok(VerifiedTrajectoryReplayV0 {
        verification_format: TRAJECTORY_REPLAY_VERIFICATION_FORMAT_V0,
        verification_version: TRAJECTORY_REPLAY_VERIFICATION_VERSION_V0,
        replay: recomputed,
        authority_receipt: authority_receipt.receipt().clone(),
    })
}

/// Builds a deterministic candidate from the proof token returned by trajectory validation.
pub fn trajectory_replay_candidate_v0(
    validated: &ValidatedTrajectoryTraceV0<'_>,
) -> TrajectoryReplayCandidateV0 {
    let trace = validated.trace;
    let trajectory_digest = ReplayDigestV0::from_validated(&validated.trajectory_digest());
    let schema = ReplayArtifactBindingV0::from_validated(&trace.schema);
    let adapter = ReplayArtifactBindingV0::from_validated(&trace.adapter);
    let policy = ReplayArtifactBindingV0::from_validated(&trace.policy);
    let raw_capture = ReplayRawCaptureSealV0::from_validated(&trace.raw_capture);
    let record_count =
        u64::try_from(trace.events.len()).expect("validated v0 event count always fits into u64");
    let record_count_bytes = record_count.to_be_bytes();
    let raw_record_count_bytes = raw_capture.record_count.to_be_bytes();
    let genesis_head = ReplayDigestV0::hash(
        REPLAY_GENESIS_DOMAIN_V0,
        &[
            TRAJECTORY_REPLAY_FORMAT_V0.as_bytes(),
            TRAJECTORY_REPLAY_VERSION_V0.as_bytes(),
            schema.identity.as_bytes(),
            schema.version.as_bytes(),
            schema.hash.as_str().as_bytes(),
            adapter.identity.as_bytes(),
            adapter.version.as_bytes(),
            adapter.hash.as_str().as_bytes(),
            policy.identity.as_bytes(),
            policy.version.as_bytes(),
            policy.hash.as_str().as_bytes(),
            &raw_record_count_bytes,
            raw_capture.digest.as_str().as_bytes(),
            trajectory_digest.as_str().as_bytes(),
            &record_count_bytes,
        ],
    );

    let mut previous_head = genesis_head.clone();
    let mut records = Vec::with_capacity(trace.events.len());
    for (event, canonical_event) in trace
        .events
        .iter()
        .zip(validated.canonical_event_components())
    {
        let sequence_index = event
            .sequence_index
            .value
            .expect("validated v0 sequence index is present");
        let event_id = event
            .event_id
            .value
            .as_deref()
            .expect("validated v0 event ID is present")
            .to_string();
        let raw_record_digest = ReplayDigestV0::from_validated(&event.raw_record.digest);
        let canonical_event_digest =
            ReplayDigestV0::hash(REPLAY_CANONICAL_EVENT_DOMAIN_V0, &[&canonical_event]);
        let sequence_bytes = sequence_index.to_be_bytes();
        let resulting_head = ReplayDigestV0::hash(
            REPLAY_CHAIN_STEP_DOMAIN_V0,
            &[
                previous_head.as_str().as_bytes(),
                &sequence_bytes,
                event_id.as_bytes(),
                raw_record_digest.as_str().as_bytes(),
                canonical_event_digest.as_str().as_bytes(),
            ],
        );
        records.push(ReplayRecordV0 {
            sequence_index,
            event_id,
            raw_record_digest,
            canonical_event_digest,
            previous_head: previous_head.clone(),
            resulting_head: resulting_head.clone(),
        });
        previous_head = resulting_head;
    }

    TrajectoryReplayCandidateV0 {
        replay_format: TRAJECTORY_REPLAY_FORMAT_V0,
        replay_version: TRAJECTORY_REPLAY_VERSION_V0,
        schema,
        adapter,
        policy,
        raw_capture,
        trajectory_digest,
        record_count,
        genesis_head,
        records,
        final_head: previous_head,
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ExactRawRecordSetWireV0 {
    record_set_format: String,
    record_set_version: String,
    records: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TrajectoryValidationDeclarationsWireV0 {
    declarations_format: String,
    declarations_version: String,
    adapter: ArtifactBindingV0,
    policy: ArtifactBindingV0,
    raw_capture: RawCaptureSealV0,
    allowed_derivations: Vec<ArtifactBindingV0>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ReplayCandidateWireV0 {
    replay_format: String,
    replay_version: String,
    schema: ArtifactBindingV0,
    adapter: ArtifactBindingV0,
    policy: ArtifactBindingV0,
    raw_capture: RawCaptureSealV0,
    trajectory_digest: String,
    record_count: u64,
    genesis_head: String,
    records: Vec<ReplayRecordWireV0>,
    final_head: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ReplayRecordWireV0 {
    sequence_index: u64,
    event_id: String,
    raw_record_digest: String,
    canonical_event_digest: String,
    previous_head: String,
    resulting_head: String,
}

impl ReplayCandidateWireV0 {
    fn try_into_candidate(self) -> ReplayResultV0<TrajectoryReplayCandidateV0> {
        if self.replay_format != TRAJECTORY_REPLAY_FORMAT_V0
            || self.replay_version != TRAJECTORY_REPLAY_VERSION_V0
        {
            return Err(ReplayErrorV0::new(ReplayErrorCodeV0::UnsupportedFormat));
        }
        let schema = parse_binding(self.schema)?;
        let adapter = parse_binding(self.adapter)?;
        let policy = parse_binding(self.policy)?;
        let raw_capture = parse_capture(self.raw_capture)?;
        let trajectory_digest = ReplayDigestV0::parse(self.trajectory_digest)?;
        let genesis_head = ReplayDigestV0::parse(self.genesis_head)?;
        let final_head = ReplayDigestV0::parse(self.final_head)?;
        if self.records.is_empty()
            || self.records.len() > MAX_EVENTS_V0
            || u64::try_from(self.records.len()).ok() != Some(self.record_count)
            || raw_capture.record_count != self.record_count
        {
            return Err(ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape));
        }

        let mut records = Vec::with_capacity(self.records.len());
        let mut expected_previous = genesis_head.clone();
        for (index, record) in self.records.into_iter().enumerate() {
            let expected_index = u64::try_from(index)
                .map_err(|_| ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape))?;
            if record.sequence_index != expected_index
                || validation::validate_identifier("replay event ID", &record.event_id).is_err()
            {
                return Err(ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape));
            }
            let previous_head = ReplayDigestV0::parse(record.previous_head)?;
            if previous_head != expected_previous {
                return Err(ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape));
            }
            let resulting_head = ReplayDigestV0::parse(record.resulting_head)?;
            records.push(ReplayRecordV0 {
                sequence_index: record.sequence_index,
                event_id: record.event_id,
                raw_record_digest: ReplayDigestV0::parse(record.raw_record_digest)?,
                canonical_event_digest: ReplayDigestV0::parse(record.canonical_event_digest)?,
                previous_head,
                resulting_head: resulting_head.clone(),
            });
            expected_previous = resulting_head;
        }
        if expected_previous != final_head {
            return Err(ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape));
        }

        Ok(TrajectoryReplayCandidateV0 {
            replay_format: TRAJECTORY_REPLAY_FORMAT_V0,
            replay_version: TRAJECTORY_REPLAY_VERSION_V0,
            schema,
            adapter,
            policy,
            raw_capture,
            trajectory_digest,
            record_count: self.record_count,
            genesis_head,
            records,
            final_head,
        })
    }
}

pub(super) fn parse_binding(binding: ArtifactBindingV0) -> ReplayResultV0<ReplayArtifactBindingV0> {
    validation::validate_binding("replay binding", &binding)
        .map_err(|_| ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape))?;
    Ok(ReplayArtifactBindingV0::from_validated(&binding))
}

pub(super) fn parse_capture(seal: RawCaptureSealV0) -> ReplayResultV0<ReplayRawCaptureSealV0> {
    Ok(ReplayRawCaptureSealV0 {
        record_count: seal.record_count,
        digest: ReplayDigestV0::parse(seal.digest)?,
    })
}

pub(super) fn preflight_json_line(
    input: &[u8],
    cap: usize,
    scan_limits: JsonScanLimits,
) -> ReplayResultV0<&[u8]> {
    if input.len() > cap {
        return Err(ReplayErrorV0::new(ReplayErrorCodeV0::InputTooLarge));
    }
    if input.is_empty()
        || input.last() != Some(&b'\n')
        || input[..input.len() - 1].contains(&b'\n')
        || input.contains(&b'\r')
    {
        return Err(ReplayErrorV0::new(ReplayErrorCodeV0::JsonFraming));
    }
    let body = &input[..input.len() - 1];
    match duplicate_json::scan_json_with_limits(body, "trajectory replay", scan_limits) {
        Ok(JsonRootKind::Object) => Ok(body),
        Ok(JsonRootKind::NonObject) => Err(ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape)),
        Err(error) => Err(ReplayErrorV0::new(if error.is_budget() {
            ReplayErrorCodeV0::InputTooLarge
        } else {
            ReplayErrorCodeV0::JsonSyntax
        })),
    }
}

fn preflight_json_object(
    input: &[u8],
    cap: usize,
    scan_limits: JsonScanLimits,
) -> ReplayResultV0<&[u8]> {
    if input.len() > cap {
        return Err(ReplayErrorV0::new(ReplayErrorCodeV0::InputTooLarge));
    }
    match duplicate_json::scan_json_with_limits(input, "trajectory replay input", scan_limits) {
        Ok(JsonRootKind::Object) => Ok(input),
        Ok(JsonRootKind::NonObject) => Err(ReplayErrorV0::new(ReplayErrorCodeV0::JsonShape)),
        Err(error) => Err(ReplayErrorV0::new(if error.is_budget() {
            ReplayErrorCodeV0::InputTooLarge
        } else {
            ReplayErrorCodeV0::JsonSyntax
        })),
    }
}

pub(super) fn serialize_json_line<T: Serialize>(value: &T, cap: usize) -> ReplayResultV0<Vec<u8>> {
    let mut bytes = serde_json::to_vec(value)
        .map_err(|_| ReplayErrorV0::new(ReplayErrorCodeV0::Serialization))?;
    if bytes.len() >= cap {
        return Err(ReplayErrorV0::new(ReplayErrorCodeV0::InputTooLarge));
    }
    bytes.push(b'\n');
    Ok(bytes)
}

fn is_digest(value: &str) -> bool {
    value.strip_prefix("sha256:").is_some_and(|hex| {
        hex.len() == 64
            && hex
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    })
}
