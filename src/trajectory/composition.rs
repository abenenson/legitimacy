use super::{
    ArtifactBindingV0, MAX_EVENTS_V0, NormalizedEventKindV0, ValidatedTrajectoryTraceV0,
    VerifiedTrajectoryReplayV0, artifact_digest_v0, trajectory_replay_candidate_v0,
};
use crate::{
    Decision, GovernanceClaim, GovernanceGraph, graph::traverse::traverse_final_decisions,
    policy::GraphPolicySpec,
};
use serde::{Deserialize, Serialize, Serializer};
use std::collections::BTreeMap;

pub const TRAJECTORY_COMPOSITION_POLICY_FORMAT_V0: &str =
    "legitimacy.trajectory-composition.policy";
pub const TRAJECTORY_COMPOSITION_POLICY_FORMAT_VERSION_V0: &str = "0";
pub const TRAJECTORY_COMPOSITION_POLICY_ID_V0: &str = "policy.trajectory-composition.peer-half";
pub const TRAJECTORY_COMPOSITION_POLICY_VERSION_V0: &str = "0";
pub const OCCURRENCE_ENCODER_ID_V0: &str =
    "legitimacy.trajectory-composition.occurrence-index-strength";
pub const OCCURRENCE_ENCODER_VERSION_V0: &str = "0";
pub const HISTORICAL_PROPERTY_ID_V0: &str =
    "legitimacy.trajectory-composition.every-observed-prefix-green";
pub const HISTORICAL_PROPERTY_VERSION_V0: &str = "0";
pub const TRAJECTORY_COMPOSITION_POLICY_BYTES_V0: &[u8] =
    include_bytes!("../../fixtures/trajectory-composition-v0/policy.toml");
/// Maximum exact composition-policy input: the one 691-byte authority supported by v0.
pub const MAX_TRAJECTORY_COMPOSITION_POLICY_BYTES_V0: usize = 691;
pub const TRAJECTORY_COMPOSITION_RESULT_FORMAT_V0: &str =
    "legitimacy.trajectory-composition.result";
pub const TRAJECTORY_COMPOSITION_RESULT_VERSION_V0: &str = "0";
pub const MAX_TRAJECTORY_COMPOSITION_RESULT_BYTES_V0: usize = 16 * 1024 * 1024;

const GRAPH_NAME_V0: &str = "trajectory-composition-peer-half";
const GRAPH_VERSION_V0: &str = "0";
const NODE_ID_V0: &str = "peer-half";
const _: [(); MAX_TRAJECTORY_COMPOSITION_POLICY_BYTES_V0] =
    [(); TRAJECTORY_COMPOSITION_POLICY_BYTES_V0.len()];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrajectoryCompositionErrorCodeV0 {
    PolicyTooLarge,
    ReplayPairMismatch,
    PolicyDigestMismatch,
    PolicyIdentityMismatch,
    PolicyVersionMismatch,
    PolicyEncoding,
    PolicyShape,
    UnsupportedPolicyProfile,
    NonCanonicalPolicy,
    GraphCompilation,
    EventReplayMismatch,
    OccurrenceOverflow,
    GraphEvaluation,
    NonBinaryDecision,
    ResultTooLarge,
    ResultSerialization,
}

impl TrajectoryCompositionErrorCodeV0 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::PolicyTooLarge => "policy-too-large",
            Self::ReplayPairMismatch => "replay-pair-mismatch",
            Self::PolicyDigestMismatch => "policy-digest-mismatch",
            Self::PolicyIdentityMismatch => "policy-identity-mismatch",
            Self::PolicyVersionMismatch => "policy-version-mismatch",
            Self::PolicyEncoding => "policy-encoding",
            Self::PolicyShape => "policy-shape",
            Self::UnsupportedPolicyProfile => "unsupported-policy-profile",
            Self::NonCanonicalPolicy => "noncanonical-policy",
            Self::GraphCompilation => "graph-compilation",
            Self::EventReplayMismatch => "event-replay-mismatch",
            Self::OccurrenceOverflow => "occurrence-overflow",
            Self::GraphEvaluation => "graph-evaluation",
            Self::NonBinaryDecision => "non-binary-decision",
            Self::ResultTooLarge => "result-too-large",
            Self::ResultSerialization => "result-serialization",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrajectoryCompositionErrorV0 {
    code: TrajectoryCompositionErrorCodeV0,
}

impl TrajectoryCompositionErrorV0 {
    const fn new(code: TrajectoryCompositionErrorCodeV0) -> Self {
        Self { code }
    }

    pub const fn code(&self) -> TrajectoryCompositionErrorCodeV0 {
        self.code
    }
}

impl std::fmt::Display for TrajectoryCompositionErrorV0 {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self.code.as_str())
    }
}

impl std::error::Error for TrajectoryCompositionErrorV0 {}

type CompositionResultV0<T> = Result<T, TrajectoryCompositionErrorV0>;

#[derive(Clone, Debug, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
struct TrajectoryCompositionPolicyEnvelopeV0 {
    policy_format: String,
    policy_format_version: String,
    policy_identity: String,
    policy_version: String,
    occurrence_encoder_identity: String,
    occurrence_encoder_version: String,
    historical_property_identity: String,
    historical_property_version: String,
    #[serde(flatten)]
    graph: GraphPolicySpec,
}

#[derive(Debug)]
pub(super) struct ExecutableTrajectoryCompositionPolicyV0 {
    canonical_bytes: Vec<u8>,
    artifact_digest: String,
    graph: GovernanceGraph,
}

#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum BinaryPolicyDecisionV0 {
    Permit,
    Deny,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct EncodedOccurrenceClaimV0 {
    occurrence_index: u64,
    claimant_wire_id: String,
    strength_numerator: u64,
    strength_denominator: u64,
    event_id: String,
    kind: NormalizedEventKindV0,
    source_item_id: Option<String>,
    raw_record_digest: String,
    canonical_event_digest: String,
}

impl EncodedOccurrenceClaimV0 {
    pub const fn occurrence_index(&self) -> u64 {
        self.occurrence_index
    }

    pub fn claimant_wire_id(&self) -> &str {
        &self.claimant_wire_id
    }

    pub const fn strength_numerator(&self) -> u64 {
        self.strength_numerator
    }

    pub const fn strength_denominator(&self) -> u64 {
        self.strength_denominator
    }

    pub fn event_id(&self) -> &str {
        &self.event_id
    }

    pub const fn kind(&self) -> &NormalizedEventKindV0 {
        &self.kind
    }

    pub fn source_item_id(&self) -> Option<&str> {
        self.source_item_id.as_deref()
    }

    pub fn raw_record_digest(&self) -> &str {
        &self.raw_record_digest
    }

    pub fn canonical_event_digest(&self) -> &str {
        &self.canonical_event_digest
    }
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct EventPolicyReceiptV0 {
    claim: EncodedOccurrenceClaimV0,
    singleton_decision: BinaryPolicyDecisionV0,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ObservedPrefixReceiptV0 {
    prefix_length: u64,
    decision: BinaryPolicyDecisionV0,
    least_denied_occurrence_index: Option<u64>,
}

impl ObservedPrefixReceiptV0 {
    pub const fn prefix_length(&self) -> u64 {
        self.prefix_length
    }

    pub const fn decision(&self) -> BinaryPolicyDecisionV0 {
        self.decision
    }

    pub const fn least_denied_occurrence_index(&self) -> Option<u64> {
        self.least_denied_occurrence_index
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TemporalCompositionKindV0 {
    LocalFailure,
    AllSingletonsPermitAndSafe,
    AllSingletonsPermitAndEarliestViolation,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
#[serde(tag = "classification", rename_all = "kebab-case")]
enum TemporalCompositionClassificationV0 {
    LocalFailure {
        occurrence_index: u64,
        event_id: String,
        decision: BinaryPolicyDecisionV0,
    },
    AllSingletonsPermitAndSafe {
        checked_prefix_count: u64,
    },
    AllSingletonsPermitAndEarliestViolation {
        transition_index: u64,
        prefix_length: u64,
        denied_occurrence_index: u64,
        denied_event_id: String,
        decision: BinaryPolicyDecisionV0,
    },
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct TemporalCompositionResultV0 {
    classification: TemporalCompositionClassificationV0,
    observed_prefixes: Vec<ObservedPrefixReceiptV0>,
}

impl TemporalCompositionResultV0 {
    pub const fn kind(&self) -> TemporalCompositionKindV0 {
        match self.classification {
            TemporalCompositionClassificationV0::LocalFailure { .. } => {
                TemporalCompositionKindV0::LocalFailure
            }
            TemporalCompositionClassificationV0::AllSingletonsPermitAndSafe { .. } => {
                TemporalCompositionKindV0::AllSingletonsPermitAndSafe
            }
            TemporalCompositionClassificationV0::AllSingletonsPermitAndEarliestViolation {
                ..
            } => TemporalCompositionKindV0::AllSingletonsPermitAndEarliestViolation,
        }
    }

    pub fn observed_prefixes(&self) -> &[ObservedPrefixReceiptV0] {
        &self.observed_prefixes
    }

    pub const fn local_failure_occurrence_index(&self) -> Option<u64> {
        match &self.classification {
            TemporalCompositionClassificationV0::LocalFailure {
                occurrence_index, ..
            } => Some(*occurrence_index),
            _ => None,
        }
    }

    pub const fn transition_index(&self) -> Option<u64> {
        match &self.classification {
            TemporalCompositionClassificationV0::AllSingletonsPermitAndEarliestViolation {
                transition_index,
                ..
            } => Some(*transition_index),
            _ => None,
        }
    }

    pub const fn prefix_length(&self) -> Option<u64> {
        match &self.classification {
            TemporalCompositionClassificationV0::AllSingletonsPermitAndEarliestViolation {
                prefix_length,
                ..
            } => Some(*prefix_length),
            _ => None,
        }
    }

    pub const fn denied_occurrence_index(&self) -> Option<u64> {
        match &self.classification {
            TemporalCompositionClassificationV0::AllSingletonsPermitAndEarliestViolation {
                denied_occurrence_index,
                ..
            } => Some(*denied_occurrence_index),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct TrajectoryCompositionPolicyArtifactV0 {
    identity: &'static str,
    version: &'static str,
    artifact_digest: String,
    #[serde(rename = "canonical_bytes_hex", serialize_with = "serialize_lower_hex")]
    canonical_bytes: Vec<u8>,
    occurrence_encoder_identity: &'static str,
    occurrence_encoder_version: &'static str,
    historical_property_identity: &'static str,
    historical_property_version: &'static str,
}

impl TrajectoryCompositionPolicyArtifactV0 {
    pub const fn identity(&self) -> &str {
        self.identity
    }

    pub const fn version(&self) -> &str {
        self.version
    }

    pub fn artifact_digest(&self) -> &str {
        &self.artifact_digest
    }

    pub fn canonical_bytes(&self) -> &[u8] {
        &self.canonical_bytes
    }

    pub const fn occurrence_encoder_identity(&self) -> &str {
        self.occurrence_encoder_identity
    }

    pub const fn occurrence_encoder_version(&self) -> &str {
        self.occurrence_encoder_version
    }

    pub const fn historical_property_identity(&self) -> &str {
        self.historical_property_identity
    }

    pub const fn historical_property_version(&self) -> &str {
        self.historical_property_version
    }
}

/// Successful output can only be minted by evaluation.
///
/// Result bytes are inspectable but are not an admission path:
///
/// ```compile_fail
/// use legitimacy::TrajectoryCompositionResultV0;
///
/// let _: TrajectoryCompositionResultV0 = serde_json::from_slice(b"{}").unwrap();
/// ```
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct TrajectoryCompositionResultV0 {
    result_format: &'static str,
    result_version: &'static str,
    trajectory_digest: String,
    replay_final_head: String,
    policy: TrajectoryCompositionPolicyArtifactV0,
    event_receipts: Vec<EventPolicyReceiptV0>,
    temporal: TemporalCompositionResultV0,
}

impl TrajectoryCompositionResultV0 {
    pub fn trajectory_digest(&self) -> &str {
        &self.trajectory_digest
    }

    pub fn replay_final_head(&self) -> &str {
        &self.replay_final_head
    }

    pub const fn policy(&self) -> &TrajectoryCompositionPolicyArtifactV0 {
        &self.policy
    }

    pub fn event_receipts(&self) -> &[EventPolicyReceiptV0] {
        &self.event_receipts
    }

    pub const fn temporal(&self) -> &TemporalCompositionResultV0 {
        &self.temporal
    }

    /// Deterministic inspection/sealing bytes. Decoding these bytes does not mint authority.
    pub fn to_json_line(&self) -> CompositionResultV0<Vec<u8>> {
        let mut output = serde_json::to_vec(self)
            .map_err(|_| error(TrajectoryCompositionErrorCodeV0::ResultSerialization))?;
        let output_length = output
            .len()
            .checked_add(1)
            .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::ResultTooLarge))?;
        if output_length > MAX_TRAJECTORY_COMPOSITION_RESULT_BYTES_V0 {
            return Err(error(TrajectoryCompositionErrorCodeV0::ResultTooLarge));
        }
        output.push(b'\n');
        Ok(output)
    }
}

impl EventPolicyReceiptV0 {
    pub const fn claim(&self) -> &EncodedOccurrenceClaimV0 {
        &self.claim
    }

    pub const fn singleton_decision(&self) -> BinaryPolicyDecisionV0 {
        self.singleton_decision
    }
}

#[derive(Debug)]
pub(super) struct PreparedTrajectoryCompositionV0 {
    pub(super) policy: ExecutableTrajectoryCompositionPolicyV0,
    pub(super) trajectory_digest: String,
    pub(super) replay_final_head: String,
    pub(super) claims: Vec<GovernanceClaim>,
    pub(super) receipts: Vec<EventPolicyReceiptV0>,
}

impl ExecutableTrajectoryCompositionPolicyV0 {
    pub(super) fn canonical_bytes(&self) -> &[u8] {
        &self.canonical_bytes
    }

    pub(super) fn artifact_digest(&self) -> &str {
        &self.artifact_digest
    }

    pub(super) fn graph(&self) -> &GovernanceGraph {
        &self.graph
    }
}

pub(super) fn load_trajectory_composition_policy_v0(
    exact_bytes: &[u8],
    binding: &ArtifactBindingV0,
) -> CompositionResultV0<ExecutableTrajectoryCompositionPolicyV0> {
    ensure_policy_size_v0(exact_bytes)?;
    let digest = artifact_digest_v0(exact_bytes);
    if digest != binding.hash {
        return Err(error(
            TrajectoryCompositionErrorCodeV0::PolicyDigestMismatch,
        ));
    }

    let input = std::str::from_utf8(exact_bytes)
        .map_err(|_| error(TrajectoryCompositionErrorCodeV0::PolicyEncoding))?;
    let envelope: TrajectoryCompositionPolicyEnvelopeV0 =
        toml::from_str(input).map_err(|_| error(TrajectoryCompositionErrorCodeV0::PolicyShape))?;

    if envelope.policy_identity != binding.identity {
        return Err(error(
            TrajectoryCompositionErrorCodeV0::PolicyIdentityMismatch,
        ));
    }
    if envelope.policy_version != binding.version {
        return Err(error(
            TrajectoryCompositionErrorCodeV0::PolicyVersionMismatch,
        ));
    }
    validate_restricted_profile(&envelope)?;

    let canonical = canonical_policy_bytes(&envelope)?;
    if canonical != exact_bytes {
        return Err(error(TrajectoryCompositionErrorCodeV0::NonCanonicalPolicy));
    }

    let graph = envelope
        .graph
        .try_into_graph("trajectory composition policy v0")
        .map_err(|_| error(TrajectoryCompositionErrorCodeV0::GraphCompilation))?;
    Ok(ExecutableTrajectoryCompositionPolicyV0 {
        canonical_bytes: canonical,
        artifact_digest: digest,
        graph,
    })
}

pub(super) fn prepare_replay_bound_composition_v0(
    validated: &ValidatedTrajectoryTraceV0<'_>,
    verified: &VerifiedTrajectoryReplayV0,
    exact_policy_bytes: &[u8],
) -> CompositionResultV0<PreparedTrajectoryCompositionV0> {
    ensure_policy_size_v0(exact_policy_bytes)?;
    let recomputed_replay = trajectory_replay_candidate_v0(validated);
    if &recomputed_replay != verified.replay() {
        return Err(error(TrajectoryCompositionErrorCodeV0::ReplayPairMismatch));
    }

    let trace = validated.trace;
    let policy = load_trajectory_composition_policy_v0(exact_policy_bytes, &trace.policy)?;
    let replay = verified.replay();
    if trace.events.len() != replay.records().len() {
        return Err(error(TrajectoryCompositionErrorCodeV0::EventReplayMismatch));
    }

    let mut claims = Vec::with_capacity(trace.events.len());
    let mut receipts = Vec::with_capacity(trace.events.len());
    for (index, (event, replay_record)) in
        trace.events.iter().zip(replay.records().iter()).enumerate()
    {
        let occurrence_index = u64::try_from(index)
            .map_err(|_| error(TrajectoryCompositionErrorCodeV0::OccurrenceOverflow))?;
        let strength_numerator = occurrence_index
            .checked_add(1)
            .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::OccurrenceOverflow))?;
        if strength_numerator > MAX_EVENTS_V0 as u64 {
            return Err(error(TrajectoryCompositionErrorCodeV0::OccurrenceOverflow));
        }
        let event_id = event
            .event_id
            .value
            .as_deref()
            .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::EventReplayMismatch))?;
        let sequence_index = event
            .sequence_index
            .value
            .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::EventReplayMismatch))?;
        let kind = event
            .kind
            .value
            .as_ref()
            .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::EventReplayMismatch))?;
        let source_item_id = event
            .source_item_id
            .as_ref()
            .map(|source| {
                source
                    .value
                    .as_deref()
                    .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::EventReplayMismatch))
            })
            .transpose()?;

        if sequence_index != occurrence_index
            || replay_record.sequence_index() != occurrence_index
            || replay_record.event_id() != event_id
            || replay_record.raw_record_digest() != event.raw_record.digest
        {
            return Err(error(TrajectoryCompositionErrorCodeV0::EventReplayMismatch));
        }

        let claimant_wire_id = format!("occurrence:{occurrence_index}");
        let graph_claim = GovernanceClaim {
            claimant_id: claimant_wire_id.clone(),
            strength: strength_numerator as f64,
            priority_class: None,
            path: None,
            action: None,
            content: None,
            metrics: BTreeMap::new(),
        };
        let decisions =
            traverse_final_decisions(policy.graph(), std::slice::from_ref(&graph_claim))
                .map_err(|_| error(TrajectoryCompositionErrorCodeV0::GraphEvaluation))?;
        let singleton_decision = decisions
            .get(&claimant_wire_id)
            .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::GraphEvaluation))?
            .try_into()?;

        claims.push(graph_claim);
        receipts.push(EventPolicyReceiptV0 {
            claim: EncodedOccurrenceClaimV0 {
                occurrence_index,
                claimant_wire_id,
                strength_numerator,
                strength_denominator: 1,
                event_id: event_id.to_string(),
                kind: kind.clone(),
                source_item_id: source_item_id.map(str::to_string),
                raw_record_digest: event.raw_record.digest.clone(),
                canonical_event_digest: replay_record.canonical_event_digest().to_string(),
            },
            singleton_decision,
        });
    }

    Ok(PreparedTrajectoryCompositionV0 {
        policy,
        trajectory_digest: replay.trajectory_digest().to_string(),
        replay_final_head: replay.final_head().to_string(),
        claims,
        receipts,
    })
}

/// Evaluates one validated/replay-matched trajectory under the exact supplied policy bytes.
pub fn evaluate_replay_bound_composition_v0(
    validated: &ValidatedTrajectoryTraceV0<'_>,
    verified: &VerifiedTrajectoryReplayV0,
    exact_policy_bytes: &[u8],
) -> CompositionResultV0<TrajectoryCompositionResultV0> {
    let prepared = prepare_replay_bound_composition_v0(validated, verified, exact_policy_bytes)?;
    let temporal = classify_temporal_composition_v0(&prepared)?;
    Ok(TrajectoryCompositionResultV0 {
        result_format: TRAJECTORY_COMPOSITION_RESULT_FORMAT_V0,
        result_version: TRAJECTORY_COMPOSITION_RESULT_VERSION_V0,
        trajectory_digest: prepared.trajectory_digest,
        replay_final_head: prepared.replay_final_head,
        policy: TrajectoryCompositionPolicyArtifactV0 {
            identity: TRAJECTORY_COMPOSITION_POLICY_ID_V0,
            version: TRAJECTORY_COMPOSITION_POLICY_VERSION_V0,
            artifact_digest: prepared.policy.artifact_digest().to_string(),
            canonical_bytes: prepared.policy.canonical_bytes().to_vec(),
            occurrence_encoder_identity: OCCURRENCE_ENCODER_ID_V0,
            occurrence_encoder_version: OCCURRENCE_ENCODER_VERSION_V0,
            historical_property_identity: HISTORICAL_PROPERTY_ID_V0,
            historical_property_version: HISTORICAL_PROPERTY_VERSION_V0,
        },
        event_receipts: prepared.receipts,
        temporal,
    })
}

fn classify_temporal_composition_v0(
    prepared: &PreparedTrajectoryCompositionV0,
) -> CompositionResultV0<TemporalCompositionResultV0> {
    if let Some(receipt) = prepared
        .receipts
        .iter()
        .find(|receipt| receipt.singleton_decision == BinaryPolicyDecisionV0::Deny)
    {
        return Ok(TemporalCompositionResultV0 {
            classification: TemporalCompositionClassificationV0::LocalFailure {
                occurrence_index: receipt.claim.occurrence_index,
                event_id: receipt.claim.event_id.clone(),
                decision: BinaryPolicyDecisionV0::Deny,
            },
            observed_prefixes: Vec::new(),
        });
    }

    let mut observed_prefixes = Vec::with_capacity(prepared.claims.len());
    for prefix_length in 1..=prepared.claims.len() {
        let prefix = prepared
            .claims
            .get(..prefix_length)
            .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::GraphEvaluation))?;
        let decisions = traverse_final_decisions(prepared.policy.graph(), prefix)
            .map_err(|_| error(TrajectoryCompositionErrorCodeV0::GraphEvaluation))?;
        let least_denied = least_denied_occurrence_v0(prefix, &decisions)?;
        let prefix_length_u64 = u64::try_from(prefix_length)
            .map_err(|_| error(TrajectoryCompositionErrorCodeV0::OccurrenceOverflow))?;
        observed_prefixes.push(ObservedPrefixReceiptV0 {
            prefix_length: prefix_length_u64,
            decision: if least_denied.is_some() {
                BinaryPolicyDecisionV0::Deny
            } else {
                BinaryPolicyDecisionV0::Permit
            },
            least_denied_occurrence_index: least_denied,
        });

        if let Some(denied_occurrence_index) = least_denied {
            let transition_index = prefix_length_u64
                .checked_sub(1)
                .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::OccurrenceOverflow))?;
            let denied_receipt = prepared
                .receipts
                .get(
                    usize::try_from(denied_occurrence_index)
                        .map_err(|_| error(TrajectoryCompositionErrorCodeV0::OccurrenceOverflow))?,
                )
                .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::GraphEvaluation))?;
            return Ok(TemporalCompositionResultV0 {
                classification:
                    TemporalCompositionClassificationV0::AllSingletonsPermitAndEarliestViolation {
                        transition_index,
                        prefix_length: prefix_length_u64,
                        denied_occurrence_index,
                        denied_event_id: denied_receipt.claim.event_id.clone(),
                        decision: BinaryPolicyDecisionV0::Deny,
                    },
                observed_prefixes,
            });
        }
    }

    Ok(TemporalCompositionResultV0 {
        classification: TemporalCompositionClassificationV0::AllSingletonsPermitAndSafe {
            checked_prefix_count: u64::try_from(prepared.claims.len())
                .map_err(|_| error(TrajectoryCompositionErrorCodeV0::OccurrenceOverflow))?,
        },
        observed_prefixes,
    })
}

fn least_denied_occurrence_v0(
    claims: &[GovernanceClaim],
    decisions: &BTreeMap<String, Decision>,
) -> CompositionResultV0<Option<u64>> {
    for (index, claim) in claims.iter().enumerate() {
        let decision = decisions
            .get(&claim.claimant_id)
            .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::GraphEvaluation))?;
        match decision {
            Decision::Permit => {}
            Decision::Deny => {
                return u64::try_from(index)
                    .map(Some)
                    .map_err(|_| error(TrajectoryCompositionErrorCodeV0::OccurrenceOverflow));
            }
            Decision::Escalate => {
                return Err(error(TrajectoryCompositionErrorCodeV0::NonBinaryDecision));
            }
        }
    }
    if decisions.len() != claims.len() {
        return Err(error(TrajectoryCompositionErrorCodeV0::GraphEvaluation));
    }
    Ok(None)
}

fn serialize_lower_hex<S>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    serializer.serialize_str(&output)
}

impl TryFrom<&Decision> for BinaryPolicyDecisionV0 {
    type Error = TrajectoryCompositionErrorV0;

    fn try_from(decision: &Decision) -> Result<Self, Self::Error> {
        match decision {
            Decision::Permit => Ok(Self::Permit),
            Decision::Deny => Ok(Self::Deny),
            Decision::Escalate => Err(error(TrajectoryCompositionErrorCodeV0::NonBinaryDecision)),
        }
    }
}

fn validate_restricted_profile(
    envelope: &TrajectoryCompositionPolicyEnvelopeV0,
) -> CompositionResultV0<()> {
    let supported_envelope = envelope.policy_format == TRAJECTORY_COMPOSITION_POLICY_FORMAT_V0
        && envelope.policy_format_version == TRAJECTORY_COMPOSITION_POLICY_FORMAT_VERSION_V0
        && envelope.policy_identity == TRAJECTORY_COMPOSITION_POLICY_ID_V0
        && envelope.policy_version == TRAJECTORY_COMPOSITION_POLICY_VERSION_V0
        && envelope.occurrence_encoder_identity == OCCURRENCE_ENCODER_ID_V0
        && envelope.occurrence_encoder_version == OCCURRENCE_ENCODER_VERSION_V0
        && envelope.historical_property_identity == HISTORICAL_PROPERTY_ID_V0
        && envelope.historical_property_version == HISTORICAL_PROPERTY_VERSION_V0
        && envelope.graph.graph.name == GRAPH_NAME_V0
        && envelope.graph.graph.version == GRAPH_VERSION_V0
        && envelope.graph.edges.is_empty()
        && envelope.graph.nodes.len() == 1;
    if !supported_envelope {
        return Err(error(
            TrajectoryCompositionErrorCodeV0::UnsupportedPolicyProfile,
        ));
    }

    let Some(node) = envelope.graph.nodes.first() else {
        return Err(error(
            TrajectoryCompositionErrorCodeV0::UnsupportedPolicyProfile,
        ));
    };
    let supported_node = node.id == NODE_ID_V0
        && node.node_type == "binary"
        && node.name.as_deref() == Some(NODE_ID_V0)
        && node.default.as_deref() == Some("deny")
        && node.combination.as_deref() == Some("first_match")
        && node.threshold.is_none()
        && node.field.is_none()
        && node.gates.len() == 1;
    if !supported_node {
        return Err(error(
            TrajectoryCompositionErrorCodeV0::UnsupportedPolicyProfile,
        ));
    }

    let Some(gate) = node.gates.first() else {
        return Err(error(
            TrajectoryCompositionErrorCodeV0::UnsupportedPolicyProfile,
        ));
    };
    let supported_gate = gate.gate_type == "peer_relative"
        && gate.pattern.is_none()
        && gate.value.is_none()
        && gate.regex.is_none()
        && gate.field.as_deref() == Some("strength")
        && gate.min.is_none()
        && gate.percentile == Some(0.5)
        && gate.decision == "permit";
    if !supported_gate {
        return Err(error(
            TrajectoryCompositionErrorCodeV0::UnsupportedPolicyProfile,
        ));
    }
    Ok(())
}

fn canonical_policy_bytes(
    envelope: &TrajectoryCompositionPolicyEnvelopeV0,
) -> CompositionResultV0<Vec<u8>> {
    let node = envelope
        .graph
        .nodes
        .first()
        .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::UnsupportedPolicyProfile))?;
    let gate = node
        .gates
        .first()
        .ok_or_else(|| error(TrajectoryCompositionErrorCodeV0::UnsupportedPolicyProfile))?;
    let mut output = String::new();
    push_quoted_assignment(&mut output, "policy_format", &envelope.policy_format);
    push_quoted_assignment(
        &mut output,
        "policy_format_version",
        &envelope.policy_format_version,
    );
    push_quoted_assignment(&mut output, "policy_identity", &envelope.policy_identity);
    push_quoted_assignment(&mut output, "policy_version", &envelope.policy_version);
    push_quoted_assignment(
        &mut output,
        "occurrence_encoder_identity",
        &envelope.occurrence_encoder_identity,
    );
    push_quoted_assignment(
        &mut output,
        "occurrence_encoder_version",
        &envelope.occurrence_encoder_version,
    );
    push_quoted_assignment(
        &mut output,
        "historical_property_identity",
        &envelope.historical_property_identity,
    );
    push_quoted_assignment(
        &mut output,
        "historical_property_version",
        &envelope.historical_property_version,
    );
    output.push_str("\n[graph]\n");
    push_quoted_assignment(&mut output, "name", &envelope.graph.graph.name);
    push_quoted_assignment(&mut output, "version", &envelope.graph.graph.version);
    output.push_str("\n[[nodes]]\n");
    push_quoted_assignment(&mut output, "id", &node.id);
    push_quoted_assignment(&mut output, "type", &node.node_type);
    push_quoted_assignment(&mut output, "name", node.name.as_deref().unwrap_or(""));
    push_quoted_assignment(
        &mut output,
        "default",
        node.default.as_deref().unwrap_or(""),
    );
    push_quoted_assignment(
        &mut output,
        "combination",
        node.combination.as_deref().unwrap_or(""),
    );
    output.push_str("\n[[nodes.gates]]\n");
    push_quoted_assignment(&mut output, "type", &gate.gate_type);
    push_quoted_assignment(&mut output, "field", gate.field.as_deref().unwrap_or(""));
    output.push_str("percentile = 0.5\n");
    push_quoted_assignment(&mut output, "decision", &gate.decision);
    Ok(output.into_bytes())
}

fn push_quoted_assignment(output: &mut String, key: &str, value: &str) {
    output.push_str(key);
    output.push_str(" = \"");
    output.push_str(value);
    output.push_str("\"\n");
}

fn ensure_policy_size_v0(exact_bytes: &[u8]) -> CompositionResultV0<()> {
    if exact_bytes.len() > MAX_TRAJECTORY_COMPOSITION_POLICY_BYTES_V0 {
        return Err(error(TrajectoryCompositionErrorCodeV0::PolicyTooLarge));
    }
    Ok(())
}

const fn error(code: TrajectoryCompositionErrorCodeV0) -> TrajectoryCompositionErrorV0 {
    TrajectoryCompositionErrorV0::new(code)
}

#[cfg(test)]
#[path = "composition/tests.rs"]
mod tests;
