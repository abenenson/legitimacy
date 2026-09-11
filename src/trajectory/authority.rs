use super::{
    ArtifactBindingV0, MAX_EVENTS_V0, RawCaptureSealV0, ValidatedTrajectoryTraceV0,
    duplicate_json::JsonScanLimits,
    replay::{
        ReplayAuthorityAnchorV0, ReplayErrorCodeV0, parse_binding, parse_capture,
        preflight_json_line, serialize_json_line, trajectory_replay_candidate_v0,
    },
};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use std::fmt;

pub const TRAJECTORY_REPLAY_AUTHORITY_ANCHOR_FORMAT_V0: &str =
    "legitimacy.trajectory.replay-authority-anchor";
pub const TRAJECTORY_REPLAY_AUTHORITY_ANCHOR_VERSION_V0: &str = "0";
pub const TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_FORMAT_V0: &str =
    "legitimacy.trajectory.replay-authority-receipt";
pub const TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_VERSION_V0: &str = "0";
pub const TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_FORMAT_V0: &str =
    "legitimacy.trajectory.replay-authority-trust-policy";
pub const TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_VERSION_V0: &str = "0";
pub const REPLAY_AUTHORITY_ALGORITHM_ED25519_V0: &str = "ed25519";

/// Maximum strict signed replay-authority receipt JSON line (64 KiB).
pub const MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0: usize = 64 * 1024;
/// Maximum strict replay-authority trust-policy JSON input (16 KiB).
pub const MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0: usize = 16 * 1024;

const SIGNATURE_DOMAIN_V0: &[u8] = b"legitimacy.trajectory.replay-authority-receipt.signature.v0\0";
const ED25519_KEY_PREFIX: &str = "ed25519:";
const RECEIPT_SCAN_LIMITS: JsonScanLimits = JsonScanLimits {
    max_depth: 5,
    max_nodes: 96,
    max_total_keys: 96,
    max_decoded_string_bytes: MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0,
};
const TRUST_POLICY_SCAN_LIMITS: JsonScanLimits = JsonScanLimits {
    max_depth: 3,
    max_nodes: 24,
    max_total_keys: 24,
    max_decoded_string_bytes: MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum ReplayAuthorityErrorCodeV0 {
    InputTooLarge,
    JsonFraming,
    JsonSyntax,
    JsonShape,
    UnsupportedFormat,
    InvalidSigningKey,
    AuthorityRejected,
    Serialization,
}

impl ReplayAuthorityErrorCodeV0 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::InputTooLarge => "input-too-large",
            Self::JsonFraming => "json-framing",
            Self::JsonSyntax => "json-syntax",
            Self::JsonShape => "json-shape",
            Self::UnsupportedFormat => "unsupported-format",
            Self::InvalidSigningKey => "authority-signing-key",
            Self::AuthorityRejected => "authority-receipt-rejected",
            Self::Serialization => "serialization",
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub struct ReplayAuthorityErrorV0 {
    code: ReplayAuthorityErrorCodeV0,
}

impl ReplayAuthorityErrorV0 {
    const fn new(code: ReplayAuthorityErrorCodeV0) -> Self {
        Self { code }
    }

    pub const fn code(&self) -> ReplayAuthorityErrorCodeV0 {
        self.code
    }
}

impl fmt::Display for ReplayAuthorityErrorV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.code.as_str())
    }
}

impl fmt::Debug for ReplayAuthorityErrorV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ReplayAuthorityErrorV0")
            .field("code", &self.code)
            .finish()
    }
}

impl std::error::Error for ReplayAuthorityErrorV0 {}

type AuthorityResultV0<T> = Result<T, ReplayAuthorityErrorV0>;

/// Bounded Ed25519 authority secret. Debug output never contains key material.
pub struct ReplayAuthoritySigningKeyV0(SigningKey);

impl ReplayAuthoritySigningKeyV0 {
    pub fn from_bytes(bytes: &[u8]) -> AuthorityResultV0<Self> {
        let secret: &[u8; 32] = bytes.try_into().map_err(|_| {
            ReplayAuthorityErrorV0::new(ReplayAuthorityErrorCodeV0::InvalidSigningKey)
        })?;
        Ok(Self(SigningKey::from_bytes(secret)))
    }

    pub fn verification_key_text(&self) -> String {
        encode_prefixed_hex(&self.0.verifying_key().to_bytes())
    }
}

impl fmt::Debug for ReplayAuthoritySigningKeyV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("ReplayAuthoritySigningKeyV0([REDACTED])")
    }
}

/// Signed receipt created only from an independently validated trajectory.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct SignedReplayAuthorityReceiptV0 {
    receipt_format: &'static str,
    receipt_version: &'static str,
    issuer: String,
    algorithm: &'static str,
    key_id: String,
    authority_epoch: u64,
    anchor: ReplayAuthorityAnchorV0,
    signature: String,
}

impl SignedReplayAuthorityReceiptV0 {
    pub fn to_json_line(&self) -> AuthorityResultV0<Vec<u8>> {
        serialize_json_line(self, MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0)
            .map_err(map_replay_error)
    }

    pub fn issuer(&self) -> &str {
        &self.issuer
    }

    pub fn key_id(&self) -> &str {
        &self.key_id
    }

    pub fn authority_epoch(&self) -> u64 {
        self.authority_epoch
    }

    fn signature_message(&self) -> Vec<u8> {
        signature_message(
            &self.issuer,
            self.algorithm,
            &self.key_id,
            self.authority_epoch,
            &self.anchor,
        )
    }
}

/// Strictly decoded signed bytes that have not acquired authority.
#[derive(Clone, Debug)]
pub struct UnverifiedReplayAuthorityReceiptV0 {
    receipt: SignedReplayAuthorityReceiptV0,
    signature: Signature,
}

impl UnverifiedReplayAuthorityReceiptV0 {
    pub fn from_json_slice(input: &[u8]) -> AuthorityResultV0<Self> {
        let body = preflight_json_line(
            input,
            MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0,
            RECEIPT_SCAN_LIMITS,
        )
        .map_err(map_replay_error)?;
        let wire: ReplayAuthorityReceiptWireV0 = serde_json::from_slice(body)
            .map_err(|_| ReplayAuthorityErrorV0::new(ReplayAuthorityErrorCodeV0::JsonShape))?;
        wire.try_into_unverified()
    }
}

/// Pinned policy supplied independently from replay artifacts and authority receipts.
#[derive(Clone, Debug)]
pub struct ReplayAuthorityTrustPolicyV0 {
    issuer: String,
    algorithm: String,
    key_id: String,
    accepted_authority_epoch: u64,
    verification_key: VerifyingKey,
}

impl ReplayAuthorityTrustPolicyV0 {
    pub fn from_json_slice(input: &[u8]) -> AuthorityResultV0<Self> {
        let body = preflight_json_line(
            input,
            MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0,
            TRUST_POLICY_SCAN_LIMITS,
        )
        .map_err(map_replay_error)?;
        let wire: ReplayAuthorityTrustPolicyWireV0 = serde_json::from_slice(body)
            .map_err(|_| ReplayAuthorityErrorV0::new(ReplayAuthorityErrorCodeV0::JsonShape))?;
        wire.try_into_policy()
    }
}

/// Receipt whose wire, pinned policy, epoch, and Ed25519 signature all verified.
#[derive(Clone, Debug)]
pub struct VerifiedReplayAuthorityReceiptV0 {
    receipt: SignedReplayAuthorityReceiptV0,
}

impl VerifiedReplayAuthorityReceiptV0 {
    pub(super) fn anchor(&self) -> &ReplayAuthorityAnchorV0 {
        &self.receipt.anchor
    }

    pub(super) fn receipt(&self) -> &SignedReplayAuthorityReceiptV0 {
        &self.receipt
    }
}

/// Independently recomputes the replay tuple from validated trace/raw/context inputs and signs it.
pub fn issue_trajectory_replay_authority_receipt_v0(
    validated: &ValidatedTrajectoryTraceV0<'_>,
    signing_key: &ReplayAuthoritySigningKeyV0,
    issuer: &str,
    key_id: &str,
    authority_epoch: u64,
) -> AuthorityResultV0<SignedReplayAuthorityReceiptV0> {
    validate_authority_name(issuer)?;
    validate_authority_name(key_id)?;
    if authority_epoch == 0 {
        return Err(ReplayAuthorityErrorV0::new(
            ReplayAuthorityErrorCodeV0::JsonShape,
        ));
    }
    let recomputed = trajectory_replay_candidate_v0(validated);
    let anchor = ReplayAuthorityAnchorV0::from_replay_candidate(&recomputed);
    let mut receipt = SignedReplayAuthorityReceiptV0 {
        receipt_format: TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_FORMAT_V0,
        receipt_version: TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_VERSION_V0,
        issuer: issuer.to_string(),
        algorithm: REPLAY_AUTHORITY_ALGORITHM_ED25519_V0,
        key_id: key_id.to_string(),
        authority_epoch,
        anchor,
        signature: String::new(),
    };
    receipt.signature =
        encode_prefixed_hex(&signing_key.0.sign(&receipt.signature_message()).to_bytes());
    Ok(receipt)
}

/// Applies the separately supplied trust policy and verifies the signed complete tuple.
pub fn verify_replay_authority_receipt_v0(
    receipt: UnverifiedReplayAuthorityReceiptV0,
    policy: &ReplayAuthorityTrustPolicyV0,
) -> AuthorityResultV0<VerifiedReplayAuthorityReceiptV0> {
    if receipt.receipt.issuer != policy.issuer
        || receipt.receipt.algorithm != policy.algorithm
        || receipt.receipt.key_id != policy.key_id
        || receipt.receipt.authority_epoch != policy.accepted_authority_epoch
        || policy
            .verification_key
            .verify_strict(&receipt.receipt.signature_message(), &receipt.signature)
            .is_err()
    {
        return Err(ReplayAuthorityErrorV0::new(
            ReplayAuthorityErrorCodeV0::AuthorityRejected,
        ));
    }
    Ok(VerifiedReplayAuthorityReceiptV0 {
        receipt: receipt.receipt,
    })
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ReplayAuthorityReceiptWireV0 {
    receipt_format: String,
    receipt_version: String,
    issuer: String,
    algorithm: String,
    key_id: String,
    authority_epoch: u64,
    anchor: ReplayAuthorityAnchorWireV0,
    signature: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ReplayAuthorityAnchorWireV0 {
    anchor_format: String,
    anchor_version: String,
    replay_format: String,
    replay_version: String,
    schema: ArtifactBindingV0,
    adapter: ArtifactBindingV0,
    policy: ArtifactBindingV0,
    raw_capture: RawCaptureSealV0,
    trajectory_digest: String,
    record_count: u64,
    genesis_head: String,
    expected_final_head: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ReplayAuthorityTrustPolicyWireV0 {
    trust_policy_format: String,
    trust_policy_version: String,
    issuer: String,
    algorithm: String,
    key_id: String,
    accepted_authority_epoch: u64,
    verification_key: String,
}

impl ReplayAuthorityReceiptWireV0 {
    fn try_into_unverified(self) -> AuthorityResultV0<UnverifiedReplayAuthorityReceiptV0> {
        if self.receipt_format != TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_FORMAT_V0
            || self.receipt_version != TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_VERSION_V0
        {
            return Err(ReplayAuthorityErrorV0::new(
                ReplayAuthorityErrorCodeV0::UnsupportedFormat,
            ));
        }
        validate_authority_name(&self.issuer)?;
        validate_authority_name(&self.key_id)?;
        if self.algorithm != REPLAY_AUTHORITY_ALGORITHM_ED25519_V0 || self.authority_epoch == 0 {
            return Err(ReplayAuthorityErrorV0::new(
                ReplayAuthorityErrorCodeV0::UnsupportedFormat,
            ));
        }
        let signature_bytes = decode_prefixed_hex::<64>(&self.signature)?;
        let signature = Signature::from_bytes(&signature_bytes);
        Ok(UnverifiedReplayAuthorityReceiptV0 {
            receipt: SignedReplayAuthorityReceiptV0 {
                receipt_format: TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_FORMAT_V0,
                receipt_version: TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_VERSION_V0,
                issuer: self.issuer,
                algorithm: REPLAY_AUTHORITY_ALGORITHM_ED25519_V0,
                key_id: self.key_id,
                authority_epoch: self.authority_epoch,
                anchor: self.anchor.try_into_anchor()?,
                signature: self.signature,
            },
            signature,
        })
    }
}

impl ReplayAuthorityAnchorWireV0 {
    fn try_into_anchor(self) -> AuthorityResultV0<ReplayAuthorityAnchorV0> {
        if self.anchor_format != TRAJECTORY_REPLAY_AUTHORITY_ANCHOR_FORMAT_V0
            || self.anchor_version != TRAJECTORY_REPLAY_AUTHORITY_ANCHOR_VERSION_V0
            || self.replay_format != super::replay::TRAJECTORY_REPLAY_FORMAT_V0
            || self.replay_version != super::replay::TRAJECTORY_REPLAY_VERSION_V0
        {
            return Err(ReplayAuthorityErrorV0::new(
                ReplayAuthorityErrorCodeV0::UnsupportedFormat,
            ));
        }
        let raw_capture = parse_capture(self.raw_capture).map_err(map_replay_error)?;
        if self.record_count == 0
            || self.record_count > MAX_EVENTS_V0 as u64
            || raw_capture.record_count != self.record_count
        {
            return Err(ReplayAuthorityErrorV0::new(
                ReplayAuthorityErrorCodeV0::JsonShape,
            ));
        }
        Ok(ReplayAuthorityAnchorV0 {
            anchor_format: TRAJECTORY_REPLAY_AUTHORITY_ANCHOR_FORMAT_V0,
            anchor_version: TRAJECTORY_REPLAY_AUTHORITY_ANCHOR_VERSION_V0,
            replay_format: super::replay::TRAJECTORY_REPLAY_FORMAT_V0,
            replay_version: super::replay::TRAJECTORY_REPLAY_VERSION_V0,
            schema: parse_binding(self.schema).map_err(map_replay_error)?,
            adapter: parse_binding(self.adapter).map_err(map_replay_error)?,
            policy: parse_binding(self.policy).map_err(map_replay_error)?,
            raw_capture,
            trajectory_digest: super::replay::ReplayDigestV0::parse(self.trajectory_digest)
                .map_err(map_replay_error)?,
            record_count: self.record_count,
            genesis_head: super::replay::ReplayDigestV0::parse(self.genesis_head)
                .map_err(map_replay_error)?,
            expected_final_head: super::replay::ReplayDigestV0::parse(self.expected_final_head)
                .map_err(map_replay_error)?,
        })
    }
}

impl ReplayAuthorityTrustPolicyWireV0 {
    fn try_into_policy(self) -> AuthorityResultV0<ReplayAuthorityTrustPolicyV0> {
        if self.trust_policy_format != TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_FORMAT_V0
            || self.trust_policy_version != TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_VERSION_V0
            || self.algorithm != REPLAY_AUTHORITY_ALGORITHM_ED25519_V0
        {
            return Err(ReplayAuthorityErrorV0::new(
                ReplayAuthorityErrorCodeV0::UnsupportedFormat,
            ));
        }
        validate_authority_name(&self.issuer)?;
        validate_authority_name(&self.key_id)?;
        if self.accepted_authority_epoch == 0 {
            return Err(ReplayAuthorityErrorV0::new(
                ReplayAuthorityErrorCodeV0::JsonShape,
            ));
        }
        let key_bytes = decode_prefixed_hex::<32>(&self.verification_key)?;
        let verification_key = VerifyingKey::from_bytes(&key_bytes)
            .map_err(|_| ReplayAuthorityErrorV0::new(ReplayAuthorityErrorCodeV0::JsonShape))?;
        Ok(ReplayAuthorityTrustPolicyV0 {
            issuer: self.issuer,
            algorithm: self.algorithm,
            key_id: self.key_id,
            accepted_authority_epoch: self.accepted_authority_epoch,
            verification_key,
        })
    }
}

fn signature_message(
    issuer: &str,
    algorithm: &str,
    key_id: &str,
    authority_epoch: u64,
    anchor: &ReplayAuthorityAnchorV0,
) -> Vec<u8> {
    let mut output = SIGNATURE_DOMAIN_V0.to_vec();
    put_string(&mut output, TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_FORMAT_V0);
    put_string(&mut output, TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_VERSION_V0);
    put_string(&mut output, issuer);
    put_string(&mut output, algorithm);
    put_string(&mut output, key_id);
    output.extend_from_slice(&authority_epoch.to_be_bytes());
    for value in [
        anchor.anchor_format,
        anchor.anchor_version,
        anchor.replay_format,
        anchor.replay_version,
        &anchor.schema.identity,
        &anchor.schema.version,
        anchor.schema.hash.as_str(),
        &anchor.adapter.identity,
        &anchor.adapter.version,
        anchor.adapter.hash.as_str(),
        &anchor.policy.identity,
        &anchor.policy.version,
        anchor.policy.hash.as_str(),
    ] {
        put_string(&mut output, value);
    }
    output.extend_from_slice(&anchor.raw_capture.record_count.to_be_bytes());
    put_string(&mut output, anchor.raw_capture.digest.as_str());
    put_string(&mut output, anchor.trajectory_digest.as_str());
    output.extend_from_slice(&anchor.record_count.to_be_bytes());
    put_string(&mut output, anchor.genesis_head.as_str());
    put_string(&mut output, anchor.expected_final_head.as_str());
    output
}

fn put_string(output: &mut Vec<u8>, value: &str) {
    output.extend_from_slice(&(value.len() as u64).to_be_bytes());
    output.extend_from_slice(value.as_bytes());
}

fn validate_authority_name(value: &str) -> AuthorityResultV0<()> {
    if value.is_empty()
        || value.len() > 128
        || !value.bytes().enumerate().all(|(index, byte)| match byte {
            b'a'..=b'z' | b'0'..=b'9' => true,
            b'.' | b'-' | b'_' => index > 0,
            _ => false,
        })
    {
        return Err(ReplayAuthorityErrorV0::new(
            ReplayAuthorityErrorCodeV0::JsonShape,
        ));
    }
    Ok(())
}

fn encode_prefixed_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(ED25519_KEY_PREFIX.len() + (bytes.len() * 2));
    output.push_str(ED25519_KEY_PREFIX);
    for byte in bytes {
        output.push(HEX[(byte >> 4) as usize] as char);
        output.push(HEX[(byte & 0x0f) as usize] as char);
    }
    output
}

fn decode_prefixed_hex<const N: usize>(value: &str) -> AuthorityResultV0<[u8; N]> {
    let hex = value
        .strip_prefix(ED25519_KEY_PREFIX)
        .ok_or_else(|| ReplayAuthorityErrorV0::new(ReplayAuthorityErrorCodeV0::JsonShape))?;
    if hex.len() != N * 2 {
        return Err(ReplayAuthorityErrorV0::new(
            ReplayAuthorityErrorCodeV0::JsonShape,
        ));
    }
    let mut output = [0u8; N];
    for (index, pair) in hex.as_bytes().chunks_exact(2).enumerate() {
        output[index] = (hex_nibble(pair[0])? << 4) | hex_nibble(pair[1])?;
    }
    Ok(output)
}

fn hex_nibble(byte: u8) -> AuthorityResultV0<u8> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        _ => Err(ReplayAuthorityErrorV0::new(
            ReplayAuthorityErrorCodeV0::JsonShape,
        )),
    }
}

fn map_replay_error(error: super::replay::ReplayErrorV0) -> ReplayAuthorityErrorV0 {
    let code = match error.code() {
        ReplayErrorCodeV0::InputTooLarge => ReplayAuthorityErrorCodeV0::InputTooLarge,
        ReplayErrorCodeV0::JsonFraming => ReplayAuthorityErrorCodeV0::JsonFraming,
        ReplayErrorCodeV0::JsonSyntax => ReplayAuthorityErrorCodeV0::JsonSyntax,
        ReplayErrorCodeV0::JsonShape
        | ReplayErrorCodeV0::CandidateMismatch
        | ReplayErrorCodeV0::AuthorityBindingMismatch => ReplayAuthorityErrorCodeV0::JsonShape,
        ReplayErrorCodeV0::UnsupportedFormat => ReplayAuthorityErrorCodeV0::UnsupportedFormat,
        ReplayErrorCodeV0::Serialization => ReplayAuthorityErrorCodeV0::Serialization,
    };
    ReplayAuthorityErrorV0::new(code)
}
