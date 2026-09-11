#[path = "receipt_canonical.rs"]
mod canonical;
#[path = "receipt_context.rs"]
mod context;
#[path = "receipt_debug.rs"]
mod debug;
#[path = "receipt_hex.rs"]
pub(super) mod hex;
#[path = "receipt_nonce.rs"]
pub(super) mod nonce;
#[path = "receipt_validate.rs"]
mod validate;
#[path = "receipt_wire.rs"]
mod wire;
#[path = "receipt_workspace.rs"]
pub(super) mod workspace;

use super::error::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0};
use super::framing::FramedCaptureV0;
use super::{
    CODEX_CLI_VERSION_V0, CODEX_SOURCE_COMMIT_SHA_V0, CODEX_SOURCE_TAG_OBJECT_SHA_V0,
    CODEX_SOURCE_TAG_V0, MAX_ARGV_ARGUMENT_BYTES_V0, MAX_ARGV_ARGUMENTS_V0,
    MAX_ARGV_TOTAL_BYTES_V0, MAX_CAPTURE_MANIFEST_ENTRIES_V0,
};
use crate::trajectory::{ArtifactBindingV0, RawCaptureSealV0, framed_sha256, raw_capture_seal_v0};
use hex::{decode_lower_hex, lower_hex, standard_sha256};
pub use nonce::AssertedNonceSourceV0;
pub use nonce::FixedSyntheticTestNonceV0;
use nonce::NonceMaterialV0;
use serde::Serialize;
use validate::validate_sha256;

const RECEIPT_COMMITMENT_DOMAIN_V0: &str = "legitimacy.codex-exec-v0.authority-commitment.v0";
const RECEIPT_MAGIC_V0: &[u8] = b"legitimacy.codex-exec-v0.authority.canonical.v0\0";

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum FreshExecModeV0 {
    FreshExecStructuredStdin,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum CaptureProfileV0 {
    UnixReadOnlyStdinJsonV0,
}

#[derive(Eq, PartialEq, Serialize)]
pub struct InodeIdentityV0 {
    dev: u64,
    ino: u64,
}

impl InodeIdentityV0 {
    pub const fn new(dev: u64, ino: u64) -> Self {
        Self { dev, ino }
    }
}

#[derive(Eq, PartialEq, Serialize)]
pub struct ArgvBytesV0 {
    argument_count: u64,
    arguments_lower_hex: Vec<String>,
    total_bytes: u64,
}

impl ArgvBytesV0 {
    pub fn from_arguments(arguments: &[&[u8]]) -> AdapterResultV0<Self> {
        if arguments.len() > MAX_ARGV_ARGUMENTS_V0 {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape));
        }
        let mut total = 0usize;
        let mut encoded = Vec::with_capacity(arguments.len());
        for argument in arguments {
            if argument.contains(&0) || argument.len() > MAX_ARGV_ARGUMENT_BYTES_V0 {
                return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape));
            }
            total = total
                .checked_add(argument.len())
                .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape))?;
            if total > MAX_ARGV_TOTAL_BYTES_V0 {
                return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape));
            }
            encoded.push(lower_hex(argument));
        }
        Ok(Self {
            argument_count: arguments.len() as u64,
            arguments_lower_hex: encoded,
            total_bytes: total as u64,
        })
    }

    fn decoded(&self) -> AdapterResultV0<Vec<Vec<u8>>> {
        let arguments = self
            .arguments_lower_hex
            .iter()
            .map(|value| decode_lower_hex(value))
            .collect::<AdapterResultV0<Vec<_>>>()?;
        let refs = arguments.iter().map(Vec::as_slice).collect::<Vec<_>>();
        let rebuilt = Self::from_arguments(&refs)?;
        if rebuilt != *self {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape));
        }
        Ok(arguments)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(tag = "termination", rename_all = "kebab-case")]
pub enum ProcessTerminationV0 {
    Exited { code: u8 },
    Signaled { signal: u8, core_dumped: bool },
}

#[derive(Eq, PartialEq, Serialize)]
pub struct CaptureManifestEntryV0 {
    ordinal: u64,
    role: String,
    format: String,
    relative_path_lower_hex: String,
    byte_length: u64,
    sha256: String,
    inode: InodeIdentityV0,
}

#[derive(Eq, PartialEq, Serialize)]
pub struct SyntheticFixtureReceiptV0 {
    receipt_format: String,
    receipt_version: String,
    evidence_class: String,
    emitter: EmitterIdentityV0,
    full_jsonl_length: u64,
    full_jsonl_digest: String,
    raw_record_count: u64,
    raw_capture_seal: RawCaptureSealV0,
    fixture_spec_manifest: ArtifactBindingV0,
    asserted_nonce_source: AssertedNonceSourceV0,
    blinding_nonce_lower_hex: String,
}

impl SyntheticFixtureReceiptV0 {
    pub fn new(jsonl: &[u8], fixture_spec_manifest: ArtifactBindingV0) -> AdapterResultV0<Self> {
        Self::with_nonce(
            jsonl,
            fixture_spec_manifest,
            NonceMaterialV0::capture_random()?,
        )
    }

    pub fn new_with_fixed_test_nonce(
        jsonl: &[u8],
        fixture_spec_manifest: ArtifactBindingV0,
        nonce: FixedSyntheticTestNonceV0,
    ) -> AdapterResultV0<Self> {
        Self::with_nonce(jsonl, fixture_spec_manifest, nonce.into_material())
    }

    fn with_nonce(
        jsonl: &[u8],
        fixture_spec_manifest: ArtifactBindingV0,
        nonce: NonceMaterialV0,
    ) -> AdapterResultV0<Self> {
        let framed = FramedCaptureV0::parse(jsonl)?;
        let records = framed.record_slices();
        Ok(Self {
            receipt_format: "legitimacy.codex-exec-v0.synthetic-fixture-receipt".to_string(),
            receipt_version: "0".to_string(),
            evidence_class: "synthetic-fixture".to_string(),
            emitter: EmitterIdentityV0::pinned(),
            full_jsonl_length: jsonl.len() as u64,
            full_jsonl_digest: framed.full_digest(),
            raw_record_count: records.len() as u64,
            raw_capture_seal: raw_capture_seal_v0(&records),
            fixture_spec_manifest,
            asserted_nonce_source: nonce.asserted_source(),
            blinding_nonce_lower_hex: lower_hex(nonce.bytes()),
        })
    }
}

#[derive(Eq, PartialEq, Serialize)]
pub struct ProcessCaptureReceiptV0 {
    receipt_format: String,
    receipt_version: String,
    evidence_class: String,
    emitter: EmitterIdentityV0,
    executable_sha256: String,
    executable_inode: InodeIdentityV0,
    executable_execution_binding: String,
    artifact_open_discipline: String,
    workspace_execution_discipline: String,
    argv: ArgvBytesV0,
    resolved_mode: FreshExecModeV0,
    capture_profile: CaptureProfileV0,
    stdin: ByteInputSealV0,
    termination: ProcessTerminationV0,
    stdout: ByteStreamSealV0,
    stderr: ByteStreamSealV0,
    raw_record_count: u64,
    raw_capture_seal: RawCaptureSealV0,
    capture_tool: ExecutedArtifactV0,
    capture_profile_artifact: ArtifactBindingV0,
    workspace_manifest: Vec<CaptureManifestEntryV0>,
    workspace_tree_digest: String,
    release_asset: ReleaseArtifactV0,
    sigstore_bundle: ReleaseArtifactV0,
    sigstore_verification: String,
    asserted_nonce_source: AssertedNonceSourceV0,
    blinding_nonce_lower_hex: String,
}

pub(super) struct ObservedProcessCaptureV0 {
    pub executable_sha256: String,
    pub executable_inode: InodeIdentityV0,
    pub stdin: Vec<u8>,
    pub termination: ProcessTerminationV0,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub capture_tool_file_sha256: String,
    pub capture_tool_inode: InodeIdentityV0,
}

impl ProcessCaptureReceiptV0 {
    pub(super) fn from_observed_process(
        observed: ObservedProcessCaptureV0,
    ) -> AdapterResultV0<InputAuthorityReceiptV0> {
        let framed = FramedCaptureV0::parse(&observed.stdout)?;
        let records = framed.record_slices();
        let nonce = NonceMaterialV0::capture_random()?;
        let workspace_manifest = Vec::new();
        let receipt = Self {
            receipt_format: "legitimacy.codex-exec-v0.process-capture-receipt".to_string(),
            receipt_version: "0".to_string(),
            evidence_class: "genuine-process-capture".to_string(),
            emitter: EmitterIdentityV0::pinned(),
            executable_sha256: observed.executable_sha256,
            executable_inode: observed.executable_inode,
            executable_execution_binding: "fexecve-held-fd".to_string(),
            artifact_open_discipline: "held-fd-no-symlink".to_string(),
            workspace_execution_discipline: "held-read-only-during-exec".to_string(),
            argv: ArgvBytesV0::from_arguments(super::PROCESS_CAPTURE_ARGV_V0)?,
            resolved_mode: FreshExecModeV0::FreshExecStructuredStdin,
            capture_profile: CaptureProfileV0::UnixReadOnlyStdinJsonV0,
            stdin: ByteInputSealV0::Present {
                byte_length: observed.stdin.len() as u64,
                sha256: standard_sha256(&observed.stdin),
            },
            termination: observed.termination,
            stdout: ByteStreamSealV0 {
                byte_length: observed.stdout.len() as u64,
                sha256: standard_sha256(&observed.stdout),
            },
            stderr: ByteStreamSealV0 {
                byte_length: observed.stderr.len() as u64,
                sha256: standard_sha256(&observed.stderr),
            },
            raw_record_count: records.len() as u64,
            raw_capture_seal: raw_capture_seal_v0(&records),
            capture_tool: ExecutedArtifactV0 {
                identity: super::codex_exec_capture_producer_binding_v0(),
                file_sha256: observed.capture_tool_file_sha256,
                inode: observed.capture_tool_inode,
            },
            capture_profile_artifact: super::codex_exec_capture_profile_binding_v0(),
            workspace_tree_digest: workspace::workspace_tree_digest(&workspace_manifest)?,
            workspace_manifest,
            release_asset: ReleaseArtifactV0 {
                name: super::PROCESS_CAPTURE_RELEASE_NAME_V0.to_string(),
                sha256: super::PROCESS_CAPTURE_RELEASE_SHA256_V0.to_string(),
            },
            sigstore_bundle: ReleaseArtifactV0 {
                name: super::PROCESS_CAPTURE_SIGSTORE_NAME_V0.to_string(),
                sha256: super::PROCESS_CAPTURE_SIGSTORE_SHA256_V0.to_string(),
            },
            sigstore_verification: "bundle-present-unverified".to_string(),
            asserted_nonce_source: nonce.asserted_source(),
            blinding_nonce_lower_hex: lower_hex(nonce.bytes()),
        };
        receipt.validate()?;
        let authority = InputAuthorityReceiptV0::ProcessCapture(Box::new(receipt));
        let _ = authority.commitment();
        Ok(authority)
    }
}

#[derive(Clone, Copy, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum AssertedParentReceiptV0 {
    AssertedParentReceiptSyntheticFixtureCaptureRandom,
    AssertedParentReceiptSyntheticFixtureFixedSyntheticTest,
    AssertedParentReceiptProcessCaptureCaptureRandom,
}

impl AssertedParentReceiptV0 {
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::AssertedParentReceiptSyntheticFixtureCaptureRandom => {
                "asserted-parent-receipt-synthetic-fixture-capture-random"
            }
            Self::AssertedParentReceiptSyntheticFixtureFixedSyntheticTest => {
                "asserted-parent-receipt-synthetic-fixture-fixed-synthetic-test"
            }
            Self::AssertedParentReceiptProcessCaptureCaptureRandom => {
                "asserted-parent-receipt-process-capture-capture-random"
            }
        }
    }
}

#[derive(Eq, PartialEq, Serialize)]
pub struct SanitizedDerivedCaptureReceiptV0 {
    receipt_format: String,
    receipt_version: String,
    evidence_class: String,
    asserted_origin_evidence_class: String,
    asserted_parent_receipt: AssertedParentReceiptV0,
    parent_receipt_commitment: String,
    parent_full_jsonl_length: u64,
    parent_full_jsonl_digest: String,
    parent_raw_capture_seal: RawCaptureSealV0,
    sanitizer_policy: ArtifactBindingV0,
    sanitizer_artifact: ArtifactBindingV0,
    derived_full_jsonl_length: u64,
    derived_full_jsonl_digest: String,
    derived_raw_capture_seal: RawCaptureSealV0,
    asserted_nonce_source: AssertedNonceSourceV0,
    blinding_nonce_lower_hex: String,
}

impl SanitizedDerivedCaptureReceiptV0 {
    pub(crate) fn new(
        inputs: DerivedReceiptInputsV0,
        derived: &FramedCaptureV0,
        nonce: NonceMaterialV0,
    ) -> Self {
        let records = derived.record_slices();
        Self {
            receipt_format: "legitimacy.codex-exec-v0.sanitized-derived-capture-receipt"
                .to_string(),
            receipt_version: "0".to_string(),
            evidence_class: "sanitized-derived-capture".to_string(),
            asserted_origin_evidence_class: inputs.asserted_origin_evidence_class,
            asserted_parent_receipt: inputs.asserted_parent_receipt,
            parent_receipt_commitment: inputs.parent_receipt_commitment,
            parent_full_jsonl_length: inputs.parent_full_jsonl_length,
            parent_full_jsonl_digest: inputs.parent_full_jsonl_digest,
            parent_raw_capture_seal: inputs.parent_raw_capture_seal,
            sanitizer_policy: inputs.sanitizer_policy,
            sanitizer_artifact: inputs.sanitizer_artifact,
            derived_full_jsonl_length: derived.bytes.len() as u64,
            derived_full_jsonl_digest: derived.full_digest(),
            derived_raw_capture_seal: raw_capture_seal_v0(&records),
            asserted_nonce_source: nonce.asserted_source(),
            blinding_nonce_lower_hex: lower_hex(nonce.bytes()),
        }
    }
}

pub(crate) struct DerivedReceiptInputsV0 {
    pub asserted_origin_evidence_class: String,
    pub asserted_parent_receipt: AssertedParentReceiptV0,
    pub parent_receipt_commitment: String,
    pub parent_full_jsonl_length: u64,
    pub parent_full_jsonl_digest: String,
    pub parent_raw_capture_seal: RawCaptureSealV0,
    pub sanitizer_policy: ArtifactBindingV0,
    pub sanitizer_artifact: ArtifactBindingV0,
}

#[derive(Eq, PartialEq, Serialize)]
#[serde(tag = "authority", rename_all = "kebab-case")]
pub enum InputAuthorityReceiptV0 {
    SyntheticFixture(SyntheticFixtureReceiptV0),
    ProcessCapture(Box<ProcessCaptureReceiptV0>),
    SanitizedDerivedCapture(SanitizedDerivedCaptureReceiptV0),
}

#[derive(Eq, PartialEq, Serialize)]
pub struct TrustedAdaptationContextV0 {
    context_format: String,
    context_version: String,
    expected_authority_commitment: String,
    downstream_governance_policy: ArtifactBindingV0,
}

#[derive(Clone, Eq, PartialEq, Serialize)]
pub struct PublicDerivedReceiptProjectionV0 {
    projection_format: String,
    projection_version: String,
    evidence_class: String,
    derived_full_jsonl_length: u64,
    derived_full_jsonl_digest: String,
    derived_raw_capture_seal: RawCaptureSealV0,
    sanitizer_policy: ArtifactBindingV0,
    sanitizer_artifact: ArtifactBindingV0,
}

impl InputAuthorityReceiptV0 {
    pub fn from_json_slice(input: &[u8]) -> AdapterResultV0<Self> {
        wire::decode_authority(input)
    }

    pub fn commitment(&self) -> String {
        framed_sha256(RECEIPT_COMMITMENT_DOMAIN_V0, &[&self.canonical_bytes()])
    }

    pub fn evidence_class(&self) -> &'static str {
        match self {
            Self::SyntheticFixture(_) => "synthetic-fixture",
            Self::ProcessCapture(_) => "genuine-process-capture",
            Self::SanitizedDerivedCapture(_) => "sanitized-derived-capture",
        }
    }

    pub(crate) fn authorize(
        &self,
        framed: &FramedCaptureV0,
        trusted: &TrustedAdaptationContextV0,
    ) -> AdapterResultV0<()> {
        self.validate()?;
        self.reject_dynamic_policy_substitution(&trusted.downstream_governance_policy)?;
        if self.commitment() != trusted.expected_authority_commitment {
            return Err(AdapterErrorV0::new(
                AdapterErrorCodeV0::TrustedContextMismatch,
            ));
        }
        let records = framed.record_slices();
        let seal = raw_capture_seal_v0(&records);
        let length = framed.bytes.len() as u64;
        let digest = framed.full_digest();
        let matches = match self {
            Self::SyntheticFixture(receipt) => {
                receipt.full_jsonl_length == length
                    && receipt.full_jsonl_digest == digest
                    && receipt.raw_record_count == records.len() as u64
                    && receipt.raw_capture_seal == seal
            }
            Self::ProcessCapture(receipt) => {
                receipt.stdout.byte_length == length
                    && receipt.stdout.sha256 == standard_sha256(&framed.bytes)
                    && receipt.raw_record_count == records.len() as u64
                    && receipt.raw_capture_seal == seal
            }
            Self::SanitizedDerivedCapture(receipt) => {
                receipt.derived_full_jsonl_length == length
                    && receipt.derived_full_jsonl_digest == digest
                    && receipt.derived_raw_capture_seal == seal
            }
        };
        if !matches {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptMismatch));
        }
        Ok(())
    }

    fn reject_dynamic_policy_substitution(
        &self,
        policy: &ArtifactBindingV0,
    ) -> AdapterResultV0<()> {
        context::validate_policy_identity(&policy.identity)?;
        let substitutes_assigned_role = match self {
            Self::SyntheticFixture(receipt) => {
                policy.identity == receipt.fixture_spec_manifest.identity
            }
            Self::ProcessCapture(receipt) => {
                policy.identity == receipt.capture_tool.identity.identity
                    || policy.identity == receipt.capture_profile_artifact.identity
            }
            Self::SanitizedDerivedCapture(receipt) => {
                policy.identity == receipt.sanitizer_policy.identity
                    || policy.identity == receipt.sanitizer_artifact.identity
            }
        };
        if substitutes_assigned_role {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReservedPolicy));
        }
        Ok(())
    }

    pub(crate) fn raw_seal(&self) -> &RawCaptureSealV0 {
        match self {
            Self::SyntheticFixture(value) => &value.raw_capture_seal,
            Self::ProcessCapture(value) => &value.raw_capture_seal,
            Self::SanitizedDerivedCapture(value) => &value.derived_raw_capture_seal,
        }
    }

    pub(crate) fn process_termination(&self) -> Option<&ProcessTerminationV0> {
        match self {
            Self::ProcessCapture(value) => Some(&value.termination),
            Self::SyntheticFixture(_) | Self::SanitizedDerivedCapture(_) => None,
        }
    }

    pub(crate) fn public_derived_projection(
        &self,
    ) -> AdapterResultV0<PublicDerivedReceiptProjectionV0> {
        let Self::SanitizedDerivedCapture(value) = self else {
            return Err(AdapterErrorV0::new(
                AdapterErrorCodeV0::UnsupportedAuthority,
            ));
        };
        Ok(PublicDerivedReceiptProjectionV0 {
            projection_format: "legitimacy.codex-exec-v0.public-child-projection".to_string(),
            projection_version: "0".to_string(),
            evidence_class: "sanitizer-conforming-child-projection".to_string(),
            derived_full_jsonl_length: value.derived_full_jsonl_length,
            derived_full_jsonl_digest: value.derived_full_jsonl_digest.clone(),
            derived_raw_capture_seal: value.derived_raw_capture_seal.clone(),
            sanitizer_policy: value.sanitizer_policy.clone(),
            sanitizer_artifact: value.sanitizer_artifact.clone(),
        })
    }

    pub(crate) fn sanitized_derived_receipt(
        &self,
    ) -> AdapterResultV0<&SanitizedDerivedCaptureReceiptV0> {
        match self {
            Self::SanitizedDerivedCapture(receipt) => Ok(receipt),
            Self::SyntheticFixture(_) | Self::ProcessCapture(_) => Err(AdapterErrorV0::new(
                AdapterErrorCodeV0::UnsupportedAuthority,
            )),
        }
    }

    pub(crate) fn parent_commitment(&self) -> Option<&str> {
        match self {
            Self::SanitizedDerivedCapture(value) => Some(&value.parent_receipt_commitment),
            Self::SyntheticFixture(_) | Self::ProcessCapture(_) => None,
        }
    }

    pub(crate) const fn asserted_nonce_source(&self) -> AssertedNonceSourceV0 {
        match self {
            Self::SyntheticFixture(value) => value.asserted_nonce_source,
            Self::ProcessCapture(value) => value.asserted_nonce_source,
            Self::SanitizedDerivedCapture(value) => value.asserted_nonce_source,
        }
    }

    pub(crate) fn asserted_parent_receipt(&self) -> AdapterResultV0<AssertedParentReceiptV0> {
        match (self, self.asserted_nonce_source()) {
            (Self::SyntheticFixture(_), AssertedNonceSourceV0::CaptureRandom) => {
                Ok(AssertedParentReceiptV0::AssertedParentReceiptSyntheticFixtureCaptureRandom)
            }
            (Self::SyntheticFixture(_), AssertedNonceSourceV0::FixedSyntheticTest) => Ok(
                AssertedParentReceiptV0::AssertedParentReceiptSyntheticFixtureFixedSyntheticTest,
            ),
            (Self::ProcessCapture(_), AssertedNonceSourceV0::CaptureRandom) => {
                Ok(AssertedParentReceiptV0::AssertedParentReceiptProcessCaptureCaptureRandom)
            }
            (Self::ProcessCapture(_), AssertedNonceSourceV0::FixedSyntheticTest)
            | (Self::SanitizedDerivedCapture(_), _) => Err(AdapterErrorV0::new(
                AdapterErrorCodeV0::UnsupportedAuthority,
            )),
        }
    }

    pub(super) fn publication_assertions(
        &self,
    ) -> AdapterResultV0<(&str, AssertedParentReceiptV0, AssertedNonceSourceV0)> {
        let Self::SanitizedDerivedCapture(value) = self else {
            return Err(AdapterErrorV0::new(
                AdapterErrorCodeV0::UnsupportedAuthority,
            ));
        };
        Ok((
            &value.asserted_origin_evidence_class,
            value.asserted_parent_receipt,
            value.asserted_nonce_source,
        ))
    }

    fn canonical_bytes(&self) -> Vec<u8> {
        let mut output = RECEIPT_MAGIC_V0.to_vec();
        match self {
            Self::SyntheticFixture(value) => value.encode(&mut output),
            Self::ProcessCapture(value) => value.encode(&mut output),
            Self::SanitizedDerivedCapture(value) => value.encode(&mut output),
        }
        output
    }

    fn validate(&self) -> AdapterResultV0<()> {
        match self {
            Self::SyntheticFixture(value) => value.validate(),
            Self::ProcessCapture(value) => value.validate(),
            Self::SanitizedDerivedCapture(value) => value.validate(),
        }
    }
}

#[derive(Eq, PartialEq, Serialize)]
struct EmitterIdentityV0 {
    package_version: String,
    source_tag: String,
    source_tag_object_sha: String,
    source_commit_sha: String,
}

impl EmitterIdentityV0 {
    fn pinned() -> Self {
        Self {
            package_version: CODEX_CLI_VERSION_V0.to_string(),
            source_tag: CODEX_SOURCE_TAG_V0.to_string(),
            source_tag_object_sha: CODEX_SOURCE_TAG_OBJECT_SHA_V0.to_string(),
            source_commit_sha: CODEX_SOURCE_COMMIT_SHA_V0.to_string(),
        }
    }

    fn validate(&self) -> AdapterResultV0<()> {
        if *self != Self::pinned() {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptMismatch));
        }
        Ok(())
    }
}

#[derive(Eq, PartialEq, Serialize)]
#[serde(tag = "presence", rename_all = "kebab-case")]
enum ByteInputSealV0 {
    Absent,
    Present { byte_length: u64, sha256: String },
}

#[derive(Eq, PartialEq, Serialize)]
struct ByteStreamSealV0 {
    byte_length: u64,
    sha256: String,
}

#[derive(Eq, PartialEq, Serialize)]
struct ExecutedArtifactV0 {
    identity: ArtifactBindingV0,
    file_sha256: String,
    inode: InodeIdentityV0,
}

#[derive(Eq, PartialEq, Serialize)]
struct ReleaseArtifactV0 {
    name: String,
    sha256: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sanitized_receipt_access_rejects_other_authority_variants_exactly() {
        let jsonl =
            b"{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}\n";
        let receipt = SyntheticFixtureReceiptV0::new_with_fixed_test_nonce(
            jsonl,
            super::super::codex_exec_fixture_spec_binding_v0(),
            FixedSyntheticTestNonceV0::new([0x62; 32]),
        )
        .unwrap();
        let authority = InputAuthorityReceiptV0::SyntheticFixture(receipt);
        let error = authority.sanitized_derived_receipt().unwrap_err();
        assert_eq!(error.code(), AdapterErrorCodeV0::UnsupportedAuthority);
        assert_eq!(error.record_index(), None);
        assert_eq!(error.structural_path(), None);
    }
}
