use super::*;
use crate::trajectory::duplicate_json::{self, JsonRootKind, JsonScanLimits};
use serde::Deserialize;

const RECEIPT_SCAN_LIMITS: JsonScanLimits = JsonScanLimits {
    max_depth: 16,
    max_nodes: 32_768,
    max_total_keys: 16_384,
    max_decoded_string_bytes: 1024 * 1024,
};

pub(super) fn decode_authority(input: &[u8]) -> AdapterResultV0<InputAuthorityReceiptV0> {
    preflight(input, super::super::MAX_AUTHORITY_RECEIPT_BYTES_V0)?;
    let wire: AuthorityWireV0 = serde_json::from_slice(input)
        .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape))?;
    let receipt = match wire {
        AuthorityWireV0::SyntheticFixture(value) => {
            InputAuthorityReceiptV0::SyntheticFixture(value.into())
        }
        AuthorityWireV0::ProcessCapture(value) => {
            InputAuthorityReceiptV0::ProcessCapture(Box::new((*value).into()))
        }
        AuthorityWireV0::SanitizedDerivedCapture(value) => {
            InputAuthorityReceiptV0::SanitizedDerivedCapture(value.into())
        }
    };
    receipt.validate()?;
    Ok(receipt)
}

pub(super) fn decode_trusted_context(input: &[u8]) -> AdapterResultV0<TrustedAdaptationContextV0> {
    preflight(input, super::super::MAX_TRUSTED_CONTEXT_BYTES_V0)?;
    let wire: TrustedContextWireV0 = serde_json::from_slice(input)
        .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape))?;
    if wire.context_format != "legitimacy.codex-exec-v0.trusted-adaptation-context"
        || wire.context_version != "0"
    {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape));
    }
    TrustedAdaptationContextV0::new(
        wire.expected_authority_commitment,
        wire.downstream_governance_policy,
    )
}

fn preflight(input: &[u8], cap: usize) -> AdapterResultV0<()> {
    if input.len() > cap {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge));
    }
    match duplicate_json::scan_json_with_limits(input, "adapter receipt", RECEIPT_SCAN_LIMITS) {
        Ok(JsonRootKind::Object) => Ok(()),
        Ok(JsonRootKind::NonObject) => Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape)),
        Err(error) => Err(AdapterErrorV0::new(if error.is_budget() {
            AdapterErrorCodeV0::JsonBudget
        } else {
            AdapterErrorCodeV0::JsonSyntax
        })),
    }
}

#[derive(Deserialize)]
#[serde(tag = "authority", rename_all = "kebab-case")]
enum AuthorityWireV0 {
    SyntheticFixture(SyntheticWireV0),
    ProcessCapture(Box<ProcessWireV0>),
    SanitizedDerivedCapture(DerivedWireV0),
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct EmitterWireV0 {
    package_version: String,
    source_tag: String,
    source_tag_object_sha: String,
    source_commit_sha: String,
}

impl From<EmitterWireV0> for EmitterIdentityV0 {
    fn from(value: EmitterWireV0) -> Self {
        Self {
            package_version: value.package_version,
            source_tag: value.source_tag,
            source_tag_object_sha: value.source_tag_object_sha,
            source_commit_sha: value.source_commit_sha,
        }
    }
}

#[derive(Deserialize)]
#[serde(rename_all = "kebab-case")]
enum NonceWireV0 {
    CaptureRandom,
    FixedSyntheticTest,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SyntheticWireV0 {
    receipt_format: String,
    receipt_version: String,
    evidence_class: String,
    emitter: EmitterWireV0,
    full_jsonl_length: u64,
    full_jsonl_digest: String,
    raw_record_count: u64,
    raw_capture_seal: RawCaptureSealV0,
    fixture_spec_manifest: ArtifactBindingV0,
    asserted_nonce_source: NonceWireV0,
    blinding_nonce_lower_hex: String,
}

impl From<SyntheticWireV0> for SyntheticFixtureReceiptV0 {
    fn from(value: SyntheticWireV0) -> Self {
        Self {
            receipt_format: value.receipt_format,
            receipt_version: value.receipt_version,
            evidence_class: value.evidence_class,
            emitter: value.emitter.into(),
            full_jsonl_length: value.full_jsonl_length,
            full_jsonl_digest: value.full_jsonl_digest,
            raw_record_count: value.raw_record_count,
            raw_capture_seal: value.raw_capture_seal,
            fixture_spec_manifest: value.fixture_spec_manifest,
            asserted_nonce_source: match value.asserted_nonce_source {
                NonceWireV0::CaptureRandom => AssertedNonceSourceV0::CaptureRandom,
                NonceWireV0::FixedSyntheticTest => AssertedNonceSourceV0::FixedSyntheticTest,
            },
            blinding_nonce_lower_hex: value.blinding_nonce_lower_hex,
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct InodeWireV0 {
    dev: u64,
    ino: u64,
}

impl From<InodeWireV0> for InodeIdentityV0 {
    fn from(value: InodeWireV0) -> Self {
        Self {
            dev: value.dev,
            ino: value.ino,
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ArgvWireV0 {
    argument_count: u64,
    arguments_lower_hex: Vec<String>,
    total_bytes: u64,
}

impl From<ArgvWireV0> for ArgvBytesV0 {
    fn from(value: ArgvWireV0) -> Self {
        Self {
            argument_count: value.argument_count,
            arguments_lower_hex: value.arguments_lower_hex,
            total_bytes: value.total_bytes,
        }
    }
}

#[derive(Deserialize)]
#[serde(rename_all = "kebab-case")]
enum ModeWireV0 {
    FreshExecStructuredStdin,
}

#[derive(Deserialize)]
#[serde(rename_all = "kebab-case")]
enum ProfileWireV0 {
    UnixReadOnlyStdinJsonV0,
}

#[derive(Deserialize)]
#[serde(tag = "presence", rename_all = "kebab-case", deny_unknown_fields)]
enum InputSealWireV0 {
    Absent,
    Present { byte_length: u64, sha256: String },
}

impl From<InputSealWireV0> for ByteInputSealV0 {
    fn from(value: InputSealWireV0) -> Self {
        match value {
            InputSealWireV0::Absent => Self::Absent,
            InputSealWireV0::Present {
                byte_length,
                sha256,
            } => Self::Present {
                byte_length,
                sha256,
            },
        }
    }
}

#[derive(Deserialize)]
#[serde(tag = "termination", rename_all = "kebab-case", deny_unknown_fields)]
enum TerminationWireV0 {
    Exited { code: u8 },
    Signaled { signal: u8, core_dumped: bool },
}

impl From<TerminationWireV0> for ProcessTerminationV0 {
    fn from(value: TerminationWireV0) -> Self {
        match value {
            TerminationWireV0::Exited { code } => Self::Exited { code },
            TerminationWireV0::Signaled {
                signal,
                core_dumped,
            } => Self::Signaled {
                signal,
                core_dumped,
            },
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct StreamWireV0 {
    byte_length: u64,
    sha256: String,
}

impl From<StreamWireV0> for ByteStreamSealV0 {
    fn from(value: StreamWireV0) -> Self {
        Self {
            byte_length: value.byte_length,
            sha256: value.sha256,
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ExecutedArtifactWireV0 {
    identity: ArtifactBindingV0,
    file_sha256: String,
    inode: InodeWireV0,
}

impl From<ExecutedArtifactWireV0> for ExecutedArtifactV0 {
    fn from(value: ExecutedArtifactWireV0) -> Self {
        Self {
            identity: value.identity,
            file_sha256: value.file_sha256,
            inode: value.inode.into(),
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ManifestWireV0 {
    ordinal: u64,
    role: String,
    format: String,
    relative_path_lower_hex: String,
    byte_length: u64,
    sha256: String,
    inode: InodeWireV0,
}

impl From<ManifestWireV0> for CaptureManifestEntryV0 {
    fn from(value: ManifestWireV0) -> Self {
        Self {
            ordinal: value.ordinal,
            role: value.role,
            format: value.format,
            relative_path_lower_hex: value.relative_path_lower_hex,
            byte_length: value.byte_length,
            sha256: value.sha256,
            inode: value.inode.into(),
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ReleaseWireV0 {
    name: String,
    sha256: String,
}

impl From<ReleaseWireV0> for ReleaseArtifactV0 {
    fn from(value: ReleaseWireV0) -> Self {
        Self {
            name: value.name,
            sha256: value.sha256,
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProcessWireV0 {
    receipt_format: String,
    receipt_version: String,
    evidence_class: String,
    emitter: EmitterWireV0,
    executable_sha256: String,
    executable_inode: InodeWireV0,
    executable_execution_binding: String,
    artifact_open_discipline: String,
    workspace_execution_discipline: String,
    argv: ArgvWireV0,
    resolved_mode: ModeWireV0,
    capture_profile: ProfileWireV0,
    stdin: InputSealWireV0,
    termination: TerminationWireV0,
    stdout: StreamWireV0,
    stderr: StreamWireV0,
    raw_record_count: u64,
    raw_capture_seal: RawCaptureSealV0,
    capture_tool: ExecutedArtifactWireV0,
    capture_profile_artifact: ArtifactBindingV0,
    workspace_manifest: Vec<ManifestWireV0>,
    workspace_tree_digest: String,
    release_asset: ReleaseWireV0,
    sigstore_bundle: ReleaseWireV0,
    sigstore_verification: String,
    asserted_nonce_source: NonceWireV0,
    blinding_nonce_lower_hex: String,
}

impl From<ProcessWireV0> for ProcessCaptureReceiptV0 {
    fn from(value: ProcessWireV0) -> Self {
        Self {
            receipt_format: value.receipt_format,
            receipt_version: value.receipt_version,
            evidence_class: value.evidence_class,
            emitter: value.emitter.into(),
            executable_sha256: value.executable_sha256,
            executable_inode: value.executable_inode.into(),
            executable_execution_binding: value.executable_execution_binding,
            artifact_open_discipline: value.artifact_open_discipline,
            workspace_execution_discipline: value.workspace_execution_discipline,
            argv: value.argv.into(),
            resolved_mode: match value.resolved_mode {
                ModeWireV0::FreshExecStructuredStdin => FreshExecModeV0::FreshExecStructuredStdin,
            },
            capture_profile: match value.capture_profile {
                ProfileWireV0::UnixReadOnlyStdinJsonV0 => CaptureProfileV0::UnixReadOnlyStdinJsonV0,
            },
            stdin: value.stdin.into(),
            termination: value.termination.into(),
            stdout: value.stdout.into(),
            stderr: value.stderr.into(),
            raw_record_count: value.raw_record_count,
            raw_capture_seal: value.raw_capture_seal,
            capture_tool: value.capture_tool.into(),
            capture_profile_artifact: value.capture_profile_artifact,
            workspace_manifest: value
                .workspace_manifest
                .into_iter()
                .map(Into::into)
                .collect(),
            workspace_tree_digest: value.workspace_tree_digest,
            release_asset: value.release_asset.into(),
            sigstore_bundle: value.sigstore_bundle.into(),
            sigstore_verification: value.sigstore_verification,
            asserted_nonce_source: match value.asserted_nonce_source {
                NonceWireV0::CaptureRandom => AssertedNonceSourceV0::CaptureRandom,
                NonceWireV0::FixedSyntheticTest => AssertedNonceSourceV0::FixedSyntheticTest,
            },
            blinding_nonce_lower_hex: value.blinding_nonce_lower_hex,
        }
    }
}

#[derive(Deserialize)]
enum AssertedParentReceiptWireV0 {
    #[serde(rename = "asserted-parent-receipt-synthetic-fixture-capture-random")]
    SyntheticFixtureCaptureRandom,
    #[serde(rename = "asserted-parent-receipt-synthetic-fixture-fixed-synthetic-test")]
    SyntheticFixtureFixedSyntheticTest,
    #[serde(rename = "asserted-parent-receipt-process-capture-capture-random")]
    ProcessCaptureCaptureRandom,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DerivedWireV0 {
    receipt_format: String,
    receipt_version: String,
    evidence_class: String,
    asserted_origin_evidence_class: String,
    asserted_parent_receipt: AssertedParentReceiptWireV0,
    parent_receipt_commitment: String,
    parent_full_jsonl_length: u64,
    parent_full_jsonl_digest: String,
    parent_raw_capture_seal: RawCaptureSealV0,
    sanitizer_policy: ArtifactBindingV0,
    sanitizer_artifact: ArtifactBindingV0,
    derived_full_jsonl_length: u64,
    derived_full_jsonl_digest: String,
    derived_raw_capture_seal: RawCaptureSealV0,
    asserted_nonce_source: NonceWireV0,
    blinding_nonce_lower_hex: String,
}

impl From<DerivedWireV0> for SanitizedDerivedCaptureReceiptV0 {
    fn from(value: DerivedWireV0) -> Self {
        Self {
            receipt_format: value.receipt_format,
            receipt_version: value.receipt_version,
            evidence_class: value.evidence_class,
            asserted_origin_evidence_class: value.asserted_origin_evidence_class,
            asserted_parent_receipt: match value.asserted_parent_receipt {
                AssertedParentReceiptWireV0::SyntheticFixtureCaptureRandom => {
                    AssertedParentReceiptV0::AssertedParentReceiptSyntheticFixtureCaptureRandom
                }
                AssertedParentReceiptWireV0::SyntheticFixtureFixedSyntheticTest => {
                    AssertedParentReceiptV0::AssertedParentReceiptSyntheticFixtureFixedSyntheticTest
                }
                AssertedParentReceiptWireV0::ProcessCaptureCaptureRandom => {
                    AssertedParentReceiptV0::AssertedParentReceiptProcessCaptureCaptureRandom
                }
            },
            parent_receipt_commitment: value.parent_receipt_commitment,
            parent_full_jsonl_length: value.parent_full_jsonl_length,
            parent_full_jsonl_digest: value.parent_full_jsonl_digest,
            parent_raw_capture_seal: value.parent_raw_capture_seal,
            sanitizer_policy: value.sanitizer_policy,
            sanitizer_artifact: value.sanitizer_artifact,
            derived_full_jsonl_length: value.derived_full_jsonl_length,
            derived_full_jsonl_digest: value.derived_full_jsonl_digest,
            derived_raw_capture_seal: value.derived_raw_capture_seal,
            asserted_nonce_source: match value.asserted_nonce_source {
                NonceWireV0::CaptureRandom => AssertedNonceSourceV0::CaptureRandom,
                NonceWireV0::FixedSyntheticTest => AssertedNonceSourceV0::FixedSyntheticTest,
            },
            blinding_nonce_lower_hex: value.blinding_nonce_lower_hex,
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TrustedContextWireV0 {
    context_format: String,
    context_version: String,
    expected_authority_commitment: String,
    downstream_governance_policy: ArtifactBindingV0,
}
