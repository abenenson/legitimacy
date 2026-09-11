#[path = "bundle_wire.rs"]
mod wire;
pub use wire::{
    InspectedPrivateAdapterBundleV0, InspectedShareableSanitizedBundleV0,
    RevalidatedPrivateAdapterBundleV0, RevalidatedShareableSanitizedBundleV0,
};

use super::error::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0};
use super::event::parse_record;
use super::framing::FramedCaptureV0;
use super::fsm;
use super::mapping;
use super::receipt::{
    InputAuthorityReceiptV0, PublicDerivedReceiptProjectionV0, TrustedAdaptationContextV0,
};
use super::{
    MAX_ADAPTER_BUNDLE_BYTES_V0, codex_exec_adapter_binding_v0, codex_exec_sanitizer_binding_v0,
    codex_exec_sanitizer_policy_binding_v0,
};
use crate::trajectory::{
    ArtifactBindingV0, RawCaptureSealV0, TrajectoryTraceV0, TrajectoryValidationContextV0,
    ValidatedTrajectoryTraceV0, artifact_digest_v0, framed_sha256, trajectory_digest_v0,
    trajectory_schema_binding_v0,
};
use serde::Serialize;
use std::fmt;
use std::io::{self, Write};

const COMPONENT_DOMAIN_PREFIX_V0: &str = "legitimacy.codex-exec-v0.payload-component";
const PRIVATE_POLICY_BYTES_V0: &[u8] =
    b"legitimacy.codex-exec-v0.private-identity-transformation.v0";

pub struct AdaptedCodexExecV0 {
    pub(super) capture: FramedCaptureV0,
    trace: TrajectoryTraceV0,
    validation_declarations: TrajectoryValidationContextV0,
    authority_commitment: String,
    evidence_class: String,
}

impl AdaptedCodexExecV0 {
    pub fn jsonl(&self) -> &[u8] {
        &self.capture.bytes
    }

    pub fn validate(&self) -> AdapterResultV0<ValidatedTrajectoryTraceV0<'_>> {
        let records = self.capture.record_slices();
        self.trace
            .validate(&records, &self.validation_declarations)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::Validation))
    }

    pub fn with_validated<T>(
        &self,
        operation: impl FnOnce(&ValidatedTrajectoryTraceV0<'_>) -> T,
    ) -> AdapterResultV0<T> {
        let validated = self.validate()?;
        Ok(operation(&validated))
    }

    pub fn trace(&self) -> &TrajectoryTraceV0 {
        &self.trace
    }

    pub fn to_private_bundle(&self) -> AdapterResultV0<PrivateAdapterBundleV0> {
        let components = self.components()?;
        let transformation_receipt = self.private_transformation_receipt(&components);
        Ok(PrivateAdapterBundleV0 {
            bundle_format: "legitimacy.codex-exec-v0.private-adapter-bundle".to_string(),
            bundle_version: "0".to_string(),
            evidence_class: self.evidence_class.clone(),
            authority_commitment: self.authority_commitment.clone(),
            schema: trajectory_schema_binding_v0(),
            adapter: codex_exec_adapter_binding_v0(),
            downstream_governance_policy: self.validation_declarations.policy.clone(),
            official_trace_json: components.official_trace_json,
            canonical_trace_lower_hex: lower_hex(&components.canonical_trace),
            trajectory_digest: components.trajectory_digest,
            payload_manifest: components.payload_manifest,
            transformation_receipt,
        })
    }

    pub(super) fn publication_fields(
        &self,
        public_derived_receipt: PublicDerivedReceiptProjectionV0,
    ) -> AdapterResultV0<PublicationBundleFieldsV0> {
        if self.evidence_class != "sanitized-derived-capture" {
            return Err(AdapterErrorV0::new(
                AdapterErrorCodeV0::PublicShareabilityDenied,
            ));
        }
        let components = self.components()?;
        let private_receipt = self.private_transformation_receipt(&components);
        let public_transformation = PublicTransformationProjectionV0 {
            projection_format: "legitimacy.codex-exec-v0.public-deterministic-projection"
                .to_string(),
            projection_version: "0".to_string(),
            adapter: private_receipt.adapter.clone(),
            schema: private_receipt.schema.clone(),
            downstream_governance_policy: private_receipt.downstream_governance_policy.clone(),
            sanitizer_policy: private_receipt.transformation_policy.clone(),
            normalized_trace_digest: private_receipt.normalized_trace_digest.clone(),
            derived_capture_seal: self.trace.raw_capture.clone(),
            payload_manifest: components.payload_manifest.clone(),
        };
        Ok(PublicationBundleFieldsV0 {
            bundle_format: "legitimacy.codex-exec-v0.shareable-sanitized-bundle".to_string(),
            bundle_version: "0".to_string(),
            evidence_class: "sanitizer-conforming-child-projection".to_string(),
            public_derived_receipt,
            schema: trajectory_schema_binding_v0(),
            adapter: codex_exec_adapter_binding_v0(),
            downstream_governance_policy: self.validation_declarations.policy.clone(),
            sanitizer: codex_exec_sanitizer_binding_v0(),
            official_trace_json: components.official_trace_json,
            canonical_trace_lower_hex: lower_hex(&components.canonical_trace),
            trajectory_digest: components.trajectory_digest,
            payload_manifest: components.payload_manifest,
            public_transformation,
        })
    }

    pub(super) fn downstream_policy(&self) -> &ArtifactBindingV0 {
        &self.validation_declarations.policy
    }

    pub(super) fn has_exact_authority(&self, authority: &InputAuthorityReceiptV0) -> bool {
        self.authority_commitment == authority.commitment()
            && self.evidence_class == authority.evidence_class()
    }

    fn components(&self) -> AdapterResultV0<OutputComponentsV0> {
        let validated = self.validate()?;
        let official_trace_json = validated
            .to_compact_json()
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::Validation))?;
        let canonical_trace = validated.canonical_bytes();
        let projected_bytes = official_trace_json
            .len()
            .checked_add(canonical_trace.len().saturating_mul(2))
            .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge))?;
        if projected_bytes > MAX_ADAPTER_BUNDLE_BYTES_V0 {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge));
        }
        let trajectory_digest = trajectory_digest_v0(&validated);
        let payload_manifest = vec![
            PayloadManifestEntryV0::new(
                ComponentRoleV0::OfficialTraceJson,
                ComponentFormatV0::TrajectoryV0CompactJson,
                0,
                &official_trace_json,
            ),
            PayloadManifestEntryV0::new(
                ComponentRoleV0::CanonicalTrace,
                ComponentFormatV0::TrajectoryV0CanonicalBytes,
                1,
                &canonical_trace,
            ),
        ];
        Ok(OutputComponentsV0 {
            official_trace_json: String::from_utf8(official_trace_json)
                .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::Validation))?,
            canonical_trace,
            trajectory_digest,
            payload_manifest,
        })
    }

    fn private_transformation_receipt(
        &self,
        components: &OutputComponentsV0,
    ) -> TransformationReceiptV0 {
        let transformation_policy = if self.evidence_class == "sanitized-derived-capture" {
            codex_exec_sanitizer_policy_binding_v0()
        } else {
            ArtifactBindingV0 {
                identity: "legitimacy.codex-exec-v0.private-identity-policy".to_string(),
                version: "0".to_string(),
                hash: artifact_digest_v0(PRIVATE_POLICY_BYTES_V0),
            }
        };
        TransformationReceiptV0 {
            receipt_format: "legitimacy.codex-exec-v0.transformation-receipt".to_string(),
            receipt_version: "0".to_string(),
            input_authority_commitment: self.authority_commitment.clone(),
            authorized_capture_seal: self.trace.raw_capture.clone(),
            adapter: codex_exec_adapter_binding_v0(),
            schema: trajectory_schema_binding_v0(),
            downstream_governance_policy: self.validation_declarations.policy.clone(),
            transformation_policy,
            normalized_trace_digest: components.trajectory_digest.clone(),
            sanitized_fixture_seal: (self.evidence_class == "sanitized-derived-capture")
                .then(|| self.trace.raw_capture.clone()),
            payload_manifest: components.payload_manifest.clone(),
        }
    }
}

pub(crate) fn adapt(
    jsonl: &[u8],
    authority: &InputAuthorityReceiptV0,
    trusted_context: &TrustedAdaptationContextV0,
) -> AdapterResultV0<AdaptedCodexExecV0> {
    adapt_owned(jsonl.to_vec(), authority, trusted_context)
}

pub(crate) fn adapt_owned(
    jsonl: Vec<u8>,
    authority: &InputAuthorityReceiptV0,
    trusted_context: &TrustedAdaptationContextV0,
) -> AdapterResultV0<AdaptedCodexExecV0> {
    let capture = FramedCaptureV0::parse_owned(jsonl)?;
    adapt_framed(capture, authority, trusted_context)
}

pub(crate) fn adapt_framed(
    capture: FramedCaptureV0,
    authority: &InputAuthorityReceiptV0,
    trusted_context: &TrustedAdaptationContextV0,
) -> AdapterResultV0<AdaptedCodexExecV0> {
    authority.authorize(&capture, trusted_context)?;
    let raw_records = capture.record_slices();
    let parsed_records = raw_records
        .iter()
        .enumerate()
        .map(|(index, record)| parse_record(record, index))
        .collect::<AdapterResultV0<Vec<_>>>()?;
    fsm::validate_stream(
        &parsed_records,
        &raw_records,
        authority.process_termination(),
    )?;
    let mapped = mapping::map_records(&parsed_records, &raw_records, authority, trusted_context)?;
    let adapted = AdaptedCodexExecV0 {
        capture,
        trace: mapped.trace,
        validation_declarations: mapped.validation_declarations,
        authority_commitment: authority.commitment(),
        evidence_class: authority.evidence_class().to_string(),
    };
    adapted.validate()?;
    Ok(adapted)
}

pub(super) fn adapt_public_sanitized_owned(
    jsonl: Vec<u8>,
    raw_capture: RawCaptureSealV0,
    downstream_policy: ArtifactBindingV0,
) -> AdapterResultV0<AdaptedCodexExecV0> {
    let capture = FramedCaptureV0::parse_owned(jsonl)?;
    let public_child_authority_commitment = framed_sha256(
        "legitimacy.codex-exec-v0.public-sanitized-child-authority.v0",
        &[
            capture.full_digest().as_bytes(),
            raw_capture.digest.as_bytes(),
            downstream_policy.identity.as_bytes(),
            downstream_policy.version.as_bytes(),
            downstream_policy.hash.as_bytes(),
            codex_exec_adapter_binding_v0().hash.as_bytes(),
            codex_exec_sanitizer_binding_v0().hash.as_bytes(),
        ],
    );
    let context = TrustedAdaptationContextV0::new(
        public_child_authority_commitment.clone(),
        downstream_policy,
    )?;
    let raw_records = capture.record_slices();
    let parsed_records = raw_records
        .iter()
        .enumerate()
        .map(|(index, record)| parse_record(record, index))
        .collect::<AdapterResultV0<Vec<_>>>()?;
    fsm::validate_stream(&parsed_records, &raw_records, None)?;
    let mapped = mapping::map_records_with_bindings(
        &parsed_records,
        &raw_records,
        &raw_capture,
        context.downstream_governance_policy(),
    )?;
    let adapted = AdaptedCodexExecV0 {
        capture,
        trace: mapped.trace,
        validation_declarations: mapped.validation_declarations,
        authority_commitment: public_child_authority_commitment,
        evidence_class: "sanitizer-conforming-child-projection".to_string(),
    };
    adapted.validate()?;
    Ok(adapted)
}

#[derive(Eq, PartialEq, Serialize)]
pub struct TransformationReceiptV0 {
    receipt_format: String,
    receipt_version: String,
    input_authority_commitment: String,
    authorized_capture_seal: RawCaptureSealV0,
    adapter: ArtifactBindingV0,
    schema: ArtifactBindingV0,
    downstream_governance_policy: ArtifactBindingV0,
    transformation_policy: ArtifactBindingV0,
    normalized_trace_digest: String,
    sanitized_fixture_seal: Option<RawCaptureSealV0>,
    payload_manifest: Vec<PayloadManifestEntryV0>,
}

#[derive(Eq, PartialEq, Serialize)]
pub struct PrivateAdapterBundleV0 {
    bundle_format: String,
    bundle_version: String,
    evidence_class: String,
    authority_commitment: String,
    schema: ArtifactBindingV0,
    adapter: ArtifactBindingV0,
    downstream_governance_policy: ArtifactBindingV0,
    official_trace_json: String,
    canonical_trace_lower_hex: String,
    trajectory_digest: String,
    payload_manifest: Vec<PayloadManifestEntryV0>,
    transformation_receipt: TransformationReceiptV0,
}

#[derive(Eq, PartialEq, Serialize)]
pub(super) struct PublicationBundleFieldsV0 {
    bundle_format: String,
    bundle_version: String,
    evidence_class: String,
    public_derived_receipt: PublicDerivedReceiptProjectionV0,
    schema: ArtifactBindingV0,
    adapter: ArtifactBindingV0,
    downstream_governance_policy: ArtifactBindingV0,
    sanitizer: ArtifactBindingV0,
    official_trace_json: String,
    canonical_trace_lower_hex: String,
    trajectory_digest: String,
    payload_manifest: Vec<PayloadManifestEntryV0>,
    public_transformation: PublicTransformationProjectionV0,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct PublicTransformationProjectionV0 {
    projection_format: String,
    projection_version: String,
    adapter: ArtifactBindingV0,
    schema: ArtifactBindingV0,
    downstream_governance_policy: ArtifactBindingV0,
    sanitizer_policy: ArtifactBindingV0,
    normalized_trace_digest: String,
    derived_capture_seal: RawCaptureSealV0,
    payload_manifest: Vec<PayloadManifestEntryV0>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct PayloadManifestEntryV0 {
    role: ComponentRoleV0,
    format: ComponentFormatV0,
    ordinal: u8,
    byte_length: u64,
    digest: String,
}

impl PayloadManifestEntryV0 {
    fn new(role: ComponentRoleV0, format: ComponentFormatV0, ordinal: u8, bytes: &[u8]) -> Self {
        let domain = format!("{COMPONENT_DOMAIN_PREFIX_V0}.{}.v0", role.label());
        Self {
            role,
            format,
            ordinal,
            byte_length: bytes.len() as u64,
            digest: framed_sha256(&domain, &[bytes]),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum ComponentRoleV0 {
    OfficialTraceJson,
    CanonicalTrace,
}

impl ComponentRoleV0 {
    const fn label(self) -> &'static str {
        match self {
            Self::OfficialTraceJson => "official-trace-json",
            Self::CanonicalTrace => "canonical-trace",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
enum ComponentFormatV0 {
    TrajectoryV0CompactJson,
    TrajectoryV0CanonicalBytes,
}

struct OutputComponentsV0 {
    official_trace_json: String,
    canonical_trace: Vec<u8>,
    trajectory_digest: String,
    payload_manifest: Vec<PayloadManifestEntryV0>,
}

impl PrivateAdapterBundleV0 {
    pub fn to_json_line(&self) -> AdapterResultV0<Vec<u8>> {
        serialize_line(self)
    }
}

fn serialize_line(value: &impl Serialize) -> AdapterResultV0<Vec<u8>> {
    let mut output = CappedVecWriterV0::new(MAX_ADAPTER_BUNDLE_BYTES_V0 - 1);
    serde_json::to_writer(&mut output, value).map_err(|_| {
        AdapterErrorV0::new(if output.exceeded {
            AdapterErrorCodeV0::InputTooLarge
        } else {
            AdapterErrorCodeV0::Validation
        })
    })?;
    let mut output = output.bytes;
    output.push(b'\n');
    Ok(output)
}

fn lower_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        output.push(HEX[usize::from(byte >> 4)] as char);
        output.push(HEX[usize::from(byte & 0x0f)] as char);
    }
    output
}

struct CappedVecWriterV0 {
    bytes: Vec<u8>,
    cap: usize,
    exceeded: bool,
}

impl CappedVecWriterV0 {
    fn new(cap: usize) -> Self {
        Self {
            bytes: Vec::new(),
            cap,
            exceeded: false,
        }
    }
}

impl Write for CappedVecWriterV0 {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let next = self
            .bytes
            .len()
            .checked_add(bytes.len())
            .ok_or_else(|| io::Error::other("bounded output overflow"))?;
        if next > self.cap {
            self.exceeded = true;
            return Err(io::Error::other("bounded output limit"));
        }
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

macro_rules! redacted_debug {
    ($type:ty, $label:literal) => {
        impl fmt::Debug for $type {
            fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str(concat!($label, " { <redacted> }"))
            }
        }
    };
}

redacted_debug!(AdaptedCodexExecV0, "AdaptedCodexExecV0");
redacted_debug!(TransformationReceiptV0, "TransformationReceiptV0");
redacted_debug!(PrivateAdapterBundleV0, "PrivateAdapterBundleV0");
