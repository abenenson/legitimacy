use super::*;
use crate::trajectory::duplicate_json::{self, JsonRootKind, JsonScanLimits};
use serde::Deserialize;
use std::fmt;

const BUNDLE_LIMITS: JsonScanLimits = JsonScanLimits {
    max_depth: 48,
    max_nodes: 200_000,
    max_total_keys: 100_000,
    max_decoded_string_bytes: MAX_ADAPTER_BUNDLE_BYTES_V0,
};

pub struct InspectedPrivateAdapterBundleV0 {
    bytes: Vec<u8>,
    official_trace_json: String,
}

pub struct InspectedShareableSanitizedBundleV0 {
    bytes: Vec<u8>,
    wire: ShareableBundleWireV0,
}

pub struct RevalidatedPrivateAdapterBundleV0 {
    adapted: AdaptedCodexExecV0,
    bundle: PrivateAdapterBundleV0,
}

pub struct RevalidatedShareableSanitizedBundleV0 {
    adapted: AdaptedCodexExecV0,
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

redacted_debug!(
    InspectedPrivateAdapterBundleV0,
    "InspectedPrivateAdapterBundleV0"
);
redacted_debug!(
    InspectedShareableSanitizedBundleV0,
    "InspectedShareableSanitizedBundleV0"
);
redacted_debug!(
    RevalidatedPrivateAdapterBundleV0,
    "RevalidatedPrivateAdapterBundleV0"
);
redacted_debug!(
    RevalidatedShareableSanitizedBundleV0,
    "RevalidatedShareableSanitizedBundleV0"
);

impl InspectedPrivateAdapterBundleV0 {
    pub fn from_json_slice(input: &[u8]) -> AdapterResultV0<Self> {
        let body = preflight_bundle(input)?;
        let wire: PrivateBundleWireV0 = serde_json::from_slice(body)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::JsonShape))?;
        Ok(Self {
            bytes: input.to_vec(),
            official_trace_json: wire.official_trace_json,
        })
    }

    pub fn revalidate(
        self,
        jsonl: &[u8],
        authority: &InputAuthorityReceiptV0,
        context: &TrustedAdaptationContextV0,
    ) -> AdapterResultV0<RevalidatedPrivateAdapterBundleV0> {
        let supplied_trace =
            TrajectoryTraceV0::from_json_slice(self.official_trace_json.as_bytes())
                .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::BundleMismatch))?;
        let adapted = adapt(jsonl, authority, context)?;
        let records = adapted.capture.record_slices();
        supplied_trace
            .validate(&records, &adapted.validation_declarations)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::BundleMismatch))?;
        let bundle = adapted.to_private_bundle()?;
        if bundle.to_json_line()? != self.bytes {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::BundleMismatch));
        }
        Ok(RevalidatedPrivateAdapterBundleV0 { adapted, bundle })
    }
}

impl InspectedShareableSanitizedBundleV0 {
    pub fn from_json_slice(input: &[u8]) -> AdapterResultV0<Self> {
        let body = preflight_bundle(input)?;
        let wire: ShareableBundleWireV0 = serde_json::from_slice(body)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::JsonShape))?;
        Ok(Self {
            bytes: input.to_vec(),
            wire,
        })
    }

    /// Revalidates the exact sanitized child against the closed public projection.
    ///
    /// This reruns framing, parsing, stream validation, mapping, trajectory
    /// validation, and every deterministic public trace component. It establishes
    /// no private-parent link; owner-private sidecar admission remains separate.
    pub fn revalidate_public_projection(
        self,
        jsonl: &[u8],
    ) -> AdapterResultV0<RevalidatedShareableSanitizedBundleV0> {
        let adapted = self.wire.revalidate_public_projection(jsonl)?;
        Ok(RevalidatedShareableSanitizedBundleV0 { adapted })
    }

    pub(in crate::trajectory::codex_exec_v0) fn revalidate_expected(
        self,
        adapted: AdaptedCodexExecV0,
        expected_bytes: Vec<u8>,
    ) -> AdapterResultV0<RevalidatedShareableSanitizedBundleV0> {
        let supplied_trace =
            TrajectoryTraceV0::from_json_slice(self.wire.official_trace_json.as_bytes())
                .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::BundleMismatch))?;
        let records = adapted.capture.record_slices();
        supplied_trace
            .validate(&records, &adapted.validation_declarations)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::BundleMismatch))?;
        if expected_bytes != self.bytes {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::BundleMismatch));
        }
        Ok(RevalidatedShareableSanitizedBundleV0 { adapted })
    }
}

impl RevalidatedPrivateAdapterBundleV0 {
    pub fn validate(&self) -> AdapterResultV0<ValidatedTrajectoryTraceV0<'_>> {
        self.adapted.validate()
    }

    pub fn bundle(&self) -> &PrivateAdapterBundleV0 {
        &self.bundle
    }
}

impl RevalidatedShareableSanitizedBundleV0 {
    /// Revalidates the imported public bytes without recreating publication authority.
    ///
    /// This proves exact private attachment and regeneration under the supplied
    /// receipt/context. It does not prove that an original in-memory publication
    /// transaction existed and cannot emit a new shareable bundle.
    pub fn validate(&self) -> AdapterResultV0<ValidatedTrajectoryTraceV0<'_>> {
        self.adapted.validate()
    }

    pub fn with_validated<T>(
        &self,
        operation: impl FnOnce(&ValidatedTrajectoryTraceV0<'_>) -> T,
    ) -> AdapterResultV0<T> {
        self.adapted.with_validated(operation)
    }
}

impl ShareableBundleWireV0 {
    fn revalidate_public_projection(&self, jsonl: &[u8]) -> AdapterResultV0<AdaptedCodexExecV0> {
        use crate::trajectory::{raw_capture_seal_v0, trajectory_schema_binding_v0};

        super::super::sanitizer::scan_public_child_jsonl(jsonl)?;

        if self.bundle_format != "legitimacy.codex-exec-v0.shareable-sanitized-bundle"
            || self.bundle_version != "0"
            || self.evidence_class != "sanitizer-conforming-child-projection"
            || self.public_derived_receipt.projection_format
                != "legitimacy.codex-exec-v0.public-child-projection"
            || self.public_derived_receipt.projection_version != "0"
            || self.public_derived_receipt.evidence_class != "sanitizer-conforming-child-projection"
            || self.public_transformation.projection_format
                != "legitimacy.codex-exec-v0.public-deterministic-projection"
            || self.public_transformation.projection_version != "0"
        {
            return Err(bundle_mismatch());
        }
        let receipt = &self.public_derived_receipt;
        if receipt.sanitizer_policy != super::codex_exec_sanitizer_policy_binding_v0()
            || receipt.sanitizer_artifact != super::codex_exec_sanitizer_binding_v0()
            || self.schema != trajectory_schema_binding_v0()
            || self.adapter != super::codex_exec_adapter_binding_v0()
            || self.sanitizer != super::codex_exec_sanitizer_binding_v0()
            || self.public_transformation.adapter != self.adapter
            || self.public_transformation.schema != self.schema
            || self.public_transformation.downstream_governance_policy
                != self.downstream_governance_policy
            || self.public_transformation.sanitizer_policy != receipt.sanitizer_policy
            || self.public_transformation.normalized_trace_digest != self.trajectory_digest
            || self.public_transformation.derived_capture_seal != receipt.derived_raw_capture_seal
            || self.public_transformation.payload_manifest != self.payload_manifest
        {
            return Err(bundle_mismatch());
        }
        let framed = FramedCaptureV0::parse(jsonl)?;
        let records = framed.record_slices();
        if receipt.derived_full_jsonl_length != jsonl.len() as u64
            || receipt.derived_full_jsonl_digest != framed.full_digest()
            || receipt.derived_raw_capture_seal != raw_capture_seal_v0(&records)
        {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptMismatch));
        }
        let adapted = super::adapt_public_sanitized_owned(
            jsonl.to_vec(),
            receipt.derived_raw_capture_seal.clone(),
            self.downstream_governance_policy.clone(),
        )?;
        let supplied_trace =
            TrajectoryTraceV0::from_json_slice(self.official_trace_json.as_bytes())
                .map_err(|_| bundle_mismatch())?;
        supplied_trace
            .validate(&records, &adapted.validation_declarations)
            .map_err(|_| bundle_mismatch())?;
        if supplied_trace != adapted.trace {
            return Err(bundle_mismatch());
        }
        let components = adapted.components()?;
        let canonical =
            super::super::receipt::hex::decode_lower_hex(&self.canonical_trace_lower_hex)
                .map_err(|_| bundle_mismatch())?;
        if self.official_trace_json != components.official_trace_json
            || canonical != components.canonical_trace
            || self.trajectory_digest != components.trajectory_digest
            || !manifest_matches(&self.payload_manifest, &components.payload_manifest)
        {
            return Err(bundle_mismatch());
        }
        Ok(adapted)
    }
}

fn manifest_matches(supplied: &[ManifestWireV0], expected: &[PayloadManifestEntryV0]) -> bool {
    supplied.len() == expected.len()
        && supplied.iter().zip(expected).all(|(left, right)| {
            matches!(
                (&left.role, right.role),
                (
                    ComponentRoleWireV0::OfficialTraceJson,
                    ComponentRoleV0::OfficialTraceJson
                ) | (
                    ComponentRoleWireV0::CanonicalTrace,
                    ComponentRoleV0::CanonicalTrace
                )
            ) && matches!(
                (&left.format, right.format),
                (
                    ComponentFormatWireV0::TrajectoryV0CompactJson,
                    ComponentFormatV0::TrajectoryV0CompactJson
                ) | (
                    ComponentFormatWireV0::TrajectoryV0CanonicalBytes,
                    ComponentFormatV0::TrajectoryV0CanonicalBytes
                )
            ) && left.ordinal == right.ordinal
                && left.byte_length == right.byte_length
                && left.digest == right.digest
        })
}

fn bundle_mismatch() -> AdapterErrorV0 {
    AdapterErrorV0::new(AdapterErrorCodeV0::BundleMismatch)
}

fn preflight_bundle(input: &[u8]) -> AdapterResultV0<&[u8]> {
    if input.len() > MAX_ADAPTER_BUNDLE_BYTES_V0
        || input.is_empty()
        || input.last() != Some(&b'\n')
        || input[..input.len() - 1].contains(&b'\n')
        || input.contains(&b'\r')
    {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::JsonFraming));
    }
    let body = &input[..input.len() - 1];
    match duplicate_json::scan_json_with_limits(body, "adapter bundle", BUNDLE_LIMITS) {
        Ok(JsonRootKind::Object) => Ok(body),
        Ok(JsonRootKind::NonObject) => Err(AdapterErrorV0::new(AdapterErrorCodeV0::JsonShape)),
        Err(error) => Err(AdapterErrorV0::new(if error.is_budget() {
            AdapterErrorCodeV0::JsonBudget
        } else {
            AdapterErrorCodeV0::JsonSyntax
        })),
    }
}

#[allow(dead_code)]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PrivateBundleWireV0 {
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
    payload_manifest: Vec<ManifestWireV0>,
    transformation_receipt: TransformationWireV0,
}

#[allow(dead_code)]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ShareableBundleWireV0 {
    bundle_format: String,
    bundle_version: String,
    evidence_class: String,
    public_derived_receipt: PublicDerivedWireV0,
    schema: ArtifactBindingV0,
    adapter: ArtifactBindingV0,
    downstream_governance_policy: ArtifactBindingV0,
    sanitizer: ArtifactBindingV0,
    official_trace_json: String,
    canonical_trace_lower_hex: String,
    trajectory_digest: String,
    payload_manifest: Vec<ManifestWireV0>,
    public_transformation: PublicTransformationWireV0,
}

#[allow(dead_code)]
#[derive(Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct ManifestWireV0 {
    role: ComponentRoleWireV0,
    format: ComponentFormatWireV0,
    ordinal: u8,
    byte_length: u64,
    digest: String,
}

#[derive(Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum ComponentRoleWireV0 {
    OfficialTraceJson,
    CanonicalTrace,
}

#[derive(Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum ComponentFormatWireV0 {
    TrajectoryV0CompactJson,
    TrajectoryV0CanonicalBytes,
}

#[allow(dead_code)]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TransformationWireV0 {
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
    payload_manifest: Vec<ManifestWireV0>,
}

#[allow(dead_code)]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PublicDerivedWireV0 {
    projection_format: String,
    projection_version: String,
    evidence_class: String,
    derived_full_jsonl_length: u64,
    derived_full_jsonl_digest: String,
    derived_raw_capture_seal: RawCaptureSealV0,
    sanitizer_policy: ArtifactBindingV0,
    sanitizer_artifact: ArtifactBindingV0,
}

#[allow(dead_code)]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PublicTransformationWireV0 {
    projection_format: String,
    projection_version: String,
    adapter: ArtifactBindingV0,
    schema: ArtifactBindingV0,
    downstream_governance_policy: ArtifactBindingV0,
    sanitizer_policy: ArtifactBindingV0,
    normalized_trace_digest: String,
    derived_capture_seal: RawCaptureSealV0,
    payload_manifest: Vec<ManifestWireV0>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trajectory::codex_exec_v0::{
        FixedSyntheticTestNonceV0, SyntheticFixtureReceiptV0, codex_exec_fixture_spec_binding_v0,
        sanitize_capture_v0,
    };
    use crate::trajectory::{ArtifactBindingV0, artifact_digest_v0, raw_capture_seal_v0};
    use serde_json::json;

    const UNSANITIZED: &[u8] =
        include_bytes!("../../../tests/fixtures/codex-exec-v0/legal-completed.synthetic.jsonl");

    #[test]
    fn untrusted_public_wire_cannot_self_label_an_unsanitized_child() {
        let (_, bundle, policy) = public_import_fixture();
        assert_self_consistent_public_attack(UNSANITIZED, &bundle, policy);
    }

    #[test]
    fn untrusted_public_wire_rejects_each_bounded_privacy_variant() {
        let (honest_child, bundle, policy) = public_import_fixture();
        for private in [
            "data:text/plain,private",
            "javascript:private",
            "e30.e30.c2lnbmF0dXJl",
            "eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxIn0.c2ln",
            "sk_live_1234567890",
            "path=/root",
        ] {
            let marker = b"message_0000";
            assert_eq!(
                honest_child
                    .windows(marker.len())
                    .filter(|part| *part == marker)
                    .count(),
                1
            );
            let offset = honest_child
                .windows(marker.len())
                .position(|part| part == marker)
                .unwrap();
            let mut attack_child = honest_child.clone();
            attack_child.splice(offset..offset + marker.len(), private.bytes());
            let error =
                crate::trajectory::codex_exec_v0::sanitizer::scan_public_child_jsonl(&attack_child)
                    .unwrap_err();
            assert_eq!(error.code(), AdapterErrorCodeV0::SanitizerRejected);
            assert_self_consistent_public_attack(&attack_child, &bundle, policy.clone());
        }
    }

    fn public_import_fixture() -> (Vec<u8>, Vec<u8>, ArtifactBindingV0) {
        let parent = InputAuthorityReceiptV0::SyntheticFixture(
            SyntheticFixtureReceiptV0::new_with_fixed_test_nonce(
                UNSANITIZED,
                codex_exec_fixture_spec_binding_v0(),
                FixedSyntheticTestNonceV0::new([0x71; 32]),
            )
            .unwrap(),
        );
        let policy = ArtifactBindingV0 {
            identity: "policy.public-import-kill-test".to_string(),
            version: "test".to_string(),
            hash: artifact_digest_v0(b"public-import-kill-test"),
        };
        let context = TrustedAdaptationContextV0::new(parent.commitment(), policy.clone()).unwrap();
        let transaction = sanitize_capture_v0(UNSANITIZED, &parent, &context).unwrap();
        let child = transaction.jsonl().to_vec();
        let (_, honest_bundle) = transaction.into_publication_pair().unwrap();
        (child, honest_bundle.to_json_line().unwrap(), policy)
    }

    fn assert_self_consistent_public_attack(
        child: &[u8],
        honest_bundle: &[u8],
        policy: ArtifactBindingV0,
    ) {
        let mut attack: serde_json::Value = serde_json::from_slice(honest_bundle).unwrap();

        let framed = FramedCaptureV0::parse(child).unwrap();
        let raw_seal = raw_capture_seal_v0(&framed.record_slices());
        let adapted =
            super::super::adapt_public_sanitized_owned(child.to_vec(), raw_seal.clone(), policy)
                .unwrap();
        let components = adapted.components().unwrap();
        attack["public_derived_receipt"]["derived_full_jsonl_length"] = json!(child.len() as u64);
        attack["public_derived_receipt"]["derived_full_jsonl_digest"] = json!(framed.full_digest());
        attack["public_derived_receipt"]["derived_raw_capture_seal"] = json!(raw_seal);
        attack["official_trace_json"] = json!(components.official_trace_json);
        attack["canonical_trace_lower_hex"] =
            json!(super::super::lower_hex(&components.canonical_trace));
        attack["trajectory_digest"] = json!(components.trajectory_digest);
        attack["payload_manifest"] = json!(components.payload_manifest);
        attack["public_transformation"]["normalized_trace_digest"] =
            attack["trajectory_digest"].clone();
        attack["public_transformation"]["derived_capture_seal"] =
            attack["public_derived_receipt"]["derived_raw_capture_seal"].clone();
        attack["public_transformation"]["payload_manifest"] = attack["payload_manifest"].clone();
        let mut bytes = serde_json::to_vec(&attack).unwrap();
        bytes.push(b'\n');

        let error = InspectedShareableSanitizedBundleV0::from_json_slice(&bytes)
            .unwrap()
            .revalidate_public_projection(child)
            .unwrap_err();
        assert_eq!(error.code(), AdapterErrorCodeV0::SanitizerRejected);
    }
}
