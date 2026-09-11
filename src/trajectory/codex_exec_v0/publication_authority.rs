//! Sealed ownership boundary for one-shot public bundle construction.

use super::bundle::{AdaptedCodexExecV0, PublicationBundleFieldsV0};
use super::error::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0};
use super::lineage_sidecar::OwnerPrivateLineageSidecarV0;
use super::receipt::nonce::NonceMaterialV0;
use super::receipt::{
    InputAuthorityReceiptV0, SanitizedDerivedCaptureReceiptV0, TrustedAdaptationContextV0,
};
use super::sanitizer::{
    SanitizedCaptureV0, sanitize_capture_with_nonce_v0, scan_publication_bundle_json,
};
use super::{
    MAX_ADAPTER_BUNDLE_BYTES_V0, codex_exec_adapter_binding_v0, codex_exec_sanitizer_binding_v0,
    codex_exec_sanitizer_policy_binding_v0,
};
use crate::trajectory::{
    ArtifactBindingV0, RawCaptureSealV0, framed_sha256, trajectory_schema_binding_v0,
};
use std::fmt;

const PRIVATE_LINEAGE_COMMITMENT_DOMAIN_V0: &str =
    "legitimacy.codex-exec-v0.owner-private-lineage-commitment.v0";

struct PublicationMintV0 {
    publication_parent_reblinding_nonce: NonceMaterialV0,
}

struct SanitizationBindingsV0 {
    original_parent_receipt_commitment: String,
    derived_receipt_commitment: String,
    child_jsonl_length: u64,
    child_jsonl_digest: String,
    child_record_seal: RawCaptureSealV0,
    downstream_policy: ArtifactBindingV0,
    adapter: ArtifactBindingV0,
    schema: ArtifactBindingV0,
    sanitizer_policy: ArtifactBindingV0,
    sanitizer_implementation: ArtifactBindingV0,
}

pub struct ProductionSanitizationTransactionV0 {
    sanitized: SanitizedCaptureV0,
    bindings: SanitizationBindingsV0,
    mint: PublicationMintV0,
}

pub struct ShareableSanitizedBundleV0 {
    bytes: Vec<u8>,
}

struct RenderedPublicationV0 {
    private_lineage_commitment: String,
    bytes: Vec<u8>,
}

pub fn sanitize_capture_v0(
    parent_jsonl: &[u8],
    parent_authority: &InputAuthorityReceiptV0,
    parent_trusted_context: &TrustedAdaptationContextV0,
) -> AdapterResultV0<ProductionSanitizationTransactionV0> {
    let derived_capture_nonce = NonceMaterialV0::capture_random()?;
    let publication_parent_reblinding_nonce = NonceMaterialV0::capture_random()?;
    if derived_capture_nonce.bytes() == publication_parent_reblinding_nonce.bytes() {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::EntropyUnavailable));
    }
    let mint = PublicationMintV0 {
        publication_parent_reblinding_nonce,
    };
    let sanitized = sanitize_capture_with_nonce_v0(
        parent_jsonl,
        parent_authority,
        parent_trusted_context,
        derived_capture_nonce,
    )?;
    ProductionSanitizationTransactionV0::new(
        parent_authority,
        parent_trusted_context,
        sanitized,
        mint,
    )
}

impl ProductionSanitizationTransactionV0 {
    fn new(
        parent_authority: &InputAuthorityReceiptV0,
        parent_context: &TrustedAdaptationContextV0,
        sanitized: SanitizedCaptureV0,
        mint: PublicationMintV0,
    ) -> AdapterResultV0<Self> {
        let bindings = SanitizationBindingsV0 {
            original_parent_receipt_commitment: parent_authority.commitment(),
            derived_receipt_commitment: sanitized.authority.commitment(),
            child_jsonl_length: sanitized.adapted.jsonl().len() as u64,
            child_jsonl_digest: sanitized.adapted.capture.full_digest(),
            child_record_seal: sanitized.authority.raw_seal().clone(),
            downstream_policy: parent_context.downstream_governance_policy().clone(),
            adapter: codex_exec_adapter_binding_v0(),
            schema: trajectory_schema_binding_v0(),
            sanitizer_policy: codex_exec_sanitizer_policy_binding_v0(),
            sanitizer_implementation: codex_exec_sanitizer_binding_v0(),
        };
        let transaction = Self {
            sanitized,
            bindings,
            mint,
        };
        transaction.validate_attachment()?;
        Ok(transaction)
    }

    pub fn jsonl(&self) -> &[u8] {
        self.sanitized.adapted.jsonl()
    }

    pub fn private_receipt(&self) -> AdapterResultV0<&SanitizedDerivedCaptureReceiptV0> {
        self.sanitized.authority.sanitized_derived_receipt()
    }

    pub fn authority(&self) -> &InputAuthorityReceiptV0 {
        &self.sanitized.authority
    }

    pub fn derived_context(&self) -> &TrustedAdaptationContextV0 {
        &self.sanitized.derived_context
    }

    pub fn adapted(&self) -> &AdaptedCodexExecV0 {
        &self.sanitized.adapted
    }

    pub fn into_publication_pair(
        self,
    ) -> AdapterResultV0<(OwnerPrivateLineageSidecarV0, ShareableSanitizedBundleV0)> {
        self.validate_attachment()?;
        self.private_receipt()?;
        let Self {
            sanitized,
            bindings,
            mint,
        } = self;
        let reblinding_nonce = *mint.publication_parent_reblinding_nonce.bytes();
        let rendered = render_publication(
            &sanitized.adapted,
            &sanitized.authority,
            &sanitized.derived_context,
            &bindings.original_parent_receipt_commitment,
            &reblinding_nonce,
        )?;
        let sidecar = OwnerPrivateLineageSidecarV0::build(
            sanitized.adapted.jsonl(),
            &sanitized.authority,
            &sanitized.derived_context,
            &bindings.original_parent_receipt_commitment,
            reblinding_nonce,
            &rendered.private_lineage_commitment,
        )?;
        let bundle = ShareableSanitizedBundleV0 {
            bytes: rendered.bytes,
        };
        Ok((sidecar, bundle))
    }

    fn validate_attachment(&self) -> AdapterResultV0<()> {
        let exact = self.sanitized.authority.parent_commitment()
            == Some(self.bindings.original_parent_receipt_commitment.as_str())
            && self.sanitized.authority.commitment() == self.bindings.derived_receipt_commitment
            && self.sanitized.adapted.jsonl().len() as u64 == self.bindings.child_jsonl_length
            && self.sanitized.adapted.capture.full_digest() == self.bindings.child_jsonl_digest
            && self.sanitized.authority.raw_seal() == &self.bindings.child_record_seal
            && self.sanitized.adapted.downstream_policy() == &self.bindings.downstream_policy
            && self
                .sanitized
                .derived_context
                .downstream_governance_policy()
                == &self.bindings.downstream_policy
            && codex_exec_adapter_binding_v0() == self.bindings.adapter
            && trajectory_schema_binding_v0() == self.bindings.schema
            && codex_exec_sanitizer_policy_binding_v0() == self.bindings.sanitizer_policy
            && codex_exec_sanitizer_binding_v0() == self.bindings.sanitizer_implementation
            && self
                .sanitized
                .adapted
                .has_exact_authority(&self.sanitized.authority);
        if !exact {
            return Err(AdapterErrorV0::new(
                AdapterErrorCodeV0::PublicShareabilityDenied,
            ));
        }
        Ok(())
    }
}

impl ShareableSanitizedBundleV0 {
    pub fn to_json_line(&self) -> AdapterResultV0<Vec<u8>> {
        Ok(self.bytes.clone())
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

impl fmt::Debug for ProductionSanitizationTransactionV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("ProductionSanitizationTransactionV0 { <redacted> }")
    }
}

impl fmt::Debug for ShareableSanitizedBundleV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("ShareableSanitizedBundleV0 { <redacted> }")
    }
}

fn render_publication(
    adapted: &AdaptedCodexExecV0,
    authority: &InputAuthorityReceiptV0,
    context: &TrustedAdaptationContextV0,
    original_parent_receipt_commitment: &str,
    publication_parent_reblinding_nonce: &[u8; 32],
) -> AdapterResultV0<RenderedPublicationV0> {
    if authority.parent_commitment() != Some(original_parent_receipt_commitment)
        || adapted.downstream_policy() != context.downstream_governance_policy()
    {
        return Err(AdapterErrorV0::new(
            AdapterErrorCodeV0::PublicShareabilityDenied,
        ));
    }
    let private_lineage_commitment = private_lineage_commitment(
        authority,
        context,
        original_parent_receipt_commitment,
        publication_parent_reblinding_nonce,
    )?;
    let public_derived_receipt = authority.public_derived_projection()?;
    let fields: PublicationBundleFieldsV0 = adapted.publication_fields(public_derived_receipt)?;
    let mut bytes = serde_json::to_vec(&fields)
        .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::Validation))?;
    if bytes.len() >= MAX_ADAPTER_BUNDLE_BYTES_V0 {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge));
    }
    bytes.push(b'\n');
    scan_publication_bundle_json(&bytes)?;
    Ok(RenderedPublicationV0 {
        private_lineage_commitment,
        bytes,
    })
}

pub(super) fn render_expected_publication_bytes(
    adapted: &AdaptedCodexExecV0,
    authority: &InputAuthorityReceiptV0,
    _context: &TrustedAdaptationContextV0,
) -> AdapterResultV0<Vec<u8>> {
    let public_derived_receipt = authority.public_derived_projection()?;
    let fields: PublicationBundleFieldsV0 = adapted.publication_fields(public_derived_receipt)?;
    let mut bytes = serde_json::to_vec(&fields)
        .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::Validation))?;
    if bytes.len() >= MAX_ADAPTER_BUNDLE_BYTES_V0 {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge));
    }
    bytes.push(b'\n');
    scan_publication_bundle_json(&bytes)?;
    Ok(bytes)
}

pub(super) fn has_expected_private_lineage_commitment(
    authority: &InputAuthorityReceiptV0,
    context: &TrustedAdaptationContextV0,
    original_parent_receipt_commitment: &str,
    publication_parent_reblinding_nonce: &[u8; 32],
    supplied_private_lineage_commitment: &str,
) -> AdapterResultV0<bool> {
    Ok(private_lineage_commitment(
        authority,
        context,
        original_parent_receipt_commitment,
        publication_parent_reblinding_nonce,
    )? == supplied_private_lineage_commitment)
}

fn private_lineage_commitment(
    authority: &InputAuthorityReceiptV0,
    context: &TrustedAdaptationContextV0,
    original_parent_receipt_commitment: &str,
    publication_parent_reblinding_nonce: &[u8; 32],
) -> AdapterResultV0<String> {
    let (asserted_origin, asserted_parent, asserted_derived_nonce_source) =
        authority.publication_assertions()?;
    let downstream_policy = context.downstream_governance_policy();
    let adapter = codex_exec_adapter_binding_v0();
    let schema = trajectory_schema_binding_v0();
    let sanitizer_policy = codex_exec_sanitizer_policy_binding_v0();
    let sanitizer_implementation = codex_exec_sanitizer_binding_v0();
    Ok(framed_sha256(
        PRIVATE_LINEAGE_COMMITMENT_DOMAIN_V0,
        &[
            b"version=0",
            original_parent_receipt_commitment.as_bytes(),
            publication_parent_reblinding_nonce,
            asserted_origin.as_bytes(),
            asserted_parent.label().as_bytes(),
            asserted_derived_nonce_source.label().as_bytes(),
            downstream_policy.identity.as_bytes(),
            downstream_policy.version.as_bytes(),
            downstream_policy.hash.as_bytes(),
            adapter.identity.as_bytes(),
            adapter.version.as_bytes(),
            adapter.hash.as_bytes(),
            schema.identity.as_bytes(),
            schema.version.as_bytes(),
            schema.hash.as_bytes(),
            sanitizer_policy.identity.as_bytes(),
            sanitizer_policy.version.as_bytes(),
            sanitizer_policy.hash.as_bytes(),
            sanitizer_implementation.identity.as_bytes(),
            sanitizer_implementation.version.as_bytes(),
            sanitizer_implementation.hash.as_bytes(),
        ],
    ))
}
