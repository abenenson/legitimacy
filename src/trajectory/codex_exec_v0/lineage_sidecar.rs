use super::bundle::{
    InspectedShareableSanitizedBundleV0, RevalidatedShareableSanitizedBundleV0, adapt,
};
use super::error::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0};
use super::publication_authority::{
    has_expected_private_lineage_commitment, render_expected_publication_bytes,
};
use super::receipt::{InputAuthorityReceiptV0, TrustedAdaptationContextV0};
use super::{
    MAX_AUTHORITY_RECEIPT_BYTES_V0, MAX_CODEX_JSONL_BYTES_V0, MAX_TRUSTED_CONTEXT_BYTES_V0,
};
use std::fmt;

const MAGIC_V0: &[u8] = b"legitimacy.codex-exec-v0.owner-private-lineage.v1\0";
const VERSION_V0: u8 = 1;
const REBLINDING_NONCE_BYTES_V0: usize = 32;
const COMMITMENT_BYTES_V0: usize = 71;
const LENGTH_FIELDS_BYTES_V0: usize = 5 * size_of::<u64>();
const HEADER_BYTES_V0: usize = MAGIC_V0.len() + 1 + LENGTH_FIELDS_BYTES_V0;

pub const MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0: usize = HEADER_BYTES_V0
    + MAX_CODEX_JSONL_BYTES_V0
    + MAX_AUTHORITY_RECEIPT_BYTES_V0
    + MAX_TRUSTED_CONTEXT_BYTES_V0
    + (2 * COMMITMENT_BYTES_V0)
    + REBLINDING_NONCE_BYTES_V0;

/// Owner-private custody for exact regeneration of one public/private pair.
///
/// The frame retains the original parent commitment and the locally drawn
/// publication-parent reblinding nonce. It is inspect-only material: importing
/// it can regenerate comparison bytes but cannot recover publication authority.
pub struct OwnerPrivateLineageSidecarV0 {
    bytes: Vec<u8>,
    child_start: usize,
    child_end: usize,
    authority: InputAuthorityReceiptV0,
    context: TrustedAdaptationContextV0,
}

impl fmt::Debug for OwnerPrivateLineageSidecarV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("OwnerPrivateLineageSidecarV0 { <redacted> }")
    }
}

impl OwnerPrivateLineageSidecarV0 {
    pub fn from_binary_slice(input: &[u8]) -> AdapterResultV0<Self> {
        if input.len() > MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0 {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge));
        }
        Self::decode(input.to_vec())
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    pub fn revalidate_public_bundle(
        self,
        inspected: InspectedShareableSanitizedBundleV0,
    ) -> AdapterResultV0<RevalidatedShareableSanitizedBundleV0> {
        let child = &self.bytes[self.child_start..self.child_end];
        let adapted = adapt(child, &self.authority, &self.context)?;
        let expected = render_expected_publication_bytes(&adapted, &self.authority, &self.context)?;
        inspected.revalidate_expected(adapted, expected)
    }

    /// Revalidates the private parent link and requires the caller's exact
    /// sanitized attachment to be the child sealed inside this sidecar.
    pub fn revalidate_public_bundle_for_jsonl(
        self,
        inspected: InspectedShareableSanitizedBundleV0,
        sanitized_jsonl: &[u8],
    ) -> AdapterResultV0<RevalidatedShareableSanitizedBundleV0> {
        if &self.bytes[self.child_start..self.child_end] != sanitized_jsonl {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptMismatch));
        }
        self.revalidate_public_bundle(inspected)
    }

    pub(super) fn build(
        child_jsonl: &[u8],
        authority: &InputAuthorityReceiptV0,
        context: &TrustedAdaptationContextV0,
        original_parent_receipt_commitment: &str,
        publication_parent_reblinding_nonce: [u8; 32],
        private_lineage_commitment: &str,
    ) -> AdapterResultV0<Self> {
        if child_jsonl.len() > MAX_CODEX_JSONL_BYTES_V0 {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge));
        }
        let authority_json = serde_json::to_vec(authority)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::LineageSidecarShape))?;
        let context_json = serde_json::to_vec(context)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::LineageSidecarShape))?;
        let total = HEADER_BYTES_V0
            .checked_add(child_jsonl.len())
            .and_then(|value| value.checked_add(authority_json.len()))
            .and_then(|value| value.checked_add(context_json.len()))
            .and_then(|value| value.checked_add(original_parent_receipt_commitment.len()))
            .and_then(|value| value.checked_add(REBLINDING_NONCE_BYTES_V0))
            .and_then(|value| value.checked_add(private_lineage_commitment.len()))
            .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge))?;
        if total > MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0 {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge));
        }

        let mut bytes = Vec::with_capacity(total);
        bytes.extend_from_slice(MAGIC_V0);
        bytes.push(VERSION_V0);
        push_length(&mut bytes, child_jsonl.len())?;
        push_length(&mut bytes, authority_json.len())?;
        push_length(&mut bytes, context_json.len())?;
        push_length(&mut bytes, original_parent_receipt_commitment.len())?;
        push_length(&mut bytes, private_lineage_commitment.len())?;
        bytes.extend_from_slice(child_jsonl);
        bytes.extend_from_slice(&authority_json);
        bytes.extend_from_slice(&context_json);
        bytes.extend_from_slice(original_parent_receipt_commitment.as_bytes());
        bytes.extend_from_slice(&publication_parent_reblinding_nonce);
        bytes.extend_from_slice(private_lineage_commitment.as_bytes());
        Self::decode(bytes)
    }

    fn decode(bytes: Vec<u8>) -> AdapterResultV0<Self> {
        if bytes.len() > MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0 {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge));
        }
        if bytes.len() < HEADER_BYTES_V0
            || &bytes[..MAGIC_V0.len()] != MAGIC_V0
            || bytes[MAGIC_V0.len()] != VERSION_V0
        {
            return Err(shape_error());
        }

        let mut cursor = MAGIC_V0.len() + 1;
        let child_len = take_length(&bytes, &mut cursor, MAX_CODEX_JSONL_BYTES_V0)?;
        let authority_len = take_length(&bytes, &mut cursor, MAX_AUTHORITY_RECEIPT_BYTES_V0)?;
        let context_len = take_length(&bytes, &mut cursor, MAX_TRUSTED_CONTEXT_BYTES_V0)?;
        let original_parent_len = take_length(&bytes, &mut cursor, COMMITMENT_BYTES_V0)?;
        let private_lineage_len = take_length(&bytes, &mut cursor, COMMITMENT_BYTES_V0)?;

        let child_start = cursor;
        let child_end = child_start.checked_add(child_len).ok_or_else(shape_error)?;
        let authority_end = child_end
            .checked_add(authority_len)
            .ok_or_else(shape_error)?;
        let context_end = authority_end
            .checked_add(context_len)
            .ok_or_else(shape_error)?;
        let original_parent_end = context_end
            .checked_add(original_parent_len)
            .ok_or_else(shape_error)?;
        let nonce_end = original_parent_end
            .checked_add(REBLINDING_NONCE_BYTES_V0)
            .ok_or_else(shape_error)?;
        let private_lineage_end = nonce_end
            .checked_add(private_lineage_len)
            .ok_or_else(shape_error)?;
        if private_lineage_end != bytes.len() {
            return Err(shape_error());
        }

        let authority_json = &bytes[child_end..authority_end];
        let context_json = &bytes[authority_end..context_end];
        let authority = InputAuthorityReceiptV0::from_json_slice(authority_json)?;
        if !matches!(
            authority,
            InputAuthorityReceiptV0::SanitizedDerivedCapture(_)
        ) {
            return Err(shape_error());
        }
        let context = TrustedAdaptationContextV0::from_json_slice(context_json)?;
        let canonical_authority = serde_json::to_vec(&authority)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::LineageSidecarShape))?;
        let canonical_context = serde_json::to_vec(&context)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::LineageSidecarShape))?;
        if canonical_authority != authority_json || canonical_context != context_json {
            return Err(shape_error());
        }
        let original_parent_receipt_commitment =
            decode_commitment(&bytes[context_end..original_parent_end])?;
        if authority.parent_commitment() != Some(original_parent_receipt_commitment.as_str()) {
            return Err(shape_error());
        }
        let publication_parent_reblinding_nonce: [u8; 32] = bytes
            .get(original_parent_end..nonce_end)
            .ok_or_else(shape_error)?
            .try_into()
            .map_err(|_| shape_error())?;
        if publication_parent_reblinding_nonce
            .iter()
            .all(|byte| *byte == 0)
        {
            return Err(shape_error());
        }
        let private_lineage_commitment = decode_commitment(&bytes[nonce_end..private_lineage_end])?;
        let adapted = adapt(&bytes[child_start..child_end], &authority, &context)?;
        if !has_expected_private_lineage_commitment(
            &authority,
            &context,
            &original_parent_receipt_commitment,
            &publication_parent_reblinding_nonce,
            &private_lineage_commitment,
        )? {
            return Err(shape_error());
        }
        drop(adapted);

        Ok(Self {
            bytes,
            child_start,
            child_end,
            authority,
            context,
        })
    }
}

fn push_length(output: &mut Vec<u8>, length: usize) -> AdapterResultV0<()> {
    let length = u64::try_from(length)
        .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge))?;
    output.extend_from_slice(&length.to_be_bytes());
    Ok(())
}

fn take_length(input: &[u8], cursor: &mut usize, cap: usize) -> AdapterResultV0<usize> {
    let end = cursor
        .checked_add(size_of::<u64>())
        .ok_or_else(shape_error)?;
    let encoded: [u8; 8] = input
        .get(*cursor..end)
        .ok_or_else(shape_error)?
        .try_into()
        .map_err(|_| shape_error())?;
    *cursor = end;
    let length = u64::from_be_bytes(encoded);
    if length > cap as u64 {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge));
    }
    usize::try_from(length).map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge))
}

fn decode_commitment(input: &[u8]) -> AdapterResultV0<String> {
    let value = std::str::from_utf8(input).map_err(|_| shape_error())?;
    let valid = value
        .strip_prefix("sha256:")
        .is_some_and(|hex| hex.len() == 64 && hex.bytes().all(|byte| byte.is_ascii_hexdigit()));
    if !valid || value.bytes().any(|byte| byte.is_ascii_uppercase()) {
        return Err(shape_error());
    }
    Ok(value.to_string())
}

fn shape_error() -> AdapterErrorV0 {
    AdapterErrorV0::new(AdapterErrorCodeV0::LineageSidecarShape)
}
