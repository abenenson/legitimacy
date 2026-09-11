use legitimacy::trajectory::codex_exec_v0::{
    AdapterErrorCodeV0, AdapterErrorV0, InputAuthorityReceiptV0,
    InspectedShareableSanitizedBundleV0, MAX_ADAPTER_BUNDLE_BYTES_V0,
    MAX_AUTHORITY_RECEIPT_BYTES_V0, MAX_CODEX_JSONL_BYTES_V0,
    MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0, MAX_TRUSTED_CONTEXT_BYTES_V0,
    OwnerPrivateLineageSidecarV0, TrustedAdaptationContextV0, adapt_codex_exec_owned_v0,
    sanitize_capture_v0,
};
use std::path::Path;

#[cfg(target_os = "linux")]
mod linux_output;
#[cfg(target_os = "linux")]
mod linux_path;

#[cfg(target_os = "linux")]
pub(crate) use linux_output::{PublicationSpecV0, publish, publish_directory_set, publish_set};
#[cfg(target_os = "linux")]
pub(crate) use linux_path::{
    SnapshotV0, read_snapshot, reject_duplicate_inodes, require_owner_private,
};

#[derive(Clone, Copy, Debug, clap::ValueEnum)]
pub(crate) enum CodexExecOutputTypeV0 {
    Private,
    ShareableSanitized,
}

pub(crate) fn run(
    raw_stdout_jsonl: &Path,
    authority_receipt: &Path,
    trusted_context: &Path,
    output_type: CodexExecOutputTypeV0,
    output: &Path,
    private_lineage_output: Option<&Path>,
) -> Result<(), AdapterErrorV0> {
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (
            raw_stdout_jsonl,
            authority_receipt,
            trusted_context,
            output_type,
            output,
            private_lineage_output,
        );
        return Err(AdapterErrorV0::from_code(
            AdapterErrorCodeV0::UnsupportedPlatform,
        ));
    }
    #[cfg(target_os = "linux")]
    {
        let mut raw = linux_path::read_snapshot(raw_stdout_jsonl, MAX_CODEX_JSONL_BYTES_V0)?;
        let receipt = linux_path::read_snapshot(authority_receipt, MAX_AUTHORITY_RECEIPT_BYTES_V0)?;
        let context = linux_path::read_snapshot(trusted_context, MAX_TRUSTED_CONTEXT_BYTES_V0)?;
        linux_path::reject_duplicate_inodes(&[&raw, &receipt, &context])?;
        let authority = InputAuthorityReceiptV0::from_json_slice(&receipt.bytes)?;
        let trusted = TrustedAdaptationContextV0::from_json_slice(&context.bytes)?;
        match output_type {
            CodexExecOutputTypeV0::Private => {
                let adapted = adapt_codex_exec_owned_v0(
                    std::mem::take(&mut *raw.bytes),
                    &authority,
                    &trusted,
                )?;
                let bytes = adapted.to_private_bundle()?.to_json_line()?;
                if bytes.len() > MAX_ADAPTER_BUNDLE_BYTES_V0 {
                    return Err(AdapterErrorV0::from_code(AdapterErrorCodeV0::InputTooLarge));
                }
                let committed = linux_output::publish(output, &bytes, &[&raw, &receipt, &context])?;
                drop(committed);
            }
            CodexExecOutputTypeV0::ShareableSanitized => {
                let sidecar_output = private_lineage_output.ok_or_else(|| {
                    AdapterErrorV0::from_code(AdapterErrorCodeV0::PublicShareabilityDenied)
                })?;
                let transaction = sanitize_capture_v0(&raw.bytes, &authority, &trusted)?;
                let (sidecar, bundle) = transaction.into_publication_pair()?;
                let sidecar_bytes = sidecar.into_bytes();
                if sidecar_bytes.len() > MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0 {
                    return Err(AdapterErrorV0::from_code(AdapterErrorCodeV0::InputTooLarge));
                }
                let public_bytes = bundle.to_json_line()?;
                if public_bytes.len() > MAX_ADAPTER_BUNDLE_BYTES_V0 {
                    return Err(AdapterErrorV0::from_code(AdapterErrorCodeV0::InputTooLarge));
                }
                let (sidecar, public) = linux_output::publish_pair(
                    sidecar_output,
                    &sidecar_bytes,
                    output,
                    &public_bytes,
                    &[&raw, &receipt, &context],
                    || validate_semantic_pair(&sidecar_bytes, &public_bytes),
                )?;
                drop(public);
                drop(sidecar);
            }
        }
        drop(context);
        drop(receipt);
        drop(raw);
        Ok(())
    }
}

fn validate_semantic_pair(sidecar_bytes: &[u8], public_bytes: &[u8]) -> Result<(), AdapterErrorV0> {
    let inspected = InspectedShareableSanitizedBundleV0::from_json_slice(public_bytes)?;
    OwnerPrivateLineageSidecarV0::from_binary_slice(sidecar_bytes)?
        .revalidate_public_bundle(inspected)?
        .validate()?;
    Ok(())
}
