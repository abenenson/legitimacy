use std::path::Path;

#[cfg(target_os = "linux")]
use crate::trajectory::{
    PublicationSpecV0, publish_directory_set, publish_set, read_snapshot, reject_duplicate_inodes,
};
#[cfg(target_os = "linux")]
use legitimacy::trajectory::codex_exec_v0::{
    InputAuthorityReceiptV0, InspectedShareableSanitizedBundleV0, OwnerPrivateLineageSidecarV0,
    TrustedAdaptationContextV0, adapt_codex_exec_owned_v0,
};
#[cfg(target_os = "linux")]
use legitimacy::trajectory::codex_exec_v0::{
    MAX_ADAPTER_BUNDLE_BYTES_V0, MAX_AUTHORITY_RECEIPT_BYTES_V0, MAX_CODEX_JSONL_BYTES_V0,
    MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0, MAX_TRUSTED_CONTEXT_BYTES_V0,
};
#[cfg(target_os = "linux")]
use legitimacy::trajectory::{
    MAX_TRAJECTORY_COMPOSITION_POLICY_BYTES_V0, MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0,
    MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0, MAX_TRAJECTORY_REPLAY_BYTES_V0,
};
#[cfg(target_os = "linux")]
use legitimacy::{
    InspectedTrajectoryReplayCandidateV0, ReplayAuthorityTrustPolicyV0,
    UnverifiedReplayAuthorityReceiptV0, evaluate_replay_bound_composition_v0,
    verify_replay_authority_receipt_v0, verify_trajectory_replay_v0,
};
use legitimacy::{
    ReplayAuthorityErrorV0, ReplayErrorV0, TrajectoryCompositionErrorV0,
    trajectory::codex_exec_v0::AdapterErrorV0,
};

pub(crate) struct CodexExecCompositionInputsV0<'a> {
    pub(crate) raw_stdout_jsonl: &'a Path,
    pub(crate) input_authority_receipt: Option<&'a Path>,
    pub(crate) trusted_adaptation_context: Option<&'a Path>,
    pub(crate) shareable_sanitized_bundle: Option<&'a Path>,
    pub(crate) private_lineage_sidecar: Option<&'a Path>,
    pub(crate) replay_candidate: &'a Path,
    pub(crate) replay_authority_receipt: &'a Path,
    pub(crate) replay_authority_trust_policy: &'a Path,
    pub(crate) composition_policy: &'a Path,
}

pub(crate) struct CodexExecCompositionOutputsV0<'a> {
    pub(crate) result: Option<&'a Path>,
    pub(crate) trace: Option<&'a Path>,
    pub(crate) canonical_trace: Option<&'a Path>,
    pub(crate) output_set: Option<&'a Path>,
}

struct MaterializedCompositionV0 {
    trace: Vec<u8>,
    canonical_trace: Vec<u8>,
    result: Vec<u8>,
}

pub(crate) fn evaluate(
    inputs: &CodexExecCompositionInputsV0<'_>,
    outputs: &CodexExecCompositionOutputsV0<'_>,
) -> Result<(), &'static str> {
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (inputs, outputs);
        Err("unsupported-platform")
    }
    #[cfg(target_os = "linux")]
    {
        let mut raw = read_snapshot(inputs.raw_stdout_jsonl, MAX_CODEX_JSONL_BYTES_V0)
            .map_err(adapter_code)?;
        let input_receipt = inputs
            .input_authority_receipt
            .map(|path| read_snapshot(path, MAX_AUTHORITY_RECEIPT_BYTES_V0))
            .transpose()
            .map_err(adapter_code)?;
        let adaptation_context = inputs
            .trusted_adaptation_context
            .map(|path| read_snapshot(path, MAX_TRUSTED_CONTEXT_BYTES_V0))
            .transpose()
            .map_err(adapter_code)?;
        let public_bundle = inputs
            .shareable_sanitized_bundle
            .map(|path| read_snapshot(path, MAX_ADAPTER_BUNDLE_BYTES_V0))
            .transpose()
            .map_err(adapter_code)?;
        let private_lineage = inputs
            .private_lineage_sidecar
            .map(|path| read_snapshot(path, MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0))
            .transpose()
            .map_err(adapter_code)?;
        let replay = read_snapshot(inputs.replay_candidate, MAX_TRAJECTORY_REPLAY_BYTES_V0)
            .map_err(adapter_code)?;
        let replay_receipt = read_snapshot(
            inputs.replay_authority_receipt,
            MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0,
        )
        .map_err(adapter_code)?;
        let replay_trust = read_snapshot(
            inputs.replay_authority_trust_policy,
            MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0,
        )
        .map_err(adapter_code)?;
        let policy = read_snapshot(
            inputs.composition_policy,
            MAX_TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
        )
        .map_err(adapter_code)?;
        let mut input_snapshots = vec![&raw, &replay, &replay_receipt, &replay_trust, &policy];
        input_snapshots.extend(input_receipt.iter());
        input_snapshots.extend(adaptation_context.iter());
        input_snapshots.extend(public_bundle.iter());
        input_snapshots.extend(private_lineage.iter());
        reject_duplicate_inodes(&input_snapshots).map_err(adapter_code)?;
        drop(input_snapshots);
        reject_output_aliases(outputs).map_err(adapter_code)?;

        let materialized = match (
            input_receipt.as_ref(),
            adaptation_context.as_ref(),
            public_bundle.as_ref(),
        ) {
            (Some(input_receipt), Some(adaptation_context), None) => {
                if private_lineage.is_some() {
                    return Err("unsupported-authority");
                }
                let authority = InputAuthorityReceiptV0::from_json_slice(&input_receipt.bytes)
                    .map_err(adapter_code)?;
                let context =
                    TrustedAdaptationContextV0::from_json_slice(&adaptation_context.bytes)
                        .map_err(adapter_code)?;
                let adapted = adapt_codex_exec_owned_v0(
                    std::mem::take(&mut *raw.bytes),
                    &authority,
                    &context,
                )
                .map_err(adapter_code)?;
                adapted
                    .with_validated(|validated| {
                        materialize(
                            validated,
                            &replay.bytes,
                            &replay_receipt.bytes,
                            &replay_trust.bytes,
                            &policy.bytes,
                        )
                    })
                    .map_err(adapter_code)??
            }
            (None, None, Some(public_bundle)) => {
                let inspected =
                    InspectedShareableSanitizedBundleV0::from_json_slice(&public_bundle.bytes)
                        .map_err(adapter_code)?;
                let revalidated = if let Some(private_lineage) = private_lineage.as_ref() {
                    let sidecar =
                        OwnerPrivateLineageSidecarV0::from_binary_slice(&private_lineage.bytes)
                            .map_err(adapter_code)?;
                    sidecar
                        .revalidate_public_bundle_for_jsonl(inspected, &raw.bytes)
                        .map_err(adapter_code)?
                } else {
                    inspected
                        .revalidate_public_projection(&raw.bytes)
                        .map_err(adapter_code)?
                };
                revalidated
                    .with_validated(|validated| {
                        materialize(
                            validated,
                            &replay.bytes,
                            &replay_receipt.bytes,
                            &replay_trust.bytes,
                            &policy.bytes,
                        )
                    })
                    .map_err(adapter_code)??
            }
            _ => return Err("unsupported-authority"),
        };
        let mut snapshots = vec![&raw, &replay, &replay_receipt, &replay_trust, &policy];
        snapshots.extend(input_receipt.iter());
        snapshots.extend(adaptation_context.iter());
        snapshots.extend(public_bundle.iter());
        snapshots.extend(private_lineage.iter());
        match (
            outputs.output_set,
            outputs.trace,
            outputs.canonical_trace,
            outputs.result,
        ) {
            (Some(output_set), None, None, None) => publish_directory_set(
                output_set,
                &[
                    ("trace.json", materialized.trace.as_slice()),
                    (
                        "canonical-trace.bin",
                        materialized.canonical_trace.as_slice(),
                    ),
                    ("composition-result.json", materialized.result.as_slice()),
                ],
                &snapshots,
                || Ok(()),
            )
            .map_err(adapter_code)?,
            (None, Some(trace), Some(canonical_trace), Some(result)) => publish_set(
                &[
                    PublicationSpecV0 {
                        output: trace,
                        bytes: &materialized.trace,
                    },
                    PublicationSpecV0 {
                        output: canonical_trace,
                        bytes: &materialized.canonical_trace,
                    },
                    PublicationSpecV0 {
                        output: result,
                        bytes: &materialized.result,
                    },
                ],
                &snapshots,
                || Ok(()),
            )
            .map_err(adapter_code)?,
            _ => return Err("unsafe-output-path"),
        }
        Ok(())
    }
}

#[cfg(target_os = "linux")]
fn materialize(
    validated: &legitimacy::ValidatedTrajectoryTraceV0<'_>,
    replay: &[u8],
    replay_receipt: &[u8],
    replay_trust: &[u8],
    policy: &[u8],
) -> Result<MaterializedCompositionV0, &'static str> {
    let inspected =
        InspectedTrajectoryReplayCandidateV0::from_json_slice(replay).map_err(replay_code)?;
    let unverified = UnverifiedReplayAuthorityReceiptV0::from_json_slice(replay_receipt)
        .map_err(authority_code)?;
    let trust_policy =
        ReplayAuthorityTrustPolicyV0::from_json_slice(replay_trust).map_err(authority_code)?;
    let authorized =
        verify_replay_authority_receipt_v0(unverified, &trust_policy).map_err(authority_code)?;
    let verified =
        verify_trajectory_replay_v0(validated, &inspected, &authorized).map_err(replay_code)?;
    let result = evaluate_replay_bound_composition_v0(validated, &verified, policy)
        .map_err(composition_code)?;
    Ok(MaterializedCompositionV0 {
        trace: validated.to_compact_json().map_err(|_| "validation")?,
        canonical_trace: validated.canonical_bytes(),
        result: result.to_json_line().map_err(composition_code)?,
    })
}

fn reject_output_aliases(
    outputs: &CodexExecCompositionOutputsV0<'_>,
) -> Result<(), AdapterErrorV0> {
    let mut paths = Vec::new();
    paths.extend(outputs.result);
    paths.extend(outputs.trace);
    paths.extend(outputs.canonical_trace);
    paths.extend(outputs.output_set);
    for (index, left) in paths.iter().enumerate() {
        if paths[index + 1..].contains(left) {
            return Err(AdapterErrorV0::from_code(
                legitimacy::trajectory::codex_exec_v0::AdapterErrorCodeV0::CrossOutputAlias,
            ));
        }
    }
    Ok(())
}

fn adapter_code(error: AdapterErrorV0) -> &'static str {
    error.code().as_str()
}

fn replay_code(error: ReplayErrorV0) -> &'static str {
    error.code().as_str()
}

fn authority_code(error: ReplayAuthorityErrorV0) -> &'static str {
    error.code().as_str()
}

fn composition_code(error: TrajectoryCompositionErrorV0) -> &'static str {
    error.code().as_str()
}
