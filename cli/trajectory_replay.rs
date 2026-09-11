use crate::commands::TrajectoryValidationInputsV0;
use std::path::Path;

#[cfg(target_os = "linux")]
use crate::trajectory::{
    SnapshotV0, publish, read_snapshot, reject_duplicate_inodes, require_owner_private,
};
#[cfg(target_os = "linux")]
use legitimacy::trajectory::{
    MAX_EXACT_RAW_RECORD_SET_JSON_BYTES_V0,
    MAX_TRAJECTORY_DECLARED_VALIDATION_CONTEXT_JSON_BYTES_V0,
    MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0,
    MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0, MAX_TRAJECTORY_REPLAY_BYTES_V0,
};
#[cfg(target_os = "linux")]
use legitimacy::{
    DeclaredTrajectoryValidationContextV0, ExactRawRecordSetV0,
    InspectedTrajectoryReplayCandidateV0, ReplayAuthoritySigningKeyV0,
    ReplayAuthorityTrustPolicyV0, TrajectoryTraceV0, UnverifiedReplayAuthorityReceiptV0,
    issue_trajectory_replay_authority_receipt_v0, trajectory_replay_candidate_v0,
    verify_replay_authority_receipt_v0, verify_trajectory_replay_v0,
};
#[cfg(target_os = "linux")]
use zeroize::Zeroize;

pub(crate) fn canonicalize(
    inputs: &TrajectoryValidationInputsV0,
    output: &Path,
) -> Result<(), &'static str> {
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (inputs, output);
        Err("unsupported-platform")
    }
    #[cfg(target_os = "linux")]
    {
        with_validated(inputs, |validated, snapshots| {
            let bytes = validated.canonical_bytes();
            let committed = publish(output, &bytes, snapshots).map_err(adapter_code)?;
            drop(committed);
            Ok(())
        })
    }
}

pub(crate) fn build_candidate(
    inputs: &TrajectoryValidationInputsV0,
    output: &Path,
) -> Result<(), &'static str> {
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (inputs, output);
        Err("unsupported-platform")
    }
    #[cfg(target_os = "linux")]
    {
        with_validated(inputs, |validated, snapshots| {
            let bytes = trajectory_replay_candidate_v0(validated)
                .to_json_line()
                .map_err(replay_code)?;
            let committed = publish(output, &bytes, snapshots).map_err(adapter_code)?;
            drop(committed);
            Ok(())
        })
    }
}

pub(crate) fn issue_authority_receipt(
    inputs: &TrajectoryValidationInputsV0,
    private_key: &Path,
    issuer: &str,
    key_id: &str,
    authority_epoch: u64,
    output: &Path,
) -> Result<(), &'static str> {
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (inputs, private_key, issuer, key_id, authority_epoch, output);
        Err("unsupported-platform")
    }
    #[cfg(target_os = "linux")]
    {
        with_validated(inputs, |validated, snapshots| {
            let mut key_snapshot = read_snapshot(private_key, 32).map_err(adapter_code)?;
            require_owner_private(&key_snapshot).map_err(adapter_code)?;
            reject_duplicate_inodes(&[snapshots[0], snapshots[1], snapshots[2], &key_snapshot])
                .map_err(adapter_code)?;
            let signing_key = ReplayAuthoritySigningKeyV0::from_bytes(&key_snapshot.bytes);
            key_snapshot.bytes.zeroize();
            let signing_key = signing_key.map_err(authority_code)?;
            let receipt = issue_trajectory_replay_authority_receipt_v0(
                validated,
                &signing_key,
                issuer,
                key_id,
                authority_epoch,
            )
            .map_err(authority_code)?;
            drop(signing_key);
            let bytes = receipt.to_json_line().map_err(authority_code)?;
            let all_inputs = [snapshots[0], snapshots[1], snapshots[2], &key_snapshot];
            let committed = publish(output, &bytes, &all_inputs).map_err(adapter_code)?;
            drop(committed);
            Ok(())
        })
    }
}

pub(crate) fn verify(
    inputs: &TrajectoryValidationInputsV0,
    replay_path: &Path,
    authority_receipt_path: &Path,
    authority_trust_policy_path: &Path,
    output: &Path,
) -> Result<(), &'static str> {
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (
            inputs,
            replay_path,
            authority_receipt_path,
            authority_trust_policy_path,
            output,
        );
        Err("unsupported-platform")
    }
    #[cfg(target_os = "linux")]
    {
        let trace = read_snapshot(
            &inputs.trace,
            legitimacy::trajectory::MAX_TRACE_JSON_INPUT_BYTES_V0,
        )
        .map_err(adapter_code)?;
        let raw = read_snapshot(&inputs.raw_records, MAX_EXACT_RAW_RECORD_SET_JSON_BYTES_V0)
            .map_err(adapter_code)?;
        let context = read_snapshot(
            &inputs.declared_context,
            MAX_TRAJECTORY_DECLARED_VALIDATION_CONTEXT_JSON_BYTES_V0,
        )
        .map_err(adapter_code)?;
        let replay =
            read_snapshot(replay_path, MAX_TRAJECTORY_REPLAY_BYTES_V0).map_err(adapter_code)?;
        let receipt = read_snapshot(
            authority_receipt_path,
            MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0,
        )
        .map_err(adapter_code)?;
        let trust_policy = read_snapshot(
            authority_trust_policy_path,
            MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0,
        )
        .map_err(adapter_code)?;
        let snapshots = [&trace, &raw, &context, &replay, &receipt, &trust_policy];
        reject_duplicate_inodes(&snapshots).map_err(adapter_code)?;

        let trace_value =
            TrajectoryTraceV0::from_json_slice(&trace.bytes).map_err(|_| "validation")?;
        let raw_value = ExactRawRecordSetV0::from_json_slice(&raw.bytes).map_err(replay_code)?;
        let context_value = DeclaredTrajectoryValidationContextV0::from_json_slice(&context.bytes)
            .map_err(replay_code)?;
        let raw_slices = raw_value.record_slices();
        let validated = trace_value
            .validate(&raw_slices, context_value.declarations())
            .map_err(|_| "validation")?;
        let inspected = InspectedTrajectoryReplayCandidateV0::from_json_slice(&replay.bytes)
            .map_err(replay_code)?;
        let unverified = UnverifiedReplayAuthorityReceiptV0::from_json_slice(&receipt.bytes)
            .map_err(authority_code)?;
        let policy = ReplayAuthorityTrustPolicyV0::from_json_slice(&trust_policy.bytes)
            .map_err(authority_code)?;
        let authorized =
            verify_replay_authority_receipt_v0(unverified, &policy).map_err(authority_code)?;
        let bytes = verify_trajectory_replay_v0(&validated, &inspected, &authorized)
            .map_err(replay_code)?
            .to_json_line()
            .map_err(replay_code)?;
        let committed = publish(output, &bytes, &snapshots).map_err(adapter_code)?;
        drop(committed);
        Ok(())
    }
}

#[cfg(target_os = "linux")]
fn with_validated<T>(
    inputs: &TrajectoryValidationInputsV0,
    operation: impl FnOnce(
        &legitimacy::ValidatedTrajectoryTraceV0<'_>,
        &[&SnapshotV0],
    ) -> Result<T, &'static str>,
) -> Result<T, &'static str> {
    let trace = read_snapshot(
        &inputs.trace,
        legitimacy::trajectory::MAX_TRACE_JSON_INPUT_BYTES_V0,
    )
    .map_err(adapter_code)?;
    let raw = read_snapshot(&inputs.raw_records, MAX_EXACT_RAW_RECORD_SET_JSON_BYTES_V0)
        .map_err(adapter_code)?;
    let context = read_snapshot(
        &inputs.declared_context,
        MAX_TRAJECTORY_DECLARED_VALIDATION_CONTEXT_JSON_BYTES_V0,
    )
    .map_err(adapter_code)?;
    let snapshots = [&trace, &raw, &context];
    reject_duplicate_inodes(&snapshots).map_err(adapter_code)?;
    let trace_value = TrajectoryTraceV0::from_json_slice(&trace.bytes).map_err(|_| "validation")?;
    let raw_value = ExactRawRecordSetV0::from_json_slice(&raw.bytes).map_err(replay_code)?;
    let context_value = DeclaredTrajectoryValidationContextV0::from_json_slice(&context.bytes)
        .map_err(replay_code)?;
    let raw_slices = raw_value.record_slices();
    let validated = trace_value
        .validate(&raw_slices, context_value.declarations())
        .map_err(|_| "validation")?;
    operation(&validated, &snapshots)
}

#[cfg(target_os = "linux")]
fn adapter_code(error: legitimacy::trajectory::codex_exec_v0::AdapterErrorV0) -> &'static str {
    error.code().as_str()
}

#[cfg(target_os = "linux")]
fn replay_code(error: legitimacy::ReplayErrorV0) -> &'static str {
    error.code().as_str()
}

#[cfg(target_os = "linux")]
fn authority_code(error: legitimacy::ReplayAuthorityErrorV0) -> &'static str {
    error.code().as_str()
}
