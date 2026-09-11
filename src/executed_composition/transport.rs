//! Reuses v0 typed authority and replay. One raw host experiment record is
//! bound as an observation; v0 event kind itself carries no action semantics.
use super::{Knowledge, Report, Run, check, report, suite};
use crate::trajectory::{
    DeclaredTrajectoryValidationContextV0, InspectedTrajectoryReplayCandidateV0,
    ReplayAuthoritySigningKeyV0, ReplayAuthorityTrustPolicyV0, TrajectoryTraceV0,
    UnverifiedReplayAuthorityReceiptV0, artifact_digest_v0,
    issue_trajectory_replay_authority_receipt_v0, raw_capture_seal_v0, raw_record_digest_v0,
    source_locator_digest_v0, trajectory_replay_candidate_v0, trajectory_schema_binding_v0,
    verify_replay_authority_receipt_v0, verify_trajectory_replay_v0,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{fs, io::Read, path::Path};

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SignedRun {
    pub run: Run,
    pub replay: Value,
    pub receipt: Value,
}

/// Strict external boundary, before any untrusted Value canonicalization.
pub fn parse_bundle(bytes: &[u8]) -> Result<Vec<SignedRun>, String> {
    if bytes.len() as u64 > super::MAX_BYTES {
        return Err("input exceeds 1 MiB".into());
    }
    crate::trajectory::preflight_executed_artifact(bytes)?;
    let signed: Vec<SignedRun> = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
    if signed.is_empty() || signed.len() > 32 {
        return Err("expected 1..32 signed runs".into());
    }
    Ok(signed)
}

fn line(value: &impl Serialize) -> Vec<u8> {
    let mut bytes = serde_json::to_vec(value).expect("serializable finite artifact");
    bytes.push(b'\n');
    bytes
}
fn envelope(
    run: &Run,
) -> Result<
    (
        TrajectoryTraceV0,
        DeclaredTrajectoryValidationContextV0,
        Vec<u8>,
    ),
    String,
> {
    let raw = line(run);
    let capture = raw_capture_seal_v0(&[raw.as_slice()]);
    let adapter = json!({"identity":"adapter.executed-composition.host","version":"1",
        "hash":artifact_digest_v0(b"controlled-release host record, canonical serde JSON, v1")});
    let policy = json!({"identity":"legitimacy.controlled-release.v1","version":"1",
        "hash":artifact_digest_v0(super::POLICY.as_bytes())});
    let evidence = json!({"classification":"cites-raw-range","locator":{
        "record_index":0,"byte_offset":0,"byte_length":raw.len(),"digest":source_locator_digest_v0(&raw)}});
    let cited = |value: Value| json!({"value":value,"evidence":evidence});
    let trace = json!({"schema":trajectory_schema_binding_v0(), "run_id":cited(json!(run.id)),
        "adapter":adapter,"policy":policy,"raw_capture":capture,"events":[{
            "event_id":cited(json!("host-experiment")),"sequence_index":cited(json!(0)),
            "kind":cited(json!("observation")),"source_item_id":null,
            "raw_record":{"record_index":0,"digest":raw_record_digest_v0(&raw)},"payload":{}}]});
    let context = json!({"declarations_format":"legitimacy.trajectory.validation-declarations",
        "declarations_version":"0","adapter":adapter,"policy":policy,"raw_capture":capture,
        "allowed_derivations":[]});
    Ok((
        TrajectoryTraceV0::from_json_slice(&line(&trace)).map_err(|e| e.to_string())?,
        DeclaredTrajectoryValidationContextV0::from_json_slice(&line(&context))
            .map_err(|e| e.to_string())?,
        raw,
    ))
}
fn authenticate(signed: &SignedRun, trust: &[u8]) -> Result<(), String> {
    let (trace, context, raw) = envelope(&signed.run)?;
    let records = [raw.as_slice()];
    let validated = trace
        .validate(&records, context.declarations())
        .map_err(|e| e.to_string())?;
    let candidate = InspectedTrajectoryReplayCandidateV0::from_json_slice(&line(&signed.replay))
        .map_err(|e| e.to_string())?;
    let receipt = UnverifiedReplayAuthorityReceiptV0::from_json_slice(&line(&signed.receipt))
        .map_err(|e| e.to_string())?;
    let policy = ReplayAuthorityTrustPolicyV0::from_json_slice(trust).map_err(|e| e.to_string())?;
    let verified =
        verify_replay_authority_receipt_v0(receipt, &policy).map_err(|e| e.to_string())?;
    verify_trajectory_replay_v0(&validated, &candidate, &verified).map_err(|e| e.to_string())?;
    Ok(())
}
pub fn check_signed(signed: &SignedRun, trust: &[u8]) -> Report {
    match authenticate(signed, trust) {
        Ok(()) => {
            let mut r = check(&signed.run);
            r.capture_authenticated = true;
            r
        }
        Err(_) => report(
            &signed.run,
            Knowledge::Invalid,
            "signed replay authentication/binding failed",
        ),
    }
}

/// Maintainer capture path. Generates one ephemeral key, retains only the public
/// trust policy, and uses the existing receipt issuer. Readers need no key.
pub fn record_suite(output: &Path) -> Result<(), String> {
    if output.exists() {
        return Err("capture output must be a new directory".into());
    }
    let mut seed = [0u8; 32];
    fs::File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut seed))
        .map_err(|e| e.to_string())?;
    let key = ReplayAuthoritySigningKeyV0::from_bytes(&seed).map_err(|e| e.to_string())?;
    use zeroize::Zeroize;
    seed.zeroize();
    let trust = json!({"trust_policy_format":"legitimacy.trajectory.replay-authority-trust-policy",
        "trust_policy_version":"0","issuer":"controlled-release-host","algorithm":"ed25519",
        "key_id":"ephemeral-capture-key","accepted_authority_epoch":1,"verification_key":key.verification_key_text()});
    let mut signed = vec![];
    for run in suite() {
        let (trace, context, raw) = envelope(&run)?;
        let records = [raw.as_slice()];
        let validated = trace
            .validate(&records, context.declarations())
            .map_err(|e| e.to_string())?;
        let replay = trajectory_replay_candidate_v0(&validated);
        let receipt = issue_trajectory_replay_authority_receipt_v0(
            &validated,
            &key,
            "controlled-release-host",
            "ephemeral-capture-key",
            1,
        )
        .map_err(|e| e.to_string())?;
        signed.push(SignedRun {
            run,
            replay: serde_json::from_slice(&replay.to_json_line().map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?,
            receipt: serde_json::from_slice(&receipt.to_json_line().map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?,
        });
    }
    let reports: Vec<_> = signed
        .iter()
        .map(|s| check_signed(s, &line(&trust)))
        .collect();
    if reports
        .iter()
        .any(|r| !r.capture_authenticated || r.knowledge == Knowledge::Invalid)
    {
        return Err("self-verification of fresh host capture failed".into());
    }
    fs::create_dir(output).map_err(|e| e.to_string())?;
    for (name, bytes) in [
        ("bundle.json", line(&signed)),
        ("trust-policy.json", line(&trust)),
        ("reports.json", line(&reports)),
    ] {
        fs::write(output.join(name), bytes).map_err(|e| e.to_string())?;
    }
    Ok(())
}
