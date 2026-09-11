use legitimacy::trajectory::{
    MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0,
    MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0, MAX_TRAJECTORY_REPLAY_BYTES_V0,
};
use legitimacy::{
    AgentActionEventV0, ArtifactBindingV0, DeclaredTrajectoryValidationContextV0, EvidenceV0,
    EvidencedV0, ExactRawRecordSetV0, InspectedTrajectoryReplayCandidateV0, NormalizedEventKindV0,
    RawRecordReferenceV0, ReplayAuthorityErrorCodeV0, ReplayAuthoritySigningKeyV0,
    ReplayAuthorityTrustPolicyV0, ReplayErrorCodeV0, SourceLocatorV0, TrajectoryTraceV0,
    TrajectoryValidationContextV0, UnverifiedReplayAuthorityReceiptV0, ValidatedTrajectoryTraceV0,
    VerifiedReplayAuthorityReceiptV0, artifact_digest_v0,
    issue_trajectory_replay_authority_receipt_v0, raw_capture_seal_v0, raw_record_digest_v0,
    source_locator_digest_v0, trajectory_replay_candidate_v0, trajectory_schema_binding_v0,
    verify_replay_authority_receipt_v0, verify_trajectory_replay_v0,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const RECORD_ZERO: &[u8] = br#"{"event":"first"}"#;
const RECORD_ONE: &[u8] = br#"{"event":"second"}"#;
const RECORD_TWO: &[u8] = br#"{"event":"third"}"#;
const AUTHORITY_KEY: [u8; 32] = [0x42; 32];
const PRODUCER_KEY: [u8; 32] = [0x24; 32];
const AUTHORITY_ISSUER: &str = "trajectory.replay.test-authority";
const AUTHORITY_KEY_ID: &str = "trajectory-replay-test-key";
const AUTHORITY_EPOCH: u64 = 7;
static NEXT_REFERENCE_DIRECTORY: AtomicU64 = AtomicU64::new(0);

#[test]
fn one_and_multiple_event_candidates_have_contiguous_links() {
    for raw in [vec![RECORD_ZERO], vec![RECORD_ZERO, RECORD_ONE]] {
        let (trace, declarations) = fixture(&raw, None);
        let validated = trace.validate(&raw, &declarations).unwrap();
        let replay = trajectory_replay_candidate_v0(&validated);

        assert_eq!(replay.record_count(), raw.len() as u64);
        assert_eq!(replay.records().len(), raw.len());
        assert_eq!(replay.records()[0].previous_head(), replay.genesis_head());
        assert_eq!(
            replay.records().last().unwrap().resulting_head(),
            replay.final_head()
        );
        for pair in replay.records().windows(2) {
            assert_eq!(pair[0].resulting_head(), pair[1].previous_head());
        }

        let receipt = issue_receipt(&validated, &AUTHORITY_KEY);
        assert_eq!(receipt.authority_epoch(), AUTHORITY_EPOCH);
    }
}

#[test]
fn replay_hashes_are_pinned_to_the_shared_canonical_event_encoding() {
    let raw = vec![RECORD_ZERO, RECORD_ONE];
    let (trace, declarations) = fixture(&raw, None);
    let validated = trace.validate(&raw, &declarations).unwrap();
    let replay = trajectory_replay_candidate_v0(&validated);

    assert_eq!(replay.trajectory_digest(), validated.trajectory_digest());
    assert_eq!(
        replay.genesis_head(),
        "sha256:61f13bc37c78252701fc3b184402a046b44d467e77453105846acb091bf68f6b"
    );
    assert_eq!(
        replay.records()[0].canonical_event_digest(),
        "sha256:d75bed8ab891add485dff9f485d44a3dcd2dc16a65dbd0ce77751826c9b1cfe5"
    );
    assert_eq!(
        replay.final_head(),
        "sha256:01ce6302772d9e6d3d620aa61f378e872186e358f6ec388de695c66cc06c5454"
    );
}

#[test]
fn complete_canonical_and_replay_golden_bytes_are_pinned() {
    let trace = TrajectoryTraceV0::from_json_slice(include_bytes!(
        "fixtures/trajectory-replay-v0/trace.json"
    ))
    .unwrap();
    let raw = ExactRawRecordSetV0::from_json_slice(include_bytes!(
        "fixtures/trajectory-replay-v0/raw-records.json"
    ))
    .unwrap();
    let context = DeclaredTrajectoryValidationContextV0::from_json_slice(include_bytes!(
        "fixtures/trajectory-replay-v0/declared-context.json"
    ))
    .unwrap();
    let validated = trace
        .validate(&raw.record_slices(), context.declarations())
        .unwrap();
    let canonical = validated.canonical_bytes();
    let replay = trajectory_replay_candidate_v0(&validated)
        .to_json_line()
        .unwrap();

    assert_eq!(
        canonical,
        include_bytes!("fixtures/trajectory-replay-v0/canonical-trace.bin")
    );
    assert_eq!(
        replay,
        include_bytes!("fixtures/trajectory-replay-v0/replay.json")
    );
    assert_eq!(
        format!("{:x}", Sha256::digest(&canonical)),
        "245fb1d661b5a3a6831317407f04bfdf5b1f777adb28adcd9f6b27e51ed76850"
    );
    assert_eq!(
        format!("{:x}", Sha256::digest(&replay)),
        "54ef8ec5d3a49eaa0d1eee0066696d363ccb0b945937c05f69d3d17a01b519f8"
    );
}

#[test]
fn independent_reference_accepts_the_vector_and_rejects_a_changed_input() {
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/trajectory-replay-v0");
    let isolated = temporary_reference_directory();
    for entry in fs::read_dir(&source).unwrap() {
        let entry = entry.unwrap();
        assert!(entry.file_type().unwrap().is_file());
        fs::copy(entry.path(), isolated.join(entry.file_name())).unwrap();
    }

    let positive = run_reference(&isolated);
    assert_eq!(positive.status.code(), Some(0), "{positive:?}");
    assert_eq!(positive.stdout, b"trajectory replay reference vector: OK\n");
    assert!(positive.stderr.is_empty(), "{positive:?}");
    println!("independent reference positive: trajectory replay reference vector: OK");

    let trace_path = isolated.join("trace.json");
    let mut trace = fs::read(&trace_path).unwrap();
    let input = b"run-replay-1";
    let offsets = trace
        .windows(input.len())
        .enumerate()
        .filter_map(|(offset, value)| (value == input).then_some(offset))
        .collect::<Vec<_>>();
    assert_eq!(offsets.len(), 1);
    trace[offsets[0] + input.len() - 1] = b'2';
    fs::write(trace_path, trace).unwrap();

    let perturbed = run_reference(&isolated);
    assert!(!perturbed.status.success(), "{perturbed:?}");
    assert!(perturbed.stdout.is_empty(), "{perturbed:?}");
    println!("independent reference perturbation: rejected");

    fs::remove_dir_all(isolated).unwrap();
}

#[test]
fn length_framing_distinguishes_ambiguous_two_event_identifiers() {
    let raw = vec![RECORD_ZERO, RECORD_ONE];
    let (left_trace, left_declarations) = fixture(&raw, Some(&["a", "bc"]));
    let (right_trace, right_declarations) = fixture(&raw, Some(&["ab", "c"]));
    let left =
        trajectory_replay_candidate_v0(&left_trace.validate(&raw, &left_declarations).unwrap());
    let right =
        trajectory_replay_candidate_v0(&right_trace.validate(&raw, &right_declarations).unwrap());

    assert_ne!(left.trajectory_digest(), right.trajectory_digest());
    assert_ne!(left.genesis_head(), right.genesis_head());
    assert_ne!(left.final_head(), right.final_head());
}

#[test]
fn signed_authority_round_trip_mints_verified_output() {
    let raw = vec![RECORD_ZERO, RECORD_ONE];
    let (trace, declarations) = fixture(&raw, None);
    let validated = trace.validate(&raw, &declarations).unwrap();
    let replay = trajectory_replay_candidate_v0(&validated);
    let replay_bytes = replay.to_json_line().unwrap();
    assert_eq!(replay_bytes.last(), Some(&b'\n'));
    assert!(!replay_bytes[..replay_bytes.len() - 1].contains(&b'\n'));
    assert_eq!(replay.to_json_line().unwrap(), replay_bytes);

    let inspected = InspectedTrajectoryReplayCandidateV0::from_json_slice(&replay_bytes).unwrap();
    let receipt = issue_receipt(&validated, &AUTHORITY_KEY);
    let receipt_bytes = receipt.to_json_line().unwrap();
    assert_eq!(receipt_bytes.last(), Some(&b'\n'));
    assert_eq!(receipt.to_json_line().unwrap(), receipt_bytes);
    let authority = authorize(&receipt_bytes, &AUTHORITY_KEY);

    let verified = verify_trajectory_replay_v0(&validated, &inspected, &authority).unwrap();
    let verified_bytes = verified.to_json_line().unwrap();
    assert_eq!(verified_bytes.last(), Some(&b'\n'));
    assert_eq!(verified.replay().final_head(), replay.final_head());
}

#[test]
fn authority_receipt_binds_exact_trace_raw_context_and_recomputed_replay() {
    let raw = vec![RECORD_ZERO, RECORD_ONE];
    let (trace, declarations) = fixture(&raw, None);
    let validated = trace.validate(&raw, &declarations).unwrap();
    let receipt = issue_receipt(&validated, &AUTHORITY_KEY);
    let authority = authorize(&receipt.to_json_line().unwrap(), &AUTHORITY_KEY);

    let assert_recomputed_rejected =
        |changed: &ValidatedTrajectoryTraceV0<'_>, authority: &VerifiedReplayAuthorityReceiptV0| {
            let replay = trajectory_replay_candidate_v0(changed);
            let inspected = InspectedTrajectoryReplayCandidateV0::from_json_slice(
                &replay.to_json_line().unwrap(),
            )
            .unwrap();
            assert_eq!(
                verify_trajectory_replay_v0(changed, &inspected, authority)
                    .unwrap_err()
                    .code(),
                ReplayErrorCodeV0::AuthorityBindingMismatch
            );
        };

    let changed_raw = vec![RECORD_ZERO, RECORD_TWO];
    let (changed_raw_trace, changed_raw_context) = fixture(&changed_raw, None);
    let changed_raw_validated = changed_raw_trace
        .validate(&changed_raw, &changed_raw_context)
        .unwrap();
    assert_recomputed_rejected(&changed_raw_validated, &authority);

    let (mut changed_trace, changed_trace_context) = fixture(&raw, None);
    changed_trace.events[0].kind.value = Some(NormalizedEventKindV0::Message);
    let changed_trace_validated = changed_trace
        .validate(&raw, &changed_trace_context)
        .unwrap();
    assert_recomputed_rejected(&changed_trace_validated, &authority);

    let (mut changed_context_trace, mut changed_context) = fixture(&raw, None);
    let changed_policy = binding("policy.changed", "0", b"changed policy");
    changed_context_trace.policy = changed_policy.clone();
    changed_context.policy = changed_policy;
    let changed_context_validated = changed_context_trace
        .validate(&raw, &changed_context)
        .unwrap();
    assert_recomputed_rejected(&changed_context_validated, &authority);
}

#[test]
fn replay_candidate_mutation_matrix_is_rejected() {
    let raw = vec![RECORD_ZERO, RECORD_ONE, RECORD_TWO];
    let (trace, declarations) = fixture(&raw, None);
    let validated = trace.validate(&raw, &declarations).unwrap();
    let replay = trajectory_replay_candidate_v0(&validated);
    let candidate: Value = serde_json::from_slice(&replay.to_json_line().unwrap()).unwrap();
    let receipt = issue_receipt(&validated, &AUTHORITY_KEY);
    let authority = authorize(&receipt.to_json_line().unwrap(), &AUTHORITY_KEY);
    let replacement = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

    let mut attacks: Vec<(&str, Value)> = Vec::new();

    let mut mutated = candidate.clone();
    mutated["records"][0]["canonical_event_digest"] = json!(replacement);
    attacks.push(("canonical event digest", mutated));

    let mut mutated = candidate.clone();
    mutated["records"][0]["resulting_head"] = json!(replacement);
    mutated["records"][1]["previous_head"] = json!(replacement);
    attacks.push(("record head", mutated));

    let mut mutated = candidate.clone();
    mutated["records"][1]["previous_head"] = json!(replacement);
    attacks.push(("previous head", mutated));

    let mut mutated = candidate.clone();
    mutated["records"].as_array_mut().unwrap().swap(0, 1);
    attacks.push(("record reorder", mutated));

    let mut mutated = candidate.clone();
    let duplicate = mutated["records"][1].clone();
    mutated["records"]
        .as_array_mut()
        .unwrap()
        .insert(2, duplicate);
    attacks.push(("record duplication", mutated));

    let mut mutated = candidate.clone();
    mutated["records"].as_array_mut().unwrap().remove(1);
    mutated["record_count"] = json!(2);
    mutated["raw_capture"]["record_count"] = json!(2);
    mutated["records"][1]["sequence_index"] = json!(1);
    mutated["records"][1]["previous_head"] = mutated["records"][0]["resulting_head"].clone();
    attacks.push(("interior deletion", mutated));

    let mut mutated = candidate.clone();
    mutated["records"].as_array_mut().unwrap().pop();
    mutated["record_count"] = json!(2);
    mutated["raw_capture"]["record_count"] = json!(2);
    mutated["final_head"] = mutated["records"][1]["resulting_head"].clone();
    attacks.push(("tail deletion", mutated));

    let mut mutated = candidate.clone();
    mutated["record_count"] = json!(2);
    attacks.push(("record count", mutated));

    let mut mutated = candidate.clone();
    mutated["trajectory_digest"] = json!(replacement);
    attacks.push(("trajectory digest", mutated));

    let mut mutated = candidate.clone();
    mutated["genesis_head"] = json!(replacement);
    mutated["records"][0]["previous_head"] = json!(replacement);
    attacks.push(("genesis", mutated));

    let mut mutated = candidate.clone();
    mutated["final_head"] = json!(replacement);
    attacks.push(("final head", mutated));

    let mut mutated = candidate.clone();
    mutated["replay_format"] = json!("legitimacy.trajectory.replay.changed");
    attacks.push(("replay format", mutated));

    let mut mutated = candidate.clone();
    mutated["replay_version"] = json!("1");
    attacks.push(("replay version", mutated));

    for field in ["schema", "adapter", "policy"] {
        let mut mutated = candidate.clone();
        mutated[field]["identity"] = json!(format!(
            "{}.changed",
            mutated[field]["identity"].as_str().unwrap()
        ));
        attacks.push((field, mutated));
    }

    let mut mutated = candidate.clone();
    mutated["raw_capture"]["digest"] = json!(replacement);
    attacks.push(("raw capture", mutated));

    let mut mutated = candidate.clone();
    mutated["authority_receipt"] = serde_json::to_value(&receipt).unwrap();
    attacks.push(("embedded authority receipt", mutated));

    for (name, mutated) in attacks {
        let bytes = value_json_line(&mutated);
        if let Ok(inspected) = InspectedTrajectoryReplayCandidateV0::from_json_slice(&bytes) {
            assert!(
                verify_trajectory_replay_v0(&validated, &inspected, &authority).is_err(),
                "{name} mutation reached verification but was accepted"
            );
        }
    }
}

#[test]
fn receipt_requires_the_pinned_authority_and_complete_signed_tuple() {
    let raw = vec![RECORD_ZERO, RECORD_ONE];
    let (trace, declarations) = fixture(&raw, None);
    let validated = trace.validate(&raw, &declarations).unwrap();
    let receipt = issue_receipt(&validated, &AUTHORITY_KEY);
    let receipt_bytes = receipt.to_json_line().unwrap();
    let receipt_json: Value = serde_json::from_slice(&receipt_bytes).unwrap();
    let replacement = "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";

    let unsigned_anchor = value_json_line(&receipt_json["anchor"]);
    assert!(UnverifiedReplayAuthorityReceiptV0::from_json_slice(&unsigned_anchor).is_err());

    let producer_receipt = issue_receipt(&validated, &PRODUCER_KEY);
    assert_authority_rejected(
        &producer_receipt.to_json_line().unwrap(),
        &trust_policy(
            &AUTHORITY_KEY,
            AUTHORITY_ISSUER,
            AUTHORITY_KEY_ID,
            AUTHORITY_EPOCH,
        ),
    );

    for (name, policy) in [
        (
            "wrong key",
            trust_policy(
                &PRODUCER_KEY,
                AUTHORITY_ISSUER,
                AUTHORITY_KEY_ID,
                AUTHORITY_EPOCH,
            ),
        ),
        (
            "wrong issuer",
            trust_policy(
                &AUTHORITY_KEY,
                "trajectory.replay.other",
                AUTHORITY_KEY_ID,
                AUTHORITY_EPOCH,
            ),
        ),
        (
            "wrong key ID",
            trust_policy(
                &AUTHORITY_KEY,
                AUTHORITY_ISSUER,
                "other-key",
                AUTHORITY_EPOCH,
            ),
        ),
        (
            "stale epoch",
            trust_policy(
                &AUTHORITY_KEY,
                AUTHORITY_ISSUER,
                AUTHORITY_KEY_ID,
                AUTHORITY_EPOCH - 1,
            ),
        ),
        (
            "future epoch",
            trust_policy(
                &AUTHORITY_KEY,
                AUTHORITY_ISSUER,
                AUTHORITY_KEY_ID,
                AUTHORITY_EPOCH + 1,
            ),
        ),
    ] {
        let unverified =
            UnverifiedReplayAuthorityReceiptV0::from_json_slice(&receipt_bytes).unwrap();
        let policy = ReplayAuthorityTrustPolicyV0::from_json_slice(&policy).unwrap();
        assert_eq!(
            verify_replay_authority_receipt_v0(unverified, &policy)
                .unwrap_err()
                .code(),
            ReplayAuthorityErrorCodeV0::AuthorityRejected,
            "{name}"
        );
    }

    let mut wrong_algorithm = serde_json::from_slice::<Value>(&trust_policy(
        &AUTHORITY_KEY,
        AUTHORITY_ISSUER,
        AUTHORITY_KEY_ID,
        AUTHORITY_EPOCH,
    ))
    .unwrap();
    wrong_algorithm["algorithm"] = json!("producer-selected");
    assert_eq!(
        ReplayAuthorityTrustPolicyV0::from_json_slice(&value_json_line(&wrong_algorithm))
            .unwrap_err()
            .code(),
        ReplayAuthorityErrorCodeV0::UnsupportedFormat
    );

    let mut attacks = Vec::new();
    for (field, value) in [
        ("issuer", json!("trajectory.replay.other")),
        ("key_id", json!("other-key")),
        ("authority_epoch", json!(AUTHORITY_EPOCH + 1)),
    ] {
        let mut mutated = receipt_json.clone();
        mutated[field] = value;
        attacks.push((field, mutated));
    }
    for field in ["schema", "adapter", "policy"] {
        let mut mutated = receipt_json.clone();
        mutated["anchor"][field]["hash"] = json!(replacement);
        attacks.push((field, mutated));
    }
    for field in ["trajectory_digest", "genesis_head", "expected_final_head"] {
        let mut mutated = receipt_json.clone();
        mutated["anchor"][field] = json!(replacement);
        attacks.push((field, mutated));
    }
    let mut mutated = receipt_json.clone();
    mutated["anchor"]["raw_capture"]["digest"] = json!(replacement);
    attacks.push(("raw capture", mutated));
    let mut mutated = receipt_json.clone();
    mutated["anchor"]["record_count"] = json!(1);
    mutated["anchor"]["raw_capture"]["record_count"] = json!(1);
    attacks.push(("record count", mutated));
    let mut mutated = receipt_json.clone();
    let signature = mutated["signature"].as_str().unwrap();
    let replacement_tail = if signature.ends_with('0') { "1" } else { "0" };
    mutated["signature"] = json!(format!(
        "{}{replacement_tail}",
        &signature[..signature.len() - 1]
    ));
    attacks.push(("signature", mutated));

    for (_name, mutated) in attacks {
        assert_authority_rejected(
            &value_json_line(&mutated),
            &trust_policy(
                &AUTHORITY_KEY,
                AUTHORITY_ISSUER,
                AUTHORITY_KEY_ID,
                AUTHORITY_EPOCH,
            ),
        );
    }

    for field in ["receipt_format", "receipt_version"] {
        let mut mutated = receipt_json.clone();
        mutated[field] = json!("changed");
        assert_eq!(
            UnverifiedReplayAuthorityReceiptV0::from_json_slice(&value_json_line(&mutated))
                .unwrap_err()
                .code(),
            ReplayAuthorityErrorCodeV0::UnsupportedFormat,
            "{field}"
        );
    }

    let mut wrong_algorithm_receipt = receipt_json;
    wrong_algorithm_receipt["algorithm"] = json!("producer-selected");
    assert_eq!(
        UnverifiedReplayAuthorityReceiptV0::from_json_slice(&value_json_line(
            &wrong_algorithm_receipt,
        ))
        .unwrap_err()
        .code(),
        ReplayAuthorityErrorCodeV0::UnsupportedFormat
    );
}

#[test]
fn strict_wire_rejects_malformed_duplicate_unknown_and_oversized_inputs() {
    let raw = vec![RECORD_ZERO];
    let (trace, declarations) = fixture(&raw, None);
    let validated = trace.validate(&raw, &declarations).unwrap();
    let replay = trajectory_replay_candidate_v0(&validated);
    let replay_bytes = replay.to_json_line().unwrap();
    let replay_text = std::str::from_utf8(&replay_bytes).unwrap();
    let duplicate = replay_text.replacen(
        "{\"replay_format\":",
        "{\"replay_format\":\"duplicate\",\"replay_format\":",
        1,
    );
    assert_eq!(
        InspectedTrajectoryReplayCandidateV0::from_json_slice(duplicate.as_bytes())
            .unwrap_err()
            .code(),
        ReplayErrorCodeV0::JsonSyntax
    );

    let mut unknown: Value = serde_json::from_slice(&replay_bytes).unwrap();
    unknown["unexpected"] = json!(true);
    assert_eq!(
        InspectedTrajectoryReplayCandidateV0::from_json_slice(&value_json_line(&unknown))
            .unwrap_err()
            .code(),
        ReplayErrorCodeV0::JsonShape
    );
    assert_eq!(
        InspectedTrajectoryReplayCandidateV0::from_json_slice(b"{}")
            .unwrap_err()
            .code(),
        ReplayErrorCodeV0::JsonFraming
    );

    let oversized_replay = vec![b' '; MAX_TRAJECTORY_REPLAY_BYTES_V0 + 1];
    assert_eq!(
        InspectedTrajectoryReplayCandidateV0::from_json_slice(&oversized_replay)
            .unwrap_err()
            .code(),
        ReplayErrorCodeV0::InputTooLarge
    );
    let oversized_receipt = vec![b' '; MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0 + 1];
    assert_eq!(
        UnverifiedReplayAuthorityReceiptV0::from_json_slice(&oversized_receipt)
            .unwrap_err()
            .code(),
        ReplayAuthorityErrorCodeV0::InputTooLarge
    );

    let receipt_bytes = issue_receipt(&validated, &AUTHORITY_KEY)
        .to_json_line()
        .unwrap();
    let receipt_text = std::str::from_utf8(&receipt_bytes).unwrap();
    let duplicate_receipt = receipt_text.replacen(
        "{\"receipt_format\":",
        "{\"receipt_format\":\"duplicate\",\"receipt_format\":",
        1,
    );
    assert_eq!(
        UnverifiedReplayAuthorityReceiptV0::from_json_slice(duplicate_receipt.as_bytes())
            .unwrap_err()
            .code(),
        ReplayAuthorityErrorCodeV0::JsonSyntax
    );
    let mut unknown_receipt: Value = serde_json::from_slice(&receipt_bytes).unwrap();
    unknown_receipt["unexpected"] = json!(true);
    assert_eq!(
        UnverifiedReplayAuthorityReceiptV0::from_json_slice(&value_json_line(&unknown_receipt))
            .unwrap_err()
            .code(),
        ReplayAuthorityErrorCodeV0::JsonShape
    );

    let oversized_policy = vec![b' '; MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0 + 1];
    assert_eq!(
        ReplayAuthorityTrustPolicyV0::from_json_slice(&oversized_policy)
            .unwrap_err()
            .code(),
        ReplayAuthorityErrorCodeV0::InputTooLarge
    );
}

#[test]
fn vendor_neutral_validation_inputs_preserve_exact_records_and_reject_ambiguity() {
    let trace = TrajectoryTraceV0::from_json_slice(include_bytes!(
        "fixtures/trajectory-replay-v0/trace.json"
    ))
    .unwrap();
    let raw = ExactRawRecordSetV0::from_json_slice(include_bytes!(
        "fixtures/trajectory-replay-v0/raw-records.json"
    ))
    .unwrap();
    let context = DeclaredTrajectoryValidationContextV0::from_json_slice(include_bytes!(
        "fixtures/trajectory-replay-v0/declared-context.json"
    ))
    .unwrap();
    trace
        .validate(&raw.record_slices(), context.declarations())
        .unwrap();

    let duplicate = br#"{"record_set_format":"legitimacy.trajectory.exact-raw-record-set","record_set_format":"duplicate","record_set_version":"0","records":["{}"]}"#;
    assert_eq!(
        ExactRawRecordSetV0::from_json_slice(duplicate)
            .unwrap_err()
            .code(),
        ReplayErrorCodeV0::JsonSyntax
    );
    let unknown = br#"{"record_set_format":"legitimacy.trajectory.exact-raw-record-set","record_set_version":"0","records":["{}"],"unexpected":true}"#;
    assert_eq!(
        ExactRawRecordSetV0::from_json_slice(unknown)
            .unwrap_err()
            .code(),
        ReplayErrorCodeV0::JsonShape
    );

    let context_bytes = include_bytes!("fixtures/trajectory-replay-v0/declared-context.json");
    let context_text = std::str::from_utf8(context_bytes).unwrap();
    let duplicate_context = context_text.replacen(
        "{\"declarations_format\":",
        "{\"declarations_format\":\"duplicate\",\"declarations_format\":",
        1,
    );
    assert_eq!(
        DeclaredTrajectoryValidationContextV0::from_json_slice(duplicate_context.as_bytes())
            .unwrap_err()
            .code(),
        ReplayErrorCodeV0::JsonSyntax
    );
    let unknown_context = context_text.replacen(
        "{\"declarations_format\":",
        "{\"unexpected\":true,\"declarations_format\":",
        1,
    );
    assert_eq!(
        DeclaredTrajectoryValidationContextV0::from_json_slice(unknown_context.as_bytes())
            .unwrap_err()
            .code(),
        ReplayErrorCodeV0::JsonShape
    );

    let changed_raw = br#"{"record_set_format":"legitimacy.trajectory.exact-raw-record-set","record_set_version":"0","records":["{\"event\": \"first\"}","{\"event\":\"second\"}"]}"#;
    let changed = ExactRawRecordSetV0::from_json_slice(changed_raw).unwrap();
    assert!(
        trace
            .validate(&changed.record_slices(), context.declarations())
            .is_err(),
        "record-internal whitespace is part of the exact sealed bytes"
    );
}

fn value_json_line(value: &Value) -> Vec<u8> {
    let mut bytes = serde_json::to_vec(value).unwrap();
    bytes.push(b'\n');
    bytes
}

fn issue_receipt(
    validated: &ValidatedTrajectoryTraceV0<'_>,
    key_bytes: &[u8; 32],
) -> legitimacy::SignedReplayAuthorityReceiptV0 {
    let key = ReplayAuthoritySigningKeyV0::from_bytes(key_bytes).unwrap();
    issue_trajectory_replay_authority_receipt_v0(
        validated,
        &key,
        AUTHORITY_ISSUER,
        AUTHORITY_KEY_ID,
        AUTHORITY_EPOCH,
    )
    .unwrap()
}

fn authorize(receipt: &[u8], key_bytes: &[u8; 32]) -> VerifiedReplayAuthorityReceiptV0 {
    let unverified = UnverifiedReplayAuthorityReceiptV0::from_json_slice(receipt).unwrap();
    let policy_bytes = trust_policy(
        key_bytes,
        AUTHORITY_ISSUER,
        AUTHORITY_KEY_ID,
        AUTHORITY_EPOCH,
    );
    let policy = ReplayAuthorityTrustPolicyV0::from_json_slice(&policy_bytes).unwrap();
    verify_replay_authority_receipt_v0(unverified, &policy).unwrap()
}

fn trust_policy(
    key_bytes: &[u8; 32],
    issuer: &str,
    key_id: &str,
    accepted_authority_epoch: u64,
) -> Vec<u8> {
    let key = ReplayAuthoritySigningKeyV0::from_bytes(key_bytes).unwrap();
    value_json_line(&json!({
        "trust_policy_format": "legitimacy.trajectory.replay-authority-trust-policy",
        "trust_policy_version": "0",
        "issuer": issuer,
        "algorithm": "ed25519",
        "key_id": key_id,
        "accepted_authority_epoch": accepted_authority_epoch,
        "verification_key": key.verification_key_text(),
    }))
}

fn assert_authority_rejected(receipt: &[u8], policy: &[u8]) {
    let unverified = UnverifiedReplayAuthorityReceiptV0::from_json_slice(receipt).unwrap();
    let policy = ReplayAuthorityTrustPolicyV0::from_json_slice(policy).unwrap();
    assert_eq!(
        verify_replay_authority_receipt_v0(unverified, &policy)
            .unwrap_err()
            .code(),
        ReplayAuthorityErrorCodeV0::AuthorityRejected
    );
}

fn run_reference(directory: &Path) -> Output {
    Command::new("python3")
        .arg(directory.join("reference.py"))
        .output()
        .unwrap()
}

fn temporary_reference_directory() -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "legitimacy-trajectory-reference-{}-{}",
        std::process::id(),
        NEXT_REFERENCE_DIRECTORY.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    directory
}

fn fixture(
    raw: &[&[u8]],
    event_ids: Option<&[&str]>,
) -> (TrajectoryTraceV0, TrajectoryValidationContextV0) {
    let adapter = binding("adapter.vendor-neutral", "0", b"vendor-neutral adapter");
    let policy = binding("policy.replay-fixture", "0", b"replay fixture policy");
    let raw_capture = raw_capture_seal_v0(raw);
    let events = raw
        .iter()
        .enumerate()
        .map(|(index, record)| {
            let locator = SourceLocatorV0 {
                record_index: index as u64,
                byte_offset: 0,
                byte_length: record.len() as u64,
                digest: source_locator_digest_v0(record),
            };
            let event_id =
                event_ids.map_or_else(|| format!("event-{index}"), |ids| ids[index].to_string());
            AgentActionEventV0 {
                event_id: cited(event_id, locator.clone()),
                sequence_index: cited(index as u64, locator.clone()),
                kind: cited(NormalizedEventKindV0::Observation, locator.clone()),
                source_item_id: None,
                raw_record: RawRecordReferenceV0 {
                    record_index: index as u64,
                    digest: raw_record_digest_v0(record),
                },
                payload: BTreeMap::new(),
            }
        })
        .collect();
    let trace = TrajectoryTraceV0 {
        schema: trajectory_schema_binding_v0(),
        run_id: cited(
            "run-replay-1".to_string(),
            SourceLocatorV0 {
                record_index: 0,
                byte_offset: 0,
                byte_length: raw[0].len() as u64,
                digest: source_locator_digest_v0(raw[0]),
            },
        ),
        adapter: adapter.clone(),
        policy: policy.clone(),
        raw_capture: raw_capture.clone(),
        events,
    };
    let declarations = TrajectoryValidationContextV0 {
        adapter,
        policy,
        raw_capture,
        allowed_derivations: BTreeSet::new(),
    };
    (trace, declarations)
}

fn binding(identity: &str, version: &str, bytes: &[u8]) -> ArtifactBindingV0 {
    ArtifactBindingV0 {
        identity: identity.to_string(),
        version: version.to_string(),
        hash: artifact_digest_v0(bytes),
    }
}

fn cited<T>(value: T, locator: SourceLocatorV0) -> EvidencedV0<T> {
    EvidencedV0 {
        value: Some(value),
        evidence: EvidenceV0::CitesRawRange { locator },
    }
}
