use legitimacy::trajectory::{
    HISTORICAL_PROPERTY_ID_V0, HISTORICAL_PROPERTY_VERSION_V0,
    MAX_TRAJECTORY_COMPOSITION_POLICY_BYTES_V0, OCCURRENCE_ENCODER_ID_V0,
    OCCURRENCE_ENCODER_VERSION_V0, TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
    TRAJECTORY_COMPOSITION_POLICY_ID_V0, TRAJECTORY_COMPOSITION_POLICY_VERSION_V0,
};
use legitimacy::{
    BinaryPolicyDecisionV0, DeclaredTrajectoryValidationContextV0, ExactRawRecordSetV0,
    InspectedTrajectoryReplayCandidateV0, NormalizedEventKindV0, ReplayAuthoritySigningKeyV0,
    ReplayAuthorityTrustPolicyV0, TemporalCompositionKindV0, TrajectoryCompositionErrorCodeV0,
    TrajectoryCompositionResultV0, TrajectoryTraceV0, UnverifiedReplayAuthorityReceiptV0,
    ValidatedTrajectoryTraceV0, VerifiedTrajectoryReplayV0, artifact_digest_v0,
    evaluate_replay_bound_composition_v0, issue_trajectory_replay_authority_receipt_v0,
    trajectory_replay_candidate_v0, verify_replay_authority_receipt_v0,
    verify_trajectory_replay_v0,
};
use serde::Deserialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const AUTHORITY_KEY: [u8; 32] = [0x65; 32];
const AUTHORITY_ISSUER: &str = "trajectory.composition.fixture-authority";
const AUTHORITY_KEY_ID: &str = "trajectory-composition-fixture-key";
const AUTHORITY_EPOCH: u64 = 1;

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
struct GeneratedExpectedResults {
    policy_identity: String,
    policy_version: String,
    policy_artifact_digest: String,
    policy_source_sha256: String,
    occurrence_encoder_identity: String,
    occurrence_encoder_version: String,
    historical_property_identity: String,
    historical_property_version: String,
    fixtures: Vec<GeneratedFixtureResult>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
struct GeneratedFixtureResult {
    name: String,
    trajectory_digest: String,
    replay_final_head: String,
    trace_file_sha256: String,
    events: Vec<GeneratedEventResult>,
    all_singletons_permit: bool,
    first_bad_prefix: Option<GeneratedFirstBadPrefix>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
struct GeneratedEventResult {
    occurrence_index: u64,
    claimant_wire_id: String,
    strength_numerator: u64,
    strength_denominator: u64,
    event_id: String,
    kind: String,
    source_item_id: Option<String>,
    raw_record_digest: String,
    canonical_event_digest: String,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
struct GeneratedFirstBadPrefix {
    transition_index: u64,
    prefix_length: u64,
    denied_occurrence_index: u64,
}

#[test]
fn rust_evaluation_matches_the_generated_lean_fixture_export() {
    let expected: GeneratedExpectedResults = serde_json::from_slice(include_bytes!(
        "../fixtures/trajectory-composition-v0/generated/expected-results.json"
    ))
    .unwrap();
    assert_eq!(
        expected.policy_identity,
        TRAJECTORY_COMPOSITION_POLICY_ID_V0
    );
    assert_eq!(
        expected.policy_version,
        TRAJECTORY_COMPOSITION_POLICY_VERSION_V0
    );
    assert_eq!(
        expected.policy_artifact_digest,
        artifact_digest_v0(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0)
    );
    assert_eq!(
        expected.policy_source_sha256,
        lower_sha256(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0)
    );
    assert_eq!(
        expected.occurrence_encoder_identity,
        OCCURRENCE_ENCODER_ID_V0
    );
    assert_eq!(
        expected.occurrence_encoder_version,
        OCCURRENCE_ENCODER_VERSION_V0
    );
    assert_eq!(
        expected.historical_property_identity,
        HISTORICAL_PROPERTY_ID_V0
    );
    assert_eq!(
        expected.historical_property_version,
        HISTORICAL_PROPERTY_VERSION_V0
    );

    for fixture in &expected.fixtures {
        with_fixture(fixture.name.as_str(), |validated, verified| {
            let actual = evaluate_replay_bound_composition_v0(
                validated,
                verified,
                TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
            )
            .unwrap();
            assert_matches_generated(&actual, fixture);
        });
    }
}

#[test]
fn generated_red_fixture_pins_all_three_index_conventions() {
    let expected = generated_fixture("red");
    with_fixture("red", |validated, verified| {
        let actual = evaluate_replay_bound_composition_v0(
            validated,
            verified,
            TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
        )
        .unwrap();
        let actual_indices = (
            actual.temporal().transition_index(),
            actual.temporal().prefix_length(),
            actual.temporal().denied_occurrence_index(),
        );
        assert_eq!(actual_indices, (Some(2), Some(3), Some(0)));

        let pinned = expected.first_bad_prefix.unwrap();
        for mutated in [
            (
                pinned.transition_index + 1,
                pinned.prefix_length,
                pinned.denied_occurrence_index,
            ),
            (
                pinned.transition_index,
                pinned.prefix_length - 1,
                pinned.denied_occurrence_index,
            ),
            (
                pinned.transition_index,
                pinned.prefix_length,
                pinned.denied_occurrence_index + 1,
            ),
        ] {
            assert_ne!(
                actual_indices,
                (Some(mutated.0), Some(mutated.1), Some(mutated.2))
            );
        }
    });
}

#[test]
fn duplicate_source_items_do_not_alias_occurrence_claims() {
    for name in ["benign", "red"] {
        with_fixture(name, |validated, verified| {
            let actual = evaluate_replay_bound_composition_v0(
                validated,
                verified,
                TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
            )
            .unwrap();
            assert!(
                actual
                    .event_receipts()
                    .iter()
                    .all(|receipt| receipt.claim().source_item_id() == Some("repeated-source-item"))
            );
            for (index, receipt) in actual.event_receipts().iter().enumerate() {
                assert_eq!(receipt.claim().occurrence_index(), index as u64);
                assert_eq!(
                    receipt.claim().claimant_wire_id(),
                    format!("occurrence:{index}")
                );
            }
        });
    }
}

#[test]
fn exact_fixture_policy_mutations_reach_distinct_closed_failures() {
    with_fixture("benign", |validated, verified| {
        let mut byte_mutation = TRAJECTORY_COMPOSITION_POLICY_BYTES_V0.to_vec();
        byte_mutation[0] ^= 1;
        assert_eq!(
            evaluate_replay_bound_composition_v0(validated, verified, &byte_mutation)
                .unwrap_err()
                .code(),
            TrajectoryCompositionErrorCodeV0::PolicyDigestMismatch
        );
    });

    let whitespace_mutation = TRAJECTORY_COMPOSITION_POLICY_BYTES_V0
        .strip_suffix(b"\n")
        .unwrap();
    with_rebound_policy(whitespace_mutation, |validated, verified| {
        assert_eq!(
            evaluate_replay_bound_composition_v0(validated, verified, whitespace_mutation)
                .unwrap_err()
                .code(),
            TrajectoryCompositionErrorCodeV0::NonCanonicalPolicy
        );
    });

    let graph_mutation = String::from_utf8(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0.to_vec())
        .unwrap()
        .replace("percentile = 0.5", "percentile = 0.6")
        .into_bytes();
    with_rebound_policy(&graph_mutation, |validated, verified| {
        assert_eq!(
            evaluate_replay_bound_composition_v0(validated, verified, &graph_mutation)
                .unwrap_err()
                .code(),
            TrajectoryCompositionErrorCodeV0::UnsupportedPolicyProfile
        );
    });
}

#[test]
fn exact_policy_limit_succeeds_and_one_over_preempts_digest_and_encoding() {
    assert_eq!(
        TRAJECTORY_COMPOSITION_POLICY_BYTES_V0.len(),
        MAX_TRAJECTORY_COMPOSITION_POLICY_BYTES_V0
    );
    with_fixture("benign", |validated, verified| {
        evaluate_replay_bound_composition_v0(
            validated,
            verified,
            TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
        )
        .unwrap();

        let mut one_over = TRAJECTORY_COMPOSITION_POLICY_BYTES_V0.to_vec();
        one_over.push(0xff);
        let error =
            evaluate_replay_bound_composition_v0(validated, verified, &one_over).unwrap_err();
        assert_eq!(
            error.code(),
            TrajectoryCompositionErrorCodeV0::PolicyTooLarge
        );
        assert_eq!(error.to_string(), "policy-too-large");
    });
}

#[test]
fn generated_fixture_reordering_and_count_mutations_fail_validation() {
    let raw = ExactRawRecordSetV0::from_json_slice(include_bytes!(
        "../fixtures/trajectory-composition-v0/red/raw-records.json"
    ))
    .unwrap();
    let context = DeclaredTrajectoryValidationContextV0::from_json_slice(include_bytes!(
        "../fixtures/trajectory-composition-v0/red/declared-context.json"
    ))
    .unwrap();
    let trace_value: Value = serde_json::from_slice(include_bytes!(
        "../fixtures/trajectory-composition-v0/red/trace.json"
    ))
    .unwrap();

    let mut reordered = trace_value.clone();
    reordered["events"].as_array_mut().unwrap().swap(0, 1);
    let reordered = TrajectoryTraceV0::from_json_slice(&json_line(&reordered)).unwrap();
    let reorder_error = reordered
        .validate(&raw.record_slices(), context.declarations())
        .unwrap_err()
        .to_string();
    assert!(reorder_error.contains("sequence index"), "{reorder_error}");

    let mut short = trace_value;
    short["events"].as_array_mut().unwrap().pop();
    let short = TrajectoryTraceV0::from_json_slice(&json_line(&short)).unwrap();
    let count_error = short
        .validate(&raw.record_slices(), context.declarations())
        .unwrap_err()
        .to_string();
    assert!(
        count_error.contains("exactly one normalized event"),
        "{count_error}"
    );
}

#[test]
fn independently_verified_fixture_replay_cannot_be_paired_with_another_trace() {
    let benign_trace = TrajectoryTraceV0::from_json_slice(include_bytes!(
        "../fixtures/trajectory-composition-v0/benign/trace.json"
    ))
    .unwrap();
    let benign_raw = ExactRawRecordSetV0::from_json_slice(include_bytes!(
        "../fixtures/trajectory-composition-v0/benign/raw-records.json"
    ))
    .unwrap();
    let benign_context = DeclaredTrajectoryValidationContextV0::from_json_slice(include_bytes!(
        "../fixtures/trajectory-composition-v0/benign/declared-context.json"
    ))
    .unwrap();
    let benign_validated = benign_trace
        .validate(&benign_raw.record_slices(), benign_context.declarations())
        .unwrap();

    with_fixture("red", |_red_validated, red_verified| {
        assert_eq!(
            evaluate_replay_bound_composition_v0(
                &benign_validated,
                red_verified,
                TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
            )
            .unwrap_err()
            .code(),
            TrajectoryCompositionErrorCodeV0::ReplayPairMismatch
        );
    });
}

fn generated_fixture(name: &str) -> GeneratedFixtureResult {
    let expected: GeneratedExpectedResults = serde_json::from_slice(include_bytes!(
        "../fixtures/trajectory-composition-v0/generated/expected-results.json"
    ))
    .unwrap();
    expected
        .fixtures
        .into_iter()
        .find(|fixture| fixture.name == name)
        .unwrap()
}

fn with_fixture(
    name: &str,
    check: impl FnOnce(&ValidatedTrajectoryTraceV0<'_>, &VerifiedTrajectoryReplayV0),
) {
    let (trace_bytes, raw_bytes, context_bytes) = match name {
        "benign" => (
            include_bytes!("../fixtures/trajectory-composition-v0/benign/trace.json").as_slice(),
            include_bytes!("../fixtures/trajectory-composition-v0/benign/raw-records.json")
                .as_slice(),
            include_bytes!("../fixtures/trajectory-composition-v0/benign/declared-context.json")
                .as_slice(),
        ),
        "red" => (
            include_bytes!("../fixtures/trajectory-composition-v0/red/trace.json").as_slice(),
            include_bytes!("../fixtures/trajectory-composition-v0/red/raw-records.json").as_slice(),
            include_bytes!("../fixtures/trajectory-composition-v0/red/declared-context.json")
                .as_slice(),
        ),
        _ => panic!("unknown test fixture"),
    };
    let trace = TrajectoryTraceV0::from_json_slice(trace_bytes).unwrap();
    let raw = ExactRawRecordSetV0::from_json_slice(raw_bytes).unwrap();
    let context = DeclaredTrajectoryValidationContextV0::from_json_slice(context_bytes).unwrap();
    let validated = trace
        .validate(&raw.record_slices(), context.declarations())
        .unwrap();
    let verified = verified_replay(&validated);
    check(&validated, &verified);
}

fn with_rebound_policy(
    policy_bytes: &[u8],
    check: impl FnOnce(&ValidatedTrajectoryTraceV0<'_>, &VerifiedTrajectoryReplayV0),
) {
    let mut trace: Value = serde_json::from_slice(include_bytes!(
        "../fixtures/trajectory-composition-v0/benign/trace.json"
    ))
    .unwrap();
    let mut context: Value = serde_json::from_slice(include_bytes!(
        "../fixtures/trajectory-composition-v0/benign/declared-context.json"
    ))
    .unwrap();
    let digest = artifact_digest_v0(policy_bytes);
    trace["policy"]["hash"] = Value::String(digest.clone());
    context["policy"]["hash"] = Value::String(digest);
    let trace = TrajectoryTraceV0::from_json_slice(&json_line(&trace)).unwrap();
    let context =
        DeclaredTrajectoryValidationContextV0::from_json_slice(&json_line(&context)).unwrap();
    let raw = ExactRawRecordSetV0::from_json_slice(include_bytes!(
        "../fixtures/trajectory-composition-v0/benign/raw-records.json"
    ))
    .unwrap();
    let validated = trace
        .validate(&raw.record_slices(), context.declarations())
        .unwrap();
    let verified = verified_replay(&validated);
    check(&validated, &verified);
}

fn verified_replay(validated: &ValidatedTrajectoryTraceV0<'_>) -> VerifiedTrajectoryReplayV0 {
    let candidate = trajectory_replay_candidate_v0(validated);
    let inspected =
        InspectedTrajectoryReplayCandidateV0::from_json_slice(&candidate.to_json_line().unwrap())
            .unwrap();
    let signing_key = ReplayAuthoritySigningKeyV0::from_bytes(&AUTHORITY_KEY).unwrap();
    let signed = issue_trajectory_replay_authority_receipt_v0(
        validated,
        &signing_key,
        AUTHORITY_ISSUER,
        AUTHORITY_KEY_ID,
        AUTHORITY_EPOCH,
    )
    .unwrap();
    let unverified =
        UnverifiedReplayAuthorityReceiptV0::from_json_slice(&signed.to_json_line().unwrap())
            .unwrap();
    let trust_policy = ReplayAuthorityTrustPolicyV0::from_json_slice(&json_line(&json!({
        "trust_policy_format": "legitimacy.trajectory.replay-authority-trust-policy",
        "trust_policy_version": "0",
        "issuer": AUTHORITY_ISSUER,
        "algorithm": "ed25519",
        "key_id": AUTHORITY_KEY_ID,
        "accepted_authority_epoch": AUTHORITY_EPOCH,
        "verification_key": signing_key.verification_key_text(),
    })))
    .unwrap();
    let authorized = verify_replay_authority_receipt_v0(unverified, &trust_policy).unwrap();
    verify_trajectory_replay_v0(validated, &inspected, &authorized).unwrap()
}

fn assert_matches_generated(
    actual: &TrajectoryCompositionResultV0,
    expected: &GeneratedFixtureResult,
) {
    assert_eq!(actual.trajectory_digest(), expected.trajectory_digest);
    assert_eq!(actual.replay_final_head(), expected.replay_final_head);
    let trace_bytes = match expected.name.as_str() {
        "benign" => {
            include_bytes!("../fixtures/trajectory-composition-v0/benign/trace.json").as_slice()
        }
        "red" => include_bytes!("../fixtures/trajectory-composition-v0/red/trace.json").as_slice(),
        _ => panic!("unknown generated fixture"),
    };
    assert_eq!(lower_sha256(trace_bytes), expected.trace_file_sha256);
    assert_eq!(
        actual.policy().identity(),
        TRAJECTORY_COMPOSITION_POLICY_ID_V0
    );
    assert_eq!(
        actual.policy().version(),
        TRAJECTORY_COMPOSITION_POLICY_VERSION_V0
    );
    assert_eq!(
        actual.policy().canonical_bytes(),
        TRAJECTORY_COMPOSITION_POLICY_BYTES_V0
    );
    assert_eq!(
        actual.policy().artifact_digest(),
        artifact_digest_v0(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0)
    );
    assert_eq!(
        actual.policy().occurrence_encoder_identity(),
        OCCURRENCE_ENCODER_ID_V0
    );
    assert_eq!(
        actual.policy().occurrence_encoder_version(),
        OCCURRENCE_ENCODER_VERSION_V0
    );
    assert_eq!(
        actual.policy().historical_property_identity(),
        HISTORICAL_PROPERTY_ID_V0
    );
    assert_eq!(
        actual.policy().historical_property_version(),
        HISTORICAL_PROPERTY_VERSION_V0
    );
    assert_eq!(actual.event_receipts().len(), expected.events.len());
    for (actual_receipt, expected_event) in actual.event_receipts().iter().zip(&expected.events) {
        let claim = actual_receipt.claim();
        assert_eq!(claim.occurrence_index(), expected_event.occurrence_index);
        assert_eq!(claim.claimant_wire_id(), expected_event.claimant_wire_id);
        assert_eq!(
            claim.strength_numerator(),
            expected_event.strength_numerator
        );
        assert_eq!(
            claim.strength_denominator(),
            expected_event.strength_denominator
        );
        assert_eq!(claim.event_id(), expected_event.event_id);
        assert_eq!(kind_label(claim.kind()), expected_event.kind);
        assert_eq!(
            claim.source_item_id(),
            expected_event.source_item_id.as_deref()
        );
        assert_eq!(claim.raw_record_digest(), expected_event.raw_record_digest);
        assert_eq!(
            claim.canonical_event_digest(),
            expected_event.canonical_event_digest
        );
        assert_eq!(
            actual_receipt.singleton_decision(),
            BinaryPolicyDecisionV0::Permit
        );
    }
    assert_eq!(
        actual
            .event_receipts()
            .iter()
            .all(|receipt| receipt.singleton_decision() == BinaryPolicyDecisionV0::Permit),
        expected.all_singletons_permit
    );
    match expected.first_bad_prefix {
        None => {
            assert_eq!(
                actual.temporal().kind(),
                TemporalCompositionKindV0::AllSingletonsPermitAndSafe
            );
            assert_eq!(actual.temporal().transition_index(), None);
        }
        Some(failure) => {
            assert_eq!(
                actual.temporal().kind(),
                TemporalCompositionKindV0::AllSingletonsPermitAndEarliestViolation
            );
            assert_eq!(
                actual.temporal().transition_index(),
                Some(failure.transition_index)
            );
            assert_eq!(
                actual.temporal().prefix_length(),
                Some(failure.prefix_length)
            );
            assert_eq!(
                actual.temporal().denied_occurrence_index(),
                Some(failure.denied_occurrence_index)
            );
        }
    }
}

fn kind_label(kind: &NormalizedEventKindV0) -> &'static str {
    match kind {
        NormalizedEventKindV0::ActionRequest => "action-request",
        NormalizedEventKindV0::ActionResult => "action-result",
        NormalizedEventKindV0::Observation => "observation",
        NormalizedEventKindV0::Message => "message",
        NormalizedEventKindV0::Lifecycle => "lifecycle",
    }
}

fn json_line(value: &Value) -> Vec<u8> {
    let mut output = serde_json::to_vec(value).unwrap();
    output.push(b'\n');
    output
}

fn lower_sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
