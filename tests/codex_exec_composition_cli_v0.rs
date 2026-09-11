#![cfg(target_os = "linux")]

use legitimacy::trajectory::codex_exec_v0::{
    FixedSyntheticTestNonceV0, InputAuthorityReceiptV0, SyntheticFixtureReceiptV0,
    TrustedAdaptationContextV0, adapt_codex_exec_v0, codex_exec_fixture_spec_binding_v0,
    sanitize_capture_v0,
};
use legitimacy::trajectory::{
    TRAJECTORY_COMPOSITION_POLICY_BYTES_V0, TRAJECTORY_COMPOSITION_POLICY_ID_V0,
    TRAJECTORY_COMPOSITION_POLICY_VERSION_V0, TRAJECTORY_COMPOSITION_RESULT_FORMAT_V0,
};
use legitimacy::{
    ArtifactBindingV0, EvidenceV0, EvidencedV0, InspectedTrajectoryReplayCandidateV0,
    NormalizedEventKindV0, ReplayAuthoritySigningKeyV0, ReplayAuthorityTrustPolicyV0,
    TrajectoryTraceV0, TrajectoryValidationContextV0, UnverifiedReplayAuthorityReceiptV0,
    artifact_digest_v0, issue_trajectory_replay_authority_receipt_v0,
    trajectory_replay_candidate_v0, verify_replay_authority_receipt_v0,
    verify_trajectory_replay_v0,
};
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const RAW_CODEX_JSONL: &[u8] = concat!(
    "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000165\"}\n",
    "{\"type\":\"turn.started\"}\n",
    "{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":0,\"cached_input_tokens\":0,\"output_tokens\":0,\"reasoning_output_tokens\":0}}\n"
)
.as_bytes();
const AUTHORITY_KEY: [u8; 32] = [0x65; 32];
const OTHER_AUTHORITY_KEY: [u8; 32] = [0x35; 32];
const AUTHORITY_ISSUER: &str = "trajectory.composition.cli-authority";
const AUTHORITY_KEY_ID: &str = "trajectory-composition-cli-key";
const AUTHORITY_EPOCH: u64 = 1;
static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

#[test]
fn minimal_capture_emits_the_existing_canonical_result() {
    let fixture = Fixture::new();
    let result = fixture.command(&fixture.output).output().unwrap();
    assert_success(result);

    let emitted = fs::read(fixture.output.join("composition-result.json")).unwrap();
    assert!(
        !emitted.is_empty(),
        "the command must emit a result before inspection"
    );
    assert_eq!(emitted.last(), Some(&b'\n'));
    let parsed: Value = serde_json::from_slice(&emitted).unwrap();
    assert_eq!(
        parsed["result_format"],
        TRAJECTORY_COMPOSITION_RESULT_FORMAT_V0
    );
    let receipts = parsed["event_receipts"].as_array().unwrap();
    assert_eq!(receipts.len(), 3);
    assert!(
        receipts
            .iter()
            .all(|receipt| receipt["singleton_decision"] == "permit")
    );
    assert_eq!(
        parsed["temporal"]["classification"]["classification"],
        "all-singletons-permit-and-earliest-violation"
    );
    assert_eq!(parsed["temporal"]["classification"]["transition_index"], 2);
    assert_eq!(parsed["temporal"]["classification"]["prefix_length"], 3);
    assert_eq!(
        parsed["temporal"]["classification"]["denied_occurrence_index"],
        0
    );
    fixture.remove();
}

#[test]
fn public_projection_and_private_lineage_routes_materialize_the_same_derived_bytes() {
    let fixture = Fixture::new();
    let parent_authority = synthetic_authority();
    let parent_context = trusted_context(&parent_authority);
    let transaction =
        sanitize_capture_v0(RAW_CODEX_JSONL, &parent_authority, &parent_context).unwrap();
    let child = transaction.jsonl().to_vec();
    let signing_key = signing_key(&AUTHORITY_KEY);
    let (candidate, receipt) = transaction
        .adapted()
        .with_validated(|validated| {
            (
                trajectory_replay_candidate_v0(validated)
                    .to_json_line()
                    .unwrap(),
                issue_trajectory_replay_authority_receipt_v0(
                    validated,
                    &signing_key,
                    AUTHORITY_ISSUER,
                    AUTHORITY_KEY_ID,
                    AUTHORITY_EPOCH,
                )
                .unwrap()
                .to_json_line()
                .unwrap(),
            )
        })
        .unwrap();
    let (sidecar, bundle) = transaction.into_publication_pair().unwrap();
    let bundle = bundle.into_bytes();
    let sidecar = sidecar.into_bytes();
    let bundle_path = fixture.directory.join("shareable-bundle.json");
    let sidecar_path = fixture.directory.join("private-lineage.bin");
    fs::write(&fixture.raw, &child).unwrap();
    fs::write(&fixture.replay, candidate).unwrap();
    fs::write(&fixture.replay_receipt, receipt).unwrap();
    fs::write(&bundle_path, &bundle).unwrap();
    fs::write(&sidecar_path, &sidecar).unwrap();

    let public_result = fixture.directory.join("public-result");
    assert_success(
        public_projection_command(&fixture, &bundle_path, None, &public_result)
            .output()
            .unwrap(),
    );
    assert!(
        !fs::read(public_result.join("trace.json"))
            .unwrap()
            .is_empty()
    );
    assert!(
        !fs::read(public_result.join("canonical-trace.bin"))
            .unwrap()
            .is_empty()
    );
    let public_result_bytes = fs::read(public_result.join("composition-result.json")).unwrap();

    let private_result = fixture.directory.join("private-result.json");
    assert_success(
        public_projection_command(&fixture, &bundle_path, Some(&sidecar_path), &private_result)
            .output()
            .unwrap(),
    );
    assert_eq!(
        fs::read(private_result.join("composition-result.json")).unwrap(),
        public_result_bytes
    );

    let parsed: Value = serde_json::from_slice(&public_result_bytes).unwrap();
    let denied_event = parsed["temporal"]["classification"]["denied_event_id"]
        .as_str()
        .unwrap();
    assert_eq!(
        denied_event,
        parsed["event_receipts"][0]["claim"]["event_id"]
    );
    assert_ne!(denied_event, "caller-authored-event-id");
    assert_ne!(parsed["temporal"]["classification"]["transition_index"], 3);
    assert_ne!(parsed["temporal"]["classification"]["prefix_length"], 2);
    assert_ne!(
        parsed["temporal"]["classification"]["denied_occurrence_index"],
        1
    );

    let mut relabeled: Value = serde_json::from_slice(&bundle).unwrap();
    relabeled["evidence_class"] = Value::String("genuine-process-capture".to_string());
    let relabeled_path = fixture.directory.join("relabeled-bundle.json");
    fs::write(&relabeled_path, json_line(&relabeled)).unwrap();
    let relabeled_output = fixture.directory.join("relabeled-result.json");
    assert_failure(
        public_projection_command(&fixture, &relabeled_path, None, &relabeled_output)
            .output()
            .unwrap(),
        "bundle-mismatch",
    );

    type CoordinatedAttack = (&'static str, fn(&mut Value));

    let original: Value = serde_json::from_slice(&bundle).unwrap();
    let coordinated_attacks: [CoordinatedAttack; 3] = [
        ("origin-relabel", |value| {
            value["public_derived_receipt"]["asserted_origin_evidence_class"] =
                json!("genuine-process-capture");
            value["public_derived_receipt"]["asserted_parent_receipt"] =
                json!("asserted-parent-receipt-process-capture-capture-random");
        }),
        ("receipt-commitment", |value| {
            value["public_derived_receipt"]["derived_receipt_commitment"] = json!(zero_digest());
            value["public_transformation"]["derived_authority_commitment"] = json!(zero_digest());
        }),
        ("parent-commitment", |value| {
            value["public_parent_commitment"] = json!(zero_digest());
            value["public_derived_receipt"]["public_parent_commitment"] = json!(zero_digest());
            value["public_transformation"]["public_parent_commitment"] = json!(zero_digest());
        }),
    ];
    for (label, mutate) in coordinated_attacks {
        let mut value = original.clone();
        mutate(&mut value);
        let path = fixture.directory.join(format!("{label}-bundle.json"));
        let output = fixture.directory.join(format!("{label}-output"));
        fs::write(&path, json_line(&value)).unwrap();
        assert_failure(
            public_projection_command(&fixture, &path, None, &output)
                .output()
                .unwrap(),
            "json-shape",
        );
        assert!(!output.exists(), "{label}");
    }

    let mut mutated_child = child.clone();
    let position = mutated_child
        .windows(b"input_tokens\":0".len())
        .position(|window| window == b"input_tokens\":0")
        .unwrap()
        + b"input_tokens\":".len();
    mutated_child[position] = b'1';
    fs::write(&fixture.raw, mutated_child).unwrap();
    let child_output = fixture.directory.join("child-mutation-result.json");
    assert_failure(
        public_projection_command(&fixture, &bundle_path, None, &child_output)
            .output()
            .unwrap(),
        "receipt-mismatch",
    );
    fs::write(&fixture.raw, &child).unwrap();

    let mut mutated_sidecar = sidecar;
    mutated_sidecar[0] ^= 1;
    fs::write(&sidecar_path, mutated_sidecar).unwrap();
    let sidecar_output = fixture.directory.join("sidecar-mutation-result.json");
    assert_failure(
        public_projection_command(&fixture, &bundle_path, Some(&sidecar_path), &sidecar_output)
            .output()
            .unwrap(),
        "lineage-sidecar-shape",
    );
    fixture.remove();
}

#[test]
fn trusted_attacker_rehashed_normalized_trace_is_rejected() {
    let fixture = Fixture::new();
    let authority = synthetic_authority();
    let context = trusted_context(&authority);
    let adapted = adapt_codex_exec_v0(RAW_CODEX_JSONL, &authority, &context).unwrap();
    let mut attacker_trace = adapted.trace().clone();
    assert_ne!(
        attacker_trace.events[0].kind.value,
        Some(NormalizedEventKindV0::Observation)
    );
    attacker_trace.events[0].kind.value = Some(NormalizedEventKindV0::Observation);

    let records = raw_records();
    let declarations = TrajectoryValidationContextV0 {
        adapter: attacker_trace.adapter.clone(),
        policy: attacker_trace.policy.clone(),
        raw_capture: attacker_trace.raw_capture.clone(),
        allowed_derivations: derivation_rules(&attacker_trace),
    };
    let attacker_validated = attacker_trace.validate(&records, &declarations).unwrap();
    let attacker_candidate = trajectory_replay_candidate_v0(&attacker_validated);
    let signing_key = signing_key(&AUTHORITY_KEY);
    let attacker_receipt = issue_trajectory_replay_authority_receipt_v0(
        &attacker_validated,
        &signing_key,
        AUTHORITY_ISSUER,
        AUTHORITY_KEY_ID,
        AUTHORITY_EPOCH,
    )
    .unwrap();
    let candidate_bytes = attacker_candidate.to_json_line().unwrap();
    let receipt_bytes = attacker_receipt.to_json_line().unwrap();

    let inspected =
        InspectedTrajectoryReplayCandidateV0::from_json_slice(&candidate_bytes).unwrap();
    let unverified = UnverifiedReplayAuthorityReceiptV0::from_json_slice(&receipt_bytes).unwrap();
    let trust =
        ReplayAuthorityTrustPolicyV0::from_json_slice(&trust_policy_bytes(&AUTHORITY_KEY)).unwrap();
    let authorized = verify_replay_authority_receipt_v0(unverified, &trust).unwrap();
    verify_trajectory_replay_v0(&attacker_validated, &inspected, &authorized).unwrap();

    fs::write(&fixture.replay, candidate_bytes).unwrap();
    fs::write(&fixture.replay_receipt, receipt_bytes).unwrap();
    let rejected = fixture.command(&fixture.output).output().unwrap();
    assert_failure(rejected, "replay-candidate-mismatch");
    assert!(!fixture.output.exists());
    fixture.remove();
}

#[test]
fn rebound_policy_and_fully_resigned_replay_fail_at_exact_policy_closure() {
    let fixture = Fixture::new();
    let authority = synthetic_authority();
    let policy_text = String::from_utf8(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0.to_vec()).unwrap();
    assert_eq!(policy_text.matches("percentile = 0.5").count(), 1);
    let rebound_policy = policy_text
        .replacen("percentile = 0.5", "percentile = 0.6", 1)
        .into_bytes();
    let rebound_context = trusted_context_for_policy(&authority, &rebound_policy);
    let adapted = adapt_codex_exec_v0(RAW_CODEX_JSONL, &authority, &rebound_context).unwrap();
    let signing_key = signing_key(&AUTHORITY_KEY);
    let trust =
        ReplayAuthorityTrustPolicyV0::from_json_slice(&trust_policy_bytes(&AUTHORITY_KEY)).unwrap();
    let (candidate_bytes, receipt_bytes) = adapted
        .with_validated(|validated| {
            let candidate = trajectory_replay_candidate_v0(validated);
            let receipt = issue_trajectory_replay_authority_receipt_v0(
                validated,
                &signing_key,
                AUTHORITY_ISSUER,
                AUTHORITY_KEY_ID,
                AUTHORITY_EPOCH,
            )
            .unwrap();
            let candidate_bytes = candidate.to_json_line().unwrap();
            let receipt_bytes = receipt.to_json_line().unwrap();
            let inspected =
                InspectedTrajectoryReplayCandidateV0::from_json_slice(&candidate_bytes).unwrap();
            let unverified =
                UnverifiedReplayAuthorityReceiptV0::from_json_slice(&receipt_bytes).unwrap();
            let authorized = verify_replay_authority_receipt_v0(unverified, &trust).unwrap();
            verify_trajectory_replay_v0(validated, &inspected, &authorized).unwrap();
            (candidate_bytes, receipt_bytes)
        })
        .unwrap();

    fs::write(
        &fixture.adaptation_context,
        serde_json::to_vec(&rebound_context).unwrap(),
    )
    .unwrap();
    fs::write(&fixture.replay, candidate_bytes).unwrap();
    fs::write(&fixture.replay_receipt, receipt_bytes).unwrap();
    fs::write(&fixture.policy, rebound_policy).unwrap();
    assert_failure(
        fixture.command(&fixture.output).output().unwrap(),
        "unsupported-policy-profile",
    );
    assert!(!fixture.output.exists());
    fixture.remove();
}

#[test]
fn rejection_controls_never_publish_a_result() {
    let fixture = Fixture::new();

    let substituted_policy = fixture.directory.join("substituted-policy.toml");
    let mut policy_bytes = TRAJECTORY_COMPOSITION_POLICY_BYTES_V0.to_vec();
    policy_bytes[0] ^= 1;
    fs::write(&substituted_policy, policy_bytes).unwrap();
    let policy_output = fixture.directory.join("policy-result.json");
    let mut policy_command = fixture.command(&policy_output);
    replace_argument(
        &mut policy_command,
        "--composition-policy",
        &substituted_policy,
    );
    assert_failure(policy_command.output().unwrap(), "policy-digest-mismatch");
    assert!(!policy_output.exists());

    let wrong_trust = fixture.directory.join("wrong-trust.json");
    fs::write(&wrong_trust, trust_policy_bytes(&OTHER_AUTHORITY_KEY)).unwrap();
    let trust_output = fixture.directory.join("trust-result.json");
    let mut trust_command = fixture.command(&trust_output);
    replace_argument(
        &mut trust_command,
        "--replay-authority-trust-policy",
        &wrong_trust,
    );
    assert_failure(
        trust_command.output().unwrap(),
        "authority-receipt-rejected",
    );
    assert!(!trust_output.exists());

    let alias_output = fixture.directory.join("alias-result.json");
    let mut alias_command = fixture.command(&alias_output);
    replace_argument(
        &mut alias_command,
        "--replay-authority-trust-policy",
        &fixture.replay_receipt,
    );
    assert_failure(alias_command.output().unwrap(), "input-alias");
    assert!(!alias_output.exists());

    fs::write(&fixture.output, b"incumbent").unwrap();
    assert_failure(
        fixture.command(&fixture.output).output().unwrap(),
        "output-exists",
    );
    assert_eq!(fs::read(&fixture.output).unwrap(), b"incumbent");
    fixture.remove();
}

#[test]
fn legacy_three_path_failures_never_publish_a_partial_set() {
    let fixture = Fixture::new();
    let raw_before = fs::read(&fixture.raw).unwrap();
    for alias_position in 0..3 {
        let trace = fixture
            .directory
            .join(format!("alias-{alias_position}-trace"));
        let canonical = fixture
            .directory
            .join(format!("alias-{alias_position}-canonical"));
        let result = fixture
            .directory
            .join(format!("alias-{alias_position}-result"));
        let mut paths = [trace, canonical, result];
        paths[alias_position] = fixture.raw.clone();
        assert_failure(
            fixture
                .legacy_command(&paths[2], &paths[0], &paths[1])
                .output()
                .unwrap(),
            "input-alias",
        );
        assert_eq!(fs::read(&fixture.raw).unwrap(), raw_before);
        for (index, path) in paths.iter().enumerate() {
            if index != alias_position {
                assert!(
                    !path.exists(),
                    "alias position {alias_position}, output {index}"
                );
            }
        }
    }

    for incumbent_position in 0..3 {
        let paths = [
            fixture
                .directory
                .join(format!("incumbent-{incumbent_position}-trace")),
            fixture
                .directory
                .join(format!("incumbent-{incumbent_position}-canonical")),
            fixture
                .directory
                .join(format!("incumbent-{incumbent_position}-result")),
        ];
        fs::write(&paths[incumbent_position], b"incumbent").unwrap();
        assert_failure(
            fixture
                .legacy_command(&paths[2], &paths[0], &paths[1])
                .output()
                .unwrap(),
            "output-exists",
        );
        for (index, path) in paths.iter().enumerate() {
            if index == incumbent_position {
                assert_eq!(fs::read(path).unwrap(), b"incumbent");
            } else {
                assert!(
                    !path.exists(),
                    "incumbent position {incumbent_position}, output {index}"
                );
            }
        }
    }
    fixture.remove();
}

#[test]
fn help_and_argument_failures_expose_only_the_exact_boundary() {
    let help = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args(["evaluate-codex-exec-composition-v0", "--help"])
        .output()
        .unwrap();
    assert!(help.status.success(), "{help:?}");
    assert!(help.stderr.is_empty());
    let text = String::from_utf8(help.stdout).unwrap().to_lowercase();
    for required in [
        "exact stdout jsonl",
        "input authority",
        "trusted adaptation context",
        "adapter-owned trace",
        "accepts no caller-authored trace or normalized event values",
        "exact composition-policy bytes",
        "does not establish",
        "completeness",
        "truth",
        "intent access",
        "enforcement",
        "concurrency safety",
        "principal discovery",
        "incident prevention",
    ] {
        assert!(
            text.contains(required),
            "missing help boundary: {required}\n{text}"
        );
    }

    let hostile = "SECRET\u{1b}[31mINJECT";
    let rejected = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args(["evaluate-codex-exec-composition-v0", hostile])
        .output()
        .unwrap();
    assert_eq!(rejected.status.code(), Some(2));
    assert!(rejected.stdout.is_empty());
    assert_eq!(
        String::from_utf8(rejected.stderr).unwrap(),
        "legitimacy: cli-arguments\n"
    );

    let rejected_help = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args(["help", "evaluate-codex-exec-composition-v0", hostile])
        .output()
        .unwrap();
    assert_eq!(rejected_help.status.code(), Some(2));
    assert!(rejected_help.stdout.is_empty());
    assert_eq!(
        String::from_utf8(rejected_help.stderr).unwrap(),
        "legitimacy: cli-arguments\n"
    );
}

struct Fixture {
    directory: PathBuf,
    raw: PathBuf,
    input_receipt: PathBuf,
    adaptation_context: PathBuf,
    replay: PathBuf,
    replay_receipt: PathBuf,
    replay_trust: PathBuf,
    policy: PathBuf,
    output: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let directory = temp_directory();
        let fixture = Self {
            raw: directory.join("raw.jsonl"),
            input_receipt: directory.join("input-receipt.json"),
            adaptation_context: directory.join("adaptation-context.json"),
            replay: directory.join("replay.json"),
            replay_receipt: directory.join("replay-receipt.json"),
            replay_trust: directory.join("replay-trust.json"),
            policy: directory.join("policy.toml"),
            output: directory.join("result.json"),
            directory,
        };
        let authority = synthetic_authority();
        let context = trusted_context(&authority);
        let adapted = adapt_codex_exec_v0(RAW_CODEX_JSONL, &authority, &context).unwrap();
        let signing_key = signing_key(&AUTHORITY_KEY);
        let (candidate, receipt) = adapted
            .with_validated(|validated| {
                let candidate = trajectory_replay_candidate_v0(validated)
                    .to_json_line()
                    .unwrap();
                let receipt = issue_trajectory_replay_authority_receipt_v0(
                    validated,
                    &signing_key,
                    AUTHORITY_ISSUER,
                    AUTHORITY_KEY_ID,
                    AUTHORITY_EPOCH,
                )
                .unwrap()
                .to_json_line()
                .unwrap();
                (candidate, receipt)
            })
            .unwrap();
        fs::write(&fixture.raw, RAW_CODEX_JSONL).unwrap();
        fs::write(
            &fixture.input_receipt,
            serde_json::to_vec(&authority).unwrap(),
        )
        .unwrap();
        fs::write(
            &fixture.adaptation_context,
            serde_json::to_vec(&context).unwrap(),
        )
        .unwrap();
        fs::write(&fixture.replay, candidate).unwrap();
        fs::write(&fixture.replay_receipt, receipt).unwrap();
        fs::write(&fixture.replay_trust, trust_policy_bytes(&AUTHORITY_KEY)).unwrap();
        fs::write(&fixture.policy, TRAJECTORY_COMPOSITION_POLICY_BYTES_V0).unwrap();
        fixture
    }

    fn command(&self, output: &Path) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_legitimacy"));
        command
            .arg("evaluate-codex-exec-composition-v0")
            .arg("--raw-stdout-jsonl")
            .arg(&self.raw)
            .arg("--input-authority-receipt")
            .arg(&self.input_receipt)
            .arg("--trusted-adaptation-context")
            .arg(&self.adaptation_context)
            .arg("--replay-candidate")
            .arg(&self.replay)
            .arg("--replay-authority-receipt")
            .arg(&self.replay_receipt)
            .arg("--replay-authority-trust-policy")
            .arg(&self.replay_trust)
            .arg("--composition-policy")
            .arg(&self.policy)
            .arg("--output-set")
            .arg(output);
        command
    }

    fn legacy_command(&self, result: &Path, trace: &Path, canonical: &Path) -> Command {
        let command = self.command(result);
        let arguments = command
            .get_args()
            .map(ToOwned::to_owned)
            .collect::<Vec<_>>();
        let program = command.get_program().to_owned();
        let mut rebuilt = Command::new(program);
        let mut skip = false;
        for argument in arguments {
            if skip {
                skip = false;
                continue;
            }
            if argument == "--output-set" {
                skip = true;
                continue;
            }
            rebuilt.arg(argument);
        }
        rebuilt
            .arg("--trace-output")
            .arg(trace)
            .arg("--canonical-trace-output")
            .arg(canonical)
            .arg("--output")
            .arg(result);
        rebuilt
    }

    fn remove(&self) {
        fs::remove_dir_all(&self.directory).unwrap();
    }
}

fn synthetic_authority() -> InputAuthorityReceiptV0 {
    InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new_with_fixed_test_nonce(
            RAW_CODEX_JSONL,
            codex_exec_fixture_spec_binding_v0(),
            FixedSyntheticTestNonceV0::new([0x42; 32]),
        )
        .unwrap(),
    )
}

fn trusted_context(authority: &InputAuthorityReceiptV0) -> TrustedAdaptationContextV0 {
    trusted_context_for_policy(authority, TRAJECTORY_COMPOSITION_POLICY_BYTES_V0)
}

fn trusted_context_for_policy(
    authority: &InputAuthorityReceiptV0,
    policy: &[u8],
) -> TrustedAdaptationContextV0 {
    TrustedAdaptationContextV0::new(
        authority.commitment(),
        ArtifactBindingV0 {
            identity: TRAJECTORY_COMPOSITION_POLICY_ID_V0.to_string(),
            version: TRAJECTORY_COMPOSITION_POLICY_VERSION_V0.to_string(),
            hash: artifact_digest_v0(policy),
        },
    )
    .unwrap()
}

fn signing_key(bytes: &[u8; 32]) -> ReplayAuthoritySigningKeyV0 {
    ReplayAuthoritySigningKeyV0::from_bytes(bytes).unwrap()
}

fn trust_policy_bytes(key_bytes: &[u8; 32]) -> Vec<u8> {
    let key = signing_key(key_bytes);
    let mut bytes = serde_json::to_vec(&json!({
        "trust_policy_format": "legitimacy.trajectory.replay-authority-trust-policy",
        "trust_policy_version": "0",
        "issuer": AUTHORITY_ISSUER,
        "algorithm": "ed25519",
        "key_id": AUTHORITY_KEY_ID,
        "accepted_authority_epoch": AUTHORITY_EPOCH,
        "verification_key": key.verification_key_text(),
    }))
    .unwrap();
    bytes.push(b'\n');
    bytes
}

fn json_line(value: &Value) -> Vec<u8> {
    let mut bytes = serde_json::to_vec(value).unwrap();
    bytes.push(b'\n');
    bytes
}

fn raw_records() -> Vec<&'static [u8]> {
    RAW_CODEX_JSONL
        .strip_suffix(b"\n")
        .unwrap()
        .split(|byte| *byte == b'\n')
        .collect()
}

fn derivation_rules(trace: &TrajectoryTraceV0) -> BTreeSet<ArtifactBindingV0> {
    let mut rules = BTreeSet::new();
    add_rule(&trace.run_id, &mut rules);
    for event in &trace.events {
        add_rule(&event.event_id, &mut rules);
        add_rule(&event.sequence_index, &mut rules);
        add_rule(&event.kind, &mut rules);
        if let Some(source_item_id) = &event.source_item_id {
            add_rule(source_item_id, &mut rules);
        }
        for value in event.payload.values() {
            add_rule(value, &mut rules);
        }
    }
    rules
}

fn add_rule<T>(value: &EvidencedV0<T>, rules: &mut BTreeSet<ArtifactBindingV0>) {
    if let EvidenceV0::DeclaredDerivationBinding { rule, .. } = &value.evidence {
        rules.insert(rule.clone());
    }
}

fn replace_argument(command: &mut Command, flag: &str, replacement: &Path) {
    let arguments = command
        .get_args()
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    let position = arguments
        .iter()
        .position(|argument| argument == flag)
        .unwrap();
    let program = command.get_program().to_owned();
    let mut rebuilt = Command::new(program);
    for (index, argument) in arguments.into_iter().enumerate() {
        if index == position + 1 {
            rebuilt.arg(replacement);
        } else {
            rebuilt.arg(argument);
        }
    }
    *command = rebuilt;
}

fn public_projection_command(
    fixture: &Fixture,
    bundle: &Path,
    sidecar: Option<&Path>,
    output: &Path,
) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_legitimacy"));
    command
        .arg("evaluate-codex-exec-composition-v0")
        .arg("--raw-stdout-jsonl")
        .arg(&fixture.raw)
        .arg("--shareable-sanitized-bundle")
        .arg(bundle)
        .arg("--replay-candidate")
        .arg(&fixture.replay)
        .arg("--replay-authority-receipt")
        .arg(&fixture.replay_receipt)
        .arg("--replay-authority-trust-policy")
        .arg(&fixture.replay_trust)
        .arg("--composition-policy")
        .arg(&fixture.policy)
        .arg("--output-set")
        .arg(output);
    if let Some(sidecar) = sidecar {
        command.arg("--private-lineage-sidecar").arg(sidecar);
    }
    command
}

fn assert_success(output: Output) {
    assert!(output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

fn assert_failure(output: Output, code: &str) {
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty());
    assert_eq!(
        String::from_utf8(output.stderr).unwrap(),
        format!("legitimacy: {code}\n")
    );
}

fn temp_directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "legitimacy-codex-composition-{}-{}",
        std::process::id(),
        NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    path
}

fn zero_digest() -> &'static str {
    "sha256:0000000000000000000000000000000000000000000000000000000000000000"
}
