#![cfg(target_os = "linux")]

use serde_json::{Value, json};
use std::fs;
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
const AUTHORITY_KEY: [u8; 32] = [0x42; 32];
const REMANENCE_MARKER: [u8; 32] = [
    0x91, 0x02, 0xa3, 0x14, 0xb5, 0x26, 0xc7, 0x38, 0xd9, 0x4a, 0xeb, 0x5c, 0xfd, 0x6e, 0x8f, 0x70,
    0x81, 0xf2, 0x63, 0xd4, 0x45, 0xb6, 0x27, 0x98, 0x09, 0x7a, 0xcb, 0x3c, 0xad, 0x1e, 0xef, 0x50,
];
const REMANENCE_FINDING: &[u8] = b"AUTHORITY_KEY_REMANENCE: marker reached free without clearing\n";

#[test]
fn cli_round_trip_matches_all_committed_outputs() {
    let directory = temp_directory();
    let canonical = directory.join("canonical-trace.bin");
    let replay = directory.join("replay.json");
    let receipt = directory.join("authority-receipt.json");
    let trust_policy = directory.join("authority-trust-policy.json");
    let verified = directory.join("verified.json");

    assert_success(
        validation_command("canonicalize-trajectory-v0", &canonical)
            .output()
            .unwrap(),
    );
    assert_eq!(
        fs::read(&canonical).unwrap(),
        fs::read(fixture("canonical-trace.bin")).unwrap()
    );

    assert_success(
        validation_command("build-trajectory-replay-candidate-v0", &replay)
            .output()
            .unwrap(),
    );
    assert_eq!(
        fs::read(&replay).unwrap(),
        fs::read(fixture("replay.json")).unwrap()
    );

    write_trust_policy(&trust_policy, &AUTHORITY_KEY);
    assert_success(authority_command(&directory, &receipt).output().unwrap());

    assert_success(
        verify_command(&replay, &receipt, &trust_policy, &verified)
            .output()
            .unwrap(),
    );
    let receipt_json: Value = serde_json::from_slice(&fs::read(&receipt).unwrap()).unwrap();
    let verified_json: Value = serde_json::from_slice(&fs::read(&verified).unwrap()).unwrap();
    assert_eq!(verified_json["authority_receipt"], receipt_json);
    assert_eq!(
        verified_json["replay"],
        serde_json::from_slice::<Value>(&fs::read(&replay).unwrap()).unwrap()
    );
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn cli_never_replaces_output_or_publishes_before_verification() {
    let directory = temp_directory();
    let replay = directory.join("replay.json");
    let receipt = directory.join("authority-receipt.json");
    let trust_policy = directory.join("authority-trust-policy.json");
    let verified = directory.join("verified.json");
    assert_success(
        validation_command("build-trajectory-replay-candidate-v0", &replay)
            .output()
            .unwrap(),
    );
    write_trust_policy(&trust_policy, &AUTHORITY_KEY);
    assert_success(authority_command(&directory, &receipt).output().unwrap());

    let incumbent = directory.join("incumbent.json");
    fs::write(&incumbent, b"incumbent").unwrap();
    let collision = validation_command("build-trajectory-replay-candidate-v0", &incumbent)
        .output()
        .unwrap();
    assert_failure(collision, "output-exists");
    assert_eq!(fs::read(&incumbent).unwrap(), b"incumbent");

    let mut mutated: Value = serde_json::from_slice(&fs::read(&receipt).unwrap()).unwrap();
    mutated["anchor"]["expected_final_head"] =
        json!("sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
    let mut mutated_bytes = serde_json::to_vec(&mutated).unwrap();
    mutated_bytes.push(b'\n');
    let bad_receipt = directory.join("bad-receipt.json");
    fs::write(&bad_receipt, mutated_bytes).unwrap();
    let rejected = verify_command(&replay, &bad_receipt, &trust_policy, &verified)
        .output()
        .unwrap();
    assert_failure(rejected, "authority-receipt-rejected");
    assert!(!verified.exists());

    let aliased = verify_command(&replay, &replay, &trust_policy, &verified)
        .output()
        .unwrap();
    assert_failure(aliased, "input-alias");
    assert!(!verified.exists());
    let inventory = fs::read_dir(&directory).unwrap().count();
    assert_eq!(inventory, 6, "no temporary publication name may remain");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn cli_validation_failure_leaves_no_success_path_and_uses_fixed_diagnostic() {
    let directory = temp_directory();
    let output = directory.join("replay.json");
    let malformed_trace = directory.join("trace.json");
    fs::write(&malformed_trace, br#"{"unexpected":"SECRET"}"#).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args([
            "build-trajectory-replay-candidate-v0",
            "--trace",
            malformed_trace.to_str().unwrap(),
            "--raw-records",
            fixture("raw-records.json").to_str().unwrap(),
            "--declared-context",
            fixture("declared-context.json").to_str().unwrap(),
            "--output",
            output.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_failure(result, "validation");
    assert!(!output.exists());
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn cli_rejects_producer_authority_copies_and_inode_aliases_without_output() {
    let directory = temp_directory();
    let replay = directory.join("replay.json");
    let producer_receipt = directory.join("producer-receipt.json");
    let copied_receipt = directory.join("copied-receipt.json");
    let trust_policy = directory.join("authority-trust-policy.json");
    let output = directory.join("verified.json");
    assert_success(
        validation_command("build-trajectory-replay-candidate-v0", &replay)
            .output()
            .unwrap(),
    );
    write_trust_policy(&trust_policy, &AUTHORITY_KEY);
    assert_success(
        authority_command_with_key(
            &directory,
            &producer_receipt,
            &[0x24; 32],
            "producer-private.key",
        )
        .output()
        .unwrap(),
    );

    let rejected = verify_command(&replay, &producer_receipt, &trust_policy, &output)
        .output()
        .unwrap();
    assert_failure(rejected, "authority-receipt-rejected");
    assert!(!output.exists());

    fs::copy(&producer_receipt, &copied_receipt).unwrap();
    let copied = verify_command(&replay, &copied_receipt, &trust_policy, &output)
        .output()
        .unwrap();
    assert_failure(copied, "authority-receipt-rejected");
    assert!(!output.exists());

    let aliased = verify_command(&replay, &producer_receipt, &producer_receipt, &output)
        .output()
        .unwrap();
    assert_failure(aliased, "input-alias");
    assert!(!output.exists());
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn authority_issuance_requires_private_key_and_never_accepts_replay_authority() {
    let directory = temp_directory();
    let replay = directory.join("shaped-fake-replay.json");
    let output = directory.join("authority-receipt.json");
    assert_success(
        validation_command("build-trajectory-replay-candidate-v0", &replay)
            .output()
            .unwrap(),
    );

    let insecure_key = directory.join("insecure.key");
    fs::write(&insecure_key, AUTHORITY_KEY).unwrap();
    fs::set_permissions(&insecure_key, fs::Permissions::from_mode(0o644)).unwrap();
    let insecure = authority_command_with_existing_key(&insecure_key, &output)
        .output()
        .unwrap();
    assert_failure(insecure, "unsupported-input-profile");
    assert!(!output.exists());

    let private_key = directory.join("private.key");
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true).mode(0o600);
    std::io::Write::write_all(&mut options.open(&private_key).unwrap(), &AUTHORITY_KEY).unwrap();
    let replay_as_trace = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args([
            "issue-trajectory-replay-authority-receipt-v0",
            "--trace",
            replay.to_str().unwrap(),
            "--raw-records",
            fixture("raw-records.json").to_str().unwrap(),
            "--declared-context",
            fixture("declared-context.json").to_str().unwrap(),
            "--authority-private-key",
            private_key.to_str().unwrap(),
            "--issuer",
            "trajectory.replay.test-authority",
            "--key-id",
            "trajectory-replay-test-key",
            "--authority-epoch",
            "7",
            "--output",
            output.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_failure(replay_as_trace, "validation");
    assert!(!output.exists());

    let removed_command = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args([
            "build-trajectory-replay-anchor-candidate-v0",
            "--replay",
            replay.to_str().unwrap(),
            "--output",
            output.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_eq!(removed_command.status.code(), Some(2));
    assert!(removed_command.stdout.is_empty());
    assert!(!output.exists());
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn authority_key_marker_is_cleared_on_every_issuance_exit() {
    let directory = temp_directory();
    let probe = directory.join("key-free-probe.so");
    let compiler = Command::new("cc")
        .args(["-shared", "-fPIC", "-O2", "-Wall", "-Wextra", "-Werror"])
        .arg(fixture("key_free_probe.c"))
        .arg("-o")
        .arg(&probe)
        .output()
        .unwrap();
    assert!(compiler.status.success(), "{compiler:?}");
    assert!(compiler.stdout.is_empty(), "{compiler:?}");
    assert!(compiler.stderr.is_empty(), "{compiler:?}");

    let control = directory.join("key-free-probe-control");
    let compiler = Command::new("cc")
        .args(["-O0", "-Wall", "-Wextra", "-Werror"])
        .arg(fixture("key_free_probe_control.c"))
        .arg("-o")
        .arg(&control)
        .output()
        .unwrap();
    assert!(compiler.status.success(), "{compiler:?}");
    assert!(compiler.stdout.is_empty(), "{compiler:?}");
    assert!(compiler.stderr.is_empty(), "{compiler:?}");
    let control = Command::new(control)
        .env("LD_PRELOAD", &probe)
        .output()
        .unwrap();
    assert!(control.status.success(), "{control:?}");
    assert!(control.stdout.is_empty(), "{control:?}");
    assert_eq!(control.stderr, REMANENCE_FINDING, "{control:?}");

    let malformed_trace = directory.join("malformed-trace.json");
    fs::write(&malformed_trace, b"{\"unexpected\":true}\n").unwrap();
    let malformed_key = write_private_key(&directory.join("malformed.key"), &REMANENCE_MARKER);
    let malformed_output = directory.join("malformed-receipt.json");
    let mut malformed = authority_command_with_paths(
        &malformed_trace,
        &fixture("raw-records.json"),
        &fixture("declared-context.json"),
        &malformed_key,
        &malformed_output,
    );
    assert_probed_failure(&mut malformed, &probe, "validation");
    assert!(!malformed_output.exists());

    let alias_key = write_private_key(&directory.join("alias.key"), &REMANENCE_MARKER);
    let mut alias = authority_command_with_existing_key(&alias_key, &alias_key);
    assert_probed_failure(&mut alias, &probe, "input-alias");
    assert_eq!(fs::read(&alias_key).unwrap(), REMANENCE_MARKER);

    let mut oversized_marker = REMANENCE_MARKER.to_vec();
    oversized_marker.push(0x61);
    let wrong_length_key = write_private_key(
        &directory.join("wrong-length.key"),
        oversized_marker.as_slice(),
    );
    let wrong_length_output = directory.join("wrong-length-receipt.json");
    let mut wrong_length =
        authority_command_with_existing_key(&wrong_length_key, &wrong_length_output);
    assert_probed_failure(&mut wrong_length, &probe, "input-too-large");
    assert!(!wrong_length_output.exists());

    let incumbent_key = write_private_key(&directory.join("incumbent.key"), &REMANENCE_MARKER);
    let incumbent_output = directory.join("incumbent.json");
    fs::write(&incumbent_output, b"incumbent").unwrap();
    let mut incumbent = authority_command_with_existing_key(&incumbent_key, &incumbent_output);
    assert_probed_failure(&mut incumbent, &probe, "output-exists");
    assert_eq!(fs::read(&incumbent_output).unwrap(), b"incumbent");

    let publication_key = write_private_key(&directory.join("publication.key"), &REMANENCE_MARKER);
    let publication_output = directory.join("missing-parent/receipt.json");
    let mut publication =
        authority_command_with_existing_key(&publication_key, &publication_output);
    assert_probed_failure(&mut publication, &probe, "output-publish");
    assert!(!publication_output.exists());

    let success_key = write_private_key(&directory.join("success.key"), &REMANENCE_MARKER);
    let success_output = directory.join("success-receipt.json");
    let mut success = authority_command_with_existing_key(&success_key, &success_output);
    let success = run_with_probe(&mut success, &probe);
    assert_success(success);
    assert_eq!(
        fs::metadata(&success_output).unwrap().permissions().mode() & 0o777,
        0o600
    );

    fs::remove_dir_all(directory).unwrap();
}

fn validation_command(command: &str, output: &Path) -> Command {
    let mut process = Command::new(env!("CARGO_BIN_EXE_legitimacy"));
    process.args([
        command,
        "--trace",
        fixture("trace.json").to_str().unwrap(),
        "--raw-records",
        fixture("raw-records.json").to_str().unwrap(),
        "--declared-context",
        fixture("declared-context.json").to_str().unwrap(),
        "--output",
        output.to_str().unwrap(),
    ]);
    process
}

fn authority_command(directory: &Path, output: &Path) -> Command {
    authority_command_with_key(directory, output, &AUTHORITY_KEY, "authority-private.key")
}

fn authority_command_with_key(
    directory: &Path,
    output: &Path,
    key_bytes: &[u8; 32],
    key_name: &str,
) -> Command {
    let key = directory.join(key_name);
    write_private_key(&key, key_bytes);
    authority_command_with_existing_key(&key, output)
}

fn authority_command_with_existing_key(key: &Path, output: &Path) -> Command {
    authority_command_with_paths(
        &fixture("trace.json"),
        &fixture("raw-records.json"),
        &fixture("declared-context.json"),
        key,
        output,
    )
}

fn authority_command_with_paths(
    trace: &Path,
    raw_records: &Path,
    declared_context: &Path,
    key: &Path,
    output: &Path,
) -> Command {
    let mut process = Command::new(env!("CARGO_BIN_EXE_legitimacy"));
    process.args([
        "issue-trajectory-replay-authority-receipt-v0",
        "--trace",
        trace.to_str().unwrap(),
        "--raw-records",
        raw_records.to_str().unwrap(),
        "--declared-context",
        declared_context.to_str().unwrap(),
        "--authority-private-key",
        key.to_str().unwrap(),
        "--issuer",
        "trajectory.replay.test-authority",
        "--key-id",
        "trajectory-replay-test-key",
        "--authority-epoch",
        "7",
        "--output",
        output.to_str().unwrap(),
    ]);
    process
}

fn write_private_key(path: &Path, bytes: &[u8]) -> PathBuf {
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true).mode(0o600);
    std::io::Write::write_all(&mut options.open(path).unwrap(), bytes).unwrap();
    path.to_path_buf()
}

fn run_with_probe(command: &mut Command, probe: &Path) -> Output {
    let output = command.env("LD_PRELOAD", probe).output().unwrap();
    assert!(
        !output
            .stderr
            .windows(REMANENCE_FINDING.len())
            .any(|window| window == REMANENCE_FINDING),
        "{output:?}"
    );
    output
}

fn assert_probed_failure(command: &mut Command, probe: &Path, code: &str) {
    assert_failure(run_with_probe(command, probe), code);
}

fn verify_command(replay: &Path, receipt: &Path, trust_policy: &Path, output: &Path) -> Command {
    let mut process = validation_command("verify-trajectory-replay-v0", output);
    process.args([
        "--replay",
        replay.to_str().unwrap(),
        "--authority-receipt",
        receipt.to_str().unwrap(),
        "--authority-trust-policy",
        trust_policy.to_str().unwrap(),
    ]);
    process
}

fn write_trust_policy(path: &Path, key_bytes: &[u8; 32]) {
    let key = legitimacy::ReplayAuthoritySigningKeyV0::from_bytes(key_bytes).unwrap();
    let mut bytes = serde_json::to_vec(&json!({
        "trust_policy_format": "legitimacy.trajectory.replay-authority-trust-policy",
        "trust_policy_version": "0",
        "issuer": "trajectory.replay.test-authority",
        "algorithm": "ed25519",
        "key_id": "trajectory-replay-test-key",
        "accepted_authority_epoch": 7,
        "verification_key": key.verification_key_text(),
    }))
    .unwrap();
    bytes.push(b'\n');
    fs::write(path, bytes).unwrap();
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

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/trajectory-replay-v0")
        .join(name)
}

fn temp_directory() -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "legitimacy-trajectory-replay-{}-{}",
        std::process::id(),
        NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    directory
}
