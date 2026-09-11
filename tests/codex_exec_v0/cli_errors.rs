#![cfg(target_os = "linux")]

use super::*;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_ERROR_CASE: AtomicU64 = AtomicU64::new(0);

#[test]
fn executable_cli_maps_parser_receipt_context_and_authority_failures_to_closed_codes() {
    let shape = concat!(
        "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000040\"}\n",
        "{\"type\":\"turn.started\",\"SECRET_FIELD\":0}\n",
        "{\"type\":\"turn.failed\",\"error\":{\"message\":\"synthetic\"}}\n"
    )
    .as_bytes();
    let unsupported = concat!(
        "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000040\"}\n",
        "{\"type\":\"turn.started\"}\n",
        "{\"type\":\"SECRET_RECORD\"}\n",
        "{\"type\":\"turn.failed\",\"error\":{\"message\":\"synthetic\"}}\n"
    )
    .as_bytes();
    let state = concat!(
        "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000040\"}\n",
        "{\"type\":\"turn.failed\",\"error\":{\"message\":\"synthetic\"}}\n"
    )
    .as_bytes();

    run_failure_case(
        &COMPLETED[..COMPLETED.len() - 1],
        &synthetic_authority(COMPLETED),
        Some(&trusted(&synthetic_authority(COMPLETED))),
        "private",
        "json-framing",
    );
    run_failure_case(
        b"{\n",
        &synthetic_authority(COMPLETED),
        Some(&trusted(&synthetic_authority(COMPLETED))),
        "private",
        "json-syntax",
    );
    let shape_authority = synthetic_authority(shape);
    run_failure_case(
        shape,
        &shape_authority,
        Some(&trusted(&shape_authority)),
        "private",
        "json-shape",
    );
    let unsupported_authority = synthetic_authority(unsupported);
    run_failure_case(
        unsupported,
        &unsupported_authority,
        Some(&trusted(&unsupported_authority)),
        "private",
        "unsupported-record",
    );
    let state_authority = synthetic_authority(state);
    run_failure_case(
        state,
        &state_authority,
        Some(&trusted(&state_authority)),
        "private",
        "stream-state",
    );

    let authority = synthetic_authority(COMPLETED);
    run_raw_files_failure(
        COMPLETED,
        b"{}",
        &serde_json::to_vec(&trusted(&authority)).unwrap(),
        "private",
        "receipt-shape",
    );
    run_raw_files_failure(
        COMPLETED,
        &serde_json::to_vec(&authority).unwrap(),
        b"{}",
        "private",
        "receipt-shape",
    );

    let unrelated = InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new(COMPLETED, codex_exec_fixture_spec_binding_v0()).unwrap(),
    );
    run_failure_case(
        COMPLETED,
        &authority,
        Some(&trusted(&unrelated)),
        "private",
        "trusted-context-mismatch",
    );
}

#[test]
fn executable_cli_maps_missing_and_nonregular_inputs_without_path_echo() {
    let directory = temp_directory();
    let missing = directory.join("SECRET-MISSING-RAW");
    let receipt = directory.join("receipt.json");
    let context = directory.join("context.json");
    let output = directory.join("output.jsonl");
    let authority = synthetic_authority(COMPLETED);
    fs::write(&receipt, serde_json::to_vec(&authority).unwrap()).unwrap();
    fs::write(&context, serde_json::to_vec(&trusted(&authority)).unwrap()).unwrap();
    let result = command(&missing, &receipt, &context, &output, "private")
        .output()
        .unwrap();
    assert_closed_failure(result, &output, "input-open");
    fs::remove_dir_all(directory).unwrap();
}

fn run_failure_case(
    raw: &[u8],
    authority: &InputAuthorityReceiptV0,
    context: Option<&TrustedAdaptationContextV0>,
    output_type: &str,
    code: &str,
) {
    let encoded_context = serde_json::to_vec(context.unwrap()).unwrap();
    run_raw_files_failure(
        raw,
        &serde_json::to_vec(authority).unwrap(),
        &encoded_context,
        output_type,
        code,
    );
}

fn run_raw_files_failure(
    raw: &[u8],
    receipt: &[u8],
    context: &[u8],
    output_type: &str,
    code: &str,
) {
    let directory = temp_directory();
    let raw_path = directory.join("raw.jsonl");
    let receipt_path = directory.join("receipt.json");
    let context_path = directory.join("context.json");
    let output = directory.join("output.jsonl");
    fs::write(&raw_path, raw).unwrap();
    fs::write(&receipt_path, receipt).unwrap();
    fs::write(&context_path, context).unwrap();
    let result = command(
        &raw_path,
        &receipt_path,
        &context_path,
        &output,
        output_type,
    )
    .output()
    .unwrap();
    assert_closed_failure(result, &output, code);
    fs::remove_dir_all(directory).unwrap();
}

fn assert_closed_failure(result: std::process::Output, output: &Path, code: &str) {
    assert_eq!(result.status.code(), Some(1));
    assert!(result.stdout.is_empty());
    assert!(!output.exists());
    assert!(!output.with_extension("lineage").exists());
    let stderr = String::from_utf8(result.stderr).unwrap();
    assert_eq!(stderr, format!("legitimacy: {code}\n"));
    assert!(stderr.len() < 64);
    assert!(!stderr.contains("SECRET"));
    assert!(!stderr.contains("sha256:"));
}

fn command(
    raw: &Path,
    receipt: &Path,
    context: &Path,
    output: &Path,
    output_type: &str,
) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_legitimacy"));
    command.args([
        "adapt-codex-exec-v0",
        "--raw-stdout-jsonl",
        raw.to_str().unwrap(),
        "--authority-receipt",
        receipt.to_str().unwrap(),
        "--trusted-context",
        context.to_str().unwrap(),
        "--output-type",
        output_type,
        "--output",
        output.to_str().unwrap(),
    ]);
    if output_type == "shareable-sanitized" {
        command.args([
            "--private-lineage-output",
            output.with_extension("lineage").to_str().unwrap(),
        ]);
    }
    command
}

fn temp_directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "legitimacy-codex-errors-{}-{}",
        std::process::id(),
        NEXT_ERROR_CASE.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    path
}
