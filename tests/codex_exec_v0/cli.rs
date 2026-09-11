use super::*;
#[cfg(target_os = "linux")]
use legitimacy::trajectory::codex_exec_v0::{
    InspectedShareableSanitizedBundleV0, OwnerPrivateLineageSidecarV0, SyntheticFixtureReceiptV0,
    codex_exec_fixture_spec_binding_v0,
};
#[cfg(target_os = "linux")]
use std::fs;
#[cfg(target_os = "linux")]
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::Path;
#[cfg(target_os = "linux")]
use std::path::PathBuf;
use std::process::Command;
#[cfg(target_os = "linux")]
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(target_os = "linux")]
static NEXT: AtomicU64 = AtomicU64::new(0);

#[cfg(target_os = "linux")]
struct TempDirectory {
    path: PathBuf,
    directory: fs::File,
}

#[cfg(target_os = "linux")]
impl std::ops::Deref for TempDirectory {
    type Target = Path;

    fn deref(&self) -> &Self::Target {
        &self.path
    }
}

#[cfg(target_os = "linux")]
impl AsRef<Path> for TempDirectory {
    fn as_ref(&self) -> &Path {
        &self.path
    }
}

#[cfg(target_os = "linux")]
impl Drop for TempDirectory {
    fn drop(&mut self) {
        let Ok(owned) = self.directory.metadata() else {
            return;
        };
        let Ok(current) = fs::symlink_metadata(&self.path) else {
            return;
        };
        if current.file_type().is_dir()
            && (owned.dev(), owned.ino()) == (current.dev(), current.ino())
        {
            let _ = fs::remove_dir_all(&self.path);
        }
    }
}

#[test]
fn cli_argument_errors_do_not_echo_attacker_values() {
    let result = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args([
            "adapt-codex-exec-v0",
            "--output-type",
            "SECRET\u{1b}[31mINJECT",
        ])
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(2));
    assert!(result.stdout.is_empty());
    let stderr = String::from_utf8(result.stderr).unwrap();
    assert_eq!(stderr, "legitimacy: cli-arguments\n");

    let mut hostiles = vec![std::ffi::OsString::from("SECRET\u{1b}[31mINJECT")];
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStringExt;
        hostiles.push(std::ffi::OsString::from_vec(vec![b'S', 0x80, b'X']));
    }
    for hostile in hostiles {
        let result = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
            .args(["help", "adapt-codex-exec-v0"])
            .arg(hostile)
            .output()
            .unwrap();
        assert_cli_arguments(result);
    }
}

#[cfg(target_os = "linux")]
#[test]
fn shareable_sidecar_argument_matrix_is_exact_and_precedes_all_input_reads() {
    let directory = temp_directory();
    let public = directory.join("public");
    let sidecar = directory.join("SECRET\u{1b}[31mNEVER-ECHO");
    let missing = ["missing-raw", "missing-receipt", "missing-context"].map(Path::new);

    let shareable_missing = command(
        missing[0],
        missing[1],
        missing[2],
        &public,
        "shareable-sanitized",
    )
    .output()
    .unwrap();
    assert_cli_arguments(shareable_missing);
    assert!(!public.exists());
    assert!(!sidecar.exists());

    let private_extraneous = command_with_sidecar(
        missing[0],
        missing[1],
        missing[2],
        &public,
        "private",
        Some(&sidecar),
    )
    .output()
    .unwrap();
    assert_cli_arguments(private_extraneous);
    assert!(!public.exists());
    assert!(!sidecar.exists());
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn clap_diagnostics_are_closed_only_for_adapter_attempts() {
    let unrelated = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args(["compile", "--UNRELATED-SECRET"])
        .output()
        .unwrap();
    assert_eq!(unrelated.status.code(), Some(2));
    assert!(unrelated.stdout.is_empty());
    let stderr = String::from_utf8(unrelated.stderr).unwrap();
    assert!(stderr.contains("--UNRELATED-SECRET"));
    assert!(stderr.contains("Usage:"));

    for args in [
        vec!["--help"],
        vec!["--version"],
        vec!["adapt-codex-exec-v0", "--help"],
        vec!["help", "adapt-codex-exec-v0"],
    ] {
        let result = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
            .args(args)
            .output()
            .unwrap();
        assert!(result.status.success());
        assert!(!result.stdout.is_empty());
        assert!(result.stderr.is_empty());
    }
}

#[cfg(not(target_os = "linux"))]
#[test]
fn executable_adapter_is_exactly_unsupported_off_linux() {
    let result = command(
        Path::new("unopened-raw"),
        Path::new("unopened-receipt"),
        Path::new("unopened-context"),
        Path::new("uncreated-output"),
        "private",
    )
    .output()
    .unwrap();
    assert_eq!(result.status.code(), Some(1));
    assert!(result.stdout.is_empty());
    assert_eq!(
        String::from_utf8(result.stderr).unwrap(),
        "legitimacy: unsupported-platform\n"
    );
    assert!(!Path::new("uncreated-output").exists());

    let valid_shareable = command_with_sidecar(
        Path::new("unopened-raw"),
        Path::new("unopened-receipt"),
        Path::new("unopened-context"),
        Path::new("uncreated-public"),
        "shareable-sanitized",
        Some(Path::new("uncreated-lineage")),
    )
    .output()
    .unwrap();
    assert_eq!(valid_shareable.status.code(), Some(1));
    assert_eq!(
        String::from_utf8(valid_shareable.stderr).unwrap(),
        "legitimacy: unsupported-platform\n"
    );
    assert!(!Path::new("uncreated-public").exists());
    assert!(!Path::new("uncreated-lineage").exists());

    let missing_lineage = command(
        Path::new("unopened-raw"),
        Path::new("unopened-receipt"),
        Path::new("unopened-context"),
        Path::new("uncreated-public"),
        "shareable-sanitized",
    )
    .output()
    .unwrap();
    assert_cli_arguments(missing_lineage);

    let private_extra = command_with_sidecar(
        Path::new("unopened-raw"),
        Path::new("unopened-receipt"),
        Path::new("unopened-context"),
        Path::new("uncreated-output"),
        "private",
        Some(Path::new("uncreated-lineage")),
    )
    .output()
    .unwrap();
    assert_cli_arguments(private_extra);
}

#[cfg(target_os = "linux")]
#[test]
fn cli_writes_private_bundle_atomically_and_emits_no_success_output() {
    let directory = temp_directory();
    let raw = directory.join("raw.jsonl");
    let receipt_path = directory.join("receipt.json");
    let context_path = directory.join("context.json");
    let output = directory.join("bundle.jsonl");
    let authority = synthetic_authority(COMPLETED);
    let context = trusted(&authority);
    fs::write(&raw, COMPLETED).unwrap();
    fs::write(&receipt_path, serde_json::to_vec(&authority).unwrap()).unwrap();
    fs::write(&context_path, serde_json::to_vec(&context).unwrap()).unwrap();

    let result = command(&raw, &receipt_path, &context_path, &output, "private")
        .output()
        .unwrap();
    assert!(result.status.success(), "{:?}", result.stderr);
    assert!(result.stdout.is_empty());
    assert!(result.stderr.is_empty());
    let bytes = fs::read(&output).unwrap();
    assert!(bytes.ends_with(b"\n"));
    assert!(
        legitimacy::trajectory::codex_exec_v0::InspectedPrivateAdapterBundleV0::from_json_slice(
            &bytes
        )
        .is_ok()
    );
    let mut inventory = fs::read_dir(&directory)
        .unwrap()
        .map(|entry| entry.unwrap().file_name())
        .collect::<Vec<_>>();
    inventory.sort();
    assert_eq!(
        inventory,
        ["bundle.jsonl", "context.json", "raw.jsonl", "receipt.json"]
            .map(std::ffi::OsString::from)
            .to_vec()
    );
    fs::remove_dir_all(directory).unwrap();
}

#[cfg(target_os = "linux")]
#[test]
fn shareable_route_mints_local_authority_for_fixed_and_random_parent_assertions() {
    let denied = temp_directory();
    let denied_raw = denied.join("raw.jsonl");
    let denied_receipt = denied.join("receipt.json");
    let denied_context = denied.join("context.json");
    let denied_public = denied.join("public.jsonl");
    let denied_sidecar = denied.join("lineage.bin");
    let fixed = synthetic_authority(COMPLETED);
    fs::write(&denied_raw, COMPLETED).unwrap();
    fs::write(&denied_receipt, serde_json::to_vec(&fixed).unwrap()).unwrap();
    fs::write(
        &denied_context,
        serde_json::to_vec(&trusted(&fixed)).unwrap(),
    )
    .unwrap();
    let result = command_with_sidecar(
        &denied_raw,
        &denied_receipt,
        &denied_context,
        &denied_public,
        "shareable-sanitized",
        Some(&denied_sidecar),
    )
    .output()
    .unwrap();
    assert!(result.status.success(), "{:?}", result.stderr);
    assert!(result.stdout.is_empty());
    assert!(result.stderr.is_empty());
    let fixed_public = fs::read(&denied_public).unwrap();
    let fixed_sidecar = fs::read(&denied_sidecar).unwrap();
    OwnerPrivateLineageSidecarV0::from_binary_slice(&fixed_sidecar)
        .unwrap()
        .revalidate_public_bundle(
            InspectedShareableSanitizedBundleV0::from_json_slice(&fixed_public).unwrap(),
        )
        .unwrap()
        .validate()
        .unwrap();
    fs::remove_dir_all(denied).unwrap();

    let directory = temp_directory();
    let raw = directory.join("raw.jsonl");
    let receipt = directory.join("receipt.json");
    let context = directory.join("context.json");
    let public = directory.join("public.jsonl");
    let sidecar = directory.join("lineage.bin");
    let random = InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new(COMPLETED, codex_exec_fixture_spec_binding_v0()).unwrap(),
    );
    fs::write(&raw, COMPLETED).unwrap();
    fs::write(&receipt, serde_json::to_vec(&random).unwrap()).unwrap();
    fs::write(&context, serde_json::to_vec(&trusted(&random)).unwrap()).unwrap();
    let result = command_with_sidecar(
        &raw,
        &receipt,
        &context,
        &public,
        "shareable-sanitized",
        Some(&sidecar),
    )
    .output()
    .unwrap();
    assert!(result.status.success(), "{:?}", result.stderr);
    assert!(result.stdout.is_empty());
    assert!(result.stderr.is_empty());
    let sidecar_bytes = fs::read(&sidecar).unwrap();
    let public_bytes = fs::read(&public).unwrap();
    let inspected = InspectedShareableSanitizedBundleV0::from_json_slice(&public_bytes).unwrap();
    OwnerPrivateLineageSidecarV0::from_binary_slice(&sidecar_bytes)
        .unwrap()
        .revalidate_public_bundle(inspected)
        .unwrap()
        .validate()
        .unwrap();
    for path in [&sidecar, &public] {
        let metadata = fs::metadata(path).unwrap();
        assert_eq!(metadata.permissions().mode() & 0o7777, 0o600);
        assert_eq!(metadata.uid(), rustix::process::geteuid().as_raw());
        assert_eq!(metadata.nlink(), 1);
    }
    let mut inventory = fs::read_dir(&directory)
        .unwrap()
        .map(|entry| entry.unwrap().file_name())
        .collect::<Vec<_>>();
    inventory.sort();
    assert_eq!(
        inventory,
        [
            "context.json",
            "lineage.bin",
            "public.jsonl",
            "raw.jsonl",
            "receipt.json",
        ]
        .map(std::ffi::OsString::from)
        .to_vec()
    );
    fs::remove_dir_all(directory).unwrap();
}

#[cfg(target_os = "linux")]
#[test]
fn executable_rejects_equal_shareable_destinations_without_creating_one() {
    let directory = temp_directory();
    let raw = directory.join("raw.jsonl");
    let receipt = directory.join("receipt.json");
    let context = directory.join("context.json");
    let output = directory.join("same");
    let random = InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new(COMPLETED, codex_exec_fixture_spec_binding_v0()).unwrap(),
    );
    fs::write(&raw, COMPLETED).unwrap();
    fs::write(&receipt, serde_json::to_vec(&random).unwrap()).unwrap();
    fs::write(&context, serde_json::to_vec(&trusted(&random)).unwrap()).unwrap();
    let result = command_with_sidecar(
        &raw,
        &receipt,
        &context,
        &output,
        "shareable-sanitized",
        Some(&output),
    )
    .output()
    .unwrap();
    assert_eq!(result.status.code(), Some(1));
    assert!(result.stdout.is_empty());
    assert_eq!(
        String::from_utf8(result.stderr).unwrap(),
        "legitimacy: cross-output-alias\n"
    );
    assert!(!output.exists());
    fs::remove_dir_all(directory).unwrap();
}

#[cfg(target_os = "linux")]
#[test]
fn cli_failure_is_closed_and_promotes_no_output() {
    let directory = temp_directory();
    let raw = directory.join("raw.jsonl");
    let receipt_path = directory.join("receipt.json");
    let context_path = directory.join("context.json");
    let output = directory.join("bundle.jsonl");
    let sidecar = directory.join("lineage.bin");
    let hostile = COMPLETED
        .windows(b"thread_id".len())
        .position(|window| window == b"thread_id")
        .unwrap();
    let mut bytes = COMPLETED.to_vec();
    bytes.splice(
        hostile..hostile + b"thread_id".len(),
        b"SECRET\\u001bINJECT".iter().copied(),
    );
    let authority = synthetic_authority(&bytes);
    let context = trusted(&authority);
    fs::write(&raw, &bytes).unwrap();
    fs::write(&receipt_path, serde_json::to_vec(&authority).unwrap()).unwrap();
    fs::write(&context_path, serde_json::to_vec(&context).unwrap()).unwrap();

    let result = command_with_sidecar(
        &raw,
        &receipt_path,
        &context_path,
        &output,
        "shareable-sanitized",
        Some(&sidecar),
    )
    .output()
    .unwrap();
    assert_eq!(result.status.code(), Some(1));
    assert!(result.stdout.is_empty());
    assert!(!output.exists());
    assert!(!sidecar.exists());
    let stderr = String::from_utf8(result.stderr).unwrap();
    assert!(stderr.starts_with("legitimacy: "));
    assert!(!stderr.contains("SECRET"));
    assert!(!stderr.contains("INJECT"));
    assert!(!stderr.contains('\u{1b}'));
    fs::remove_dir_all(directory).unwrap();
}

#[cfg(target_os = "linux")]
#[test]
fn cli_rejects_symlink_and_hard_link_inputs() {
    use std::os::unix::fs::symlink;

    let directory = temp_directory();
    let raw_real = directory.join("raw-real.jsonl");
    let raw_link = directory.join("raw-link.jsonl");
    let receipt_path = directory.join("receipt.json");
    let context_path = directory.join("context.json");
    let output = directory.join("bundle.jsonl");
    let authority = synthetic_authority(COMPLETED);
    fs::write(&raw_real, COMPLETED).unwrap();
    symlink(&raw_real, &raw_link).unwrap();
    fs::write(&receipt_path, serde_json::to_vec(&authority).unwrap()).unwrap();
    fs::hard_link(&receipt_path, &context_path).unwrap();

    let result = command(&raw_link, &receipt_path, &context_path, &output, "private")
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(1));
    assert!(!output.exists());
    let stderr = String::from_utf8(result.stderr).unwrap();
    assert!(!stderr.contains(raw_link.to_str().unwrap()));

    let second_output = directory.join("bundle-second.jsonl");
    let result = command(
        &raw_real,
        &receipt_path,
        &context_path,
        &second_output,
        "private",
    )
    .output()
    .unwrap();
    assert_eq!(result.status.code(), Some(1));
    assert!(!second_output.exists());
    assert!(
        String::from_utf8(result.stderr)
            .unwrap()
            .contains("input-alias")
    );

    let fifo = directory.join("raw.fifo");
    assert!(
        Command::new("mkfifo")
            .arg(&fifo)
            .status()
            .unwrap()
            .success()
    );
    let third_output = directory.join("bundle-third.jsonl");
    let mut fifo_command = command(
        &fifo,
        &receipt_path,
        &context_path,
        &third_output,
        "private",
    );
    fifo_command
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    let mut child = fifo_command.spawn().unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    loop {
        if child.try_wait().unwrap().is_some() {
            break;
        }
        if std::time::Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("FIFO input exceeded the five-second deadline");
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    let result = child.wait_with_output().unwrap();
    assert_eq!(result.status.code(), Some(1));
    assert!(!third_output.exists());
    assert_eq!(
        String::from_utf8(result.stderr).unwrap(),
        "legitimacy: input-type\n"
    );
    fs::remove_dir_all(directory).unwrap();
}

#[cfg(target_os = "linux")]
#[test]
fn cli_rejects_parent_and_final_symlinks_aliases_and_nonregular_inputs() {
    use std::os::unix::fs::symlink;
    use std::os::unix::net::UnixListener;

    let root = temp_directory();
    let real = root.join("real");
    let linked = root.join("linked");
    fs::create_dir(&real).unwrap();
    symlink(&real, &linked).unwrap();
    let authority = synthetic_authority(COMPLETED);
    let context = trusted(&authority);
    let raw = real.join("raw.jsonl");
    let receipt = real.join("receipt.json");
    let trusted_path = real.join("context.json");
    fs::write(&raw, COMPLETED).unwrap();
    fs::write(&receipt, serde_json::to_vec(&authority).unwrap()).unwrap();
    fs::write(&trusted_path, serde_json::to_vec(&context).unwrap()).unwrap();

    let linked_output = real.join("linked-output.jsonl");
    let result = command(
        &linked.join("raw.jsonl"),
        &receipt,
        &trusted_path,
        &linked_output,
        "private",
    )
    .output()
    .unwrap();
    assert_eq!(result.status.code(), Some(1));
    assert!(!linked_output.exists());

    let final_symlink = real.join("final-symlink.jsonl");
    symlink(real.join("missing-target"), &final_symlink).unwrap();
    let result = command(&raw, &receipt, &trusted_path, &final_symlink, "private")
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(1));
    assert!(
        fs::symlink_metadata(&final_symlink)
            .unwrap()
            .file_type()
            .is_symlink()
    );
    assert_eq!(
        String::from_utf8(result.stderr).unwrap(),
        "legitimacy: output-symlink\n"
    );

    for (index, input) in [&raw, &receipt, &trusted_path].into_iter().enumerate() {
        let alias = real.join(format!("input-{index}-alias-output.jsonl"));
        fs::hard_link(input, &alias).unwrap();
        let result = command(&raw, &receipt, &trusted_path, &alias, "private")
            .output()
            .unwrap();
        assert_eq!(result.status.code(), Some(1));
        assert_eq!(
            String::from_utf8(result.stderr).unwrap(),
            "legitimacy: input-alias\n"
        );
        fs::remove_file(alias).unwrap();
    }

    let socket = real.join("input.socket");
    let _listener = UnixListener::bind(&socket).unwrap();
    let socket_output = real.join("socket-output.jsonl");
    let result = command(&socket, &receipt, &trusted_path, &socket_output, "private")
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(1));
    assert!(!socket_output.exists());

    let device_output = real.join("device-output.jsonl");
    let result = command(
        Path::new("/dev/null"),
        &receipt,
        &trusted_path,
        &device_output,
        "private",
    )
    .output()
    .unwrap();
    assert_eq!(result.status.code(), Some(1));
    assert!(!device_output.exists());

    fs::remove_dir_all(root).unwrap();
}

#[cfg(target_os = "linux")]
#[test]
fn cli_bounds_sparse_inputs_and_preserves_existing_output() {
    use legitimacy::trajectory::codex_exec_v0::MAX_CODEX_JSONL_BYTES_V0;

    let directory = temp_directory();
    let sparse = directory.join("sparse.jsonl");
    let receipt = directory.join("receipt.json");
    let context = directory.join("context.json");
    let output = directory.join("existing.jsonl");
    let authority = synthetic_authority(COMPLETED);
    fs::File::create(&sparse)
        .unwrap()
        .set_len(MAX_CODEX_JSONL_BYTES_V0 as u64 + 1)
        .unwrap();
    fs::write(&receipt, serde_json::to_vec(&authority).unwrap()).unwrap();
    fs::write(&context, serde_json::to_vec(&trusted(&authority)).unwrap()).unwrap();
    fs::write(&output, b"preserve-me").unwrap();

    let result = command(&sparse, &receipt, &context, &output, "private")
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(1));
    assert_eq!(fs::read(&output).unwrap(), b"preserve-me");
    assert!(
        String::from_utf8(result.stderr)
            .unwrap()
            .contains("input-too-large")
    );
    fs::remove_dir_all(directory).unwrap();
}

#[cfg(target_os = "linux")]
#[test]
fn cli_scratch_cleanup_survives_panic() {
    let mut path = None;
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let directory = temp_directory();
        path = Some(directory.to_path_buf());
        panic!("exercise scratch cleanup");
    }));
    assert!(panic.is_err());
    assert!(!path.unwrap().exists());
}

#[cfg(target_os = "linux")]
#[test]
fn cli_scratch_cleanup_preserves_same_path_replacement() {
    let directory = temp_directory();
    let path = directory.to_path_buf();
    fs::remove_dir(&path).unwrap();
    fs::create_dir(&path).unwrap();
    let sentinel = path.join("replacement-sentinel");
    fs::write(&sentinel, b"replacement").unwrap();
    drop(directory);
    assert_eq!(fs::read(&sentinel).unwrap(), b"replacement");
    fs::remove_dir_all(path).unwrap();
}

fn command(
    raw: &Path,
    receipt: &Path,
    context: &Path,
    output: &Path,
    output_type: &str,
) -> Command {
    command_with_sidecar(raw, receipt, context, output, output_type, None)
}

fn command_with_sidecar(
    raw: &Path,
    receipt: &Path,
    context: &Path,
    output: &Path,
    output_type: &str,
    private_lineage_output: Option<&Path>,
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
    if let Some(sidecar) = private_lineage_output {
        command.args(["--private-lineage-output", sidecar.to_str().unwrap()]);
    }
    command
}

fn assert_cli_arguments(result: std::process::Output) {
    assert_eq!(result.status.code(), Some(2));
    assert!(result.stdout.is_empty());
    assert_eq!(
        String::from_utf8(result.stderr).unwrap(),
        "legitimacy: cli-arguments\n"
    );
}

#[cfg(target_os = "linux")]
fn temp_directory() -> TempDirectory {
    loop {
        let path = Path::new("/tmp").join(format!(
            "cxv0-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        match fs::create_dir(&path) {
            Ok(()) => {
                let directory = fs::File::open(&path).unwrap_or_else(|error| {
                    let _ = fs::remove_dir(&path);
                    panic!("open CLI scratch directory: {error}");
                });
                return TempDirectory { path, directory };
            }
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("create CLI scratch directory: {error}"),
        }
    }
}
