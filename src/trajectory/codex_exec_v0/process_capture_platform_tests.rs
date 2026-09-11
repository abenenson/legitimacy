use super::*;
use flate2::Compression;
use flate2::write::GzEncoder;
use std::io::Write;
use std::os::unix::fs::symlink;
use std::os::unix::net::UnixListener;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

use super::output::{OutputOperations, RealOutputOperations};
static NEXT_TEST: AtomicU64 = AtomicU64::new(0);

#[path = "process_capture_supervision_tests.rs"]
mod supervision_tests;

fn private_test_root(label: &str) -> PathBuf {
    let root = std::env::temp_dir().join(format!(
        "legitimacy-process-{label}-{}-{}",
        std::process::id(),
        NEXT_TEST.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&root).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
    root
}

#[test]
fn every_capture_error_code_has_a_stable_spelling() {
    let expected = [
        (AdapterErrorCodeV0::CaptureSpawn, "capture-spawn"),
        (AdapterErrorCodeV0::CaptureStdin, "capture-stdin"),
        (
            AdapterErrorCodeV0::CaptureStdoutOverflow,
            "capture-stdout-overflow",
        ),
        (
            AdapterErrorCodeV0::CaptureStderrOverflow,
            "capture-stderr-overflow",
        ),
        (AdapterErrorCodeV0::CaptureTimeout, "capture-timeout"),
        (
            AdapterErrorCodeV0::CaptureLiveDescendant,
            "capture-live-descendant",
        ),
        (AdapterErrorCodeV0::CaptureCleanup, "capture-cleanup"),
    ];
    for (code, spelling) in expected {
        assert_eq!(code.as_str(), spelling);
    }
}

#[test]
fn held_inputs_reject_symlinks_special_files_modes_aliases_and_changes() {
    let root = private_test_root("input-controls");
    let private = root.join("private");
    fs::write(&private, b"secret").unwrap();
    fs::set_permissions(&private, fs::Permissions::from_mode(0o600)).unwrap();
    let held = HeldFile::open(&private, FileRole::PrivateStdin).unwrap();

    let link = root.join("link");
    symlink(&private, &link).unwrap();
    assert!(HeldFile::open(&link, FileRole::PrivateStdin).is_err());

    let socket = root.join("socket");
    let listener = UnixListener::bind(&socket).unwrap();
    assert!(HeldFile::open(&socket, FileRole::SigstoreBundle).is_err());

    let wrong_mode = root.join("wrong-mode");
    fs::write(&wrong_mode, b"secret").unwrap();
    fs::set_permissions(&wrong_mode, fs::Permissions::from_mode(0o644)).unwrap();
    let wrong_mode_error = match HeldFile::open(&wrong_mode, FileRole::PrivateStdin) {
        Ok(_) => panic!("wrong private-input mode must fail"),
        Err(error) => error,
    };
    assert_eq!(
        wrong_mode_error.code(),
        AdapterErrorCodeV0::UnsupportedInputProfile
    );

    let alias = root.join("alias");
    fs::hard_link(&private, &alias).unwrap();
    let alias = HeldFile::open(&alias, FileRole::PrivateStdin).unwrap();
    assert_eq!(
        reject_aliases([&held, &alias]).unwrap_err().code(),
        AdapterErrorCodeV0::InputAlias
    );

    fs::write(&private, b"changed").unwrap();
    assert_eq!(
        held.verify().unwrap_err().code(),
        AdapterErrorCodeV0::InputChanged
    );

    drop(listener);
    drop(alias);
    drop(held);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn every_held_input_role_rejects_one_over_bound_sparse_files() {
    let root = private_test_root("input-bounds");
    for (label, role, mode) in [
        ("executable", FileRole::Executable, 0o700),
        ("release-archive", FileRole::ReleaseArchive, 0o600),
        ("sigstore-bundle", FileRole::SigstoreBundle, 0o600),
        ("capture-profile", FileRole::CaptureProfile, 0o600),
        ("private-stdin", FileRole::PrivateStdin, 0o600),
    ] {
        let path = root.join(label);
        let file = File::create(&path).unwrap();
        file.set_len(role.byte_cap() + 1).unwrap();
        drop(file);
        fs::set_permissions(&path, fs::Permissions::from_mode(mode)).unwrap();
        let error = match HeldFile::open(&path, role) {
            Ok(_) => panic!("one-over-bound {label} must fail"),
            Err(error) => error,
        };
        assert_eq!(error.code(), AdapterErrorCodeV0::InputTooLarge, "{label}");
    }

    let capture_tool = root.join("capture-tool");
    let file = File::create(&capture_tool).unwrap();
    file.set_len(CAPTURE_TOOL_FILE_CAP + 1).unwrap();
    drop(file);
    fs::set_permissions(&capture_tool, fs::Permissions::from_mode(0o700)).unwrap();
    let error = match open_running_image(capture_tool.to_str().unwrap()) {
        Ok(_) => panic!("one-over-bound capture tool must fail"),
        Err(error) => error,
    };
    assert_eq!(error.code(), AdapterErrorCodeV0::InputTooLarge);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn changed_length_is_rejected_before_reverification_hashing() {
    let root = private_test_root("input-length-change");
    let archive_path = root.join("release-archive");
    fs::write(&archive_path, b"initial").unwrap();
    fs::set_permissions(&archive_path, fs::Permissions::from_mode(0o600)).unwrap();
    let archive = HeldFile::open(&archive_path, FileRole::ReleaseArchive).unwrap();
    File::options()
        .write(true)
        .open(&archive_path)
        .unwrap()
        .set_len(RELEASE_ARCHIVE_FILE_CAP)
        .unwrap();
    assert_eq!(
        archive.verify().unwrap_err().code(),
        AdapterErrorCodeV0::InputChanged
    );
    drop(archive);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn release_archive_member_is_exactly_bound_to_the_held_executable() {
    let root = private_test_root("archive-controls");
    let member = root.join("member");
    fs::write(&member, b"held executable bytes").unwrap();
    fs::set_permissions(&member, fs::Permissions::from_mode(0o700)).unwrap();
    let executable = HeldFile::open(&member, FileRole::Executable).unwrap();
    let archive_path = root.join("release.tar.gz");
    let encoder = GzEncoder::new(File::create(&archive_path).unwrap(), Compression::fast());
    let mut builder = tar::Builder::new(encoder);
    let mut header = tar::Header::new_gnu();
    header.set_size(b"held executable bytes".len() as u64);
    header.set_mode(0o755);
    header.set_cksum();
    builder
        .append_data(
            &mut header,
            std::str::from_utf8(super::super::super::PROCESS_CAPTURE_ARCHIVE_MEMBER_V0).unwrap(),
            b"held executable bytes".as_slice(),
        )
        .unwrap();
    builder.into_inner().unwrap().finish().unwrap();
    fs::set_permissions(&archive_path, fs::Permissions::from_mode(0o600)).unwrap();
    let archive = HeldFile::open(&archive_path, FileRole::ReleaseArchive).unwrap();
    verify_archive_member(&archive, &executable.digest).unwrap();
    assert_eq!(
        verify_archive_member(
            &archive,
            "sha256:0000000000000000000000000000000000000000000000000000000000000000"
        )
        .unwrap_err()
        .code(),
        AdapterErrorCodeV0::ReceiptMismatch
    );
    assert_eq!(
        require_digest(
            &archive,
            "sha256:0000000000000000000000000000000000000000000000000000000000000000"
        )
        .unwrap_err()
        .code(),
        AdapterErrorCodeV0::ReceiptMismatch
    );
    drop(archive);
    drop(executable);
    fs::remove_dir_all(root).unwrap();
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum OutputFault {
    None,
    PartialWrite,
    FileSync,
    Revalidate,
    DirectorySync,
    ParentSyncBeforeAcceptance,
    UnlinkRollback,
    RemoveDirectoryRollback,
    ParentSyncRollback,
}

struct FaultOutputOperations {
    primary: OutputFault,
    rollback: OutputFault,
    real: RealOutputOperations,
    rollback_attempts: Vec<String>,
}

impl OutputOperations for FaultOutputOperations {
    fn write_file(&mut self, file: &mut File, content: &[u8], index: usize) -> AdapterResultV0<()> {
        if self.primary == OutputFault::PartialWrite && index == 0 {
            file.write_all(&content[..1]).unwrap();
            return Err(error(AdapterErrorCodeV0::OutputPublish));
        }
        self.real.write_file(file, content, index)
    }

    fn sync_file(&mut self, file: &File, index: usize) -> AdapterResultV0<()> {
        if self.primary == OutputFault::FileSync && index == 0 {
            return Err(error(AdapterErrorCodeV0::OutputPublish));
        }
        self.real.sync_file(file, index)
    }

    fn revalidate_held_and_named(&mut self) -> AdapterResultV0<()> {
        if self.primary == OutputFault::Revalidate {
            Err(error(AdapterErrorCodeV0::OutputPublish))
        } else {
            self.real.revalidate_held_and_named()
        }
    }

    fn sync_directory_before_acceptance(
        &mut self,
        directory: &std::os::fd::OwnedFd,
    ) -> AdapterResultV0<()> {
        if self.primary == OutputFault::DirectorySync {
            Err(error(AdapterErrorCodeV0::DurabilityUncertain))
        } else {
            self.real.sync_directory_before_acceptance(directory)
        }
    }

    fn sync_parent_before_acceptance(
        &mut self,
        parent: &std::os::fd::OwnedFd,
    ) -> AdapterResultV0<()> {
        if self.primary == OutputFault::ParentSyncBeforeAcceptance {
            Err(error(AdapterErrorCodeV0::DurabilityUncertain))
        } else {
            self.real.sync_parent_before_acceptance(parent)
        }
    }

    fn unlink_rollback(
        &mut self,
        directory: &std::os::fd::OwnedFd,
        name: &str,
    ) -> AdapterResultV0<()> {
        self.rollback_attempts.push(format!("unlink:{name}"));
        if self.rollback == OutputFault::UnlinkRollback && name == OUTPUTS[0] {
            Err(error(AdapterErrorCodeV0::CaptureCleanup))
        } else {
            self.real.unlink_rollback(directory, name)
        }
    }

    fn remove_directory_rollback(
        &mut self,
        parent: &std::os::fd::OwnedFd,
        name: &std::ffi::OsStr,
    ) -> AdapterResultV0<()> {
        self.rollback_attempts.push("remove-directory".to_string());
        if self.rollback == OutputFault::RemoveDirectoryRollback {
            Err(error(AdapterErrorCodeV0::CaptureCleanup))
        } else {
            self.real.remove_directory_rollback(parent, name)
        }
    }

    fn sync_parent_rollback(&mut self, parent: &std::os::fd::OwnedFd) -> AdapterResultV0<()> {
        self.rollback_attempts.push("sync-parent".to_string());
        if self.rollback == OutputFault::ParentSyncRollback {
            Err(error(AdapterErrorCodeV0::CaptureCleanup))
        } else {
            self.real.sync_parent_rollback(parent)
        }
    }
}

#[test]
fn output_fault_stages_have_exact_errors_and_residual_state() {
    let root = private_test_root("output-controls");
    for (label, primary, expected) in [
        (
            "partial",
            OutputFault::PartialWrite,
            AdapterErrorCodeV0::OutputPublish,
        ),
        (
            "file-sync",
            OutputFault::FileSync,
            AdapterErrorCodeV0::OutputPublish,
        ),
        (
            "revalidate",
            OutputFault::Revalidate,
            AdapterErrorCodeV0::OutputPublish,
        ),
        (
            "directory-sync",
            OutputFault::DirectorySync,
            AdapterErrorCodeV0::DurabilityUncertain,
        ),
        (
            "parent-sync-before-acceptance",
            OutputFault::ParentSyncBeforeAcceptance,
            AdapterErrorCodeV0::DurabilityUncertain,
        ),
    ] {
        let output = root.join(label);
        let mut operations = FaultOutputOperations {
            primary,
            rollback: OutputFault::None,
            real: RealOutputOperations,
            rollback_attempts: Vec::new(),
        };
        let error = publish_output_directory_with_operations(
            &output,
            [b"input", b"output", b"error", b"receipt\n"],
            &mut operations,
        )
        .unwrap_err();
        assert_eq!(error.code(), expected, "{label}");
        assert!(!output.exists(), "{label}");
        assert!(
            !OUTPUTS.iter().all(|name| output.join(name).is_file()),
            "{label} must not resemble an accepted publication"
        );
        if primary == OutputFault::ParentSyncBeforeAcceptance {
            assert_eq!(
                operations.rollback_attempts,
                [
                    "unlink:stdin.bin",
                    "unlink:stdout.jsonl",
                    "unlink:stderr.bin",
                    "unlink:process-capture-receipt.json",
                    "remove-directory",
                    "sync-parent",
                ]
            );
        }
    }

    for (label, rollback) in [
        ("unlink", OutputFault::UnlinkRollback),
        ("remove-directory", OutputFault::RemoveDirectoryRollback),
        ("parent-sync", OutputFault::ParentSyncRollback),
    ] {
        let output = root.join(label);
        let mut operations = FaultOutputOperations {
            primary: OutputFault::Revalidate,
            rollback,
            real: RealOutputOperations,
            rollback_attempts: Vec::new(),
        };
        let error = publish_output_directory_with_operations(
            &output,
            [b"input", b"output", b"error", b"receipt\n"],
            &mut operations,
        )
        .unwrap_err();
        assert_eq!(error.code(), AdapterErrorCodeV0::CaptureCleanup, "{label}");
        match rollback {
            OutputFault::UnlinkRollback => {
                assert_eq!(fs::read_dir(&output).unwrap().count(), 1);
                assert!(output.join(OUTPUTS[0]).is_file());
            }
            OutputFault::RemoveDirectoryRollback => {
                assert!(output.is_dir());
                assert_eq!(fs::read_dir(&output).unwrap().count(), 0);
            }
            OutputFault::ParentSyncRollback => assert!(!output.exists()),
            _ => unreachable!(),
        }
        if output.exists() {
            fs::remove_dir_all(&output).unwrap();
        }
    }

    fs::set_permissions(&root, fs::Permissions::from_mode(0o755)).unwrap();
    assert_eq!(
        publish_output_directory(&root.join("wrong-parent"), [b"x", b"x", b"x", b"x"])
            .unwrap_err()
            .code(),
        AdapterErrorCodeV0::UnsafeOutputPath
    );
    fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[serial_test::serial]
fn embedding_boundary_rejects_before_subreaper_and_preserves_unrelated_child() {
    let keep_thread = std::thread::spawn(|| std::thread::sleep(Duration::from_millis(200)));
    let mut unrelated = Command::new("/bin/sh")
        .args(["-c", "sleep 30"])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let before = rustix::process::child_subreaper().unwrap();
    assert_eq!(
        require_single_purpose_process().unwrap_err().code(),
        AdapterErrorCodeV0::CaptureSpawn
    );
    assert_eq!(rustix::process::child_subreaper().unwrap(), before);
    assert!(unrelated.try_wait().unwrap().is_none());
    unrelated.kill().unwrap();
    unrelated.wait().unwrap();
    keep_thread.join().unwrap();
}

#[test]
fn running_image_descriptor_ignores_named_path_replacement() {
    const MARKER: &str = "LEGITIMACY_RUNNING_IMAGE_REPLACEMENT_HELPER";
    if std::env::var_os(MARKER).is_some() {
        let named = std::env::current_exe().unwrap();
        let moved = named.with_extension("running");
        fs::rename(&named, &moved).unwrap();
        fs::copy("/bin/false", &named).unwrap();
        fs::set_permissions(&named, fs::Permissions::from_mode(0o700)).unwrap();
        let running = HeldRunningImage::open().unwrap();
        let moved_metadata = fs::metadata(&moved).unwrap();
        let replacement_metadata = fs::metadata(&named).unwrap();
        assert_eq!(
            (running.snapshot.dev, running.snapshot.ino),
            (moved_metadata.dev(), moved_metadata.ino())
        );
        assert_ne!(
            (running.snapshot.dev, running.snapshot.ino),
            (replacement_metadata.dev(), replacement_metadata.ino())
        );
        let moved_file = File::open(&moved).unwrap();
        assert_eq!(
            running.digest,
            standard_sha256_file(&moved_file, CAPTURE_TOOL_FILE_CAP, moved_metadata.len(),)
                .unwrap()
        );
        assert_ne!(
            running.digest,
            standard_sha256_file(
                &File::open(&named).unwrap(),
                CAPTURE_TOOL_FILE_CAP,
                replacement_metadata.len(),
            )
            .unwrap()
        );
        running.verify().unwrap();

        let stdout =
            include_bytes!("../../../tests/fixtures/codex-exec-v0/legal-completed.synthetic.jsonl")
                .to_vec();
        let authority = ProcessCaptureReceiptV0::from_observed_process(ObservedProcessCaptureV0 {
            executable_sha256: super::super::super::PROCESS_CAPTURE_EXECUTABLE_SHA256_V0
                .to_string(),
            executable_inode: InodeIdentityV0::new(11, 101),
            stdin: b"prompt".to_vec(),
            termination: ProcessTerminationV0::Exited { code: 0 },
            stdout,
            stderr: Vec::new(),
            capture_tool_file_sha256: running.digest.clone(),
            capture_tool_inode: running.inode(),
        })
        .unwrap();
        let wire = serde_json::to_value(authority).unwrap();
        assert_eq!(wire["capture_tool"]["file_sha256"], running.digest);
        assert_eq!(wire["capture_tool"]["inode"]["dev"], running.snapshot.dev);
        assert_eq!(wire["capture_tool"]["inode"]["ino"], running.snapshot.ino);
        return;
    }

    let root = private_test_root("running-image-replacement");
    let helper = root.join("capture-test-helper");
    fs::copy(std::env::current_exe().unwrap(), &helper).unwrap();
    fs::set_permissions(&helper, fs::Permissions::from_mode(0o700)).unwrap();
    let status = Command::new(&helper)
        .args([
            "--exact",
            "trajectory::codex_exec_v0::process_capture::platform::tests::running_image_descriptor_ignores_named_path_replacement",
            "--nocapture",
        ])
        .env(MARKER, "1")
        .status()
        .unwrap();
    assert!(status.success());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn empty_workspace_transaction_and_typed_receipt_round_trip() {
    let root = std::env::temp_dir().join(format!(
        "legitimacy-process-receipt-{}-{}",
        std::process::id(),
        NEXT_TEST.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&root).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
    let workspace_path = root.join("workspace");
    fs::create_dir(&workspace_path).unwrap();
    fs::set_permissions(&workspace_path, fs::Permissions::from_mode(0o700)).unwrap();
    let mut workspace = HeldWorkspace::open(&workspace_path).unwrap();
    workspace
        .execute_read_only(|| {
            assert_eq!(
                fs::metadata(&workspace_path).unwrap().permissions().mode() & 0o7777,
                0o500
            );
            Ok(())
        })
        .unwrap();
    assert_eq!(
        fs::metadata(&workspace_path).unwrap().permissions().mode() & 0o7777,
        0o700
    );
    fs::write(workspace_path.join("unexpected"), b"x").unwrap();
    assert_eq!(
        workspace.verify_empty_mode(0o700).unwrap_err().code(),
        AdapterErrorCodeV0::UnsupportedInputProfile
    );
    fs::remove_file(workspace_path.join("unexpected")).unwrap();

    let stdout =
        include_bytes!("../../../tests/fixtures/codex-exec-v0/legal-completed.synthetic.jsonl")
            .to_vec();
    let authority = ProcessCaptureReceiptV0::from_observed_process(ObservedProcessCaptureV0 {
        executable_sha256: super::super::super::PROCESS_CAPTURE_EXECUTABLE_SHA256_V0.to_string(),
        executable_inode: InodeIdentityV0::new(9, 100),
        stdin: b"prompt".to_vec(),
        termination: ProcessTerminationV0::Exited { code: 0 },
        stdout,
        stderr: Vec::new(),
        capture_tool_file_sha256: format!("sha256:{:x}", Sha256::digest(b"tool")),
        capture_tool_inode: InodeIdentityV0::new(9, 101),
    })
    .unwrap();
    let encoded = serde_json::to_vec(&authority).unwrap();
    let imported = InputAuthorityReceiptV0::from_json_slice(&encoded).unwrap();
    assert_eq!(imported.commitment(), authority.commitment());
    let wire: serde_json::Value = serde_json::from_slice(&encoded).unwrap();
    assert_eq!(wire["asserted_nonce_source"], "capture-random");
    assert_ne!(wire["blinding_nonce_lower_hex"], "00".repeat(32));
    assert_eq!(
        format!("{authority:?}"),
        "InputAuthorityReceiptV0 { authority: \"process-capture\", .. }"
    );

    drop(workspace);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn workspace_restoration_uncertainty_dominates_postcheck_failure() {
    let result = finish_workspace_transaction(
        Ok(()) as AdapterResultV0<()>,
        Err(error(AdapterErrorCodeV0::InputChanged)),
        Err(error(AdapterErrorCodeV0::CaptureCleanup)),
    );
    assert_eq!(
        result.unwrap_err().code(),
        AdapterErrorCodeV0::CaptureCleanup
    );
}
