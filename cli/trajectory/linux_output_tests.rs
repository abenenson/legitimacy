use super::*;
use crate::trajectory::linux_path::read_snapshot;
use std::collections::VecDeque;
use std::fs;
use std::os::unix::ffi::OsStringExt;
use std::os::unix::fs::{MetadataExt, PermissionsExt, symlink};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
static NEXT: AtomicU64 = AtomicU64::new(0);
static SERIAL: Mutex<()> = Mutex::new(());
type StageAction = Box<dyn FnMut(PublicationStageV0, Option<&OwnedFd>)>;
struct Hooks {
    events: Vec<PublicationEventV0>,
    fail: Option<PublicationStageV0>,
    action: Option<StageAction>,
    proc_root: PathBuf,
    sync_name: PathBuf,
    proc_source: Option<String>,
    write_steps: VecDeque<IoStep>,
    pread_steps: VecDeque<IoStep>,
}
#[derive(Clone, Copy)]
enum IoStep {
    Interrupt,
    Zero,
    Error,
    Max(usize),
}
impl Default for Hooks {
    fn default() -> Self {
        Self {
            events: Vec::new(),
            fail: None,
            action: None,
            proc_root: PathBuf::from("/proc"),
            sync_name: PathBuf::from("."),
            proc_source: None,
            write_steps: VecDeque::new(),
            pread_steps: VecDeque::new(),
        }
    }
}
impl PublicationHooksV0 for Hooks {
    fn event(&mut self, event: PublicationEventV0, _held: Option<&OwnedFd>) {
        self.events.push(event);
    }
    fn fail_before(&mut self, stage: PublicationStageV0, held: Option<&OwnedFd>) -> bool {
        if let Some(action) = &mut self.action {
            action(stage, held);
        }
        self.fail == Some(stage)
    }
    fn proc_root(&self) -> &Path {
        &self.proc_root
    }
    fn parent_sync_name(&self) -> &Path {
        &self.sync_name
    }
    fn proc_source(&self, held_fd: i32) -> String {
        self.proc_source
            .clone()
            .unwrap_or_else(|| format!("self/fd/{held_fd}"))
    }
    fn write(&mut self, held: &OwnedFd, bytes: &[u8]) -> Result<usize, Errno> {
        match self.write_steps.pop_front() {
            Some(IoStep::Interrupt) => Err(Errno::INTR),
            Some(IoStep::Zero) => Ok(0),
            Some(IoStep::Error) => Err(Errno::IO),
            Some(IoStep::Max(limit)) => rustix::io::write(held, &bytes[..bytes.len().min(limit)]),
            None => rustix::io::write(held, bytes),
        }
    }
    fn pread(&mut self, held: &OwnedFd, bytes: &mut [u8], offset: u64) -> Result<usize, Errno> {
        match self.pread_steps.pop_front() {
            Some(IoStep::Interrupt) => Err(Errno::INTR),
            Some(IoStep::Zero) => Ok(0),
            Some(IoStep::Error) => Err(Errno::IO),
            Some(IoStep::Max(limit)) => {
                let length = bytes.len().min(limit);
                rustix::io::pread(held, &mut bytes[..length], offset)
            }
            None => rustix::io::pread(held, bytes, offset),
        }
    }
}

#[test]
fn anonymous_publication_succeeds_on_repo_filesystem_and_never_clobbers() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("success");
    let output = root.join("bundle.jsonl");
    let bytes = b"private\n";
    let callback_root = root.clone();
    let callback_output = output.clone();
    let mut hooks = Hooks {
        action: Some(Box::new(move |stage, _| {
            if stage == PublicationStageV0::PreLinkSourceVerify {
                assert_directory_entries(&callback_root, &[]);
                assert!(!callback_output.exists());
            }
        })),
        ..Hooks::default()
    };
    let handle = publish_with_hooks(&output, bytes, &[], &mut hooks).unwrap();
    let metadata = fs::metadata(&output).unwrap();
    assert_eq!(fs::read(&output).unwrap(), bytes);
    assert_eq!(metadata.permissions().mode() & 0o7777, 0o600);
    assert_eq!(metadata.nlink(), 1);
    assert_directory_entries(&root, &["bundle.jsonl"]);

    let inode = (metadata.dev(), metadata.ino());
    let error = publish(&output, b"replacement\n", &[]).unwrap_err();
    assert_code(error, AdapterErrorCodeV0::OutputExists);
    let after = fs::metadata(&output).unwrap();
    assert_eq!((after.dev(), after.ino()), inode);
    assert_eq!(fs::read(&output).unwrap(), bytes);
    drop(handle);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn write_and_pread_drivers_exercise_partial_interrupt_zero_and_error_paths() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("io-driver");
    let output = root.join("partial");
    let mut hooks = Hooks {
        write_steps: VecDeque::from([IoStep::Interrupt, IoStep::Max(2)]),
        pread_steps: VecDeque::from([IoStep::Interrupt, IoStep::Max(3)]),
        ..Hooks::default()
    };
    let handle = publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap();
    assert_eq!(fs::read(&output).unwrap(), b"private\n");
    drop(handle);

    for (index, step) in [IoStep::Zero, IoStep::Error].into_iter().enumerate() {
        let output = root.join(format!("write-failure-{index}"));
        let mut hooks = Hooks {
            write_steps: VecDeque::from([step]),
            ..Hooks::default()
        };
        assert_code(
            publish_with_hooks(&output, b"x", &[], &mut hooks).unwrap_err(),
            AdapterErrorCodeV0::OutputPublish,
        );
        assert!(!output.exists());
    }
    for (index, step) in [IoStep::Zero, IoStep::Error].into_iter().enumerate() {
        let output = root.join(format!("pread-failure-{index}"));
        let mut hooks = Hooks {
            pread_steps: VecDeque::from([step]),
            ..Hooks::default()
        };
        assert_code(
            publish_with_hooks(&output, b"x", &[], &mut hooks).unwrap_err(),
            AdapterErrorCodeV0::OutputPublish,
        );
        assert!(!output.exists());
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn committed_handle_retains_readable_inode_after_name_unlink() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("retained-handle");
    let output = root.join("bundle");
    let handle = publish(&output, b"private\n", &[]).unwrap();
    fs::remove_file(&output).unwrap();
    let mut bytes = [0_u8; 8];
    assert_eq!(rustix::io::pread(&handle.held, &mut bytes, 0).unwrap(), 8);
    assert_eq!(&bytes, b"private\n");
    drop(handle);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn every_precommit_failure_is_truthful_and_leaves_no_final_artifact() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("precommit");
    let stages = [
        PublicationStageV0::StartOpen,
        PublicationStageV0::AncestorOpen(2),
        PublicationStageV0::ParentSyncOpen,
        PublicationStageV0::FinalPreflight,
        PublicationStageV0::TemporaryOpen,
        PublicationStageV0::Write,
        PublicationStageV0::Chmod,
        PublicationStageV0::TemporaryVerify,
        PublicationStageV0::FileSync,
        PublicationStageV0::PreLinkDirectorySync,
        PublicationStageV0::ProcOpen,
        PublicationStageV0::PreLinkSourceVerify,
        PublicationStageV0::Link,
    ];
    for (index, stage) in stages.into_iter().enumerate() {
        let parent = root.join(format!("case-{index}"));
        fs::create_dir(&parent).unwrap();
        let output = parent.join("bundle.jsonl");
        let mut hooks = Hooks {
            fail: Some(stage),
            ..Hooks::default()
        };
        let error = publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err();
        assert_code(error, AdapterErrorCodeV0::OutputPublish);
        assert!(!output.exists(), "{stage:?}");
        assert!(
            hooks.events.contains(&PublicationEventV0::Attempted(stage)),
            "{stage:?}"
        );
        assert!(
            !hooks.events.contains(&PublicationEventV0::Completed(stage)),
            "{stage:?}"
        );
        assert_directory_entries(&parent, &[]);
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn post_link_hook_preflight_preserves_exact_incumbent_inode_and_bytes() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("eexist");
    let output = root.join("bundle.jsonl");
    let observed = Arc::new(Mutex::new(None));
    let callback_observed = Arc::clone(&observed);
    let callback_output = output.clone();
    let mut hooks = Hooks {
        action: Some(Box::new(move |stage, _| {
            if stage == PublicationStageV0::Link {
                fs::write(&callback_output, b"incumbent\n").unwrap();
                let metadata = fs::metadata(&callback_output).unwrap();
                *callback_observed.lock().unwrap() = Some((metadata.dev(), metadata.ino()));
            }
        })),
        ..Hooks::default()
    };
    let error = publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err();
    assert_code(error, AdapterErrorCodeV0::OutputExists);
    let metadata = fs::metadata(&output).unwrap();
    assert_eq!(
        Some((metadata.dev(), metadata.ino())),
        *observed.lock().unwrap()
    );
    assert_eq!(fs::read(&output).unwrap(), b"incumbent\n");
    assert!(
        !hooks
            .events
            .contains(&PublicationEventV0::Completed(PublicationStageV0::Link))
    );
    assert_directory_entries(&root, &["bundle.jsonl"]);

    let raced_symlink = root.join("raced-symlink");
    let target = root.join("target");
    fs::write(&target, b"target").unwrap();
    let callback_output = raced_symlink.clone();
    let callback_target = target.clone();
    let mut hooks = Hooks {
        action: Some(Box::new(move |stage, _| {
            if stage == PublicationStageV0::Link {
                symlink(&callback_target, &callback_output).unwrap();
            }
        })),
        ..Hooks::default()
    };
    assert_code(
        publish_with_hooks(&raced_symlink, b"private\n", &[], &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::OutputSymlink,
    );
    assert!(
        fs::symlink_metadata(&raced_symlink)
            .unwrap()
            .file_type()
            .is_symlink()
    );

    let input_paths = [root.join("raw"), root.join("receipt"), root.join("context")];
    for (index, input) in input_paths.iter().enumerate() {
        fs::write(input, format!("input-{index}")).unwrap();
    }
    let raw = read_snapshot(&input_paths[0], 32).unwrap();
    let receipt = read_snapshot(&input_paths[1], 32).unwrap();
    let context = read_snapshot(&input_paths[2], 32).unwrap();
    for (index, input) in input_paths.iter().enumerate() {
        let output = root.join(format!("raced-input-alias-{index}"));
        let callback_output = output.clone();
        let callback_input = input.clone();
        let mut hooks = Hooks {
            action: Some(Box::new(move |stage, _| {
                if stage == PublicationStageV0::Link {
                    fs::hard_link(&callback_input, &callback_output).unwrap();
                }
            })),
            ..Hooks::default()
        };
        assert_code(
            publish_with_hooks(
                &output,
                b"private\n",
                &[&raw, &receipt, &context],
                &mut hooks,
            )
            .unwrap_err(),
            AdapterErrorCodeV0::InputAlias,
        );
        let input_metadata = fs::metadata(input).unwrap();
        let output_metadata = fs::metadata(&output).unwrap();
        assert_eq!(
            (output_metadata.dev(), output_metadata.ino()),
            (input_metadata.dev(), input_metadata.ino())
        );
        assert_eq!(fs::read(&output).unwrap(), fs::read(input).unwrap());
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn postcommit_failures_keep_artifact_and_obey_identity_integrity_durability_precedence() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());

    let root = test_root("post-sync");
    let output = root.join("bundle.jsonl");
    let mut hooks = Hooks {
        fail: Some(PublicationStageV0::PostLinkDirectorySync),
        ..Hooks::default()
    };
    let error = publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err();
    assert_code(error, AdapterErrorCodeV0::DurabilityUncertain);
    assert_eq!(fs::read(&output).unwrap(), b"private\n");
    assert!(!hooks.events.contains(&PublicationEventV0::Completed(
        PublicationStageV0::PostLinkDirectorySync
    )));
    fs::remove_dir_all(root).unwrap();

    let root = test_root("post-source");
    let output = root.join("bundle");
    let mut hooks = Hooks {
        fail: Some(PublicationStageV0::PostLinkSourceVerify),
        ..Hooks::default()
    };
    assert_code(
        publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::OutputIdentityUncertain,
    );
    assert_eq!(fs::read(&output).unwrap(), b"private\n");
    for stage in [
        PublicationStageV0::PostLinkSourceVerify,
        PublicationStageV0::PostLinkDirectorySync,
        PublicationStageV0::HeldIntegrityVerify,
        PublicationStageV0::FinalIdentityVerify,
    ] {
        assert!(
            hooks.events.contains(&PublicationEventV0::Attempted(stage)),
            "{stage:?}"
        );
    }
    fs::remove_dir_all(root).unwrap();

    for action in ["remove", "symlink", "replace"] {
        let root = test_root(&format!("identity-{action}"));
        let output = root.join("bundle.jsonl");
        let callback_output = output.clone();
        let target = root.join("target");
        fs::write(&target, b"target\n").unwrap();
        let mut hooks = Hooks {
            action: Some(Box::new(move |stage, _| {
                if stage == PublicationStageV0::FinalIdentityVerify {
                    fs::remove_file(&callback_output).unwrap();
                    match action {
                        "remove" => {}
                        "symlink" => symlink(&target, &callback_output).unwrap(),
                        "replace" => fs::write(&callback_output, b"replacement\n").unwrap(),
                        _ => unreachable!(),
                    }
                }
            })),
            ..Hooks::default()
        };
        let error = publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err();
        assert_code(error, AdapterErrorCodeV0::OutputIdentityUncertain);
        fs::remove_dir_all(root).unwrap();
    }

    let root = test_root("integrity");
    let output = root.join("bundle.jsonl");
    let mut hooks = Hooks {
        action: Some(Box::new(|stage, held| {
            if stage == PublicationStageV0::HeldIntegrityVerify {
                rustix::fs::ftruncate(held.unwrap(), 3).unwrap();
            }
        })),
        ..Hooks::default()
    };
    let error = publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err();
    assert_code(error, AdapterErrorCodeV0::OutputIdentityUncertain);
    assert_eq!(fs::metadata(&output).unwrap().len(), 3);
    fs::remove_dir_all(root).unwrap();

    let root = test_root("final-same-size-overwrite");
    let output = root.join("bundle");
    let mut hooks = Hooks {
        action: Some(Box::new(|stage, held| {
            if stage == PublicationStageV0::FinalIdentityVerify {
                rustix::io::pwrite(held.unwrap(), b"PRIVATE\n", 0).unwrap();
            }
        })),
        ..Hooks::default()
    };
    assert_code(
        publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::OutputIdentityUncertain,
    );
    fs::remove_dir_all(root).unwrap();

    for mutation in ["append", "truncate", "overwrite", "chmod", "add-link"] {
        let root = test_root(&format!("held-{mutation}"));
        let output = root.join("bundle");
        let extra = root.join("extra");
        let mut hooks = Hooks {
            action: Some(Box::new(move |stage, held| {
                if stage != PublicationStageV0::HeldIntegrityVerify {
                    return;
                }
                let held = held.unwrap();
                match mutation {
                    "append" => {
                        rustix::io::pwrite(held, b"x", 8).unwrap();
                    }
                    "truncate" => rustix::fs::ftruncate(held, 2).unwrap(),
                    "overwrite" => {
                        rustix::io::pwrite(held, b"PRIVATE\n", 0).unwrap();
                    }
                    "chmod" => fchmod(held, Mode::from_raw_mode(0o644)).unwrap(),
                    "add-link" => {
                        let proc = openat(
                            rustix::fs::CWD,
                            Path::new("/proc"),
                            OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
                            Mode::empty(),
                        )
                        .unwrap();
                        linkat(
                            &proc,
                            format!("self/fd/{}", held.as_raw_fd()),
                            rustix::fs::CWD,
                            &extra,
                            AtFlags::SYMLINK_FOLLOW,
                        )
                        .unwrap();
                    }
                    _ => unreachable!(),
                }
            })),
            ..Hooks::default()
        };
        let error = publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err();
        let expected = if mutation == "overwrite" {
            AdapterErrorCodeV0::OutputIntegrityUncertain
        } else {
            AdapterErrorCodeV0::OutputIdentityUncertain
        };
        assert_code(error, expected);
        fs::remove_dir_all(root).unwrap();
    }

    let root = test_root("name-to-input");
    let output = root.join("bundle");
    let input = root.join("input");
    fs::write(&input, b"input").unwrap();
    let callback_output = output.clone();
    let callback_input = input.clone();
    let mut hooks = Hooks {
        action: Some(Box::new(move |stage, _| {
            if stage == PublicationStageV0::FinalIdentityVerify {
                fs::remove_file(&callback_output).unwrap();
                fs::hard_link(&callback_input, &callback_output).unwrap();
            }
        })),
        ..Hooks::default()
    };
    assert_code(
        publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::OutputIdentityUncertain,
    );
    fs::remove_dir_all(root).unwrap();

    let root = test_root("integrity-over-sync");
    let output = root.join("bundle");
    let mut hooks = Hooks {
        fail: Some(PublicationStageV0::PostLinkDirectorySync),
        action: Some(Box::new(|stage, held| {
            if stage == PublicationStageV0::HeldIntegrityVerify {
                rustix::io::pwrite(held.unwrap(), b"PRIVATE\n", 0).unwrap();
            }
        })),
        ..Hooks::default()
    };
    assert_code(
        publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::OutputIntegrityUncertain,
    );
    fs::remove_dir_all(root).unwrap();

    let root = test_root("identity-over-sync");
    let output = root.join("bundle");
    let callback_output = output.clone();
    let mut hooks = Hooks {
        fail: Some(PublicationStageV0::PostLinkDirectorySync),
        action: Some(Box::new(move |stage, _| {
            if stage == PublicationStageV0::FinalIdentityVerify {
                fs::remove_file(&callback_output).unwrap();
            }
        })),
        ..Hooks::default()
    };
    assert_code(
        publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::OutputIdentityUncertain,
    );
    fs::remove_dir_all(root).unwrap();

    let root = test_root("precedence");
    let output = root.join("bundle.jsonl");
    let callback_output = output.clone();
    let mut hooks = Hooks {
        fail: Some(PublicationStageV0::PostLinkDirectorySync),
        action: Some(Box::new(move |stage, held| match stage {
            PublicationStageV0::FinalIdentityVerify => {
                fs::remove_file(&callback_output).unwrap();
            }
            PublicationStageV0::HeldIntegrityVerify => {
                rustix::fs::ftruncate(held.unwrap(), 2).unwrap();
            }
            _ => {}
        })),
        ..Hooks::default()
    };
    let error = publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err();
    assert_code(error, AdapterErrorCodeV0::OutputIdentityUncertain);
    assert!(hooks.events.contains(&PublicationEventV0::Attempted(
        PublicationStageV0::HeldIntegrityVerify
    )));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn output_path_parent_and_final_races_are_classified_and_pinned() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("paths");
    let absolute = root.join("absolute");
    let handle = publish(&absolute, b"a", &[]).unwrap();
    drop(handle);
    let repeated = PathBuf::from(std::ffi::OsString::from_vec(
        absolute
            .as_os_str()
            .as_bytes()
            .iter()
            .flat_map(|byte| {
                if *byte == b'/' {
                    vec![b'/', b'/']
                } else {
                    vec![*byte]
                }
            })
            .collect::<Vec<_>>(),
    ));
    fs::remove_file(&absolute).unwrap();
    let handle = publish(&repeated, b"b", &[]).unwrap();
    drop(handle);
    let internal_dot = root.join("dot").join(".").join("bundle");
    fs::create_dir(root.join("dot")).unwrap();
    let handle = publish(&internal_dot, b"c", &[]).unwrap();
    drop(handle);
    let non_utf8 = root.join(std::ffi::OsString::from_vec(b"non-utf8-\xff".to_vec()));
    let handle = publish(&non_utf8, b"d", &[]).unwrap();
    drop(handle);
    let relative_root = PathBuf::from(format!(
        "g3a-relative-output-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&relative_root).unwrap();
    let relative = relative_root.join("bundle");
    let handle = publish(&relative, b"e", &[]).unwrap();
    drop(handle);
    fs::remove_dir_all(&relative_root).unwrap();

    for unsafe_path in [
        PathBuf::new(),
        PathBuf::from("."),
        PathBuf::from("./"),
        PathBuf::from("/"),
        PathBuf::from("../"),
        PathBuf::from("../."),
        PathBuf::from("a/../"),
        PathBuf::from("/../"),
        PathBuf::from("a/../b"),
        PathBuf::from("input/.."),
    ] {
        assert_code(
            publish(&unsafe_path, b"x", &[]).unwrap_err(),
            AdapterErrorCodeV0::UnsafeOutputPath,
        );
    }
    let nul = PathBuf::from(std::ffi::OsString::from_vec(b"nul\0name".to_vec()));
    assert_code(
        publish(&nul, b"x", &[]).unwrap_err(),
        AdapterErrorCodeV0::UnsafeOutputPath,
    );
    let trailing = PathBuf::from(format!("{}/", root.display()));
    assert_code(
        publish(&trailing, b"x", &[]).unwrap_err(),
        AdapterErrorCodeV0::UnsafeOutputPath,
    );

    let real = root.join("real");
    let linked = root.join("linked");
    fs::create_dir(&real).unwrap();
    symlink(&real, &linked).unwrap();
    assert_code(
        publish(&linked.join("bundle"), b"x", &[]).unwrap_err(),
        AdapterErrorCodeV0::OutputSymlink,
    );
    let final_link = real.join("final");
    symlink(real.join("missing"), &final_link).unwrap();
    assert_code(
        publish(&final_link, b"x", &[]).unwrap_err(),
        AdapterErrorCodeV0::OutputSymlink,
    );
    let incumbent_directory = real.join("directory-output");
    fs::create_dir(&incumbent_directory).unwrap();
    assert_code(
        publish(&incumbent_directory, b"x", &[]).unwrap_err(),
        AdapterErrorCodeV0::OutputExists,
    );

    let before = root.join("before");
    let moved = root.join("before-moved");
    fs::create_dir(&before).unwrap();
    let output = before.join("bundle");
    let callback_before = before.clone();
    let callback_moved = moved.clone();
    let ancestor_index = output
        .components()
        .filter(|component| matches!(component, Component::Normal(_)))
        .count()
        - 2;
    let mut hooks = Hooks {
        action: Some(Box::new(move |stage, _| {
            if stage == PublicationStageV0::AncestorOpen(ancestor_index) {
                fs::rename(&callback_before, &callback_moved).unwrap();
                fs::create_dir(&callback_before).unwrap();
            }
        })),
        ..Hooks::default()
    };
    assert_code(
        publish_with_hooks(&output, b"x", &[], &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::OutputPublish,
    );
    assert!(!before.join("bundle").exists());
    assert!(!moved.join("bundle").exists());

    let after = root.join("after");
    let after_moved = root.join("after-moved");
    fs::create_dir(&after).unwrap();
    let output = after.join("bundle");
    let callback_after = after.clone();
    let callback_moved = after_moved.clone();
    let mut hooks = Hooks {
        action: Some(Box::new(move |stage, _| {
            if stage == PublicationStageV0::FinalPreflight {
                fs::rename(&callback_after, &callback_moved).unwrap();
                fs::create_dir(&callback_after).unwrap();
            }
        })),
        ..Hooks::default()
    };
    let handle = publish_with_hooks(&output, b"x", &[], &mut hooks).unwrap();
    assert!(!after.join("bundle").exists());
    assert_eq!(fs::read(after_moved.join("bundle")).unwrap(), b"x");
    drop(handle);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn every_controlled_ancestor_index_rejects_directory_and_symlink_substitution() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    for kind in ["directory", "symlink"] {
        for index in 0..3 {
            let first = PathBuf::from(format!(
                "g3a-ancestor-{}-{kind}-{index}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let second = first.join("second");
            let third = second.join("third");
            fs::create_dir_all(&third).unwrap();
            let output = third.join("bundle");
            let ancestors = [first.clone(), second, third];
            let target = ancestors[index].clone();
            let saved = target.with_extension("saved");
            let callback_target = target.clone();
            let callback_saved = saved.clone();
            let mut hooks = Hooks {
                action: Some(Box::new(move |stage, _| {
                    if stage == PublicationStageV0::AncestorOpen(index) {
                        fs::rename(&callback_target, &callback_saved).unwrap();
                        if kind == "directory" {
                            fs::create_dir(&callback_target).unwrap();
                        } else {
                            symlink(&callback_saved, &callback_target).unwrap();
                        }
                    }
                })),
                ..Hooks::default()
            };
            assert_code(
                publish_with_hooks(&output, b"x", &[], &mut hooks).unwrap_err(),
                AdapterErrorCodeV0::OutputPublish,
            );
            assert!(!target.join("bundle").exists());
            fs::remove_dir_all(&first).ok();
            fs::remove_dir_all(&saved).ok();
        }
    }
}

#[test]
fn profile_and_temporary_property_checks_fail_closed_before_commit() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("profiles");

    let output = root.join("wrong-proc");
    let mut hooks = Hooks {
        proc_root: root.clone(),
        ..Hooks::default()
    };
    assert_code(
        publish_with_hooks(&output, b"x", &[], &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::UnsupportedPublicationProfile,
    );
    assert!(!output.exists());

    let output = root.join("missing-proc");
    let mut hooks = Hooks {
        proc_root: root.join("missing"),
        ..Hooks::default()
    };
    assert_code(
        publish_with_hooks(&output, b"x", &[], &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::UnsupportedPublicationProfile,
    );

    let proc_link = root.join("proc-link");
    symlink("/proc", &proc_link).unwrap();
    let output = root.join("symlink-proc");
    let mut hooks = Hooks {
        proc_root: proc_link,
        ..Hooks::default()
    };
    assert_code(
        publish_with_hooks(&output, b"x", &[], &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::UnsupportedPublicationProfile,
    );

    let output = root.join("wrong-procfd");
    let mut hooks = Hooks {
        proc_source: Some("self/fd/999999999".to_string()),
        ..Hooks::default()
    };
    assert_code(
        publish_with_hooks(&output, b"x", &[], &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::UnsupportedPublicationProfile,
    );
    assert!(!output.exists());

    let output = root.join("wrong-sync-name");
    let mut hooks = Hooks {
        sync_name: PathBuf::from("missing"),
        ..Hooks::default()
    };
    assert_code(
        publish_with_hooks(&output, b"x", &[], &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::OutputPublish,
    );
    assert!(!output.exists());

    for (name, mutation) in ["mode", "length", "nlink"].into_iter().enumerate() {
        let output = root.join(format!("property-{name}"));
        let extra = root.join(format!("extra-{name}"));
        let mut hooks = Hooks {
            action: Some(Box::new(move |stage, held| {
                if stage != PublicationStageV0::TemporaryVerify {
                    return;
                }
                let held = held.unwrap();
                match mutation {
                    "mode" => fchmod(held, Mode::from_raw_mode(0o644)).unwrap(),
                    "length" => rustix::fs::ftruncate(held, 0).unwrap(),
                    "nlink" => {
                        let proc = openat(
                            rustix::fs::CWD,
                            Path::new("/proc"),
                            OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
                            Mode::empty(),
                        )
                        .unwrap();
                        linkat(
                            &proc,
                            format!("self/fd/{}", held.as_raw_fd()),
                            rustix::fs::CWD,
                            &extra,
                            AtFlags::SYMLINK_FOLLOW,
                        )
                        .unwrap();
                    }
                    _ => unreachable!(),
                }
            })),
            ..Hooks::default()
        };
        let error = publish_with_hooks(&output, b"private\n", &[], &mut hooks).unwrap_err();
        let expected = if mutation == "length" {
            AdapterErrorCodeV0::OutputPublish
        } else {
            AdapterErrorCodeV0::UnsupportedPublicationProfile
        };
        assert_code(error, expected);
        assert!(!output.exists());
    }
    let uid = rustix::process::geteuid().as_raw();
    assert!(temporary_properties_are_exact(
        FileType::RegularFile,
        uid,
        uid,
        u64::from(uid),
        0o100600,
        0,
        0,
    ));
    assert!(!temporary_properties_are_exact(
        FileType::Directory,
        uid,
        uid,
        u64::from(uid),
        0o040600,
        0,
        0,
    ));
    assert!(!temporary_properties_are_exact(
        FileType::RegularFile,
        uid,
        uid,
        u64::from(uid).saturating_add(1),
        0o100600,
        0,
        0,
    ));
    assert_code(
        publication_errno(Errno::NOTSUP, is_profile_errno(Errno::NOTSUP)),
        AdapterErrorCodeV0::UnsupportedPublicationProfile,
    );
    assert_code(
        publication_errno(Errno::IO, is_profile_errno(Errno::IO)),
        AdapterErrorCodeV0::OutputPublish,
    );
    assert_code(
        publication_errno(Errno::ACCESS, is_profile_errno(Errno::ACCESS)),
        AdapterErrorCodeV0::OutputPublish,
    );
    assert_code(
        publication_errno(Errno::NOENT, is_link_profile_errno(Errno::NOENT)),
        AdapterErrorCodeV0::OutputPublish,
    );
    for errno in [Errno::XDEV, Errno::NOTSUP, Errno::NOSYS, Errno::INVAL] {
        assert!(is_link_profile_errno(errno));
    }
    for errno in [Errno::NOENT, Errno::IO, Errno::ACCESS, Errno::PERM] {
        assert!(!is_link_profile_errno(errno));
    }
    let exact_temporary = OFlags::RDWR | OFlags::TMPFILE | OFlags::LARGEFILE;
    assert!(flags_are_exact(
        exact_temporary,
        FdFlags::CLOEXEC,
        OFlags::RDWR,
        OFlags::TMPFILE,
        OFlags::ACCMODE | OFlags::TMPFILE | OFlags::LARGEFILE,
    ));
    for extra in [OFlags::APPEND, OFlags::NONBLOCK, OFlags::NOATIME] {
        assert!(!flags_are_exact(
            exact_temporary | extra,
            FdFlags::CLOEXEC,
            OFlags::RDWR,
            OFlags::TMPFILE,
            OFlags::ACCMODE | OFlags::TMPFILE | OFlags::LARGEFILE,
        ));
    }
    assert!(!flags_are_exact(
        exact_temporary,
        FdFlags::empty(),
        OFlags::RDWR,
        OFlags::TMPFILE,
        OFlags::ACCMODE | OFlags::TMPFILE | OFlags::LARGEFILE,
    ));
    let append_temporary = openat(
        rustix::fs::CWD,
        &root,
        OFlags::TMPFILE | OFlags::RDWR | OFlags::APPEND | OFlags::CLOEXEC,
        Mode::from_raw_mode(0o600),
    )
    .unwrap();
    assert_code(
        verify_temporary_flags(&append_temporary).unwrap_err(),
        AdapterErrorCodeV0::UnsupportedPublicationProfile,
    );

    let ordinary = root.join("ordinary-file");
    fs::write(&ordinary, b"x").unwrap();
    let ordinary_fd = openat(
        rustix::fs::CWD,
        &ordinary,
        OFlags::RDONLY | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .unwrap();
    let ordinary_identity = identity(&fstat(&ordinary_fd).unwrap());
    assert_code(
        verify_sync_directory(&ordinary_fd, ordinary_identity).unwrap_err(),
        AdapterErrorCodeV0::UnsupportedPublicationProfile,
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn umask_extremes_still_publish_exact_mode_in_isolated_children() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    const CHILD: &str = "trajectory::linux_output::tests::umask_child";
    for mask in ["000", "777"] {
        let status = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", CHILD, "--ignored"])
            .env("LEGITIMACY_G3A_UMASK_CHILD", mask)
            .status()
            .unwrap();
        assert!(status.success(), "umask {mask}");
    }
}

#[test]
#[ignore]
fn umask_child() {
    let Some(mask) = std::env::var_os("LEGITIMACY_G3A_UMASK_CHILD") else {
        return;
    };
    let raw = u32::from_str_radix(mask.to_str().unwrap(), 8).unwrap();
    let root = test_root("umask-child");
    let output = root.join("bundle");
    let previous = rustix::process::umask(Mode::from_raw_mode(raw));
    let handle = publish(&output, b"x", &[]).unwrap();
    assert_eq!(
        fs::metadata(&output).unwrap().permissions().mode() & 0o7777,
        0o600
    );
    drop(handle);
    rustix::process::umask(previous);
    fs::remove_dir_all(root).unwrap();
}

fn test_root(label: &str) -> PathBuf {
    let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join(format!(
            "g3a-linux-output-{}-{label}-{sequence}",
            std::process::id()
        ));
    fs::create_dir_all(&path).unwrap();
    path
}

fn assert_directory_entries(directory: &Path, expected: &[&str]) {
    let mut actual = fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    actual.sort();
    assert_eq!(actual, expected);
}

fn assert_code(error: AdapterErrorV0, expected: AdapterErrorCodeV0) {
    assert_eq!(error.code(), expected);
}
