use super::output_set::{OutputSetHooksV0, OutputSetStageV0, publish_directory_set_with_hooks};
use super::*;
use rustix::fs::{fchmod, linkat, mkdirat, symlinkat};
use std::fs;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
static SERIAL: Mutex<()> = Mutex::new(());
type Action = Box<dyn FnMut(OutputSetStageV0, &std::ffi::OsStr, &OwnedFd)>;

#[derive(Default)]
struct Hooks {
    action: Option<Action>,
}

impl OutputSetHooksV0 for Hooks {
    fn event(&mut self, stage: OutputSetStageV0, name: &std::ffi::OsStr, staging: &OwnedFd) {
        if let Some(action) = &mut self.action {
            action(stage, name, staging);
        }
    }
}

struct RollbackHooks {
    output: PathBuf,
    stage: PublicationStageV0,
}

impl PublicationHooksV0 for RollbackHooks {
    fn fail_before(&mut self, stage: PublicationStageV0, _held: Option<&OwnedFd>) -> bool {
        if stage == self.stage {
            let target = if stage == PublicationStageV0::RollbackQuarantine {
                self.output.clone()
            } else {
                fs::read_dir(self.output.parent().unwrap())
                    .unwrap()
                    .map(|entry| entry.unwrap().path())
                    .find(|path| {
                        path.file_name().is_some_and(|name| {
                            name.as_bytes().starts_with(b".rollback-")
                                && name.as_bytes().ends_with(b".quarantine")
                        })
                    })
                    .unwrap()
            };
            fs::remove_file(&target).unwrap();
            fs::write(&target, b"replacement").unwrap();
            fs::set_permissions(&target, fs::Permissions::from_mode(0o600)).unwrap();
        }
        false
    }
}

const MEMBERS: &[(&str, &[u8])] = &[
    ("trace.json", b"trace"),
    ("canonical-trace.bin", b"canonical"),
    ("composition-result.json", b"result"),
];

#[test]
fn ancestor_substitution_cannot_redirect_descriptor_relative_member_writes() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("ancestor");
    let ancestor = root.join("ancestor");
    let moved = root.join("moved");
    fs::create_dir(&ancestor).unwrap();
    let output = ancestor.join("package");
    let hook_ancestor = ancestor.clone();
    let hook_moved = moved.clone();
    let mut hooks = Hooks {
        action: Some(Box::new(move |stage, name, _| {
            if stage == OutputSetStageV0::StagingOpened {
                fs::rename(&hook_ancestor, &hook_moved).unwrap();
                fs::create_dir(&hook_ancestor).unwrap();
                fs::create_dir(hook_ancestor.join(name)).unwrap();
                fs::set_permissions(hook_ancestor.join(name), fs::Permissions::from_mode(0o700))
                    .unwrap();
            }
        })),
    };
    publish_directory_set_with_hooks(&output, MEMBERS, &[], &mut hooks, || Ok(())).unwrap();
    assert!(!output.exists());
    assert_eq!(
        fs::read(moved.join("package/trace.json")).unwrap(),
        b"trace"
    );
    let substitute = fs::read_dir(&ancestor)
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    assert!(fs::read_dir(substitute).unwrap().next().is_none());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn member_replacement_after_publication_is_never_accepted_or_deleted() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("member-replacement");
    let output = root.join("package");
    let mut hooks = mutate_member_hooks(MemberAttack::ChangedContent);
    assert_code(
        publish_directory_set_with_hooks(&output, MEMBERS, &[], &mut hooks, || Ok(())).unwrap_err(),
        AdapterErrorCodeV0::OutputRollbackUncertain,
    );
    assert!(!output.exists());
    assert!(find_staging(&root).join("trace.json").exists());
    assert_eq!(
        fs::read(find_staging(&root).join("trace.json")).unwrap(),
        b"other"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn member_replacement_after_final_proof_cannot_be_committed() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("final-proof-member-replacement");
    let output = root.join("package");
    let mut hooks = Hooks {
        action: Some(Box::new(move |stage, _, staging| {
            if stage == OutputSetStageV0::FinalProofComplete {
                let held = open_member(staging, "trace.json", OFlags::WRONLY | OFlags::TRUNC);
                rustix::io::write(&held, b"late-mutant").unwrap();
            }
        })),
    };
    assert_code(
        publish_directory_set_with_hooks(&output, MEMBERS, &[], &mut hooks, || Ok(())).unwrap_err(),
        AdapterErrorCodeV0::OutputRollbackUncertain,
    );
    assert!(!output.exists());
    assert_eq!(
        fs::read(find_staging(&root).join("trace.json")).unwrap(),
        b"late-mutant"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn staging_name_substitution_and_wrong_directory_mode_fail_uncertain() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    for attack in [DirectoryAttack::Substitute, DirectoryAttack::WrongMode] {
        let root = test_root("staging-identity");
        let output = root.join("package");
        let hook_root = root.clone();
        let mut hooks = Hooks {
            action: Some(Box::new(move |stage, name, staging| {
                if stage != OutputSetStageV0::BeforeRename {
                    return;
                }
                match attack {
                    DirectoryAttack::Substitute => {
                        fs::rename(hook_root.join(name), hook_root.join("moved-staging")).unwrap();
                        fs::create_dir(hook_root.join(name)).unwrap();
                        fs::set_permissions(
                            hook_root.join(name),
                            fs::Permissions::from_mode(0o700),
                        )
                        .unwrap();
                        fs::write(hook_root.join(name).join("replacement"), b"keep").unwrap();
                    }
                    DirectoryAttack::WrongMode => {
                        fchmod(staging, Mode::from_raw_mode(0o755)).unwrap();
                    }
                }
            })),
        };
        assert_code(
            publish_directory_set_with_hooks(&output, MEMBERS, &[], &mut hooks, || Ok(()))
                .unwrap_err(),
            AdapterErrorCodeV0::OutputRollbackUncertain,
        );
        assert!(!output.exists());
        if attack == DirectoryAttack::Substitute {
            assert_eq!(
                fs::read(find_staging(&root).join("replacement")).unwrap(),
                b"keep"
            );
        }
        fs::remove_dir_all(root).unwrap();
    }
}

#[test]
fn cleanup_substitution_preserves_the_empty_replacement() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("cleanup-substitution");
    let output = root.join("package");
    let hook_root = root.clone();
    let mut hooks = Hooks {
        action: Some(Box::new(move |stage, name, _| {
            if stage == OutputSetStageV0::CleanupBeforeFinalProof {
                fs::rename(hook_root.join(name), hook_root.join("moved-original")).unwrap();
                fs::create_dir(hook_root.join(name)).unwrap();
                fs::set_permissions(hook_root.join(name), fs::Permissions::from_mode(0o700))
                    .unwrap();
            }
        })),
    };
    assert_code(
        publish_directory_set_with_hooks(&output, MEMBERS, &[], &mut hooks, || {
            Err(error(AdapterErrorCodeV0::BundleMismatch))
        })
        .unwrap_err(),
        AdapterErrorCodeV0::OutputRollbackUncertain,
    );
    assert!(!output.exists());
    assert!(fs::read_dir(find_staging(&root)).unwrap().next().is_none());
    assert!(
        fs::read_dir(root.join("moved-original"))
            .unwrap()
            .next()
            .is_none()
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn hostile_member_type_mode_link_and_content_matrix_fails_closed() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    for attack in [
        MemberAttack::Symlink,
        MemberAttack::HardLink,
        MemberAttack::WrongType,
        MemberAttack::WrongMode,
        MemberAttack::LinkCount,
        MemberAttack::ChangedContent,
    ] {
        let root = test_root("member-matrix");
        let output = root.join("package");
        let mut hooks = mutate_member_hooks(attack);
        assert_code(
            publish_directory_set_with_hooks(&output, MEMBERS, &[], &mut hooks, || Ok(()))
                .unwrap_err(),
            AdapterErrorCodeV0::OutputRollbackUncertain,
        );
        assert!(!output.exists(), "{attack:?}");
        fs::remove_dir_all(root).unwrap();
    }
}

#[test]
fn changed_input_cleanup_failure_and_final_incumbent_are_distinct() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("late-schedules");
    let input = root.join("input");
    fs::write(&input, b"input").unwrap();
    let snapshot = crate::trajectory::linux_path::read_snapshot(&input, 16).unwrap();
    let hook_input = input.clone();
    let mut changed = Hooks {
        action: Some(Box::new(move |stage, _, _| {
            if stage == OutputSetStageV0::BeforeRename {
                fs::write(&hook_input, b"other").unwrap();
            }
        })),
    };
    assert_code(
        publish_directory_set_with_hooks(
            &root.join("changed"),
            MEMBERS,
            &[&snapshot],
            &mut changed,
            || Ok(()),
        )
        .unwrap_err(),
        AdapterErrorCodeV0::InputChanged,
    );
    drop(snapshot);

    let incumbent = root.join("incumbent");
    let hook_incumbent = incumbent.clone();
    let mut incumbent_hooks = Hooks {
        action: Some(Box::new(move |stage, _, _| {
            if stage == OutputSetStageV0::BeforeRename {
                fs::write(&hook_incumbent, b"keep").unwrap();
            }
        })),
    };
    assert_code(
        publish_directory_set_with_hooks(&incumbent, MEMBERS, &[], &mut incumbent_hooks, || Ok(()))
            .unwrap_err(),
        AdapterErrorCodeV0::OutputExists,
    );
    assert_eq!(fs::read(&incumbent).unwrap(), b"keep");

    let cleanup = root.join("cleanup");
    let mut cleanup_hooks = Hooks {
        action: Some(Box::new(move |stage, _, staging| {
            if stage == OutputSetStageV0::BeforeCleanup {
                fchmod(staging, Mode::from_raw_mode(0o500)).unwrap();
            }
        })),
    };
    assert_code(
        publish_directory_set_with_hooks(&cleanup, MEMBERS, &[], &mut cleanup_hooks, || {
            Err(error(AdapterErrorCodeV0::BundleMismatch))
        })
        .unwrap_err(),
        AdapterErrorCodeV0::OutputRollbackUncertain,
    );
    fs::set_permissions(find_staging(&root), fs::Permissions::from_mode(0o700)).unwrap();
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn rollback_race_quarantines_and_never_deletes_the_replacement() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("rollback-quarantine");
    let output = root.join("output");
    let committed = publish(&output, b"original", &[]).unwrap();
    let mut hooks = RollbackHooks {
        output: output.clone(),
        stage: PublicationStageV0::RollbackQuarantine,
    };
    assert_code(
        rollback_committed_with_hooks(committed, b"original", &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::OutputRollbackUncertain,
    );
    assert!(!output.exists());
    let quarantine = fs::read_dir(&root).unwrap().next().unwrap().unwrap().path();
    assert_eq!(fs::read(quarantine).unwrap(), b"replacement");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn quarantine_substitution_after_validation_is_never_unlinked() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("rollback-before-unlink");
    let output = root.join("output");
    let committed = publish(&output, b"original", &[]).unwrap();
    let mut hooks = RollbackHooks {
        output: output.clone(),
        stage: PublicationStageV0::RollbackBeforeUnlink,
    };
    assert_code(
        rollback_committed_with_hooks(committed, b"original", &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::OutputRollbackUncertain,
    );
    assert!(!output.exists());
    let quarantine = fs::read_dir(&root).unwrap().next().unwrap().unwrap().path();
    assert_eq!(fs::read(quarantine).unwrap(), b"replacement");
    fs::remove_dir_all(root).unwrap();
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DirectoryAttack {
    Substitute,
    WrongMode,
}

#[derive(Clone, Copy, Debug)]
enum MemberAttack {
    Symlink,
    HardLink,
    WrongType,
    WrongMode,
    LinkCount,
    ChangedContent,
}

fn mutate_member_hooks(attack: MemberAttack) -> Hooks {
    Hooks {
        action: Some(Box::new(move |stage, _, staging| {
            if stage != OutputSetStageV0::MembersPublished {
                return;
            }
            match attack {
                MemberAttack::Symlink => {
                    unlinkat(staging, "trace.json", AtFlags::empty()).unwrap();
                    symlinkat("canonical-trace.bin", staging, "trace.json").unwrap();
                }
                MemberAttack::HardLink => {
                    unlinkat(staging, "trace.json", AtFlags::empty()).unwrap();
                    linkat(
                        staging,
                        "canonical-trace.bin",
                        staging,
                        "trace.json",
                        AtFlags::empty(),
                    )
                    .unwrap();
                }
                MemberAttack::WrongType => {
                    unlinkat(staging, "trace.json", AtFlags::empty()).unwrap();
                    mkdirat(staging, "trace.json", Mode::from_raw_mode(0o700)).unwrap();
                }
                MemberAttack::WrongMode => {
                    let held = open_member(staging, "trace.json", OFlags::RDONLY);
                    fchmod(&held, Mode::from_raw_mode(0o400)).unwrap();
                }
                MemberAttack::LinkCount => {
                    linkat(
                        staging,
                        "trace.json",
                        staging,
                        "extra-link",
                        AtFlags::empty(),
                    )
                    .unwrap();
                }
                MemberAttack::ChangedContent => {
                    let held = open_member(staging, "trace.json", OFlags::WRONLY | OFlags::TRUNC);
                    rustix::io::write(&held, b"other").unwrap();
                }
            }
        })),
    }
}

fn open_member(directory: &OwnedFd, name: &str, flags: OFlags) -> OwnedFd {
    openat(
        directory,
        name,
        flags | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .unwrap()
}

fn find_staging(root: &Path) -> PathBuf {
    fs::read_dir(root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .find(|path| {
            path.file_name()
                .is_some_and(|name| name.as_bytes().starts_with(b".legitimacy-output-set-"))
        })
        .unwrap()
}

fn test_root(label: &str) -> PathBuf {
    let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
    let root = Path::new("target").join(format!(
        "g3b-output-set-{}-{label}-{sequence}",
        std::process::id()
    ));
    fs::create_dir_all(&root).unwrap();
    root
}

fn assert_code(error: AdapterErrorV0, expected: AdapterErrorCodeV0) {
    assert_eq!(error.code(), expected);
}
