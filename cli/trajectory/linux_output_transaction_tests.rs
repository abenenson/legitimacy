use super::*;
use std::cell::Cell;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::os::unix::ffi::OsStringExt;
use std::os::unix::fs::{MetadataExt, PermissionsExt, symlink};
use std::path::PathBuf;
use std::rc::Rc;

use phase_tests::{Mutation, mutate};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
static SERIAL: Mutex<()> = Mutex::new(());
type StageAction = Box<dyn FnMut(PublicationStageV0, Option<&OwnedFd>)>;

#[derive(Default)]
struct Hooks {
    events: Vec<PublicationEventV0>,
    fail: Option<PublicationStageV0>,
    action: Option<StageAction>,
    after_complete: Option<StageAction>,
}

impl PublicationHooksV0 for Hooks {
    fn event(&mut self, event: PublicationEventV0, held: Option<&OwnedFd>) {
        self.events.push(event);
        if let PublicationEventV0::Completed(stage) = event
            && let Some(action) = &mut self.after_complete
        {
            action(stage, held);
        }
    }

    fn fail_before(&mut self, stage: PublicationStageV0, held: Option<&OwnedFd>) -> bool {
        if let Some(action) = &mut self.action {
            action(stage, held);
        }
        self.fail == Some(stage)
    }
}

#[derive(Clone, Copy, Debug)]
enum Role {
    Sidecar,
    Public,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Incumbent {
    Ordinary,
    Symlink,
    Input(usize),
    Sidecar,
}

const SIDECAR_BYTES: &[u8] = b"owner-private-sidecar";
const PUBLIC_BYTES: &[u8] = b"{\"shareable\":true}\n";

#[test]
fn complete_set_rolls_back_late_failure_and_changed_snapshot() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("set-rollback");
    let outputs = [
        root.join("trace"),
        root.join("canonical"),
        root.join("result"),
    ];
    let specs = [
        PublicationSpecV0 {
            output: &outputs[0],
            bytes: b"trace",
        },
        PublicationSpecV0 {
            output: &outputs[1],
            bytes: b"canonical",
        },
        PublicationSpecV0 {
            output: &outputs[2],
            bytes: b"result",
        },
    ];
    assert_code(
        publish_set(&specs, &[], || {
            Err(error(AdapterErrorCodeV0::BundleMismatch))
        })
        .unwrap_err(),
        AdapterErrorCodeV0::BundleMismatch,
    );
    assert!(outputs.iter().all(|path| !path.exists()));

    let input = root.join("input");
    fs::write(&input, b"input").unwrap();
    let snapshot = crate::trajectory::linux_path::read_snapshot(&input, 16).unwrap();
    assert_code(
        publish_set(&specs, &[&snapshot], || {
            fs::write(&input, b"other").unwrap();
            Ok(())
        })
        .unwrap_err(),
        AdapterErrorCodeV0::InputChanged,
    );
    assert!(outputs.iter().all(|path| !path.exists()));
    drop(snapshot);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn rollback_identity_failure_is_visible_and_never_deletes_a_replacement() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("set-rollback-uncertain");
    let outputs = [
        root.join("trace"),
        root.join("canonical"),
        root.join("result"),
    ];
    let specs = [
        PublicationSpecV0 {
            output: &outputs[0],
            bytes: b"trace",
        },
        PublicationSpecV0 {
            output: &outputs[1],
            bytes: b"canonical",
        },
        PublicationSpecV0 {
            output: &outputs[2],
            bytes: b"result",
        },
    ];
    assert_code(
        publish_set(&specs, &[], || {
            fs::remove_file(&outputs[0]).unwrap();
            fs::write(&outputs[0], b"replacement").unwrap();
            fs::set_permissions(&outputs[0], fs::Permissions::from_mode(0o600)).unwrap();
            Err(error(AdapterErrorCodeV0::BundleMismatch))
        })
        .unwrap_err(),
        AdapterErrorCodeV0::OutputRollbackUncertain,
    );
    assert_eq!(fs::read(&outputs[0]).unwrap(), b"replacement");
    assert!(!outputs[1].exists());
    assert!(!outputs[2].exists());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn directory_set_has_one_final_namespace_commit_point() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("directory-set");
    let output_set = root.join("package");
    let verifier_called = Cell::new(false);
    publish_directory_set(
        &output_set,
        &[
            ("trace.json", b"trace"),
            ("canonical-trace.bin", b"canonical"),
            ("composition-result.json", b"result"),
        ],
        &[],
        || {
            verifier_called.set(true);
            assert!(!output_set.exists());
            Ok(())
        },
    )
    .unwrap();
    assert!(verifier_called.get());
    assert_eq!(fs::read(output_set.join("trace.json")).unwrap(), b"trace");
    assert_eq!(
        fs::read(output_set.join("canonical-trace.bin")).unwrap(),
        b"canonical"
    );
    assert_eq!(
        fs::read(output_set.join("composition-result.json")).unwrap(),
        b"result"
    );
    let staging = fs::read_dir(&root)
        .unwrap()
        .filter_map(|entry| entry.ok())
        .filter(|entry| entry.file_name().to_string_lossy().contains("staging"))
        .count();
    assert_eq!(staging, 0);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn pair_success_is_exact_and_handles_are_redacted_and_live() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("success");
    let sidecar = root.join("lineage.bin");
    let public = root.join("bundle.jsonl");
    let mut sidecar_hooks = Hooks::default();
    let mut public_hooks = Hooks::default();
    let (sidecar_handle, public_handle) =
        pair(&sidecar, &public, &mut sidecar_hooks, &mut public_hooks).unwrap();
    assert_success_link_events(&sidecar_hooks);
    assert_success_link_events(&public_hooks);
    for (path, expected) in [(&sidecar, SIDECAR_BYTES), (&public, PUBLIC_BYTES)] {
        let metadata = fs::metadata(path).unwrap();
        assert_eq!(fs::read(path).unwrap(), expected);
        assert_eq!(metadata.mode() & 0o7777, 0o600);
        assert_eq!(metadata.uid(), rustix::process::geteuid().as_raw());
        assert_eq!(metadata.nlink(), 1);
    }
    let mut inventory: Vec<_> = fs::read_dir(&root)
        .unwrap()
        .map(|entry| entry.unwrap().file_name())
        .collect();
    inventory.sort();
    assert_eq!(
        inventory,
        vec![
            std::ffi::OsString::from("bundle.jsonl"),
            std::ffi::OsString::from("lineage.bin"),
        ]
    );
    assert_eq!(
        format!("{sidecar_handle:?}"),
        "CommittedPublicationV0(redacted)"
    );
    assert_eq!(
        format!("{public_handle:?}"),
        "CommittedPublicationV0(redacted)"
    );
    fs::remove_file(&sidecar).unwrap();
    fs::remove_file(&public).unwrap();
    let mut byte = [0_u8; 1];
    assert_eq!(
        rustix::io::pread(&sidecar_handle.held, &mut byte, 0).unwrap(),
        1
    );
    assert_eq!(
        rustix::io::pread(&public_handle.held, &mut byte, 0).unwrap(),
        1
    );
    drop(public_handle);
    drop(sidecar_handle);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn equivalent_destinations_and_each_input_alias_fail_before_publication() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("aliases");
    let absolute = fs::canonicalize(&root).unwrap().join("same");
    let relative = root.join("same");
    let repeated = PathBuf::from(format!("{}/./same", root.display()));
    let doubled = PathBuf::from(format!("{}//same", root.display()));
    for (index, (sidecar, public)) in [
        (absolute.clone(), relative.clone()),
        (relative.clone(), repeated),
        (relative.clone(), doubled),
    ]
    .into_iter()
    .enumerate()
    {
        assert_code(
            pair(
                &sidecar,
                &public,
                &mut Hooks::default(),
                &mut Hooks::default(),
            )
            .unwrap_err(),
            AdapterErrorCodeV0::CrossOutputAlias,
        );
        assert!(!relative.exists(), "case {index}");
    }
    let non_utf8 = std::ffi::OsString::from_vec(vec![b'n', 0x80]);
    let non_utf8_path = root.join(&non_utf8);
    let non_utf8_alias = root.join(".").join(&non_utf8);
    assert_code(
        pair(
            &non_utf8_path,
            &non_utf8_alias,
            &mut Hooks::default(),
            &mut Hooks::default(),
        )
        .unwrap_err(),
        AdapterErrorCodeV0::CrossOutputAlias,
    );

    let input = root.join("input");
    fs::write(&input, b"input").unwrap();
    let snapshot = crate::trajectory::linux_path::read_snapshot(&input, 16).unwrap();
    for role in [Role::Sidecar, Role::Public] {
        let sidecar = root.join(format!("sidecar-{}", role_label(role)));
        let public = root.join(format!("public-{}", role_label(role)));
        let alias = match role {
            Role::Sidecar => &sidecar,
            Role::Public => &public,
        };
        fs::hard_link(&input, alias).unwrap();
        let error = publish_pair_with_hooks(
            spec(&sidecar, SIDECAR_BYTES),
            spec(&public, PUBLIC_BYTES),
            &[&snapshot],
            &mut Hooks::default(),
            &mut Hooks::default(),
            || Ok(()),
        )
        .unwrap_err();
        assert_code(error, AdapterErrorCodeV0::InputAlias);
        assert_eq!(fs::read(alias).unwrap(), b"input");
        fs::remove_file(alias).unwrap();
    }
    drop(snapshot);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn semantic_validation_is_once_at_entry_and_precedes_all_filesystem_work() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("semantic-entry");
    let sidecar = root.join("sidecar");
    let public = root.join("public");
    let calls = Cell::new(0);
    let mut sidecar_hooks = Hooks::default();
    let mut public_hooks = Hooks::default();
    let result = publish_pair_with_hooks(
        spec(&sidecar, SIDECAR_BYTES),
        spec(&public, PUBLIC_BYTES),
        &[],
        &mut sidecar_hooks,
        &mut public_hooks,
        || {
            calls.set(calls.get() + 1);
            Err(error(AdapterErrorCodeV0::BundleMismatch))
        },
    );
    assert_code(result.unwrap_err(), AdapterErrorCodeV0::BundleMismatch);
    assert_eq!(calls.get(), 1);
    assert!(sidecar_hooks.events.is_empty());
    assert!(public_hooks.events.is_empty());
    assert!(!sidecar.exists());
    assert!(!public.exists());

    let calls = Cell::new(0);
    let (sidecar_handle, public_handle) = publish_pair_with_hooks(
        spec(&sidecar, SIDECAR_BYTES),
        spec(&public, PUBLIC_BYTES),
        &[],
        &mut Hooks::default(),
        &mut Hooks::default(),
        || {
            calls.set(calls.get() + 1);
            Ok(())
        },
    )
    .unwrap();
    assert_eq!(calls.get(), 1);
    drop(public_handle);
    drop(sidecar_handle);
    fs::remove_file(&public).unwrap();
    fs::remove_file(&sidecar).unwrap();

    let calls = Cell::new(0);
    let mut public_hooks = Hooks {
        fail: Some(PublicationStageV0::PostLinkDirectorySync),
        ..Hooks::default()
    };
    let result = publish_pair_with_hooks(
        spec(&sidecar, SIDECAR_BYTES),
        spec(&public, PUBLIC_BYTES),
        &[],
        &mut Hooks::default(),
        &mut public_hooks,
        || {
            calls.set(calls.get() + 1);
            Ok(())
        },
    );
    assert_code(result.unwrap_err(), AdapterErrorCodeV0::DurabilityUncertain);
    assert_eq!(calls.get(), 1);
    assert!(sidecar.exists());
    assert!(public.exists());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn byte_identical_output_paths_are_rejected_before_preparation() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("raw-alias");
    let output = root.join("missing-parent").join("same");
    let calls = Cell::new(0);
    let mut sidecar_hooks = Hooks::default();
    let mut public_hooks = Hooks::default();
    let result = publish_pair_with_hooks(
        spec(&output, SIDECAR_BYTES),
        spec(&output, PUBLIC_BYTES),
        &[],
        &mut sidecar_hooks,
        &mut public_hooks,
        || {
            calls.set(calls.get() + 1);
            Ok(())
        },
    );
    assert_code(result.unwrap_err(), AdapterErrorCodeV0::CrossOutputAlias);
    assert_eq!(calls.get(), 1);
    assert!(sidecar_hooks.events.is_empty());
    assert!(public_hooks.events.is_empty());
    assert!(!output.exists());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn public_link_race_to_live_sidecar_is_cross_output_alias_before_guard() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("link-race");
    let sidecar = root.join("sidecar");
    let public = root.join("public");
    let race_sidecar = sidecar.clone();
    let race_public = public.clone();
    let mut public_hooks = Hooks {
        action: Some(Box::new(move |stage, _| {
            if stage == PublicationStageV0::Link {
                fs::hard_link(&race_sidecar, &race_public).unwrap();
            }
        })),
        ..Hooks::default()
    };
    let error = pair(&sidecar, &public, &mut Hooks::default(), &mut public_hooks).unwrap_err();
    assert_code(error, AdapterErrorCodeV0::CrossOutputAlias);
    assert_eq!(
        fs::metadata(&sidecar).unwrap().ino(),
        fs::metadata(&public).unwrap().ino()
    );
    assert!(
        !public_hooks.events.contains(&PublicationEventV0::Attempted(
            PublicationStageV0::ProtectedGuard
        ))
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn actual_linkat_eexist_classifies_every_incumbent_without_clobbering() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    for incumbent in [
        Incumbent::Ordinary,
        Incumbent::Symlink,
        Incumbent::Input(0),
        Incumbent::Input(1),
        Incumbent::Input(2),
        Incumbent::Sidecar,
    ] {
        let root = test_root("real-eexist");
        let sidecar = root.join("sidecar");
        let public = root.join("public");
        let input_paths = [
            root.join("raw-input"),
            root.join("receipt-input"),
            root.join("context-input"),
        ];
        for (index, input) in input_paths.iter().enumerate() {
            fs::write(input, format!("input-{index}")).unwrap();
        }
        let snapshots: Vec<_> = input_paths
            .iter()
            .map(|input| crate::trajectory::linux_path::read_snapshot(input, 32).unwrap())
            .collect();
        let inputs: Vec<_> = snapshots.iter().collect();
        let action_public = public.clone();
        let action_inputs = input_paths.clone();
        let after_guard_sidecar = sidecar.clone();
        let after_guard_public = public.clone();
        let mut public_hooks = Hooks {
            action: Some(Box::new(move |stage, _| {
                if stage != PublicationStageV0::RealLink {
                    return;
                }
                match incumbent {
                    Incumbent::Ordinary => fs::write(&action_public, b"incumbent").unwrap(),
                    Incumbent::Symlink => {
                        symlink("missing-target", &action_public).unwrap();
                    }
                    Incumbent::Input(index) => {
                        fs::hard_link(&action_inputs[index], &action_public).unwrap();
                    }
                    Incumbent::Sidecar => {}
                }
            })),
            after_complete: Some(Box::new(move |stage, _| {
                if incumbent == Incumbent::Sidecar && stage == PublicationStageV0::ProtectedGuard {
                    fs::hard_link(&after_guard_sidecar, &after_guard_public).unwrap();
                }
            })),
            ..Hooks::default()
        };
        let result = publish_pair_with_hooks(
            spec(&sidecar, SIDECAR_BYTES),
            spec(&public, PUBLIC_BYTES),
            &inputs,
            &mut Hooks::default(),
            &mut public_hooks,
            || Ok(()),
        );
        let expected = match incumbent {
            Incumbent::Ordinary => AdapterErrorCodeV0::OutputExists,
            Incumbent::Symlink => AdapterErrorCodeV0::OutputSymlink,
            Incumbent::Input(_) => AdapterErrorCodeV0::InputAlias,
            Incumbent::Sidecar => AdapterErrorCodeV0::CrossOutputAlias,
        };
        assert_code(result.unwrap_err(), expected);
        assert!(sidecar.exists(), "{incumbent:?}");
        assert_eexist_link_events(&public_hooks, true);
        match incumbent {
            Incumbent::Ordinary => assert_eq!(fs::read(&public).unwrap(), b"incumbent"),
            Incumbent::Symlink => {
                assert_eq!(fs::read_link(&public).unwrap(), Path::new("missing-target"));
            }
            Incumbent::Input(index) => {
                assert_eq!(
                    fs::symlink_metadata(&public).unwrap().ino(),
                    fs::metadata(&input_paths[index]).unwrap().ino()
                );
            }
            Incumbent::Sidecar => {
                assert_eq!(
                    fs::metadata(&public).unwrap().ino(),
                    fs::metadata(&sidecar).unwrap().ino()
                );
            }
        }
        drop(snapshots);
        fs::remove_dir_all(root).unwrap();
    }
}

#[test]
fn incumbent_disappearance_and_swap_are_classified_from_the_live_name() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("eexist-disappear");
    let sidecar = root.join("sidecar");
    let public = root.join("public");
    let action_public = public.clone();
    let mut public_hooks = Hooks {
        action: Some(Box::new(move |stage, _| match stage {
            PublicationStageV0::RealLink => fs::write(&action_public, b"incumbent").unwrap(),
            PublicationStageV0::IncumbentClassify => {
                fs::remove_file(&action_public).unwrap();
            }
            _ => {}
        })),
        ..Hooks::default()
    };
    let result = pair(&sidecar, &public, &mut Hooks::default(), &mut public_hooks);
    assert_code(result.unwrap_err(), AdapterErrorCodeV0::OutputPublish);
    assert!(sidecar.exists());
    assert!(!public.exists());
    assert_eexist_link_events(&public_hooks, true);
    fs::remove_dir_all(root).unwrap();

    let root = test_root("eexist-swap");
    let sidecar = root.join("sidecar");
    let public = root.join("public");
    let action_public = public.clone();
    let mut public_hooks = Hooks {
        action: Some(Box::new(move |stage, _| match stage {
            PublicationStageV0::RealLink => {
                fs::write(&action_public, b"incumbent").unwrap();
            }
            PublicationStageV0::IncumbentClassify => {
                fs::remove_file(&action_public).unwrap();
                fs::write(&action_public, b"swapped").unwrap();
            }
            _ => {}
        })),
        ..Hooks::default()
    };
    let result = pair(&sidecar, &public, &mut Hooks::default(), &mut public_hooks);
    assert_code(result.unwrap_err(), AdapterErrorCodeV0::OutputExists);
    assert_eq!(fs::read(&public).unwrap(), b"swapped");
    assert_eq!(fs::metadata(&sidecar).unwrap().nlink(), 1);
    assert_eexist_link_events(&public_hooks, true);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn cross_output_alias_precedence_is_explicit_when_sidecar_is_also_corrupt() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("cross-precedence");
    let sidecar = root.join("sidecar");
    let public = root.join("public");
    let action_sidecar = sidecar.clone();
    let action_public = public.clone();
    let mut public_hooks = Hooks {
        after_complete: Some(Box::new(move |stage, _| {
            if stage == PublicationStageV0::ProtectedGuard {
                fs::hard_link(&action_sidecar, &action_public).unwrap();
                OpenOptions::new()
                    .append(true)
                    .open(&action_sidecar)
                    .unwrap()
                    .write_all(b"x")
                    .unwrap();
            }
        })),
        ..Hooks::default()
    };
    let result = pair(&sidecar, &public, &mut Hooks::default(), &mut public_hooks);
    assert_code(result.unwrap_err(), AdapterErrorCodeV0::CrossOutputAlias);
    let sidecar_metadata = fs::metadata(&sidecar).unwrap();
    assert_eq!(sidecar_metadata.nlink(), 2);
    assert_eq!(sidecar_metadata.ino(), fs::metadata(&public).unwrap().ino());
    assert_eq!(fs::read(&sidecar).unwrap(), [SIDECAR_BYTES, b"x"].concat());
    assert_eexist_link_events(&public_hooks, true);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn external_content_mutation_after_guard_can_link_but_final_revalidation_fails_closed() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("after-guard-content");
    let sidecar = root.join("sidecar");
    let public = root.join("public");
    let action_sidecar = sidecar.clone();
    let mut sidecar_hooks = Hooks::default();
    let mut public_hooks = Hooks {
        after_complete: Some(Box::new(move |stage, _| {
            if stage == PublicationStageV0::ProtectedGuard {
                OpenOptions::new()
                    .append(true)
                    .open(&action_sidecar)
                    .unwrap()
                    .write_all(b"x")
                    .unwrap();
            }
        })),
        ..Hooks::default()
    };
    let result = pair(&sidecar, &public, &mut sidecar_hooks, &mut public_hooks);
    assert_code(
        result.unwrap_err(),
        AdapterErrorCodeV0::OutputIdentityUncertain,
    );
    assert_eq!(fs::read(&sidecar).unwrap(), [SIDECAR_BYTES, b"x"].concat());
    assert_eq!(fs::read(&public).unwrap(), PUBLIC_BYTES);
    assert_success_link_events(&public_hooks);
    assert_eq!(
        sidecar_hooks
            .events
            .iter()
            .filter(|event| {
                **event
                    == PublicationEventV0::Attempted(
                        PublicationStageV0::CommittedIdentityRevalidate,
                    )
            })
            .count(),
        2
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn sidecar_mutations_before_and_after_public_link_fail_closed() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    for timing in [
        PublicationStageV0::Link,
        PublicationStageV0::RealLink,
        PublicationStageV0::PostLinkSourceVerify,
    ] {
        for mutation in [
            Mutation::Append,
            Mutation::Truncate,
            Mutation::Overwrite,
            Mutation::Chmod,
            Mutation::AddLink,
            Mutation::Unlink,
            Mutation::Replace,
        ] {
            let root = test_root("sidecar-mutation");
            let sidecar = root.join("sidecar");
            let public = root.join("public");
            let action_root = root.clone();
            let action_sidecar = sidecar.clone();
            let expected_code = Rc::new(Cell::new(None));
            let observed_code = expected_code.clone();
            let mut public_hooks = Hooks {
                action: Some(Box::new(move |stage, _| {
                    if stage == timing {
                        let expected = mutate(&action_root, &action_sidecar, mutation);
                        assert!(observed_code.replace(Some(expected)).is_none());
                    }
                })),
                ..Hooks::default()
            };
            let error =
                pair(&sidecar, &public, &mut Hooks::default(), &mut public_hooks).unwrap_err();
            assert_eq!(
                error.code(),
                expected_code.get().expect("mutation hook did not run"),
                "{timing:?} {mutation:?}"
            );
            if matches!(
                timing,
                PublicationStageV0::Link | PublicationStageV0::RealLink
            ) {
                assert!(!public.exists());
            } else {
                assert!(public.exists());
            }
            fs::remove_dir_all(root).unwrap();
        }
    }
}

#[test]
fn sidecar_committed_uncertainty_dominates_public_prelink_and_all_postchecks_run() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("precedence");
    let sidecar = root.join("sidecar");
    let public = root.join("public");
    let action_sidecar = sidecar.clone();
    let mut public_hooks = Hooks {
        fail: Some(PublicationStageV0::CommitEuidVerify),
        action: Some(Box::new(move |stage, _| {
            if stage == PublicationStageV0::CommitEuidVerify {
                OpenOptions::new()
                    .append(true)
                    .open(&action_sidecar)
                    .unwrap()
                    .write_all(b"x")
                    .unwrap();
            }
        })),
        ..Hooks::default()
    };
    let error = pair(&sidecar, &public, &mut Hooks::default(), &mut public_hooks).unwrap_err();
    assert_code(error, AdapterErrorCodeV0::OutputIdentityUncertain);
    assert!(sidecar.exists());
    assert!(!public.exists());
    fs::remove_dir_all(root).unwrap();

    let root = test_root("all-postchecks");
    let sidecar = root.join("sidecar");
    let public = root.join("public");
    let action_public = public.clone();
    let mut public_hooks = Hooks {
        fail: Some(PublicationStageV0::PostLinkDirectorySync),
        action: Some(Box::new(move |stage, _| match stage {
            PublicationStageV0::HeldIntegrityVerify => {
                OpenOptions::new()
                    .append(true)
                    .open(&action_public)
                    .unwrap()
                    .write_all(b"x")
                    .unwrap();
            }
            PublicationStageV0::FinalIdentityVerify => {
                fs::remove_file(&action_public).unwrap();
            }
            _ => {}
        })),
        ..Hooks::default()
    };
    let error = pair(&sidecar, &public, &mut Hooks::default(), &mut public_hooks).unwrap_err();
    assert_code(error, AdapterErrorCodeV0::OutputIdentityUncertain);
    for stage in [
        PublicationStageV0::PostLinkSourceVerify,
        PublicationStageV0::PostLinkDirectorySync,
        PublicationStageV0::HeldIntegrityVerify,
        PublicationStageV0::FinalIdentityVerify,
        PublicationStageV0::CommittedEuidRevalidate,
        PublicationStageV0::CommittedIntegrityRevalidate,
        PublicationStageV0::CommittedIdentityRevalidate,
    ] {
        assert!(
            public_hooks
                .events
                .contains(&PublicationEventV0::Attempted(stage)),
            "{stage:?}"
        );
    }
    assert!(sidecar.exists());
    assert!(!public.exists());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn prepared_parent_observe_open_and_post_pin_rename_schedules_are_role_exact() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    for role in [Role::Sidecar, Role::Public] {
        let root = test_root("ancestor-swap");
        let moved = root.with_extension("moved");
        let action_root = root.clone();
        let action_moved = moved.clone();
        let action = Box::new(move |stage, _held: Option<&OwnedFd>| {
            if stage == PublicationStageV0::AncestorOpen(1) {
                fs::rename(&action_root, &action_moved).unwrap();
                fs::create_dir(&action_root).unwrap();
            }
        });
        let mut sidecar_hooks = Hooks::default();
        let mut public_hooks = Hooks::default();
        match role {
            Role::Sidecar => sidecar_hooks.action = Some(action),
            Role::Public => public_hooks.action = Some(action),
        }
        let error = pair(
            &root.join("sidecar"),
            &root.join("public"),
            &mut sidecar_hooks,
            &mut public_hooks,
        )
        .unwrap_err();
        assert_code(error, AdapterErrorCodeV0::OutputPublish);
        assert!(!root.join("sidecar").exists());
        assert!(!root.join("public").exists());
        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(moved).unwrap();
    }

    for role in [Role::Sidecar, Role::Public] {
        let root = test_root("post-pin");
        let moved = root.with_extension("moved");
        let action_root = root.clone();
        let action_moved = moved.clone();
        let action = Box::new(move |stage, _held: Option<&OwnedFd>| {
            if stage == PublicationStageV0::FinalPreflight {
                fs::rename(&action_root, &action_moved).unwrap();
                fs::create_dir(&action_root).unwrap();
            }
        });
        let mut sidecar_hooks = Hooks::default();
        let mut public_hooks = Hooks::default();
        match role {
            Role::Sidecar => sidecar_hooks.action = Some(action),
            Role::Public => public_hooks.action = Some(action),
        }
        pair(
            &root.join("sidecar"),
            &root.join("public"),
            &mut sidecar_hooks,
            &mut public_hooks,
        )
        .unwrap();
        match role {
            Role::Sidecar => {
                assert!(moved.join("sidecar").exists());
                assert!(root.join("public").exists());
            }
            Role::Public => {
                assert!(moved.join("sidecar").exists());
                assert!(moved.join("public").exists());
            }
        }
        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(moved).unwrap();
    }
}

fn assert_success_link_events(hooks: &Hooks) {
    assert_eq!(
        link_phase_events(hooks),
        vec![
            PublicationEventV0::Attempted(PublicationStageV0::Link),
            PublicationEventV0::Attempted(PublicationStageV0::PostHookFinalPreflight),
            PublicationEventV0::Completed(PublicationStageV0::PostHookFinalPreflight),
            PublicationEventV0::Attempted(PublicationStageV0::RealLink),
            PublicationEventV0::Attempted(PublicationStageV0::ProtectedGuard),
            PublicationEventV0::Completed(PublicationStageV0::ProtectedGuard),
            PublicationEventV0::Completed(PublicationStageV0::RealLink),
            PublicationEventV0::Completed(PublicationStageV0::Link),
        ]
    );
}

fn assert_eexist_link_events(hooks: &Hooks, classification_completed: bool) {
    let mut expected = vec![
        PublicationEventV0::Attempted(PublicationStageV0::Link),
        PublicationEventV0::Attempted(PublicationStageV0::PostHookFinalPreflight),
        PublicationEventV0::Completed(PublicationStageV0::PostHookFinalPreflight),
        PublicationEventV0::Attempted(PublicationStageV0::RealLink),
        PublicationEventV0::Attempted(PublicationStageV0::ProtectedGuard),
        PublicationEventV0::Completed(PublicationStageV0::ProtectedGuard),
        PublicationEventV0::Attempted(PublicationStageV0::IncumbentClassify),
    ];
    if classification_completed {
        expected.push(PublicationEventV0::Completed(
            PublicationStageV0::IncumbentClassify,
        ));
    }
    assert_eq!(link_phase_events(hooks), expected);
}

fn link_phase_events(hooks: &Hooks) -> Vec<PublicationEventV0> {
    hooks
        .events
        .iter()
        .copied()
        .filter(|event| {
            let stage = match *event {
                PublicationEventV0::Attempted(stage) | PublicationEventV0::Completed(stage) => {
                    stage
                }
            };
            matches!(
                stage,
                PublicationStageV0::Link
                    | PublicationStageV0::PostHookFinalPreflight
                    | PublicationStageV0::RealLink
                    | PublicationStageV0::ProtectedGuard
                    | PublicationStageV0::IncumbentClassify
            )
        })
        .collect()
}

#[cfg(test)]
#[path = "linux_output_transaction_phase_tests.rs"]
mod phase_tests;

fn pair(
    sidecar: &Path,
    public: &Path,
    sidecar_hooks: &mut Hooks,
    public_hooks: &mut Hooks,
) -> Result<(CommittedPublicationV0, CommittedPublicationV0), AdapterErrorV0> {
    publish_pair_with_hooks(
        PublicationSpecV0 {
            output: sidecar,
            bytes: SIDECAR_BYTES,
        },
        PublicationSpecV0 {
            output: public,
            bytes: PUBLIC_BYTES,
        },
        &[],
        sidecar_hooks,
        public_hooks,
        || Ok(()),
    )
}

fn spec<'a>(output: &'a Path, bytes: &'a [u8]) -> PublicationSpecV0<'a> {
    PublicationSpecV0 { output, bytes }
}

fn test_root(label: &str) -> PathBuf {
    let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
    let root = Path::new("target").join(format!(
        "g3b-output-{}-{label}-{sequence}",
        std::process::id()
    ));
    fs::create_dir_all(&root).unwrap();
    root
}

fn role_label(role: Role) -> &'static str {
    match role {
        Role::Sidecar => "sidecar",
        Role::Public => "public",
    }
}

fn assert_code(error: AdapterErrorV0, expected: AdapterErrorCodeV0) {
    assert_eq!(error.code(), expected);
}
