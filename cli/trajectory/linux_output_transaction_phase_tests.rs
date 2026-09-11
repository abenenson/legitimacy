use super::*;

#[test]
fn every_sidecar_and_public_phase_has_the_required_artifact_state() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let prepare = [
        PublicationStageV0::StartOpen,
        PublicationStageV0::AncestorOpen(0),
        PublicationStageV0::AncestorOpen(1),
        PublicationStageV0::ParentSyncOpen,
        PublicationStageV0::FinalPreflight,
    ];
    let prelink = [
        PublicationStageV0::CommitEuidVerify,
        PublicationStageV0::CommitFinalPreflight,
        PublicationStageV0::TemporaryOpen,
        PublicationStageV0::Write,
        PublicationStageV0::Chmod,
        PublicationStageV0::TemporaryVerify,
        PublicationStageV0::FileSync,
        PublicationStageV0::PreLinkDirectorySync,
        PublicationStageV0::ProcOpen,
        PublicationStageV0::PreLinkSourceVerify,
        PublicationStageV0::Link,
        PublicationStageV0::PostHookFinalPreflight,
        PublicationStageV0::RealLink,
        PublicationStageV0::ProtectedGuard,
    ];
    let postlink = [
        (
            PublicationStageV0::PostLinkSourceVerify,
            AdapterErrorCodeV0::OutputIdentityUncertain,
        ),
        (
            PublicationStageV0::PostLinkDirectorySync,
            AdapterErrorCodeV0::DurabilityUncertain,
        ),
        (
            PublicationStageV0::HeldIntegrityVerify,
            AdapterErrorCodeV0::OutputIntegrityUncertain,
        ),
        (
            PublicationStageV0::FinalIdentityVerify,
            AdapterErrorCodeV0::OutputIdentityUncertain,
        ),
    ];
    let revalidation = [
        (
            PublicationStageV0::CommittedEuidRevalidate,
            AdapterErrorCodeV0::OutputIdentityUncertain,
        ),
        (
            PublicationStageV0::CommittedIntegrityRevalidate,
            AdapterErrorCodeV0::OutputIntegrityUncertain,
        ),
        (
            PublicationStageV0::CommittedIdentityRevalidate,
            AdapterErrorCodeV0::OutputIdentityUncertain,
        ),
    ];
    for role in [Role::Sidecar, Role::Public] {
        for stage in prepare {
            assert_phase_state(role, stage, None, false, false);
        }
        for stage in prelink {
            assert_phase_state(role, stage, None, matches!(role, Role::Public), false);
        }
        for (stage, code) in postlink {
            assert_phase_state(role, stage, Some(code), true, matches!(role, Role::Public));
        }
        for (stage, code) in revalidation {
            assert_phase_state(role, stage, Some(code), true, matches!(role, Role::Public));
        }
    }
}

#[test]
fn failing_before_incumbent_classification_is_phase_exact_for_both_roles() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    for role in [Role::Sidecar, Role::Public] {
        let root = test_root("classify-failure");
        let sidecar = root.join("sidecar");
        let public = root.join("public");
        let incumbent = match role {
            Role::Sidecar => sidecar.clone(),
            Role::Public => public.clone(),
        };
        let hooks = Hooks {
            fail: Some(PublicationStageV0::IncumbentClassify),
            action: Some(Box::new(move |stage, _| {
                if stage == PublicationStageV0::RealLink {
                    fs::write(&incumbent, b"incumbent").unwrap();
                }
            })),
            ..Hooks::default()
        };
        let (mut sidecar_hooks, mut public_hooks) = match role {
            Role::Sidecar => (hooks, Hooks::default()),
            Role::Public => (Hooks::default(), hooks),
        };
        let result = pair(&sidecar, &public, &mut sidecar_hooks, &mut public_hooks);
        assert_code(result.unwrap_err(), AdapterErrorCodeV0::OutputPublish);
        assert_eq!(
            fs::read(match role {
                Role::Sidecar => &sidecar,
                Role::Public => &public,
            })
            .unwrap(),
            b"incumbent"
        );
        match role {
            Role::Sidecar => assert!(!public.exists()),
            Role::Public => assert_eq!(fs::read(&sidecar).unwrap(), SIDECAR_BYTES),
        }
        assert_eexist_link_events(
            match role {
                Role::Sidecar => &sidecar_hooks,
                Role::Public => &public_hooks,
            },
            false,
        );
        fs::remove_dir_all(root).unwrap();
    }
}

#[test]
fn prepare_and_commit_reject_wrong_captured_euid_before_publication() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("direct-euid");
    let output = root.join("output");
    let current_uid = rustix::process::geteuid().as_raw();
    let mut hooks = Hooks::default();
    assert_code(
        prepare_with_hooks(&output, &[], current_uid ^ 1, &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::UnsupportedPublicationProfile,
    );
    assert!(hooks.events.is_empty());
    assert!(!output.exists());

    let mut prepared =
        prepare_with_hooks(&output, &[], current_uid, &mut Hooks::default()).unwrap();
    prepared.expected_uid ^= 1;
    let mut hooks = Hooks::default();
    let error = match commit_with_hooks(prepared, b"x", &[], &[], &mut hooks, || Ok(())) {
        Err(CommitFailureV0::PreLink(error)) => error,
        Err(CommitFailureV0::PostLink { .. }) => panic!("wrong euid must fail before link"),
        Ok(_) => panic!("wrong euid must fail"),
    };
    assert_code(error, AdapterErrorCodeV0::UnsupportedPublicationProfile);
    assert_eq!(
        hooks.events,
        vec![PublicationEventV0::Attempted(
            PublicationStageV0::CommitEuidVerify
        )]
    );
    assert!(!output.exists());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn every_committed_revalidation_checks_the_captured_euid() {
    let _serial = SERIAL.lock().unwrap_or_else(|error| error.into_inner());
    let root = test_root("euid");
    let output = root.join("output");
    let prepared = prepare_with_hooks(
        &output,
        &[],
        rustix::process::geteuid().as_raw(),
        &mut Hooks::default(),
    )
    .unwrap();
    let mut committed =
        match commit_with_hooks(prepared, b"x", &[], &[], &mut Hooks::default(), || Ok(())) {
            Ok(committed) => committed,
            Err(_) => panic!("publication must commit"),
        };
    committed.expected_uid ^= 1;
    let mut hooks = Hooks::default();
    assert_code(
        revalidate_committed(&committed, b"x", &mut hooks).unwrap_err(),
        AdapterErrorCodeV0::OutputIdentityUncertain,
    );
    assert!(hooks.events.contains(&PublicationEventV0::Attempted(
        PublicationStageV0::CommittedEuidRevalidate
    )));
    drop(committed);
    fs::remove_dir_all(root).unwrap();
}

fn assert_phase_state(
    role: Role,
    stage: PublicationStageV0,
    expected: Option<AdapterErrorCodeV0>,
    sidecar_exists: bool,
    public_exists: bool,
) {
    let root = test_root("phase");
    let sidecar = root.join("sidecar");
    let public = root.join("public");
    let mut sidecar_hooks = Hooks::default();
    let mut public_hooks = Hooks::default();
    match role {
        Role::Sidecar => sidecar_hooks.fail = Some(stage),
        Role::Public => public_hooks.fail = Some(stage),
    }
    let error = pair(&sidecar, &public, &mut sidecar_hooks, &mut public_hooks).unwrap_err();
    assert_code(error, expected.unwrap_or(AdapterErrorCodeV0::OutputPublish));
    assert_eq!(sidecar.exists(), sidecar_exists, "{role:?} {stage:?}");
    assert_eq!(public.exists(), public_exists, "{role:?} {stage:?}");
    let hooks = match role {
        Role::Sidecar => &sidecar_hooks,
        Role::Public => &public_hooks,
    };
    assert!(hooks.events.contains(&PublicationEventV0::Attempted(stage)));
    assert!(!hooks.events.contains(&PublicationEventV0::Completed(stage)));
    if stage == PublicationStageV0::RealLink {
        assert_eq!(
            link_phase_events(hooks),
            vec![
                PublicationEventV0::Attempted(PublicationStageV0::Link),
                PublicationEventV0::Attempted(PublicationStageV0::PostHookFinalPreflight),
                PublicationEventV0::Completed(PublicationStageV0::PostHookFinalPreflight),
                PublicationEventV0::Attempted(PublicationStageV0::RealLink),
            ]
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[derive(Clone, Copy, Debug)]
pub(super) enum Mutation {
    Append,
    Truncate,
    Overwrite,
    Chmod,
    AddLink,
    Unlink,
    Replace,
}

pub(super) fn mutate(root: &Path, sidecar: &Path, mutation: Mutation) -> AdapterErrorCodeV0 {
    let before = fs::metadata(sidecar).unwrap();
    match mutation {
        Mutation::Append => {
            OpenOptions::new()
                .append(true)
                .open(sidecar)
                .unwrap()
                .write_all(b"x")
                .unwrap();
        }
        Mutation::Truncate => {
            OpenOptions::new()
                .write(true)
                .truncate(true)
                .open(sidecar)
                .unwrap();
        }
        Mutation::Overwrite => fs::write(sidecar, vec![b'x'; SIDECAR_BYTES.len()]).unwrap(),
        Mutation::Chmod => {
            fs::set_permissions(sidecar, fs::Permissions::from_mode(0o400)).unwrap();
        }
        Mutation::AddLink => fs::hard_link(sidecar, root.join("extra-link")).unwrap(),
        Mutation::Unlink => fs::remove_file(sidecar).unwrap(),
        Mutation::Replace => {
            fs::remove_file(sidecar).unwrap();
            fs::write(sidecar, SIDECAR_BYTES).unwrap();
            fs::set_permissions(sidecar, fs::Permissions::from_mode(0o600)).unwrap();
        }
    }
    // Same-size writes may share mtime and ctime with the committed file.
    // In that case the byte check, rather than an identity change, must reject.
    if matches!(mutation, Mutation::Overwrite) {
        let after = fs::metadata(sidecar).unwrap();
        let before_times = (
            before.mtime(),
            before.mtime_nsec(),
            before.ctime(),
            before.ctime_nsec(),
        );
        let after_times = (
            after.mtime(),
            after.mtime_nsec(),
            after.ctime(),
            after.ctime_nsec(),
        );
        if before_times == after_times {
            return AdapterErrorCodeV0::OutputIntegrityUncertain;
        }
    }
    AdapterErrorCodeV0::OutputIdentityUncertain
}
