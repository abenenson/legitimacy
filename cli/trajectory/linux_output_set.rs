use super::*;
use rustix::fs::{Dir, RenameFlags, mkdirat, renameat_with};
use std::collections::BTreeSet;
use std::ffi::OsStr;

const SET_DIRECTORY_MODE: u32 = 0o700;
const STAGING_ATTEMPTS: usize = 8;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum OutputSetStageV0 {
    StagingOpened,
    MembersPublished,
    BeforeFinalValidation,
    BeforeRename,
    FinalProofComplete,
    BeforeCleanup,
    CleanupBeforeFinalProof,
}

pub(super) trait OutputSetHooksV0 {
    fn event(&mut self, _stage: OutputSetStageV0, _name: &OsStr, _staging: &OwnedFd) {}
}

struct NoOutputSetHooksV0;
impl OutputSetHooksV0 for NoOutputSetHooksV0 {}

pub(crate) fn publish_directory_set<F>(
    output_set: &Path,
    members: &[(&str, &[u8])],
    inputs: &[&SnapshotV0],
    late_verifier: F,
) -> Result<(), AdapterErrorV0>
where
    F: FnOnce() -> Result<(), AdapterErrorV0>,
{
    publish_directory_set_with_hooks(
        output_set,
        members,
        inputs,
        &mut NoOutputSetHooksV0,
        late_verifier,
    )
}

pub(super) fn publish_directory_set_with_hooks<F>(
    output_set: &Path,
    members: &[(&str, &[u8])],
    inputs: &[&SnapshotV0],
    hooks: &mut impl OutputSetHooksV0,
    late_verifier: F,
) -> Result<(), AdapterErrorV0>
where
    F: FnOnce() -> Result<(), AdapterErrorV0>,
{
    validate_members(members)?;
    let parsed = parse_output_path(output_set)?;
    let mut parent_path = pin_start(parsed.absolute)?;
    for component in &parsed.ancestors {
        let observed = statat(&parent_path, component, AtFlags::SYMLINK_NOFOLLOW)
            .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
        require_directory(&observed)?;
        let opened = openat(
            &parent_path,
            component,
            OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
            Mode::empty(),
        )
        .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
        let pinned = fstat(&opened).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
        if !same_directory(&observed, &pinned) {
            return Err(error(AdapterErrorCodeV0::OutputPublish));
        }
        parent_path = opened;
    }
    let parent_sync = openat(
        &parent_path,
        Path::new("."),
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    let parent_identity =
        identity(&fstat(&parent_path).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?);
    verify_sync_directory(&parent_sync, parent_identity)?;
    preflight_final(&parent_path, &parsed.final_name, inputs, &[])?;
    revalidate_inputs(inputs)?;

    let staging_name = create_staging_directory(&parent_path)?;
    let observed = statat(&parent_path, &staging_name, AtFlags::SYMLINK_NOFOLLOW)
        .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    let staging = openat(
        &parent_path,
        &staging_name,
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    let staging_stat = fstat(&staging).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    if !same_directory(&observed, &staging_stat) || !exact_staging_properties(&staging_stat) {
        return Err(error(AdapterErrorCodeV0::OutputPublish));
    }
    let staging_identity = identity(&staging_stat);
    hooks.event(OutputSetStageV0::StagingOpened, &staging_name, &staging);

    let (committed, publication_result) =
        match publish_relative_set(&staging, members, inputs, late_verifier) {
            Ok(publications) => {
                hooks.event(OutputSetStageV0::MembersPublished, &staging_name, &staging);
                hooks.event(
                    OutputSetStageV0::BeforeFinalValidation,
                    &staging_name,
                    &staging,
                );
                let result = finalize_staging(
                    &parent_path,
                    &parent_sync,
                    &parsed.final_name,
                    &staging_name,
                    &staging,
                    staging_identity,
                    members,
                    &publications,
                    inputs,
                    hooks,
                );
                (publications, result)
            }
            Err(failure) => (failure.committed, Err(failure.error)),
        };
    if publication_result.is_err() {
        hooks.event(OutputSetStageV0::BeforeCleanup, &staging_name, &staging);
        if cleanup_staging(
            &parent_path,
            &parent_sync,
            &staging_name,
            &staging,
            staging_identity,
            members,
            &committed,
            hooks,
        )
        .is_err()
        {
            return Err(error(AdapterErrorCodeV0::OutputRollbackUncertain));
        }
    }
    publication_result
}

#[allow(clippy::too_many_arguments)]
fn finalize_staging(
    parent: &OwnedFd,
    parent_sync: &OwnedFd,
    final_name: &OsStr,
    staging_name: &OsStr,
    staging: &OwnedFd,
    staging_identity: IdentityV0,
    members: &[(&str, &[u8])],
    committed: &[CommittedPublicationV0],
    inputs: &[&SnapshotV0],
    hooks: &mut impl OutputSetHooksV0,
) -> Result<(), AdapterErrorV0> {
    verify_staging_name(parent, staging_name, staging_identity)?;
    verify_staging_directory(staging, staging_identity, members, committed)?;
    revalidate_inputs(inputs)?;
    preflight_final(parent, &final_name.to_os_string(), inputs, &[])?;
    fsync(staging).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    fsync(parent_sync).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;

    hooks.event(OutputSetStageV0::BeforeRename, staging_name, staging);
    verify_staging_name(parent, staging_name, staging_identity)?;
    verify_staging_directory(staging, staging_identity, members, committed)?;
    revalidate_inputs(inputs)?;
    preflight_final(parent, &final_name.to_os_string(), inputs, &[])?;
    hooks.event(OutputSetStageV0::FinalProofComplete, staging_name, staging);
    verify_staging_name(parent, staging_name, staging_identity)?;
    verify_staging_directory(staging, staging_identity, members, committed)?;
    revalidate_inputs(inputs)?;
    preflight_final(parent, &final_name.to_os_string(), inputs, &[])?;
    renameat_with(
        parent,
        staging_name,
        parent,
        final_name,
        RenameFlags::NOREPLACE,
    )
    .map_err(|errno| {
        if errno == Errno::EXIST {
            classify_incumbent(parent, &final_name.to_os_string(), inputs, &[])
        } else {
            publication_errno(errno, is_link_profile_errno(errno))
        }
    })?;
    let _ = fsync(parent_sync);
    Ok(())
}

fn validate_members(members: &[(&str, &[u8])]) -> Result<(), AdapterErrorV0> {
    if members.is_empty()
        || members.iter().any(|(name, _)| !valid_relative_name(name))
        || members
            .iter()
            .enumerate()
            .any(|(index, (name, _))| members[index + 1..].iter().any(|(other, _)| name == other))
    {
        Err(error(AdapterErrorCodeV0::UnsafeOutputPath))
    } else {
        Ok(())
    }
}

fn create_staging_directory(parent: &OwnedFd) -> Result<OsString, AdapterErrorV0> {
    for _ in 0..STAGING_ATTEMPTS {
        let name = random_name(".legitimacy-output-set-", ".staging")?;
        match mkdirat(parent, &name, Mode::from_raw_mode(SET_DIRECTORY_MODE)) {
            Ok(()) => return Ok(name),
            Err(Errno::EXIST) => {}
            Err(_) => return Err(error(AdapterErrorCodeV0::OutputPublish)),
        }
    }
    Err(error(AdapterErrorCodeV0::OutputPublish))
}

fn random_name(prefix: &str, suffix: &str) -> Result<OsString, AdapterErrorV0> {
    let mut random = [0_u8; 16];
    rustix::rand::getrandom(&mut random, rustix::rand::GetRandomFlags::empty())
        .map_err(|_| error(AdapterErrorCodeV0::EntropyUnavailable))?;
    if random.iter().all(|byte| *byte == 0) {
        return Err(error(AdapterErrorCodeV0::EntropyUnavailable));
    }
    let encoded = random
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    Ok(OsString::from(format!("{prefix}{encoded}{suffix}")))
}

fn exact_staging_properties(stat: &Stat) -> bool {
    FileType::from_raw_mode(stat.st_mode) == FileType::Directory
        && widen_u64(stat.st_uid) == u64::from(rustix::process::geteuid().as_raw())
        && widen_u64(stat.st_mode) & 0o7777 == u64::from(SET_DIRECTORY_MODE)
}

fn verify_staging_name(
    parent: &OwnedFd,
    name: &OsStr,
    expected: IdentityV0,
) -> Result<(), AdapterErrorV0> {
    let stat = statat(parent, name, AtFlags::SYMLINK_NOFOLLOW)
        .map_err(|_| error(AdapterErrorCodeV0::OutputIdentityUncertain))?;
    if identity(&stat) != expected || !exact_staging_properties(&stat) {
        return Err(error(AdapterErrorCodeV0::OutputIdentityUncertain));
    }
    Ok(())
}

fn verify_staging_directory(
    staging: &OwnedFd,
    expected: IdentityV0,
    members: &[(&str, &[u8])],
    committed: &[CommittedPublicationV0],
) -> Result<(), AdapterErrorV0> {
    let stat = fstat(staging).map_err(|_| error(AdapterErrorCodeV0::OutputIdentityUncertain))?;
    if identity(&stat) != expected || !exact_staging_properties(&stat) {
        return Err(error(AdapterErrorCodeV0::OutputIdentityUncertain));
    }
    let inventory_fd = openat(
        staging,
        Path::new("."),
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputIdentityUncertain))?;
    let names = directory_names(&inventory_fd, AdapterErrorCodeV0::OutputIdentityUncertain)?;
    let inventory = members
        .iter()
        .map(|(name, _)| name.as_bytes().to_vec())
        .collect::<BTreeSet<_>>();
    if names != inventory || committed.len() != members.len() {
        return Err(error(AdapterErrorCodeV0::OutputIdentityUncertain));
    }
    for (publication, (name, bytes)) in committed.iter().zip(members) {
        let parent_stat = fstat(&publication.parent_path)
            .map_err(|_| error(AdapterErrorCodeV0::OutputIdentityUncertain))?;
        if publication.name.as_os_str().as_bytes() != name.as_bytes()
            || identity(&parent_stat) != expected
        {
            return Err(error(AdapterErrorCodeV0::OutputIdentityUncertain));
        }
        revalidate_committed(publication, bytes, &mut NoPublicationHooksV0)?;
    }
    Ok(())
}

fn directory_names(
    directory: &OwnedFd,
    code: AdapterErrorCodeV0,
) -> Result<BTreeSet<Vec<u8>>, AdapterErrorV0> {
    let mut names = BTreeSet::new();
    let mut entries = Dir::read_from(directory).map_err(|_| error(code))?;
    while let Some(entry) = entries.read() {
        let entry = entry.map_err(|_| error(code))?;
        if !matches!(entry.file_name().to_bytes(), b"." | b"..") {
            names.insert(entry.file_name().to_bytes().to_vec());
        }
    }
    Ok(names)
}

fn verify_empty_staging_directory(
    staging: &OwnedFd,
    expected: IdentityV0,
) -> Result<(), AdapterErrorV0> {
    let uncertain = || error(AdapterErrorCodeV0::OutputRollbackUncertain);
    let stat = fstat(staging).map_err(|_| uncertain())?;
    if identity(&stat) != expected || !exact_staging_properties(&stat) {
        return Err(uncertain());
    }
    let inventory_fd = openat(
        staging,
        Path::new("."),
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| uncertain())?;
    if !directory_names(&inventory_fd, AdapterErrorCodeV0::OutputRollbackUncertain)?.is_empty() {
        return Err(uncertain());
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn cleanup_staging(
    parent: &OwnedFd,
    parent_sync: &OwnedFd,
    staging_name: &OsStr,
    staging: &OwnedFd,
    staging_identity: IdentityV0,
    members: &[(&str, &[u8])],
    committed: &[CommittedPublicationV0],
    hooks: &mut impl OutputSetHooksV0,
) -> Result<(), AdapterErrorV0> {
    let uncertain = || error(AdapterErrorCodeV0::OutputRollbackUncertain);
    verify_staging_name(parent, staging_name, staging_identity).map_err(|_| uncertain())?;
    for (publication, (name, bytes)) in committed.iter().zip(members) {
        revalidate_committed(publication, bytes, &mut NoPublicationHooksV0)
            .map_err(|_| uncertain())?;
        let quarantine = random_name(".rollback-", ".quarantine").map_err(|_| uncertain())?;
        renameat_with(
            &publication.parent_path,
            *name,
            &publication.parent_path,
            &quarantine,
            RenameFlags::NOREPLACE,
        )
        .map_err(|_| uncertain())?;
        verify_final_identity(
            &publication.parent_path,
            &quarantine,
            publication.identity,
            None,
            publication.expected_uid,
            bytes.len(),
        )
        .map_err(|_| uncertain())?;
        let hash = Sha256::digest(bytes);
        verify_held(
            &mut NoPublicationHooksV0,
            &publication.held,
            HeldExpectationV0 {
                bytes,
                hash: &hash,
                uid: publication.expected_uid,
                links: 1,
                property_code: AdapterErrorCodeV0::OutputRollbackUncertain,
                content_code: AdapterErrorCodeV0::OutputRollbackUncertain,
            },
        )?;
        unlinkat(&publication.parent_path, &quarantine, AtFlags::empty())
            .map_err(|_| uncertain())?;
    }
    verify_empty_staging_directory(staging, staging_identity)?;
    hooks.event(
        OutputSetStageV0::CleanupBeforeFinalProof,
        staging_name,
        staging,
    );
    verify_staging_name(parent, staging_name, staging_identity).map_err(|_| uncertain())?;
    verify_empty_staging_directory(staging, staging_identity)?;
    unlinkat(parent, staging_name, AtFlags::REMOVEDIR).map_err(|_| uncertain())?;
    fsync(parent_sync).map_err(|_| uncertain())
}
