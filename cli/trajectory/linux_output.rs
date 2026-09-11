use super::linux_path::SnapshotV0;
use legitimacy::trajectory::codex_exec_v0::{AdapterErrorCodeV0, AdapterErrorV0};
use rustix::fd::{AsRawFd, OwnedFd};
use rustix::fs::{
    AtFlags, FileType, Mode, OFlags, PROC_SUPER_MAGIC, Stat, fchmod, fcntl_getfl, fstat, fstatfs,
    fsync, linkat, openat, statat, unlinkat,
};
use rustix::io::{Errno, FdFlags, fcntl_getfd};
use sha2::{Digest, Sha256};
use std::ffi::OsString;
use std::fmt;
use std::os::unix::ffi::OsStrExt;
use std::path::{Component, Path};

const OUTPUT_MODE: u32 = 0o600;
const VERIFY_CHUNK_BYTES: usize = 64 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PublicationStageV0 {
    StartOpen,
    AncestorOpen(usize),
    ParentSyncOpen,
    FinalPreflight,
    CommitEuidVerify,
    CommitFinalPreflight,
    TemporaryOpen,
    Write,
    Chmod,
    TemporaryVerify,
    FileSync,
    PreLinkDirectorySync,
    ProcOpen,
    PreLinkSourceVerify,
    Link,
    PostHookFinalPreflight,
    ProtectedGuard,
    RealLink,
    IncumbentClassify,
    PostLinkSourceVerify,
    PostLinkDirectorySync,
    FinalIdentityVerify,
    HeldIntegrityVerify,
    CommittedEuidRevalidate,
    CommittedIntegrityRevalidate,
    CommittedIdentityRevalidate,
    RollbackQuarantine,
    RollbackBeforeUnlink,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PublicationEventV0 {
    Attempted(PublicationStageV0),
    Completed(PublicationStageV0),
}

pub(crate) trait PublicationHooksV0 {
    fn event(&mut self, _event: PublicationEventV0, _held: Option<&OwnedFd>) {}

    fn fail_before(&mut self, _stage: PublicationStageV0, _held: Option<&OwnedFd>) -> bool {
        false
    }

    fn proc_root(&self) -> &Path {
        Path::new("/proc")
    }

    fn parent_sync_name(&self) -> &Path {
        Path::new(".")
    }

    fn proc_source(&self, held_fd: i32) -> String {
        format!("self/fd/{held_fd}")
    }

    fn write(&mut self, held: &OwnedFd, bytes: &[u8]) -> Result<usize, Errno> {
        rustix::io::write(held, bytes)
    }

    fn pread(&mut self, held: &OwnedFd, bytes: &mut [u8], offset: u64) -> Result<usize, Errno> {
        rustix::io::pread(held, bytes, offset)
    }
}

struct NoPublicationHooksV0;

impl PublicationHooksV0 for NoPublicationHooksV0 {}

pub(crate) struct PreparedPublicationV0 {
    parent_path: OwnedFd,
    parent_sync: OwnedFd,
    name: OsString,
    parent_identity: IdentityV0,
    expected_uid: u32,
}

impl fmt::Debug for PreparedPublicationV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("PreparedPublicationV0(redacted)")
    }
}

pub(crate) struct CommittedPublicationV0 {
    held: OwnedFd,
    parent_path: OwnedFd,
    parent_sync: OwnedFd,
    name: OsString,
    identity: IdentityV0,
    metadata: Option<StableMetadataV0>,
    expected_uid: u32,
}

impl fmt::Debug for CommittedPublicationV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("CommittedPublicationV0(redacted)")
    }
}

pub(crate) enum CommitFailureV0 {
    PreLink(AdapterErrorV0),
    PostLink {
        committed: Box<CommittedPublicationV0>,
        error: AdapterErrorV0,
    },
}

pub(crate) fn publish(
    output: &Path,
    bytes: &[u8],
    inputs: &[&SnapshotV0],
) -> Result<CommittedPublicationV0, AdapterErrorV0> {
    publish_with_hooks(output, bytes, inputs, &mut NoPublicationHooksV0)
}

pub(crate) fn publish_with_hooks(
    output: &Path,
    bytes: &[u8],
    inputs: &[&SnapshotV0],
    hooks: &mut impl PublicationHooksV0,
) -> Result<CommittedPublicationV0, AdapterErrorV0> {
    let expected_uid = rustix::process::geteuid().as_raw();
    let prepared = prepare_with_hooks(output, inputs, expected_uid, hooks)?;
    match commit_with_hooks(prepared, bytes, inputs, &[], hooks, || Ok(())) {
        Ok(committed) => Ok(committed),
        Err(CommitFailureV0::PreLink(error)) => Err(error),
        Err(CommitFailureV0::PostLink { committed, error }) => {
            drop(committed);
            Err(error)
        }
    }
}

fn prepare_with_hooks(
    output: &Path,
    inputs: &[&SnapshotV0],
    expected_uid: u32,
    hooks: &mut impl PublicationHooksV0,
) -> Result<PreparedPublicationV0, AdapterErrorV0> {
    if rustix::process::geteuid().as_raw() != expected_uid {
        return Err(error(AdapterErrorCodeV0::UnsupportedPublicationProfile));
    }
    let parsed = parse_output_path(output)?;
    attempt(hooks, PublicationStageV0::StartOpen, None)?;
    let mut parent_path = pin_start(parsed.absolute)?;
    complete(hooks, PublicationStageV0::StartOpen, None);
    for (index, component) in parsed.ancestors.iter().enumerate() {
        let observed = statat(&parent_path, component, AtFlags::SYMLINK_NOFOLLOW)
            .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
        require_directory(&observed)?;
        attempt(hooks, PublicationStageV0::AncestorOpen(index), None)?;
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
        complete(
            hooks,
            PublicationStageV0::AncestorOpen(index),
            Some(&opened),
        );
        parent_path = opened;
    }

    let parent_identity =
        identity(&fstat(&parent_path).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?);
    attempt(hooks, PublicationStageV0::ParentSyncOpen, None)?;
    let parent_sync = openat(
        &parent_path,
        hooks.parent_sync_name(),
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    verify_sync_directory(&parent_sync, parent_identity)?;
    complete(
        hooks,
        PublicationStageV0::ParentSyncOpen,
        Some(&parent_sync),
    );

    attempt(hooks, PublicationStageV0::FinalPreflight, None)?;
    preflight_final(&parent_path, &parsed.final_name, inputs, &[])?;
    complete(hooks, PublicationStageV0::FinalPreflight, None);

    Ok(PreparedPublicationV0 {
        parent_path,
        parent_sync,
        name: parsed.final_name,
        parent_identity,
        expected_uid,
    })
}

fn prepare_relative(
    directory: &OwnedFd,
    name: &str,
    inputs: &[&SnapshotV0],
    expected_uid: u32,
) -> Result<PreparedPublicationV0, AdapterErrorV0> {
    if rustix::process::geteuid().as_raw() != expected_uid || !valid_relative_name(name) {
        return Err(error(AdapterErrorCodeV0::UnsafeOutputPath));
    }
    let parent_identity =
        identity(&fstat(directory).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?);
    let parent_path = openat(
        directory,
        Path::new("."),
        OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    let parent_sync = openat(
        directory,
        Path::new("."),
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    if identity(&fstat(&parent_path).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?)
        != parent_identity
    {
        return Err(error(AdapterErrorCodeV0::OutputPublish));
    }
    verify_sync_directory(&parent_sync, parent_identity)?;
    let name = OsString::from(name);
    preflight_final(&parent_path, &name, inputs, &[])?;
    Ok(PreparedPublicationV0 {
        parent_path,
        parent_sync,
        name,
        parent_identity,
        expected_uid,
    })
}

fn valid_relative_name(name: &str) -> bool {
    !name.is_empty()
        && name != "."
        && name != ".."
        && !name.as_bytes().contains(&0)
        && !name.as_bytes().contains(&b'/')
}

fn commit_with_hooks<F>(
    prepared: PreparedPublicationV0,
    bytes: &[u8],
    inputs: &[&SnapshotV0],
    protected: &[&CommittedPublicationV0],
    hooks: &mut impl PublicationHooksV0,
    mut guard: F,
) -> Result<CommittedPublicationV0, CommitFailureV0>
where
    F: FnMut() -> Result<(), AdapterErrorV0>,
{
    let PreparedPublicationV0 {
        parent_path,
        parent_sync,
        name,
        parent_identity: _,
        expected_uid,
    } = prepared;
    attempt(hooks, PublicationStageV0::CommitEuidVerify, None)?;
    if rustix::process::geteuid().as_raw() != expected_uid {
        return Err(error(AdapterErrorCodeV0::UnsupportedPublicationProfile).into());
    }
    complete(hooks, PublicationStageV0::CommitEuidVerify, None);
    attempt(hooks, PublicationStageV0::CommitFinalPreflight, None)?;
    preflight_final(&parent_path, &name, inputs, protected)?;
    complete(hooks, PublicationStageV0::CommitFinalPreflight, None);

    attempt(hooks, PublicationStageV0::TemporaryOpen, None)?;
    let held = openat(
        &parent_sync,
        Path::new("."),
        OFlags::TMPFILE | OFlags::RDWR | OFlags::CLOEXEC,
        Mode::from_raw_mode(OUTPUT_MODE),
    )
    .map_err(|errno| publication_errno(errno, is_profile_errno(errno)))?;
    verify_temporary_flags(&held)?;
    complete(hooks, PublicationStageV0::TemporaryOpen, Some(&held));

    attempt(hooks, PublicationStageV0::Write, Some(&held))?;
    write_all(hooks, &held, bytes)?;
    complete(hooks, PublicationStageV0::Write, Some(&held));
    attempt(hooks, PublicationStageV0::Chmod, Some(&held))?;
    fchmod(&held, Mode::from_raw_mode(OUTPUT_MODE))
        .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    complete(hooks, PublicationStageV0::Chmod, Some(&held));
    attempt(hooks, PublicationStageV0::TemporaryVerify, Some(&held))?;
    let expected_hash = Sha256::digest(bytes);
    let _ = verify_held(
        hooks,
        &held,
        HeldExpectationV0 {
            bytes,
            hash: &expected_hash,
            uid: expected_uid,
            links: 0,
            property_code: AdapterErrorCodeV0::UnsupportedPublicationProfile,
            content_code: AdapterErrorCodeV0::OutputPublish,
        },
    )?;
    complete(hooks, PublicationStageV0::TemporaryVerify, Some(&held));

    attempt(hooks, PublicationStageV0::FileSync, Some(&held))?;
    fsync(&held).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    complete(hooks, PublicationStageV0::FileSync, Some(&held));
    attempt(hooks, PublicationStageV0::PreLinkDirectorySync, Some(&held))?;
    fsync(&parent_sync).map_err(|errno| publication_errno(errno, is_profile_errno(errno)))?;
    complete(hooks, PublicationStageV0::PreLinkDirectorySync, Some(&held));

    attempt(hooks, PublicationStageV0::ProcOpen, Some(&held))?;
    let proc = openat(
        rustix::fs::CWD,
        hooks.proc_root(),
        OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::UnsupportedPublicationProfile))?;
    if fstatfs(&proc)
        .map_err(|_| error(AdapterErrorCodeV0::UnsupportedPublicationProfile))?
        .f_type
        != PROC_SUPER_MAGIC
    {
        return Err(error(AdapterErrorCodeV0::UnsupportedPublicationProfile).into());
    }
    complete(hooks, PublicationStageV0::ProcOpen, Some(&held));
    let proc_source = hooks.proc_source(held.as_raw_fd());
    let held_identity =
        identity(&fstat(&held).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?);
    attempt(hooks, PublicationStageV0::PreLinkSourceVerify, Some(&held))?;
    verify_proc_source(&proc, &proc_source, held_identity)?;
    complete(hooks, PublicationStageV0::PreLinkSourceVerify, Some(&held));

    attempt(hooks, PublicationStageV0::Link, Some(&held))?;
    attempt(
        hooks,
        PublicationStageV0::PostHookFinalPreflight,
        Some(&held),
    )?;
    preflight_final(&parent_path, &name, inputs, protected)?;
    complete(
        hooks,
        PublicationStageV0::PostHookFinalPreflight,
        Some(&held),
    );
    attempt(hooks, PublicationStageV0::RealLink, Some(&held))?;
    attempt(hooks, PublicationStageV0::ProtectedGuard, Some(&held))?;
    guard()?;
    complete(hooks, PublicationStageV0::ProtectedGuard, Some(&held));
    if let Err(errno) = linkat(
        &proc,
        &proc_source,
        &parent_sync,
        &name,
        AtFlags::SYMLINK_FOLLOW,
    ) {
        if errno == Errno::EXIST {
            attempt(hooks, PublicationStageV0::IncumbentClassify, Some(&held))?;
            let error = classify_incumbent(&parent_path, &name, inputs, protected);
            complete(hooks, PublicationStageV0::IncumbentClassify, Some(&held));
            return Err(error.into());
        }
        return Err(publication_errno(errno, is_link_profile_errno(errno)).into());
    }
    complete(hooks, PublicationStageV0::RealLink, Some(&held));
    let mut committed = CommittedPublicationV0 {
        held,
        parent_path,
        parent_sync,
        name,
        identity: held_identity,
        metadata: None,
        expected_uid,
    };
    committed.metadata = fstat(&committed.held)
        .ok()
        .map(|stat| stable_metadata(&stat));
    complete(hooks, PublicationStageV0::Link, Some(&committed.held));
    let post_result = postlink_checks(&committed, bytes, &proc, &proc_source, hooks);
    match post_result {
        Ok(()) => Ok(committed),
        Err(error) => Err(CommitFailureV0::PostLink {
            committed: Box::new(committed),
            error,
        }),
    }
}

fn postlink_checks(
    committed: &CommittedPublicationV0,
    bytes: &[u8],
    proc: &OwnedFd,
    proc_source: &str,
    hooks: &mut impl PublicationHooksV0,
) -> Result<(), AdapterErrorV0> {
    let expected_hash = Sha256::digest(bytes);
    let source_identity_result = attempt(
        hooks,
        PublicationStageV0::PostLinkSourceVerify,
        Some(&committed.held),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputIdentityUncertain));
    let source_identity_result = source_identity_result.and_then(|()| {
        verify_proc_source(proc, proc_source, committed.identity)
            .map_err(|_| error(AdapterErrorCodeV0::OutputIdentityUncertain))
    });
    if source_identity_result.is_ok() {
        complete(
            hooks,
            PublicationStageV0::PostLinkSourceVerify,
            Some(&committed.held),
        );
    }

    let sync_result = attempt(
        hooks,
        PublicationStageV0::PostLinkDirectorySync,
        Some(&committed.held),
    )
    .map_err(|_| Errno::IO)
    .and_then(|()| fsync(&committed.parent_sync));
    if sync_result.is_ok() {
        complete(
            hooks,
            PublicationStageV0::PostLinkDirectorySync,
            Some(&committed.held),
        );
    }

    let integrity_result = attempt(
        hooks,
        PublicationStageV0::HeldIntegrityVerify,
        Some(&committed.held),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputIntegrityUncertain));
    let integrity_result = integrity_result.and_then(|()| {
        verify_held(
            hooks,
            &committed.held,
            HeldExpectationV0 {
                bytes,
                hash: &expected_hash,
                uid: committed.expected_uid,
                links: 1,
                property_code: AdapterErrorCodeV0::OutputIntegrityUncertain,
                content_code: AdapterErrorCodeV0::OutputIntegrityUncertain,
            },
        )
        .and_then(|metadata| {
            if committed.metadata == Some(metadata) {
                Ok(metadata)
            } else {
                Err(error(AdapterErrorCodeV0::OutputIntegrityUncertain))
            }
        })
    });
    if integrity_result.is_ok() {
        complete(
            hooks,
            PublicationStageV0::HeldIntegrityVerify,
            Some(&committed.held),
        );
    }

    let identity_result = attempt(
        hooks,
        PublicationStageV0::FinalIdentityVerify,
        Some(&committed.held),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputIdentityUncertain));
    let identity_result = identity_result.and_then(|()| {
        let final_held = verify_held(
            hooks,
            &committed.held,
            HeldExpectationV0 {
                bytes,
                hash: &expected_hash,
                uid: committed.expected_uid,
                links: 1,
                property_code: AdapterErrorCodeV0::OutputIdentityUncertain,
                content_code: AdapterErrorCodeV0::OutputIdentityUncertain,
            },
        );
        let expected_metadata = match (&integrity_result, final_held) {
            (Ok(integrity_metadata), Ok(final_metadata))
                if *integrity_metadata == final_metadata
                    && committed.metadata == Some(final_metadata) =>
            {
                Some(final_metadata)
            }
            (Ok(_), _) => return Err(error(AdapterErrorCodeV0::OutputIdentityUncertain)),
            (Err(_), Ok(final_metadata)) => Some(final_metadata),
            (Err(_), Err(_)) => None,
        };
        verify_final_identity(
            &committed.parent_path,
            &committed.name,
            committed.identity,
            expected_metadata,
            committed.expected_uid,
            bytes.len(),
        )
    });
    if identity_result.is_ok() {
        complete(
            hooks,
            PublicationStageV0::FinalIdentityVerify,
            Some(&committed.held),
        );
    }

    if source_identity_result.is_err() || identity_result.is_err() {
        return Err(error(AdapterErrorCodeV0::OutputIdentityUncertain));
    }
    if integrity_result.is_err() {
        return Err(error(AdapterErrorCodeV0::OutputIntegrityUncertain));
    }
    if sync_result.is_err() {
        return Err(error(AdapterErrorCodeV0::DurabilityUncertain));
    }

    Ok(())
}

fn attempt(
    hooks: &mut impl PublicationHooksV0,
    stage: PublicationStageV0,
    held: Option<&OwnedFd>,
) -> Result<(), AdapterErrorV0> {
    hooks.event(PublicationEventV0::Attempted(stage), held);
    if hooks.fail_before(stage, held) {
        Err(error(AdapterErrorCodeV0::OutputPublish))
    } else {
        Ok(())
    }
}

fn complete(
    hooks: &mut impl PublicationHooksV0,
    stage: PublicationStageV0,
    held: Option<&OwnedFd>,
) {
    hooks.event(PublicationEventV0::Completed(stage), held);
}

fn write_all(
    hooks: &mut impl PublicationHooksV0,
    held: &OwnedFd,
    bytes: &[u8],
) -> Result<(), AdapterErrorV0> {
    let mut written = 0;
    while written < bytes.len() {
        match hooks.write(held, &bytes[written..]) {
            Ok(0) => return Err(error(AdapterErrorCodeV0::OutputPublish)),
            Ok(count) => written += count,
            Err(Errno::INTR) => {}
            Err(_) => return Err(error(AdapterErrorCodeV0::OutputPublish)),
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct HeldExpectationV0<'a> {
    bytes: &'a [u8],
    hash: &'a [u8],
    uid: u32,
    links: u64,
    property_code: AdapterErrorCodeV0,
    content_code: AdapterErrorCodeV0,
}

fn verify_held(
    hooks: &mut impl PublicationHooksV0,
    held: &OwnedFd,
    expected: HeldExpectationV0<'_>,
) -> Result<StableMetadataV0, AdapterErrorV0> {
    let before = fstat(held).map_err(|_| error(expected.content_code))?;
    let expected_len =
        u64::try_from(expected.bytes.len()).map_err(|_| error(expected.content_code))?;
    if !temporary_properties_are_exact(
        FileType::from_raw_mode(before.st_mode),
        rustix::process::geteuid().as_raw(),
        expected.uid,
        widen_u64(before.st_uid),
        widen_u64(before.st_mode),
        widen_u64(before.st_nlink),
        expected.links,
    ) {
        return Err(error(expected.property_code));
    }
    if u64::try_from(before.st_size).ok() != Some(expected_len) {
        return Err(error(expected.content_code));
    }
    let mut bytes = Vec::with_capacity(expected.bytes.len());
    let mut offset = 0_u64;
    while bytes.len() < expected.bytes.len() {
        let mut chunk = [0_u8; VERIFY_CHUNK_BYTES];
        let remaining = expected.bytes.len() - bytes.len();
        let count = loop {
            match hooks.pread(
                held,
                &mut chunk[..remaining.min(VERIFY_CHUNK_BYTES)],
                offset,
            ) {
                Ok(count) => break count,
                Err(Errno::INTR) => {}
                Err(_) => return Err(error(expected.content_code)),
            }
        };
        if count == 0 {
            return Err(error(expected.content_code));
        }
        bytes.extend_from_slice(&chunk[..count]);
        offset = offset
            .checked_add(u64::try_from(count).map_err(|_| error(expected.content_code))?)
            .ok_or_else(|| error(expected.content_code))?;
    }
    let mut eof = [0_u8; 1];
    let eof_count = loop {
        match hooks.pread(held, &mut eof, offset) {
            Ok(count) => break count,
            Err(Errno::INTR) => {}
            Err(_) => return Err(error(expected.content_code)),
        }
    };
    if eof_count != 0 || bytes != expected.bytes || &Sha256::digest(&bytes)[..] != expected.hash {
        return Err(error(expected.content_code));
    }
    let after = fstat(held).map_err(|_| error(expected.content_code))?;
    if stable_metadata(&before) != stable_metadata(&after) {
        return Err(error(expected.content_code));
    }
    Ok(stable_metadata(&after))
}

fn temporary_properties_are_exact(
    file_type: FileType,
    current_uid: u32,
    expected_uid: u32,
    stat_uid: u64,
    mode: u64,
    nlink: u64,
    expected_links: u64,
) -> bool {
    file_type == FileType::RegularFile
        && current_uid == expected_uid
        && stat_uid == u64::from(expected_uid)
        && mode & 0o7777 == u64::from(OUTPUT_MODE)
        && nlink == expected_links
}

fn verify_final_identity(
    parent: &OwnedFd,
    name: &OsString,
    expected: IdentityV0,
    expected_metadata: Option<StableMetadataV0>,
    expected_uid: u32,
    expected_len: usize,
) -> Result<(), AdapterErrorV0> {
    let stat = statat(parent, name, AtFlags::SYMLINK_NOFOLLOW)
        .map_err(|_| error(AdapterErrorCodeV0::OutputIdentityUncertain))?;
    if identity(&stat) != expected
        || FileType::from_raw_mode(stat.st_mode) != FileType::RegularFile
        || rustix::process::geteuid().as_raw() != expected_uid
        || widen_u64(stat.st_uid) != u64::from(expected_uid)
        || widen_u64(stat.st_mode) & 0o7777 != u64::from(OUTPUT_MODE)
        || widen_u64(stat.st_nlink) != 1
        || usize::try_from(stat.st_size).ok() != Some(expected_len)
    {
        return Err(error(AdapterErrorCodeV0::OutputIdentityUncertain));
    }
    if expected_metadata.is_some_and(|expected| stable_metadata(&stat) != expected) {
        return Err(error(AdapterErrorCodeV0::OutputIdentityUncertain));
    }
    Ok(())
}

fn verify_proc_source(
    proc: &OwnedFd,
    source: &str,
    expected: IdentityV0,
) -> Result<(), AdapterErrorV0> {
    let stat = statat(proc, source, AtFlags::empty())
        .map_err(|_| error(AdapterErrorCodeV0::UnsupportedPublicationProfile))?;
    if identity(&stat) != expected || FileType::from_raw_mode(stat.st_mode) != FileType::RegularFile
    {
        return Err(error(AdapterErrorCodeV0::UnsupportedPublicationProfile));
    }
    Ok(())
}

fn verify_temporary_flags(held: &OwnedFd) -> Result<(), AdapterErrorV0> {
    let status = fcntl_getfl(held).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    let descriptor = fcntl_getfd(held).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    let allowed = OFlags::ACCMODE | OFlags::TMPFILE | OFlags::LARGEFILE;
    if !flags_are_exact(status, descriptor, OFlags::RDWR, OFlags::TMPFILE, allowed) {
        return Err(error(AdapterErrorCodeV0::UnsupportedPublicationProfile));
    }
    Ok(())
}

fn verify_sync_directory(directory: &OwnedFd, expected: IdentityV0) -> Result<(), AdapterErrorV0> {
    let stat = fstat(directory).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    let status = fcntl_getfl(directory).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    let descriptor =
        fcntl_getfd(directory).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
    let allowed = OFlags::ACCMODE | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::LARGEFILE;
    if identity(&stat) != expected
        || FileType::from_raw_mode(stat.st_mode) != FileType::Directory
        || !flags_are_exact(
            status,
            descriptor,
            OFlags::RDONLY,
            OFlags::DIRECTORY,
            allowed,
        )
    {
        return Err(error(AdapterErrorCodeV0::UnsupportedPublicationProfile));
    }
    Ok(())
}

fn flags_are_exact(
    status: OFlags,
    descriptor: FdFlags,
    access: OFlags,
    required: OFlags,
    allowed: OFlags,
) -> bool {
    status & OFlags::ACCMODE == access
        && status.contains(required)
        && status.bits() & !allowed.bits() == 0
        && descriptor == FdFlags::CLOEXEC
}

fn preflight_final(
    parent: &OwnedFd,
    name: &OsString,
    inputs: &[&SnapshotV0],
    protected: &[&CommittedPublicationV0],
) -> Result<(), AdapterErrorV0> {
    match statat(parent, name, AtFlags::SYMLINK_NOFOLLOW) {
        Ok(stat) if FileType::from_raw_mode(stat.st_mode) == FileType::Symlink => {
            Err(error(AdapterErrorCodeV0::OutputSymlink))
        }
        Ok(stat) if protected_alias(&stat, protected) => {
            Err(error(AdapterErrorCodeV0::CrossOutputAlias))
        }
        Ok(stat) if input_alias(&stat, inputs) => Err(error(AdapterErrorCodeV0::InputAlias)),
        Ok(_) => Err(error(AdapterErrorCodeV0::OutputExists)),
        Err(Errno::NOENT) => Ok(()),
        Err(_) => Err(error(AdapterErrorCodeV0::OutputPublish)),
    }
}

fn classify_incumbent(
    parent: &OwnedFd,
    name: &OsString,
    inputs: &[&SnapshotV0],
    protected: &[&CommittedPublicationV0],
) -> AdapterErrorV0 {
    match statat(parent, name, AtFlags::SYMLINK_NOFOLLOW) {
        Ok(stat) if FileType::from_raw_mode(stat.st_mode) == FileType::Symlink => {
            error(AdapterErrorCodeV0::OutputSymlink)
        }
        Ok(stat) if protected_alias(&stat, protected) => {
            error(AdapterErrorCodeV0::CrossOutputAlias)
        }
        Ok(stat) if input_alias(&stat, inputs) => error(AdapterErrorCodeV0::InputAlias),
        Ok(_) => error(AdapterErrorCodeV0::OutputExists),
        Err(_) => error(AdapterErrorCodeV0::OutputPublish),
    }
}

fn protected_alias(stat: &Stat, protected: &[&CommittedPublicationV0]) -> bool {
    let candidate = identity(stat);
    protected
        .iter()
        .any(|publication| publication.identity == candidate)
}

fn input_alias(stat: &Stat, inputs: &[&SnapshotV0]) -> bool {
    let candidate = identity(stat);
    inputs
        .iter()
        .any(|input| (input.dev, input.ino) == (candidate.dev, candidate.ino))
}

fn pin_start(absolute: bool) -> Result<OwnedFd, AdapterErrorV0> {
    openat(
        rustix::fs::CWD,
        if absolute {
            Path::new("/")
        } else {
            Path::new(".")
        },
        OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))
}

fn require_directory(stat: &Stat) -> Result<(), AdapterErrorV0> {
    let file_type = FileType::from_raw_mode(stat.st_mode);
    if file_type == FileType::Directory {
        Ok(())
    } else if file_type == FileType::Symlink {
        Err(error(AdapterErrorCodeV0::OutputSymlink))
    } else {
        Err(error(AdapterErrorCodeV0::OutputPublish))
    }
}

fn same_directory(left: &Stat, right: &Stat) -> bool {
    FileType::from_raw_mode(right.st_mode) == FileType::Directory
        && identity(left) == identity(right)
}

struct ParsedOutputPathV0 {
    absolute: bool,
    ancestors: Vec<OsString>,
    final_name: OsString,
}

fn parse_output_path(path: &Path) -> Result<ParsedOutputPathV0, AdapterErrorV0> {
    let raw = path.as_os_str().as_bytes();
    if raw.is_empty() || raw.contains(&0) {
        return Err(error(AdapterErrorCodeV0::UnsafeOutputPath));
    }
    let mut names = Vec::new();
    for component in path.components() {
        match component {
            Component::RootDir | Component::CurDir => {}
            Component::Normal(name) => names.push(name.to_os_string()),
            Component::ParentDir | Component::Prefix(_) => {
                return Err(error(AdapterErrorCodeV0::UnsafeOutputPath));
            }
        }
    }
    if raw.ends_with(b"/") || raw == b"." || raw == b"./" || raw.ends_with(b"/.") {
        return Err(error(AdapterErrorCodeV0::UnsafeOutputPath));
    }
    let final_name = names
        .pop()
        .ok_or_else(|| error(AdapterErrorCodeV0::UnsafeOutputPath))?;
    Ok(ParsedOutputPathV0 {
        absolute: raw.starts_with(b"/"),
        ancestors: names,
        final_name,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct IdentityV0 {
    dev: u64,
    ino: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct StableMetadataV0 {
    dev: u64,
    ino: u64,
    mode: u64,
    uid: u64,
    gid: u64,
    nlink: u64,
    size: i128,
    mtime: i128,
    mtime_nsec: i128,
    ctime: i128,
    ctime_nsec: i128,
}

fn identity(stat: &Stat) -> IdentityV0 {
    IdentityV0 {
        dev: widen_u64(stat.st_dev),
        ino: widen_u64(stat.st_ino),
    }
}

fn stable_metadata(stat: &Stat) -> StableMetadataV0 {
    StableMetadataV0 {
        dev: widen_u64(stat.st_dev),
        ino: widen_u64(stat.st_ino),
        mode: widen_u64(stat.st_mode),
        uid: widen_u64(stat.st_uid),
        gid: widen_u64(stat.st_gid),
        nlink: widen_u64(stat.st_nlink),
        size: widen_i128(stat.st_size),
        mtime: widen_i128(stat.st_mtime),
        mtime_nsec: widen_i128(stat.st_mtime_nsec),
        ctime: widen_i128(stat.st_ctime),
        ctime_nsec: widen_i128(stat.st_ctime_nsec),
    }
}

fn is_link_profile_errno(errno: Errno) -> bool {
    matches!(
        errno,
        Errno::XDEV | Errno::NOTSUP | Errno::NOSYS | Errno::INVAL
    )
}

fn is_profile_errno(errno: Errno) -> bool {
    matches!(
        errno,
        Errno::NOTSUP | Errno::NOSYS | Errno::INVAL | Errno::ISDIR
    )
}

fn publication_errno(errno: Errno, profile: bool) -> AdapterErrorV0 {
    error(if profile || is_profile_errno(errno) {
        AdapterErrorCodeV0::UnsupportedPublicationProfile
    } else {
        AdapterErrorCodeV0::OutputPublish
    })
}

fn widen_u64<T: Into<u64>>(value: T) -> u64 {
    value.into()
}

fn widen_i128<T: Into<i128>>(value: T) -> i128 {
    value.into()
}

fn error(code: AdapterErrorCodeV0) -> AdapterErrorV0 {
    AdapterErrorV0::from_code(code)
}

#[path = "linux_output_rollback.rs"]
mod rollback;
use rollback::rollback_committed;
#[cfg(test)]
use rollback::rollback_committed_with_hooks;

#[path = "linux_output_transaction.rs"]
mod transaction;
pub(crate) use transaction::{PublicationSpecV0, publish_directory_set, publish_pair, publish_set};

#[cfg(test)]
#[path = "linux_output_tests.rs"]
mod tests;
