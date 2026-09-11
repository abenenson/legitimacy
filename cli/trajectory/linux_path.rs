use legitimacy::trajectory::codex_exec_v0::{AdapterErrorCodeV0, AdapterErrorV0};
use rustix::fd::{AsRawFd, OwnedFd};
use rustix::fs::{
    AtFlags, FileType, Mode, OFlags, PROC_SUPER_MAGIC, Stat, fcntl_getfl, fstat, fstatfs, openat,
    statat,
};
use rustix::io::{Errno, FdFlags, fcntl_getfd};
use sha2::{Digest, Sha256};
use std::ffi::OsString;
use std::os::unix::ffi::OsStrExt;
use std::path::{Component, Path};
use zeroize::Zeroizing;

const READ_CHUNK_BYTES: usize = 64 * 1024;

pub(crate) struct SnapshotV0 {
    pub(crate) bytes: Zeroizing<Vec<u8>>,
    pub(crate) dev: u64,
    pub(crate) ino: u64,
    mode: u64,
    uid: u64,
    baseline: FingerprintV0,
    expected_len: usize,
    expected_sha256: [u8; 32],
    reader: OwnedFd,
}

pub(crate) trait SnapshotHooksV0 {
    fn before_ancestor_open(&mut self, _index: usize) {}

    fn before_final_open(&mut self) {}

    fn after_first_chunk(&mut self) {}

    fn after_staging_read(&mut self, _staging: &[u8], _read: usize) {}

    fn proc_root(&self) -> &Path {
        Path::new("/proc")
    }
}

struct NoSnapshotHooksV0;

impl SnapshotHooksV0 for NoSnapshotHooksV0 {}

pub(crate) fn read_snapshot(path: &Path, cap: usize) -> Result<SnapshotV0, AdapterErrorV0> {
    read_snapshot_with_hooks(path, cap, &mut NoSnapshotHooksV0)
}

pub(crate) fn read_snapshot_with_hooks(
    path: &Path,
    cap: usize,
    hooks: &mut impl SnapshotHooksV0,
) -> Result<SnapshotV0, AdapterErrorV0> {
    let parsed = parse_path(path)?;
    let mut parent = pin_start(parsed.absolute)?;

    for (index, component) in parsed.ancestors.iter().enumerate() {
        let observed = statat(&parent, component, AtFlags::SYMLINK_NOFOLLOW)
            .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
        require_initial_type(&observed, FileType::Directory)?;
        hooks.before_ancestor_open(index);
        let opened = openat(
            &parent,
            component,
            OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
            Mode::empty(),
        )
        .map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
        let pinned = fstat(&opened).map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
        if FileType::from_raw_mode(pinned.st_mode) != FileType::Directory
            || directory_identity(&observed) != directory_identity(&pinned)
        {
            return Err(error(AdapterErrorCodeV0::InputChanged));
        }
        parent = opened;
    }

    let observed = statat(&parent, &parsed.final_name, AtFlags::SYMLINK_NOFOLLOW)
        .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
    require_initial_type(&observed, FileType::RegularFile)?;
    hooks.before_final_open();
    let gate = openat(
        &parent,
        &parsed.final_name,
        OFlags::PATH | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
    let gate_stat = fstat(&gate).map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
    let baseline = fingerprint(&observed);
    if FileType::from_raw_mode(gate_stat.st_mode) != FileType::RegularFile
        || fingerprint(&gate_stat) != baseline
    {
        return Err(error(AdapterErrorCodeV0::InputChanged));
    }
    let expected_size =
        nonnegative_size(&gate_stat).ok_or_else(|| error(AdapterErrorCodeV0::InputChanged))?;
    verify_held_and_name(&gate, &parent, &parsed.final_name, baseline)?;

    let reader = match reopen_gate(&gate, hooks.proc_root()) {
        Ok(reader) => reader,
        Err(_) => {
            verify_held_and_name(&gate, &parent, &parsed.final_name, baseline)?;
            return Err(error(AdapterErrorCodeV0::UnsupportedInputProfile));
        }
    };
    if validate_reader(&reader, baseline).is_err() {
        verify_held_and_name(&gate, &parent, &parsed.final_name, baseline)?;
        return Err(error(AdapterErrorCodeV0::UnsupportedInputProfile));
    }

    let limit = cap
        .checked_add(1)
        .ok_or_else(|| error(AdapterErrorCodeV0::InputTooLarge))?;
    let staging_length = limit.min(READ_CHUNK_BYTES);
    let mut staging = Zeroizing::new(vec![0_u8; staging_length].into_boxed_slice());
    let mut bytes = Zeroizing::new(Vec::with_capacity(staging_length));
    let mut hook_fired = false;
    while bytes.len() < limit {
        let remaining = limit - bytes.len();
        let slice_length = remaining.min(staging.len());
        let read = loop {
            match rustix::io::read(&reader, &mut staging[..slice_length]) {
                Ok(read) => break read,
                Err(Errno::INTR) => {}
                Err(_) => {
                    verify_reader_and_name(&reader, &gate, &parent, &parsed.final_name, baseline)?;
                    return Err(error(AdapterErrorCodeV0::InputOpen));
                }
            }
        };
        if read == 0 {
            break;
        }
        hooks.after_staging_read(&staging, read);
        bytes.extend_from_slice(&staging[..read]);
        if !hook_fired {
            hook_fired = true;
            hooks.after_first_chunk();
        }
    }

    verify_reader_and_name(&reader, &gate, &parent, &parsed.final_name, baseline)?;
    if bytes.len() > cap {
        return Err(error(AdapterErrorCodeV0::InputTooLarge));
    }
    if u64::try_from(bytes.len()).ok() != Some(expected_size) {
        return Err(error(AdapterErrorCodeV0::InputChanged));
    }

    let expected_len = bytes.len();
    let expected_sha256 = Sha256::digest(&*bytes).into();
    Ok(SnapshotV0 {
        bytes,
        dev: baseline.dev,
        ino: baseline.ino,
        mode: baseline.mode,
        uid: baseline.uid,
        baseline,
        expected_len,
        expected_sha256,
        reader,
    })
}

impl SnapshotV0 {
    pub(crate) fn revalidate(&self) -> Result<(), AdapterErrorV0> {
        let before = fstat(&self.reader).map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
        if fingerprint(&before) != self.baseline {
            return Err(error(AdapterErrorCodeV0::InputChanged));
        }
        let mut observed = Zeroizing::new(Vec::with_capacity(self.expected_len));
        let mut offset = 0_u64;
        while observed.len() < self.expected_len {
            let mut chunk = [0_u8; READ_CHUNK_BYTES];
            let remaining = self.expected_len - observed.len();
            let count = loop {
                match rustix::io::pread(
                    &self.reader,
                    &mut chunk[..remaining.min(READ_CHUNK_BYTES)],
                    offset,
                ) {
                    Ok(count) => break count,
                    Err(Errno::INTR) => {}
                    Err(_) => return Err(error(AdapterErrorCodeV0::InputChanged)),
                }
            };
            if count == 0 {
                return Err(error(AdapterErrorCodeV0::InputChanged));
            }
            observed.extend_from_slice(&chunk[..count]);
            offset = offset
                .checked_add(
                    u64::try_from(count).map_err(|_| error(AdapterErrorCodeV0::InputChanged))?,
                )
                .ok_or_else(|| error(AdapterErrorCodeV0::InputChanged))?;
        }
        let mut eof = [0_u8; 1];
        let eof_count = rustix::io::pread(&self.reader, &mut eof, offset)
            .map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
        let after = fstat(&self.reader).map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
        if eof_count != 0
            || <[u8; 32]>::from(Sha256::digest(&*observed)) != self.expected_sha256
            || fingerprint(&after) != self.baseline
        {
            return Err(error(AdapterErrorCodeV0::InputChanged));
        }
        Ok(())
    }
}

pub(crate) fn require_owner_private(snapshot: &SnapshotV0) -> Result<(), AdapterErrorV0> {
    let permissions = snapshot.mode & 0o7777;
    if snapshot.uid != u64::from(rustix::process::geteuid().as_raw())
        || !matches!(permissions, 0o400 | 0o600)
    {
        return Err(error(AdapterErrorCodeV0::UnsupportedInputProfile));
    }
    Ok(())
}

pub(crate) fn reject_duplicate_inodes(snapshots: &[&SnapshotV0]) -> Result<(), AdapterErrorV0> {
    for (index, left) in snapshots.iter().enumerate() {
        if snapshots[index + 1..]
            .iter()
            .any(|right| (left.dev, left.ino) == (right.dev, right.ino))
        {
            return Err(error(AdapterErrorCodeV0::InputAlias));
        }
    }
    Ok(())
}

fn reopen_gate(gate: &OwnedFd, proc_root: &Path) -> Result<OwnedFd, AdapterErrorV0> {
    let proc = openat(
        rustix::fs::CWD,
        proc_root,
        OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::UnsupportedInputProfile))?;
    let filesystem =
        fstatfs(&proc).map_err(|_| error(AdapterErrorCodeV0::UnsupportedInputProfile))?;
    if filesystem.f_type != PROC_SUPER_MAGIC {
        return Err(error(AdapterErrorCodeV0::UnsupportedInputProfile));
    }
    let source = format!("self/fd/{}", gate.as_raw_fd());
    // This verified procfs gate is the sole intentional follow in input resolution.
    openat(
        &proc,
        source,
        OFlags::RDONLY | OFlags::NONBLOCK | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::UnsupportedInputProfile))
}

fn validate_reader(reader: &OwnedFd, baseline: FingerprintV0) -> Result<(), AdapterErrorV0> {
    let reader_stat =
        fstat(reader).map_err(|_| error(AdapterErrorCodeV0::UnsupportedInputProfile))?;
    if FileType::from_raw_mode(reader_stat.st_mode) != FileType::RegularFile
        || fingerprint(&reader_stat) != baseline
    {
        return Err(error(AdapterErrorCodeV0::UnsupportedInputProfile));
    }
    let status =
        fcntl_getfl(reader).map_err(|_| error(AdapterErrorCodeV0::UnsupportedInputProfile))?;
    let descriptor =
        fcntl_getfd(reader).map_err(|_| error(AdapterErrorCodeV0::UnsupportedInputProfile))?;
    if status & OFlags::ACCMODE != OFlags::RDONLY
        || !status.contains(OFlags::NONBLOCK)
        || status.contains(OFlags::PATH)
        || !descriptor.contains(FdFlags::CLOEXEC)
    {
        return Err(error(AdapterErrorCodeV0::UnsupportedInputProfile));
    }
    Ok(())
}

fn verify_held_and_name(
    gate: &OwnedFd,
    parent: &OwnedFd,
    final_name: &OsString,
    baseline: FingerprintV0,
) -> Result<(), AdapterErrorV0> {
    let held = fstat(gate).map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
    let named = statat(parent, final_name, AtFlags::SYMLINK_NOFOLLOW)
        .map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
    if FileType::from_raw_mode(held.st_mode) != FileType::RegularFile
        || FileType::from_raw_mode(named.st_mode) != FileType::RegularFile
        || fingerprint(&held) != baseline
        || fingerprint(&named) != baseline
    {
        return Err(error(AdapterErrorCodeV0::InputChanged));
    }
    Ok(())
}

fn verify_reader_and_name(
    reader: &OwnedFd,
    gate: &OwnedFd,
    parent: &OwnedFd,
    final_name: &OsString,
    baseline: FingerprintV0,
) -> Result<(), AdapterErrorV0> {
    verify_held_and_name(gate, parent, final_name, baseline)?;
    let reader_stat = fstat(reader).map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
    if FileType::from_raw_mode(reader_stat.st_mode) != FileType::RegularFile
        || fingerprint(&reader_stat) != baseline
    {
        return Err(error(AdapterErrorCodeV0::InputChanged));
    }
    Ok(())
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
    .map_err(|_| error(AdapterErrorCodeV0::InputOpen))
}

fn require_initial_type(stat: &Stat, expected: FileType) -> Result<(), AdapterErrorV0> {
    if let Some(code) = initial_type_error(FileType::from_raw_mode(stat.st_mode), expected) {
        Err(error(code))
    } else {
        Ok(())
    }
}

fn initial_type_error(actual: FileType, expected: FileType) -> Option<AdapterErrorCodeV0> {
    if actual == expected {
        None
    } else if actual == FileType::Symlink {
        Some(AdapterErrorCodeV0::InputSymlink)
    } else {
        Some(AdapterErrorCodeV0::InputType)
    }
}

struct ParsedPathV0 {
    absolute: bool,
    ancestors: Vec<OsString>,
    final_name: OsString,
}

fn parse_path(path: &Path) -> Result<ParsedPathV0, AdapterErrorV0> {
    let raw = path.as_os_str().as_bytes();
    if raw.is_empty() || raw.contains(&0) {
        return Err(error(AdapterErrorCodeV0::UnsafeInputPath));
    }

    let mut names = Vec::new();
    for component in path.components() {
        match component {
            Component::RootDir | Component::CurDir => {}
            Component::Normal(name) => names.push(name.to_os_string()),
            Component::ParentDir | Component::Prefix(_) => {
                return Err(error(AdapterErrorCodeV0::UnsafeInputPath));
            }
        }
    }
    if raw.ends_with(b"/") || raw == b"." || raw == b"./" || raw.ends_with(b"/.") {
        return Err(error(AdapterErrorCodeV0::InputType));
    }
    let final_name = names
        .pop()
        .ok_or_else(|| error(AdapterErrorCodeV0::InputType))?;
    Ok(ParsedPathV0 {
        absolute: raw.starts_with(b"/"),
        ancestors: names,
        final_name,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FingerprintV0 {
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DirectoryIdentityV0 {
    dev: u64,
    ino: u64,
    mode: u64,
    uid: u64,
    gid: u64,
}

fn directory_identity(stat: &Stat) -> DirectoryIdentityV0 {
    DirectoryIdentityV0 {
        dev: widen_u64(stat.st_dev),
        ino: widen_u64(stat.st_ino),
        mode: widen_u64(stat.st_mode),
        uid: widen_u64(stat.st_uid),
        gid: widen_u64(stat.st_gid),
    }
}

fn fingerprint(stat: &Stat) -> FingerprintV0 {
    FingerprintV0 {
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

fn widen_u64<T: Into<u64>>(value: T) -> u64 {
    value.into()
}

fn widen_i128<T: Into<i128>>(value: T) -> i128 {
    value.into()
}

fn nonnegative_size(stat: &Stat) -> Option<u64> {
    u64::try_from(stat.st_size).ok()
}

fn error(code: AdapterErrorCodeV0) -> AdapterErrorV0 {
    AdapterErrorV0::from_code(code)
}

#[cfg(test)]
#[path = "linux_path_tests.rs"]
mod tests;
