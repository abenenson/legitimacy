use rustix::fs::{AtFlags, FileType, Mode, OFlags, Stat, fstat, open, openat, statat};
use std::ffi::OsString;
use std::os::unix::ffi::OsStrExt;
use std::path::{Component, Path};

pub(crate) const ROOT_OBJECT_CHANGED: &str = "repository-root-object-changed";
pub(crate) const INPUT_SYMLINK: &str = "selected-input-symlink";
pub(crate) const INPUT_NONREGULAR: &str = "selected-input-nonregular";
pub(crate) const INPUT_ROOT_ESCAPE: &str = "selected-input-root-escape";
pub(crate) const INPUT_IDENTITY_CHANGED: &str = "selected-input-identity-changed";
pub(crate) const INPUT_CONTENT_CHANGED: &str = "selected-input-content-changed";
pub(crate) const INPUT_PATH: &str = "selected-input-path";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ReadStage {
    AfterOpen,
    AfterFirstChunk,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Identity {
    device: u64,
    inode: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct StableMetadata {
    identity: Identity,
    mode: u32,
    links: u64,
    size: i64,
    modified_seconds: i64,
    modified_nanoseconds: u64,
    changed_seconds: i64,
    changed_nanoseconds: u64,
}

pub(crate) fn read_repository_file(
    root: &Path,
    relative: &str,
    cap: usize,
) -> Result<Vec<u8>, &'static str> {
    read_repository_file_with_hook(root, relative, cap, |_| {})
}

pub(crate) fn read_repository_file_with_hook(
    root: &Path,
    relative: &str,
    cap: usize,
    mut hook: impl FnMut(ReadStage),
) -> Result<Vec<u8>, &'static str> {
    let canonical_root = std::fs::canonicalize(root).map_err(|_| ROOT_OBJECT_CHANGED)?;
    if !canonical_root.is_dir() {
        return Err(ROOT_OBJECT_CHANGED);
    }
    let root_fd = open(
        root,
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| ROOT_OBJECT_CHANGED)?;
    let root_identity = identity(&fstat(&root_fd).map_err(|_| ROOT_OBJECT_CHANGED)?);
    let components = relative_components(relative)?;
    let mut held_directories = Vec::new();
    let mut component_identities = Vec::new();
    let mut current = &root_fd;
    for component in &components[..components.len() - 1] {
        let before = stat_component(current, component)?;
        let kind = FileType::from_raw_mode(before.st_mode);
        if kind.is_symlink() {
            return Err(INPUT_SYMLINK);
        }
        if !kind.is_dir() {
            return Err(INPUT_NONREGULAR);
        }
        let directory = openat(
            current,
            component,
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
            Mode::empty(),
        )
        .map_err(|_| INPUT_IDENTITY_CHANGED)?;
        let opened = fstat(&directory).map_err(|_| INPUT_IDENTITY_CHANGED)?;
        if identity(&before) != identity(&opened) {
            return Err(INPUT_IDENTITY_CHANGED);
        }
        component_identities.push(identity(&opened));
        held_directories.push(directory);
        current = held_directories.last().ok_or(INPUT_IDENTITY_CHANGED)?;
    }
    let final_name = components.last().ok_or(INPUT_PATH)?;
    let before = stat_component(current, final_name)?;
    let final_kind = FileType::from_raw_mode(before.st_mode);
    if final_kind.is_symlink() {
        return Err(INPUT_SYMLINK);
    }
    if !final_kind.is_file() {
        return Err(INPUT_NONREGULAR);
    }
    let file = openat(
        current,
        final_name,
        OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| INPUT_IDENTITY_CHANGED)?;
    let opened = fstat(&file).map_err(|_| INPUT_IDENTITY_CHANGED)?;
    if identity(&before) != identity(&opened) || !FileType::from_raw_mode(opened.st_mode).is_file()
    {
        return Err(INPUT_IDENTITY_CHANGED);
    }
    let initial_metadata = stable_metadata(&opened);
    let resolved = std::fs::canonicalize(root.join(relative)).map_err(|_| INPUT_ROOT_ESCAPE)?;
    if resolved == canonical_root || !resolved.starts_with(&canonical_root) {
        return Err(INPUT_ROOT_ESCAPE);
    }

    hook(ReadStage::AfterOpen);
    let mut bytes = Vec::with_capacity((initial_metadata.size.max(0) as usize).min(cap));
    let mut chunk = [0u8; 16 * 1024];
    let mut first = true;
    loop {
        let length = rustix::io::read(&file, &mut chunk).map_err(|_| INPUT_CONTENT_CHANGED)?;
        if length == 0 {
            break;
        }
        let next = bytes
            .len()
            .checked_add(length)
            .ok_or(INPUT_CONTENT_CHANGED)?;
        if next > cap {
            return Err(INPUT_CONTENT_CHANGED);
        }
        bytes.extend_from_slice(&chunk[..length]);
        if first {
            first = false;
            hook(ReadStage::AfterFirstChunk);
        }
    }
    let mut verified = 0usize;
    while verified < bytes.len() {
        let length = rustix::io::pread(
            &file,
            &mut chunk,
            u64::try_from(verified).map_err(|_| INPUT_CONTENT_CHANGED)?,
        )
        .map_err(|_| INPUT_CONTENT_CHANGED)?;
        if length == 0
            || length > bytes.len() - verified
            || chunk[..length] != bytes[verified..verified + length]
        {
            return Err(INPUT_CONTENT_CHANGED);
        }
        verified = verified.checked_add(length).ok_or(INPUT_CONTENT_CHANGED)?;
    }
    if rustix::io::pread(
        &file,
        &mut chunk[..1],
        u64::try_from(bytes.len()).map_err(|_| INPUT_CONTENT_CHANGED)?,
    )
    .map_err(|_| INPUT_CONTENT_CHANGED)?
        != 0
    {
        return Err(INPUT_CONTENT_CHANGED);
    }
    revalidate_path(
        root,
        root_identity,
        &components,
        &component_identities,
        initial_metadata.identity,
    )?;
    let after = fstat(&file).map_err(|_| INPUT_IDENTITY_CHANGED)?;
    if stable_metadata(&after) != initial_metadata
        || usize::try_from(initial_metadata.size).ok() != Some(bytes.len())
    {
        return Err(INPUT_CONTENT_CHANGED);
    }
    Ok(bytes)
}

fn relative_components(relative: &str) -> Result<Vec<OsString>, &'static str> {
    let path = Path::new(relative);
    if path.is_absolute() || relative.contains('\\') {
        return Err(INPUT_PATH);
    }
    let components = path
        .components()
        .map(|component| match component {
            Component::Normal(value) if !value.as_bytes().is_empty() => Ok(value.to_os_string()),
            _ => Err(INPUT_PATH),
        })
        .collect::<Result<Vec<_>, _>>()?;
    if components.is_empty() {
        return Err(INPUT_PATH);
    }
    Ok(components)
}

fn revalidate_path(
    root: &Path,
    root_identity: Identity,
    components: &[OsString],
    expected_directories: &[Identity],
    expected_file: Identity,
) -> Result<(), &'static str> {
    let reopened_root = open(
        root,
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| ROOT_OBJECT_CHANGED)?;
    if identity(&fstat(&reopened_root).map_err(|_| ROOT_OBJECT_CHANGED)?) != root_identity {
        return Err(ROOT_OBJECT_CHANGED);
    }
    let mut held = Vec::new();
    let mut current = &reopened_root;
    for (index, component) in components[..components.len() - 1].iter().enumerate() {
        let stat = stat_component(current, component)?;
        if FileType::from_raw_mode(stat.st_mode).is_symlink() {
            return Err(INPUT_SYMLINK);
        }
        if identity(&stat) != expected_directories[index] {
            return Err(INPUT_IDENTITY_CHANGED);
        }
        let directory = openat(
            current,
            component,
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
            Mode::empty(),
        )
        .map_err(|_| INPUT_IDENTITY_CHANGED)?;
        held.push(directory);
        current = held.last().ok_or(INPUT_IDENTITY_CHANGED)?;
    }
    let final_stat = stat_component(current, components.last().ok_or(INPUT_PATH)?)?;
    if FileType::from_raw_mode(final_stat.st_mode).is_symlink() {
        return Err(INPUT_SYMLINK);
    }
    if identity(&final_stat) != expected_file {
        return Err(INPUT_IDENTITY_CHANGED);
    }
    Ok(())
}

fn stat_component(
    parent: &impl std::os::fd::AsFd,
    component: &OsString,
) -> Result<Stat, &'static str> {
    statat(parent, component, AtFlags::SYMLINK_NOFOLLOW).map_err(|_| INPUT_IDENTITY_CHANGED)
}

fn identity(stat: &Stat) -> Identity {
    Identity {
        device: stat.st_dev,
        inode: stat.st_ino,
    }
}

fn stable_metadata(stat: &Stat) -> StableMetadata {
    StableMetadata {
        identity: identity(stat),
        mode: stat.st_mode,
        links: stat.st_nlink,
        size: stat.st_size,
        modified_seconds: stat.st_mtime,
        modified_nanoseconds: stat.st_mtime_nsec,
        changed_seconds: stat.st_ctime,
        changed_nanoseconds: stat.st_ctime_nsec,
    }
}
