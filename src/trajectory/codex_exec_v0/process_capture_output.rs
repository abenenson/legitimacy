//! Owner-private no-clobber process-capture output transaction.

use super::{AdapterErrorCodeV0, AdapterResultV0, FileSnapshot, error};
use rustix::fs::{AtFlags, Dir, Mode, OFlags, fsync, mkdirat, open, openat, unlinkat};
use std::collections::BTreeSet;
use std::ffi::OsString;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom, Write};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::Path;

pub(super) const OUTPUTS: &[&str] = &[
    "stdin.bin",
    "stdout.jsonl",
    "stderr.bin",
    "process-capture-receipt.json",
];

pub(super) fn path_components(path: &Path) -> AdapterResultV0<Vec<OsString>> {
    let mut components = Vec::new();
    for component in path.components() {
        match component {
            std::path::Component::RootDir => {}
            std::path::Component::Normal(value) if !value.as_bytes().contains(&0) => {
                components.push(value.to_os_string());
            }
            _ => return Err(error(AdapterErrorCodeV0::UnsafeInputPath)),
        }
    }
    Ok(components)
}

pub(super) fn publish_output_directory(path: &Path, contents: [&[u8]; 4]) -> AdapterResultV0<()> {
    publish_output_directory_with_operations(path, contents, &mut RealOutputOperations)
}

pub(super) trait OutputOperations {
    fn write_file(&mut self, file: &mut File, content: &[u8], index: usize) -> AdapterResultV0<()>;
    fn sync_file(&mut self, file: &File, index: usize) -> AdapterResultV0<()>;
    fn revalidate_held_and_named(&mut self) -> AdapterResultV0<()>;
    fn sync_directory_before_acceptance(
        &mut self,
        directory: &std::os::fd::OwnedFd,
    ) -> AdapterResultV0<()>;
    fn sync_parent_before_acceptance(
        &mut self,
        parent: &std::os::fd::OwnedFd,
    ) -> AdapterResultV0<()>;
    fn unlink_rollback(
        &mut self,
        directory: &std::os::fd::OwnedFd,
        name: &str,
    ) -> AdapterResultV0<()>;
    fn remove_directory_rollback(
        &mut self,
        parent: &std::os::fd::OwnedFd,
        name: &std::ffi::OsStr,
    ) -> AdapterResultV0<()>;
    fn sync_parent_rollback(&mut self, parent: &std::os::fd::OwnedFd) -> AdapterResultV0<()>;
}

pub(super) struct RealOutputOperations;

impl OutputOperations for RealOutputOperations {
    fn write_file(
        &mut self,
        file: &mut File,
        content: &[u8],
        _index: usize,
    ) -> AdapterResultV0<()> {
        file.write_all(content)
            .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))
    }

    fn sync_file(&mut self, file: &File, _index: usize) -> AdapterResultV0<()> {
        file.sync_all()
            .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))
    }

    fn revalidate_held_and_named(&mut self) -> AdapterResultV0<()> {
        Ok(())
    }

    fn sync_directory_before_acceptance(
        &mut self,
        directory: &std::os::fd::OwnedFd,
    ) -> AdapterResultV0<()> {
        fsync(directory).map_err(|_| error(AdapterErrorCodeV0::DurabilityUncertain))
    }

    fn sync_parent_before_acceptance(
        &mut self,
        parent: &std::os::fd::OwnedFd,
    ) -> AdapterResultV0<()> {
        fsync(parent).map_err(|_| error(AdapterErrorCodeV0::DurabilityUncertain))
    }

    fn unlink_rollback(
        &mut self,
        directory: &std::os::fd::OwnedFd,
        name: &str,
    ) -> AdapterResultV0<()> {
        match unlinkat(directory, name, AtFlags::empty()) {
            Ok(()) | Err(rustix::io::Errno::NOENT) => Ok(()),
            Err(_) => Err(error(AdapterErrorCodeV0::CaptureCleanup)),
        }
    }

    fn remove_directory_rollback(
        &mut self,
        parent: &std::os::fd::OwnedFd,
        name: &std::ffi::OsStr,
    ) -> AdapterResultV0<()> {
        unlinkat(parent, name, AtFlags::REMOVEDIR)
            .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))
    }

    fn sync_parent_rollback(&mut self, parent: &std::os::fd::OwnedFd) -> AdapterResultV0<()> {
        fsync(parent).map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))
    }
}

pub(super) fn publish_output_directory_with_operations(
    path: &Path,
    contents: [&[u8]; 4],
    operations: &mut impl OutputOperations,
) -> AdapterResultV0<()> {
    if !path.is_absolute() {
        return Err(error(AdapterErrorCodeV0::UnsafeOutputPath));
    }
    let components = path_components(path)?;
    let (final_name, parents) = components
        .split_last()
        .ok_or_else(|| error(AdapterErrorCodeV0::UnsafeOutputPath))?;
    let mut parent = open(
        "/",
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::UnsafeOutputPath))?;
    for component in parents {
        parent = openat(
            &parent,
            component.as_os_str(),
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
            Mode::empty(),
        )
        .map_err(|_| error(AdapterErrorCodeV0::UnsafeOutputPath))?;
    }
    let parent_metadata = File::from(
        rustix::io::dup(&parent).map_err(|_| error(AdapterErrorCodeV0::UnsafeOutputPath))?,
    )
    .metadata()
    .map_err(|_| error(AdapterErrorCodeV0::UnsafeOutputPath))?;
    if parent_metadata.uid() != rustix::process::geteuid().as_raw()
        || parent_metadata.permissions().mode() & 0o7777 != 0o700
    {
        return Err(error(AdapterErrorCodeV0::UnsafeOutputPath));
    }
    match mkdirat(&parent, final_name.as_os_str(), Mode::from_raw_mode(0o700)) {
        Ok(()) => {}
        Err(rustix::io::Errno::EXIST) => {
            return Err(error(AdapterErrorCodeV0::OutputExists));
        }
        Err(_) => return Err(error(AdapterErrorCodeV0::OutputPublish)),
    }
    let directory = match openat(
        &parent,
        final_name.as_os_str(),
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    ) {
        Ok(directory) => directory,
        Err(_) => {
            if unlinkat(&parent, final_name.as_os_str(), AtFlags::REMOVEDIR).is_err()
                || fsync(&parent).is_err()
            {
                return Err(error(AdapterErrorCodeV0::CaptureCleanup));
            }
            return Err(error(AdapterErrorCodeV0::OutputPublish));
        }
    };
    let result = (|| {
        let directory_metadata = File::from(
            rustix::io::dup(&directory).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?,
        )
        .metadata()
        .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
        if !directory_metadata.is_dir()
            || directory_metadata.uid() != rustix::process::geteuid().as_raw()
            || directory_metadata.permissions().mode() & 0o7777 != 0o700
        {
            return Err(error(AdapterErrorCodeV0::OutputPublish));
        }
        let directory_identity = (
            directory_metadata.dev(),
            directory_metadata.ino(),
            directory_metadata.uid(),
            directory_metadata.permissions().mode() & 0o7777,
        );
        let mut held_outputs = Vec::with_capacity(OUTPUTS.len());
        for (index, (name, expected_content)) in OUTPUTS.iter().zip(contents).enumerate() {
            let descriptor = openat(
                &directory,
                *name,
                OFlags::RDWR | OFlags::CREATE | OFlags::EXCL | OFlags::NOFOLLOW | OFlags::CLOEXEC,
                Mode::from_raw_mode(0o600),
            )
            .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
            let mut file = File::from(descriptor);
            operations
                .write_file(&mut file, expected_content, index)
                .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
            operations
                .sync_file(&file, index)
                .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
            let metadata = file
                .metadata()
                .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
            if !metadata.is_file()
                || metadata.uid() != rustix::process::geteuid().as_raw()
                || metadata.permissions().mode() & 0o7777 != 0o600
                || metadata.nlink() != 1
                || metadata.len() != expected_content.len() as u64
            {
                return Err(error(AdapterErrorCodeV0::OutputPublish));
            }
            file.seek(SeekFrom::Start(0))
                .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
            let mut observed = Vec::with_capacity(expected_content.len());
            file.read_to_end(&mut observed)
                .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
            if observed != expected_content {
                return Err(error(AdapterErrorCodeV0::OutputPublish));
            }
            let snapshot = FileSnapshot::from_metadata(&metadata);
            held_outputs.push((*name, file, snapshot, expected_content));
        }
        let named_directory = openat(
            &parent,
            final_name.as_os_str(),
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
            Mode::empty(),
        )
        .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
        let named_directory_metadata = File::from(
            rustix::io::dup(&named_directory)
                .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?,
        )
        .metadata()
        .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
        if (
            named_directory_metadata.dev(),
            named_directory_metadata.ino(),
            named_directory_metadata.uid(),
            named_directory_metadata.permissions().mode() & 0o7777,
        ) != directory_identity
        {
            return Err(error(AdapterErrorCodeV0::OutputPublish));
        }
        let mut observed_names = BTreeSet::new();
        let mut entries =
            Dir::read_from(&directory).map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
        while let Some(entry) = entries.read() {
            let entry = entry.map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
            if !matches!(entry.file_name().to_bytes(), b"." | b"..") {
                observed_names.insert(entry.file_name().to_bytes().to_vec());
            }
        }
        let expected_names = OUTPUTS
            .iter()
            .map(|name| name.as_bytes().to_vec())
            .collect::<BTreeSet<_>>();
        if observed_names != expected_names {
            return Err(error(AdapterErrorCodeV0::OutputPublish));
        }
        operations
            .revalidate_held_and_named()
            .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
        for (name, mut held, snapshot, expected_content) in held_outputs {
            let reopened = File::from(
                openat(
                    &directory,
                    name,
                    OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
                    Mode::empty(),
                )
                .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?,
            );
            let held_metadata = held
                .metadata()
                .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
            let reopened_metadata = reopened
                .metadata()
                .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
            if FileSnapshot::from_metadata(&held_metadata) != snapshot
                || FileSnapshot::from_metadata(&reopened_metadata) != snapshot
                || !reopened_metadata.is_file()
                || reopened_metadata.nlink() != 1
            {
                return Err(error(AdapterErrorCodeV0::OutputPublish));
            }
            held.seek(SeekFrom::Start(0))
                .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
            let mut held_bytes = Vec::new();
            held.read_to_end(&mut held_bytes)
                .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
            let mut reopened_bytes = Vec::new();
            reopened
                .take((expected_content.len() as u64).saturating_add(1))
                .read_to_end(&mut reopened_bytes)
                .map_err(|_| error(AdapterErrorCodeV0::OutputPublish))?;
            if held_bytes != expected_content || reopened_bytes != expected_content {
                return Err(error(AdapterErrorCodeV0::OutputPublish));
            }
        }
        operations
            .sync_directory_before_acceptance(&directory)
            .map_err(|_| error(AdapterErrorCodeV0::DurabilityUncertain))?;
        operations
            .sync_parent_before_acceptance(&parent)
            .map_err(|_| error(AdapterErrorCodeV0::DurabilityUncertain))
    })();
    if result.is_err() {
        let mut cleanup_ok = true;
        for name in OUTPUTS {
            if operations.unlink_rollback(&directory, name).is_err() {
                cleanup_ok = false;
            }
        }
        drop(directory);
        if operations
            .remove_directory_rollback(&parent, final_name.as_os_str())
            .is_err()
        {
            cleanup_ok = false;
        }
        if operations.sync_parent_rollback(&parent).is_err() {
            cleanup_ok = false;
        }
        if !cleanup_ok {
            return Err(error(AdapterErrorCodeV0::CaptureCleanup));
        }
    }
    result
}
