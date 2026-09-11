#![cfg(target_os = "linux")]

use super::*;
use crate::trajectory::codex_exec_v0::receipt::{
    InodeIdentityV0, InputAuthorityReceiptV0, ObservedProcessCaptureV0, ProcessCaptureReceiptV0,
    ProcessTerminationV0,
};
use flate2::read::GzDecoder;
use rustix::fs::{Dir, Mode, OFlags, fchmod, open, openat};
use sha2::{Digest, Sha256};
use std::collections::HashSet;
use std::ffi::CString;
#[cfg(test)]
use std::fs;
use std::fs::{File, Metadata};
use std::io::{Read, Seek, SeekFrom};
use std::os::fd::AsRawFd;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::Path;
use std::sync::Mutex;
use std::time::Duration;

const STDIN_CAP: usize = 1024 * 1024;
const STDERR_CAP: usize = 8 * 1024 * 1024;
const READ_CHUNK: usize = 64 * 1024;
const EXECUTABLE_FILE_CAP: u64 = 384 * 1024 * 1024;
const RELEASE_ARCHIVE_FILE_CAP: u64 = 256 * 1024 * 1024;
const SIGSTORE_BUNDLE_FILE_CAP: u64 = 4 * 1024 * 1024;
const CAPTURE_TOOL_FILE_CAP: u64 = 512 * 1024 * 1024;
#[path = "process_capture_cleanup.rs"]
mod cleanup;
#[path = "process_capture_output.rs"]
mod output;
#[path = "process_capture_signal.rs"]
mod signal;
#[path = "process_capture_supervision.rs"]
mod supervision;
#[path = "process_capture_supervisor.rs"]
mod supervisor;
#[cfg(test)]
use output::{OUTPUTS, publish_output_directory_with_operations};
use output::{path_components, publish_output_directory};
#[cfg(test)]
use supervision::ObservedTermination;
use supervisor::{execute_held, require_single_purpose_process};
static PROCESS_CAPTURE_LOCK: Mutex<()> = Mutex::new(());

pub(super) fn capture(request: &ProcessCaptureRequestV0) -> AdapterResultV0<()> {
    let _exclusive = PROCESS_CAPTURE_LOCK
        .lock()
        .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))?;
    require_single_purpose_process()?;
    let native = HeldFile::open(&request.native_executable, FileRole::Executable)?;
    require_digest(&native, super::super::PROCESS_CAPTURE_EXECUTABLE_SHA256_V0)?;
    if !native.starts_with(b"\x7fELF")? {
        return Err(error(AdapterErrorCodeV0::ReceiptMismatch));
    }
    let archive = HeldFile::open(&request.release_archive, FileRole::ReleaseArchive)?;
    require_digest(&archive, super::super::PROCESS_CAPTURE_RELEASE_SHA256_V0)?;
    let sigstore = HeldFile::open(&request.sigstore_bundle, FileRole::SigstoreBundle)?;
    require_digest(&sigstore, super::super::PROCESS_CAPTURE_SIGSTORE_SHA256_V0)?;
    let profile = HeldFile::open(&request.capture_profile_artifact, FileRole::CaptureProfile)?;
    if profile.read_bounded(super::super::CAPTURE_PROFILE_ARTIFACT_V0.len())?
        != super::super::CAPTURE_PROFILE_ARTIFACT_V0
    {
        return Err(error(AdapterErrorCodeV0::UnsupportedProfile));
    }
    let stdin = HeldFile::open(&request.stdin_artifact, FileRole::PrivateStdin)?;
    let stdin_bytes = stdin.read_bounded(STDIN_CAP)?;
    if stdin_bytes.is_empty() {
        return Err(error(AdapterErrorCodeV0::UnsupportedInputProfile));
    }
    let capture_tool = HeldRunningImage::open()?;
    reject_aliases([&native, &archive, &sigstore, &profile, &stdin])?;
    if [&native, &archive, &sigstore, &profile, &stdin]
        .iter()
        .any(|held| {
            held.snapshot.dev == capture_tool.snapshot.dev
                && held.snapshot.ino == capture_tool.snapshot.ino
        })
    {
        return Err(error(AdapterErrorCodeV0::InputAlias));
    }
    verify_archive_member(&archive, &native.digest)?;

    let mut workspace = HeldWorkspace::open(&request.workspace)?;
    let execution_workspace = workspace
        .file
        .try_clone()
        .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
    let execution = workspace.execute_read_only(|| {
        execute_held(
            &native,
            &execution_workspace,
            &stdin_bytes,
            Duration::from_secs(DEFAULT_TIMEOUT_SECONDS),
            super::super::MAX_CODEX_JSONL_BYTES_V0,
            STDERR_CAP,
            super::super::PROCESS_CAPTURE_ARGV_V0,
        )
    })?;

    for held in [&native, &archive, &sigstore, &profile, &stdin] {
        held.verify()?;
    }
    capture_tool.verify()?;
    workspace.verify_empty_mode(0o700)?;
    verify_archive_member(&archive, &native.digest)?;
    let authority = ProcessCaptureReceiptV0::from_observed_process(ObservedProcessCaptureV0 {
        executable_sha256: native.digest.clone(),
        executable_inode: native.inode(),
        stdin: stdin_bytes.clone(),
        termination: execution.termination.into_receipt()?,
        stdout: execution.stdout.clone(),
        stderr: execution.stderr.clone(),
        capture_tool_file_sha256: capture_tool.digest.clone(),
        capture_tool_inode: capture_tool.inode(),
    })?;
    let mut receipt_json =
        serde_json::to_vec(&authority).map_err(|_| error(AdapterErrorCodeV0::ReceiptShape))?;
    receipt_json.push(b'\n');
    let imported = InputAuthorityReceiptV0::from_json_slice(&receipt_json)?;
    if imported.commitment() != authority.commitment() {
        return Err(error(AdapterErrorCodeV0::ReceiptMismatch));
    }
    publish_output_directory(
        &request.output_directory,
        [
            &stdin_bytes,
            &execution.stdout,
            &execution.stderr,
            &receipt_json,
        ],
    )
}

struct HeldRunningImage {
    file: File,
    snapshot: FileSnapshot,
    digest: String,
}

impl HeldRunningImage {
    fn open() -> AdapterResultV0<Self> {
        let (file, snapshot, digest) = open_running_image("/proc/self/exe")?;
        Ok(Self {
            file,
            snapshot,
            digest,
        })
    }

    fn inode(&self) -> InodeIdentityV0 {
        InodeIdentityV0::new(self.snapshot.dev, self.snapshot.ino)
    }

    fn verify(&self) -> AdapterResultV0<()> {
        let held = FileSnapshot::from_metadata(
            &self
                .file
                .metadata()
                .map_err(|_| error(AdapterErrorCodeV0::InputChanged))?,
        );
        if held != self.snapshot {
            return Err(error(AdapterErrorCodeV0::InputChanged));
        }
        let (rebound_file, rebound_snapshot, rebound_digest) = open_running_image("/proc/self/exe")
            .map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
        if rebound_snapshot != self.snapshot
            || standard_sha256_file(&self.file, CAPTURE_TOOL_FILE_CAP, self.snapshot.len)?
                != self.digest
            || rebound_digest != self.digest
        {
            return Err(error(AdapterErrorCodeV0::InputChanged));
        }
        drop(rebound_file);
        Ok(())
    }
}

fn open_running_image(path: &str) -> AdapterResultV0<(File, FileSnapshot, String)> {
    let file = File::from(
        open(path, OFlags::RDONLY | OFlags::CLOEXEC, Mode::empty())
            .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?,
    );
    let metadata = file
        .metadata()
        .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
    let snapshot = FileSnapshot::from_metadata(&metadata);
    let mode = snapshot.mode & 0o7777;
    if !metadata.is_file()
        || snapshot.uid != rustix::process::geteuid().as_raw()
        || mode & 0o022 != 0
        || mode & 0o111 == 0
    {
        return Err(error(AdapterErrorCodeV0::UnsupportedInputProfile));
    }
    require_length_at_most(snapshot.len, CAPTURE_TOOL_FILE_CAP)?;
    let digest = standard_sha256_file(&file, CAPTURE_TOOL_FILE_CAP, snapshot.len)?;
    Ok((file, snapshot, digest))
}

#[derive(Clone, Copy)]
enum FileRole {
    Executable,
    ReleaseArchive,
    SigstoreBundle,
    CaptureProfile,
    PrivateStdin,
}

impl FileRole {
    const fn byte_cap(self) -> u64 {
        match self {
            Self::Executable => EXECUTABLE_FILE_CAP,
            Self::ReleaseArchive => RELEASE_ARCHIVE_FILE_CAP,
            Self::SigstoreBundle => SIGSTORE_BUNDLE_FILE_CAP,
            Self::CaptureProfile => super::super::CAPTURE_PROFILE_ARTIFACT_V0.len() as u64,
            Self::PrivateStdin => STDIN_CAP as u64,
        }
    }
}

#[derive(Clone, Eq, PartialEq)]
struct FileSnapshot {
    dev: u64,
    ino: u64,
    len: u64,
    mode: u32,
    uid: u32,
    mtime: i64,
    mtime_nsec: i64,
    ctime: i64,
    ctime_nsec: i64,
}

impl FileSnapshot {
    fn from_metadata(metadata: &Metadata) -> Self {
        Self {
            dev: metadata.dev(),
            ino: metadata.ino(),
            len: metadata.len(),
            mode: metadata.mode(),
            uid: metadata.uid(),
            mtime: metadata.mtime(),
            mtime_nsec: metadata.mtime_nsec(),
            ctime: metadata.ctime(),
            ctime_nsec: metadata.ctime_nsec(),
        }
    }
}

struct HeldFile {
    path: PathBuf,
    file: File,
    snapshot: FileSnapshot,
    digest: String,
    role: FileRole,
}

impl HeldFile {
    fn open(path: &Path, role: FileRole) -> AdapterResultV0<Self> {
        let file = open_regular_nofollow(path)?;
        let snapshot = FileSnapshot::from_metadata(
            &file
                .metadata()
                .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?,
        );
        validate_held_file_snapshot(&snapshot, role)?;
        let digest = standard_sha256_file(&file, role.byte_cap(), snapshot.len)?;
        Ok(Self {
            path: path.to_path_buf(),
            file,
            snapshot,
            digest,
            role,
        })
    }

    fn inode(&self) -> InodeIdentityV0 {
        InodeIdentityV0::new(self.snapshot.dev, self.snapshot.ino)
    }

    fn starts_with(&self, prefix: &[u8]) -> AdapterResultV0<bool> {
        let mut reader = self
            .file
            .try_clone()
            .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
        reader
            .seek(SeekFrom::Start(0))
            .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
        let mut bytes = vec![0; prefix.len()];
        reader
            .read_exact(&mut bytes)
            .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
        Ok(bytes == prefix)
    }

    fn read_bounded(&self, cap: usize) -> AdapterResultV0<Vec<u8>> {
        let mut reader = self
            .file
            .try_clone()
            .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
        reader
            .seek(SeekFrom::Start(0))
            .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
        let mut bytes = Vec::new();
        reader
            .take((cap as u64).saturating_add(1))
            .read_to_end(&mut bytes)
            .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
        if bytes.len() > cap {
            return Err(error(AdapterErrorCodeV0::InputTooLarge));
        }
        Ok(bytes)
    }

    fn verify(&self) -> AdapterResultV0<()> {
        let held_snapshot = FileSnapshot::from_metadata(
            &self
                .file
                .metadata()
                .map_err(|_| error(AdapterErrorCodeV0::InputChanged))?,
        );
        if held_snapshot != self.snapshot {
            return Err(error(AdapterErrorCodeV0::InputChanged));
        }
        let reopened_file = open_regular_nofollow(&self.path)?;
        let reopened_snapshot = FileSnapshot::from_metadata(
            &reopened_file
                .metadata()
                .map_err(|_| error(AdapterErrorCodeV0::InputChanged))?,
        );
        validate_held_file_snapshot(&reopened_snapshot, self.role)
            .map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
        if reopened_snapshot != self.snapshot {
            return Err(error(AdapterErrorCodeV0::InputChanged));
        }
        let held_digest =
            standard_sha256_file(&self.file, self.role.byte_cap(), self.snapshot.len)?;
        let reopened_digest =
            standard_sha256_file(&reopened_file, self.role.byte_cap(), reopened_snapshot.len)?;
        if held_digest != self.digest || reopened_digest != self.digest {
            return Err(error(AdapterErrorCodeV0::InputChanged));
        }
        Ok(())
    }
}

fn validate_held_file_snapshot(snapshot: &FileSnapshot, role: FileRole) -> AdapterResultV0<()> {
    let mode = snapshot.mode & 0o7777;
    if snapshot.uid != rustix::process::geteuid().as_raw()
        || mode & 0o022 != 0
        || matches!(role, FileRole::Executable) && mode & 0o111 == 0
        || matches!(role, FileRole::PrivateStdin) && mode != 0o600
    {
        return Err(error(AdapterErrorCodeV0::UnsupportedInputProfile));
    }
    require_length_at_most(snapshot.len, role.byte_cap())
}

fn require_length_at_most(length: u64, cap: u64) -> AdapterResultV0<()> {
    if length > cap {
        Err(error(AdapterErrorCodeV0::InputTooLarge))
    } else {
        Ok(())
    }
}

fn require_digest(file: &HeldFile, expected: &str) -> AdapterResultV0<()> {
    if file.digest != expected {
        return Err(error(AdapterErrorCodeV0::ReceiptMismatch));
    }
    Ok(())
}

fn reject_aliases<const N: usize>(files: [&HeldFile; N]) -> AdapterResultV0<()> {
    let mut identities = HashSet::new();
    for file in files {
        if !identities.insert((file.snapshot.dev, file.snapshot.ino)) {
            return Err(error(AdapterErrorCodeV0::InputAlias));
        }
    }
    Ok(())
}

fn standard_sha256_file(file: &File, cap: u64, expected_len: u64) -> AdapterResultV0<String> {
    let mut reader = file
        .try_clone()
        .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
    reader
        .seek(SeekFrom::Start(0))
        .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
    let mut hasher = Sha256::new();
    let mut buffer = [0_u8; READ_CHUNK];
    let mut observed_len = 0_u64;
    let mut reader = reader.take(cap.saturating_add(1));
    loop {
        let count = reader
            .read(&mut buffer)
            .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
        if count == 0 {
            break;
        }
        observed_len = observed_len
            .checked_add(count as u64)
            .ok_or_else(|| error(AdapterErrorCodeV0::InputTooLarge))?;
        if observed_len > cap {
            return Err(error(AdapterErrorCodeV0::InputTooLarge));
        }
        hasher.update(&buffer[..count]);
    }
    if observed_len != expected_len {
        return Err(error(AdapterErrorCodeV0::InputChanged));
    }
    Ok(format!("sha256:{:x}", hasher.finalize()))
}

fn open_regular_nofollow(path: &Path) -> AdapterResultV0<File> {
    let descriptor = walk_open(path, OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::CLOEXEC)?;
    let file = File::from(descriptor);
    let metadata = file
        .metadata()
        .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
    if !metadata.is_file() || metadata.file_type().is_symlink() {
        return Err(error(AdapterErrorCodeV0::InputType));
    }
    Ok(file)
}

fn walk_open(path: &Path, final_flags: OFlags) -> AdapterResultV0<std::os::fd::OwnedFd> {
    if !path.is_absolute() {
        return Err(error(AdapterErrorCodeV0::UnsafeInputPath));
    }
    let components = path_components(path)?;
    let (final_name, parents) = components
        .split_last()
        .ok_or_else(|| error(AdapterErrorCodeV0::UnsafeInputPath))?;
    let mut parent = open(
        "/",
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
    for component in parents {
        parent = openat(
            &parent,
            component.as_os_str(),
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
            Mode::empty(),
        )
        .map_err(|errno| {
            if errno == rustix::io::Errno::LOOP {
                error(AdapterErrorCodeV0::InputSymlink)
            } else {
                error(AdapterErrorCodeV0::InputOpen)
            }
        })?;
    }
    openat(&parent, final_name.as_os_str(), final_flags, Mode::empty()).map_err(|errno| {
        if errno == rustix::io::Errno::LOOP {
            error(AdapterErrorCodeV0::InputSymlink)
        } else {
            error(AdapterErrorCodeV0::InputOpen)
        }
    })
}

fn verify_archive_member(archive: &HeldFile, expected_digest: &str) -> AdapterResultV0<()> {
    let mut file = archive
        .file
        .try_clone()
        .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
    file.seek(SeekFrom::Start(0))
        .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
    let mut tar = tar::Archive::new(GzDecoder::new(file));
    let mut matches = 0_u8;
    for entry in tar
        .entries()
        .map_err(|_| error(AdapterErrorCodeV0::ReceiptMismatch))?
    {
        let mut entry = entry.map_err(|_| error(AdapterErrorCodeV0::ReceiptMismatch))?;
        if entry.path_bytes().as_ref() != super::super::PROCESS_CAPTURE_ARCHIVE_MEMBER_V0 {
            continue;
        }
        if !entry.header().entry_type().is_file() || matches != 0 {
            return Err(error(AdapterErrorCodeV0::ReceiptMismatch));
        }
        matches += 1;
        let mut hasher = Sha256::new();
        let mut buffer = [0_u8; READ_CHUNK];
        loop {
            let count = entry
                .read(&mut buffer)
                .map_err(|_| error(AdapterErrorCodeV0::ReceiptMismatch))?;
            if count == 0 {
                break;
            }
            hasher.update(&buffer[..count]);
        }
        if format!("sha256:{:x}", hasher.finalize()) != expected_digest {
            return Err(error(AdapterErrorCodeV0::ReceiptMismatch));
        }
    }
    if matches != 1 {
        return Err(error(AdapterErrorCodeV0::ReceiptMismatch));
    }
    Ok(())
}

struct HeldWorkspace {
    path: PathBuf,
    file: File,
    dev: u64,
    ino: u64,
}

impl HeldWorkspace {
    fn open(path: &Path) -> AdapterResultV0<Self> {
        let descriptor = walk_open(
            path,
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        )?;
        let file = File::from(descriptor);
        let metadata = file
            .metadata()
            .map_err(|_| error(AdapterErrorCodeV0::InputOpen))?;
        if !metadata.is_dir()
            || metadata.uid() != rustix::process::geteuid().as_raw()
            || metadata.permissions().mode() & 0o7777 != 0o700
        {
            return Err(error(AdapterErrorCodeV0::UnsupportedInputProfile));
        }
        let workspace = Self {
            path: path.to_path_buf(),
            file,
            dev: metadata.dev(),
            ino: metadata.ino(),
        };
        workspace.verify_empty_mode(0o700)?;
        Ok(workspace)
    }

    fn execute_read_only<T>(
        &mut self,
        operation: impl FnOnce() -> AdapterResultV0<T>,
    ) -> AdapterResultV0<T> {
        fchmod(&self.file, Mode::from_raw_mode(0o500))
            .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))?;
        let operation_result = if self.verify_empty_mode(0o500).is_ok() {
            operation()
        } else {
            Err(error(AdapterErrorCodeV0::CaptureCleanup))
        };
        let postcheck = self.verify_empty_mode(0o500);
        let restore = fchmod(&self.file, Mode::from_raw_mode(0o700))
            .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))
            .and_then(|()| self.verify_empty_mode(0o700))
            .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup));
        finish_workspace_transaction(operation_result, postcheck, restore)
    }

    fn verify_empty_mode(&self, mode: u32) -> AdapterResultV0<()> {
        let metadata = self
            .file
            .metadata()
            .map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
        if (metadata.dev(), metadata.ino()) != (self.dev, self.ino)
            || metadata.uid() != rustix::process::geteuid().as_raw()
            || metadata.permissions().mode() & 0o7777 != mode
            || !directory_is_empty(&self.file)?
        {
            return Err(error(AdapterErrorCodeV0::UnsupportedInputProfile));
        }
        let named = walk_open(
            &self.path,
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        )?;
        let named = File::from(named)
            .metadata()
            .map_err(|_| error(AdapterErrorCodeV0::InputChanged))?;
        if (named.dev(), named.ino()) != (self.dev, self.ino) {
            return Err(error(AdapterErrorCodeV0::InputChanged));
        }
        Ok(())
    }
}

fn finish_workspace_transaction<T>(
    operation: AdapterResultV0<T>,
    postcheck: AdapterResultV0<()>,
    restoration: AdapterResultV0<()>,
) -> AdapterResultV0<T> {
    match (postcheck, restoration) {
        (_, Err(_)) => Err(error(AdapterErrorCodeV0::CaptureCleanup)),
        (Err(postcheck), Ok(())) => Err(postcheck),
        (Ok(()), Ok(())) => operation,
    }
}

impl Drop for HeldWorkspace {
    fn drop(&mut self) {
        let _ = fchmod(&self.file, Mode::from_raw_mode(0o700));
    }
}

fn directory_is_empty(file: &File) -> AdapterResultV0<bool> {
    let mut directory =
        Dir::read_from(file).map_err(|_| error(AdapterErrorCodeV0::UnsupportedInputProfile))?;
    while let Some(entry) = directory.read() {
        let entry = entry.map_err(|_| error(AdapterErrorCodeV0::UnsupportedInputProfile))?;
        if !matches!(entry.file_name().to_bytes(), b"." | b"..") {
            return Ok(false);
        }
    }
    Ok(true)
}

fn c_strings(values: &[&[u8]]) -> AdapterResultV0<Vec<CString>> {
    values
        .iter()
        .map(|value| CString::new(*value).map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn)))
        .collect()
}

fn capture_environment() -> AdapterResultV0<Vec<CString>> {
    const ALLOWED: &[&str] = &[
        "HOME",
        "CODEX_HOME",
        "OPENAI_API_KEY",
        "OPENAI_BASE_URL",
        "HTTPS_PROXY",
        "HTTP_PROXY",
        "NO_PROXY",
        "SSL_CERT_FILE",
        "SSL_CERT_DIR",
        "LANG",
        "TERM",
    ];
    let mut environment = Vec::new();
    for name in ALLOWED {
        if let Some(value) = std::env::var_os(name) {
            let mut bytes = name.as_bytes().to_vec();
            bytes.push(b'=');
            bytes.extend_from_slice(value.as_bytes());
            environment
                .push(CString::new(bytes).map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn))?);
        }
    }
    Ok(environment)
}

fn error(code: AdapterErrorCodeV0) -> AdapterErrorV0 {
    AdapterErrorV0::from_code(code)
}

#[cfg(test)]
#[path = "process_capture_platform_tests.rs"]
mod tests;
