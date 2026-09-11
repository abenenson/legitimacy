use rustix::fd::OwnedFd;
use rustix::fs::{Mode, OFlags, RenameFlags, fsync, open, openat, renameat_with};
use sha2::{Digest, Sha256};
use std::io::{Read, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use uuid::Uuid;

const READY_MAGIC: &[u8] = b"legitimacy.selected-authority-invocation\0";
const OWNED_MARKER: &str = ".legitimacy-selected-authority-owned-v1";
const NAMESPACE: &str = "legitimacy-selected-authority-v1";
const COMPILER_PROXY_SOURCE: &[u8] = include_bytes!("support/selected_authority_compiler_proxy.rs");
const GIT_ANSWER_SOURCE: &[u8] = include_bytes!("support/selected_authority_git_answer.rs");
const RLIB_PROBE_SOURCE: &[u8] = include_bytes!("support/selected_authority_rlib_probe.rs");

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RecordFailure {
    RecordCollision,
    RecordDurability,
    SlotAccounting,
    Scavenge,
}

pub(crate) struct EvidenceDirectory {
    path: PathBuf,
    descriptor: OwnedFd,
}

impl EvidenceDirectory {
    pub(crate) fn create(path: &Path) -> Result<Self, RecordFailure> {
        std::fs::create_dir(path).map_err(|_| RecordFailure::RecordDurability)?;
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700))
            .map_err(|_| RecordFailure::RecordDurability)?;
        let descriptor = open(
            path,
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
            Mode::empty(),
        )
        .map_err(|_| RecordFailure::RecordDurability)?;
        let metadata = std::fs::metadata(path).map_err(|_| RecordFailure::RecordDurability)?;
        if !metadata.is_dir()
            || metadata.uid() != rustix::process::geteuid().as_raw()
            || metadata.mode() & 0o7777 != 0o700
        {
            return Err(RecordFailure::RecordDurability);
        }
        Ok(Self {
            path: path.to_path_buf(),
            descriptor,
        })
    }

    pub(crate) fn claim_slot(&self, bytes: &[u8]) -> Result<u16, RecordFailure> {
        for slot in 0..512u16 {
            let name = format!(".slot.{slot:03}.v1");
            match create_record(&self.descriptor, &name, bytes) {
                Ok(()) => return Ok(slot),
                Err(rustix::io::Errno::EXIST) => {}
                Err(_) => return Err(RecordFailure::SlotAccounting),
            }
        }
        Err(RecordFailure::SlotAccounting)
    }

    pub(crate) fn publish(
        &self,
        pid: u32,
        nonce: &str,
        payload: &[u8],
    ) -> Result<PathBuf, RecordFailure> {
        let temporary = format!(".invocation.{pid}.{nonce}.tmp");
        let ready = format!("invocation.{pid}.{nonce}.ready");
        let framed = frame_record(payload);
        create_record(&self.descriptor, &temporary, &framed)
            .map_err(|_| RecordFailure::RecordDurability)?;
        renameat_with(
            &self.descriptor,
            temporary.as_str(),
            &self.descriptor,
            ready.as_str(),
            RenameFlags::NOREPLACE,
        )
        .map_err(|error| {
            if error == rustix::io::Errno::EXIST {
                RecordFailure::RecordCollision
            } else {
                RecordFailure::RecordDurability
            }
        })?;
        let ready_fd = openat(
            &self.descriptor,
            ready.as_str(),
            OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
            Mode::empty(),
        )
        .map_err(|_| RecordFailure::RecordDurability)?;
        let mut ready_file = std::fs::File::from(ready_fd);
        let mut observed = Vec::new();
        ready_file
            .read_to_end(&mut observed)
            .map_err(|_| RecordFailure::RecordDurability)?;
        if observed != framed {
            return Err(RecordFailure::RecordDurability);
        }
        fsync(&self.descriptor).map_err(|_| RecordFailure::RecordDurability)?;
        Ok(self.path.join(ready))
    }
}

fn create_record(directory: &OwnedFd, name: &str, bytes: &[u8]) -> rustix::io::Result<()> {
    let descriptor = openat(
        directory,
        name,
        OFlags::CREATE | OFlags::EXCL | OFlags::WRONLY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::from_raw_mode(0o600),
    )?;
    let mut file = std::fs::File::from(descriptor);
    file.write_all(bytes).map_err(|_| rustix::io::Errno::IO)?;
    file.flush().map_err(|_| rustix::io::Errno::IO)?;
    file.sync_all().map_err(|_| rustix::io::Errno::IO)?;
    Ok(())
}

fn frame_record(payload: &[u8]) -> Vec<u8> {
    let mut framed = Vec::new();
    framed.extend_from_slice(READY_MAGIC);
    framed.extend_from_slice(&1u16.to_be_bytes());
    framed.extend_from_slice(&u64::try_from(payload.len()).unwrap().to_be_bytes());
    framed.extend_from_slice(payload);
    framed.extend_from_slice(&Sha256::digest(&framed));
    framed
}

pub(crate) fn assert_ready_record_publication_is_atomic_durable_and_no_replace() {
    assert!(syn::parse_file(std::str::from_utf8(COMPILER_PROXY_SOURCE).unwrap()).is_ok());
    assert!(syn::parse_file(std::str::from_utf8(GIT_ANSWER_SOURCE).unwrap()).is_ok());
    assert!(syn::parse_file(std::str::from_utf8(RLIB_PROBE_SOURCE).unwrap()).is_ok());
    assert_ne!(
        Sha256::digest(COMPILER_PROXY_SOURCE),
        Sha256::digest(GIT_ANSWER_SOURCE)
    );
    assert_ne!(
        Sha256::digest(COMPILER_PROXY_SOURCE),
        Sha256::digest(RLIB_PROBE_SOURCE)
    );
    let parent = unique_test_parent("records");
    std::fs::create_dir(&parent).unwrap();
    let evidence = EvidenceDirectory::create(&parent.join("evidence")).unwrap();
    assert_eq!(evidence.claim_slot(b"slot-v1").unwrap(), 0);
    let ready = evidence.publish(17, "001122", b"payload").unwrap();
    assert!(ready.is_file());
    let collision = evidence.publish(17, "001122", b"different");
    assert_eq!(collision, Err(RecordFailure::RecordCollision));
    assert!(parent.join("evidence/.invocation.17.001122.tmp").is_file());
    drop(evidence);
    std::fs::remove_dir_all(parent).unwrap();
}

pub(crate) fn assert_owned_suite_scavenging_rejects_foreign_live_and_symlink_roots() {
    let parent = unique_test_parent("scavenge");
    std::fs::create_dir(&parent).unwrap();
    let uid = rustix::process::geteuid().as_raw();
    let live_name = format!("{NAMESPACE}.{uid}.{}", "11".repeat(16));
    let live = parent.join(&live_name);
    std::fs::create_dir(&live).unwrap();
    std::fs::set_permissions(&live, std::fs::Permissions::from_mode(0o700)).unwrap();
    write_marker(&live, uid, [0x11; 16], now_seconds());

    let foreign_name = format!("{NAMESPACE}.{uid}.{}", "22".repeat(16));
    let foreign = parent.join(&foreign_name);
    std::fs::create_dir(&foreign).unwrap();
    std::fs::set_permissions(&foreign, std::fs::Permissions::from_mode(0o755)).unwrap();

    let target = parent.join("ordinary");
    std::fs::create_dir(&target).unwrap();
    let symlink_name = format!("{NAMESPACE}.{uid}.{}", "33".repeat(16));
    std::os::unix::fs::symlink(&target, parent.join(&symlink_name)).unwrap();

    let rejected = classify_scavenge_candidates(&parent).unwrap();
    assert_eq!(
        rejected,
        vec![
            (live_name, RecordFailure::Scavenge),
            (foreign_name, RecordFailure::Scavenge),
            (symlink_name.clone(), RecordFailure::Scavenge),
        ]
    );
    assert!(live.is_dir());
    assert!(foreign.is_dir());
    assert!(parent.join(&symlink_name).is_symlink());
    std::fs::remove_file(parent.join(symlink_name)).unwrap();
    std::fs::remove_dir_all(parent).unwrap();
}

fn classify_scavenge_candidates(
    parent: &Path,
) -> Result<Vec<(String, RecordFailure)>, RecordFailure> {
    let mut names = std::fs::read_dir(parent)
        .map_err(|_| RecordFailure::Scavenge)?
        .map(|entry| {
            entry
                .map_err(|_| RecordFailure::Scavenge)
                .and_then(|entry| {
                    entry
                        .file_name()
                        .into_string()
                        .map_err(|_| RecordFailure::Scavenge)
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    names.sort_by(|left, right| left.as_bytes().cmp(right.as_bytes()));
    let mut rejected = Vec::new();
    for name in names {
        if !name.starts_with(&format!("{NAMESPACE}.")) {
            continue;
        }
        let path = parent.join(&name);
        let metadata = std::fs::symlink_metadata(&path).map_err(|_| RecordFailure::Scavenge)?;
        let safe = metadata.is_dir()
            && !metadata.file_type().is_symlink()
            && metadata.uid() == rustix::process::geteuid().as_raw()
            && metadata.mode() & 0o7777 == 0o700
            && marker_is_old_and_exact(&path, &name).unwrap_or(false);
        if !safe {
            rejected.push((name, RecordFailure::Scavenge));
        }
    }
    Ok(rejected)
}

fn write_marker(root: &Path, uid: u32, run_id: [u8; 16], created: u64) {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"legitimacy.selected-authority-owned");
    bytes.extend_from_slice(&1u16.to_be_bytes());
    bytes.extend_from_slice(&uid.to_be_bytes());
    bytes.extend_from_slice(&run_id);
    bytes.extend_from_slice(&created.to_be_bytes());
    let metadata = std::fs::metadata(root.parent().unwrap()).unwrap();
    bytes.extend_from_slice(&metadata.dev().to_be_bytes());
    bytes.extend_from_slice(&metadata.ino().to_be_bytes());
    let path = root.join(OWNED_MARKER);
    let mut options = std::fs::OpenOptions::new();
    options.write(true).create_new(true).mode(0o600);
    let mut file = options.open(path).unwrap();
    file.write_all(&bytes).unwrap();
    file.sync_all().unwrap();
}

fn marker_is_old_and_exact(root: &Path, name: &str) -> Result<bool, RecordFailure> {
    let metadata =
        std::fs::symlink_metadata(root.join(OWNED_MARKER)).map_err(|_| RecordFailure::Scavenge)?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || metadata.nlink() != 1
        || metadata.mode() & 0o7777 != 0o600
    {
        return Ok(false);
    }
    let bytes = std::fs::read(root.join(OWNED_MARKER)).map_err(|_| RecordFailure::Scavenge)?;
    let prefix = b"legitimacy.selected-authority-owned";
    if bytes.len() != prefix.len() + 2 + 4 + 16 + 8 + 8 + 8 || !bytes.starts_with(prefix) {
        return Ok(false);
    }
    let created_offset = prefix.len() + 2 + 4 + 16;
    let created = u64::from_be_bytes(
        bytes[created_offset..created_offset + 8]
            .try_into()
            .unwrap(),
    );
    let grammar = name.split('.').collect::<Vec<_>>();
    Ok(grammar.len() == 3
        && grammar[0] == NAMESPACE
        && grammar[2].len() == 32
        && grammar[2]
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        && now_seconds().saturating_sub(created) >= 24 * 60 * 60)
}

fn unique_test_parent(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "legitimacy-selected-authority-test-{label}-{}",
        Uuid::new_v4().simple()
    ))
}

fn now_seconds() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
}
