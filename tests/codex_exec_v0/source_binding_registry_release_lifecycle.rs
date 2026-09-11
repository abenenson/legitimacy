use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};

#[derive(Eq, PartialEq)]
pub(super) struct Identity {
    pub(super) device: u64,
    pub(super) inode: u64,
    pub(super) length: u64,
    pub(super) digest: [u8; 32],
}

pub(super) fn file_identity(path: &Path) -> Result<Identity, String> {
    let mut file = File::open(path).map_err(|_| "CompilerIdentity: executable open".to_string())?;
    let metadata = file
        .metadata()
        .map_err(|_| "CompilerIdentity: executable stat".to_string())?;
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let count = file
            .read(&mut buffer)
            .map_err(|_| "CompilerIdentity: executable read".to_string())?;
        if count == 0 {
            break;
        }
        hasher.update(&buffer[..count]);
    }
    let identity = Identity {
        device: metadata.dev(),
        inode: metadata.ino(),
        length: metadata.len(),
        digest: hasher.finalize().into(),
    };
    let path_metadata =
        fs::metadata(path).map_err(|_| "CompilerIdentity: executable restat".to_string())?;
    if (
        path_metadata.dev(),
        path_metadata.ino(),
        path_metadata.len(),
    ) != (identity.device, identity.inode, identity.length)
    {
        return Err("CompilerIdentity: executable changed".to_string());
    }
    Ok(identity)
}

pub(super) fn publish_create_once_file(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .map_err(|_| "SuiteLifecycle: result collision".to_string())?;
    file.write_all(bytes)
        .map_err(|_| "SuiteLifecycle: result write".to_string())?;
    file.sync_all()
        .map_err(|_| "SuiteLifecycle: result sync".to_string())
}

pub(super) fn write_owned_marker(
    root: &Path,
    parent: &Path,
    uid: u32,
    run_id: &str,
) -> Result<(), String> {
    let parent_metadata =
        std::fs::metadata(parent).map_err(|_| "SuiteLifecycle: parent stat".to_string())?;
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"legitimacy.selected-authority-owned");
    bytes.extend_from_slice(&1u16.to_be_bytes());
    bytes.extend_from_slice(&uid.to_be_bytes());
    let raw_id = hex::decode(run_id).map_err(|_| "SuiteLifecycle: run ID".to_string())?;
    bytes.extend_from_slice(&raw_id);
    bytes.extend_from_slice(
        &std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|_| "SuiteLifecycle: clock".to_string())?
            .as_secs()
            .to_be_bytes(),
    );
    bytes.extend_from_slice(&parent_metadata.dev().to_be_bytes());
    bytes.extend_from_slice(&parent_metadata.ino().to_be_bytes());
    publish_create_once_file(
        &root.join(".legitimacy-selected-authority-owned-v1"),
        &bytes,
    )
}

pub(super) fn required_path(name: &str) -> Result<PathBuf, String> {
    let value =
        std::env::var_os(name).ok_or_else(|| format!("ReleaseLaneInvocation: missing {name}"))?;
    let path = PathBuf::from(value);
    if !path.is_absolute() {
        return Err(format!("ReleaseLaneInvocation: nonabsolute {name}"));
    }
    Ok(path)
}

pub(super) fn required_ascii(name: &str, length: usize) -> Result<String, String> {
    let value =
        std::env::var(name).map_err(|_| format!("ReleaseLaneInvocation: missing {name}"))?;
    if value.len() != length
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(format!("ReleaseLaneInvocation: invalid {name}"));
    }
    Ok(value)
}

pub(super) fn canonical_regular_file(path: &Path) -> Result<PathBuf, String> {
    let canonical =
        std::fs::canonicalize(path).map_err(|_| "SuiteLifecycle: canonical file".to_string())?;
    let metadata =
        std::fs::metadata(&canonical).map_err(|_| "SuiteLifecycle: file stat".to_string())?;
    if !metadata.is_file() {
        return Err("SuiteLifecycle: nonregular file".to_string());
    }
    Ok(canonical)
}

pub(super) fn canonical_regular_directory(path: &Path) -> Result<PathBuf, String> {
    let canonical = std::fs::canonicalize(path)
        .map_err(|_| "SuiteLifecycle: canonical directory".to_string())?;
    if !std::fs::metadata(&canonical)
        .map_err(|_| "SuiteLifecycle: directory stat".to_string())?
        .is_dir()
    {
        return Err("SuiteLifecycle: nondirectory".to_string());
    }
    Ok(canonical)
}

pub(super) fn create_owned_directory(path: &Path) -> Result<(), String> {
    std::fs::create_dir(path).map_err(|_| "SuiteLifecycle: directory create".to_string())?;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700))
        .map_err(|_| "SuiteLifecycle: directory mode".to_string())?;
    verify_owned_mode(path, 0o700)
}

pub(super) fn verify_owned_mode(path: &Path, mode: u32) -> Result<(), String> {
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|_| "SuiteLifecycle: ownership stat".to_string())?;
    if !metadata.is_dir()
        || metadata.file_type().is_symlink()
        || metadata.uid() != rustix::process::geteuid().as_raw()
        || metadata.mode() & 0o7777 != mode
    {
        return Err("SuiteLifecycle: ownership or mode".to_string());
    }
    Ok(())
}

pub(super) fn require_empty_directory(path: &Path) -> Result<(), String> {
    if std::fs::read_dir(path)
        .map_err(|_| "SuiteLifecycle: target open".to_string())?
        .next()
        .is_some()
    {
        return Err("SuiteLifecycle: target not empty".to_string());
    }
    Ok(())
}

pub(super) fn regular_tree_bytes(root: &Path) -> Result<u64, String> {
    let mut total = 0u64;
    for entry in
        std::fs::read_dir(root).map_err(|_| "SuiteLifecycle: size inventory".to_string())?
    {
        let path = entry
            .map_err(|_| "SuiteLifecycle: size entry".to_string())?
            .path();
        let metadata = std::fs::symlink_metadata(&path)
            .map_err(|_| "SuiteLifecycle: size stat".to_string())?;
        if metadata.file_type().is_symlink() {
            return Err("SuiteLifecycle: size symlink".to_string());
        }
        if metadata.is_dir() {
            total = total
                .checked_add(regular_tree_bytes(&path)?)
                .ok_or_else(|| "SuiteLifecycle: size overflow".to_string())?;
        } else if metadata.is_file() {
            total = total
                .checked_add(metadata.len())
                .ok_or_else(|| "SuiteLifecycle: size overflow".to_string())?;
        }
    }
    Ok(total)
}

pub(super) fn remove_owned_tree(path: &Path) -> Result<(), String> {
    let metadata =
        fs::symlink_metadata(path).map_err(|_| "SuiteLifecycle: cleanup stat".to_string())?;
    if metadata.uid() != rustix::process::geteuid().as_raw() {
        return Err("SuiteLifecycle: cleanup ownership".to_string());
    }
    if metadata.is_dir() && !metadata.file_type().is_symlink() {
        let entries = fs::read_dir(path)
            .map_err(|_| "SuiteLifecycle: cleanup inventory".to_string())?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| "SuiteLifecycle: cleanup entry".to_string())?;
        let mut failure = None;
        for entry in entries {
            if let Err(error) = remove_owned_tree(&entry.path()) {
                failure.get_or_insert(error);
            }
        }
        if fs::remove_dir(path).is_err() {
            failure.get_or_insert_with(|| "SuiteLifecycle: directory cleanup".to_string());
        }
        failure.map_or(Ok(()), Err)
    } else {
        let expected = metadata.is_file() && !metadata.file_type().is_symlink();
        fs::remove_file(path).map_err(|_| "SuiteLifecycle: file cleanup".to_string())?;
        if expected {
            Ok(())
        } else {
            Err("SuiteLifecycle: cleanup object".to_string())
        }
    }
}

pub(super) mod hex {
    pub(in super::super) fn encode(bytes: &[u8]) -> String {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";
        let mut output = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            output.push(char::from(DIGITS[usize::from(byte >> 4)]));
            output.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
        }
        output
    }

    pub(super) fn decode(value: &str) -> Result<Vec<u8>, ()> {
        if !value.len().is_multiple_of(2) {
            return Err(());
        }
        value
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| Ok((nibble(pair[0])? << 4) | nibble(pair[1])?))
            .collect()
    }

    fn nibble(value: u8) -> Result<u8, ()> {
        match value {
            b'0'..=b'9' => Ok(value - b'0'),
            b'a'..=b'f' => Ok(value - b'a' + 10),
            _ => Err(()),
        }
    }
}
