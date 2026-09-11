use super::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0, CaptureManifestEntryV0};
use crate::trajectory::framed_sha256;

const WORKSPACE_TREE_DOMAIN_V0: &str = "legitimacy.codex-exec-v0.workspace-tree.v0";

impl CaptureManifestEntryV0 {
    pub fn new(
        ordinal: u64,
        role: &str,
        format: &str,
        relative_path: &[u8],
        byte_length: u64,
        sha256: String,
        inode: super::InodeIdentityV0,
    ) -> AdapterResultV0<Self> {
        let entry = Self {
            ordinal,
            role: role.to_string(),
            format: format.to_string(),
            relative_path_lower_hex: super::lower_hex(relative_path),
            byte_length,
            sha256,
            inode,
        };
        entry.validate()?;
        Ok(entry)
    }

    pub(super) fn validate(&self) -> AdapterResultV0<()> {
        if self.role != "fixture-input" || self.format != "regular-file-bytes" {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape));
        }
        super::validate_sha256(&self.sha256)?;
        let path = super::decode_lower_hex(&self.relative_path_lower_hex)?;
        if path.is_empty()
            || path.len() > 4_096
            || path[0] == b'/'
            || path
                .split(|byte| *byte == b'/')
                .any(|part| part.is_empty() || part == b"." || part == b".." || part.contains(&0))
        {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape));
        }
        Ok(())
    }
}

pub fn workspace_tree_digest(entries: &[CaptureManifestEntryV0]) -> AdapterResultV0<String> {
    validate_order(entries)?;
    let ordinals = entries
        .iter()
        .map(|entry| entry.ordinal.to_be_bytes())
        .collect::<Vec<_>>();
    let lengths = entries
        .iter()
        .map(|entry| entry.byte_length.to_be_bytes())
        .collect::<Vec<_>>();
    let devices = entries
        .iter()
        .map(|entry| entry.inode.dev.to_be_bytes())
        .collect::<Vec<_>>();
    let inodes = entries
        .iter()
        .map(|entry| entry.inode.ino.to_be_bytes())
        .collect::<Vec<_>>();
    let mut components = Vec::<&[u8]>::with_capacity(entries.len() * 8);
    for (index, entry) in entries.iter().enumerate() {
        components.extend([
            ordinals[index].as_slice(),
            entry.role.as_bytes(),
            entry.format.as_bytes(),
            entry.relative_path_lower_hex.as_bytes(),
            lengths[index].as_slice(),
            entry.sha256.as_bytes(),
            devices[index].as_slice(),
            inodes[index].as_slice(),
        ]);
    }
    Ok(framed_sha256(WORKSPACE_TREE_DOMAIN_V0, &components))
}

pub(super) fn validate_order(entries: &[CaptureManifestEntryV0]) -> AdapterResultV0<()> {
    for (index, entry) in entries.iter().enumerate() {
        entry.validate()?;
        if entry.ordinal != index as u64
            || index > 0
                && entries[index - 1].relative_path_lower_hex >= entry.relative_path_lower_hex
        {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape));
        }
        if entries[..index]
            .iter()
            .any(|previous| previous.inode == entry.inode)
        {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape));
        }
    }
    Ok(())
}
