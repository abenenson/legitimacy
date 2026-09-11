use super::error::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0};
use super::{
    MAX_CODEX_DECODED_STRING_BYTES_V0, MAX_CODEX_JSON_DEPTH_V0, MAX_CODEX_JSON_KEYS_V0,
    MAX_CODEX_JSON_NODES_V0, MAX_CODEX_JSONL_BYTES_V0, MAX_CODEX_RECORD_BYTES_V0,
    MAX_CODEX_RECORDS_V0,
};
use crate::trajectory::duplicate_json::{self, JsonRootKind, JsonScanLimits};
use crate::trajectory::framed_sha256;
use std::ops::Range;

const FULL_JSONL_DOMAIN_V0: &str = "legitimacy.codex-exec-v0.full-jsonl.v0";
const FRAME_SCAN_CHUNK_BYTES_V0: usize = 8 * 1024;

pub(crate) struct FramedCaptureV0 {
    pub bytes: Vec<u8>,
    pub records: Vec<Range<usize>>,
}

impl FramedCaptureV0 {
    pub fn parse(input: &[u8]) -> AdapterResultV0<Self> {
        Self::parse_owned(input.to_vec())
    }

    pub fn parse_owned(bytes: Vec<u8>) -> AdapterResultV0<Self> {
        if bytes.len() > MAX_CODEX_JSONL_BYTES_V0 {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge));
        }
        if bytes.is_empty() || bytes.last() != Some(&b'\n') || bytes.contains(&b'\r') {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::JsonFraming));
        }
        std::str::from_utf8(&bytes)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::JsonSyntax))?;

        let mut records = Vec::new();
        let mut start = 0usize;
        for (chunk_index, chunk) in bytes.chunks(FRAME_SCAN_CHUNK_BYTES_V0).enumerate() {
            let chunk_start = chunk_index
                .checked_mul(FRAME_SCAN_CHUNK_BYTES_V0)
                .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::JsonFraming))?;
            for relative_end in chunk
                .iter()
                .enumerate()
                .filter_map(|(index, byte)| (*byte == b'\n').then_some(index))
            {
                let end = chunk_start
                    .checked_add(relative_end)
                    .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::JsonFraming))?;
                let length = end
                    .checked_sub(start)
                    .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::JsonFraming))?;
                if length == 0 || length > MAX_CODEX_RECORD_BYTES_V0 {
                    return Err(AdapterErrorV0::new(if length == 0 {
                        AdapterErrorCodeV0::JsonFraming
                    } else {
                        AdapterErrorCodeV0::InputTooLarge
                    }));
                }
                if records.len() == MAX_CODEX_RECORDS_V0 {
                    return Err(AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge));
                }
                let record = &bytes[start..end];
                let limits = JsonScanLimits {
                    max_depth: MAX_CODEX_JSON_DEPTH_V0,
                    max_nodes: MAX_CODEX_JSON_NODES_V0,
                    max_total_keys: MAX_CODEX_JSON_KEYS_V0,
                    max_decoded_string_bytes: MAX_CODEX_DECODED_STRING_BYTES_V0,
                };
                let record_index = records.len();
                match duplicate_json::scan_json_with_limits(record, "codex exec record", limits) {
                    Ok(JsonRootKind::Object) => {}
                    Ok(JsonRootKind::NonObject) => {
                        return Err(AdapterErrorV0::record(
                            AdapterErrorCodeV0::JsonShape,
                            record_index,
                            "$",
                        ));
                    }
                    Err(error) => {
                        return Err(AdapterErrorV0::record(
                            if error.is_budget() {
                                AdapterErrorCodeV0::JsonBudget
                            } else {
                                AdapterErrorCodeV0::JsonSyntax
                            },
                            record_index,
                            "$",
                        ));
                    }
                }
                records.push(start..end);
                start = end
                    .checked_add(1)
                    .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::JsonFraming))?;
            }
        }
        if start != bytes.len() || records.is_empty() {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::JsonFraming));
        }
        Ok(Self { bytes, records })
    }

    pub fn record_slices(&self) -> Vec<&[u8]> {
        self.records
            .iter()
            .map(|range| &self.bytes[range.clone()])
            .collect()
    }

    pub fn full_digest(&self) -> String {
        full_jsonl_digest_v0(&self.bytes)
    }
}

pub(crate) fn full_jsonl_digest_v0(bytes: &[u8]) -> String {
    framed_sha256(FULL_JSONL_DOMAIN_V0, &[bytes])
}
