use super::{
    MAX_TRACE_COMPACT_JSON_BYTES_V0, TrajectoryTraceV0, ValidatedTrajectoryTraceV0, invalid,
};
use crate::LegitimacyError;
use serde::Serialize;
use std::io::{self, Write};

impl ValidatedTrajectoryTraceV0<'_> {
    /// Official deterministic compact v0 JSON, hard-capped at the interchange limit.
    pub fn to_compact_json(&self) -> Result<Vec<u8>, LegitimacyError> {
        let mut output = Vec::new();
        serialize_bounded_compact_json(self.trace, &mut output)?;
        Ok(output)
    }
}

pub(super) fn validate_compact_json_size(trace: &TrajectoryTraceV0) -> Result<(), LegitimacyError> {
    serialize_bounded_compact_json(trace, io::sink())
}

fn serialize_bounded_compact_json(
    trace: &TrajectoryTraceV0,
    output: impl Write,
) -> Result<(), LegitimacyError> {
    let mut output = BoundedWriter::new(output, MAX_TRACE_COMPACT_JSON_BYTES_V0);
    let result = {
        let mut serializer = serde_json::Serializer::new(&mut output);
        trace.serialize(&mut serializer)
    };
    if output.limit_exceeded {
        return invalid(format!(
            "trajectory trace official compact JSON exceeds v0 byte limit of {MAX_TRACE_COMPACT_JSON_BYTES_V0}"
        ));
    }
    result.map_err(|source| LegitimacyError::Serialize {
        context: "official compact trajectory JSON".to_string(),
        source,
    })
}

struct BoundedWriter<W> {
    inner: W,
    written: usize,
    limit: usize,
    limit_exceeded: bool,
}

impl<W> BoundedWriter<W> {
    fn new(inner: W, limit: usize) -> Self {
        Self {
            inner,
            written: 0,
            limit,
            limit_exceeded: false,
        }
    }
}

impl<W: Write> Write for BoundedWriter<W> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let Some(next) = self.written.checked_add(bytes.len()) else {
            self.limit_exceeded = true;
            return Err(io::Error::other("bounded writer byte count overflow"));
        };
        if next > self.limit {
            self.limit_exceeded = true;
            return Err(io::Error::other("bounded writer limit exceeded"));
        }
        let written = self.inner.write(bytes)?;
        self.written = self
            .written
            .checked_add(written)
            .ok_or_else(|| io::Error::other("bounded writer byte count overflow"))?;
        Ok(written)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounded_writer_accepts_exact_limit_and_rejects_one_more() {
        // A full valid trace engineered to serialize to exactly 8 MiB would
        // couple this boundary proof to unrelated field spelling. Exercising
        // the production writer directly keeps the exact/one-over kill stable,
        // while integration tests separately prove full oversized rejection.
        let mut writer = BoundedWriter::new(io::sink(), MAX_TRACE_COMPACT_JSON_BYTES_V0);
        let chunk = [0_u8; 8 * 1024];
        for _ in 0..MAX_TRACE_COMPACT_JSON_BYTES_V0 / chunk.len() {
            writer.write_all(&chunk).unwrap();
        }
        assert_eq!(writer.written, MAX_TRACE_COMPACT_JSON_BYTES_V0);
        assert!(!writer.limit_exceeded);

        writer
            .write_all(&[0])
            .expect_err("one byte over the limit must fail");
        assert!(writer.limit_exceeded);
        assert_eq!(writer.written, MAX_TRACE_COMPACT_JSON_BYTES_V0);
    }
}
