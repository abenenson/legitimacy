use super::{
    AgentActionEventV0, ArtifactBindingV0, EvidenceV0, EvidencedV0, NormalizedValueV0,
    SourceLocatorV0, TRACE_DOMAIN_V0, TrajectoryTraceV0, ValidatedTrajectoryTraceV0, framed_sha256,
};

const TRACE_CANONICAL_MAGIC_V0: &[u8] = b"legitimacy.trajectory.trace.canonical.v0\0";

impl ValidatedTrajectoryTraceV0<'_> {
    /// Deterministic contract bytes, available only for a successfully validated trace.
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut output = canonical_header_bytes(self.trace);
        for event in self.canonical_event_components() {
            output.extend_from_slice(&event);
        }
        output
    }

    /// Official v0 trajectory digest over validated canonical bytes.
    pub fn trajectory_digest(&self) -> String {
        framed_sha256(TRACE_DOMAIN_V0, &[&self.canonical_bytes()])
    }

    pub(super) fn canonical_event_components(&self) -> impl Iterator<Item = Vec<u8>> + '_ {
        self.trace.events.iter().map(canonical_event_bytes)
    }
}

pub(super) fn canonical_header_bytes(trace: &TrajectoryTraceV0) -> Vec<u8> {
    let mut output = TRACE_CANONICAL_MAGIC_V0.to_vec();
    encode_binding(&mut output, &trace.schema);
    encode_evidenced(&mut output, &trace.run_id, |output, value| {
        put_string(output, value);
    });
    encode_binding(&mut output, &trace.adapter);
    encode_binding(&mut output, &trace.policy);
    put_u64(&mut output, trace.raw_capture.record_count);
    put_string(&mut output, &trace.raw_capture.digest);
    put_len(&mut output, trace.events.len());
    output
}

pub(super) fn canonical_event_bytes(event: &AgentActionEventV0) -> Vec<u8> {
    let mut output = Vec::new();
    encode_evidenced(&mut output, &event.event_id, |output, value| {
        put_string(output, value);
    });
    encode_evidenced(&mut output, &event.sequence_index, |output, value| {
        put_u64(output, *value);
    });
    encode_evidenced(&mut output, &event.kind, |output, value| {
        put_string(output, value.label());
    });
    match &event.source_item_id {
        Some(value) => {
            output.push(1);
            encode_evidenced(&mut output, value, |output, value| {
                put_string(output, value);
            });
        }
        None => output.push(0),
    }
    put_u64(&mut output, event.raw_record.record_index);
    put_string(&mut output, &event.raw_record.digest);
    put_len(&mut output, event.payload.len());
    for (key, value) in &event.payload {
        put_string(&mut output, key);
        encode_evidenced(&mut output, value, encode_normalized_value);
    }
    output
}

fn encode_binding(output: &mut Vec<u8>, binding: &ArtifactBindingV0) {
    put_string(output, &binding.identity);
    put_string(output, &binding.version);
    put_string(output, &binding.hash);
}

fn encode_evidenced<T>(
    output: &mut Vec<u8>,
    field: &EvidencedV0<T>,
    encode_value: impl Fn(&mut Vec<u8>, &T),
) {
    match &field.value {
        Some(value) => {
            output.push(1);
            encode_value(output, value);
        }
        None => output.push(0),
    }
    encode_evidence(output, &field.evidence);
}

fn encode_evidence(output: &mut Vec<u8>, evidence: &EvidenceV0) {
    match evidence {
        EvidenceV0::CitesRawRange { locator } => {
            output.push(0);
            encode_locator(output, locator);
        }
        EvidenceV0::DeclaredDerivationBinding {
            rule,
            source_inputs,
        } => {
            output.push(1);
            encode_binding(output, rule);
            put_len(output, source_inputs.len());
            for locator in source_inputs {
                encode_locator(output, locator);
            }
        }
        EvidenceV0::Unavailable { reason } => {
            output.push(2);
            put_string(output, reason);
        }
    }
}

fn encode_locator(output: &mut Vec<u8>, locator: &SourceLocatorV0) {
    put_u64(output, locator.record_index);
    put_u64(output, locator.byte_offset);
    put_u64(output, locator.byte_length);
    put_string(output, &locator.digest);
}

fn encode_normalized_value(output: &mut Vec<u8>, value: &NormalizedValueV0) {
    match value {
        NormalizedValueV0::Null => output.push(0),
        NormalizedValueV0::Boolean(value) => {
            output.push(1);
            output.push(u8::from(*value));
        }
        NormalizedValueV0::Integer(value) => {
            output.push(2);
            put_string(output, value);
        }
        NormalizedValueV0::String(value) => {
            output.push(3);
            put_string(output, value);
        }
        NormalizedValueV0::Array(values) => {
            output.push(4);
            put_len(output, values.len());
            for value in values {
                encode_normalized_value(output, value);
            }
        }
        NormalizedValueV0::Object(values) => {
            output.push(5);
            put_len(output, values.len());
            for (key, value) in values {
                put_string(output, key);
                encode_normalized_value(output, value);
            }
        }
    }
}

fn put_string(output: &mut Vec<u8>, value: &str) {
    put_len(output, value.len());
    output.extend_from_slice(value.as_bytes());
}

fn put_len(output: &mut Vec<u8>, value: usize) {
    put_u64(
        output,
        u64::try_from(value).expect("usize always fits u64 on supported targets"),
    );
}

fn put_u64(output: &mut Vec<u8>, value: u64) {
    output.extend_from_slice(&value.to_be_bytes());
}
