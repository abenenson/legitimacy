use super::*;
use std::io::{self, Write};

#[test]
fn valid_trace_round_trips_through_official_compact_export() {
    let raw = vec![RECORD_ZERO];
    let (trace, trusted) = fixture(&raw);
    let digest = trajectory_digest_v0(&trace.validate(&raw, &trusted).unwrap());
    let encoded = serde_json::to_vec(&trace).unwrap();
    let parsed = TrajectoryTraceV0::from_json_slice(&encoded).unwrap();
    assert_eq!(parsed, trace);

    let validated = parsed.validate(&raw, &trusted).unwrap();
    let exported = validated.to_compact_json().unwrap();
    assert_eq!(exported, encoded);
    assert_eq!(validated.to_compact_json().unwrap(), exported);
    assert!(exported.len() <= legitimacy::trajectory::MAX_TRACE_COMPACT_JSON_BYTES_V0);

    let reparsed = TrajectoryTraceV0::from_json_slice(&exported).unwrap();
    let revalidated = reparsed.validate(&raw, &trusted).unwrap();
    assert_eq!(trajectory_digest_v0(&revalidated), digest);
}

#[test]
fn bounded_loader_rejects_duplicate_dynamic_map_keys_at_every_depth() {
    let raw = vec![RECORD_ZERO];
    let (mut trace, _) = fixture(&raw);
    let field = trace.events[0].payload["command"].clone();
    let encoded_field = serde_json::to_string(&field).unwrap();
    let encoded = serde_json::to_string(&trace).unwrap();
    let payload = format!("\"payload\":{{\"command\":{encoded_field}}}");
    let duplicate_payload =
        format!("\"payload\":{{\"command\":{encoded_field},\"command\":{encoded_field}}}");
    let duplicate = encoded.replacen(&payload, &duplicate_payload, 1);
    let error = TrajectoryTraceV0::from_json_slice(duplicate.as_bytes())
        .expect_err("bounded loader payload decoding must reject duplicate keys");
    assert!(error.to_string().contains("duplicate JSON object key"));

    let nested = NormalizedValueV0::Object(BTreeMap::from([(
        "nested".to_string(),
        NormalizedValueV0::String("one".to_string()),
    )]));
    trace.events[0].payload.get_mut("command").unwrap().value = Some(nested.clone());
    let encoded = serde_json::to_string(&trace).unwrap();
    let nested_wire = serde_json::to_string(&nested).unwrap();
    let duplicate_nested_wire = nested_wire.replacen(
        r#""nested":{"type":"string","value":"one"}"#,
        r#""nested":{"type":"string","value":"one"},"nested":{"type":"string","value":"two"}"#,
        1,
    );
    let duplicate = encoded.replacen(&nested_wire, &duplicate_nested_wire, 1);
    let error = TrajectoryTraceV0::from_json_slice(duplicate.as_bytes())
        .expect_err("bounded loader nested-object decoding must reject duplicate keys");
    assert!(error.to_string().contains("duplicate JSON object key"));
}

#[test]
fn reported_ten_thousand_event_trace_hits_both_interchange_caps_first() {
    let raw = vec![b"{}".as_slice(); legitimacy::trajectory::MAX_EVENTS_V0];
    let (trace, trusted) = fixture(&raw);
    let compact_len = compact_json_len(&trace);
    assert!(
        compact_len > legitimacy::trajectory::MAX_TRACE_COMPACT_JSON_BYTES_V0,
        "reported near-cardinality fixture must exceed the compact export cap"
    );

    let invalid_raw = vec![b"not-json".as_slice(); legitimacy::trajectory::MAX_RAW_RECORDS_V0];
    assert_validation_error(
        &trace,
        &invalid_raw,
        &trusted,
        "official compact JSON exceeds v0 byte limit",
    );

    let oversized_wire = serde_json::to_vec(&trace).unwrap();
    assert_eq!(oversized_wire.len(), compact_len);
    let error = TrajectoryTraceV0::from_json_slice(&oversized_wire)
        .expect_err("the bounded loader must reject the same oversized compact bytes");
    assert!(
        error
            .to_string()
            .contains("JSON input exceeds v0 byte limit")
    );
}

#[test]
fn escaping_amplification_hits_compact_cap_without_expanded_allocation() {
    let raw = vec![RECORD_ZERO];
    let (mut trace, trusted) = fixture(&raw);
    let field = trace.events[0].payload.remove("command").unwrap();
    let escaped_chunk = "\0".repeat(legitimacy::trajectory::MAX_NORMALIZED_STRING_SCALARS_V0);
    assert_eq!(
        escaped_chunk.len(),
        legitimacy::trajectory::MAX_NORMALIZED_STRING_SCALARS_V0
    );
    let escaped_value = NormalizedValueV0::String(escaped_chunk);
    trace.events[0].payload.insert(
        "escaped".to_string(),
        EvidencedV0 {
            value: Some(NormalizedValueV0::Array(vec![escaped_value; 128])),
            evidence: field.evidence,
        },
    );

    assert!(compact_json_len(&trace) > legitimacy::trajectory::MAX_TRACE_COMPACT_JSON_BYTES_V0);
    assert_validation_error(
        &trace,
        &[b"not-json".as_slice()],
        &trusted,
        "official compact JSON exceeds v0 byte limit",
    );
}

#[test]
fn input_limit_counts_insignificant_whitespace_exactly() {
    let raw = vec![RECORD_ZERO];
    let (trace, _) = fixture(&raw);
    let mut wire = serde_json::to_vec(&trace).unwrap();
    wire.resize(legitimacy::trajectory::MAX_TRACE_JSON_INPUT_BYTES_V0, b' ');
    TrajectoryTraceV0::from_json_slice(&wire)
        .expect("exact-limit input with trailing whitespace must decode");

    wire.push(b' ');
    let error = TrajectoryTraceV0::from_json_slice(&wire)
        .expect_err("one byte over the exact input limit must fail before decoding");
    assert!(
        error
            .to_string()
            .contains("JSON input exceeds v0 byte limit")
    );
}

fn compact_json_len(trace: &TrajectoryTraceV0) -> usize {
    let mut writer = CountingWriter::default();
    serde_json::to_writer(&mut writer, trace).unwrap();
    writer.bytes
}

#[derive(Default)]
struct CountingWriter {
    bytes: usize,
}

impl Write for CountingWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.bytes = self
            .bytes
            .checked_add(bytes.len())
            .ok_or_else(|| io::Error::other("test compact JSON length overflow"))?;
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
