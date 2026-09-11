use super::*;

#[test]
fn aggregate_normalized_content_budget_rejects_one_more_before_compact_measurement() {
    let raw = vec![RECORD_ZERO];
    let (mut trace, trusted) = fixture(&raw);
    let field = trace.events[0].payload.remove("command").unwrap();
    let full_chunk = "🦀".repeat(legitimacy::trajectory::MAX_NORMALIZED_STRING_SCALARS_V0);
    assert_eq!(
        full_chunk.len(),
        legitimacy::trajectory::MAX_NORMALIZED_STRING_BYTES_V0
    );
    let mut values = vec![NormalizedValueV0::String(full_chunk); 127];
    let final_chunk = format!(
        "{}€",
        "🦀".repeat(legitimacy::trajectory::MAX_NORMALIZED_STRING_SCALARS_V0 - 1)
    );
    assert_eq!(
        final_chunk.len(),
        legitimacy::trajectory::MAX_NORMALIZED_STRING_BYTES_V0 - 1
    );
    values.push(NormalizedValueV0::String(final_chunk));
    trace.events[0].payload.insert(
        "x".to_string(),
        EvidencedV0 {
            value: Some(NormalizedValueV0::Array(values)),
            evidence: field.evidence,
        },
    );

    assert_validation_error(
        &trace,
        &raw,
        &trusted,
        "official compact JSON exceeds v0 byte limit",
    );

    let NormalizedValueV0::Array(values) = trace.events[0]
        .payload
        .get_mut("x")
        .unwrap()
        .value
        .as_mut()
        .unwrap()
    else {
        unreachable!();
    };
    let NormalizedValueV0::String(final_chunk) = values.last_mut().unwrap() else {
        unreachable!();
    };
    final_chunk.push('a');
    let invalid_raw = vec![b"not-json".as_slice()];
    assert_validation_error(
        &trace,
        &invalid_raw,
        &trusted,
        "payload content bytes exceed v0 total limit",
    );
}
