use super::*;
use std::fmt::Write as _;

const ZERO_DIGEST: &str = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

#[test]
fn near_limit_unknown_array_is_fully_scanned_without_retaining_elements() {
    let wire = unknown_zero_array_json(
        legitimacy::trajectory::MAX_TRACE_JSON_INPUT_BYTES_V0.saturating_sub(1),
    );
    assert_eq!(
        wire.len(),
        legitimacy::trajectory::MAX_TRACE_JSON_INPUT_BYTES_V0 - 1
    );

    let error = TrajectoryTraceV0::from_json_slice(&wire)
        .expect_err("the closed typed shape must reject the unknown field");
    assert!(
        error.to_string().contains("unknown field"),
        "expected typed unknown-field rejection after streaming scan, got '{error}'"
    );
}

#[test]
fn duplicate_near_end_of_large_unknown_array_is_not_skipped() {
    let mut wire = unknown_zero_array_json(
        legitimacy::trajectory::MAX_TRACE_JSON_INPUT_BYTES_V0.saturating_sub(65),
    );
    wire.truncate(wire.len() - 3);
    wire.extend_from_slice(br#"{"late":1,"late":2}]}"#);
    assert!(wire.len() <= legitimacy::trajectory::MAX_TRACE_JSON_INPUT_BYTES_V0);

    let error = TrajectoryTraceV0::from_json_slice(&wire)
        .expect_err("a duplicate in the final nested value must be scanned");
    assert!(
        error.to_string().contains("duplicate JSON object key"),
        "expected nested duplicate rejection, got '{error}'"
    );
}

#[test]
fn raw_record_root_kind_and_trailing_material_remain_fail_closed() {
    let object = br#"{"accepted":[null,true,3.5,{"nested":"value"}]}"#.as_slice();
    let (trace, trusted) = fixture(&[object]);
    trace.validate(&[object], &trusted).unwrap();

    for non_object in [
        b"[]".as_slice(),
        b"null".as_slice(),
        b"true".as_slice(),
        b"7".as_slice(),
        br#""scalar""#.as_slice(),
    ] {
        let (trace, trusted) = fixture(&[non_object]);
        assert_validation_error(
            &trace,
            &[non_object],
            &trusted,
            "raw record 0 must be a JSON object",
        );
    }

    for trailing in [b"{} []".as_slice(), b"{} false".as_slice()] {
        let (trace, trusted) = fixture(&[trailing]);
        assert_raw_json_error(&trace, trailing, &trusted);
    }
}

#[test]
fn malformed_utf8_json_and_unsupported_numbers_remain_fail_closed() {
    let malformed_utf8 = b"{\"\xff\":0}".as_slice();
    let malformed_json = br#"{"unterminated":[1,2}"#.as_slice();
    let hostile_numbers = [
        br#"{"value":NaN}"#.as_slice(),
        br#"{"value":Infinity}"#.as_slice(),
        br#"{"value":-Infinity}"#.as_slice(),
        br#"{"value":1e9999}"#.as_slice(),
        br#"{"value":01}"#.as_slice(),
        br#"{"value":+1}"#.as_slice(),
    ];

    for raw in std::iter::once(malformed_utf8)
        .chain(std::iter::once(malformed_json))
        .chain(hostile_numbers)
    {
        let (trace, trusted) = fixture(&[raw]);
        assert_raw_json_error(&trace, raw, &trusted);
    }
}

#[test]
fn trace_key_count_cap_accepts_exact_and_rejects_one_over_before_typed_decode() {
    let exact = object_with_uniform_values(short_keys(
        legitimacy::trajectory::MAX_JSON_KEYS_PER_OBJECT_V0,
    ));
    assert_trace_scan_reaches_typed_decode(&exact);

    let one_over = object_with_uniform_values(short_keys(
        legitimacy::trajectory::MAX_JSON_KEYS_PER_OBJECT_V0 + 1,
    ));
    assert_trace_scan_error(&one_over, "JSON object key count exceeds v0 limit");
}

#[test]
fn trace_key_byte_cap_accepts_exact_and_rejects_one_over_before_typed_decode() {
    let exact_keys = fixed_width_keys(
        legitimacy::trajectory::MAX_JSON_KEYS_PER_OBJECT_V0,
        legitimacy::trajectory::MAX_JSON_KEY_BYTES_PER_OBJECT_V0
            / legitimacy::trajectory::MAX_JSON_KEYS_PER_OBJECT_V0,
    );
    assert_eq!(
        decoded_key_bytes(&exact_keys),
        legitimacy::trajectory::MAX_JSON_KEY_BYTES_PER_OBJECT_V0
    );
    assert_trace_scan_reaches_typed_decode(&object_with_uniform_values(exact_keys.clone()));

    let mut one_over_keys = exact_keys;
    one_over_keys.last_mut().unwrap().push('x');
    assert_eq!(
        decoded_key_bytes(&one_over_keys),
        legitimacy::trajectory::MAX_JSON_KEY_BYTES_PER_OBJECT_V0 + 1
    );
    assert_trace_scan_error(
        &object_with_uniform_values(one_over_keys),
        "JSON object key bytes exceed v0 limit",
    );
}

#[test]
fn raw_record_key_caps_accept_exact_and_reject_one_over_before_hashing() {
    let exact_count = object_with_uniform_values(short_keys(
        legitimacy::trajectory::MAX_JSON_KEYS_PER_OBJECT_V0,
    ));
    assert_raw_record_accepts(&exact_count);
    let one_over_count = object_with_uniform_values(short_keys(
        legitimacy::trajectory::MAX_JSON_KEYS_PER_OBJECT_V0 + 1,
    ));
    assert_raw_scan_precedes_capture_hash(
        &one_over_count,
        "JSON object key count exceeds v0 limit",
    );

    let exact_byte_keys = fixed_width_keys(
        legitimacy::trajectory::MAX_JSON_KEYS_PER_OBJECT_V0,
        legitimacy::trajectory::MAX_JSON_KEY_BYTES_PER_OBJECT_V0
            / legitimacy::trajectory::MAX_JSON_KEYS_PER_OBJECT_V0,
    );
    let exact_bytes = object_with_uniform_values(exact_byte_keys.clone());
    assert_raw_record_accepts(&exact_bytes);

    let mut one_over_byte_keys = exact_byte_keys;
    one_over_byte_keys.last_mut().unwrap().push('x');
    let one_over_bytes = object_with_uniform_values(one_over_byte_keys);
    assert_raw_scan_precedes_capture_hash(&one_over_bytes, "JSON object key bytes exceed v0 limit");
}

#[test]
fn nested_objects_account_independently_and_release_completed_child_keys() {
    let width = legitimacy::trajectory::MAX_JSON_KEY_BYTES_PER_OBJECT_V0
        / legitimacy::trajectory::MAX_JSON_KEYS_PER_OBJECT_V0;
    let exact_keys = fixed_width_keys(legitimacy::trajectory::MAX_JSON_KEYS_PER_OBJECT_V0, width);
    let exact_child = object_with_uniform_values(exact_keys.clone());
    let exact_parent =
        object_with_selected_values(exact_keys.clone(), &[(0, &exact_child), (1, &exact_child)]);
    assert_raw_record_accepts(&exact_parent);

    let mut child_one_over_keys = exact_keys;
    child_one_over_keys.last_mut().unwrap().push('x');
    let child_one_over = object_with_uniform_values(child_one_over_keys);
    let parent_with_oversized_child =
        object_with_selected_values(short_keys(2), &[(0, &child_one_over)]);
    assert_raw_scan_precedes_capture_hash(
        &parent_with_oversized_child,
        "JSON object key bytes exceed v0 limit",
    );

    let parent_one_over = object_with_selected_values(
        short_keys(legitimacy::trajectory::MAX_JSON_KEYS_PER_OBJECT_V0 + 1),
        &[(0, &exact_child)],
    );
    assert_raw_scan_precedes_capture_hash(
        &parent_one_over,
        "JSON object key count exceeds v0 limit",
    );
}

fn unknown_zero_array_json(byte_length: usize) -> Vec<u8> {
    const PREFIX: &[u8] = br#"{"unknown":["#;
    const SUFFIX: &[u8] = b"]}";
    let content_length = byte_length
        .checked_sub(PREFIX.len() + SUFFIX.len())
        .expect("fixture must have room for an array");
    assert_eq!(
        content_length % 2,
        1,
        "zero/comma array content must have odd length"
    );

    let mut wire = Vec::with_capacity(byte_length);
    wire.extend_from_slice(PREFIX);
    let content_start = wire.len();
    wire.resize(content_start + content_length, b',');
    for index in (content_start..wire.len()).step_by(2) {
        wire[index] = b'0';
    }
    wire.extend_from_slice(SUFFIX);
    wire
}

fn short_keys(count: usize) -> Vec<String> {
    (0..count).map(|index| format!("k{index:04}")).collect()
}

fn fixed_width_keys(count: usize, width: usize) -> Vec<String> {
    assert!(width >= 8);
    (0..count)
        .map(|index| format!("{index:08}{}", "k".repeat(width - 8)))
        .collect()
}

fn decoded_key_bytes(keys: &[String]) -> usize {
    keys.iter().map(String::len).sum()
}

fn object_with_uniform_values(keys: Vec<String>) -> Vec<u8> {
    object_with_selected_values(keys, &[])
}

fn object_with_selected_values(keys: Vec<String>, selected: &[(usize, &[u8])]) -> Vec<u8> {
    let mut wire = String::from("{");
    for (index, key) in keys.iter().enumerate() {
        if index != 0 {
            wire.push(',');
        }
        write!(&mut wire, "\"{key}\":").unwrap();
        if let Some((_, value)) = selected.iter().find(|(selected, _)| *selected == index) {
            wire.push_str(std::str::from_utf8(value).unwrap());
        } else {
            wire.push_str("null");
        }
    }
    wire.push('}');
    wire.into_bytes()
}

fn assert_trace_scan_reaches_typed_decode(wire: &[u8]) {
    let error = TrajectoryTraceV0::from_json_slice(wire)
        .expect_err("unknown fields must fail in authoritative typed decoding");
    assert!(
        error.to_string().contains("unknown field"),
        "expected typed rejection after an exact-cap scan, got '{error}'"
    );
}

fn assert_trace_scan_error(wire: &[u8], expected: &str) {
    let error = TrajectoryTraceV0::from_json_slice(wire)
        .expect_err("one-over scanner input must fail before typed decoding");
    assert!(
        error.to_string().contains(expected),
        "expected '{expected}', got '{error}'"
    );
}

fn assert_raw_record_accepts(raw: &[u8]) {
    let raw_records = [raw];
    let (trace, trusted) = fixture(&raw_records);
    trace.validate(&raw_records, &trusted).unwrap();
}

fn assert_raw_scan_precedes_capture_hash(raw: &[u8], expected: &str) {
    let (mut trace, mut trusted) = fixture(&[RECORD_ZERO]);
    trace.raw_capture.digest = ZERO_DIGEST.to_string();
    trusted.raw_capture = trace.raw_capture.clone();

    assert_validation_error(&trace, &[raw], &trusted, expected);
}

fn assert_raw_json_error(
    trace: &TrajectoryTraceV0,
    raw: &[u8],
    trusted: &TrajectoryValidationContextV0,
) {
    let error = trace
        .validate(&[raw], trusted)
        .expect_err("malformed or trailing JSON must fail");
    assert!(
        matches!(error, legitimacy::LegitimacyError::Json { .. }),
        "expected a JSON error, got '{error}'"
    );
}
