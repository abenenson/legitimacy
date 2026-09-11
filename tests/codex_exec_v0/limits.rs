use super::*;
use legitimacy::trajectory::codex_exec_v0::{
    MAX_AUTHORITY_RECEIPT_BYTES_V0, MAX_CODEX_DECODED_STRING_BYTES_V0, MAX_CODEX_JSON_DEPTH_V0,
    MAX_CODEX_JSON_KEYS_V0, MAX_CODEX_JSON_NODES_V0, MAX_CODEX_JSONL_BYTES_V0,
    MAX_CODEX_RECORD_BYTES_V0, MAX_CODEX_RECORDS_V0,
};
use legitimacy::trajectory::{MAX_JSON_KEY_BYTES_PER_OBJECT_V0, MAX_JSON_KEYS_PER_OBJECT_V0};

#[test]
fn record_count_exact_limit_and_one_over_are_enforced() {
    let exact = b"{}\n".repeat(MAX_CODEX_RECORDS_V0);
    assert!(fixture_receipt(&exact).is_ok());
    let over = b"{}\n".repeat(MAX_CODEX_RECORDS_V0 + 1);
    assert_adapter_error(
        fixture_receipt(&over),
        AdapterErrorCodeV0::InputTooLarge,
        None,
        None,
    );
}

#[test]
fn record_byte_exact_limit_and_one_over_are_enforced() {
    let exact = padded_object(MAX_CODEX_RECORD_BYTES_V0);
    let mut exact_jsonl = exact;
    exact_jsonl.push(b'\n');
    assert!(fixture_receipt(&exact_jsonl).is_ok());

    let over = padded_object(MAX_CODEX_RECORD_BYTES_V0 + 1);
    let mut over_jsonl = over;
    over_jsonl.push(b'\n');
    assert_adapter_error(
        fixture_receipt(&over_jsonl),
        AdapterErrorCodeV0::InputTooLarge,
        None,
        None,
    );
}

#[test]
fn aggregate_byte_exact_limit_and_one_over_are_enforced() {
    let mut exact = Vec::new();
    while exact.len() + MAX_CODEX_RECORD_BYTES_V0 < MAX_CODEX_JSONL_BYTES_V0 {
        exact.extend(padded_object(MAX_CODEX_RECORD_BYTES_V0));
        exact.push(b'\n');
    }
    let remainder = MAX_CODEX_JSONL_BYTES_V0 - exact.len();
    if remainder > 0 {
        exact.extend(padded_object(remainder - 1));
        exact.push(b'\n');
    }
    assert_eq!(exact.len(), MAX_CODEX_JSONL_BYTES_V0);
    assert!(fixture_receipt(&exact).is_ok());

    let mut over = exact;
    over.insert(over.len() - 2, b' ');
    assert_eq!(over.len(), MAX_CODEX_JSONL_BYTES_V0 + 1);
    assert_adapter_error(
        fixture_receipt(&over),
        AdapterErrorCodeV0::InputTooLarge,
        None,
        None,
    );
}

#[test]
fn receipt_and_context_duplicate_keys_and_floats_fail_closed() {
    let authority = synthetic_authority(COMPLETED);
    let context = trusted(&authority);
    let encoded = serde_json::to_string(&context).unwrap();
    let duplicate = format!("{{\"context_version\":\"0\",{}", &encoded[1..]);
    assert_adapter_error(
        TrustedAdaptationContextV0::from_json_slice(duplicate.as_bytes()),
        AdapterErrorCodeV0::JsonSyntax,
        None,
        None,
    );

    let receipt = serde_json::to_string(&authority).unwrap();
    let float = receipt.replacen(
        &format!("\"full_jsonl_length\":{}", COMPLETED.len()),
        "\"full_jsonl_length\":1.0",
        1,
    );
    assert_adapter_error(
        InputAuthorityReceiptV0::from_json_slice(float.as_bytes()),
        AdapterErrorCodeV0::ReceiptShape,
        None,
        None,
    );
}

#[test]
fn depth_node_key_and_decoded_string_limits_accept_exact_and_reject_one_over() {
    let exact_depth = nested_array_object(MAX_CODEX_JSON_DEPTH_V0 - 2);
    assert!(fixture_receipt(&exact_depth).is_ok());
    let over_depth = nested_array_object(MAX_CODEX_JSON_DEPTH_V0 - 1);
    assert_adapter_error(
        fixture_receipt(&over_depth),
        AdapterErrorCodeV0::JsonBudget,
        Some(0),
        Some("$"),
    );

    let exact_nodes = array_object("0", MAX_CODEX_JSON_NODES_V0 - 2);
    assert!(fixture_receipt(&exact_nodes).is_ok());
    let over_nodes = array_object("0", MAX_CODEX_JSON_NODES_V0 - 1);
    assert_adapter_error(
        fixture_receipt(&over_nodes),
        AdapterErrorCodeV0::JsonBudget,
        Some(0),
        Some("$"),
    );

    let exact_keys = array_object(r#"{"a":0}"#, MAX_CODEX_JSON_KEYS_V0 - 1);
    assert!(fixture_receipt(&exact_keys).is_ok());
    let over_keys = array_object(r#"{"a":0}"#, MAX_CODEX_JSON_KEYS_V0);
    assert_adapter_error(
        fixture_receipt(&over_keys),
        AdapterErrorCodeV0::JsonBudget,
        Some(0),
        Some("$"),
    );

    let exact_string = string_object(MAX_CODEX_DECODED_STRING_BYTES_V0 - 1);
    assert!(fixture_receipt(&exact_string).is_ok());
    let over_string = string_object(MAX_CODEX_DECODED_STRING_BYTES_V0);
    assert_adapter_error(
        fixture_receipt(&over_string),
        AdapterErrorCodeV0::JsonBudget,
        Some(0),
        Some("$"),
    );
}

#[test]
fn object_key_count_and_byte_limits_accept_exact_and_reject_one_over() {
    let exact_count = object_with_keys(short_keys(MAX_JSON_KEYS_PER_OBJECT_V0));
    assert!(fixture_receipt(&exact_count).is_ok());
    let over_count = object_with_keys(short_keys(MAX_JSON_KEYS_PER_OBJECT_V0 + 1));
    assert_adapter_error(
        fixture_receipt(&over_count),
        AdapterErrorCodeV0::JsonBudget,
        Some(0),
        Some("$"),
    );

    let key_width = MAX_JSON_KEY_BYTES_PER_OBJECT_V0 / MAX_JSON_KEYS_PER_OBJECT_V0;
    assert_eq!(
        key_width * MAX_JSON_KEYS_PER_OBJECT_V0,
        MAX_JSON_KEY_BYTES_PER_OBJECT_V0
    );
    let exact_bytes = object_with_keys(fixed_width_keys(MAX_JSON_KEYS_PER_OBJECT_V0, key_width));
    assert!(fixture_receipt(&exact_bytes).is_ok());
    let mut over_widths = vec![key_width; MAX_JSON_KEYS_PER_OBJECT_V0];
    over_widths[0] += 1;
    let over_bytes = object_with_keys(variable_width_keys(&over_widths));
    assert_adapter_error(
        fixture_receipt(&over_bytes),
        AdapterErrorCodeV0::JsonBudget,
        Some(0),
        Some("$"),
    );
}

#[test]
fn authority_receipt_byte_cap_accepts_exact_and_rejects_one_over() {
    let authority = synthetic_authority(COMPLETED);
    let mut exact = serde_json::to_vec(&authority).unwrap();
    exact.resize(MAX_AUTHORITY_RECEIPT_BYTES_V0, b' ');
    assert!(InputAuthorityReceiptV0::from_json_slice(&exact).is_ok());
    exact.push(b' ');
    assert_adapter_error(
        InputAuthorityReceiptV0::from_json_slice(&exact),
        AdapterErrorCodeV0::InputTooLarge,
        None,
        None,
    );
}

fn fixture_receipt(
    bytes: &[u8],
) -> Result<SyntheticFixtureReceiptV0, legitimacy::trajectory::codex_exec_v0::AdapterErrorV0> {
    SyntheticFixtureReceiptV0::new_with_fixed_test_nonce(
        bytes,
        codex_exec_fixture_spec_binding_v0(),
        FixedSyntheticTestNonceV0::new([5; 32]),
    )
}

fn padded_object(length: usize) -> Vec<u8> {
    assert!(length >= 2);
    let mut bytes = vec![b' '; length];
    bytes[0] = b'{';
    bytes[length - 1] = b'}';
    bytes
}

fn nested_array_object(array_count: usize) -> Vec<u8> {
    let mut value = "0".to_string();
    for _ in 0..array_count {
        value = format!("[{value}]");
    }
    format!("{{\"x\":{value}}}\n").into_bytes()
}

fn array_object(element: &str, count: usize) -> Vec<u8> {
    let elements = std::iter::repeat_n(element, count)
        .collect::<Vec<_>>()
        .join(",");
    format!("{{\"x\":[{elements}]}}\n").into_bytes()
}

fn string_object(value_bytes: usize) -> Vec<u8> {
    format!("{{\"x\":\"{}\"}}\n", "a".repeat(value_bytes)).into_bytes()
}

fn short_keys(count: usize) -> Vec<String> {
    (0..count).map(|index| format!("k{index}")).collect()
}

fn fixed_width_keys(count: usize, width: usize) -> Vec<String> {
    variable_width_keys(&vec![width; count])
}

fn variable_width_keys(widths: &[usize]) -> Vec<String> {
    widths
        .iter()
        .enumerate()
        .map(|(index, width)| {
            let prefix = format!("k{index:04}");
            assert!(prefix.len() <= *width);
            format!("{prefix}{}", "x".repeat(width - prefix.len()))
        })
        .collect()
}

fn object_with_keys(keys: Vec<String>) -> Vec<u8> {
    let members = keys
        .into_iter()
        .map(|key| format!("\"{key}\":0"))
        .collect::<Vec<_>>()
        .join(",");
    format!("{{{members}}}\n").into_bytes()
}
