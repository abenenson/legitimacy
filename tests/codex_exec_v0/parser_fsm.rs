use super::*;

#[test]
fn duplicate_keys_and_framing_anomalies_fail_closed() {
    let cases = [
        (
            br#"{"type":"thread.started","type":"turn.started","thread_id":"00000000-0000-7000-8000-000000000010"}
"#
            .as_slice(),
            AdapterErrorCodeV0::JsonSyntax,
            Some(0),
            Some("$"),
        ),
        (
            br#"{"type":"thread.started","thread_id":"00000000-0000-7000-8000-000000000010"}
{"type":"turn.started","extra":{"a":1,"a":2}}
"#
            .as_slice(),
            AdapterErrorCodeV0::JsonSyntax,
            Some(1),
            Some("$"),
        ),
        (
            b"{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}\r\n"
                .as_slice(),
            AdapterErrorCodeV0::JsonFraming,
            None,
            None,
        ),
        (
            b"{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}"
                .as_slice(),
            AdapterErrorCodeV0::JsonFraming,
            None,
            None,
        ),
        (
            b"{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}\n\n"
                .as_slice(),
            AdapterErrorCodeV0::JsonFraming,
            None,
            None,
        ),
        (
            b"\xff\n".as_slice(),
            AdapterErrorCodeV0::JsonSyntax,
            None,
            None,
        ),
        (
            b"[]\n".as_slice(),
            AdapterErrorCodeV0::JsonShape,
            Some(0),
            Some("$"),
        ),
    ];
    for (bytes, code, record_index, structural_path) in cases {
        assert_adapter_error(
            synthetic_receipt_or_adapt(bytes),
            code,
            record_index,
            structural_path,
        );
    }
}

#[test]
fn stream_state_mutations_fail_without_partial_trace() {
    let cases = [
        (
            concat!(
                "{\"type\":\"turn.started\"}\n",
                "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}\n",
                "{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":0,\"cached_input_tokens\":0,\"output_tokens\":0,\"reasoning_output_tokens\":0}}\n"
            ),
            None,
            None,
        ),
        (
            concat!(
                "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}\n",
                "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_0\",\"type\":\"agent_message\",\"text\":\"x\"}}\n",
                "{\"type\":\"turn.started\"}\n",
                "{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":0,\"cached_input_tokens\":0,\"output_tokens\":0,\"reasoning_output_tokens\":0}}\n"
            ),
            Some(1),
            Some("$.item"),
        ),
        (
            concat!(
                "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}\n",
                "{\"type\":\"turn.started\"}\n"
            ),
            None,
            None,
        ),
        (
            concat!(
                "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}\n",
                "{\"type\":\"turn.started\"}\n",
                "{\"type\":\"turn.failed\",\"error\":{\"message\":\"x\"}}\n",
                "{\"type\":\"error\",\"message\":\"late\"}\n"
            ),
            Some(3),
            Some("$.type"),
        ),
        (
            concat!(
                "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}\n",
                "{\"type\":\"turn.started\"}\n",
                "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_0\",\"type\":\"command_execution\",\"command\":\"x\",\"aggregated_output\":\"\",\"exit_code\":0,\"status\":\"completed\"}}\n",
                "{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":0,\"cached_input_tokens\":0,\"output_tokens\":0,\"reasoning_output_tokens\":0}}\n"
            ),
            Some(2),
            Some("$.item"),
        ),
    ];
    for (case, record_index, structural_path) in cases {
        assert_adapter_error(
            adapt_fresh(case.as_bytes()),
            AdapterErrorCodeV0::StreamState,
            record_index,
            structural_path,
        );
    }
}

#[test]
fn illegal_lifecycle_item_status_and_property_matrix_fails() {
    let illegal_items = [
        (
            r#"{"type":"item.started","item":{"id":"item_0","type":"agent_message","text":"x"}}"#,
            AdapterErrorCodeV0::StreamState,
            "$.item",
        ),
        (
            r#"{"type":"item.updated","item":{"id":"item_0","type":"command_execution","command":"x","aggregated_output":"","exit_code":null,"status":"in_progress"}}"#,
            AdapterErrorCodeV0::StreamState,
            "$.item",
        ),
        (
            r#"{"type":"item.started","item":{"id":"item_0","type":"command_execution","command":"x","aggregated_output":"not-empty","exit_code":null,"status":"in_progress"}}"#,
            AdapterErrorCodeV0::StreamState,
            "$.item",
        ),
        (
            r#"{"type":"item.completed","item":{"id":"item_0","type":"file_change","changes":[],"status":"in_progress"}}"#,
            AdapterErrorCodeV0::StreamState,
            "$.item",
        ),
        (
            r#"{"type":"item.completed","item":{"id":"item_0","type":"file_change","changes":[],"status":"declined"}}"#,
            AdapterErrorCodeV0::JsonShape,
            "$.item.status",
        ),
        (
            r#"{"type":"item.started","item":{"id":"item_0","type":"todo_list","items":[],"status":"in_progress"}}"#,
            AdapterErrorCodeV0::JsonShape,
            "$.item",
        ),
        (
            r#"{"type":"item.completed","item":{"id":"item_0","type":"mcp_tool_call","server":"x"}}"#,
            AdapterErrorCodeV0::UnsupportedRecord,
            "$.item.type",
        ),
        (
            r#"{"type":"item.completed","item":{"id":"item_0","type":"collab_tool_call"}}"#,
            AdapterErrorCodeV0::UnsupportedRecord,
            "$.item.type",
        ),
        (
            r#"{"type":"item.completed","item":{"id":"item_0","type":"web_search"}}"#,
            AdapterErrorCodeV0::UnsupportedRecord,
            "$.item.type",
        ),
    ];
    for (item, code, structural_path) in illegal_items {
        let bytes = format!(
            "{{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}}\n{{\"type\":\"turn.started\"}}\n{item}\n{{\"type\":\"turn.completed\",\"usage\":{{\"input_tokens\":0,\"cached_input_tokens\":0,\"output_tokens\":0,\"reasoning_output_tokens\":0}}}}\n"
        );
        assert_adapter_error(
            adapt_fresh(bytes.as_bytes()),
            code,
            Some(2),
            Some(structural_path),
        );
    }
}

#[test]
fn item_identity_gaps_cross_type_reuse_and_changed_active_items_fail() {
    let cases = [
        (
            concat!(
                "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}\n",
                "{\"type\":\"turn.started\"}\n",
                "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_1\",\"type\":\"agent_message\",\"text\":\"x\"}}\n",
                "{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":0,\"cached_input_tokens\":0,\"output_tokens\":0,\"reasoning_output_tokens\":0}}\n"
            ),
            2,
            "$.item.id",
        ),
        (
            concat!(
                "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}\n",
                "{\"type\":\"turn.started\"}\n",
                "{\"type\":\"item.started\",\"item\":{\"id\":\"item_0\",\"type\":\"command_execution\",\"command\":\"a\",\"aggregated_output\":\"\",\"exit_code\":null,\"status\":\"in_progress\"}}\n",
                "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_0\",\"type\":\"file_change\",\"changes\":[],\"status\":\"completed\"}}\n",
                "{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":0,\"cached_input_tokens\":0,\"output_tokens\":0,\"reasoning_output_tokens\":0}}\n"
            ),
            3,
            "$.item.id",
        ),
        (
            concat!(
                "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000010\"}\n",
                "{\"type\":\"turn.started\"}\n",
                "{\"type\":\"item.started\",\"item\":{\"id\":\"item_0\",\"type\":\"command_execution\",\"command\":\"a\",\"aggregated_output\":\"\",\"exit_code\":null,\"status\":\"in_progress\"}}\n",
                "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_0\",\"type\":\"command_execution\",\"command\":\"b\",\"aggregated_output\":\"\",\"exit_code\":0,\"status\":\"completed\"}}\n",
                "{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":0,\"cached_input_tokens\":0,\"output_tokens\":0,\"reasoning_output_tokens\":0}}\n"
            ),
            3,
            "$.item",
        ),
    ];
    for (case, record_index, structural_path) in cases {
        assert_adapter_error(
            adapt_fresh(case.as_bytes()),
            AdapterErrorCodeV0::StreamState,
            Some(record_index),
            Some(structural_path),
        );
    }
}

#[test]
fn fresh_thread_id_is_exact_canonical_lowercase_uuid_v7() {
    let legal = [
        "00000000-0000-7000-8000-000000000000",
        "ffffffff-ffff-7fff-bfff-ffffffffffff",
        "01234567-89ab-7def-9abc-def012345678",
    ];
    for thread_id in legal {
        assert!(minimal_trace(thread_id).is_ok(), "{thread_id}");
    }
    let illegal = [
        "00000000-0000-6000-8000-000000000000",
        "00000000-0000-7000-c000-000000000000",
        "00000000-0000-7000-7000-000000000000",
        "00000000-0000-7000-8000-00000000000",
        "000000000000-7000-8000-000000000000",
        "00000000-0000-7000-8000-00000000000g",
        "00000000-0000-7000-A000-000000000000",
        "urn:uuid:00000000-0000-7000-8000-000000000000",
        "{00000000-0000-7000-8000-000000000000}",
    ];
    for thread_id in illegal {
        assert_adapter_error(
            minimal_trace(thread_id),
            AdapterErrorCodeV0::JsonShape,
            Some(0),
            Some("$.thread_id"),
        );
    }
}

#[test]
fn todo_lifecycle_matches_terminal_reconciliation_order() {
    let prefix = concat!(
        "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000020\"}\n",
        "{\"type\":\"turn.started\"}\n",
        "{\"type\":\"item.started\",\"item\":{\"id\":\"item_0\",\"type\":\"command_execution\",\"command\":\"synthetic\",\"aggregated_output\":\"\",\"exit_code\":null,\"status\":\"in_progress\"}}\n",
        "{\"type\":\"item.started\",\"item\":{\"id\":\"item_1\",\"type\":\"file_change\",\"changes\":[],\"status\":\"in_progress\"}}\n",
        "{\"type\":\"item.started\",\"item\":{\"id\":\"item_2\",\"type\":\"todo_list\",\"items\":[{\"text\":\"a\",\"completed\":false}]}}\n",
        "{\"type\":\"item.updated\",\"item\":{\"id\":\"item_2\",\"type\":\"todo_list\",\"items\":[{\"text\":\"a\",\"completed\":true}]}}\n"
    );
    let reconciliation = concat!(
        "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_2\",\"type\":\"todo_list\",\"items\":[{\"text\":\"a\",\"completed\":true}]}}\n",
        "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_0\",\"type\":\"command_execution\",\"command\":\"synthetic\",\"aggregated_output\":\"done\",\"exit_code\":0,\"status\":\"completed\"}}\n",
        "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_1\",\"type\":\"file_change\",\"changes\":[],\"status\":\"completed\"}}\n"
    );
    let completed = format!(
        "{prefix}{reconciliation}{}",
        "{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":0,\"cached_input_tokens\":0,\"output_tokens\":0,\"reasoning_output_tokens\":0}}\n"
    );
    assert!(adapt_fresh(completed.as_bytes()).is_ok());
    let failed = format!(
        "{prefix}{reconciliation}{}",
        "{\"type\":\"turn.failed\",\"error\":{\"message\":\"synthetic\"}}\n"
    );
    assert!(adapt_fresh(failed.as_bytes()).is_ok());

    let stale = format!(
        "{prefix}{}",
        concat!(
            "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_2\",\"type\":\"todo_list\",\"items\":[{\"text\":\"a\",\"completed\":false}]}}\n",
            "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_0\",\"type\":\"command_execution\",\"command\":\"synthetic\",\"aggregated_output\":\"done\",\"exit_code\":0,\"status\":\"completed\"}}\n",
            "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_1\",\"type\":\"file_change\",\"changes\":[],\"status\":\"completed\"}}\n",
            "{\"type\":\"turn.failed\",\"error\":{\"message\":\"synthetic\"}}\n"
        )
    );
    assert_adapter_error(
        adapt_fresh(stale.as_bytes()),
        AdapterErrorCodeV0::StreamState,
        Some(6),
        Some("$.item.items"),
    );

    for illegal_interleaving in [
        "{\"type\":\"error\",\"message\":\"late\"}\n",
        "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_3\",\"type\":\"agent_message\",\"text\":\"late\"}}\n",
        "{\"type\":\"item.updated\",\"item\":{\"id\":\"item_2\",\"type\":\"todo_list\",\"items\":[{\"text\":\"a\",\"completed\":true}]}}\n",
        "{\"type\":\"item.started\",\"item\":{\"id\":\"item_3\",\"type\":\"command_execution\",\"command\":\"late\",\"aggregated_output\":\"\",\"exit_code\":null,\"status\":\"in_progress\"}}\n",
    ] {
        let bytes = format!(
            "{prefix}{}{illegal_interleaving}{}",
            "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_2\",\"type\":\"todo_list\",\"items\":[{\"text\":\"a\",\"completed\":true}]}}\n",
            concat!(
                "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_0\",\"type\":\"command_execution\",\"command\":\"synthetic\",\"aggregated_output\":\"done\",\"exit_code\":0,\"status\":\"completed\"}}\n",
                "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_1\",\"type\":\"file_change\",\"changes\":[],\"status\":\"completed\"}}\n",
                "{\"type\":\"turn.failed\",\"error\":{\"message\":\"synthetic\"}}\n"
            )
        );
        assert_adapter_error(
            adapt_fresh(bytes.as_bytes()),
            AdapterErrorCodeV0::StreamState,
            Some(7),
            Some("$.type"),
        );
    }

    let wrong_order = format!(
        "{prefix}{}",
        concat!(
            "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_0\",\"type\":\"command_execution\",\"command\":\"synthetic\",\"aggregated_output\":\"done\",\"exit_code\":0,\"status\":\"completed\"}}\n",
            "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_2\",\"type\":\"todo_list\",\"items\":[{\"text\":\"a\",\"completed\":true}]}}\n",
            "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_1\",\"type\":\"file_change\",\"changes\":[],\"status\":\"completed\"}}\n",
            "{\"type\":\"turn.failed\",\"error\":{\"message\":\"synthetic\"}}\n"
        )
    );
    assert!(adapt_fresh(wrong_order.as_bytes()).is_ok());

    let second_todo = concat!(
        "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000020\"}\n",
        "{\"type\":\"turn.started\"}\n",
        "{\"type\":\"item.started\",\"item\":{\"id\":\"item_0\",\"type\":\"todo_list\",\"items\":[]}}\n",
        "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_0\",\"type\":\"todo_list\",\"items\":[]}}\n",
        "{\"type\":\"item.started\",\"item\":{\"id\":\"item_1\",\"type\":\"todo_list\",\"items\":[]}}\n",
        "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_1\",\"type\":\"todo_list\",\"items\":[]}}\n",
        "{\"type\":\"turn.failed\",\"error\":{\"message\":\"synthetic\"}}\n"
    );
    assert_adapter_error(
        adapt_fresh(second_todo.as_bytes()),
        AdapterErrorCodeV0::StreamState,
        Some(4),
        Some("$.type"),
    );
}

fn minimal_trace(
    thread_id: &str,
) -> Result<(), legitimacy::trajectory::codex_exec_v0::AdapterErrorV0> {
    let bytes = format!(
        "{{\"type\":\"thread.started\",\"thread_id\":\"{thread_id}\"}}\n{{\"type\":\"turn.started\"}}\n{{\"type\":\"turn.failed\",\"error\":{{\"message\":\"synthetic\"}}}}\n"
    );
    adapt_fresh(bytes.as_bytes()).map(|_| ())
}

fn synthetic_receipt_or_adapt(
    bytes: &[u8],
) -> Result<(), legitimacy::trajectory::codex_exec_v0::AdapterErrorV0> {
    let receipt = SyntheticFixtureReceiptV0::new_with_fixed_test_nonce(
        bytes,
        codex_exec_fixture_spec_binding_v0(),
        FixedSyntheticTestNonceV0::new([3; 32]),
    )?;
    let authority = InputAuthorityReceiptV0::SyntheticFixture(receipt);
    adapt_codex_exec_v0(bytes, &authority, &trusted(&authority)).map(|_| ())
}
