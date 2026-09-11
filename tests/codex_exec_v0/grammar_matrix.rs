use super::*;

const THREAD: &str =
    "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000030\"}\n";
const TURN: &str = "{\"type\":\"turn.started\"}\n";
const STARTED_TURN: &str = concat!(
    "{\"type\":\"thread.started\",\"thread_id\":\"00000000-0000-7000-8000-000000000030\"}\n",
    "{\"type\":\"turn.started\"}\n"
);
const COMPLETE: &str = "{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":0,\"cached_input_tokens\":0,\"output_tokens\":0,\"reasoning_output_tokens\":0}}\n";

#[test]
fn every_legal_item_status_variant_is_accepted() {
    for item in [
        completed(r#"{"id":"item_0","type":"agent_message","text":"synthetic"}"#),
        completed(r#"{"id":"item_0","type":"reasoning","text":"synthetic"}"#),
        completed(r#"{"id":"item_0","type":"error","message":"synthetic"}"#),
        command_pair("completed", "0"),
        command_pair("failed", "1"),
        command_pair("declined", "null"),
        file_pair("completed"),
        file_pair("failed"),
        todo_triplet(),
    ] {
        assert!(adapt_fresh(format!("{THREAD}{TURN}{item}{COMPLETE}").as_bytes()).is_ok());
    }
}

#[test]
fn every_illegal_lifecycle_item_and_status_class_is_rejected() {
    let text_items = [
        r#"{"id":"item_0","type":"agent_message","text":"synthetic"}"#,
        r#"{"id":"item_0","type":"reasoning","text":"synthetic"}"#,
        r#"{"id":"item_0","type":"error","message":"synthetic"}"#,
    ];
    for lifecycle in ["started", "updated"] {
        for item in text_items {
            rejects(
                &format!(r#"{{"type":"item.{lifecycle}","item":{item}}}"#),
                AdapterErrorCodeV0::StreamState,
                "$.item",
            );
        }
    }
    for item in [
        r#"{"id":"item_0","type":"command_execution","command":"x","aggregated_output":"","exit_code":null,"status":"in_progress"}"#,
        r#"{"id":"item_0","type":"file_change","changes":[],"status":"in_progress"}"#,
    ] {
        rejects(
            &format!(r#"{{"type":"item.updated","item":{item}}}"#),
            AdapterErrorCodeV0::StreamState,
            "$.item",
        );
    }
    for status in ["completed", "failed", "declined"] {
        rejects(
            &format!(
                r#"{{"type":"item.started","item":{{"id":"item_0","type":"command_execution","command":"x","aggregated_output":"","exit_code":null,"status":"{status}"}}}}"#
            ),
            AdapterErrorCodeV0::StreamState,
            "$.item",
        );
    }
    rejects(
        r#"{"type":"item.started","item":{"id":"item_0","type":"command_execution","command":"x","aggregated_output":"","exit_code":null,"status":"unknown"}}"#,
        AdapterErrorCodeV0::JsonShape,
        "$.item.status",
    );
    rejects(
        r#"{"type":"item.completed","item":{"id":"item_0","type":"command_execution","command":"x","aggregated_output":"","exit_code":null,"status":"in_progress"}}"#,
        AdapterErrorCodeV0::StreamState,
        "$.item",
    );
    rejects(
        r#"{"type":"item.completed","item":{"id":"item_0","type":"command_execution","command":"x","aggregated_output":"","exit_code":null,"status":"unknown"}}"#,
        AdapterErrorCodeV0::JsonShape,
        "$.item.status",
    );
    for status in ["completed", "failed"] {
        rejects(
            &format!(
                r#"{{"type":"item.started","item":{{"id":"item_0","type":"file_change","changes":[],"status":"{status}"}}}}"#
            ),
            AdapterErrorCodeV0::StreamState,
            "$.item",
        );
    }
    for status in ["declined", "unknown"] {
        rejects(
            &format!(
                r#"{{"type":"item.started","item":{{"id":"item_0","type":"file_change","changes":[],"status":"{status}"}}}}"#
            ),
            AdapterErrorCodeV0::JsonShape,
            "$.item.status",
        );
    }
    rejects(
        r#"{"type":"item.completed","item":{"id":"item_0","type":"file_change","changes":[],"status":"in_progress"}}"#,
        AdapterErrorCodeV0::StreamState,
        "$.item",
    );
    for status in ["declined", "unknown"] {
        rejects(
            &format!(
                r#"{{"type":"item.completed","item":{{"id":"item_0","type":"file_change","changes":[],"status":"{status}"}}}}"#
            ),
            AdapterErrorCodeV0::JsonShape,
            "$.item.status",
        );
    }
    for lifecycle in ["updated", "completed"] {
        rejects(
            &format!(
                r#"{{"type":"item.{lifecycle}","item":{{"id":"item_0","type":"todo_list","items":[]}}}}"#
            ),
            AdapterErrorCodeV0::StreamState,
            "$.item",
        );
    }
}

#[test]
fn unknown_properties_fail_at_every_accepted_object_layer() {
    for (record, code, structural_path, prefix, suffix, record_index) in [
        (
            r#"{"type":"thread.started","thread_id":"00000000-0000-7000-8000-000000000030","extra":0}"#,
            AdapterErrorCodeV0::JsonShape,
            "$",
            "",
            "",
            0,
        ),
        (
            r#"{"type":"turn.started","extra":0}"#,
            AdapterErrorCodeV0::JsonShape,
            "$",
            STARTED_TURN,
            COMPLETE,
            2,
        ),
        (
            r#"{"type":"turn.completed","usage":{"input_tokens":0,"cached_input_tokens":0,"output_tokens":0,"reasoning_output_tokens":0,"extra":0}}"#,
            AdapterErrorCodeV0::JsonShape,
            "$",
            "",
            "",
            0,
        ),
        (
            r#"{"type":"turn.failed","error":{"message":"x","extra":0}}"#,
            AdapterErrorCodeV0::JsonShape,
            "$",
            "",
            "",
            0,
        ),
        (
            r#"{"type":"error","message":"x","extra":0}"#,
            AdapterErrorCodeV0::JsonShape,
            "$",
            STARTED_TURN,
            COMPLETE,
            2,
        ),
        (
            r#"{"type":"item.completed","extra":0,"item":{"id":"item_0","type":"agent_message","text":"x"}}"#,
            AdapterErrorCodeV0::JsonShape,
            "$",
            STARTED_TURN,
            COMPLETE,
            2,
        ),
        (
            r#"{"type":"item.completed","item":{"id":"item_0","type":"agent_message","text":"x","extra":0}}"#,
            AdapterErrorCodeV0::JsonShape,
            "$.item",
            STARTED_TURN,
            COMPLETE,
            2,
        ),
        (
            r#"{"type":"item.started","item":{"id":"item_0","type":"file_change","changes":[{"path":"a","kind":"add","extra":0}],"status":"in_progress"}}"#,
            AdapterErrorCodeV0::JsonShape,
            "$.item",
            STARTED_TURN,
            COMPLETE,
            2,
        ),
        (
            r#"{"type":"item.started","item":{"id":"item_0","type":"todo_list","items":[{"text":"a","completed":false,"extra":0}]}}"#,
            AdapterErrorCodeV0::JsonShape,
            "$.item",
            STARTED_TURN,
            COMPLETE,
            2,
        ),
        (
            r#"{"type":"unknown"}"#,
            AdapterErrorCodeV0::UnsupportedRecord,
            "$.type",
            STARTED_TURN,
            COMPLETE,
            2,
        ),
    ] {
        let bytes = format!("{prefix}{record}\n{suffix}");
        assert_adapter_error(
            adapt_fresh(bytes.as_bytes()),
            code,
            Some(record_index),
            Some(structural_path),
        );
    }
}

fn rejects(record: &str, code: AdapterErrorCodeV0, structural_path: &'static str) {
    assert_adapter_error(
        adapt_fresh(format!("{THREAD}{TURN}{record}\n{COMPLETE}").as_bytes()),
        code,
        Some(2),
        Some(structural_path),
    );
}

fn completed(item: &str) -> String {
    format!(r#"{{"type":"item.completed","item":{item}}}"#) + "\n"
}

fn command_pair(status: &str, exit_code: &str) -> String {
    format!(
        "{}\n{}\n",
        r#"{"type":"item.started","item":{"id":"item_0","type":"command_execution","command":"synthetic","aggregated_output":"","exit_code":null,"status":"in_progress"}}"#,
        format_args!(
            r#"{{"type":"item.completed","item":{{"id":"item_0","type":"command_execution","command":"synthetic","aggregated_output":"synthetic","exit_code":{exit_code},"status":"{status}"}}}}"#
        )
    )
}

fn file_pair(status: &str) -> String {
    format!(
        "{}\n{}\n",
        r#"{"type":"item.started","item":{"id":"item_0","type":"file_change","changes":[],"status":"in_progress"}}"#,
        format_args!(
            r#"{{"type":"item.completed","item":{{"id":"item_0","type":"file_change","changes":[],"status":"{status}"}}}}"#
        )
    )
}

fn todo_triplet() -> String {
    concat!(
        "{\"type\":\"item.started\",\"item\":{\"id\":\"item_0\",\"type\":\"todo_list\",\"items\":[{\"text\":\"a\",\"completed\":false}]}}\n",
        "{\"type\":\"item.updated\",\"item\":{\"id\":\"item_0\",\"type\":\"todo_list\",\"items\":[{\"text\":\"a\",\"completed\":true}]}}\n",
        "{\"type\":\"item.completed\",\"item\":{\"id\":\"item_0\",\"type\":\"todo_list\",\"items\":[{\"text\":\"a\",\"completed\":true}]}}\n"
    )
    .to_string()
}
