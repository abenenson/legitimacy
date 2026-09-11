#[path = "event_wire.rs"]
mod wire;

use super::error::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0};
use serde::Deserialize;
use serde_json::Value;
use wire::*;

const MAX_CHANGES_OR_TODOS_V0: usize = 1_024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LifecycleV0 {
    Started,
    Updated,
    Completed,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CommandStatusV0 {
    InProgress,
    Completed,
    Failed,
    Declined,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FileStatusV0 {
    InProgress,
    Completed,
    Failed,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ChangeKindV0 {
    Add,
    Delete,
    Update,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UsageV0 {
    pub input_tokens: i64,
    pub cached_input_tokens: i64,
    pub output_tokens: i64,
    pub reasoning_output_tokens: i64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ChangeV0 {
    pub path: String,
    pub kind: ChangeKindV0,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TodoV0 {
    pub text: String,
    pub completed: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ItemV0 {
    AgentMessage {
        id: String,
        text: String,
    },
    Reasoning {
        id: String,
        text: String,
    },
    Error {
        id: String,
        message: String,
    },
    Command {
        id: String,
        command: String,
        aggregated_output: String,
        exit_code: Option<i32>,
        status: CommandStatusV0,
    },
    FileChange {
        id: String,
        changes: Vec<ChangeV0>,
        status: FileStatusV0,
    },
    TodoList {
        id: String,
        items: Vec<TodoV0>,
    },
}

impl ItemV0 {
    pub fn id(&self) -> &str {
        match self {
            Self::AgentMessage { id, .. }
            | Self::Reasoning { id, .. }
            | Self::Error { id, .. }
            | Self::Command { id, .. }
            | Self::FileChange { id, .. }
            | Self::TodoList { id, .. } => id,
        }
    }

    pub fn class(&self) -> ItemClassV0 {
        match self {
            Self::AgentMessage { .. } => ItemClassV0::AgentMessage,
            Self::Reasoning { .. } => ItemClassV0::Reasoning,
            Self::Error { .. } => ItemClassV0::Error,
            Self::Command { .. } => ItemClassV0::Command,
            Self::FileChange { .. } => ItemClassV0::FileChange,
            Self::TodoList { .. } => ItemClassV0::TodoList,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum ItemClassV0 {
    AgentMessage,
    Reasoning,
    Error,
    Command,
    FileChange,
    TodoList,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ParsedRecordV0 {
    ThreadStarted {
        thread_id: String,
    },
    TurnStarted,
    TurnCompleted {
        usage: UsageV0,
    },
    TurnFailed {
        message: String,
    },
    Error {
        message: String,
    },
    Item {
        lifecycle: LifecycleV0,
        item: ItemV0,
    },
}

pub(crate) fn parse_record(bytes: &[u8], record_index: usize) -> AdapterResultV0<ParsedRecordV0> {
    let value: Value = serde_json::from_slice(bytes)
        .map_err(|_| AdapterErrorV0::record(AdapterErrorCodeV0::JsonSyntax, record_index, "$"))?;
    let record_type = value
        .as_object()
        .and_then(|object| object.get("type"))
        .and_then(Value::as_str)
        .ok_or_else(|| shape(record_index, "$.type"))?
        .to_string();

    let parsed = match record_type.as_str() {
        "thread.started" => {
            let wire: ThreadStartedWire = decode(value, record_index, "$")?;
            if !is_canonical_uuid_v7(&wire.thread_id) {
                return Err(shape(record_index, "$.thread_id"));
            }
            ParsedRecordV0::ThreadStarted {
                thread_id: wire.thread_id,
            }
        }
        "turn.started" => {
            let _: TurnStartedWire = decode(value, record_index, "$")?;
            ParsedRecordV0::TurnStarted
        }
        "turn.completed" => {
            let wire: TurnCompletedWire = decode(value, record_index, "$")?;
            let usage = wire.usage.into();
            if !usage_nonnegative(&usage) {
                return Err(shape(record_index, "$.usage"));
            }
            ParsedRecordV0::TurnCompleted { usage }
        }
        "turn.failed" => {
            let wire: TurnFailedWire = decode(value, record_index, "$")?;
            ParsedRecordV0::TurnFailed {
                message: wire.error.message,
            }
        }
        "error" => {
            let wire: ErrorRecordWire = decode(value, record_index, "$")?;
            ParsedRecordV0::Error {
                message: wire.message,
            }
        }
        "item.started" => parse_item_record(value, record_index, LifecycleV0::Started)?,
        "item.updated" => parse_item_record(value, record_index, LifecycleV0::Updated)?,
        "item.completed" => parse_item_record(value, record_index, LifecycleV0::Completed)?,
        _ => {
            return Err(AdapterErrorV0::record(
                AdapterErrorCodeV0::UnsupportedRecord,
                record_index,
                "$.type",
            ));
        }
    };
    validate_lifecycle(&parsed, record_index)?;
    Ok(parsed)
}

fn parse_item_record(
    value: Value,
    record_index: usize,
    lifecycle: LifecycleV0,
) -> AdapterResultV0<ParsedRecordV0> {
    let wire: ItemRecordWire = decode(value, record_index, "$")?;
    Ok(ParsedRecordV0::Item {
        lifecycle,
        item: parse_item(wire.item, record_index)?,
    })
}

fn parse_item(value: Value, index: usize) -> AdapterResultV0<ItemV0> {
    let item_type = value
        .as_object()
        .and_then(|object| object.get("type"))
        .and_then(Value::as_str)
        .ok_or_else(|| shape(index, "$.item.type"))?;
    match item_type {
        "agent_message" => {
            let value: TextItemWire = decode(value, index, "$.item")?;
            Ok(ItemV0::AgentMessage {
                id: value.id,
                text: value.text,
            })
        }
        "reasoning" => {
            let value: TextItemWire = decode(value, index, "$.item")?;
            if value.text.trim().is_empty() {
                return Err(shape(index, "$.item.text"));
            }
            Ok(ItemV0::Reasoning {
                id: value.id,
                text: value.text,
            })
        }
        "error" => {
            let value: ErrorItemWire = decode(value, index, "$.item")?;
            Ok(ItemV0::Error {
                id: value.id,
                message: value.message,
            })
        }
        "command_execution" => {
            let value: CommandItemWire = decode(value, index, "$.item")?;
            Ok(ItemV0::Command {
                id: value.id,
                command: value.command,
                aggregated_output: value.aggregated_output,
                exit_code: value.exit_code,
                status: parse_command_status(&value.status)
                    .ok_or_else(|| shape(index, "$.item.status"))?,
            })
        }
        "file_change" => {
            let value: FileItemWire = decode(value, index, "$.item")?;
            if value.changes.len() > MAX_CHANGES_OR_TODOS_V0
                || value
                    .changes
                    .windows(2)
                    .any(|pair| pair[0].path >= pair[1].path)
            {
                return Err(shape(index, "$.item.changes"));
            }
            let changes = value
                .changes
                .into_iter()
                .map(|change| {
                    let kind = match change.kind.as_str() {
                        "add" => ChangeKindV0::Add,
                        "delete" => ChangeKindV0::Delete,
                        "update" => ChangeKindV0::Update,
                        _ => return Err(shape(index, "$.item.changes[].kind")),
                    };
                    Ok(ChangeV0 {
                        path: change.path,
                        kind,
                    })
                })
                .collect::<AdapterResultV0<Vec<_>>>()?;
            let status = match value.status.as_str() {
                "in_progress" => FileStatusV0::InProgress,
                "completed" => FileStatusV0::Completed,
                "failed" => FileStatusV0::Failed,
                _ => return Err(shape(index, "$.item.status")),
            };
            Ok(ItemV0::FileChange {
                id: value.id,
                changes,
                status,
            })
        }
        "todo_list" => {
            let value: TodoItemWire = decode(value, index, "$.item")?;
            if value.items.len() > MAX_CHANGES_OR_TODOS_V0 {
                return Err(shape(index, "$.item.items"));
            }
            Ok(ItemV0::TodoList {
                id: value.id,
                items: value
                    .items
                    .into_iter()
                    .map(|item| TodoV0 {
                        text: item.text,
                        completed: item.completed,
                    })
                    .collect(),
            })
        }
        "mcp_tool_call" | "collab_tool_call" | "web_search" => Err(AdapterErrorV0::record(
            AdapterErrorCodeV0::UnsupportedRecord,
            index,
            "$.item.type",
        )),
        _ => Err(AdapterErrorV0::record(
            AdapterErrorCodeV0::UnsupportedRecord,
            index,
            "$.item.type",
        )),
    }
}

fn validate_lifecycle(record: &ParsedRecordV0, index: usize) -> AdapterResultV0<()> {
    let ParsedRecordV0::Item { lifecycle, item } = record else {
        return Ok(());
    };
    let legal = match (lifecycle, item) {
        (
            LifecycleV0::Completed,
            ItemV0::AgentMessage { .. } | ItemV0::Reasoning { .. } | ItemV0::Error { .. },
        ) => true,
        (
            LifecycleV0::Started,
            ItemV0::Command {
                aggregated_output,
                exit_code,
                status: CommandStatusV0::InProgress,
                ..
            },
        ) => aggregated_output.is_empty() && exit_code.is_none(),
        (
            LifecycleV0::Completed,
            ItemV0::Command {
                status:
                    CommandStatusV0::Completed | CommandStatusV0::Failed | CommandStatusV0::Declined,
                ..
            },
        ) => true,
        (
            LifecycleV0::Started,
            ItemV0::FileChange {
                status: FileStatusV0::InProgress,
                ..
            },
        )
        | (
            LifecycleV0::Completed,
            ItemV0::FileChange {
                status: FileStatusV0::Completed | FileStatusV0::Failed,
                ..
            },
        ) => true,
        (
            LifecycleV0::Started | LifecycleV0::Updated | LifecycleV0::Completed,
            ItemV0::TodoList { .. },
        ) => true,
        _ => false,
    };
    if legal {
        Ok(())
    } else {
        Err(AdapterErrorV0::record(
            AdapterErrorCodeV0::StreamState,
            index,
            "$.item",
        ))
    }
}

fn parse_command_status(value: &str) -> Option<CommandStatusV0> {
    match value {
        "in_progress" => Some(CommandStatusV0::InProgress),
        "completed" => Some(CommandStatusV0::Completed),
        "failed" => Some(CommandStatusV0::Failed),
        "declined" => Some(CommandStatusV0::Declined),
        _ => None,
    }
}

fn usage_nonnegative(value: &UsageV0) -> bool {
    value.input_tokens >= 0
        && value.cached_input_tokens >= 0
        && value.output_tokens >= 0
        && value.reasoning_output_tokens >= 0
}

fn is_canonical_uuid_v7(value: &str) -> bool {
    let bytes = value.as_bytes();
    bytes.len() == 36
        && bytes.iter().enumerate().all(|(index, byte)| match index {
            8 | 13 | 18 | 23 => *byte == b'-',
            14 => *byte == b'7',
            19 => matches!(*byte, b'8' | b'9' | b'a' | b'b'),
            _ => byte.is_ascii_digit() || matches!(*byte, b'a'..=b'f'),
        })
}

fn decode<T: for<'de> Deserialize<'de>>(
    value: Value,
    index: usize,
    path: &'static str,
) -> AdapterResultV0<T> {
    serde_json::from_value(value).map_err(|_| shape(index, path))
}

fn shape(index: usize, path: &'static str) -> AdapterErrorV0 {
    AdapterErrorV0::record(AdapterErrorCodeV0::JsonShape, index, path)
}
