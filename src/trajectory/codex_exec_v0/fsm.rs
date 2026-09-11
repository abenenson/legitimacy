use super::error::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0};
use super::event::{
    CommandStatusV0, FileStatusV0, ItemClassV0, ItemV0, LifecycleV0, ParsedRecordV0,
};
use super::receipt::ProcessTerminationV0;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TerminalV0 {
    Completed,
    Failed,
}

#[derive(Clone)]
struct ActiveItemV0 {
    started: ItemV0,
}

#[derive(Clone)]
struct TodoLifecycleV0 {
    id: String,
    latest_items: Vec<super::event::TodoV0>,
    completed: bool,
}

pub(crate) fn validate_stream(
    records: &[ParsedRecordV0],
    raw_records: &[&[u8]],
    termination: Option<&ProcessTerminationV0>,
) -> AdapterResultV0<TerminalV0> {
    if !matches!(records.first(), Some(ParsedRecordV0::ThreadStarted { .. })) {
        return Err(state());
    }
    let mut turn_started = false;
    let mut terminal = None;
    let mut next_item = 0u64;
    let mut seen_items = BTreeMap::new();
    let mut active = BTreeMap::<String, ActiveItemV0>::new();
    let mut todo = None::<TodoLifecycleV0>;
    let mut reconciling_after_todo = false;

    for (index, record) in records.iter().enumerate() {
        if terminal.is_some() {
            return Err(at_record(index, raw_records, "$.type"));
        }
        if reconciling_after_todo && !is_reconciliation_or_terminal(record) {
            return Err(at_record(index, raw_records, "$.type"));
        }
        match record {
            ParsedRecordV0::ThreadStarted { .. } if index == 0 => {}
            ParsedRecordV0::ThreadStarted { .. } => {
                return Err(at_record(index, raw_records, "$.type"));
            }
            ParsedRecordV0::TurnStarted if !turn_started && index > 0 => {
                turn_started = true;
            }
            ParsedRecordV0::TurnStarted => {
                return Err(at_record(index, raw_records, "$.type"));
            }
            ParsedRecordV0::Error { .. } => {}
            ParsedRecordV0::Item { lifecycle, item } => {
                if !turn_started
                    && !matches!(
                        (lifecycle, item),
                        (LifecycleV0::Completed, ItemV0::Error { .. })
                    )
                {
                    return Err(at_record(index, raw_records, "$.item"));
                }
                validate_item_id(
                    index,
                    *lifecycle,
                    item,
                    &mut next_item,
                    &mut seen_items,
                    &mut active,
                    &mut todo,
                    &mut reconciling_after_todo,
                    raw_records,
                )?;
            }
            ParsedRecordV0::TurnCompleted { .. } => {
                if !turn_started || !active.is_empty() {
                    return Err(at_record(index, raw_records, "$.type"));
                }
                terminal = Some(TerminalV0::Completed);
            }
            ParsedRecordV0::TurnFailed { .. } => {
                if !turn_started || !active.is_empty() {
                    return Err(at_record(index, raw_records, "$.type"));
                }
                terminal = Some(TerminalV0::Failed);
            }
        }
    }
    let terminal = terminal.ok_or_else(state)?;
    validate_termination(terminal, termination)?;
    Ok(terminal)
}

#[allow(clippy::too_many_arguments)]
fn validate_item_id(
    index: usize,
    lifecycle: LifecycleV0,
    item: &ItemV0,
    next_item: &mut u64,
    seen: &mut BTreeMap<String, ItemClassV0>,
    active: &mut BTreeMap<String, ActiveItemV0>,
    todo: &mut Option<TodoLifecycleV0>,
    reconciling_after_todo: &mut bool,
    raw_records: &[&[u8]],
) -> AdapterResultV0<()> {
    let id = item.id();
    if id.len() > 128 {
        return Err(at_record(index, raw_records, "$.item.id"));
    }
    let class = item.class();
    if let Some(previous) = seen.get(id) {
        if *previous != class {
            return Err(at_record(index, raw_records, "$.item.id"));
        }
        let started = active
            .get(id)
            .ok_or_else(|| at_record(index, raw_records, "$.item.id"))?;
        if !same_active_item(&started.started, item) {
            return Err(at_record(index, raw_records, "$.item"));
        }
        match (item, lifecycle) {
            (ItemV0::TodoList { items, .. }, LifecycleV0::Updated) => {
                let state = todo
                    .as_mut()
                    .filter(|state| state.id == id && !state.completed)
                    .ok_or_else(|| at_record(index, raw_records, "$.item"))?;
                state.latest_items.clone_from(items);
            }
            (ItemV0::Command { .. } | ItemV0::FileChange { .. }, LifecycleV0::Completed) => {
                active.remove(id);
            }
            (ItemV0::TodoList { items, .. }, LifecycleV0::Completed) => {
                let state = todo
                    .as_mut()
                    .filter(|state| state.id == id && !state.completed)
                    .ok_or_else(|| at_record(index, raw_records, "$.item"))?;
                if state.latest_items != *items {
                    return Err(at_record(index, raw_records, "$.item.items"));
                }
                state.completed = true;
                active.remove(id);
                *reconciling_after_todo = true;
            }
            _ => return Err(at_record(index, raw_records, "$.item")),
        }
        return Ok(());
    }

    let expected = format!("item_{next_item}");
    if id != expected {
        return Err(at_record(index, raw_records, "$.item.id"));
    }
    *next_item = next_item.checked_add(1).ok_or_else(state)?;
    let first_is_legal = matches!(
        (item, lifecycle),
        (
            ItemV0::AgentMessage { .. } | ItemV0::Reasoning { .. } | ItemV0::Error { .. },
            LifecycleV0::Completed
        ) | (
            ItemV0::Command { .. } | ItemV0::FileChange { .. } | ItemV0::TodoList { .. },
            LifecycleV0::Started
        )
    );
    if !first_is_legal {
        return Err(at_record(index, raw_records, "$.item"));
    }
    seen.insert(id.to_string(), class);
    match item {
        ItemV0::TodoList { items, .. } => {
            if todo.is_some() {
                return Err(at_record(index, raw_records, "$.item"));
            }
            *todo = Some(TodoLifecycleV0 {
                id: id.to_string(),
                latest_items: items.clone(),
                completed: false,
            });
            active.insert(
                id.to_string(),
                ActiveItemV0 {
                    started: item.clone(),
                },
            );
        }
        ItemV0::Command { .. } | ItemV0::FileChange { .. } => {
            active.insert(
                id.to_string(),
                ActiveItemV0 {
                    started: item.clone(),
                },
            );
        }
        ItemV0::AgentMessage { .. } | ItemV0::Reasoning { .. } | ItemV0::Error { .. } => {}
    }
    Ok(())
}

fn same_active_item(started: &ItemV0, current: &ItemV0) -> bool {
    match (started, current) {
        (
            ItemV0::Command {
                command: first,
                status: CommandStatusV0::InProgress,
                ..
            },
            ItemV0::Command {
                command: second,
                status:
                    CommandStatusV0::Completed | CommandStatusV0::Failed | CommandStatusV0::Declined,
                ..
            },
        ) => first == second,
        (
            ItemV0::FileChange {
                changes: first,
                status: FileStatusV0::InProgress,
                ..
            },
            ItemV0::FileChange {
                changes: second,
                status: FileStatusV0::Completed | FileStatusV0::Failed,
                ..
            },
        ) => first == second,
        (ItemV0::TodoList { .. }, ItemV0::TodoList { .. }) => true,
        _ => false,
    }
}

fn is_reconciliation_or_terminal(record: &ParsedRecordV0) -> bool {
    matches!(
        record,
        ParsedRecordV0::Item {
            lifecycle: LifecycleV0::Completed,
            item: ItemV0::Command { .. } | ItemV0::FileChange { .. },
        } | ParsedRecordV0::TurnCompleted { .. }
            | ParsedRecordV0::TurnFailed { .. }
    )
}

fn validate_termination(
    terminal: TerminalV0,
    termination: Option<&ProcessTerminationV0>,
) -> AdapterResultV0<()> {
    let Some(termination) = termination else {
        return Ok(());
    };
    match (terminal, termination) {
        (TerminalV0::Completed, ProcessTerminationV0::Exited { code: 0 | 1 })
        | (TerminalV0::Failed, ProcessTerminationV0::Exited { code: 1 }) => Ok(()),
        (_, ProcessTerminationV0::Signaled { .. }) => {
            Err(AdapterErrorV0::new(AdapterErrorCodeV0::UnsupportedProfile))
        }
        (_, ProcessTerminationV0::Exited { .. }) => {
            Err(AdapterErrorV0::new(AdapterErrorCodeV0::IllegalTermination))
        }
    }
}

fn at_record(index: usize, _raw_records: &[&[u8]], path: &'static str) -> AdapterErrorV0 {
    AdapterErrorV0::record(AdapterErrorCodeV0::StreamState, index, path)
}

fn state() -> AdapterErrorV0 {
    AdapterErrorV0::new(AdapterErrorCodeV0::StreamState)
}
