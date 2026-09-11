use super::UsageV0;
use serde::Deserialize;
use serde_json::Value;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ThreadStartedWire {
    #[serde(rename = "type")]
    _type: String,
    pub thread_id: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct TurnStartedWire {
    #[serde(rename = "type")]
    _type: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct TurnCompletedWire {
    #[serde(rename = "type")]
    _type: String,
    pub usage: UsageWire,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct UsageWire {
    input_tokens: i64,
    cached_input_tokens: i64,
    output_tokens: i64,
    reasoning_output_tokens: i64,
}

impl From<UsageWire> for UsageV0 {
    fn from(value: UsageWire) -> Self {
        Self {
            input_tokens: value.input_tokens,
            cached_input_tokens: value.cached_input_tokens,
            output_tokens: value.output_tokens,
            reasoning_output_tokens: value.reasoning_output_tokens,
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ErrorWire {
    pub message: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct TurnFailedWire {
    #[serde(rename = "type")]
    _type: String,
    pub error: ErrorWire,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ErrorRecordWire {
    #[serde(rename = "type")]
    _type: String,
    pub message: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ItemRecordWire {
    #[serde(rename = "type")]
    _type: String,
    pub item: Value,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct TextItemWire {
    pub id: String,
    #[serde(rename = "type")]
    _type: String,
    pub text: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ErrorItemWire {
    pub id: String,
    #[serde(rename = "type")]
    _type: String,
    pub message: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct CommandItemWire {
    pub id: String,
    #[serde(rename = "type")]
    _type: String,
    pub command: String,
    pub aggregated_output: String,
    #[serde(deserialize_with = "required_option")]
    pub exit_code: Option<i32>,
    pub status: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct FileItemWire {
    pub id: String,
    #[serde(rename = "type")]
    _type: String,
    pub changes: Vec<ChangeWire>,
    pub status: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ChangeWire {
    pub path: String,
    pub kind: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct TodoItemWire {
    pub id: String,
    #[serde(rename = "type")]
    _type: String,
    pub items: Vec<TodoWire>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct TodoWire {
    pub text: String,
    pub completed: bool,
}

fn required_option<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}
