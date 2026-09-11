use super::codex_exec_adapter_binding_v0;
use super::error::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0};
use super::event::{
    ChangeKindV0, CommandStatusV0, FileStatusV0, ItemV0, LifecycleV0, ParsedRecordV0,
};
use super::receipt::{InputAuthorityReceiptV0, TrustedAdaptationContextV0};
use crate::trajectory::{
    AgentActionEventV0, ArtifactBindingV0, EvidenceV0, EvidencedV0, NormalizedEventKindV0,
    NormalizedValueV0, RawRecordReferenceV0, SourceLocatorV0, TrajectoryTraceV0,
    TrajectoryValidationContextV0, artifact_digest_v0, framed_sha256, raw_record_digest_v0,
    source_locator_digest_v0, trajectory_schema_binding_v0,
};
use std::collections::{BTreeMap, BTreeSet};

const RUN_ID_DOMAIN_V0: &str = "legitimacy.codex-exec-v0.run-id.v0";
const EVENT_ID_DOMAIN_V0: &str = "legitimacy.codex-exec-v0.event-id.v0";
const RUN_RULE_BYTES: &[u8] =
    b"run-id := hash(thread-started-whole-record-digest, decoded-canonical-thread-id)";
const EVENT_RULE_BYTES: &[u8] =
    b"event-id := hash(normalized-run-id, source-position, whole-raw-record-digest)";
const POSITION_RULE_BYTES: &[u8] = b"sequence-index := zero-based-source-record-position";
const FIELD_RULE_BYTES: &[u8] =
    b"field-projection := closed-v0-table(decoded-source-fields, whole-raw-record)";

pub(crate) struct MappedV0 {
    pub trace: TrajectoryTraceV0,
    pub validation_declarations: TrajectoryValidationContextV0,
}

pub(crate) fn map_records(
    records: &[ParsedRecordV0],
    raw_records: &[&[u8]],
    authority: &InputAuthorityReceiptV0,
    context: &TrustedAdaptationContextV0,
) -> AdapterResultV0<MappedV0> {
    map_records_with_bindings(
        records,
        raw_records,
        authority.raw_seal(),
        context.downstream_governance_policy(),
    )
}

pub(crate) fn map_records_with_bindings(
    records: &[ParsedRecordV0],
    raw_records: &[&[u8]],
    raw_capture: &crate::trajectory::RawCaptureSealV0,
    downstream_policy: &ArtifactBindingV0,
) -> AdapterResultV0<MappedV0> {
    if records.len() != raw_records.len() {
        return Err(mapping_record(records.len().min(raw_records.len()), "$"));
    }
    let (thread_id, record_zero) = match (records.first(), raw_records.first()) {
        (Some(ParsedRecordV0::ThreadStarted { thread_id }), Some(raw)) => (thread_id, *raw),
        (Some(_), Some(_)) => return Err(mapping_record(0, "$.type")),
        (None, None) => return Err(AdapterErrorV0::new(AdapterErrorCodeV0::Mapping)),
        (Some(_), None) | (None, Some(_)) => {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::Mapping));
        }
    };
    let run_rule = rule("derivation.codex-exec-v0.run-id", RUN_RULE_BYTES);
    let event_rule = rule("derivation.codex-exec-v0.event-id", EVENT_RULE_BYTES);
    let position_rule = rule(
        "derivation.codex-exec-v0.source-position",
        POSITION_RULE_BYTES,
    );
    let field_rule = rule(
        "derivation.codex-exec-v0.field-projection",
        FIELD_RULE_BYTES,
    );
    let record_zero_digest = raw_record_digest_v0(record_zero);
    let run_hash = framed_sha256(
        RUN_ID_DOMAIN_V0,
        &[record_zero_digest.as_bytes(), thread_id.as_bytes()],
    );
    let run_id = format!("run-{}", &run_hash["sha256:".len()..]);
    let events = records
        .iter()
        .zip(raw_records)
        .enumerate()
        .map(|(index, (record, raw))| {
            map_event(
                index,
                record,
                raw,
                record_zero,
                &run_id,
                &event_rule,
                &position_rule,
                &field_rule,
            )
        })
        .collect::<AdapterResultV0<Vec<_>>>()?;
    let trace = TrajectoryTraceV0 {
        schema: trajectory_schema_binding_v0(),
        run_id: derived(run_id, &run_rule, locator(0, record_zero)),
        adapter: codex_exec_adapter_binding_v0(),
        policy: downstream_policy.clone(),
        raw_capture: raw_capture.clone(),
        events,
    };
    let allowed_derivations = BTreeSet::from([run_rule, event_rule, position_rule, field_rule]);
    let validation_declarations = TrajectoryValidationContextV0 {
        adapter: codex_exec_adapter_binding_v0(),
        policy: downstream_policy.clone(),
        raw_capture: raw_capture.clone(),
        allowed_derivations,
    };
    Ok(MappedV0 {
        trace,
        validation_declarations,
    })
}

#[allow(clippy::too_many_arguments)]
fn map_event(
    index: usize,
    record: &ParsedRecordV0,
    raw: &[u8],
    record_zero: &[u8],
    run_id: &str,
    event_rule: &ArtifactBindingV0,
    position_rule: &ArtifactBindingV0,
    field_rule: &ArtifactBindingV0,
) -> AdapterResultV0<AgentActionEventV0> {
    let source = locator(index, raw);
    let record_zero_source = locator(0, record_zero);
    let raw_digest = raw_record_digest_v0(raw);
    let index_bytes = (index as u64).to_be_bytes();
    let event_hash = framed_sha256(
        EVENT_ID_DOMAIN_V0,
        &[run_id.as_bytes(), &index_bytes, raw_digest.as_bytes()],
    );
    let event_id = format!("event-{}", &event_hash["sha256:".len()..]);
    let mut payload = BTreeMap::new();
    add_string(
        &mut payload,
        "source-event",
        source_event(record),
        field_rule,
        &source,
    );
    if let ParsedRecordV0::ThreadStarted { thread_id } = record {
        add_string(
            &mut payload,
            "observed-thread-id",
            thread_id,
            field_rule,
            &source,
        );
    }
    if let ParsedRecordV0::TurnCompleted { usage } = record {
        add_integer(
            &mut payload,
            "input-tokens",
            usage.input_tokens,
            field_rule,
            &source,
        );
        add_integer(
            &mut payload,
            "cached-input-tokens",
            usage.cached_input_tokens,
            field_rule,
            &source,
        );
        add_integer(
            &mut payload,
            "output-tokens",
            usage.output_tokens,
            field_rule,
            &source,
        );
        add_integer(
            &mut payload,
            "reasoning-output-tokens",
            usage.reasoning_output_tokens,
            field_rule,
            &source,
        );
        add_string(
            &mut payload,
            "usage-projection",
            "emitter-total-or-zero-default",
            field_rule,
            &source,
        );
    }
    let source_item_id = if let ParsedRecordV0::Item { lifecycle, item } = record {
        add_string(
            &mut payload,
            "source-item-type",
            item_type(item),
            field_rule,
            &source,
        );
        add_string(
            &mut payload,
            "source-lifecycle",
            lifecycle_label(*lifecycle),
            field_rule,
            &source,
        );
        add_item_payload(&mut payload, item, field_rule, &source);
        Some(derived(item.id().to_string(), field_rule, source.clone()))
    } else {
        None
    };
    Ok(AgentActionEventV0 {
        event_id: derived_from(
            event_id,
            event_rule,
            if index == 0 {
                vec![record_zero_source]
            } else {
                vec![record_zero_source, source.clone()]
            },
        ),
        sequence_index: derived(index as u64, position_rule, source.clone()),
        kind: derived(normalized_kind(record, index)?, field_rule, source.clone()),
        source_item_id,
        raw_record: RawRecordReferenceV0 {
            record_index: index as u64,
            digest: raw_digest,
        },
        payload,
    })
}

fn add_item_payload(
    payload: &mut BTreeMap<String, EvidencedV0<NormalizedValueV0>>,
    item: &ItemV0,
    rule: &ArtifactBindingV0,
    source: &SourceLocatorV0,
) {
    match item {
        ItemV0::Command {
            exit_code, status, ..
        } => {
            add_string(
                payload,
                "source-status",
                command_status(*status),
                rule,
                source,
            );
            let value = exit_code.map_or(NormalizedValueV0::Null, |value| {
                NormalizedValueV0::Integer(value.to_string())
            });
            payload.insert(
                "exit-code".to_string(),
                derived(value, rule, source.clone()),
            );
        }
        ItemV0::FileChange {
            changes, status, ..
        } => {
            add_string(payload, "source-status", file_status(*status), rule, source);
            payload.insert(
                "change-count".to_string(),
                derived(
                    NormalizedValueV0::Integer(changes.len().to_string()),
                    rule,
                    source.clone(),
                ),
            );
            payload.insert(
                "change-kinds".to_string(),
                derived(
                    NormalizedValueV0::Array(
                        changes
                            .iter()
                            .map(|change| {
                                NormalizedValueV0::String(
                                    match change.kind {
                                        ChangeKindV0::Add => "add",
                                        ChangeKindV0::Delete => "delete",
                                        ChangeKindV0::Update => "update",
                                    }
                                    .to_string(),
                                )
                            })
                            .collect(),
                    ),
                    rule,
                    source.clone(),
                ),
            );
        }
        ItemV0::TodoList { items, .. } => {
            payload.insert(
                "todo-completed".to_string(),
                derived(
                    NormalizedValueV0::Array(
                        items
                            .iter()
                            .map(|item| NormalizedValueV0::Boolean(item.completed))
                            .collect(),
                    ),
                    rule,
                    source.clone(),
                ),
            );
        }
        ItemV0::AgentMessage { .. } | ItemV0::Reasoning { .. } | ItemV0::Error { .. } => {}
    }
}

fn normalized_kind(
    record: &ParsedRecordV0,
    index: usize,
) -> AdapterResultV0<NormalizedEventKindV0> {
    let kind = match record {
        ParsedRecordV0::ThreadStarted { .. }
        | ParsedRecordV0::TurnStarted
        | ParsedRecordV0::TurnCompleted { .. }
        | ParsedRecordV0::TurnFailed { .. }
        | ParsedRecordV0::Item {
            item: ItemV0::TodoList { .. },
            ..
        } => NormalizedEventKindV0::Lifecycle,
        ParsedRecordV0::Error { .. } => NormalizedEventKindV0::Observation,
        ParsedRecordV0::Item {
            lifecycle: LifecycleV0::Completed,
            item: ItemV0::Error { .. },
        } => NormalizedEventKindV0::Observation,
        ParsedRecordV0::Item {
            lifecycle: LifecycleV0::Completed,
            item: ItemV0::AgentMessage { .. } | ItemV0::Reasoning { .. },
        } => NormalizedEventKindV0::Message,
        ParsedRecordV0::Item {
            lifecycle: LifecycleV0::Started,
            item: ItemV0::Command { .. } | ItemV0::FileChange { .. },
        } => NormalizedEventKindV0::ActionRequest,
        ParsedRecordV0::Item {
            lifecycle: LifecycleV0::Completed,
            item: ItemV0::Command { .. } | ItemV0::FileChange { .. },
        } => NormalizedEventKindV0::ActionResult,
        ParsedRecordV0::Item { .. } => return Err(mapping_record(index, "$.item")),
    };
    Ok(kind)
}

fn source_event(record: &ParsedRecordV0) -> &'static str {
    match record {
        ParsedRecordV0::ThreadStarted { .. } => "thread.started",
        ParsedRecordV0::TurnStarted => "turn.started",
        ParsedRecordV0::TurnCompleted { .. } => "turn.completed",
        ParsedRecordV0::TurnFailed { .. } => "turn.failed",
        ParsedRecordV0::Error { .. } => "error",
        ParsedRecordV0::Item {
            lifecycle: LifecycleV0::Started,
            ..
        } => "item.started",
        ParsedRecordV0::Item {
            lifecycle: LifecycleV0::Updated,
            ..
        } => "item.updated",
        ParsedRecordV0::Item {
            lifecycle: LifecycleV0::Completed,
            ..
        } => "item.completed",
    }
}

fn item_type(item: &ItemV0) -> &'static str {
    match item {
        ItemV0::AgentMessage { .. } => "agent-message",
        ItemV0::Reasoning { .. } => "reasoning-summary",
        ItemV0::Error { .. } => "item-error-projection",
        ItemV0::Command { .. } => "command-execution",
        ItemV0::FileChange { .. } => "file-change",
        ItemV0::TodoList { .. } => "todo-list",
    }
}

fn lifecycle_label(value: LifecycleV0) -> &'static str {
    match value {
        LifecycleV0::Started => "started",
        LifecycleV0::Updated => "updated",
        LifecycleV0::Completed => "completed",
    }
}

fn command_status(value: CommandStatusV0) -> &'static str {
    match value {
        CommandStatusV0::InProgress => "in-progress",
        CommandStatusV0::Completed => "completed",
        CommandStatusV0::Failed => "failed",
        CommandStatusV0::Declined => "declined",
    }
}

fn file_status(value: FileStatusV0) -> &'static str {
    match value {
        FileStatusV0::InProgress => "in-progress",
        FileStatusV0::Completed => "completed",
        FileStatusV0::Failed => "failed-or-declined-projection",
    }
}

fn add_string(
    payload: &mut BTreeMap<String, EvidencedV0<NormalizedValueV0>>,
    key: &str,
    value: &str,
    rule: &ArtifactBindingV0,
    source: &SourceLocatorV0,
) {
    payload.insert(
        key.to_string(),
        derived(
            NormalizedValueV0::String(value.to_string()),
            rule,
            source.clone(),
        ),
    );
}

fn add_integer(
    payload: &mut BTreeMap<String, EvidencedV0<NormalizedValueV0>>,
    key: &str,
    value: i64,
    rule: &ArtifactBindingV0,
    source: &SourceLocatorV0,
) {
    payload.insert(
        key.to_string(),
        derived(
            NormalizedValueV0::Integer(value.to_string()),
            rule,
            source.clone(),
        ),
    );
}

fn derived<T>(value: T, rule: &ArtifactBindingV0, source: SourceLocatorV0) -> EvidencedV0<T> {
    derived_from(value, rule, vec![source])
}

fn derived_from<T>(
    value: T,
    rule: &ArtifactBindingV0,
    source_inputs: Vec<SourceLocatorV0>,
) -> EvidencedV0<T> {
    EvidencedV0 {
        value: Some(value),
        evidence: EvidenceV0::DeclaredDerivationBinding {
            rule: rule.clone(),
            source_inputs,
        },
    }
}

fn locator(index: usize, raw: &[u8]) -> SourceLocatorV0 {
    SourceLocatorV0 {
        record_index: index as u64,
        byte_offset: 0,
        byte_length: raw.len() as u64,
        digest: source_locator_digest_v0(raw),
    }
}

fn rule(identity: &str, bytes: &[u8]) -> ArtifactBindingV0 {
    ArtifactBindingV0 {
        identity: identity.to_string(),
        version: "0".to_string(),
        hash: artifact_digest_v0(bytes),
    }
}

fn mapping_record(index: usize, path: &'static str) -> AdapterErrorV0 {
    AdapterErrorV0::record(AdapterErrorCodeV0::Mapping, index, path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trajectory::codex_exec_v0::{
        FixedSyntheticTestNonceV0, SyntheticFixtureReceiptV0, codex_exec_fixture_spec_binding_v0,
    };

    const THREAD_RAW: &[u8] =
        br#"{"type":"thread.started","thread_id":"00000000-0000-7000-8000-000000000010"}"#;
    const TURN_RAW: &[u8] = br#"{"type":"turn.started"}"#;
    const ILLEGAL_ITEM_RAW: &[u8] =
        br#"{"type":"item.started","item":{"id":"item_0","type":"agent_message","text":"x"}}"#;

    #[test]
    fn mapping_rejects_empty_and_unequal_inputs_with_exact_diagnostics() {
        let (authority, context) = authority_and_context();

        assert_mapping_error(map_records(&[], &[], &authority, &context), None, None);

        let thread = thread_started();
        assert_mapping_error(
            map_records(std::slice::from_ref(&thread), &[], &authority, &context),
            Some(0),
            Some("$"),
        );
        assert_mapping_error(
            map_records(&[], &[THREAD_RAW], &authority, &context),
            Some(0),
            Some("$"),
        );
    }

    #[test]
    fn mapping_rejects_non_thread_first_record_with_exact_diagnostic() {
        let (authority, context) = authority_and_context();
        assert_mapping_error(
            map_records(
                &[ParsedRecordV0::TurnStarted],
                &[TURN_RAW],
                &authority,
                &context,
            ),
            Some(0),
            Some("$.type"),
        );
    }

    #[test]
    fn mapping_rejects_unmappable_item_lifecycle_with_exact_diagnostic() {
        let (authority, context) = authority_and_context();
        let records = [
            thread_started(),
            ParsedRecordV0::Item {
                lifecycle: LifecycleV0::Started,
                item: ItemV0::AgentMessage {
                    id: "item_0".to_string(),
                    text: "x".to_string(),
                },
            },
        ];
        assert_mapping_error(
            map_records(
                &records,
                &[THREAD_RAW, ILLEGAL_ITEM_RAW],
                &authority,
                &context,
            ),
            Some(1),
            Some("$.item"),
        );
    }

    fn thread_started() -> ParsedRecordV0 {
        ParsedRecordV0::ThreadStarted {
            thread_id: "00000000-0000-7000-8000-000000000010".to_string(),
        }
    }

    fn authority_and_context() -> (InputAuthorityReceiptV0, TrustedAdaptationContextV0) {
        let mut jsonl = THREAD_RAW.to_vec();
        jsonl.push(b'\n');
        let receipt = SyntheticFixtureReceiptV0::new_with_fixed_test_nonce(
            &jsonl,
            codex_exec_fixture_spec_binding_v0(),
            FixedSyntheticTestNonceV0::new([0x61; 32]),
        )
        .unwrap();
        let authority = InputAuthorityReceiptV0::SyntheticFixture(receipt);
        let context = TrustedAdaptationContextV0::new(
            authority.commitment(),
            ArtifactBindingV0 {
                identity: "policy.mapping-test".to_string(),
                version: "0".to_string(),
                hash: artifact_digest_v0(b"mapping-test"),
            },
        )
        .unwrap();
        (authority, context)
    }

    fn assert_mapping_error(
        result: AdapterResultV0<MappedV0>,
        record_index: Option<u64>,
        structural_path: Option<&'static str>,
    ) {
        let error = result.err().expect("mapping must reject the input");
        assert_eq!(error.code(), AdapterErrorCodeV0::Mapping);
        assert_eq!(error.record_index(), record_index);
        assert_eq!(error.structural_path(), structural_path);
    }
}
