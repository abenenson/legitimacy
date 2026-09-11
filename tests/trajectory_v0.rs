use legitimacy::{
    AgentActionEventV0, ArtifactBindingV0, EvidenceV0, EvidencedV0, NormalizedEventKindV0,
    NormalizedValueV0, RawRecordReferenceV0, SourceLocatorV0, TrajectoryTraceV0,
    TrajectoryValidationContextV0, artifact_digest_v0, raw_capture_seal_v0, raw_record_digest_v0,
    source_locator_digest_v0, trajectory_digest_v0, trajectory_schema_binding_v0,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

const RECORD_ZERO: &[u8] =
    br#"{"timestamp":"2099-01-02T00:00:00Z","id":"source-a","kind":"request","command":"inspect"}"#;
const RECORD_ONE: &[u8] =
    br#"{"timestamp":"1999-01-02T00:00:00Z","id":"source-a","kind":"result","status":"ok"}"#;

#[path = "trajectory_v0/duplicate_scanner.rs"]
mod duplicate_scanner;
#[path = "trajectory_v0/evidence_semantics.rs"]
mod evidence_semantics;
#[path = "trajectory_v0/interchange_bounds.rs"]
mod interchange_bounds;
#[path = "trajectory_v0/resource_budgets.rs"]
mod resource_budgets;
#[path = "trajectory_v0/schema_portability.rs"]
mod schema_portability;

#[test]
fn rejects_unknown_normalized_fields_event_kinds_and_duplicate_json_keys() {
    let raw = vec![RECORD_ZERO];
    let (trace, _) = fixture(&raw);
    let mut encoded = serde_json::to_value(&trace).unwrap();
    encoded["events"][0]["semantic_surprise"] = json!(true);
    assert_parse_error(&encoded, "unknown field");

    let mut encoded = serde_json::to_value(&trace).unwrap();
    encoded["events"][0]["kind"]["value"] = json!("vendor-specific-secret");
    assert_parse_error(&encoded, "unknown variant");

    let duplicate = br#"{
        "schema":{"identity":"a","identity":"b","version":"0","hash":"sha256:0000000000000000000000000000000000000000000000000000000000000000"},
        "run_id":null,
        "adapter":null,
        "policy":null,
        "raw_capture":null,
        "events":[]
    }"#;
    let error = TrajectoryTraceV0::from_json_slice(duplicate)
        .expect_err("duplicate keys must fail before semantic decoding");
    assert!(error.to_string().contains("duplicate JSON object key"));
}

#[test]
fn rejects_missing_or_unavailable_load_bearing_evidence() {
    let raw = vec![RECORD_ZERO];
    let (mut trace, declarations) = fixture(&raw);
    trace.events[0].kind.value = None;
    assert_validation_error(&trace, &raw, &declarations, "missing a normalized value");

    let (mut trace, declarations) = fixture(&raw);
    trace.events[0].payload.get_mut("command").unwrap().evidence = EvidenceV0::Unavailable {
        reason: "not emitted".to_string(),
    };
    trace.events[0].payload.get_mut("command").unwrap().value = None;
    assert_validation_error(&trace, &raw, &declarations, "unavailable evidence");

    let (trace, _) = fixture(&raw);
    let mut encoded = serde_json::to_value(&trace).unwrap();
    encoded["events"][0]["event_id"]
        .as_object_mut()
        .unwrap()
        .remove("value");
    assert_parse_error(&encoded, "missing field `value`");
}

#[test]
fn rejects_missing_and_duplicate_identities_and_noncontiguous_order() {
    let raw = vec![RECORD_ZERO, RECORD_ONE];
    let (mut trace, declarations) = fixture(&raw);
    trace.events[1].event_id.value = trace.events[0].event_id.value.clone();
    assert_validation_error(&trace, &raw, &declarations, "duplicate event identity");

    let (mut trace, declarations) = fixture(&raw);
    trace.run_id.value = Some(String::new());
    assert_validation_error(&trace, &raw, &declarations, "run_id must be");

    let (trace, _) = fixture(&raw);
    let mut encoded = serde_json::to_value(&trace).unwrap();
    encoded.as_object_mut().unwrap().remove("run_id");
    assert_parse_error(&encoded, "missing field `run_id`");

    let mut encoded = serde_json::to_value(&trace).unwrap();
    encoded["events"][0]
        .as_object_mut()
        .unwrap()
        .remove("event_id");
    assert_parse_error(&encoded, "missing field `event_id`");

    let encoded = serde_json::to_string(&trace).unwrap();
    let duplicate_run_id = format!(
        "{{\"run_id\":{},{}",
        serde_json::to_string(&trace.run_id).unwrap(),
        &encoded[1..]
    );
    let error = TrajectoryTraceV0::from_json_slice(duplicate_run_id.as_bytes())
        .expect_err("duplicate run identity fields must be rejected");
    assert!(error.to_string().contains("duplicate JSON object key"));

    let mut encoded = serde_json::to_value(&trace).unwrap();
    encoded["events"][0]
        .as_object_mut()
        .unwrap()
        .remove("sequence_index");
    assert_parse_error(&encoded, "missing field `sequence_index`");

    let (mut trace, declarations) = fixture(&raw);
    trace.events[1].sequence_index.value = Some(2);
    assert_validation_error(
        &trace,
        &raw,
        &declarations,
        "not contiguous source position 1",
    );

    let (mut trace, declarations) = fixture(&raw);
    trace.events.remove(0);
    assert_validation_error(
        &trace,
        &raw,
        &declarations,
        "each sealed raw record must have exactly one normalized event",
    );
}

#[test]
fn identity_profile_rejects_sentinels_and_spoofing_at_exact_boundaries() {
    let raw = vec![RECORD_ZERO];
    let (mut trace, declarations) = fixture(&raw);

    for invalid in [
        "",
        " ",
        " unknown",
        "unknown",
        "unknown ",
        "run\nid",
        "run\u{202e}id",
        "run\u{200d}id",
        "rún",
        "А",
    ] {
        trace.run_id.value = Some(invalid.to_string());
        assert_validation_error(
            &trace,
            &raw,
            &declarations,
            "printable ASCII identity profile",
        );
    }

    for valid in ["unknown-1", "A", "run:vendor/item@host+attempt_1"] {
        trace.run_id.value = Some(valid.to_string());
        trace.validate(&raw, &declarations).unwrap();
    }

    trace.run_id.value = Some(format!("A{}", "a".repeat(127)));
    trace.validate(&raw, &declarations).unwrap();
    trace.run_id.value = Some(format!("A{}", "a".repeat(128)));
    assert_validation_error(&trace, &raw, &declarations, "identifier byte limit of 128");
}

#[test]
fn occurrence_ids_remain_unique_while_source_item_ids_may_recur() {
    let raw = vec![RECORD_ZERO, RECORD_ONE];
    let (trace, declarations) = fixture(&raw);
    trace.validate(&raw, &declarations).unwrap();

    assert_ne!(
        trace.events[0].event_id.value,
        trace.events[1].event_id.value
    );
    assert_eq!(
        trace.events[0].source_item_id.as_ref().unwrap().value,
        trace.events[1].source_item_id.as_ref().unwrap().value
    );
}

#[test]
fn rejects_raw_references_outside_sealed_bytes_and_digest_mismatches() {
    let raw = vec![RECORD_ZERO];
    let (mut trace, declarations) = fixture(&raw);
    trace.events[0].raw_record.record_index = 1;
    assert_validation_error(
        &trace,
        &raw,
        &declarations,
        "does not match source position",
    );

    let (mut trace, declarations) = fixture(&raw);
    trace.events[0].raw_record.digest =
        "sha256:0000000000000000000000000000000000000000000000000000000000000000".to_string();
    assert_validation_error(
        &trace,
        &raw,
        &declarations,
        "raw-record digest does not match",
    );

    let (mut trace, declarations) = fixture(&raw);
    let locator = match &mut trace.events[0].event_id.evidence {
        EvidenceV0::CitesRawRange { locator } => locator,
        _ => unreachable!(),
    };
    locator.byte_offset = RECORD_ZERO.len() as u64;
    locator.byte_length = 1;
    assert_validation_error(&trace, &raw, &declarations, "outside the sealed record");

    let (mut trace, declarations) = fixture(&raw);
    let locator = match &mut trace.events[0].kind.evidence {
        EvidenceV0::CitesRawRange { locator } => locator,
        _ => unreachable!(),
    };
    locator.digest =
        "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".to_string();
    assert_validation_error(
        &trace,
        &raw,
        &declarations,
        "does not match the sealed bytes",
    );

    let (trace, declarations) = fixture(&raw);
    let mutated = vec![br#"{"timestamp":"changed"}"#.as_slice()];
    assert_validation_error(
        &trace,
        &mutated,
        &declarations,
        "sealed raw capture bytes or record count",
    );

    let duplicate_key_raw = vec![br#"{"kind":"request","kind":"result"}"#.as_slice()];
    let (trace, declarations) = fixture(&duplicate_key_raw);
    assert_validation_error(
        &trace,
        &duplicate_key_raw,
        &declarations,
        "duplicate JSON object key",
    );
}

#[test]
fn declared_seal_rejects_explicit_tail_truncation_and_record_reordering() {
    let raw = vec![RECORD_ZERO, RECORD_ONE];
    let (trace, declarations) = fixture(&raw);

    let truncated = vec![RECORD_ZERO];
    assert_validation_error(
        &trace,
        &truncated,
        &declarations,
        "sealed raw capture bytes or record count",
    );

    let reordered = vec![RECORD_ONE, RECORD_ZERO];
    assert_validation_error(
        &trace,
        &reordered,
        &declarations,
        "sealed raw capture bytes or record count",
    );
}

#[test]
fn repeated_identical_locators_are_charged_once_and_validate() {
    let record = large_json_record(128 * 1024);
    let raw = vec![record.as_slice()];
    let (mut trace, declarations) = fixture(&raw);
    let shared_locator = locator(&raw, 0);
    trace.events[0].payload = (0..256)
        .map(|index| {
            (
                format!("field-{index:03}"),
                cited(
                    NormalizedValueV0::String("same citation".to_string()),
                    shared_locator.clone(),
                ),
            )
        })
        .collect();

    trace.validate(&raw, &declarations).unwrap();
    assert!(
        shared_locator.byte_length * 256 > legitimacy::trajectory::MAX_DISTINCT_CITED_BYTES_V0,
        "the fixture would fail if repeated ranges were charged repeatedly"
    );
}

#[test]
fn distinct_overlapping_locators_hit_the_cited_byte_budget_before_hashing() {
    let record = large_json_record(legitimacy::trajectory::MAX_RAW_RECORD_BYTES_V0);
    let raw = vec![record.as_slice()];
    let (mut trace, declarations) = fixture(&raw);
    let full_length = record.len() as u64;
    let claimed_digest = source_locator_digest_v0(b"budget check happens before locator hashing");
    let evidence = |byte_offset| EvidenceV0::CitesRawRange {
        locator: SourceLocatorV0 {
            record_index: 0,
            byte_offset,
            byte_length: full_length - 1,
            digest: claimed_digest.clone(),
        },
    };
    trace.events[0].payload.insert(
        "overlap-a".to_string(),
        EvidencedV0 {
            value: Some(NormalizedValueV0::String("a".to_string())),
            evidence: evidence(0),
        },
    );
    trace.events[0].payload.insert(
        "overlap-b".to_string(),
        EvidencedV0 {
            value: Some(NormalizedValueV0::String("b".to_string())),
            evidence: evidence(1),
        },
    );

    assert_validation_error(
        &trace,
        &raw,
        &declarations,
        "distinct cited bytes exceed v0 limit",
    );
}

#[test]
fn hostile_cardinality_depth_and_input_sizes_fail_closed() {
    let raw = vec![RECORD_ZERO];
    let (trace, declarations) = fixture(&raw);

    let oversized_json =
        vec![b' '; legitimacy::trajectory::MAX_TRACE_JSON_INPUT_BYTES_V0.saturating_add(1)];
    let error = TrajectoryTraceV0::from_json_slice(&oversized_json).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("trace JSON input exceeds v0 byte limit")
    );

    let too_many_raw = vec![b"{}".as_slice(); legitimacy::trajectory::MAX_RAW_RECORDS_V0 + 1];
    assert_validation_error(
        &trace,
        &too_many_raw,
        &declarations,
        "raw record count exceeds v0 limit",
    );

    let oversized_record = large_json_record(legitimacy::trajectory::MAX_RAW_RECORD_BYTES_V0 + 1);
    assert_validation_error(
        &trace,
        &[oversized_record.as_slice()],
        &declarations,
        "per-record limit",
    );

    let max_record = large_json_record(legitimacy::trajectory::MAX_RAW_RECORD_BYTES_V0);
    let oversized_capture = vec![max_record.as_slice(); 9];
    assert_validation_error(
        &trace,
        &oversized_capture,
        &declarations,
        "raw capture bytes exceed v0 limit",
    );

    let (mut excessive_events, declarations) = fixture(&raw);
    excessive_events.events =
        vec![excessive_events.events[0].clone(); legitimacy::trajectory::MAX_EVENTS_V0 + 1];
    assert_validation_error(
        &excessive_events,
        &raw,
        &declarations,
        "event count exceeds v0 limit",
    );

    let (mut excessive_fields, declarations) = fixture(&raw);
    let field = excessive_fields.events[0].payload["command"].clone();
    excessive_fields.events[0].payload = (0
        ..=legitimacy::trajectory::MAX_PAYLOAD_FIELDS_PER_OBJECT_V0)
        .map(|index| (format!("field-{index:03}"), field.clone()))
        .collect();
    assert_validation_error(
        &excessive_fields,
        &raw,
        &declarations,
        "payload field count exceeds v0 per-object limit",
    );

    let (mut excessive_depth, declarations) = fixture(&raw);
    let mut nested = NormalizedValueV0::Null;
    for _ in 0..legitimacy::trajectory::MAX_NORMALIZED_DEPTH_V0 {
        nested = NormalizedValueV0::Array(vec![nested]);
    }
    excessive_depth.events[0]
        .payload
        .get_mut("command")
        .unwrap()
        .value = Some(nested);
    assert_validation_error(
        &excessive_depth,
        &raw,
        &declarations,
        "normalized value depth exceeds v0 limit",
    );

    let (mut excessive_inputs, declarations) = fixture(&raw);
    let rule = declarations
        .allowed_derivations
        .iter()
        .next()
        .unwrap()
        .clone();
    excessive_inputs.events[0].sequence_index.evidence = EvidenceV0::DeclaredDerivationBinding {
        rule,
        source_inputs: vec![locator(&raw, 0); legitimacy::trajectory::MAX_DERIVATION_INPUTS_V0 + 1],
    };
    assert_validation_error(
        &excessive_inputs,
        &raw,
        &declarations,
        "derivation source input count exceeds v0 limit",
    );
}

#[test]
fn hostile_total_node_and_evidence_locator_counts_fail_closed() {
    let raw = vec![RECORD_ZERO];
    let (mut excessive_nodes, declarations) = fixture(&raw);
    let evidence = excessive_nodes.events[0].payload["command"]
        .evidence
        .clone();
    excessive_nodes.events[0].payload = (0..100)
        .map(|index| {
            (
                format!("node-{index:03}"),
                EvidencedV0 {
                    value: Some(NormalizedValueV0::Array(vec![
                        NormalizedValueV0::Null;
                        legitimacy::trajectory::MAX_NORMALIZED_ARRAY_ITEMS_V0
                    ])),
                    evidence: evidence.clone(),
                },
            )
        })
        .collect();
    assert_validation_error(
        &excessive_nodes,
        &raw,
        &declarations,
        "normalized node count exceeds v0 limit",
    );

    let (mut excessive_locators, declarations) = fixture(&raw);
    let rule = declarations
        .allowed_derivations
        .iter()
        .next()
        .unwrap()
        .clone();
    let repeated_inputs = vec![locator(&raw, 0); legitimacy::trajectory::MAX_DERIVATION_INPUTS_V0];
    excessive_locators.events[0].payload = (0..99)
        .map(|index| {
            (
                format!("locator-{index:03}"),
                EvidencedV0 {
                    value: Some(NormalizedValueV0::String("bounded".to_string())),
                    evidence: EvidenceV0::DeclaredDerivationBinding {
                        rule: rule.clone(),
                        source_inputs: repeated_inputs.clone(),
                    },
                },
            )
        })
        .collect();
    assert_validation_error(
        &excessive_locators,
        &raw,
        &declarations,
        "evidence locator count exceeds v0 limit",
    );
}

#[test]
fn timestamps_do_not_determine_declared_sequence_order() {
    let raw = vec![RECORD_ZERO, RECORD_ONE];
    let (trace, declarations) = fixture(&raw);
    trace.validate(&raw, &declarations).unwrap();

    assert_eq!(trace.events[0].sequence_index.value, Some(0));
    assert_eq!(trace.events[1].sequence_index.value, Some(1));
    assert!(
        std::str::from_utf8(raw[0]).unwrap().contains("2099"),
        "first source position intentionally has the later timestamp"
    );
    assert!(
        std::str::from_utf8(raw[1]).unwrap().contains("1999"),
        "second source position intentionally has the earlier timestamp"
    );
}

#[test]
fn v0_has_no_speculative_distributed_authority_fields() {
    let schema: Value =
        serde_json::from_slice(legitimacy::trajectory::TRAJECTORY_SCHEMA_BYTES_V0).unwrap();
    let top_level_properties = schema["properties"]
        .as_object()
        .unwrap()
        .keys()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        top_level_properties,
        BTreeSet::from([
            "adapter",
            "events",
            "policy",
            "raw_capture",
            "run_id",
            "schema",
        ])
    );
    let event_properties = schema["$defs"]["event"]["properties"]
        .as_object()
        .unwrap()
        .keys()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        event_properties,
        BTreeSet::from([
            "event_id",
            "kind",
            "payload",
            "raw_record",
            "sequence_index",
            "source_item_id",
        ])
    );

    let raw = vec![RECORD_ZERO];
    let (trace, declarations) = fixture(&raw);
    trace.validate(&raw, &declarations).unwrap();
    let encoded = serde_json::to_string(&trace).unwrap();

    for forbidden in [
        "shard",
        "happened_before",
        "principal",
        "capability",
        "delegation",
        "lease",
    ] {
        assert!(
            !encoded.contains(forbidden),
            "v0 unexpectedly requires {forbidden}"
        );
    }
}

#[test]
fn schema_and_typed_surface_share_the_tested_structural_subset() {
    let schema: Value =
        serde_json::from_slice(legitimacy::trajectory::TRAJECTORY_SCHEMA_BYTES_V0).unwrap();
    assert_eq!(
        schema["x-contract-identity"],
        legitimacy::trajectory::TRAJECTORY_SCHEMA_ID_V0
    );
    assert_eq!(
        schema["x-contract-version"],
        legitimacy::trajectory::TRAJECTORY_SCHEMA_VERSION_V0
    );
    assert_eq!(schema["additionalProperties"], false);
    assert_eq!(schema["$defs"]["event"]["additionalProperties"], false);
    assert_eq!(
        schema["$defs"]["event_kind"]["enum"],
        json!([
            "action-request",
            "action-result",
            "observation",
            "message",
            "lifecycle"
        ])
    );
    assert_eq!(
        schema["$defs"]["normalized_value"]["oneOf"]
            .as_array()
            .unwrap()
            .len(),
        6
    );

    let raw = vec![RECORD_ZERO];
    let (trace, declarations) = fixture(&raw);
    let encoded = serde_json::to_value(&trace).unwrap();
    let required = schema["required"].as_array().unwrap();
    for field in required {
        assert!(encoded.get(field.as_str().unwrap()).is_some());
    }
    let typed = TrajectoryTraceV0::from_json_slice(&serde_json::to_vec(&encoded).unwrap()).unwrap();
    typed.validate(&raw, &declarations).unwrap();

    let mut invalid = encoded;
    invalid.as_object_mut().unwrap().remove("policy");
    assert_parse_error(&invalid, "missing field `policy`");
}

#[test]
fn draft_2020_12_schema_gate_exercises_good_and_bad_wire_mutations() {
    let schema: Value =
        serde_json::from_slice(legitimacy::trajectory::TRAJECTORY_SCHEMA_BYTES_V0).unwrap();
    assert!(
        jsonschema::draft202012::meta::is_valid(&schema),
        "embedded schema must satisfy the Draft 2020-12 meta-schema"
    );
    let validator = jsonschema::draft202012::new(&schema).unwrap();

    let raw = vec![RECORD_ZERO];
    let (trace, _) = fixture(&raw);
    let good = serde_json::to_value(&trace).unwrap();
    assert_schema_and_serde(&validator, &good, true);

    let mut missing_required = good.clone();
    missing_required.as_object_mut().unwrap().remove("policy");
    assert_schema_and_serde(&validator, &missing_required, false);

    let mut unknown_field = good.clone();
    unknown_field["events"][0]["unexpected"] = json!(true);
    assert_schema_and_serde(&validator, &unknown_field, false);

    let mut null_binding = good.clone();
    null_binding["adapter"] = Value::Null;
    assert_schema_and_serde(&validator, &null_binding, false);

    let evidence = good["events"][0]["payload"]["command"]["evidence"].clone();
    let mut all_values = good.clone();
    all_values["events"][0]["payload"] = json!({
        "array": {"value": {"type": "array", "value": [
            {"type": "null"},
            {"type": "boolean", "value": true}
        ]}, "evidence": evidence},
        "boolean": {"value": {"type": "boolean", "value": false}, "evidence": evidence},
        "integer": {"value": {"type": "integer", "value": "-42"}, "evidence": evidence},
        "null": {"value": {"type": "null"}, "evidence": evidence},
        "object": {"value": {"type": "object", "value": {
            "inner-a": {"type": "string", "value": "a"},
            "inner-z": {"type": "integer", "value": "9"}
        }}, "evidence": evidence},
        "string": {"value": {"type": "string", "value": "text"}, "evidence": evidence}
    });
    assert_schema_and_serde(&validator, &all_values, true);

    let mut record_count_boundary = good.clone();
    record_count_boundary["raw_capture"]["record_count"] = json!(10_000_u64);
    assert_schema_and_serde(&validator, &record_count_boundary, true);
    record_count_boundary["raw_capture"]["record_count"] = json!(10_001_u64);
    assert!(!validator.is_valid(&record_count_boundary));
    assert!(
        TrajectoryTraceV0::from_json_slice(&serde_json::to_vec(&record_count_boundary).unwrap())
            .is_ok(),
        "typed construction is intentionally followed by runtime budget validation"
    );
}

#[test]
fn schema_patterns_and_runtime_reject_all_trailing_terminators() {
    let schema: Value =
        serde_json::from_slice(legitimacy::trajectory::TRAJECTORY_SCHEMA_BYTES_V0).unwrap();
    let validator = jsonschema::draft202012::new(&schema).unwrap();
    let raw = vec![RECORD_ZERO];
    let (trace, declarations) = fixture(&raw);
    let good = serde_json::to_value(&trace).unwrap();

    for terminator in ['\n', '\r', '\u{2028}', '\u{2029}'] {
        let mut mutated = good.clone();
        mutated["run_id"]["value"] = json!(format!("run-id{terminator}"));
        assert!(!validator.is_valid(&mutated));
        let decoded =
            TrajectoryTraceV0::from_json_slice(&serde_json::to_vec(&mutated).unwrap()).unwrap();
        assert_validation_error(
            &decoded,
            &raw,
            &declarations,
            "printable ASCII identity profile",
        );

        let mut mutated = good.clone();
        mutated["schema"]["hash"] = json!(format!("{}{terminator}", trace.schema.hash));
        assert!(!validator.is_valid(&mutated));
        let decoded =
            TrajectoryTraceV0::from_json_slice(&serde_json::to_vec(&mutated).unwrap()).unwrap();
        assert_validation_error(&decoded, &raw, &declarations, "schema hash");

        let mut mutated = good.clone();
        mutated["events"][0]["payload"]["command"]["value"] =
            json!({"type": "integer", "value": format!("1{terminator}")});
        assert!(!validator.is_valid(&mutated));
        let decoded =
            TrajectoryTraceV0::from_json_slice(&serde_json::to_vec(&mutated).unwrap()).unwrap();
        assert_validation_error(&decoded, &raw, &declarations, "canonical base-10");
    }
}

#[test]
fn canonical_encoding_sorts_multi_key_payloads_and_nested_objects() {
    let raw = vec![RECORD_ZERO];
    let (mut trace, declarations) = fixture(&raw);
    let evidence = trace.events[0].payload["command"].evidence.clone();
    let nested = NormalizedValueV0::Object(BTreeMap::from([
        (
            "inner-z".to_string(),
            NormalizedValueV0::String("last".to_string()),
        ),
        (
            "inner-a".to_string(),
            NormalizedValueV0::String("first".to_string()),
        ),
    ]));
    trace.events[0].payload = BTreeMap::from([
        (
            "outer-z".to_string(),
            EvidencedV0 {
                value: Some(NormalizedValueV0::Boolean(true)),
                evidence: evidence.clone(),
            },
        ),
        (
            "outer-a".to_string(),
            EvidencedV0 {
                value: Some(nested),
                evidence,
            },
        ),
    ]);

    let canonical = trace
        .validate(&raw, &declarations)
        .unwrap()
        .canonical_bytes();
    assert!(
        framed_string_position(&canonical, "outer-a")
            < framed_string_position(&canonical, "outer-z")
    );
    assert!(
        framed_string_position(&canonical, "inner-a")
            < framed_string_position(&canonical, "inner-z")
    );
}

#[test]
fn canonical_integer_spellings_and_digit_boundaries_are_enforced() {
    let raw = vec![RECORD_ZERO];
    let (mut trace, declarations) = fixture(&raw);

    for valid in ["0", "1", "-1"] {
        trace.events[0].payload.get_mut("command").unwrap().value =
            Some(NormalizedValueV0::Integer(valid.to_string()));
        trace.validate(&raw, &declarations).unwrap();
    }
    trace.events[0].payload.get_mut("command").unwrap().value =
        Some(NormalizedValueV0::Integer("1".repeat(1024)));
    trace.validate(&raw, &declarations).unwrap();

    for invalid in ["-0", "00", "01", "-01", "+1", "1.0", "1e0"] {
        trace.events[0].payload.get_mut("command").unwrap().value =
            Some(NormalizedValueV0::Integer(invalid.to_string()));
        assert_validation_error(
            &trace,
            &raw,
            &declarations,
            "canonical base-10 with no leading zero",
        );
    }
    trace.events[0].payload.get_mut("command").unwrap().value =
        Some(NormalizedValueV0::Integer("1".repeat(1025)));
    assert_validation_error(&trace, &raw, &declarations, "digit limit of 1024");
}

#[test]
fn canonical_bytes_and_hash_preimages_are_pinned() {
    let raw = vec![RECORD_ZERO];
    let (trace, declarations) = fixture(&raw);
    let validated = trace.validate(&raw, &declarations).unwrap();

    assert_eq!(
        trajectory_schema_binding_v0().hash,
        "sha256:8f5fe4d99ac420ef108f1c126ff3a9ce13d68ffb591433b3134f997e29a9eec9"
    );
    assert_eq!(
        raw_record_digest_v0(RECORD_ZERO),
        "sha256:51f23fc0b7d39b94f7eb9da8d6910e6545a6b1afb4682099371112161cc0ffb9"
    );
    assert_eq!(
        source_locator_digest_v0(RECORD_ZERO),
        "sha256:daf63c3dce2aa4f01dd2b2bef24513d6f41a73dad0e580f5e312cfc6a9835dc5"
    );
    assert_eq!(
        raw_capture_seal_v0(&raw).digest,
        "sha256:2de8dd11c75f908a5a212e3977860ca14d7700c13b93cda27eb4b2020ef883a3"
    );
    assert_eq!(
        trajectory_digest_v0(&validated),
        "sha256:d78b05bb308a904f6a68fc766b88ffe25e045c3f69459f3ff52004da1954ebd0"
    );
    assert_eq!(
        format!("sha256:{:x}", Sha256::digest(validated.canonical_bytes())),
        "sha256:c755e43d25349523d6ead9bc0c4f2eba67b68da5059295d3e200304c5b4f9196"
    );
}

fn framed_string_position(bytes: &[u8], value: &str) -> usize {
    let mut framed = (value.len() as u64).to_be_bytes().to_vec();
    framed.extend_from_slice(value.as_bytes());
    bytes
        .windows(framed.len())
        .position(|window| window == framed)
        .expect("framed string must occur in canonical bytes")
}

fn assert_schema_and_serde(validator: &jsonschema::Validator, value: &Value, expected_valid: bool) {
    assert_eq!(
        validator.is_valid(value),
        expected_valid,
        "unexpected Draft 2020-12 result for {value}"
    );
    assert_eq!(
        TrajectoryTraceV0::from_json_slice(&serde_json::to_vec(value).unwrap()).is_ok(),
        expected_valid,
        "unexpected typed decoding result for {value}"
    );
}

fn large_json_record(byte_length: usize) -> Vec<u8> {
    assert!(byte_length >= 2);
    let mut record = vec![b' '; byte_length];
    record[0] = b'{';
    record[byte_length - 1] = b'}';
    record
}

fn fixture(raw: &[&[u8]]) -> (TrajectoryTraceV0, TrajectoryValidationContextV0) {
    let adapter = binding("adapter.synthetic-json", "0.1.0", b"synthetic adapter");
    let policy = binding("policy.synthetic", "7", b"synthetic policy");
    let sequence_rule = binding(
        "derivation.source-record-position",
        "1",
        b"sequence := zero-based raw record position",
    );
    let capture = raw_capture_seal_v0(raw);
    let events = raw
        .iter()
        .enumerate()
        .map(|(index, record)| {
            let source = locator(raw, index);
            AgentActionEventV0 {
                event_id: cited(format!("event-{index}"), source.clone()),
                sequence_index: EvidencedV0 {
                    value: Some(index as u64),
                    evidence: EvidenceV0::DeclaredDerivationBinding {
                        rule: sequence_rule.clone(),
                        source_inputs: vec![source.clone()],
                    },
                },
                kind: cited(
                    if index == 0 {
                        NormalizedEventKindV0::ActionRequest
                    } else {
                        NormalizedEventKindV0::ActionResult
                    },
                    source.clone(),
                ),
                source_item_id: Some(cited("source-a".to_string(), source.clone())),
                raw_record: RawRecordReferenceV0 {
                    record_index: index as u64,
                    digest: raw_record_digest_v0(record),
                },
                payload: BTreeMap::from([(
                    if index == 0 { "command" } else { "status" }.to_string(),
                    cited(
                        NormalizedValueV0::String(
                            if index == 0 { "inspect" } else { "ok" }.to_string(),
                        ),
                        source,
                    ),
                )]),
            }
        })
        .collect();
    let trace = TrajectoryTraceV0 {
        schema: trajectory_schema_binding_v0(),
        run_id: cited("run-sterile-1".to_string(), locator(raw, 0)),
        adapter: adapter.clone(),
        policy: policy.clone(),
        raw_capture: capture.clone(),
        events,
    };
    let declarations = TrajectoryValidationContextV0 {
        adapter,
        policy,
        raw_capture: capture,
        allowed_derivations: BTreeSet::from([sequence_rule]),
    };
    (trace, declarations)
}

fn binding(identity: &str, version: &str, bytes: &[u8]) -> ArtifactBindingV0 {
    ArtifactBindingV0 {
        identity: identity.to_string(),
        version: version.to_string(),
        hash: artifact_digest_v0(bytes),
    }
}

fn locator(raw: &[&[u8]], index: usize) -> SourceLocatorV0 {
    SourceLocatorV0 {
        record_index: index as u64,
        byte_offset: 0,
        byte_length: raw[index].len() as u64,
        digest: source_locator_digest_v0(raw[index]),
    }
}

fn cited<T>(value: T, locator: SourceLocatorV0) -> EvidencedV0<T> {
    EvidencedV0 {
        value: Some(value),
        evidence: EvidenceV0::CitesRawRange { locator },
    }
}

fn assert_validation_error(
    trace: &TrajectoryTraceV0,
    raw: &[&[u8]],
    declarations: &TrajectoryValidationContextV0,
    expected: &str,
) {
    let error = trace
        .validate(raw, declarations)
        .expect_err("fixture should be rejected");
    assert!(
        error.to_string().contains(expected),
        "expected '{expected}', got '{error}'"
    );
}

fn assert_parse_error(value: &Value, expected: &str) {
    let error = TrajectoryTraceV0::from_json_slice(&serde_json::to_vec(value).unwrap())
        .expect_err("fixture should not decode");
    assert!(
        error.to_string().contains(expected),
        "expected '{expected}', got '{error}'"
    );
}
