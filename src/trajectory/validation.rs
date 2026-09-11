use super::{
    ArtifactBindingV0, EvidenceV0, EvidencedV0, MAX_DERIVATION_INPUTS_V0,
    MAX_DISTINCT_CITED_BYTES_V0, MAX_EVENTS_V0, MAX_EVIDENCE_LOCATORS_V0,
    MAX_EVIDENCE_REASON_BYTES_V0, MAX_IDENTIFIER_BYTES_V0, MAX_INTEGER_DIGITS_V0,
    MAX_NORMALIZED_ARRAY_ITEMS_V0, MAX_NORMALIZED_DEPTH_V0, MAX_NORMALIZED_NODES_V0,
    MAX_NORMALIZED_STRING_BYTES_V0, MAX_NORMALIZED_STRING_SCALARS_V0,
    MAX_PAYLOAD_CONTENT_BYTES_TOTAL_V0, MAX_PAYLOAD_FIELDS_PER_OBJECT_V0,
    MAX_PAYLOAD_FIELDS_TOTAL_V0, MAX_RAW_CAPTURE_BYTES_V0, MAX_RAW_RECORD_BYTES_V0,
    MAX_RAW_RECORDS_V0, NormalizedValueV0, SourceLocatorV0, TrajectoryTraceV0,
    TrajectoryValidationContextV0, duplicate_json, interchange, invalid, raw_capture_seal_v0,
    raw_record_digest_v0, source_locator_digest_v0, trajectory_schema_binding_v0,
};
use crate::LegitimacyError;
use std::collections::{BTreeMap, BTreeSet};

type LocatorRange = (u64, u64, u64);

#[derive(Default)]
struct ValidationState {
    locator_digests: BTreeMap<LocatorRange, String>,
    locator_hashes: usize,
}

pub(super) fn validate_trace(
    trace: &TrajectoryTraceV0,
    raw_records: &[&[u8]],
    declarations: &TrajectoryValidationContextV0,
) -> Result<(), LegitimacyError> {
    validate_resource_budget(trace, raw_records, declarations)?;
    interchange::validate_compact_json_size(trace)?;

    validate_binding("schema", &trace.schema)?;
    validate_binding("adapter", &trace.adapter)?;
    validate_binding("policy", &trace.policy)?;
    validate_binding("declared adapter", &declarations.adapter)?;
    validate_binding("declared policy", &declarations.policy)?;
    if trace.schema != trajectory_schema_binding_v0() {
        return invalid("schema identity, version, or hash mismatch");
    }
    if trace.adapter != declarations.adapter {
        return invalid("adapter identity, version, or hash mismatch");
    }
    if trace.policy != declarations.policy {
        return invalid("policy identity, version, or hash mismatch");
    }

    validate_digest("declared raw-capture digest", &trace.raw_capture.digest)?;
    validate_digest(
        "declared raw-capture digest",
        &declarations.raw_capture.digest,
    )?;
    if trace.raw_capture != declarations.raw_capture {
        return invalid("trace raw-capture seal does not match the declared seal");
    }
    for (index, raw_record) in raw_records.iter().enumerate() {
        let root_kind =
            duplicate_json::reject_duplicate_json_keys(raw_record, "sealed raw record")?;
        if root_kind != duplicate_json::JsonRootKind::Object {
            return invalid(format!("raw record {index} must be a JSON object"));
        }
    }
    let actual_seal = raw_capture_seal_v0(raw_records);
    if trace.raw_capture != actual_seal {
        return invalid("sealed raw capture bytes or record count do not match the declaration");
    }

    let mut state = ValidationState::default();
    let run_id = validate_required_field(
        "run_id",
        &trace.run_id,
        raw_records,
        declarations,
        &mut state,
    )?;
    validate_identifier("run_id", run_id)?;

    let mut event_ids = BTreeSet::new();
    for (index, event) in trace.events.iter().enumerate() {
        let expected_index = u64::try_from(index)
            .map_err(|_| LegitimacyError::invalid_input("event count exceeds u64"))?;
        let event_id = validate_required_field(
            "event_id",
            &event.event_id,
            raw_records,
            declarations,
            &mut state,
        )?;
        validate_identifier("event_id", event_id)?;
        if !event_ids.insert(event_id) {
            return invalid(format!("duplicate event identity '{event_id}'"));
        }

        let sequence_index = *validate_required_field(
            "sequence_index",
            &event.sequence_index,
            raw_records,
            declarations,
            &mut state,
        )?;
        if sequence_index != expected_index {
            return invalid(format!(
                "event '{event_id}' sequence index {sequence_index} is not contiguous source position {expected_index}"
            ));
        }
        validate_required_field("kind", &event.kind, raw_records, declarations, &mut state)?;

        if let Some(source_item_id) = &event.source_item_id {
            let value = validate_required_field(
                "source_item_id",
                source_item_id,
                raw_records,
                declarations,
                &mut state,
            )?;
            validate_identifier("source_item_id", value)?;
        }

        if event.raw_record.record_index != expected_index {
            return invalid(format!(
                "event '{event_id}' raw record index {} does not match source position {expected_index}",
                event.raw_record.record_index
            ));
        }
        validate_digest("raw-record digest", &event.raw_record.digest)?;
        if event.raw_record.digest != raw_record_digest_v0(raw_records[index]) {
            return invalid(format!(
                "event '{event_id}' raw-record digest does not match sealed record {index}"
            ));
        }

        for (field_name, field) in &event.payload {
            validate_payload_key(field_name)?;
            let value = validate_required_field(
                &format!("payload.{field_name}"),
                field,
                raw_records,
                declarations,
                &mut state,
            )?;
            validate_normalized_value(value, &format!("payload.{field_name}"))?;
        }
    }
    Ok(())
}

fn validate_resource_budget(
    trace: &TrajectoryTraceV0,
    raw_records: &[&[u8]],
    declarations: &TrajectoryValidationContextV0,
) -> Result<(), LegitimacyError> {
    if raw_records.len() > MAX_RAW_RECORDS_V0 {
        return invalid(format!(
            "raw record count exceeds v0 limit of {MAX_RAW_RECORDS_V0}"
        ));
    }
    if trace.events.len() > MAX_EVENTS_V0 {
        return invalid(format!("event count exceeds v0 limit of {MAX_EVENTS_V0}"));
    }
    let mut raw_capture_bytes = 0usize;
    for record in raw_records {
        if record.len() > MAX_RAW_RECORD_BYTES_V0 {
            return invalid(format!(
                "raw record bytes exceed v0 per-record limit of {MAX_RAW_RECORD_BYTES_V0}"
            ));
        }
        raw_capture_bytes = raw_capture_bytes
            .checked_add(record.len())
            .ok_or_else(|| LegitimacyError::invalid_input("raw capture byte count overflow"))?;
        if raw_capture_bytes > MAX_RAW_CAPTURE_BYTES_V0 {
            return invalid(format!(
                "raw capture bytes exceed v0 limit of {MAX_RAW_CAPTURE_BYTES_V0}"
            ));
        }
    }
    let raw_record_count = u64::try_from(raw_records.len())
        .map_err(|_| LegitimacyError::invalid_input("raw record count exceeds u64"))?;
    if raw_record_count != trace.raw_capture.record_count {
        return invalid("sealed raw capture bytes or record count do not match the declaration");
    }
    if trace.events.is_empty() {
        return invalid("trajectory must contain at least one event");
    }
    if trace.events.len() != raw_records.len() {
        return invalid("each sealed raw record must have exactly one normalized event");
    }

    check_binding_sizes("schema", &trace.schema)?;
    check_binding_sizes("adapter", &trace.adapter)?;
    check_binding_sizes("policy", &trace.policy)?;
    check_binding_sizes("declared adapter", &declarations.adapter)?;
    check_binding_sizes("declared policy", &declarations.policy)?;
    check_short_string(
        "declared raw-capture digest",
        &trace.raw_capture.digest,
        71,
        "digest",
    )?;
    check_short_string(
        "declared raw-capture digest",
        &declarations.raw_capture.digest,
        71,
        "digest",
    )?;

    let mut budget = PayloadBudget::default();
    budget.add_evidence(&trace.run_id.evidence)?;
    check_identifier_size("run_id", trace.run_id.value.as_deref())?;
    for event in &trace.events {
        if event.payload.len() > MAX_PAYLOAD_FIELDS_PER_OBJECT_V0 {
            return invalid(format!(
                "event payload field count exceeds v0 per-object limit of {MAX_PAYLOAD_FIELDS_PER_OBJECT_V0}"
            ));
        }
        budget.add_evidence(&event.event_id.evidence)?;
        budget.add_evidence(&event.sequence_index.evidence)?;
        budget.add_evidence(&event.kind.evidence)?;
        check_short_string("raw-record digest", &event.raw_record.digest, 71, "digest")?;
        check_identifier_size("event_id", event.event_id.value.as_deref())?;
        if let Some(source_item_id) = &event.source_item_id {
            budget.add_evidence(&source_item_id.evidence)?;
            check_identifier_size("source_item_id", source_item_id.value.as_deref())?;
        }
        for (field_name, field) in &event.payload {
            check_short_string("payload field name", field_name, 128, "artifact name")?;
            budget.add_field(field_name.len())?;
            budget.add_evidence(&field.evidence)?;
            if let Some(value) = &field.value {
                budget.add_normalized_value(value, 1)?;
            }
        }
    }
    Ok(())
}

#[derive(Default)]
struct PayloadBudget {
    payload_fields: usize,
    payload_content_bytes: usize,
    normalized_nodes: usize,
    evidence_locators: usize,
    distinct_ranges: BTreeSet<LocatorRange>,
    distinct_cited_bytes: u64,
}

impl PayloadBudget {
    fn add_field(&mut self, key_bytes: usize) -> Result<(), LegitimacyError> {
        self.payload_fields = self
            .payload_fields
            .checked_add(1)
            .ok_or_else(|| LegitimacyError::invalid_input("payload field count overflow"))?;
        if self.payload_fields > MAX_PAYLOAD_FIELDS_TOTAL_V0 {
            return invalid(format!(
                "payload field count exceeds v0 total limit of {MAX_PAYLOAD_FIELDS_TOTAL_V0}"
            ));
        }
        self.add_content_bytes(key_bytes)
    }

    fn add_content_bytes(&mut self, bytes: usize) -> Result<(), LegitimacyError> {
        self.payload_content_bytes = self
            .payload_content_bytes
            .checked_add(bytes)
            .ok_or_else(|| LegitimacyError::invalid_input("payload content byte count overflow"))?;
        if self.payload_content_bytes > MAX_PAYLOAD_CONTENT_BYTES_TOTAL_V0 {
            return invalid(format!(
                "payload content bytes exceed v0 total limit of {MAX_PAYLOAD_CONTENT_BYTES_TOTAL_V0}"
            ));
        }
        Ok(())
    }

    fn add_evidence(&mut self, evidence: &EvidenceV0) -> Result<(), LegitimacyError> {
        match evidence {
            EvidenceV0::CitesRawRange { locator } => self.add_locator(locator),
            EvidenceV0::DeclaredDerivationBinding {
                rule,
                source_inputs,
            } => {
                check_binding_sizes("derivation rule", rule)?;
                if source_inputs.len() > MAX_DERIVATION_INPUTS_V0 {
                    return invalid(format!(
                        "derivation source input count exceeds v0 limit of {MAX_DERIVATION_INPUTS_V0}"
                    ));
                }
                for locator in source_inputs {
                    self.add_locator(locator)?;
                }
                Ok(())
            }
            EvidenceV0::Unavailable { reason } => {
                if reason.len() > MAX_EVIDENCE_REASON_BYTES_V0 {
                    return invalid(format!(
                        "unavailable evidence reason exceeds v0 byte limit of {MAX_EVIDENCE_REASON_BYTES_V0}"
                    ));
                }
                Ok(())
            }
        }
    }

    fn add_locator(&mut self, locator: &SourceLocatorV0) -> Result<(), LegitimacyError> {
        check_short_string("source-locator digest", &locator.digest, 71, "digest")?;
        self.evidence_locators = self
            .evidence_locators
            .checked_add(1)
            .ok_or_else(|| LegitimacyError::invalid_input("evidence locator count overflow"))?;
        if self.evidence_locators > MAX_EVIDENCE_LOCATORS_V0 {
            return invalid(format!(
                "evidence locator count exceeds v0 limit of {MAX_EVIDENCE_LOCATORS_V0}"
            ));
        }

        let range = (
            locator.record_index,
            locator.byte_offset,
            locator.byte_length,
        );
        if self.distinct_ranges.insert(range) {
            self.distinct_cited_bytes = self
                .distinct_cited_bytes
                .checked_add(locator.byte_length)
                .ok_or_else(|| {
                    LegitimacyError::invalid_input("distinct cited byte count overflow")
                })?;
            if self.distinct_cited_bytes > MAX_DISTINCT_CITED_BYTES_V0 {
                return invalid(format!(
                    "distinct cited bytes exceed v0 limit of {MAX_DISTINCT_CITED_BYTES_V0}"
                ));
            }
        }
        Ok(())
    }

    fn add_normalized_value(
        &mut self,
        value: &NormalizedValueV0,
        depth: usize,
    ) -> Result<(), LegitimacyError> {
        if depth > MAX_NORMALIZED_DEPTH_V0 {
            return invalid(format!(
                "normalized value depth exceeds v0 limit of {MAX_NORMALIZED_DEPTH_V0}"
            ));
        }
        self.normalized_nodes = self
            .normalized_nodes
            .checked_add(1)
            .ok_or_else(|| LegitimacyError::invalid_input("normalized node count overflow"))?;
        if self.normalized_nodes > MAX_NORMALIZED_NODES_V0 {
            return invalid(format!(
                "normalized node count exceeds v0 limit of {MAX_NORMALIZED_NODES_V0}"
            ));
        }
        match value {
            NormalizedValueV0::Array(values) => {
                if values.len() > MAX_NORMALIZED_ARRAY_ITEMS_V0 {
                    return invalid(format!(
                        "normalized array size exceeds v0 limit of {MAX_NORMALIZED_ARRAY_ITEMS_V0}"
                    ));
                }
                let child_depth = depth.checked_add(1).ok_or_else(|| {
                    LegitimacyError::invalid_input("normalized value depth overflow")
                })?;
                for value in values {
                    self.add_normalized_value(value, child_depth)?;
                }
            }
            NormalizedValueV0::Object(values) => {
                if values.len() > MAX_PAYLOAD_FIELDS_PER_OBJECT_V0 {
                    return invalid(format!(
                        "normalized object field count exceeds v0 per-object limit of {MAX_PAYLOAD_FIELDS_PER_OBJECT_V0}"
                    ));
                }
                let child_depth = depth.checked_add(1).ok_or_else(|| {
                    LegitimacyError::invalid_input("normalized value depth overflow")
                })?;
                for (field_name, value) in values {
                    check_short_string(
                        "normalized object field name",
                        field_name,
                        128,
                        "artifact name",
                    )?;
                    self.add_field(field_name.len())?;
                    self.add_normalized_value(value, child_depth)?;
                }
            }
            NormalizedValueV0::Integer(value) => {
                if value.len() > MAX_INTEGER_DIGITS_V0 + 1 {
                    return invalid(format!(
                        "normalized integer exceeds v0 digit limit of {MAX_INTEGER_DIGITS_V0}"
                    ));
                }
                self.add_content_bytes(value.len())?;
            }
            NormalizedValueV0::String(value) => {
                if value.len() > MAX_NORMALIZED_STRING_BYTES_V0 {
                    return invalid(format!(
                        "normalized string exceeds v0 byte limit of {MAX_NORMALIZED_STRING_BYTES_V0}"
                    ));
                }
                self.add_content_bytes(value.len())?;
            }
            NormalizedValueV0::Null | NormalizedValueV0::Boolean(_) => {}
        }
        Ok(())
    }
}

fn check_binding_sizes(name: &str, binding: &ArtifactBindingV0) -> Result<(), LegitimacyError> {
    check_short_string(
        &format!("{name} identity"),
        &binding.identity,
        128,
        "artifact binding",
    )?;
    check_short_string(
        &format!("{name} version"),
        &binding.version,
        64,
        "artifact binding",
    )?;
    check_short_string(&format!("{name} hash"), &binding.hash, 71, "digest")
}

fn check_short_string(
    name: &str,
    value: &str,
    max_bytes: usize,
    kind: &str,
) -> Result<(), LegitimacyError> {
    if value.len() > max_bytes {
        return invalid(format!(
            "{name} exceeds v0 {kind} byte limit of {max_bytes}"
        ));
    }
    Ok(())
}

fn check_identifier_size(name: &str, value: Option<&str>) -> Result<(), LegitimacyError> {
    if value.is_some_and(|value| value.len() > MAX_IDENTIFIER_BYTES_V0) {
        return invalid(format!(
            "{name} exceeds v0 identifier byte limit of {MAX_IDENTIFIER_BYTES_V0}"
        ));
    }
    Ok(())
}

fn validate_required_field<'a, T>(
    name: &str,
    field: &'a EvidencedV0<T>,
    raw_records: &[&[u8]],
    declarations: &TrajectoryValidationContextV0,
    state: &mut ValidationState,
) -> Result<&'a T, LegitimacyError> {
    match &field.evidence {
        EvidenceV0::CitesRawRange { locator } => {
            validate_locator(locator, raw_records, state)?;
        }
        EvidenceV0::DeclaredDerivationBinding {
            rule,
            source_inputs,
        } => {
            validate_binding("derivation rule", rule)?;
            if !declarations.allowed_derivations.contains(rule) {
                return invalid(format!(
                    "field '{name}' uses an undeclared derivation rule binding"
                ));
            }
            if source_inputs.is_empty() {
                return invalid(format!(
                    "field '{name}' derivation has no declared source inputs"
                ));
            }
            let mut unique_inputs = BTreeSet::new();
            for locator in source_inputs {
                validate_locator(locator, raw_records, state)?;
                if !unique_inputs.insert((
                    locator.record_index,
                    locator.byte_offset,
                    locator.byte_length,
                )) {
                    return invalid(format!("field '{name}' derivation repeats a source input"));
                }
            }
        }
        EvidenceV0::Unavailable { reason } => {
            if reason.trim().is_empty() {
                return invalid(format!(
                    "field '{name}' unavailable evidence requires a reason"
                ));
            }
            return invalid(format!(
                "load-bearing field '{name}' has unavailable evidence"
            ));
        }
    }
    field.value.as_ref().ok_or_else(|| {
        LegitimacyError::invalid_input(format!(
            "load-bearing field '{name}' is missing a normalized value"
        ))
    })
}

pub(super) fn validate_binding(
    name: &str,
    binding: &ArtifactBindingV0,
) -> Result<(), LegitimacyError> {
    validate_ascii_name(&format!("{name} identity"), &binding.identity)?;
    validate_ascii_version(&format!("{name} version"), &binding.version)?;
    validate_digest(&format!("{name} hash"), &binding.hash)
}

fn validate_ascii_name(name: &str, value: &str) -> Result<(), LegitimacyError> {
    let valid = !value.is_empty()
        && value.len() <= 128
        && value.bytes().enumerate().all(|(index, byte)| match byte {
            b'a'..=b'z' | b'0'..=b'9' => true,
            b'.' | b'-' | b'_' => index > 0,
            _ => false,
        });
    if !valid {
        return invalid(format!(
            "{name} must be 1..128 lowercase ASCII name characters"
        ));
    }
    Ok(())
}

fn validate_ascii_version(name: &str, value: &str) -> Result<(), LegitimacyError> {
    let valid = !value.is_empty()
        && value.len() <= 64
        && value.bytes().all(|byte| {
            matches!(
                byte,
                b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'.' | b'-' | b'_' | b'+'
            )
        });
    if !valid {
        return invalid(format!(
            "{name} must be 1..64 restricted printable ASCII characters"
        ));
    }
    Ok(())
}

pub(super) fn validate_identifier(name: &str, value: &str) -> Result<(), LegitimacyError> {
    let valid = !value.is_empty()
        && value.len() <= MAX_IDENTIFIER_BYTES_V0
        && value != "unknown"
        && value.bytes().enumerate().all(|(index, byte)| match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' => true,
            b'.' | b'_' | b':' | b'@' | b'/' | b'+' | b'-' => index > 0,
            _ => false,
        });
    if !valid {
        return invalid(format!(
            "{name} must be 1..{MAX_IDENTIFIER_BYTES_V0} bytes in the v0 printable ASCII identity profile and must not equal 'unknown'"
        ));
    }
    Ok(())
}

fn validate_payload_key(value: &str) -> Result<(), LegitimacyError> {
    validate_ascii_name("payload field name", value)
}

fn validate_digest(name: &str, value: &str) -> Result<(), LegitimacyError> {
    let Some(hex) = value.strip_prefix("sha256:") else {
        return invalid(format!("{name} must use 'sha256:' spelling"));
    };
    if hex.len() != 64
        || !hex
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return invalid(format!(
            "{name} must contain exactly 64 lowercase hexadecimal digits"
        ));
    }
    Ok(())
}

fn validate_locator(
    locator: &SourceLocatorV0,
    raw_records: &[&[u8]],
    state: &mut ValidationState,
) -> Result<(), LegitimacyError> {
    validate_digest("source-locator digest", &locator.digest)?;
    if locator.byte_length == 0 {
        return invalid("source locator byte_length must be nonzero");
    }
    let range = (
        locator.record_index,
        locator.byte_offset,
        locator.byte_length,
    );
    let actual_digest = if let Some(digest) = state.locator_digests.get(&range) {
        digest
    } else {
        let record_index = usize::try_from(locator.record_index).map_err(|_| {
            LegitimacyError::invalid_input("source locator record index exceeds usize")
        })?;
        let record = raw_records.get(record_index).ok_or_else(|| {
            LegitimacyError::invalid_input(format!(
                "source locator record index {} is outside the sealed capture",
                locator.record_index
            ))
        })?;
        let start = usize::try_from(locator.byte_offset).map_err(|_| {
            LegitimacyError::invalid_input("source locator byte offset exceeds usize")
        })?;
        let length = usize::try_from(locator.byte_length).map_err(|_| {
            LegitimacyError::invalid_input("source locator byte length exceeds usize")
        })?;
        let end = start.checked_add(length).ok_or_else(|| {
            LegitimacyError::invalid_input("source locator byte range overflows usize")
        })?;
        let located = record.get(start..end).ok_or_else(|| {
            LegitimacyError::invalid_input("source locator byte range is outside the sealed record")
        })?;
        let digest = source_locator_digest_v0(located);
        state.locator_hashes = state
            .locator_hashes
            .checked_add(1)
            .ok_or_else(|| LegitimacyError::invalid_input("locator hash count overflow"))?;
        state.locator_digests.entry(range).or_insert(digest)
    };
    if locator.digest != actual_digest.as_str() {
        return invalid("source locator digest does not match the sealed bytes");
    }
    Ok(())
}

fn validate_normalized_value(value: &NormalizedValueV0, path: &str) -> Result<(), LegitimacyError> {
    match value {
        NormalizedValueV0::Integer(value) => {
            let digits = value.strip_prefix('-').unwrap_or(value);
            if digits.len() > MAX_INTEGER_DIGITS_V0 {
                return invalid(format!(
                    "{path} integer exceeds v0 digit limit of {MAX_INTEGER_DIGITS_V0}"
                ));
            }
            if digits.is_empty()
                || !digits.bytes().all(|byte| byte.is_ascii_digit())
                || (digits.len() > 1 && digits.starts_with('0'))
                || value == "-0"
            {
                return invalid(format!(
                    "{path} integer must be canonical base-10 with no leading zero"
                ));
            }
        }
        NormalizedValueV0::String(value) => {
            if value.chars().count() > MAX_NORMALIZED_STRING_SCALARS_V0 {
                return invalid(format!(
                    "{path} string exceeds v0 scalar limit of {MAX_NORMALIZED_STRING_SCALARS_V0}"
                ));
            }
        }
        NormalizedValueV0::Array(values) => {
            for (index, value) in values.iter().enumerate() {
                validate_normalized_value(value, &format!("{path}[{index}]"))?;
            }
        }
        NormalizedValueV0::Object(values) => {
            for (key, value) in values {
                validate_payload_key(key)?;
                validate_normalized_value(value, &format!("{path}.{key}"))?;
            }
        }
        NormalizedValueV0::Null | NormalizedValueV0::Boolean(_) => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_locator_ranges_are_hashed_once_per_validation_state() {
        let raw = br#"{"id":"same-range"}"#;
        let locator = SourceLocatorV0 {
            record_index: 0,
            byte_offset: 0,
            byte_length: raw.len() as u64,
            digest: source_locator_digest_v0(raw),
        };
        let mut state = ValidationState::default();
        for _ in 0..100 {
            validate_locator(&locator, &[raw.as_slice()], &mut state).unwrap();
        }
        assert_eq!(state.locator_hashes, 1);
        assert_eq!(state.locator_digests.len(), 1);
    }
}
