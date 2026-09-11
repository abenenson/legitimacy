use super::bundle::{AdaptedCodexExecV0, adapt, adapt_framed};
use super::error::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0};
use super::event::{ItemV0, LifecycleV0, ParsedRecordV0, parse_record};
use super::framing::FramedCaptureV0;
use super::receipt::{
    DerivedReceiptInputsV0, InputAuthorityReceiptV0, SanitizedDerivedCaptureReceiptV0,
    TrustedAdaptationContextV0,
};
use super::receipt::{FixedSyntheticTestNonceV0, nonce::NonceMaterialV0};
use super::{
    CODEX_EXEC_SANITIZED_THREAD_ID_DOMAIN_V0, codex_exec_sanitizer_binding_v0,
    codex_exec_sanitizer_policy_binding_v0,
};
use serde_json::{Map, Value};
use std::collections::BTreeMap;
use std::fmt;

#[path = "sanitizer_jwt.rs"]
mod jwt;
use jwt::contains_jwt_like;

pub(super) struct SanitizedCaptureV0 {
    pub(super) adapted: AdaptedCodexExecV0,
    pub(super) authority: InputAuthorityReceiptV0,
    pub(super) derived_context: TrustedAdaptationContextV0,
}

pub struct FixedTestSanitizationMaterialV0 {
    derived_capture_nonce: FixedSyntheticTestNonceV0,
    publication_parent_reblinding_nonce: FixedSyntheticTestNonceV0,
}

pub struct FixedTestSanitizedCaptureV0 {
    sanitized: SanitizedCaptureV0,
}

impl fmt::Debug for SanitizedCaptureV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("SanitizedCaptureV0 { <redacted> }")
    }
}

impl fmt::Debug for FixedTestSanitizationMaterialV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("FixedTestSanitizationMaterialV0 { <redacted> }")
    }
}

impl fmt::Debug for FixedTestSanitizedCaptureV0 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("FixedTestSanitizedCaptureV0 { <redacted> }")
    }
}

impl FixedTestSanitizationMaterialV0 {
    pub const fn new(
        derived_capture_nonce: FixedSyntheticTestNonceV0,
        publication_parent_reblinding_nonce: FixedSyntheticTestNonceV0,
    ) -> Self {
        Self {
            derived_capture_nonce,
            publication_parent_reblinding_nonce,
        }
    }
}

pub fn sanitize_capture_with_fixed_test_nonce_v0(
    parent_jsonl: &[u8],
    parent_authority: &InputAuthorityReceiptV0,
    parent_trusted_context: &TrustedAdaptationContextV0,
    material: FixedTestSanitizationMaterialV0,
) -> AdapterResultV0<FixedTestSanitizedCaptureV0> {
    if parent_authority.evidence_class() != "synthetic-fixture" {
        return Err(AdapterErrorV0::new(
            AdapterErrorCodeV0::UnsupportedAuthority,
        ));
    }
    if material.derived_capture_nonce.bytes()
        == material.publication_parent_reblinding_nonce.bytes()
    {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::EntropyUnavailable));
    }
    let sanitized = sanitize_capture_inner(
        parent_jsonl,
        parent_authority,
        parent_trusted_context,
        material.derived_capture_nonce.into_material(),
        |_| {},
    )?;
    Ok(FixedTestSanitizedCaptureV0 { sanitized })
}

pub(super) fn sanitize_capture_with_nonce_v0(
    parent_jsonl: &[u8],
    parent_authority: &InputAuthorityReceiptV0,
    parent_trusted_context: &TrustedAdaptationContextV0,
    nonce: NonceMaterialV0,
) -> AdapterResultV0<SanitizedCaptureV0> {
    sanitize_capture_inner(
        parent_jsonl,
        parent_authority,
        parent_trusted_context,
        nonce,
        |_| {},
    )
}

fn sanitize_capture_inner(
    parent_jsonl: &[u8],
    parent_authority: &InputAuthorityReceiptV0,
    parent_trusted_context: &TrustedAdaptationContextV0,
    nonce: NonceMaterialV0,
    mutate_after_rewrite: impl FnOnce(&mut Vec<u8>),
) -> AdapterResultV0<SanitizedCaptureV0> {
    if !matches!(
        parent_authority.evidence_class(),
        "synthetic-fixture" | "genuine-process-capture"
    ) {
        return Err(AdapterErrorV0::new(
            AdapterErrorCodeV0::UnsupportedAuthority,
        ));
    }
    let parent = adapt(parent_jsonl, parent_authority, parent_trusted_context)?;
    let raw_records = parent.capture.record_slices();
    let parsed = raw_records
        .iter()
        .enumerate()
        .map(|(index, record)| parse_record(record, index))
        .collect::<AdapterResultV0<Vec<_>>>()?;

    let sanitized_thread_id = sanitized_thread_id(&nonce)?;
    let mut pseudonyms = PseudonymsV0::default();
    let mut output = Vec::with_capacity(parent_jsonl.len());
    for (index, (raw, record)) in raw_records.iter().zip(&parsed).enumerate() {
        let mut value: Value = serde_json::from_slice(raw)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::JsonSyntax))?;
        sanitize_record(&mut value, record, &sanitized_thread_id, &mut pseudonyms)?;
        serde_json::to_writer(&mut output, &value)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?;
        output.push(b' ');
        output.push(b'\n');
        if output.len() > super::MAX_CODEX_JSONL_BYTES_V0 {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::InputTooLarge));
        }
        let _ = index;
    }
    mutate_after_rewrite(&mut output);
    scan_public_child_jsonl(&output)?;
    let derived = FramedCaptureV0::parse_owned(output)?;
    let private_receipt = SanitizedDerivedCaptureReceiptV0::new(
        DerivedReceiptInputsV0 {
            asserted_origin_evidence_class: parent_authority.evidence_class().to_string(),
            asserted_parent_receipt: parent_authority.asserted_parent_receipt()?,
            parent_receipt_commitment: parent_authority.commitment(),
            parent_full_jsonl_length: parent.jsonl().len() as u64,
            parent_full_jsonl_digest: parent.capture.full_digest(),
            parent_raw_capture_seal: parent_authority.raw_seal().clone(),
            sanitizer_policy: codex_exec_sanitizer_policy_binding_v0(),
            sanitizer_artifact: codex_exec_sanitizer_binding_v0(),
        },
        &derived,
        nonce,
    );
    let authority = InputAuthorityReceiptV0::SanitizedDerivedCapture(private_receipt);
    scan_public_child_jsonl(&derived.bytes)?;
    let derived_context = TrustedAdaptationContextV0::new(
        authority.commitment(),
        parent_trusted_context
            .downstream_governance_policy()
            .clone(),
    )?;
    let adapted = adapt_framed(derived, &authority, &derived_context)?;
    Ok(SanitizedCaptureV0 {
        adapted,
        authority,
        derived_context,
    })
}

impl FixedTestSanitizedCaptureV0 {
    pub fn jsonl(&self) -> &[u8] {
        self.sanitized.adapted.jsonl()
    }

    pub fn private_receipt(&self) -> AdapterResultV0<&SanitizedDerivedCaptureReceiptV0> {
        self.sanitized.authority.sanitized_derived_receipt()
    }

    pub fn authority(&self) -> &InputAuthorityReceiptV0 {
        &self.sanitized.authority
    }

    pub fn derived_context(&self) -> &TrustedAdaptationContextV0 {
        &self.sanitized.derived_context
    }

    pub fn adapted(&self) -> &AdaptedCodexExecV0 {
        &self.sanitized.adapted
    }
}

fn sanitized_thread_id(nonce: &NonceMaterialV0) -> AdapterResultV0<String> {
    let digest = crate::trajectory::framed_sha256(
        CODEX_EXEC_SANITIZED_THREAD_ID_DOMAIN_V0,
        &[nonce.asserted_source().label().as_bytes(), nonce.bytes()],
    );
    let digest_bytes = super::receipt::hex::decode_lower_hex(
        digest
            .strip_prefix("sha256:")
            .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?,
    )?;
    let mut uuid = [0u8; 16];
    uuid.copy_from_slice(
        digest_bytes
            .get(..16)
            .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?,
    );
    uuid[6] = (uuid[6] & 0x0f) | 0x70;
    uuid[8] = (uuid[8] & 0x3f) | 0x80;
    Ok(format!(
        "{:02x}{:02x}{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
        uuid[0],
        uuid[1],
        uuid[2],
        uuid[3],
        uuid[4],
        uuid[5],
        uuid[6],
        uuid[7],
        uuid[8],
        uuid[9],
        uuid[10],
        uuid[11],
        uuid[12],
        uuid[13],
        uuid[14],
        uuid[15]
    ))
}

#[derive(Default)]
struct PseudonymsV0 {
    message: PseudonymMapV0,
    reasoning: PseudonymMapV0,
    diagnostic: PseudonymMapV0,
    command: PseudonymMapV0,
    output: PseudonymMapV0,
    path: PseudonymMapV0,
    todo: PseudonymMapV0,
}

#[derive(Default)]
struct PseudonymMapV0 {
    values: BTreeMap<String, String>,
}

impl PseudonymMapV0 {
    fn get(&mut self, value: &str, prefix: &str) -> String {
        if let Some(existing) = self.values.get(value) {
            return existing.clone();
        }
        let placeholder = format!("{prefix}_{:04}", self.values.len());
        self.values.insert(value.to_string(), placeholder.clone());
        placeholder
    }
}

fn sanitize_record(
    value: &mut Value,
    record: &ParsedRecordV0,
    sanitized_thread_id: &str,
    pseudonyms: &mut PseudonymsV0,
) -> AdapterResultV0<()> {
    let object = value
        .as_object_mut()
        .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?;
    match record {
        ParsedRecordV0::ThreadStarted { thread_id } => {
            let _ = thread_id;
            replace(object, "thread_id", sanitized_thread_id.to_string())?
        }
        ParsedRecordV0::TurnFailed { message } => {
            let error = nested_object(object, "error")?;
            replace(
                error,
                "message",
                pseudonyms.diagnostic.get(message, "turn_error"),
            )?;
        }
        ParsedRecordV0::Error { message } => replace(
            object,
            "message",
            pseudonyms.diagnostic.get(message, "stream_error"),
        )?,
        ParsedRecordV0::Item { lifecycle, item } => {
            sanitize_item(nested_object(object, "item")?, *lifecycle, item, pseudonyms)?;
        }
        ParsedRecordV0::TurnStarted | ParsedRecordV0::TurnCompleted { .. } => {}
    }
    Ok(())
}

fn sanitize_item(
    item_object: &mut Map<String, Value>,
    lifecycle: LifecycleV0,
    item: &ItemV0,
    pseudonyms: &mut PseudonymsV0,
) -> AdapterResultV0<()> {
    match item {
        ItemV0::AgentMessage { text, .. } => {
            replace(item_object, "text", pseudonyms.message.get(text, "message"))?
        }
        ItemV0::Reasoning { text, .. } => replace(
            item_object,
            "text",
            pseudonyms.reasoning.get(text, "reasoning_summary"),
        )?,
        ItemV0::Error { message, .. } => replace(
            item_object,
            "message",
            pseudonyms.diagnostic.get(message, "item_error"),
        )?,
        ItemV0::Command {
            command,
            aggregated_output,
            ..
        } => {
            replace(
                item_object,
                "command",
                pseudonyms.command.get(command, "command"),
            )?;
            let output = if lifecycle == LifecycleV0::Started || aggregated_output.is_empty() {
                String::new()
            } else {
                pseudonyms.output.get(aggregated_output, "output")
            };
            replace(item_object, "aggregated_output", output)?;
        }
        ItemV0::FileChange { changes, .. } => {
            let array = item_object
                .get_mut("changes")
                .and_then(Value::as_array_mut)
                .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?;
            for (entry, change) in array.iter_mut().zip(changes) {
                replace(
                    entry.as_object_mut().ok_or_else(|| {
                        AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected)
                    })?,
                    "path",
                    pseudonyms.path.get(&change.path, "path"),
                )?;
            }
            array.sort_by(|left, right| {
                left.get("path")
                    .and_then(Value::as_str)
                    .cmp(&right.get("path").and_then(Value::as_str))
            });
        }
        ItemV0::TodoList { items, .. } => {
            let array = item_object
                .get_mut("items")
                .and_then(Value::as_array_mut)
                .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?;
            for (entry, todo) in array.iter_mut().zip(items) {
                replace(
                    entry.as_object_mut().ok_or_else(|| {
                        AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected)
                    })?,
                    "text",
                    pseudonyms.todo.get(&todo.text, "todo"),
                )?;
            }
        }
    }
    Ok(())
}

fn nested_object<'a>(
    object: &'a mut Map<String, Value>,
    key: &str,
) -> AdapterResultV0<&'a mut Map<String, Value>> {
    object
        .get_mut(key)
        .and_then(Value::as_object_mut)
        .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))
}

fn replace(object: &mut Map<String, Value>, key: &str, value: String) -> AdapterResultV0<()> {
    let slot = object
        .get_mut(key)
        .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?;
    *slot = Value::String(value);
    Ok(())
}

const PUBLIC_SCAN_CHUNK_BYTES_V0: usize = 8 * 1024;
// Structural rewriting and the typed public schema are the primary privacy
// boundary. This bounded byte scan is defense in depth for canaries that
// should never survive onto any serialized public surface.
const PUBLIC_SCAN_MAX_PATTERN_BYTES_V0: usize = 32;
const PUBLIC_SCAN_OVERLAP_BYTES_V0: usize = PUBLIC_SCAN_MAX_PATTERN_BYTES_V0 - 1;
const PUBLIC_SCAN_PATTERNS_V0: &[&[u8]] = &[
    b"bearer ",
    b"api_key",
    b"api-key",
    b"apikey",
    b"access_token",
    b"refresh_token",
    b"client_secret",
    b"private_key",
    b"password",
    b"passwd",
    b"secret=",
    b"session=",
    b"cookie=",
    b"authorization:",
    b"begin private key",
    b"begin rsa private key",
    b"aws_access_key_id",
    b"aws_secret_access_key",
    b"github_pat_",
    b"ghp_",
    b"xoxb-",
    b"xoxp-",
    b"?token=",
    b"&token=",
    b"/home/",
    b"/users/",
    b"user=",
    b"account=",
    b"account_id",
    b"email=",
    b"host=",
    b"hostname=",
    b"env=",
    b"environment=",
    b"\\home\\",
];

#[cfg(test)]
pub(crate) fn scan_public_surface(surfaces: &[&[u8]]) -> AdapterResultV0<()> {
    for surface in surfaces {
        scan_one_public_surface(surface)?;
    }
    Ok(())
}

pub(crate) fn scan_public_child_jsonl(jsonl: &[u8]) -> AdapterResultV0<()> {
    scan_fixed_patterns_and_controls(jsonl)?;
    std::str::from_utf8(jsonl)
        .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?;
    for line in jsonl
        .split(|byte| *byte == b'\n')
        .filter(|line| !line.is_empty())
    {
        let body = line.strip_suffix(b" ").unwrap_or(line);
        let value: Value = serde_json::from_slice(body)
            .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?;
        let object = value
            .as_object()
            .ok_or_else(|| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?;
        let thread_slot = object.get("type").and_then(Value::as_str) == Some("thread.started");
        scan_json_value(&value, thread_slot, None)?;
    }
    Ok(())
}

pub(crate) fn scan_publication_bundle_json(bytes: &[u8]) -> AdapterResultV0<()> {
    scan_fixed_patterns_and_controls(bytes)?;
    let body = bytes.strip_suffix(b"\n").unwrap_or(bytes);
    let value: Value = serde_json::from_slice(body)
        .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?;
    scan_bundle_value(&value, None)
}

fn scan_bundle_value(value: &Value, key: Option<&str>) -> AdapterResultV0<()> {
    match value {
        Value::Object(object) => {
            for (name, child) in object {
                scan_bundle_value(child, Some(name))?;
            }
        }
        Value::Array(array) => {
            for child in array {
                scan_bundle_value(child, key)?;
            }
        }
        Value::String(text) if key == Some("official_trace_json") => {
            let trace: Value = serde_json::from_str(text)
                .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?;
            scan_trace_value(&trace, false, None)?;
        }
        Value::String(text) => scan_text_value(text, false)?,
        Value::Null | Value::Bool(_) | Value::Number(_) => {}
    }
    Ok(())
}

fn scan_trace_value(
    value: &Value,
    observed_thread_slot: bool,
    key: Option<&str>,
) -> AdapterResultV0<()> {
    match value {
        Value::Object(object) => {
            for (name, child) in object {
                scan_trace_value(
                    child,
                    observed_thread_slot || name == "observed-thread-id",
                    Some(name),
                )?;
            }
        }
        Value::Array(array) => {
            for child in array {
                scan_trace_value(child, observed_thread_slot, key)?;
            }
        }
        Value::String(text) => {
            scan_text_value(text, observed_thread_slot && key == Some("value"))?;
        }
        Value::Null | Value::Bool(_) | Value::Number(_) => {}
    }
    Ok(())
}

fn scan_json_value(value: &Value, thread_slot: bool, key: Option<&str>) -> AdapterResultV0<()> {
    match value {
        Value::Object(object) => {
            for (name, child) in object {
                scan_json_value(child, thread_slot, Some(name))?;
            }
        }
        Value::Array(array) => {
            for child in array {
                scan_json_value(child, thread_slot, key)?;
            }
        }
        Value::String(text) => {
            let allow_derived_uuid = thread_slot && key == Some("thread_id");
            scan_text_value(text, allow_derived_uuid)?;
        }
        Value::Null | Value::Bool(_) | Value::Number(_) => {}
    }
    Ok(())
}

fn scan_text_value(text: &str, allow_derived_uuid: bool) -> AdapterResultV0<()> {
    let bytes = text.as_bytes();
    let allowed_uuid = allow_derived_uuid && is_derived_uuid(bytes);
    let rejected = text
        .chars()
        .any(|character| character.is_control() || character.is_whitespace())
        || contains_pattern(bytes)
        || contains_email_like(bytes)
        || contains_ipv4_like(bytes)
        || contains_ipv6_like(text)
        || contains_url_scheme(bytes)
        || contains_access_key_like(bytes)
        || contains_jwt_like(bytes)
        || contains_private_home_path(bytes)
        || (contains_uuid_like(bytes) && !allowed_uuid);
    if rejected {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected));
    }
    Ok(())
}

fn scan_fixed_patterns_and_controls(surface: &[u8]) -> AdapterResultV0<()> {
    let mut carry = [0u8; PUBLIC_SCAN_OVERLAP_BYTES_V0];
    let mut carry_length = 0usize;
    let mut window = [0u8; PUBLIC_SCAN_CHUNK_BYTES_V0 + PUBLIC_SCAN_OVERLAP_BYTES_V0];
    for chunk in surface.chunks(PUBLIC_SCAN_CHUNK_BYTES_V0) {
        if chunk
            .iter()
            .any(|byte| (*byte < 0x20 && *byte != b'\n') || *byte == 0x7f)
        {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected));
        }
        window[..carry_length].copy_from_slice(&carry[..carry_length]);
        for (slot, byte) in window[carry_length..carry_length + chunk.len()]
            .iter_mut()
            .zip(chunk)
        {
            *slot = byte.to_ascii_lowercase();
        }
        let window_length = carry_length + chunk.len();
        let scanned = &window[..window_length];
        if contains_pattern(scanned) {
            return Err(AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected));
        }
        carry_length = PUBLIC_SCAN_OVERLAP_BYTES_V0.min(window_length);
        carry[..carry_length]
            .copy_from_slice(&scanned[window_length - carry_length..window_length]);
    }
    Ok(())
}

#[cfg(test)]
fn scan_one_public_surface(surface: &[u8]) -> AdapterResultV0<()> {
    let text = std::str::from_utf8(surface)
        .map_err(|_| AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected))?;
    scan_fixed_patterns_and_controls(surface)?;
    if contains_email_like(surface)
        || contains_ipv4_like(surface)
        || contains_ipv6_like(text)
        || contains_uuid_like(surface)
        || contains_url_scheme(surface)
        || contains_access_key_like(surface)
        || contains_jwt_like(surface)
        || contains_private_home_path(surface)
        || contains_unexpected_prose(surface)
    {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::SanitizerRejected));
    }
    Ok(())
}

fn contains_pattern(surface: &[u8]) -> bool {
    PUBLIC_SCAN_PATTERNS_V0.iter().any(|pattern| {
        surface
            .windows(pattern.len())
            .any(|part| part.eq_ignore_ascii_case(pattern))
    })
}

fn contains_email_like(surface: &[u8]) -> bool {
    surface.iter().enumerate().any(|(index, byte)| {
        if *byte != b'@' {
            return false;
        }
        let left = surface[..index]
            .iter()
            .rev()
            .take_while(|byte| byte.is_ascii_alphanumeric() || b"._%+-".contains(byte))
            .count();
        let right_length = surface[index + 1..]
            .iter()
            .take_while(|byte| byte.is_ascii_alphanumeric() || **byte == b'.' || **byte == b'-')
            .count();
        let right = &surface[index + 1..index + 1 + right_length];
        left != 0 && !right.is_empty() && right[0].is_ascii_alphanumeric()
    })
}

fn contains_ipv4_like(surface: &[u8]) -> bool {
    let mut start = 0;
    while start < surface.len() {
        if !surface[start].is_ascii_digit() {
            start += 1;
            continue;
        }
        let end = surface[start..]
            .iter()
            .position(|byte| !byte.is_ascii_digit() && *byte != b'.')
            .map_or(surface.len(), |length| start + length);
        let token = &surface[start..end];
        let left_bound = start == 0 || !is_version_token_byte(surface[start - 1]);
        let right_bound = end == surface.len() || !is_version_token_byte(surface[end]);
        if left_bound && right_bound {
            let mut parts = token.split(|byte| *byte == b'.');
            let valid = (&mut parts).take(4).all(|part| {
                !part.is_empty()
                    && part.len() <= 3
                    && part
                        .iter()
                        .try_fold(0_u16, |value, digit| {
                            value
                                .checked_mul(10)
                                .and_then(|value| value.checked_add(u16::from(*digit - b'0')))
                        })
                        .is_some_and(|value| value <= 255)
            });
            if valid
                && token.iter().filter(|byte| **byte == b'.').count() == 3
                && parts.next().is_none()
            {
                return true;
            }
        }
        start = end.max(start + 1);
    }
    false
}

fn is_version_token_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-' | b'_')
}

fn contains_uuid_like(surface: &[u8]) -> bool {
    surface.windows(36).any(is_uuid_shape)
}

fn is_uuid_shape(candidate: &[u8]) -> bool {
    let hyphens = [8, 13, 18, 23];
    candidate.len() == 36
        && candidate.iter().enumerate().all(|(index, byte)| {
            if hyphens.contains(&index) {
                *byte == b'-'
            } else {
                byte.is_ascii_hexdigit()
            }
        })
}

fn is_derived_uuid(candidate: &[u8]) -> bool {
    is_uuid_shape(candidate)
        && candidate[14] == b'7'
        && matches!(
            candidate[19].to_ascii_lowercase(),
            b'8' | b'9' | b'a' | b'b'
        )
}

fn contains_url_scheme(surface: &[u8]) -> bool {
    surface.iter().enumerate().any(|(separator, byte)| {
        if *byte != b':' || separator == 0 {
            return false;
        }
        let start = surface[..separator]
            .iter()
            .rposition(|byte| !byte.is_ascii_alphanumeric() && !b"+.-".contains(byte))
            .map_or(0, |index| index + 1);
        let scheme = &surface[start..separator];
        (2..=16).contains(&scheme.len())
            && scheme[0].is_ascii_alphabetic()
            && scheme
                .iter()
                .all(|byte| byte.is_ascii_alphanumeric() || b"+.-".contains(byte))
            && (surface.get(separator + 1..separator + 3) == Some(b"//")
                || scheme.eq_ignore_ascii_case(b"data")
                || scheme.eq_ignore_ascii_case(b"javascript"))
    })
}

fn contains_access_key_like(surface: &[u8]) -> bool {
    surface
        .split(|byte| !byte.is_ascii_alphanumeric() && !matches!(byte, b'-' | b'_'))
        .any(|token| {
            (token.len() >= 11
                && (token[..3].eq_ignore_ascii_case(b"sk-")
                    || token[..3].eq_ignore_ascii_case(b"sk_"))
                && token[3..]
                    .iter()
                    .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_')))
                || (token.len() == 20
                    && matches!(&token[..4], b"AKIA" | b"ASIA")
                    && token[4..]
                        .iter()
                        .all(|byte| byte.is_ascii_uppercase() || byte.is_ascii_digit()))
        })
}

fn contains_ipv6_like(surface: &str) -> bool {
    surface
        .split(|character: char| {
            !(character.is_ascii_hexdigit() || matches!(character, ':' | '.' | '[' | ']'))
        })
        .filter(|token| token.contains(':'))
        .any(|token| {
            token
                .trim_matches(['[', ']'])
                .parse::<std::net::Ipv6Addr>()
                .is_ok()
        })
}

fn contains_private_home_path(surface: &[u8]) -> bool {
    let lower = surface
        .iter()
        .map(u8::to_ascii_lowercase)
        .collect::<Vec<_>>();
    lower.windows(5).enumerate().any(|(index, window)| {
        window == b"/root" && matches!(lower.get(index + 5), None | Some(b'/'))
    }) || lower.windows(8).any(|window| window == b":\\users\\")
}

#[cfg(test)]
fn contains_unexpected_prose(surface: &[u8]) -> bool {
    let ascii = surface.iter().enumerate().any(|(index, byte)| {
        matches!(*byte, b'\t' | b'\r')
            || (*byte == b' ' && surface.get(index + 1).copied() != Some(b'\n'))
    });
    ascii
        || std::str::from_utf8(surface).is_ok_and(|text| {
            text.chars()
                .any(|character| !character.is_ascii() && character.is_whitespace())
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scanner_is_fixed_chunk_boundary_complete_and_surface_aware() {
        for pattern in PUBLIC_SCAN_PATTERNS_V0 {
            for split in 1..pattern.len() {
                let mut surface = vec![b'x'; PUBLIC_SCAN_CHUNK_BYTES_V0 - split];
                surface.extend_from_slice(pattern);
                assert!(
                    scan_public_surface(&[&surface]).is_err(),
                    "{} split at {split}",
                    String::from_utf8_lossy(pattern)
                );
            }
            let mut staged = b"{\"retained_slot\":\"".to_vec();
            staged.extend_from_slice(pattern);
            staged.extend_from_slice(b"\"}\n");
            assert!(scan_public_surface(&[&staged]).is_err());
        }
        assert!(scan_public_surface(&[b"prefixhttps", b"://separate"]).is_ok());
        assert!(scan_public_surface(&[b"prefixhttps://whole"]).is_err());

        for length in [
            PUBLIC_SCAN_CHUNK_BYTES_V0 - 1,
            PUBLIC_SCAN_CHUNK_BYTES_V0,
            PUBLIC_SCAN_CHUNK_BYTES_V0 + 1,
            super::super::MAX_CODEX_JSONL_BYTES_V0 - 1,
        ] {
            assert!(scan_public_surface(&[&vec![b'x'; length]]).is_ok());
        }
        for control in (0usize..0x20)
            .chain([0x7fusize])
            .filter(|byte| *byte != usize::from(b'\n'))
        {
            assert!(scan_public_surface(&[&[b'x', control as u8, b'y']]).is_err());
        }
    }

    #[test]
    fn scanner_rejects_canaries_in_each_staged_public_component() {
        let staged_components: &[(&str, &[u8])] = &[
            (
                "sanitized child jsonl",
                b"{\"message\":\"Bearer attacker-secret\"}\n",
            ),
            (
                "public derived receipt",
                b"{\"asserted_origin_evidence_class\":\"?token=attacker-secret\"}",
            ),
            (
                "official trace json",
                b"{\"public_summary\":\"cookie=attacker-secret\"}",
            ),
            (
                "bundle policy slot",
                b"{\"downstream_governance_policy\":{\"identity\":\"host=attacker-secret\"}}",
            ),
            (
                "canonical payload slot",
                b"{\"canonical_trace_lower_hex\":\"safe\",\"payload\":\"/home/attacker/private\"}",
            ),
        ];
        for (component, surface) in staged_components {
            let error = scan_public_surface(&[surface]).unwrap_err();
            assert_eq!(
                error.code(),
                AdapterErrorCodeV0::SanitizerRejected,
                "{component}"
            );
        }

        let mut serialized_bundle = b"{\"left\":\"https".to_vec();
        serialized_bundle.extend_from_slice(b"://attacker.invalid\",\"right\":\"safe\"}\n");
        assert_eq!(
            scan_public_surface(&[&serialized_bundle])
                .unwrap_err()
                .code(),
            AdapterErrorCodeV0::SanitizerRejected
        );
        assert!(
            scan_public_surface(&[b"{\"left\":\"https", b"://logically-separate-component\"}"])
                .is_ok()
        );

        for harmless in [
            b"{\"message\":\"public_message_0001\"}\n".as_slice(),
            b"{\"asserted_origin_evidence_class\":\"synthetic-fixture\"}".as_slice(),
            b"{\"public_summary\":\"public_summary_0001\"}".as_slice(),
            b"{\"downstream_governance_policy\":{\"identity\":\"policy.user\"}}".as_slice(),
            b"{\"canonical_trace_lower_hex\":\"73616665\"}".as_slice(),
        ] {
            assert!(scan_public_surface(&[harmless]).is_ok());
        }

        for canary in [
            b"account_42@example.invalid".as_slice(),
            b"network=192.0.2.44".as_slice(),
            b"550e8400-e29b-41d4-a716-446655440000".as_slice(),
            b"client_secret=synthetic-canary".as_slice(),
            b"unexpected retained prose".as_slice(),
            b"C:\\home\\synthetic-user\\capture.jsonl".as_slice(),
        ] {
            assert!(scan_public_surface(&[canary]).is_err());
        }
        assert!(scan_public_surface(&[b"018f47a2-4c32-7a9b-8123-0123456789ab"]).is_err());
        assert!(
            scan_public_child_jsonl(
                b"{\"type\":\"thread.started\",\"thread_id\":\"018f47a2-4c32-7a9b-8123-0123456789ab\"} \n"
            )
            .is_ok()
        );
        assert!(
            scan_public_child_jsonl(
                b"{\"type\":\"item.completed\",\"thread_id\":\"018f47a2-4c32-7a9b-8123-0123456789ab\"} \n"
            )
            .is_err()
        );
    }

    #[test]
    fn hostile_privacy_canary_matrix_is_typed_and_bounded() {
        let rejected = [
            b"550e8400-e29b-41d4-a716-446655440000".as_slice(),
            b"018f47a2-4c32-7a9b-8123-0123456789ab".as_slice(),
            b"account@localhost".as_slice(),
            b"AKIAIOSFODNN7EXAMPLE".as_slice(),
            b"eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.signature0".as_slice(),
            b"ftp://example.invalid/private".as_slice(),
            b"data:text/plain,private".as_slice(),
            b"javascript:private".as_slice(),
            b"e30.e30.c2lnbmF0dXJl".as_slice(),
            b"eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxIn0.c2ln".as_slice(),
            b"sk_live_1234567890".as_slice(),
            b"2001:db8::1".as_slice(),
            b"/root/private/capture.jsonl".as_slice(),
            b"path=/root".as_slice(),
            b"C:\\Users\\alice\\capture.jsonl".as_slice(),
            "retained\u{2003}prose".as_bytes(),
            b"non-text-\x80".as_slice(),
            b"non-text-\xff".as_slice(),
        ];
        for canary in rejected {
            assert!(scan_public_surface(&[canary]).is_err(), "{canary:?}");
        }
        let sha256 = format!("sha256:{}", "a".repeat(64));
        let ed25519_key = format!("ed25519:{}", "b".repeat(64));
        let ed25519_signature = format!("ed25519:{}", "c".repeat(128));
        for benign in [
            b"risk-score".as_slice(),
            b"release-2026.08.30".as_slice(),
            b"v1.20.30-beta".as_slice(),
            b"release-1.2.3.4".as_slice(),
            sha256.as_bytes(),
            ed25519_key.as_bytes(),
            ed25519_signature.as_bytes(),
        ] {
            assert!(scan_public_surface(&[benign]).is_ok(), "{benign:?}");
        }
    }

    #[test]
    fn postcondition_rejects_json_valid_rewrite_that_breaks_stream_state() {
        use crate::trajectory::codex_exec_v0::{
            FixedSyntheticTestNonceV0, SyntheticFixtureReceiptV0,
            codex_exec_fixture_spec_binding_v0,
        };
        use crate::trajectory::{ArtifactBindingV0, artifact_digest_v0};

        let bytes =
            include_bytes!("../../../tests/fixtures/codex-exec-v0/legal-completed.synthetic.jsonl");
        let receipt = SyntheticFixtureReceiptV0::new_with_fixed_test_nonce(
            bytes,
            codex_exec_fixture_spec_binding_v0(),
            FixedSyntheticTestNonceV0::new([0x31; 32]),
        )
        .unwrap();
        let authority = InputAuthorityReceiptV0::SyntheticFixture(receipt);
        let context = TrustedAdaptationContextV0::new(
            authority.commitment(),
            ArtifactBindingV0 {
                identity: "policy.synthetic-downstream".to_string(),
                version: "test".to_string(),
                hash: artifact_digest_v0(b"synthetic"),
            },
        )
        .unwrap();
        let error = sanitize_capture_inner(
            bytes,
            &authority,
            &context,
            FixedSyntheticTestNonceV0::new([0x32; 32]).into_material(),
            |output| {
                let mut lines = output
                    .split_inclusive(|byte| *byte == b'\n')
                    .map(<[u8]>::to_vec)
                    .collect::<Vec<_>>();
                lines.swap(3, 4);
                output.clear();
                output.extend(lines.into_iter().flatten());
            },
        )
        .unwrap_err();
        assert_eq!(error.code(), AdapterErrorCodeV0::StreamState);
    }
}
