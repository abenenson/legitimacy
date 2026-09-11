use super::*;
use legitimacy::trajectory::codex_exec_v0::{
    InspectedPrivateAdapterBundleV0, sanitize_capture_v0, sanitize_capture_with_fixed_test_nonce_v0,
};

#[test]
fn production_and_fixed_test_nonces_have_disjoint_honest_labels() {
    let first = InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new(COMPLETED, codex_exec_fixture_spec_binding_v0()).unwrap(),
    );
    let first_json = serde_json::to_value(&first).unwrap();
    assert_eq!(first_json["asserted_nonce_source"], "capture-random");
    assert_ne!(first_json["blinding_nonce_lower_hex"], "00".repeat(32));

    let fixed = synthetic_authority(COMPLETED);
    let fixed_json = serde_json::to_value(&fixed).unwrap();
    assert_eq!(fixed_json["asserted_nonce_source"], "fixed-synthetic-test");
    assert_eq!(fixed_json["blinding_nonce_lower_hex"], "42".repeat(32));

    let sanitized = sanitize_capture_with_fixed_test_nonce_v0(
        COMPLETED,
        &fixed,
        &trusted(&fixed),
        fixed_sanitization_material(0x55),
    )
    .unwrap();
    let derived_json = serde_json::to_value(sanitized.authority()).unwrap();
    assert_eq!(
        derived_json["asserted_nonce_source"],
        "fixed-synthetic-test"
    );
    assert_eq!(derived_json["blinding_nonce_lower_hex"], "55".repeat(32));

    let mut forged_genuine_origin = derived_json;
    forged_genuine_origin["asserted_origin_evidence_class"] =
        serde_json::json!("genuine-process-capture");
    assert!(
        InputAuthorityReceiptV0::from_json_slice(
            &serde_json::to_vec(&forged_genuine_origin).unwrap()
        )
        .is_err()
    );
}

#[test]
fn public_debug_and_error_formatting_redact_private_material() {
    let authority = InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new(COMPLETED, codex_exec_fixture_spec_binding_v0()).unwrap(),
    );
    let context = trusted(&authority);
    let authority_json = serde_json::to_value(&authority).unwrap();
    let nonce = authority_json["blinding_nonce_lower_hex"].as_str().unwrap();
    let raw_digest = authority_json["raw_capture_seal"]["digest"]
        .as_str()
        .unwrap();
    let adapted = adapt_codex_exec_v0(COMPLETED, &authority, &context).unwrap();
    let private = adapted.to_private_bundle().unwrap();
    let private_bytes = private.to_json_line().unwrap();
    let inspected = InspectedPrivateAdapterBundleV0::from_json_slice(&private_bytes).unwrap();
    let revalidated = inspected
        .revalidate(COMPLETED, &authority, &context)
        .unwrap();
    let sanitized = sanitize_capture_v0(COMPLETED, &authority, &context).unwrap();
    let sanitized_debug = format!("{sanitized:?}");
    let receipt_debug = format!("{:?}", sanitized.private_receipt());
    let (sidecar, shareable) = sanitized.into_publication_pair().unwrap();
    let sidecar_debug = format!("{sidecar:?}");
    let sidecar_bytes = sidecar.into_bytes();
    let shareable_bytes = shareable.to_json_line().unwrap();

    for formatted in [
        format!("{authority:?}"),
        format!("{context:?}"),
        format!("{adapted:?}"),
        format!("{private:?}"),
        format!("{revalidated:?}"),
        sanitized_debug,
        receipt_debug,
        sidecar_debug,
        format!("{shareable:?}"),
    ] {
        assert!(!formatted.contains("synthetic response"));
        assert!(!formatted.contains("synthetic-command"));
        assert!(!formatted.contains(nonce));
        assert!(!formatted.contains(raw_digest));
        assert!(!formatted.contains("sha256:"));
    }

    let shareable_text = String::from_utf8(shareable_bytes).unwrap();
    let private_value: serde_json::Value = serde_json::from_slice(&private_bytes).unwrap();
    let original_parent_commitment = authority.commitment();
    let full_parent_digest = authority_json["full_jsonl_digest"].as_str().unwrap();
    let parent_trace_digest = private_value["trajectory_digest"].as_str().unwrap();
    for private_digest in [
        original_parent_commitment.as_str(),
        raw_digest,
        full_parent_digest,
        parent_trace_digest,
    ] {
        assert!(!shareable_text.contains(private_digest));
    }
    let original_offset = sidecar_bytes
        .windows(original_parent_commitment.len())
        .rposition(|window| window == original_parent_commitment.as_bytes())
        .unwrap();
    let nonce_start = original_offset + original_parent_commitment.len();
    let reblinding_nonce = &sidecar_bytes[nonce_start..nonce_start + 32];
    let reblinding_nonce_hex = reblinding_nonce
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    assert!(!shareable_text.contains(&reblinding_nonce_hex));
    assert!(
        !shareable_text
            .as_bytes()
            .windows(reblinding_nonce.len())
            .any(|window| window == reblinding_nonce)
    );
    assert!(
        !shareable_text
            .as_bytes()
            .windows(sidecar_bytes.len())
            .any(|window| window == sidecar_bytes)
    );
    for event in &adapted.trace().events {
        assert!(!shareable_text.contains(&event.raw_record.digest));
        for evidence in [
            &event.event_id.evidence,
            &event.sequence_index.evidence,
            &event.kind.evidence,
        ] {
            if let legitimacy::EvidenceV0::DeclaredDerivationBinding { source_inputs, .. } =
                evidence
            {
                for locator in source_inputs {
                    assert!(!shareable_text.contains(&locator.digest));
                }
            }
        }
    }

    let mut malformed = COMPLETED.to_vec();
    let offset = malformed
        .windows(b"00000000-0000-7000-8000-000000000001".len())
        .position(|window| window == b"00000000-0000-7000-8000-000000000001")
        .unwrap();
    malformed[offset] = b'G';
    let malformed_authority = synthetic_authority(&malformed);
    let error = adapt_codex_exec_v0(
        &malformed,
        &malformed_authority,
        &trusted(&malformed_authority),
    )
    .unwrap_err();
    let private_record_digest =
        legitimacy::raw_record_digest_v0(malformed.split(|byte| *byte == b'\n').next().unwrap());
    for formatted in [format!("{error}"), format!("{error:?}")] {
        assert!(!formatted.contains(&private_record_digest));
        assert!(!formatted.contains("synthetic"));
    }
    malformed[offset + 1] = b'F';
    let other_authority = synthetic_authority(&malformed);
    let other =
        adapt_codex_exec_v0(&malformed, &other_authority, &trusted(&other_authority)).unwrap_err();
    assert_eq!(
        error, other,
        "private digest must not affect error equality"
    );
}
