use super::*;
use legitimacy::trajectory::codex_exec_v0::{
    AdapterErrorCodeV0, InspectedPrivateAdapterBundleV0, InspectedShareableSanitizedBundleV0,
    sanitize_capture_v0, sanitize_capture_with_fixed_test_nonce_v0,
};
use legitimacy::{
    EvidenceV0, NormalizedEventKindV0, NormalizedValueV0, ReplayAuthorityErrorCodeV0,
    ReplayAuthoritySigningKeyV0, ReplayAuthorityTrustPolicyV0, UnverifiedReplayAuthorityReceiptV0,
    issue_trajectory_replay_authority_receipt_v0, verify_replay_authority_receipt_v0,
};
use sha2::{Digest, Sha256};

#[test]
fn source_derived_golden_ids_rules_evidence_locators_and_payloads() {
    let authority = synthetic_authority(FAILED);
    let adapted = adapt_codex_exec_v0(FAILED, &authority, &trusted(&authority)).unwrap();
    let validated = adapted.validate().unwrap();
    let compact = validated.to_compact_json().unwrap();
    let canonical = validated.canonical_bytes();
    let private = adapted.to_private_bundle().unwrap().to_json_line().unwrap();
    assert_eq!(compact.len(), 7_319);
    assert_eq!(
        format!("sha256:{:x}", Sha256::digest(&compact)),
        "sha256:0c7761ed7c3752cbb046b668a6060d5696c36164e2f127ab0d22282dad8a2b41"
    );
    assert_eq!(canonical.len(), 5_056);
    assert_eq!(
        format!("sha256:{:x}", Sha256::digest(&canonical)),
        "sha256:c1bebd1b87d4d7293caa5837624104d0d0db02c02591fd093ff8b4ec268b816a"
    );
    assert_eq!(private.len(), 20_850);
    assert_eq!(
        format!("sha256:{:x}", Sha256::digest(&private)),
        "sha256:66dede74f328e22b4f81861599502a5170f22085d906bee64af7010f5e858050"
    );
    let trace = adapted.trace();
    let records = FAILED
        .split(|byte| *byte == b'\n')
        .filter(|record| !record.is_empty())
        .collect::<Vec<_>>();
    let record_digests = records
        .iter()
        .map(|record| independent_framed_hash("legitimacy.trajectory.raw-record.v0", &[record]))
        .collect::<Vec<_>>();
    let locator_digests = records
        .iter()
        .map(|record| independent_framed_hash("legitimacy.trajectory.source-locator.v0", &[record]))
        .collect::<Vec<_>>();
    let expected_run_hash = independent_framed_hash(
        "legitimacy.codex-exec-v0.run-id.v0",
        &[
            record_digests[0].as_bytes(),
            b"00000000-0000-7000-8000-000000000002",
        ],
    );
    let expected_run_id = format!("run-{}", expected_run_hash.strip_prefix("sha256:").unwrap());
    assert_eq!(
        expected_run_id,
        "run-62e124f838db3eb19beb7675a859f5cd189728097c43002fb987d6da902b7b79"
    );
    assert_eq!(
        trace.run_id.value.as_deref(),
        Some(expected_run_id.as_str())
    );

    let expected_event_ids = record_digests
        .iter()
        .enumerate()
        .map(|(index, digest)| {
            let index_bytes = (index as u64).to_be_bytes();
            let hash = independent_framed_hash(
                "legitimacy.codex-exec-v0.event-id.v0",
                &[expected_run_id.as_bytes(), &index_bytes, digest.as_bytes()],
            );
            format!("event-{}", hash.strip_prefix("sha256:").unwrap())
        })
        .collect::<Vec<_>>();
    assert_eq!(
        expected_event_ids,
        [
            "event-42cc669ebb397185c9511d7455615481489776bd26f79e56ac80af557759ad2b",
            "event-d80e9ad8bdcb4ac0deef6543d04e4eb03a05acd456499b3647af4e443ed723a3",
            "event-79c9268ebafdc9beb6611b39829f9523dd9b257b09a52a38d4356c56eb9d28f5",
        ]
    );
    assert_eq!(
        trace
            .events
            .iter()
            .map(|event| event.event_id.value.as_deref().unwrap())
            .collect::<Vec<_>>(),
        expected_event_ids
    );

    let EvidenceV0::DeclaredDerivationBinding {
        rule: run_rule,
        source_inputs: run_inputs,
    } = &trace.run_id.evidence
    else {
        panic!("run id must be derived");
    };
    assert_eq!(
        run_rule.hash,
        independent_framed_hash(
            "legitimacy.trajectory.artifact.v0",
            &[b"run-id := hash(thread-started-whole-record-digest, decoded-canonical-thread-id)"]
        )
    );
    assert_eq!(run_inputs.len(), 1);
    assert_eq!(run_inputs[0].record_index, 0);
    assert_eq!(run_inputs[0].byte_length, records[0].len() as u64);
    assert_eq!(run_inputs[0].digest, locator_digests[0]);

    for (index, event) in trace.events.iter().enumerate() {
        assert_eq!(event.raw_record.digest, record_digests[index]);
        let EvidenceV0::DeclaredDerivationBinding {
            rule,
            source_inputs,
        } = &event.event_id.evidence
        else {
            panic!("event id must be derived");
        };
        assert_eq!(
            rule.hash,
            independent_framed_hash(
                "legitimacy.trajectory.artifact.v0",
                &[b"event-id := hash(normalized-run-id, source-position, whole-raw-record-digest)"]
            )
        );
        assert_eq!(source_inputs[0].record_index, 0);
        assert_eq!(source_inputs[0].digest, locator_digests[0]);
        if index == 0 {
            assert_eq!(source_inputs.len(), 1);
        } else {
            assert_eq!(source_inputs.len(), 2);
            assert_eq!(source_inputs[1].record_index, index as u64);
            assert_eq!(source_inputs[1].digest, locator_digests[index]);
        }
    }
    assert_eq!(
        trace.events[0].payload["observed-thread-id"].value,
        Some(NormalizedValueV0::String(
            "00000000-0000-7000-8000-000000000002".to_string()
        ))
    );
    assert_eq!(
        trace.events[2].payload["source-event"].value,
        Some(NormalizedValueV0::String("turn.failed".to_string()))
    );
}

#[test]
fn source_derived_matrix_maps_one_record_to_one_validated_event() {
    let authority = synthetic_authority(COMPLETED);
    let adapted = adapt_codex_exec_v0(COMPLETED, &authority, &trusted(&authority)).unwrap();
    let validated = adapted.validate().unwrap();
    assert_eq!(adapted.trace().events.len(), 16);
    assert!(!validated.to_compact_json().unwrap().is_empty());

    let source_ids = adapted
        .trace()
        .events
        .iter()
        .filter_map(|event| event.source_item_id.as_ref())
        .map(|id| id.value.as_deref().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        source_ids,
        [
            "item_0", "item_1", "item_1", "item_2", "item_2", "item_3", "item_4", "item_5",
            "item_6", "item_6", "item_6"
        ]
    );
    assert_eq!(
        adapted.trace().events[4].kind.value,
        Some(NormalizedEventKindV0::ActionRequest)
    );
    assert_eq!(
        adapted.trace().events[5].kind.value,
        Some(NormalizedEventKindV0::ActionResult)
    );
    assert!(
        adapted
            .trace()
            .events
            .iter()
            .enumerate()
            .all(|(index, event)| {
                event.sequence_index.value == Some(index as u64)
                    && event.raw_record.record_index == index as u64
            })
    );
}

#[test]
fn repeated_adaptation_and_private_bundle_are_byte_identical() {
    let authority = synthetic_authority(COMPLETED);
    let context = trusted(&authority);
    let first = adapt_codex_exec_v0(COMPLETED, &authority, &context)
        .unwrap()
        .to_private_bundle()
        .unwrap()
        .to_json_line()
        .unwrap();
    let second = adapt_codex_exec_v0(COMPLETED, &authority, &context)
        .unwrap()
        .to_private_bundle()
        .unwrap()
        .to_json_line()
        .unwrap();
    assert_eq!(first, second);
    let inspected = InspectedPrivateAdapterBundleV0::from_json_slice(&first).unwrap();
    inspected
        .revalidate(COMPLETED, &authority, &context)
        .unwrap()
        .validate()
        .unwrap();
}

#[test]
fn trace_policy_is_exactly_the_accepted_caller_binding() {
    let authority = synthetic_authority(COMPLETED);
    let expected = policy_binding();
    let adapted = adapt_codex_exec_v0(
        COMPLETED,
        &authority,
        &TrustedAdaptationContextV0::new(authority.commitment(), expected.clone()).unwrap(),
    )
    .unwrap();
    assert_eq!(adapted.trace().policy, expected);
}

#[test]
fn sanitizer_is_deterministic_and_re_adapts_derived_bytes() {
    let authority = synthetic_authority(COMPLETED);
    let context = trusted(&authority);
    let first = sanitize_capture_with_fixed_test_nonce_v0(
        COMPLETED,
        &authority,
        &context,
        fixed_sanitization_material(0x91),
    )
    .unwrap();
    let second = sanitize_capture_with_fixed_test_nonce_v0(
        COMPLETED,
        &authority,
        &context,
        fixed_sanitization_material(0x91),
    )
    .unwrap();
    assert_eq!(first.jsonl(), second.jsonl());
    assert_eq!(first.private_receipt(), second.private_receipt());
    let sanitized_text = std::str::from_utf8(first.jsonl()).unwrap();
    for secret in [
        "synthetic response",
        "synthetic public summary",
        "synthetic-command",
        "synthetic output",
        "synthetic/a.txt",
        "synthetic first step",
    ] {
        assert!(!sanitized_text.contains(secret));
    }

    let derived_authority = first.authority();
    let derived_context =
        TrustedAdaptationContextV0::new(derived_authority.commitment(), policy_binding()).unwrap();
    let adapted = adapt_codex_exec_v0(first.jsonl(), derived_authority, &derived_context).unwrap();
    adapted.validate().unwrap();
    let second_json = serde_json::to_value(second.authority()).unwrap();
    assert_eq!(second_json["asserted_nonce_source"], "fixed-synthetic-test");
}

#[test]
fn sanitizer_policy_and_implementation_bindings_cannot_substitute() {
    use legitimacy::trajectory::codex_exec_v0::{
        codex_exec_sanitizer_binding_v0, codex_exec_sanitizer_policy_binding_v0,
    };

    let authority = InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new(COMPLETED, codex_exec_fixture_spec_binding_v0()).unwrap(),
    );
    let context = trusted(&authority);
    let sanitized = sanitize_capture_v0(COMPLETED, &authority, &context).unwrap();
    let private: serde_json::Value = serde_json::from_slice(
        &sanitized
            .adapted()
            .to_private_bundle()
            .unwrap()
            .to_json_line()
            .unwrap(),
    )
    .unwrap();
    assert_eq!(
        private["transformation_receipt"]["transformation_policy"],
        serde_json::to_value(codex_exec_sanitizer_policy_binding_v0()).unwrap()
    );

    let (sidecar, bundle) = sanitized.into_publication_pair().unwrap();
    let shareable_bytes = bundle.to_json_line().unwrap();
    let shareable: serde_json::Value = serde_json::from_slice(&shareable_bytes).unwrap();
    let policy = serde_json::to_value(codex_exec_sanitizer_policy_binding_v0()).unwrap();
    let implementation = serde_json::to_value(codex_exec_sanitizer_binding_v0()).unwrap();
    assert_eq!(
        shareable["public_derived_receipt"]["sanitizer_policy"],
        policy
    );
    assert_eq!(
        shareable["public_derived_receipt"]["sanitizer_artifact"],
        implementation
    );
    assert!(
        shareable["public_derived_receipt"]
            .get("asserted_origin_evidence_class")
            .is_none()
    );
    assert!(
        shareable["public_derived_receipt"]
            .get("attested_origin_evidence_class")
            .is_none()
    );
    assert!(shareable.get("parent_receipt_commitment").is_none());
    assert_eq!(
        shareable["public_transformation"]["sanitizer_policy"],
        policy
    );
    assert_eq!(shareable["sanitizer"], implementation);

    let mut substituted = shareable;
    substituted["public_derived_receipt"]["sanitizer_policy"] =
        substituted["public_derived_receipt"]["sanitizer_artifact"].clone();
    substituted["public_transformation"]["sanitizer_policy"] = substituted["sanitizer"].clone();
    let mut bytes = serde_json::to_vec(&substituted).unwrap();
    bytes.push(b'\n');
    let inspected = InspectedShareableSanitizedBundleV0::from_json_slice(&bytes).unwrap();
    assert!(sidecar.revalidate_public_bundle(inspected).is_err());
}

#[test]
fn generated_publication_rejects_decoded_jwt_policy_versions() {
    for private in [
        "e30.e30.c2lnbmF0dXJl",
        "eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxIn0.c2ln",
    ] {
        let authority = synthetic_authority(COMPLETED);
        let context = TrustedAdaptationContextV0::new(
            authority.commitment(),
            ArtifactBindingV0 {
                identity: "policy.generated-jwt-kill-test".to_string(),
                version: private.to_string(),
                hash: artifact_digest_v0(b"generated-jwt-kill-test"),
            },
        )
        .unwrap();
        let transaction = sanitize_capture_v0(COMPLETED, &authority, &context).unwrap();
        let error = match transaction.into_publication_pair() {
            Ok(_) => panic!("decoded JWT policy version must not publish"),
            Err(error) => error,
        };
        assert_eq!(error.code(), AdapterErrorCodeV0::SanitizerRejected);
    }
}

#[test]
fn ordinary_versions_publish_and_revalidate_as_self_consistent_public_bundles() {
    for version in ["release-2026.08.30", "v1.20.30-beta", "release-1.2.3.4"] {
        let authority = synthetic_authority(COMPLETED);
        let context = TrustedAdaptationContextV0::new(
            authority.commitment(),
            ArtifactBindingV0 {
                identity: "policy.benign-version-control".to_string(),
                version: version.to_string(),
                hash: artifact_digest_v0(b"benign-version-control"),
            },
        )
        .unwrap();
        let transaction = sanitize_capture_v0(COMPLETED, &authority, &context).unwrap();
        let child = transaction.jsonl().to_vec();
        let (_, bundle) = transaction.into_publication_pair().unwrap();
        let revalidated =
            InspectedShareableSanitizedBundleV0::from_json_slice(&bundle.to_json_line().unwrap())
                .unwrap()
                .revalidate_public_projection(&child)
                .unwrap();
        revalidated.validate().unwrap();
    }
}

#[test]
fn equal_child_bytes_with_different_parent_lineage_cannot_exchange_authority() {
    let parent_a = InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new_with_fixed_test_nonce(
            COMPLETED,
            codex_exec_fixture_spec_binding_v0(),
            FixedSyntheticTestNonceV0::new([0xb1; 32]),
        )
        .unwrap(),
    );
    let parent_b = InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new_with_fixed_test_nonce(
            COMPLETED,
            codex_exec_fixture_spec_binding_v0(),
            FixedSyntheticTestNonceV0::new([0xb2; 32]),
        )
        .unwrap(),
    );
    let first = sanitize_capture_with_fixed_test_nonce_v0(
        COMPLETED,
        &parent_a,
        &trusted(&parent_a),
        fixed_sanitization_material(0xb3),
    )
    .unwrap();
    let second = sanitize_capture_with_fixed_test_nonce_v0(
        COMPLETED,
        &parent_b,
        &trusted(&parent_b),
        fixed_sanitization_material(0xb3),
    )
    .unwrap();
    assert_eq!(first.jsonl(), second.jsonl());
    assert_ne!(
        first.authority().commitment(),
        second.authority().commitment()
    );
    assert_ne!(first.private_receipt(), second.private_receipt());
    assert_eq!(
        adapt_codex_exec_v0(first.jsonl(), second.authority(), first.derived_context())
            .unwrap_err()
            .code(),
        AdapterErrorCodeV0::TrustedContextMismatch
    );
}

#[test]
fn sanitizer_removes_every_retained_string_slot_canary_class() {
    let source = String::from_utf8(COMPLETED.to_vec()).unwrap();
    let mutations = [
        (
            "synthetic pre-turn diagnostic",
            "https://example.invalid/?token=secret",
        ),
        ("synthetic configuration warning", "user=alice"),
        ("synthetic-command", "host=workstation"),
        ("synthetic output", "env=PRIVATE"),
        ("synthetic/a.txt", "/home/alice/private"),
        ("synthetic first step", "control\\u001bcanary"),
        ("synthetic public summary", "cookie=session"),
    ];
    let mutated = mutations
        .iter()
        .fold(source, |text, (from, to)| text.replace(from, to));
    let bytes = mutated.as_bytes();
    let authority = synthetic_authority(bytes);
    let sanitized = sanitize_capture_with_fixed_test_nonce_v0(
        bytes,
        &authority,
        &trusted(&authority),
        fixed_sanitization_material(0x92),
    )
    .unwrap();
    let public = std::str::from_utf8(sanitized.jsonl())
        .unwrap()
        .to_ascii_lowercase();
    assert!(!public.contains("00000000-0000-7000-8000-000000000000"));
    for (_, canary) in mutations {
        assert!(!public.contains(&canary.to_ascii_lowercase()));
    }
}

#[test]
fn nonce_derived_thread_ids_are_repeatable_shaped_and_separate_run_identity() {
    let parent_a = synthetic_authority(COMPLETED);
    let parent_b = synthetic_authority(FAILED);
    let first = sanitize_capture_with_fixed_test_nonce_v0(
        COMPLETED,
        &parent_a,
        &trusted(&parent_a),
        fixed_sanitization_material(0xa1),
    )
    .unwrap();
    let repeat = sanitize_capture_with_fixed_test_nonce_v0(
        COMPLETED,
        &parent_a,
        &trusted(&parent_a),
        fixed_sanitization_material(0xa1),
    )
    .unwrap();
    let different_nonce_same_parent = sanitize_capture_with_fixed_test_nonce_v0(
        COMPLETED,
        &parent_a,
        &trusted(&parent_a),
        fixed_sanitization_material(0xa2),
    )
    .unwrap();
    let different_parent_and_nonce = sanitize_capture_with_fixed_test_nonce_v0(
        FAILED,
        &parent_b,
        &trusted(&parent_b),
        fixed_sanitization_material(0xa3),
    )
    .unwrap();

    let thread = |jsonl: &[u8]| {
        serde_json::from_slice::<serde_json::Value>(
            jsonl.split(|byte| *byte == b'\n').next().unwrap(),
        )
        .unwrap()["thread_id"]
            .as_str()
            .unwrap()
            .to_string()
    };
    let first_thread = thread(first.jsonl());
    assert_eq!(first.jsonl(), repeat.jsonl());
    assert_eq!(first_thread, thread(repeat.jsonl()));
    assert_ne!(first.jsonl(), different_nonce_same_parent.jsonl());
    assert_ne!(first_thread, thread(different_nonce_same_parent.jsonl()));
    assert_ne!(first_thread, thread(different_parent_and_nonce.jsonl()));
    assert_eq!(first_thread.len(), 36);
    assert_eq!(&first_thread[8..9], "-");
    assert_eq!(&first_thread[13..15], "-7");
    assert_eq!(&first_thread[18..19], "-");
    assert!(matches!(
        first_thread.as_bytes()[19],
        b'8' | b'9' | b'a' | b'b'
    ));
    assert_eq!(&first_thread[23..24], "-");
    assert!(
        first_thread
            .bytes()
            .all(|byte| { byte == b'-' || byte.is_ascii_digit() || matches!(byte, b'a'..=b'f') })
    );

    let first_trace = first
        .adapted()
        .validate()
        .unwrap()
        .to_compact_json()
        .unwrap();
    let repeat_trace = repeat
        .adapted()
        .validate()
        .unwrap()
        .to_compact_json()
        .unwrap();
    let different_nonce_trace = different_nonce_same_parent
        .adapted()
        .validate()
        .unwrap()
        .to_compact_json()
        .unwrap();
    let different_parent_trace = different_parent_and_nonce
        .adapted()
        .validate()
        .unwrap()
        .to_compact_json()
        .unwrap();
    let run_id = |trace: &[u8]| {
        serde_json::from_slice::<serde_json::Value>(trace).unwrap()["run_id"].clone()
    };
    assert_eq!(first_trace, repeat_trace);
    assert_eq!(run_id(&first_trace), run_id(&repeat_trace));
    assert_ne!(run_id(&first_trace), run_id(&different_nonce_trace));
    assert_ne!(run_id(&first_trace), run_id(&different_parent_trace));
    assert_ne!(first_trace, different_nonce_trace);
    assert_ne!(
        first.adapted().validate().unwrap().canonical_bytes(),
        different_nonce_same_parent
            .adapted()
            .validate()
            .unwrap()
            .canonical_bytes()
    );
    assert_eq!(
        first.adapted().validate().unwrap().canonical_bytes(),
        repeat.adapted().validate().unwrap().canonical_bytes()
    );
    assert_eq!(
        first
            .adapted()
            .to_private_bundle()
            .unwrap()
            .to_json_line()
            .unwrap(),
        repeat
            .adapted()
            .to_private_bundle()
            .unwrap()
            .to_json_line()
            .unwrap()
    );
}

#[test]
fn imported_nonce_assertions_do_not_gate_locally_minted_publication() {
    let fixed_parent = synthetic_authority(COMPLETED);
    let fixed_random_child =
        sanitize_capture_v0(COMPLETED, &fixed_parent, &trusted(&fixed_parent)).unwrap();
    let (_, fixed_parent_bundle) = fixed_random_child.into_publication_pair().unwrap();
    let fixed_parent_public: serde_json::Value =
        serde_json::from_slice(&fixed_parent_bundle.to_json_line().unwrap()).unwrap();
    assert!(
        fixed_parent_public["public_derived_receipt"]
            .get("asserted_parent_receipt")
            .is_none()
    );

    let random_parent = InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new(COMPLETED, codex_exec_fixture_spec_binding_v0()).unwrap(),
    );
    let random_parent_context = trusted(&random_parent);
    let random_fixed_child = sanitize_capture_with_fixed_test_nonce_v0(
        COMPLETED,
        &random_parent,
        &random_parent_context,
        fixed_sanitization_material(0xa3),
    )
    .unwrap();
    assert_eq!(
        serde_json::to_value(random_fixed_child.authority()).unwrap()["asserted_nonce_source"],
        "fixed-synthetic-test"
    );

    let random_random_child =
        sanitize_capture_v0(COMPLETED, &random_parent, &random_parent_context).unwrap();
    let (_, shareable) = random_random_child.into_publication_pair().unwrap();
    assert!(shareable.to_json_line().is_ok());
}

#[test]
fn public_wire_excludes_parent_provenance_and_coordinated_substitutions() {
    let parent = InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new(COMPLETED, codex_exec_fixture_spec_binding_v0()).unwrap(),
    );
    let transaction = sanitize_capture_v0(COMPLETED, &parent, &trusted(&parent)).unwrap();
    let child = transaction.jsonl().to_vec();
    let (sidecar, bundle) = transaction.into_publication_pair().unwrap();
    let bytes = bundle.to_json_line().unwrap();
    let original: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(
        original["evidence_class"],
        "sanitizer-conforming-child-projection"
    );
    assert_eq!(
        original["public_derived_receipt"]["evidence_class"],
        "sanitizer-conforming-child-projection"
    );

    InspectedShareableSanitizedBundleV0::from_json_slice(&bytes)
        .unwrap()
        .revalidate_public_projection(&child)
        .unwrap()
        .validate()
        .unwrap();
    sidecar
        .revalidate_public_bundle(
            InspectedShareableSanitizedBundleV0::from_json_slice(&bytes).unwrap(),
        )
        .unwrap()
        .validate()
        .unwrap();

    for field in [
        "asserted_origin_evidence_class",
        "asserted_parent_receipt",
        "derived_receipt_commitment",
        "public_parent_commitment",
    ] {
        assert!(original["public_derived_receipt"].get(field).is_none());
    }
    for field in ["derived_authority_commitment", "public_parent_commitment"] {
        assert!(original["public_transformation"].get(field).is_none());
    }
    assert!(original.get("public_parent_commitment").is_none());

    type CoordinatedAttack = (&'static str, fn(&mut serde_json::Value));

    let attacks: [CoordinatedAttack; 3] = [
        (
            "coordinated origin relabel",
            |value: &mut serde_json::Value| {
                value["public_derived_receipt"]["asserted_origin_evidence_class"] =
                    serde_json::json!("genuine-process-capture");
                value["public_derived_receipt"]["asserted_parent_receipt"] =
                    serde_json::json!("asserted-parent-receipt-process-capture-capture-random");
            },
        ),
        (
            "coordinated receipt commitment",
            |value: &mut serde_json::Value| {
                value["public_derived_receipt"]["derived_receipt_commitment"] =
                    serde_json::json!(public_zero_digest());
                value["public_transformation"]["derived_authority_commitment"] =
                    serde_json::json!(public_zero_digest());
            },
        ),
        (
            "coordinated parent commitment",
            |value: &mut serde_json::Value| {
                value["public_parent_commitment"] = serde_json::json!(public_zero_digest());
                value["public_derived_receipt"]["public_parent_commitment"] =
                    serde_json::json!(public_zero_digest());
                value["public_transformation"]["public_parent_commitment"] =
                    serde_json::json!(public_zero_digest());
            },
        ),
    ];
    for (name, attack) in attacks {
        let mut mutated = original.clone();
        attack(&mut mutated);
        let mut encoded = serde_json::to_vec(&mutated).unwrap();
        encoded.push(b'\n');
        assert_eq!(
            InspectedShareableSanitizedBundleV0::from_json_slice(&encoded)
                .expect_err(name)
                .code(),
            AdapterErrorCodeV0::JsonShape,
            "{name}"
        );
    }
}

fn public_zero_digest() -> &'static str {
    "sha256:0000000000000000000000000000000000000000000000000000000000000000"
}

#[test]
fn fixed_sanitization_roles_must_use_distinct_explicit_material() {
    let parent = synthetic_authority(COMPLETED);
    let error = sanitize_capture_with_fixed_test_nonce_v0(
        COMPLETED,
        &parent,
        &trusted(&parent),
        FixedTestSanitizationMaterialV0::new(
            FixedSyntheticTestNonceV0::new([0xa4; 32]),
            FixedSyntheticTestNonceV0::new([0xa4; 32]),
        ),
    )
    .unwrap_err();
    assert_eq!(error.code(), AdapterErrorCodeV0::EntropyUnavailable);
}

#[test]
fn regenerated_mapping_kills_valid_local_trace_mutation() {
    let authority = synthetic_authority(COMPLETED);
    let context = trusted(&authority);
    let bundle = adapt_codex_exec_v0(COMPLETED, &authority, &context)
        .unwrap()
        .to_private_bundle()
        .unwrap()
        .to_json_line()
        .unwrap();
    let mut value: serde_json::Value = serde_json::from_slice(&bundle[..bundle.len() - 1]).unwrap();
    let mut trace: serde_json::Value =
        serde_json::from_str(value["official_trace_json"].as_str().unwrap()).unwrap();
    trace["run_id"]["value"] = serde_json::json!("run-attacker-rehashed");
    value["official_trace_json"] =
        serde_json::Value::String(serde_json::to_string(&trace).unwrap());
    let mut mutated = serde_json::to_vec(&value).unwrap();
    mutated.push(b'\n');
    let inspected = InspectedPrivateAdapterBundleV0::from_json_slice(&mutated).unwrap();
    let error = match inspected.revalidate(COMPLETED, &authority, &context) {
        Ok(_) => panic!("regenerated mapping must reject the mutation"),
        Err(error) => error,
    };
    assert_eq!(error.code().as_str(), "bundle-mismatch");
}

#[test]
fn checker_mutations_reach_production_authority_rejection() {
    const ORIGINAL_KEY: [u8; 32] = [0x65; 32];
    const ALTERNATE_KEY: [u8; 32] = [0x35; 32];
    const ORIGINAL_TEXT: &str =
        "ed25519:d62f016a1efd1e4fdf793eb42cd84471e1ba9f0cf04d1287b5cc71f616287cb8";
    const ALTERNATE_TEXT: &str =
        "ed25519:a6d2455ea3a5771aba9fcb037924114c92f9f325049f6b4269e739d9048bb869";

    let authority = synthetic_authority(COMPLETED);
    let adapted = adapt_codex_exec_v0(COMPLETED, &authority, &trusted(&authority)).unwrap();
    let validated = adapted.validate().unwrap();
    let original_key = ReplayAuthoritySigningKeyV0::from_bytes(&ORIGINAL_KEY).unwrap();
    let alternate_key = ReplayAuthoritySigningKeyV0::from_bytes(&ALTERNATE_KEY).unwrap();
    assert_eq!(original_key.verification_key_text(), ORIGINAL_TEXT);
    assert_eq!(alternate_key.verification_key_text(), ALTERNATE_TEXT);
    assert_typed_ed25519_hex(ORIGINAL_TEXT, 64);
    assert_typed_ed25519_hex(ALTERNATE_TEXT, 64);
    assert_ne!(ORIGINAL_TEXT, ALTERNATE_TEXT);

    let receipt = issue_trajectory_replay_authority_receipt_v0(
        &validated,
        &original_key,
        "trajectory.composition.fixture-authority",
        "trajectory-composition-fixture-key",
        1,
    )
    .unwrap();
    let receipt_bytes = receipt.to_json_line().unwrap();
    let mut mutated_receipt: serde_json::Value = serde_json::from_slice(&receipt_bytes).unwrap();
    let original_signature = mutated_receipt["signature"].as_str().unwrap().to_string();
    let mut mutated_signature = original_signature.clone();
    let replacement = if mutated_signature.ends_with('0') {
        '1'
    } else {
        '0'
    };
    mutated_signature.pop();
    mutated_signature.push(replacement);
    assert_typed_ed25519_hex(&original_signature, 128);
    assert_typed_ed25519_hex(&mutated_signature, 128);
    assert_ne!(original_signature, mutated_signature);
    mutated_receipt["signature"] = serde_json::json!(mutated_signature);
    let mut mutated_receipt_bytes = serde_json::to_vec(&mutated_receipt).unwrap();
    mutated_receipt_bytes.push(b'\n');

    let policy_bytes = |verification_key: &str| {
        let mut bytes = serde_json::to_vec(&serde_json::json!({
            "trust_policy_format": "legitimacy.trajectory.replay-authority-trust-policy",
            "trust_policy_version": "0",
            "issuer": "trajectory.composition.fixture-authority",
            "algorithm": "ed25519",
            "key_id": "trajectory-composition-fixture-key",
            "accepted_authority_epoch": 1,
            "verification_key": verification_key,
        }))
        .unwrap();
        bytes.push(b'\n');
        bytes
    };
    let original_policy =
        ReplayAuthorityTrustPolicyV0::from_json_slice(&policy_bytes(ORIGINAL_TEXT)).unwrap();
    let alternate_policy =
        ReplayAuthorityTrustPolicyV0::from_json_slice(&policy_bytes(ALTERNATE_TEXT)).unwrap();
    let trust_error = verify_replay_authority_receipt_v0(
        UnverifiedReplayAuthorityReceiptV0::from_json_slice(&receipt_bytes).unwrap(),
        &alternate_policy,
    )
    .unwrap_err();
    assert_eq!(
        trust_error.code(),
        ReplayAuthorityErrorCodeV0::AuthorityRejected
    );
    println!(
        "checker mutation replay-trust {}",
        trust_error.code().as_str()
    );

    let signature_error = verify_replay_authority_receipt_v0(
        UnverifiedReplayAuthorityReceiptV0::from_json_slice(&mutated_receipt_bytes).unwrap(),
        &original_policy,
    )
    .unwrap_err();
    assert_eq!(
        signature_error.code(),
        ReplayAuthorityErrorCodeV0::AuthorityRejected
    );
    println!(
        "checker mutation replay-signature {}",
        signature_error.code().as_str()
    );
}

fn assert_typed_ed25519_hex(value: &str, payload_length: usize) {
    let payload = value.strip_prefix("ed25519:").unwrap();
    assert_eq!(payload.len(), payload_length);
    assert!(
        payload
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    );
}

fn independent_framed_hash(domain: &str, components: &[&[u8]]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"legitimacy.trajectory.hash.v0\0");
    independent_frame(&mut hasher, domain.as_bytes());
    hasher.update(u64::try_from(components.len()).unwrap().to_be_bytes());
    for component in components {
        independent_frame(&mut hasher, component);
    }
    format!("sha256:{:x}", hasher.finalize())
}

fn independent_frame(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update(u64::try_from(bytes.len()).unwrap().to_be_bytes());
    hasher.update(bytes);
}
