use super::*;
use legitimacy::raw_capture_seal_v0;
use legitimacy::trajectory::codex_exec_v0::{
    AdapterErrorCodeV0, sanitize_capture_v0, sanitize_capture_with_fixed_test_nonce_v0,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

#[derive(Clone, Copy, Debug)]
enum ReceiptMutationOutcome {
    Import(AdapterErrorCodeV0),
    Adapt(AdapterErrorCodeV0),
}

struct ReceiptMutation {
    path: &'static [&'static str],
    replacement: Value,
    expected: ReceiptMutationOutcome,
}

impl ReceiptMutation {
    fn new(
        path: &'static [&'static str],
        replacement: Value,
        expected: ReceiptMutationOutcome,
    ) -> Self {
        Self {
            path,
            replacement,
            expected,
        }
    }
}

macro_rules! receipt_mutation {
    ($path:expr, $replacement:expr, $expected:expr) => {
        ReceiptMutation::new($path, json!($replacement), $expected)
    };
}

#[test]
fn fixed_trusted_commitment_rejects_every_synthetic_receipt_field_mutation() {
    let authority = synthetic_authority(COMPLETED);
    let context = trusted(&authority);
    let original = serde_json::to_value(&authority).unwrap();
    use ReceiptMutationOutcome::{Adapt, Import};
    let mutations = [
        ReceiptMutation::new(
            &["authority"],
            json!("other"),
            Import(AdapterErrorCodeV0::ReceiptShape),
        ),
        ReceiptMutation::new(
            &["receipt_format"],
            json!("other"),
            Import(AdapterErrorCodeV0::ReceiptShape),
        ),
        ReceiptMutation::new(
            &["receipt_version"],
            json!("1"),
            Import(AdapterErrorCodeV0::ReceiptShape),
        ),
        ReceiptMutation::new(
            &["evidence_class"],
            json!("genuine-process-capture"),
            Import(AdapterErrorCodeV0::ReceiptShape),
        ),
        ReceiptMutation::new(
            &["emitter", "package_version"],
            json!("0.0.0"),
            Import(AdapterErrorCodeV0::ReceiptMismatch),
        ),
        ReceiptMutation::new(
            &["emitter", "source_tag"],
            json!("rust-v0.0.0"),
            Import(AdapterErrorCodeV0::ReceiptMismatch),
        ),
        ReceiptMutation::new(
            &["emitter", "source_tag_object_sha"],
            json!("0000000000000000000000000000000000000000"),
            Import(AdapterErrorCodeV0::ReceiptMismatch),
        ),
        ReceiptMutation::new(
            &["emitter", "source_commit_sha"],
            json!("0000000000000000000000000000000000000000"),
            Import(AdapterErrorCodeV0::ReceiptMismatch),
        ),
        ReceiptMutation::new(
            &["full_jsonl_length"],
            json!(1),
            Adapt(AdapterErrorCodeV0::TrustedContextMismatch),
        ),
        ReceiptMutation::new(
            &["full_jsonl_digest"],
            json!(zero_digest()),
            Adapt(AdapterErrorCodeV0::TrustedContextMismatch),
        ),
        ReceiptMutation::new(
            &["raw_record_count"],
            json!(1),
            Import(AdapterErrorCodeV0::ReceiptShape),
        ),
        ReceiptMutation::new(
            &["raw_capture_seal", "record_count"],
            json!(1),
            Import(AdapterErrorCodeV0::ReceiptShape),
        ),
        ReceiptMutation::new(
            &["raw_capture_seal", "digest"],
            json!(zero_digest()),
            Adapt(AdapterErrorCodeV0::TrustedContextMismatch),
        ),
        ReceiptMutation::new(
            &["fixture_spec_manifest", "identity"],
            json!("legitimacy.codex-exec-v0.other-fixture"),
            Import(AdapterErrorCodeV0::ReceiptMismatch),
        ),
        ReceiptMutation::new(
            &["fixture_spec_manifest", "version"],
            json!("1"),
            Import(AdapterErrorCodeV0::ReceiptMismatch),
        ),
        ReceiptMutation::new(
            &["fixture_spec_manifest", "hash"],
            json!(zero_digest()),
            Import(AdapterErrorCodeV0::ReceiptMismatch),
        ),
        ReceiptMutation::new(
            &["asserted_nonce_source"],
            json!("capture-random"),
            Adapt(AdapterErrorCodeV0::TrustedContextMismatch),
        ),
        ReceiptMutation::new(
            &["blinding_nonce_lower_hex"],
            json!("11".repeat(32)),
            Adapt(AdapterErrorCodeV0::TrustedContextMismatch),
        ),
    ];
    assert_eq!(mutations.len(), 18);
    for mutation in &mutations {
        assert_receipt_mutation_rejected(&original, COMPLETED, &context, mutation);
    }
}

#[test]
fn decoded_capture_random_receipts_reject_all_zero_nonce_in_every_receipt_class() {
    let parent = InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new(COMPLETED, codex_exec_fixture_spec_binding_v0()).unwrap(),
    );
    let parent_context = trusted(&parent);
    let derived = sanitize_capture_v0(COMPLETED, &parent, &parent_context).unwrap();

    let mut synthetic = serde_json::to_value(&parent).unwrap();
    synthetic["blinding_nonce_lower_hex"] = json!("00".repeat(32));

    let mut process = process_receipt_wire(COMPLETED, json!({"termination":"exited","code":0}));
    process["blinding_nonce_lower_hex"] = json!("00".repeat(32));

    let mut sanitized_derived = serde_json::to_value(derived.authority()).unwrap();
    assert_eq!(sanitized_derived["asserted_nonce_source"], "capture-random");
    sanitized_derived["blinding_nonce_lower_hex"] = json!("00".repeat(32));

    for wire in [synthetic, process, sanitized_derived] {
        assert!(
            InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&wire).unwrap()).is_err(),
            "{wire}"
        );
    }
}

#[test]
fn imported_derived_and_process_nonce_declarations_remain_syntactically_constrained() {
    let synthetic = synthetic_authority(COMPLETED);
    let synthetic_context = trusted(&synthetic);
    let derived = sanitize_capture_with_fixed_test_nonce_v0(
        COMPLETED,
        &synthetic,
        &synthetic_context,
        fixed_sanitization_material(0x79),
    )
    .unwrap();
    let derived_context =
        TrustedAdaptationContextV0::new(derived.authority().commitment(), policy_binding())
            .unwrap();
    let mut relabeled_derived = serde_json::to_value(derived.authority()).unwrap();
    relabeled_derived["asserted_nonce_source"] = json!("capture-random");
    relabeled_derived["asserted_parent_receipt"] =
        json!("asserted-parent-receipt-synthetic-fixture-capture-random");
    let relabeled_derived =
        InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&relabeled_derived).unwrap())
            .unwrap();
    assert_eq!(
        adapt_codex_exec_v0(derived.jsonl(), &relabeled_derived, &derived_context)
            .unwrap_err()
            .code(),
        AdapterErrorCodeV0::TrustedContextMismatch
    );

    let process_wire = process_receipt_wire(COMPLETED, json!({"termination":"exited","code":0}));
    let process =
        InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&process_wire).unwrap())
            .unwrap();
    let process_context = trusted(&process);
    let mut relabeled_process = process_wire;
    relabeled_process["asserted_nonce_source"] = json!("fixed-synthetic-test");
    assert_eq!(
        InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&relabeled_process).unwrap())
            .unwrap_err()
            .code(),
        AdapterErrorCodeV0::ReceiptShape
    );
    assert!(adapt_codex_exec_v0(COMPLETED, &process, &process_context).is_ok());
}

#[test]
fn receipt_raw_fields_are_rechecked_but_other_private_facts_are_attested() {
    let authority = synthetic_authority(COMPLETED);
    let context = trusted(&authority);
    let mut mutated = COMPLETED.to_vec();
    let needle = b"synthetic response";
    let position = mutated
        .windows(needle.len())
        .position(|window| window == needle)
        .unwrap();
    mutated[position] = b'S';
    assert!(adapt_codex_exec_v0(&mutated, &authority, &context).is_err());

    let replacement_authority = synthetic_authority(&mutated);
    let replacement_context = trusted(&replacement_authority);
    assert!(
        adapt_codex_exec_v0(&mutated, &replacement_authority, &replacement_context).is_ok(),
        "replacing bytes, receipt, and trusted commitment is explicitly outside the claim"
    );
}

#[test]
fn reserved_and_dynamic_artifact_identities_cannot_substitute_downstream_policy() {
    use legitimacy::trajectory::{
        codex_exec_v0::{
            codex_exec_adapter_binding_v0, codex_exec_capture_profile_binding_v0,
            codex_exec_sanitizer_binding_v0, codex_exec_sanitizer_policy_binding_v0,
        },
        trajectory_schema_binding_v0,
    };

    let authority = synthetic_authority(COMPLETED);
    for binding in [
        codex_exec_adapter_binding_v0(),
        codex_exec_capture_profile_binding_v0(),
        codex_exec_fixture_spec_binding_v0(),
        codex_exec_sanitizer_binding_v0(),
        codex_exec_sanitizer_policy_binding_v0(),
        trajectory_schema_binding_v0(),
        ArtifactBindingV0 {
            identity: "derivation.codex-exec-v0.attacker".to_string(),
            version: "0".to_string(),
            hash: artifact_digest_v0(b"attacker"),
        },
    ] {
        assert_eq!(
            TrustedAdaptationContextV0::new(authority.commitment(), binding)
                .unwrap_err()
                .code(),
            AdapterErrorCodeV0::ReservedPolicy
        );
    }

    for prefix in [
        "legitimacy.codex-exec-v0.",
        "legitimacy.trajectory.",
        "derivation.codex-exec-v0.",
    ] {
        let identity = format!("{prefix}attacker-controlled");
        assert_eq!(
            TrustedAdaptationContextV0::new(
                authority.commitment(),
                ArtifactBindingV0 {
                    identity,
                    version: "attacker".to_string(),
                    hash: artifact_digest_v0(format!("{prefix}arbitrary-hash").as_bytes()),
                },
            )
            .unwrap_err()
            .code(),
            AdapterErrorCodeV0::ReservedPolicy,
            "{prefix}"
        );
    }

    for identity in [
        "legitimacy.codex-exec-v0x.user-policy",
        "legitimacy.trajectoryx.user-policy",
        "derivation.codex-exec-v0x.user-policy",
    ] {
        assert!(
            TrustedAdaptationContextV0::new(
                authority.commitment(),
                ArtifactBindingV0 {
                    identity: identity.to_string(),
                    version: "0".to_string(),
                    hash: artifact_digest_v0(identity.as_bytes()),
                },
            )
            .is_ok(),
            "{identity}"
        );
    }

    let process = InputAuthorityReceiptV0::from_json_slice(
        &serde_json::to_vec(&process_receipt_wire(
            COMPLETED,
            json!({"termination":"exited","code":0}),
        ))
        .unwrap(),
    )
    .unwrap();
    let capture_tool_policy =
        legitimacy::trajectory::codex_exec_v0::codex_exec_capture_producer_binding_v0();
    assert_eq!(
        TrustedAdaptationContextV0::new(process.commitment(), capture_tool_policy)
            .unwrap_err()
            .code(),
        AdapterErrorCodeV0::ReservedPolicy
    );
}

#[test]
fn process_terminal_relations_are_exact_and_signals_are_unsupported() {
    use ReceiptMutationOutcome::{Adapt, Import};
    for (bytes, termination, expected) in [
        (COMPLETED, json!({"termination":"exited","code":0}), None),
        (COMPLETED, json!({"termination":"exited","code":1}), None),
        (
            COMPLETED,
            json!({"termination":"exited","code":2}),
            Some(Adapt(AdapterErrorCodeV0::IllegalTermination)),
        ),
        (FAILED, json!({"termination":"exited","code":1}), None),
        (
            FAILED,
            json!({"termination":"exited","code":0}),
            Some(Adapt(AdapterErrorCodeV0::IllegalTermination)),
        ),
        (
            COMPLETED,
            json!({"termination":"signaled","signal":9,"core_dumped":false}),
            Some(Adapt(AdapterErrorCodeV0::UnsupportedProfile)),
        ),
        (
            COMPLETED,
            json!({"termination":"exited","code":137}),
            Some(Import(AdapterErrorCodeV0::IllegalTermination)),
        ),
    ] {
        let wire = process_receipt_wire(bytes, termination);
        let decoded = InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&wire).unwrap());
        match expected {
            None => {
                let authority = decoded.expect("declared import success");
                adapt_codex_exec_v0(bytes, &authority, &trusted(&authority))
                    .expect("declared adaptation success");
            }
            Some(Import(code)) => {
                assert_eq!(decoded.unwrap_err().code(), code, "{wire}");
            }
            Some(Adapt(code)) => {
                let authority = decoded.expect("declared import success");
                assert_eq!(
                    adapt_codex_exec_v0(bytes, &authority, &trusted(&authority))
                        .unwrap_err()
                        .code(),
                    code,
                    "{wire}"
                );
            }
        }
    }
}

#[test]
fn noncanonical_fresh_exec_argv_and_process_receipt_facts_fail() {
    let mut wire = process_receipt_wire(COMPLETED, json!({"termination":"exited","code":0}));
    wire["argv"]["arguments_lower_hex"][1] = json!(hex(b"resume"));
    assert!(InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&wire).unwrap()).is_err());

    let mut wire = process_receipt_wire(COMPLETED, json!({"termination":"exited","code":0}));
    wire["stderr"]["sha256"] = json!("sha256:bad");
    assert!(InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&wire).unwrap()).is_err());

    let mut wire = process_receipt_wire(COMPLETED, json!({"termination":"exited","code":0}));
    wire["stdin"] = json!({"presence":"absent"});
    assert!(InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&wire).unwrap()).is_err());

    let mut wire = process_receipt_wire(COMPLETED, json!({"termination":"exited","code":0}));
    wire["executable_execution_binding"] = json!("path-open-then-exec");
    assert!(InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&wire).unwrap()).is_err());

    let mut wire = process_receipt_wire(COMPLETED, json!({"termination":"exited","code":0}));
    wire["executable_sha256"] = json!(standard_sha(b"different executable"));
    assert!(InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&wire).unwrap()).is_err());

    let mut wire = process_receipt_wire(COMPLETED, json!({"termination":"exited","code":0}));
    wire["asserted_nonce_source"] = json!("fixed-synthetic-test");
    assert!(InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&wire).unwrap()).is_err());
}

#[test]
fn workspace_tree_preimage_is_ordered_closed_and_self_consistent() {
    use legitimacy::trajectory::codex_exec_v0::{
        CaptureManifestEntryV0, InodeIdentityV0, codex_exec_workspace_tree_digest_v0,
    };

    let entries = vec![
        CaptureManifestEntryV0::new(
            0,
            "fixture-input",
            "regular-file-bytes",
            b"a.txt",
            1,
            standard_sha(b"a"),
            InodeIdentityV0::new(8, 201),
        )
        .unwrap(),
        CaptureManifestEntryV0::new(
            1,
            "fixture-input",
            "regular-file-bytes",
            b"b.txt",
            1,
            standard_sha(b"b"),
            InodeIdentityV0::new(8, 202),
        )
        .unwrap(),
    ];
    let tree = codex_exec_workspace_tree_digest_v0(&entries).unwrap();
    let mut wire = process_receipt_wire(COMPLETED, json!({"termination":"exited","code":0}));
    wire["workspace_manifest"] = serde_json::to_value(&entries).unwrap();
    wire["workspace_tree_digest"] = json!(tree);
    assert!(InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&wire).unwrap()).is_ok());

    for path in [
        &["workspace_manifest", "0", "ordinal"][..],
        &["workspace_manifest", "0", "role"],
        &["workspace_manifest", "0", "format"],
        &["workspace_manifest", "0", "relative_path_lower_hex"],
        &["workspace_manifest", "0", "byte_length"],
        &["workspace_manifest", "0", "sha256"],
        &["workspace_manifest", "0", "inode", "dev"],
        &["workspace_manifest", "0", "inode", "ino"],
        &["workspace_tree_digest"],
    ] {
        let mut mutated = wire.clone();
        let target = path.iter().fold(&mut mutated, |value, key| {
            if let Ok(index) = key.parse::<usize>() {
                &mut value[index]
            } else {
                &mut value[*key]
            }
        });
        *target = if target.is_number() {
            json!(99)
        } else {
            json!("mutated")
        };
        assert!(
            InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&mutated).unwrap())
                .is_err(),
            "{path:?}"
        );
    }

    let mut reordered = wire;
    reordered["workspace_manifest"]
        .as_array_mut()
        .unwrap()
        .swap(0, 1);
    assert!(
        InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&reordered).unwrap()).is_err()
    );
}

#[test]
fn process_receipt_inode_roles_are_pairwise_disjoint_at_every_member_position() {
    use legitimacy::trajectory::codex_exec_v0::{
        CaptureManifestEntryV0, InodeIdentityV0, codex_exec_workspace_tree_digest_v0,
    };

    let entries = vec![
        CaptureManifestEntryV0::new(
            0,
            "fixture-input",
            "regular-file-bytes",
            b"a.txt",
            1,
            standard_sha(b"a"),
            InodeIdentityV0::new(8, 201),
        )
        .unwrap(),
        CaptureManifestEntryV0::new(
            1,
            "fixture-input",
            "regular-file-bytes",
            b"b.txt",
            1,
            standard_sha(b"b"),
            InodeIdentityV0::new(8, 202),
        )
        .unwrap(),
    ];
    let mut valid = process_receipt_wire(COMPLETED, json!({"termination":"exited","code":0}));
    valid["workspace_manifest"] = serde_json::to_value(&entries).unwrap();
    valid["workspace_tree_digest"] = json!(codex_exec_workspace_tree_digest_v0(&entries).unwrap());
    assert!(InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&valid).unwrap()).is_ok());

    let mut executable_tool_alias = valid.clone();
    executable_tool_alias["executable_inode"] =
        executable_tool_alias["capture_tool"]["inode"].clone();
    assert_eq!(
        InputAuthorityReceiptV0::from_json_slice(
            &serde_json::to_vec(&executable_tool_alias).unwrap()
        )
        .unwrap_err()
        .code(),
        AdapterErrorCodeV0::ReceiptMismatch
    );

    for member_index in 0..2 {
        for role in ["executable_inode", "capture_tool"] {
            let mut aliased = valid.clone();
            let role_inode = if role == "executable_inode" {
                aliased["executable_inode"].clone()
            } else {
                aliased["capture_tool"]["inode"].clone()
            };
            aliased["workspace_manifest"][member_index]["inode"] = role_inode;
            assert_eq!(
                InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&aliased).unwrap())
                    .unwrap_err()
                    .code(),
                AdapterErrorCodeV0::ReceiptMismatch,
                "member {member_index} alias with {role}"
            );
        }
    }

    let mut duplicate_members = valid;
    duplicate_members["workspace_manifest"][1]["inode"] =
        duplicate_members["workspace_manifest"][0]["inode"].clone();
    assert_eq!(
        InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&duplicate_members).unwrap())
            .unwrap_err()
            .code(),
        AdapterErrorCodeV0::ReceiptShape
    );
}

#[test]
fn fixed_context_rejects_every_derived_receipt_field_mutation() {
    use ReceiptMutationOutcome::{Adapt, Import};
    use legitimacy::trajectory::codex_exec_v0::sanitize_capture_with_fixed_test_nonce_v0;

    let parent = synthetic_authority(COMPLETED);
    let sanitized = sanitize_capture_with_fixed_test_nonce_v0(
        COMPLETED,
        &parent,
        &trusted(&parent),
        fixed_sanitization_material(0x71),
    )
    .unwrap();
    let context =
        TrustedAdaptationContextV0::new(sanitized.authority().commitment(), policy_binding())
            .unwrap();
    let original = serde_json::to_value(sanitized.authority()).unwrap();
    let import_shape = Import(AdapterErrorCodeV0::ReceiptShape);
    let import_mismatch = Import(AdapterErrorCodeV0::ReceiptMismatch);
    let adapt_context = Adapt(AdapterErrorCodeV0::TrustedContextMismatch);
    let mutations = [
        ReceiptMutation::new(&["authority"], json!("other"), import_shape),
        ReceiptMutation::new(&["receipt_format"], json!("other"), import_shape),
        ReceiptMutation::new(&["receipt_version"], json!("1"), import_shape),
        ReceiptMutation::new(&["evidence_class"], json!("other"), import_shape),
        ReceiptMutation::new(
            &["asserted_origin_evidence_class"],
            json!("other"),
            import_shape,
        ),
        ReceiptMutation::new(&["asserted_parent_receipt"], json!("other"), import_shape),
        ReceiptMutation::new(
            &["parent_receipt_commitment"],
            json!(zero_digest()),
            adapt_context,
        ),
        ReceiptMutation::new(&["parent_full_jsonl_length"], json!(1), adapt_context),
        ReceiptMutation::new(
            &["parent_full_jsonl_digest"],
            json!(zero_digest()),
            adapt_context,
        ),
        ReceiptMutation::new(
            &["parent_raw_capture_seal", "record_count"],
            json!(1),
            adapt_context,
        ),
        ReceiptMutation::new(
            &["parent_raw_capture_seal", "digest"],
            json!(zero_digest()),
            adapt_context,
        ),
        ReceiptMutation::new(
            &["sanitizer_policy", "identity"],
            json!("legitimacy.codex-exec-v0.other-sanitizer-policy"),
            import_mismatch,
        ),
        ReceiptMutation::new(
            &["sanitizer_policy", "version"],
            json!("1"),
            import_mismatch,
        ),
        ReceiptMutation::new(
            &["sanitizer_policy", "hash"],
            json!(zero_digest()),
            import_mismatch,
        ),
        ReceiptMutation::new(
            &["sanitizer_artifact", "identity"],
            json!("legitimacy.codex-exec-v0.other-sanitizer"),
            import_mismatch,
        ),
        ReceiptMutation::new(
            &["sanitizer_artifact", "version"],
            json!("1"),
            import_mismatch,
        ),
        ReceiptMutation::new(
            &["sanitizer_artifact", "hash"],
            json!(zero_digest()),
            import_mismatch,
        ),
        ReceiptMutation::new(&["derived_full_jsonl_length"], json!(1), adapt_context),
        ReceiptMutation::new(
            &["derived_full_jsonl_digest"],
            json!(zero_digest()),
            adapt_context,
        ),
        ReceiptMutation::new(
            &["derived_raw_capture_seal", "record_count"],
            json!(1),
            adapt_context,
        ),
        ReceiptMutation::new(
            &["derived_raw_capture_seal", "digest"],
            json!(zero_digest()),
            adapt_context,
        ),
        ReceiptMutation::new(
            &["asserted_nonce_source"],
            json!("capture-random"),
            adapt_context,
        ),
        ReceiptMutation::new(
            &["blinding_nonce_lower_hex"],
            json!("11".repeat(32)),
            adapt_context,
        ),
    ];
    assert_eq!(mutations.len(), 23);
    for mutation in &mutations {
        assert_receipt_mutation_rejected(&original, sanitized.jsonl(), &context, mutation);
    }
}

#[test]
fn process_origin_derived_receipt_rejects_fixed_synthetic_nonce() {
    let process = InputAuthorityReceiptV0::from_json_slice(
        &serde_json::to_vec(&process_receipt_wire(
            COMPLETED,
            json!({"termination":"exited","code":0}),
        ))
        .unwrap(),
    )
    .unwrap();
    let derived = sanitize_capture_v0(COMPLETED, &process, &trusted(&process)).unwrap();
    let mut relabeled = serde_json::to_value(derived.authority()).unwrap();
    assert_eq!(
        relabeled["asserted_origin_evidence_class"],
        "genuine-process-capture"
    );
    relabeled["asserted_nonce_source"] = json!("fixed-synthetic-test");
    relabeled["blinding_nonce_lower_hex"] = json!("44".repeat(32));
    assert_eq!(
        InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&relabeled).unwrap())
            .unwrap_err()
            .code(),
        AdapterErrorCodeV0::ReceiptShape
    );
}

#[test]
fn fixed_context_rejects_every_process_receipt_field_mutation() {
    use ReceiptMutationOutcome::{Adapt, Import};

    let original = process_receipt_wire(COMPLETED, json!({"termination":"exited","code":0}));
    let authority =
        InputAuthorityReceiptV0::from_json_slice(&serde_json::to_vec(&original).unwrap()).unwrap();
    let context = trusted(&authority);
    let import_shape = Import(AdapterErrorCodeV0::ReceiptShape);
    let import_mismatch = Import(AdapterErrorCodeV0::ReceiptMismatch);
    let import_profile = Import(AdapterErrorCodeV0::UnsupportedProfile);
    let adapt_context = Adapt(AdapterErrorCodeV0::TrustedContextMismatch);
    let mutations = [
        receipt_mutation!(&["authority"], "other", import_shape),
        receipt_mutation!(&["receipt_format"], "other", import_shape),
        receipt_mutation!(&["receipt_version"], "1", import_shape),
        receipt_mutation!(&["evidence_class"], "other", import_shape),
        receipt_mutation!(&["emitter", "package_version"], "0.0.0", import_mismatch),
        receipt_mutation!(&["emitter", "source_tag"], "rust-v0.0.0", import_mismatch),
        receipt_mutation!(
            &["emitter", "source_tag_object_sha"],
            "0000000000000000000000000000000000000000",
            import_mismatch
        ),
        receipt_mutation!(
            &["emitter", "source_commit_sha"],
            "0000000000000000000000000000000000000000",
            import_mismatch
        ),
        receipt_mutation!(&["executable_sha256"], zero_digest(), import_mismatch),
        receipt_mutation!(&["executable_inode", "dev"], 9, adapt_context),
        receipt_mutation!(&["executable_inode", "ino"], 102, adapt_context),
        receipt_mutation!(
            &["executable_execution_binding"],
            "path-open-then-exec",
            import_profile
        ),
        receipt_mutation!(&["artifact_open_discipline"], "path-open", import_profile),
        receipt_mutation!(
            &["workspace_execution_discipline"],
            "mutable-during-exec",
            import_profile
        ),
        receipt_mutation!(&["argv", "argument_count"], 9, import_shape),
        ReceiptMutation::new(&["argv", "arguments_lower_hex"], json!([]), import_shape),
        receipt_mutation!(&["argv", "arguments_lower_hex", "0"], "00", import_shape),
        receipt_mutation!(&["argv", "arguments_lower_hex", "1"], "00", import_shape),
        receipt_mutation!(&["argv", "arguments_lower_hex", "2"], "00", import_shape),
        receipt_mutation!(&["argv", "arguments_lower_hex", "3"], "00", import_shape),
        receipt_mutation!(&["argv", "arguments_lower_hex", "4"], "00", import_shape),
        receipt_mutation!(&["argv", "arguments_lower_hex", "5"], "00", import_shape),
        receipt_mutation!(&["argv", "arguments_lower_hex", "6"], "00", import_shape),
        receipt_mutation!(&["argv", "arguments_lower_hex", "7"], "00", import_shape),
        receipt_mutation!(&["argv", "arguments_lower_hex", "8"], "00", import_shape),
        receipt_mutation!(&["argv", "arguments_lower_hex", "9"], "00", import_shape),
        receipt_mutation!(&["argv", "total_bytes"], 1, import_shape),
        receipt_mutation!(&["resolved_mode"], "other", import_shape),
        receipt_mutation!(&["capture_profile"], "other", import_shape),
        receipt_mutation!(&["stdin", "presence"], "absent", import_profile),
        receipt_mutation!(&["stdin", "byte_length"], 1, adapt_context),
        receipt_mutation!(&["stdin", "sha256"], zero_digest(), adapt_context),
        receipt_mutation!(&["termination", "termination"], "other", import_shape),
        receipt_mutation!(&["termination", "code"], 1, adapt_context),
        receipt_mutation!(&["stdout", "byte_length"], 1, adapt_context),
        receipt_mutation!(&["stdout", "sha256"], zero_digest(), adapt_context),
        receipt_mutation!(&["stderr", "byte_length"], 1, adapt_context),
        receipt_mutation!(&["stderr", "sha256"], zero_digest(), adapt_context),
        receipt_mutation!(&["raw_record_count"], 99, import_shape),
        receipt_mutation!(&["raw_capture_seal", "record_count"], 99, import_shape),
        receipt_mutation!(
            &["raw_capture_seal", "digest"],
            zero_digest(),
            adapt_context
        ),
        receipt_mutation!(
            &["capture_tool", "identity", "identity"],
            "legitimacy.codex-capture-tool-other",
            import_mismatch
        ),
        receipt_mutation!(
            &["capture_tool", "identity", "version"],
            "1",
            import_mismatch
        ),
        receipt_mutation!(
            &["capture_tool", "identity", "hash"],
            zero_digest(),
            import_mismatch
        ),
        receipt_mutation!(
            &["capture_tool", "file_sha256"],
            zero_digest(),
            adapt_context
        ),
        receipt_mutation!(&["capture_tool", "inode", "dev"], 9, adapt_context),
        receipt_mutation!(&["capture_tool", "inode", "ino"], 102, adapt_context),
        receipt_mutation!(
            &["capture_profile_artifact", "identity"],
            "legitimacy.codex-exec-v0.other-profile",
            import_profile
        ),
        receipt_mutation!(
            &["capture_profile_artifact", "version"],
            "1",
            import_profile
        ),
        receipt_mutation!(
            &["capture_profile_artifact", "hash"],
            zero_digest(),
            import_profile
        ),
        ReceiptMutation::new(
            &["workspace_manifest"],
            json!([{
                "ordinal": 0,
                "role": "fixture-input",
                "format": "regular-file-bytes",
                "relative_path_lower_hex": "612e747874",
                "byte_length": 1,
                "sha256": zero_digest(),
                "inode": {"dev": 8, "ino": 201}
            }]),
            import_mismatch,
        ),
        receipt_mutation!(&["workspace_tree_digest"], zero_digest(), import_mismatch),
        receipt_mutation!(&["release_asset", "name"], "other.tar.gz", import_mismatch),
        receipt_mutation!(&["release_asset", "sha256"], zero_digest(), import_mismatch),
        receipt_mutation!(
            &["sigstore_bundle", "name"],
            "other.sigstore",
            import_mismatch
        ),
        receipt_mutation!(
            &["sigstore_bundle", "sha256"],
            zero_digest(),
            import_mismatch
        ),
        receipt_mutation!(
            &["sigstore_verification"],
            "verified-sigstore-rekor",
            adapt_context
        ),
        receipt_mutation!(
            &["asserted_nonce_source"],
            "fixed-synthetic-test",
            import_shape
        ),
        receipt_mutation!(
            &["blinding_nonce_lower_hex"],
            "11".repeat(32),
            adapt_context
        ),
    ];
    assert_eq!(mutations.len(), 59);
    for mutation in &mutations {
        assert_receipt_mutation_rejected(&original, COMPLETED, &context, mutation);
    }
}

fn assert_receipt_mutation_rejected(
    original: &Value,
    capture: &[u8],
    context: &TrustedAdaptationContextV0,
    mutation: &ReceiptMutation,
) {
    let mut mutated = original.clone();
    let target = mutation.path.iter().fold(&mut mutated, |value, key| {
        if let Ok(index) = key.parse::<usize>() {
            &mut value[index]
        } else {
            &mut value[*key]
        }
    });
    assert_ne!(*target, mutation.replacement, "{:?}", mutation.path);
    *target = mutation.replacement.clone();
    let encoded = serde_json::to_vec(&mutated).unwrap();
    match mutation.expected {
        ReceiptMutationOutcome::Import(code) => assert_eq!(
            InputAuthorityReceiptV0::from_json_slice(&encoded)
                .expect_err("declared import rejection")
                .code(),
            code,
            "{:?}",
            mutation.path
        ),
        ReceiptMutationOutcome::Adapt(code) => {
            let receipt = InputAuthorityReceiptV0::from_json_slice(&encoded)
                .expect("declared import success");
            assert_eq!(
                adapt_codex_exec_v0(capture, &receipt, context)
                    .expect_err("declared adaptation rejection")
                    .code(),
                code,
                "{:?}",
                mutation.path
            );
        }
    }
}

fn process_receipt_wire(bytes: &[u8], termination: Value) -> Value {
    let records = bytes
        .strip_suffix(b"\n")
        .unwrap()
        .split(|byte| *byte == b'\n')
        .collect::<Vec<_>>();
    let raw_seal = raw_capture_seal_v0(&records);
    let args: &[&[u8]] = &[
        b"codex",
        b"exec",
        b"--json",
        b"--ephemeral",
        b"--ignore-user-config",
        b"--ignore-rules",
        b"--skip-git-repo-check",
        b"--sandbox",
        b"read-only",
        b"-",
    ];
    json!({
        "authority":"process-capture",
        "receipt_format":"legitimacy.codex-exec-v0.process-capture-receipt",
        "receipt_version":"0",
        "evidence_class":"genuine-process-capture",
        "emitter":{
            "package_version":"0.144.0",
            "source_tag":"rust-v0.144.0",
            "source_tag_object_sha":"e0a9ff6938d85db1a7b11a693b6aa2bc31fe5a55",
            "source_commit_sha":"767822446c7a594caa19609ca435281a9ec67e0d"
        },
        "executable_sha256":"sha256:901923c1808a151f6926d41d703c17ad48815662cefb1c8d832a052c44271429",
        "executable_inode":{"dev":8,"ino":100},
        "executable_execution_binding":"fexecve-held-fd",
        "artifact_open_discipline":"held-fd-no-symlink",
        "workspace_execution_discipline":"held-read-only-during-exec",
        "argv":{
            "argument_count":args.len(),
            "arguments_lower_hex":args.iter().map(|arg| hex(arg)).collect::<Vec<_>>(),
            "total_bytes":args.iter().map(|arg| arg.len()).sum::<usize>()
        },
        "resolved_mode":"fresh-exec-structured-stdin",
        "capture_profile":"unix-read-only-stdin-json-v0",
        "stdin":{"presence":"present","byte_length":9,"sha256":standard_sha(b"synthetic")},
        "termination":termination,
        "stdout":{"byte_length":bytes.len(),"sha256":standard_sha(bytes)},
        "stderr":{"byte_length":0,"sha256":standard_sha(b"")},
        "raw_record_count":records.len(),
        "raw_capture_seal":raw_seal,
        "capture_tool":{
            "identity":legitimacy::trajectory::codex_exec_v0::codex_exec_capture_producer_binding_v0(),
            "file_sha256":standard_sha(b"synthetic capture tool"),
            "inode":{"dev":8,"ino":101}
        },
        "capture_profile_artifact":{
            "identity":"legitimacy.codex-exec-v0.capture-profile",
            "version":"0",
            "hash":legitimacy::trajectory::codex_exec_v0::codex_exec_capture_profile_binding_v0().hash
        },
        "workspace_manifest":[],
        "workspace_tree_digest":legitimacy::trajectory::codex_exec_v0::codex_exec_workspace_tree_digest_v0(&[]).unwrap(),
        "release_asset":{
            "name":"codex-x86_64-unknown-linux-musl.tar.gz",
            "sha256":"sha256:725883fc20ab4af3072829aaa0edf6d12c216238f9f7315a6656b950fb05c8bb"
        },
        "sigstore_bundle":{
            "name":"codex-x86_64-unknown-linux-musl.sigstore",
            "sha256":"sha256:73ee5b4cb99abfce4d7a03faf7b410b5d7c869a24b856bf23a5be031e619b4cd"
        },
        "sigstore_verification":"bundle-present-unverified",
        "asserted_nonce_source":"capture-random",
        "blinding_nonce_lower_hex":"77".repeat(32)
    })
}

fn standard_sha(bytes: &[u8]) -> String {
    format!("sha256:{:x}", Sha256::digest(bytes))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn zero_digest() -> &'static str {
    "sha256:0000000000000000000000000000000000000000000000000000000000000000"
}
