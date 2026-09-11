use super::*;
use crate::graph::node::peer_relative_rank_at_least_percentile;
use crate::{
    AgentActionEventV0, EvidenceV0, EvidencedV0, Gate, GateLogic, GovernanceNode,
    RawRecordReferenceV0, ReplayAuthoritySigningKeyV0, ReplayAuthorityTrustPolicyV0,
    SourceLocatorV0, TrajectoryTraceV0, TrajectoryValidationContextV0,
    UnverifiedReplayAuthorityReceiptV0, issue_trajectory_replay_authority_receipt_v0,
    raw_capture_seal_v0, raw_record_digest_v0, source_locator_digest_v0,
    trajectory_schema_binding_v0, verify_replay_authority_receipt_v0, verify_trajectory_replay_v0,
};
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet};
use syn::{Expr, Item, Stmt, Visibility};

const AUTHORITY_KEY: [u8; 32] = [0x31; 32];

fn binding(bytes: &[u8]) -> ArtifactBindingV0 {
    ArtifactBindingV0 {
        identity: TRAJECTORY_COMPOSITION_POLICY_ID_V0.to_string(),
        version: TRAJECTORY_COMPOSITION_POLICY_VERSION_V0.to_string(),
        hash: artifact_digest_v0(bytes),
    }
}

fn load(bytes: &[u8]) -> CompositionResultV0<ExecutableTrajectoryCompositionPolicyV0> {
    load_trajectory_composition_policy_v0(bytes, &binding(bytes))
}

#[test]
fn canonical_policy_compiles_exactly_one_peer_half_graph() {
    let executable = load(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0).unwrap();
    assert_eq!(
        executable.canonical_bytes(),
        TRAJECTORY_COMPOSITION_POLICY_BYTES_V0
    );
    assert_eq!(
        executable.artifact_digest(),
        artifact_digest_v0(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0)
    );
    assert_eq!(executable.graph().nodes.len(), 1);
    assert!(executable.graph().edges.is_empty());
    let node = executable.graph().nodes.values().next().unwrap();
    assert!(matches!(
        node,
        GovernanceNode::Binary {
            default: Decision::Deny,
            combination: GateLogic::FirstMatch,
            gates,
            ..
        } if matches!(gates.as_slice(), [Gate::PeerRelative {
            field,
            percentile,
            decision: Decision::Permit,
        }] if field == "strength" && *percentile == 0.5)
    ));
}

#[test]
fn selected_bounded_numeric_profile_matches_the_exact_half_criterion() {
    assert_eq!(0.5_f64.to_bits(), (1.0_f64 / 2.0).to_bits());
    for strength in 1_u64..=MAX_EVENTS_V0 as u64 {
        assert_eq!(strength as f64 as u64, strength);
    }
    for total in 1_usize..=MAX_EVENTS_V0 {
        assert_eq!(total as f64 as usize, total);
        for rank in 0_usize..=total {
            assert_eq!(rank as f64 as usize, rank);
            assert_eq!(
                peer_relative_rank_at_least_percentile(rank, total, 0.5),
                2 * rank >= total,
                "rank={rank}, total={total}"
            );
        }
    }
}

#[test]
fn production_peer_relative_evaluator_returns_the_bounded_helper_comparison() {
    let syntax = syn::parse_file(include_str!("../../graph/node.rs")).unwrap();
    let evaluator = top_level_function(&syntax, "evaluate_peer_relative");
    let helper = top_level_function(&syntax, "peer_relative_rank_at_least_percentile");

    assert!(matches!(helper.vis, Visibility::Restricted(ref visibility)
        if visibility.path.is_ident("crate")));
    assert!(
        helper
            .attrs
            .iter()
            .all(|attribute| !attribute.path().is_ident("cfg"))
    );

    let Some(Stmt::Expr(Expr::Call(ok_call), None)) = evaluator.block.stmts.last() else {
        panic!("evaluate_peer_relative must return the helper result directly");
    };
    assert!(expression_is_path(&ok_call.func, "Ok"));
    assert_eq!(ok_call.args.len(), 1);
    let Expr::Call(helper_call) = &ok_call.args[0] else {
        panic!("evaluate_peer_relative must wrap one direct helper call in Ok");
    };
    assert!(expression_is_path(
        &helper_call.func,
        "peer_relative_rank_at_least_percentile"
    ));
    assert_eq!(helper_call.args.len(), 3);
    assert!(expression_is_path(&helper_call.args[0], "less_or_equal"));
    assert!(matches!(&helper_call.args[1], Expr::MethodCall(call)
        if call.method == "len"
            && call.args.is_empty()
            && expression_is_path(&call.receiver, "values")));
    assert!(expression_is_path(&helper_call.args[2], "percentile"));
}

fn top_level_function<'a>(syntax: &'a syn::File, name: &str) -> &'a syn::ItemFn {
    syntax
        .items
        .iter()
        .find_map(|item| match item {
            Item::Fn(function) if function.sig.ident == name => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing top-level function {name}"))
}

fn expression_is_path(expression: &Expr, name: &str) -> bool {
    matches!(expression, Expr::Path(path)
        if path.path.leading_colon.is_none()
            && path.path.segments.len() == 1
            && path.path.is_ident(name))
}

#[test]
fn policy_byte_mutation_fails_at_digest_binding() {
    let mut mutated = TRAJECTORY_COMPOSITION_POLICY_BYTES_V0.to_vec();
    mutated[0] ^= 1;
    let error = load_trajectory_composition_policy_v0(
        &mutated,
        &binding(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0),
    )
    .unwrap_err();
    assert_eq!(
        error.code(),
        TrajectoryCompositionErrorCodeV0::PolicyDigestMismatch
    );
}

#[test]
fn equivalent_whitespace_and_numeric_spelling_are_noncanonical() {
    for mutated in [
        TRAJECTORY_COMPOSITION_POLICY_BYTES_V0
            .strip_suffix(b"\n")
            .unwrap()
            .to_vec(),
        String::from_utf8(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0.to_vec())
            .unwrap()
            .replace("percentile = 0.5", "percentile = 0.50")
            .strip_suffix('\n')
            .unwrap()
            .as_bytes()
            .to_vec(),
    ] {
        assert_eq!(
            load(&mutated).unwrap_err().code(),
            TrajectoryCompositionErrorCodeV0::NonCanonicalPolicy
        );
    }
}

#[test]
fn restricted_profile_rejects_graph_and_semantic_mutations() {
    for mutated in [
        replace("percentile = 0.5", "percentile = 0.6"),
        replace("decision = \"permit\"", "decision = \"deny\""),
        replace("default = \"deny\"", "default = \"no\""),
        replace("combination = \"first_match\"", "combination = \"any\""),
        replace(
            "name = \"trajectory-composition-peer-half\"",
            "name = \"unsupported\"",
        ),
    ] {
        assert_eq!(
            load(&mutated).unwrap_err().code(),
            TrajectoryCompositionErrorCodeV0::UnsupportedPolicyProfile
        );
    }
}

#[test]
fn restricted_profile_rejects_identity_and_version_mutations() {
    for mutated in [
        replace(
            TRAJECTORY_COMPOSITION_POLICY_FORMAT_V0,
            "unsupported.policy-format",
        ),
        replace(
            "policy_format_version = \"0\"",
            "policy_format_version = \"1\"",
        ),
        replace(OCCURRENCE_ENCODER_ID_V0, "unsupported.encoder"),
        replace(
            "occurrence_encoder_version = \"0\"",
            "occurrence_encoder_version = \"1\"",
        ),
        replace(HISTORICAL_PROPERTY_ID_V0, "unsupported.property"),
        replace(
            "historical_property_version = \"0\"",
            "historical_property_version = \"1\"",
        ),
    ] {
        assert_eq!(
            load(&mutated).unwrap_err().code(),
            TrajectoryCompositionErrorCodeV0::UnsupportedPolicyProfile
        );
    }
}

#[test]
fn trace_binding_identity_and_version_are_checked_separately() {
    let mut wrong_identity = binding(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0);
    wrong_identity.identity = "wrong-policy".to_string();
    assert_eq!(
        load_trajectory_composition_policy_v0(
            TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
            &wrong_identity,
        )
        .unwrap_err()
        .code(),
        TrajectoryCompositionErrorCodeV0::PolicyIdentityMismatch
    );

    let mut wrong_version = binding(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0);
    wrong_version.version = "1".to_string();
    assert_eq!(
        load_trajectory_composition_policy_v0(
            TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
            &wrong_version,
        )
        .unwrap_err()
        .code(),
        TrajectoryCompositionErrorCodeV0::PolicyVersionMismatch
    );
}

#[test]
fn unknown_and_missing_fields_fail_closed_without_echoing_input() {
    for mutated in [
        replace("policy_version = \"0\"", "unknown = \"secret\""),
        replace("historical_property_version = \"0\"\n", ""),
    ] {
        let error = load(&mutated).unwrap_err();
        assert_eq!(error.code(), TrajectoryCompositionErrorCodeV0::PolicyShape);
        assert_eq!(error.to_string(), "policy-shape");
        assert!(!error.to_string().contains("secret"));
    }
}

#[test]
fn replay_bound_encoding_preserves_every_occurrence_and_duplicate_source_ids() {
    let raw: Vec<&[u8]> = vec![
        br#"{"i":0}"#,
        br#"{"i":1}"#,
        br#"{"i":2}"#,
        br#"{"i":3}"#,
        br#"{"i":4}"#,
    ];
    let kinds = [
        NormalizedEventKindV0::ActionRequest,
        NormalizedEventKindV0::ActionResult,
        NormalizedEventKindV0::Observation,
        NormalizedEventKindV0::Message,
        NormalizedEventKindV0::Lifecycle,
    ];
    let (trace, declarations) = trace_fixture(&raw, &kinds, "event");
    let validated = trace.validate(&raw, &declarations).unwrap();
    let verified = verified_replay(&validated);
    let prepared = prepare_replay_bound_composition_v0(
        &validated,
        &verified,
        TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
    )
    .unwrap();

    assert_eq!(prepared.claims.len(), raw.len());
    assert_eq!(prepared.receipts.len(), raw.len());
    assert_eq!(
        prepared.trajectory_digest,
        verified.replay().trajectory_digest()
    );
    assert_eq!(prepared.replay_final_head, verified.replay().final_head());
    assert_eq!(
        prepared.policy.canonical_bytes(),
        TRAJECTORY_COMPOSITION_POLICY_BYTES_V0
    );
    for (index, receipt) in prepared.receipts.iter().enumerate() {
        assert_eq!(receipt.claim().occurrence_index(), index as u64);
        assert_eq!(
            receipt.claim().claimant_wire_id(),
            format!("occurrence:{index}")
        );
        assert_eq!(receipt.claim().strength_numerator(), index as u64 + 1);
        assert_eq!(receipt.claim().strength_denominator(), 1);
        assert_eq!(receipt.claim().event_id(), format!("event-{index}"));
        assert_eq!(receipt.claim().kind(), &kinds[index]);
        assert_eq!(receipt.claim().source_item_id(), Some("repeated-source"));
        assert_eq!(receipt.singleton_decision(), BinaryPolicyDecisionV0::Permit);
        assert_eq!(
            receipt.claim().canonical_event_digest(),
            verified.replay().records()[index].canonical_event_digest()
        );
    }
    let claim_ids = prepared
        .receipts
        .iter()
        .map(|receipt| receipt.claim().claimant_wire_id())
        .collect::<BTreeSet<_>>();
    assert_eq!(claim_ids.len(), raw.len());
}

#[test]
fn independently_valid_trace_and_replay_objects_must_match() {
    let raw: Vec<&[u8]> = vec![br#"{"i":0}"#, br#"{"i":1}"#];
    let kinds = [
        NormalizedEventKindV0::Observation,
        NormalizedEventKindV0::Message,
    ];
    let (left_trace, left_declarations) = trace_fixture(&raw, &kinds, "left");
    let (right_trace, right_declarations) = trace_fixture(&raw, &kinds, "right");
    let left_validated = left_trace.validate(&raw, &left_declarations).unwrap();
    let right_validated = right_trace.validate(&raw, &right_declarations).unwrap();
    let right_verified = verified_replay(&right_validated);

    assert_eq!(
        prepare_replay_bound_composition_v0(
            &left_validated,
            &right_verified,
            TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
        )
        .unwrap_err()
        .code(),
        TrajectoryCompositionErrorCodeV0::ReplayPairMismatch
    );
}

#[test]
fn evaluator_classifies_two_events_safe_and_three_events_at_2_3_0() {
    for (event_count, expected_kind) in [
        (2, TemporalCompositionKindV0::AllSingletonsPermitAndSafe),
        (
            3,
            TemporalCompositionKindV0::AllSingletonsPermitAndEarliestViolation,
        ),
    ] {
        let raw_storage = (0..event_count)
            .map(|index| format!("{{\"i\":{index}}}").into_bytes())
            .collect::<Vec<_>>();
        let raw = raw_storage.iter().map(Vec::as_slice).collect::<Vec<_>>();
        let kinds = (0..event_count)
            .map(|index| {
                if index % 2 == 0 {
                    NormalizedEventKindV0::Observation
                } else {
                    NormalizedEventKindV0::Message
                }
            })
            .collect::<Vec<_>>();
        let (trace, declarations) = trace_fixture(&raw, &kinds, "classification");
        let validated = trace.validate(&raw, &declarations).unwrap();
        let verified = verified_replay(&validated);
        let result = evaluate_replay_bound_composition_v0(
            &validated,
            &verified,
            TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
        )
        .unwrap();

        assert_eq!(result.temporal().kind(), expected_kind);
        assert!(
            result
                .event_receipts()
                .iter()
                .all(|receipt| receipt.singleton_decision() == BinaryPolicyDecisionV0::Permit)
        );
        assert_eq!(result.temporal().observed_prefixes().len(), event_count);
        if event_count == 2 {
            assert_eq!(result.temporal().transition_index(), None);
            assert!(result.temporal().observed_prefixes().iter().all(|prefix| {
                prefix.decision() == BinaryPolicyDecisionV0::Permit
                    && prefix.least_denied_occurrence_index().is_none()
            }));
        } else {
            assert_eq!(result.temporal().transition_index(), Some(2));
            assert_eq!(result.temporal().prefix_length(), Some(3));
            assert_eq!(result.temporal().denied_occurrence_index(), Some(0));
            assert_eq!(
                result
                    .temporal()
                    .observed_prefixes()
                    .get(2)
                    .unwrap()
                    .decision(),
                BinaryPolicyDecisionV0::Deny
            );
        }
        let bytes = result.to_json_line().unwrap();
        assert_eq!(bytes.last(), Some(&b'\n'));
        assert_eq!(bytes, result.to_json_line().unwrap());
        assert!(
            !bytes
                .windows(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0.len())
                .any(|window| window == TRAJECTORY_COMPOSITION_POLICY_BYTES_V0)
        );
    }
}

#[test]
fn multiple_denials_choose_the_least_occurrence() {
    let executable = load(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0).unwrap();
    let claims = (0..5)
        .map(|index| GovernanceClaim {
            claimant_id: format!("occurrence:{index}"),
            strength: (index + 1) as f64,
            priority_class: None,
            path: None,
            action: None,
            content: None,
            metrics: BTreeMap::new(),
        })
        .collect::<Vec<_>>();
    let decisions = traverse_final_decisions(executable.graph(), &claims).unwrap();
    assert_eq!(decisions["occurrence:0"], Decision::Deny);
    assert_eq!(decisions["occurrence:1"], Decision::Deny);
    assert_eq!(
        least_denied_occurrence_v0(&claims, &decisions).unwrap(),
        Some(0)
    );
}

#[test]
fn local_failure_is_never_composition_failure() {
    let raw: Vec<&[u8]> = vec![br#"{"i":0}"#, br#"{"i":1}"#];
    let kinds = [
        NormalizedEventKindV0::Observation,
        NormalizedEventKindV0::Message,
    ];
    let (trace, declarations) = trace_fixture(&raw, &kinds, "local");
    let validated = trace.validate(&raw, &declarations).unwrap();
    let verified = verified_replay(&validated);
    let mut prepared = prepare_replay_bound_composition_v0(
        &validated,
        &verified,
        TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
    )
    .unwrap();
    prepared.receipts.first_mut().unwrap().singleton_decision = BinaryPolicyDecisionV0::Deny;

    let temporal = classify_temporal_composition_v0(&prepared).unwrap();
    assert_eq!(temporal.kind(), TemporalCompositionKindV0::LocalFailure);
    assert_eq!(temporal.local_failure_occurrence_index(), Some(0));
    assert!(temporal.observed_prefixes().is_empty());
    assert_eq!(temporal.transition_index(), None);
}

fn replace(from: &str, to: &str) -> Vec<u8> {
    String::from_utf8(TRAJECTORY_COMPOSITION_POLICY_BYTES_V0.to_vec())
        .unwrap()
        .replace(from, to)
        .into_bytes()
}

fn trace_fixture(
    raw: &[&[u8]],
    kinds: &[NormalizedEventKindV0],
    event_prefix: &str,
) -> (TrajectoryTraceV0, TrajectoryValidationContextV0) {
    assert_eq!(raw.len(), kinds.len());
    let adapter = artifact_binding("adapter.trajectory-composition-fixture", "0", b"adapter");
    let policy = artifact_binding(
        TRAJECTORY_COMPOSITION_POLICY_ID_V0,
        TRAJECTORY_COMPOSITION_POLICY_VERSION_V0,
        TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,
    );
    let raw_capture = raw_capture_seal_v0(raw);
    let events = raw
        .iter()
        .zip(kinds)
        .enumerate()
        .map(|(index, (record, kind))| {
            let locator = SourceLocatorV0 {
                record_index: index as u64,
                byte_offset: 0,
                byte_length: record.len() as u64,
                digest: source_locator_digest_v0(record),
            };
            AgentActionEventV0 {
                event_id: cited(format!("{event_prefix}-{index}"), locator.clone()),
                sequence_index: cited(index as u64, locator.clone()),
                kind: cited(kind.clone(), locator.clone()),
                source_item_id: Some(cited("repeated-source".to_string(), locator.clone())),
                raw_record: RawRecordReferenceV0 {
                    record_index: index as u64,
                    digest: raw_record_digest_v0(record),
                },
                payload: BTreeMap::new(),
            }
        })
        .collect();
    let run_locator = SourceLocatorV0 {
        record_index: 0,
        byte_offset: 0,
        byte_length: raw[0].len() as u64,
        digest: source_locator_digest_v0(raw[0]),
    };
    let trace = TrajectoryTraceV0 {
        schema: trajectory_schema_binding_v0(),
        run_id: cited("composition-fixture".to_string(), run_locator),
        adapter: adapter.clone(),
        policy: policy.clone(),
        raw_capture: raw_capture.clone(),
        events,
    };
    let declarations = TrajectoryValidationContextV0 {
        adapter,
        policy,
        raw_capture,
        allowed_derivations: BTreeSet::new(),
    };
    (trace, declarations)
}

fn cited<T>(value: T, locator: SourceLocatorV0) -> EvidencedV0<T> {
    EvidencedV0 {
        value: Some(value),
        evidence: EvidenceV0::CitesRawRange { locator },
    }
}

fn artifact_binding(identity: &str, version: &str, bytes: &[u8]) -> ArtifactBindingV0 {
    ArtifactBindingV0 {
        identity: identity.to_string(),
        version: version.to_string(),
        hash: artifact_digest_v0(bytes),
    }
}

fn verified_replay(validated: &ValidatedTrajectoryTraceV0<'_>) -> VerifiedTrajectoryReplayV0 {
    let signing_key = ReplayAuthoritySigningKeyV0::from_bytes(&AUTHORITY_KEY).unwrap();
    let signed = issue_trajectory_replay_authority_receipt_v0(
        validated,
        &signing_key,
        "trajectory.composition.test-authority",
        "trajectory-composition-test-key",
        1,
    )
    .unwrap();
    let unverified =
        UnverifiedReplayAuthorityReceiptV0::from_json_slice(&signed.to_json_line().unwrap())
            .unwrap();
    let mut trust_bytes = serde_json::to_vec(&json!({
        "trust_policy_format": "legitimacy.trajectory.replay-authority-trust-policy",
        "trust_policy_version": "0",
        "issuer": "trajectory.composition.test-authority",
        "algorithm": "ed25519",
        "key_id": "trajectory-composition-test-key",
        "accepted_authority_epoch": 1,
        "verification_key": signing_key.verification_key_text(),
    }))
    .unwrap();
    trust_bytes.push(b'\n');
    let trust = ReplayAuthorityTrustPolicyV0::from_json_slice(&trust_bytes).unwrap();
    let authority = verify_replay_authority_receipt_v0(unverified, &trust).unwrap();
    let candidate = trajectory_replay_candidate_v0(validated);
    let inspected = super::super::InspectedTrajectoryReplayCandidateV0::from_json_slice(
        &candidate.to_json_line().unwrap(),
    )
    .unwrap();
    verify_trajectory_replay_v0(validated, &inspected, &authority).unwrap()
}
