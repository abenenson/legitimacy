use super::*;

pub(super) fn verify_trajectory_route(source: &str) -> Result<(), &'static str> {
    // This is an independent seal of the exact reviewed route, not a claim
    // that this test implements a general Rust call-graph analysis.
    if source_sha256(source) != EXPECTED_TRAJECTORY_SOURCE_SHA256 {
        return Err("route-source");
    }
    verify_trajectory_route_shape(source)
}

pub(super) fn verify_trajectory_route_shape(source: &str) -> Result<(), &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "route-shape")?;
    let imports = flattened_imports_from_syntax(&syntax)?;
    let first_party = imports
        .into_iter()
        .filter(|path| path.starts_with("legitimacy::"))
        .collect::<BTreeSet<_>>();
    let expected_imports = BTreeSet::from([
        "legitimacy::trajectory::codex_exec_v0::AdapterErrorCodeV0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::AdapterErrorV0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::InputAuthorityReceiptV0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::InspectedShareableSanitizedBundleV0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::MAX_ADAPTER_BUNDLE_BYTES_V0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::MAX_AUTHORITY_RECEIPT_BYTES_V0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::MAX_CODEX_JSONL_BYTES_V0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0"
            .to_string(),
        "legitimacy::trajectory::codex_exec_v0::MAX_TRUSTED_CONTEXT_BYTES_V0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::OwnerPrivateLineageSidecarV0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::TrustedAdaptationContextV0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::adapt_codex_exec_owned_v0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::sanitize_capture_v0".to_string(),
    ]);
    if first_party != expected_imports {
        return Err("route-shape");
    }
    if identifier_count(source, "adapt_codex_exec_owned_v0") != 2 {
        return Err("route-shape");
    }
    if identifier_count(source, "sanitize_capture_v0") != 2
        || identifier_count(source, "sanitize_capture_with_fixed_test_nonce_v0") != 0
    {
        return Err("route-shape");
    }

    let mut parser = rust_parser();
    let tree = parser.parse(source, None).ok_or("route-shape")?;
    if tree.root_node().has_error() {
        return Err("route-shape");
    }
    let calls = call_name_counts(tree.root_node(), source.as_bytes());
    let expected_calls = EXPECTED_TRAJECTORY_CALLS
        .iter()
        .map(|(call, count)| ((*call).to_string(), *count))
        .collect();
    if calls != expected_calls
        || direct_call_argument_profiles(source, "linux_output::publish")?
            != vec![compact_profile(&[
                "output",
                "&bytes",
                "&[&raw, &receipt, &context]",
            ])]
        || direct_call_argument_profiles(source, "linux_output::publish_pair")?
            != vec![compact_profile(&[
                "sidecar_output",
                "&sidecar_bytes",
                "output",
                "&public_bytes",
                "&[&raw, &receipt, &context]",
                "|| validate_semantic_pair(&sidecar_bytes, &public_bytes)",
            ])]
        || direct_call_argument_profiles(source, "validate_semantic_pair")?
            != vec![compact_profile(&["&sidecar_bytes", "&public_bytes"])]
    {
        return Err("route-shape");
    }
    Ok(())
}

pub(super) fn verify_composition_route(source: &str) -> Result<(), &'static str> {
    if source_sha256(source) != EXPECTED_COMPOSITION_SOURCE_SHA256 {
        return Err("route-source");
    }
    verify_composition_route_shape(source)
}

pub(super) fn verify_composition_route_shape(source: &str) -> Result<(), &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "route-shape")?;
    let imports = flattened_imports_from_syntax(&syntax)?;
    let first_party = imports
        .iter()
        .filter(|path| path.starts_with("legitimacy::"))
        .cloned()
        .collect::<BTreeSet<_>>();
    let expected_first_party = BTreeSet::from([
        "legitimacy::InspectedTrajectoryReplayCandidateV0".to_string(),
        "legitimacy::ReplayAuthorityErrorV0".to_string(),
        "legitimacy::ReplayAuthorityTrustPolicyV0".to_string(),
        "legitimacy::ReplayErrorV0".to_string(),
        "legitimacy::TrajectoryCompositionErrorV0".to_string(),
        "legitimacy::UnverifiedReplayAuthorityReceiptV0".to_string(),
        "legitimacy::evaluate_replay_bound_composition_v0".to_string(),
        "legitimacy::trajectory::MAX_TRAJECTORY_COMPOSITION_POLICY_BYTES_V0".to_string(),
        "legitimacy::trajectory::MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0".to_string(),
        "legitimacy::trajectory::MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0".to_string(),
        "legitimacy::trajectory::MAX_TRAJECTORY_REPLAY_BYTES_V0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::AdapterErrorV0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::InputAuthorityReceiptV0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::InspectedShareableSanitizedBundleV0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::MAX_ADAPTER_BUNDLE_BYTES_V0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::MAX_AUTHORITY_RECEIPT_BYTES_V0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::MAX_CODEX_JSONL_BYTES_V0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0"
            .to_string(),
        "legitimacy::trajectory::codex_exec_v0::MAX_TRUSTED_CONTEXT_BYTES_V0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::OwnerPrivateLineageSidecarV0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::TrustedAdaptationContextV0".to_string(),
        "legitimacy::trajectory::codex_exec_v0::adapt_codex_exec_owned_v0".to_string(),
        "legitimacy::verify_replay_authority_receipt_v0".to_string(),
        "legitimacy::verify_trajectory_replay_v0".to_string(),
    ]);
    if first_party != expected_first_party
        || ![
            "crate::trajectory::PublicationSpecV0",
            "crate::trajectory::publish_directory_set",
            "crate::trajectory::publish_set",
            "crate::trajectory::read_snapshot",
            "crate::trajectory::reject_duplicate_inodes",
        ]
        .iter()
        .all(|required| imports.contains(*required))
    {
        return Err("route-shape");
    }
    for forbidden in [
        "TrajectoryTraceV0",
        "TrajectoryValidationContextV0",
        "DeclaredTrajectoryValidationContextV0",
        "ExactRawRecordSetV0",
        "NormalizedEventV0",
        "NormalizedEventKindV0",
        "trajectory_replay_candidate_v0",
        "evaluate_trajectory_composition_v0",
        "expected_result",
        "expected_receipt",
        "adapt_codex_exec_v0",
        "caller_validated",
    ] {
        if identifier_count(source, forbidden) != 0 {
            return Err("route-shape");
        }
    }
    if source.contains("move ||") {
        return Err("route-shape");
    }
    if identifier_count(source, "adapt_codex_exec_owned_v0") != 2
        || identifier_count(source, "with_validated") != 2
        || direct_call_argument_profiles(source, "InputAuthorityReceiptV0::from_json_slice")?
            != vec![compact_profile(&["&input_receipt.bytes"])]
        || direct_call_argument_profiles(source, "TrustedAdaptationContextV0::from_json_slice")?
            != vec![compact_profile(&["&adaptation_context.bytes"])]
        || direct_call_argument_profiles(source, "adapt_codex_exec_owned_v0")?
            != vec![compact_profile(&[
                "std::mem::take(&mut *raw.bytes)",
                "&authority",
                "&context",
            ])]
        || direct_call_argument_profiles(
            source,
            "InspectedShareableSanitizedBundleV0::from_json_slice",
        )? != vec![compact_profile(&["&public_bundle.bytes"])]
        || direct_call_argument_profiles(source, "read_snapshot")?
            != vec![
                compact_profile(&["inputs.raw_stdout_jsonl", "MAX_CODEX_JSONL_BYTES_V0"]),
                compact_profile(&["path", "MAX_AUTHORITY_RECEIPT_BYTES_V0"]),
                compact_profile(&["path", "MAX_TRUSTED_CONTEXT_BYTES_V0"]),
                compact_profile(&["path", "MAX_ADAPTER_BUNDLE_BYTES_V0"]),
                compact_profile(&["path", "MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0"]),
                compact_profile(&["inputs.replay_candidate", "MAX_TRAJECTORY_REPLAY_BYTES_V0"]),
                compact_profile(&[
                    "inputs.replay_authority_receipt",
                    "MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0",
                ]),
                compact_profile(&[
                    "inputs.replay_authority_trust_policy",
                    "MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0",
                ]),
                compact_profile(&[
                    "inputs.composition_policy",
                    "MAX_TRAJECTORY_COMPOSITION_POLICY_BYTES_V0",
                ]),
            ]
        || direct_call_argument_profiles(source, "reject_duplicate_inodes")?
            != vec![compact_profile(&["&input_snapshots"])]
        || direct_call_argument_profiles(source, "materialize")?.len() != 2
        || direct_call_argument_profiles(
            source,
            "InspectedTrajectoryReplayCandidateV0::from_json_slice",
        )? != vec![compact_profile(&["replay"])]
        || direct_call_argument_profiles(
            source,
            "UnverifiedReplayAuthorityReceiptV0::from_json_slice",
        )? != vec![compact_profile(&["replay_receipt"])]
        || direct_call_argument_profiles(source, "ReplayAuthorityTrustPolicyV0::from_json_slice")?
            != vec![compact_profile(&["replay_trust"])]
        || direct_call_argument_profiles(source, "verify_replay_authority_receipt_v0")?
            != vec![compact_profile(&["unverified", "&trust_policy"])]
        || direct_call_argument_profiles(source, "verify_trajectory_replay_v0")?
            != vec![compact_profile(&["validated", "&inspected", "&authorized"])]
        || direct_call_argument_profiles(source, "evaluate_replay_bound_composition_v0")?
            != vec![compact_profile(&["validated", "&verified", "policy"])]
        || direct_call_argument_profiles(source, "publish_directory_set")?
            != vec![compact_profile(&[
                "output_set",
                "&[(\"trace.json\", materialized.trace.as_slice()), (\"canonical-trace.bin\", materialized.canonical_trace.as_slice(),), (\"composition-result.json\", materialized.result.as_slice()),]",
                "&snapshots",
                "|| Ok(())",
            ])]
        || direct_call_argument_profiles(source, "publish_set")?
            != vec![compact_profile(&[
                "&[PublicationSpecV0 { output: trace, bytes: &materialized.trace, }, PublicationSpecV0 { output: canonical_trace, bytes: &materialized.canonical_trace, }, PublicationSpecV0 { output: result, bytes: &materialized.result, },]",
                "&snapshots",
                "|| Ok(())",
            ])]
        || !direct_call_argument_profiles(source, "publish")?.is_empty()
    {
        return Err("route-shape");
    }

    let compact = compact_source(source);
    ordered_unique_fragments(
        &compact,
        &[
            "letmutraw=read_snapshot(inputs.raw_stdout_jsonl,MAX_CODEX_JSONL_BYTES_V0).map_err(adapter_code)?;",
            "letinput_receipt=inputs.input_authority_receipt.map(|path|read_snapshot(path,MAX_AUTHORITY_RECEIPT_BYTES_V0)).transpose().map_err(adapter_code)?;",
            "letadaptation_context=inputs.trusted_adaptation_context.map(|path|read_snapshot(path,MAX_TRUSTED_CONTEXT_BYTES_V0)).transpose().map_err(adapter_code)?;",
            "letpublic_bundle=inputs.shareable_sanitized_bundle.map(|path|read_snapshot(path,MAX_ADAPTER_BUNDLE_BYTES_V0)).transpose().map_err(adapter_code)?;",
            "letprivate_lineage=inputs.private_lineage_sidecar.map(|path|read_snapshot(path,MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0)).transpose().map_err(adapter_code)?;",
            "letreplay=read_snapshot(inputs.replay_candidate,MAX_TRAJECTORY_REPLAY_BYTES_V0).map_err(adapter_code)?;",
            "letreplay_receipt=read_snapshot(inputs.replay_authority_receipt,MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0,).map_err(adapter_code)?;",
            "letreplay_trust=read_snapshot(inputs.replay_authority_trust_policy,MAX_TRAJECTORY_REPLAY_AUTHORITY_TRUST_POLICY_BYTES_V0,).map_err(adapter_code)?;",
            "letpolicy=read_snapshot(inputs.composition_policy,MAX_TRAJECTORY_COMPOSITION_POLICY_BYTES_V0,).map_err(adapter_code)?;",
            "reject_duplicate_inodes(&input_snapshots).map_err(adapter_code)?;",
            "reject_output_aliases(outputs).map_err(adapter_code)?;",
            "letmaterialized=match(input_receipt.as_ref(),adaptation_context.as_ref(),public_bundle.as_ref(),){",
            "(Some(input_receipt),Some(adaptation_context),None)=>{",
            "letauthority=InputAuthorityReceiptV0::from_json_slice(&input_receipt.bytes).map_err(adapter_code)?;",
            "letcontext=TrustedAdaptationContextV0::from_json_slice(&adaptation_context.bytes).map_err(adapter_code)?;",
            "letadapted=adapt_codex_exec_owned_v0(std::mem::take(&mut*raw.bytes),&authority,&context,).map_err(adapter_code)?;",
            "adapted.with_validated(|validated|{materialize(validated,&replay.bytes,&replay_receipt.bytes,&replay_trust.bytes,&policy.bytes,)}).map_err(adapter_code)??",
            "(None,None,Some(public_bundle))=>{",
            "letinspected=InspectedShareableSanitizedBundleV0::from_json_slice(&public_bundle.bytes).map_err(adapter_code)?;",
            "sidecar.revalidate_public_bundle_for_jsonl(inspected,&raw.bytes).map_err(adapter_code)?",
            "inspected.revalidate_public_projection(&raw.bytes).map_err(adapter_code)?",
            "revalidated.with_validated(|validated|{materialize(validated,&replay.bytes,&replay_receipt.bytes,&replay_trust.bytes,&policy.bytes,)}).map_err(adapter_code)??",
            "letmutsnapshots=vec![&raw,&replay,&replay_receipt,&replay_trust,&policy];snapshots.extend(input_receipt.iter());snapshots.extend(adaptation_context.iter());snapshots.extend(public_bundle.iter());snapshots.extend(private_lineage.iter());",
            "(Some(output_set),None,None,None)=>publish_directory_set(",
            "(None,Some(trace),Some(canonical_trace),Some(result))=>publish_set(",
            "letinspected=InspectedTrajectoryReplayCandidateV0::from_json_slice(replay).map_err(replay_code)?;",
            "letunverified=UnverifiedReplayAuthorityReceiptV0::from_json_slice(replay_receipt).map_err(authority_code)?;",
            "lettrust_policy=ReplayAuthorityTrustPolicyV0::from_json_slice(replay_trust).map_err(authority_code)?;",
            "letauthorized=verify_replay_authority_receipt_v0(unverified,&trust_policy).map_err(authority_code)?;",
            "letverified=verify_trajectory_replay_v0(validated,&inspected,&authorized).map_err(replay_code)?;",
            "letresult=evaluate_replay_bound_composition_v0(validated,&verified,policy).map_err(composition_code)?;",
            "trace:validated.to_compact_json().map_err(|_|\"validation\")?,",
            "canonical_trace:validated.canonical_bytes(),",
            "result:result.to_json_line().map_err(composition_code)?,",
        ],
    )?;
    Ok(())
}

#[rustfmt::skip]
pub(super) fn composition_route_mutants(source: &str) -> Vec<(&'static str, String)> {
    let mut mutants = vec![
        ("raw snapshot substituted", mutate_direct_call_argument(source, "read_snapshot", 0, 0, "inputs.replay_candidate")),
        ("input receipt snapshot substituted", mutate_direct_call_argument(source, "read_snapshot", 1, 0, "inputs.replay_candidate")),
        ("adaptation context snapshot substituted", mutate_direct_call_argument(source, "read_snapshot", 2, 0, "inputs.replay_candidate")),
        ("public bundle snapshot substituted", mutate_direct_call_argument(source, "read_snapshot", 3, 0, "inputs.replay_candidate")),
        ("private lineage snapshot substituted", mutate_direct_call_argument(source, "read_snapshot", 4, 0, "inputs.replay_candidate")),
        ("replay snapshot substituted", mutate_direct_call_argument(source, "read_snapshot", 5, 0, "inputs.raw_stdout_jsonl")),
        ("replay receipt snapshot substituted", mutate_direct_call_argument(source, "read_snapshot", 6, 0, "inputs.replay_candidate")),
        ("replay trust snapshot substituted", mutate_direct_call_argument(source, "read_snapshot", 7, 0, "inputs.replay_candidate")),
        ("composition policy snapshot substituted", mutate_direct_call_argument(source, "read_snapshot", 8, 0, "inputs.replay_candidate")),
        ("inode rejection removed", replace_exact_once(source, "reject_duplicate_inodes(&input_snapshots)", "bypass_duplicate_inodes(&input_snapshots)")),
        ("output alias rejection removed", replace_exact_once(source, "reject_output_aliases(outputs)", "bypass_output_aliases(outputs)")),
        ("private receipt parser substituted", replace_exact_once(source, "InputAuthorityReceiptV0::from_json_slice", "UncheckedAuthorityReceipt::from_json_slice")),
        ("private adapter substituted", replace_exact_nth(source, "adapt_codex_exec_owned_v0", 2, 1, "adapt_unchecked_owned_v0")),
        ("public bundle parser substituted", replace_exact_once(source, "InspectedShareableSanitizedBundleV0::from_json_slice", "UncheckedShareableBundle::from_json_slice")),
        ("public projection revalidation removed", replace_exact_once(source, "revalidate_public_projection", "accept_public_projection")),
        ("private lineage child match removed", replace_exact_once(source, "revalidate_public_bundle_for_jsonl", "revalidate_public_bundle")),
        ("private validated scope removed", replace_exact_nth(source, "with_validated", 2, 0, "without_validation")),
        ("public validated scope removed", replace_exact_nth(source, "with_validated", 2, 1, "without_validation")),
        ("replay candidate inspection removed", replace_exact_once(source, "InspectedTrajectoryReplayCandidateV0::from_json_slice", "UncheckedReplayCandidate::from_json_slice")),
        ("replay receipt inspection removed", replace_exact_once(source, "UnverifiedReplayAuthorityReceiptV0::from_json_slice", "UncheckedReplayReceipt::from_json_slice")),
        ("replay trust inspection removed", replace_exact_once(source, "ReplayAuthorityTrustPolicyV0::from_json_slice", "UncheckedReplayTrust::from_json_slice")),
        ("replay authority verification removed", replace_exact_nth(source, "verify_replay_authority_receipt_v0", 2, 1, "accept_replay_authority_receipt_v0")),
        ("adapter-owned replay verification removed", replace_exact_nth(source, "verify_trajectory_replay_v0", 2, 1, "accept_trajectory_replay_v0")),
        ("composition evaluator substituted", replace_exact_nth(source, "evaluate_replay_bound_composition_v0", 2, 1, "evaluate_trajectory_composition_v0")),
        ("composition policy substituted", mutate_direct_call_argument(source, "evaluate_replay_bound_composition_v0", 0, 2, "attacker_policy")),
        ("official trace serialization removed", replace_exact_once(source, "validated.to_compact_json()", "validated.to_unchecked_json()")),
        ("canonical trace serialization removed", replace_exact_once(source, "validated.canonical_bytes()", "validated.unchecked_bytes()")),
        ("result serialization removed", replace_exact_once(source, "result.to_json_line()", "result.to_unchecked_json_line()")),
        ("directory set publication removed", replace_exact_nth(source, "publish_directory_set", 2, 1, "publish_directory_unchecked")),
        ("legacy set publication removed", replace_exact_nth(source, "publish_set", 2, 1, "publish_individually")),
        ("trace publication bytes substituted", replace_exact_once(source, "bytes: &materialized.trace", "bytes: &replay.bytes")),
        ("canonical publication bytes substituted", replace_exact_once(source, "bytes: &materialized.canonical_trace", "bytes: &replay.bytes")),
        ("result publication bytes substituted", replace_exact_once(source, "bytes: &materialized.result", "bytes: &replay.bytes")),
    ];
    mutants.extend(composition_scope_and_order_mutants(source));
    mutants.retain(|(_, mutation)| mutation != source);
    mutants
}

#[rustfmt::skip]
fn composition_scope_and_order_mutants(source: &str) -> Vec<(&'static str, String)> {
    let swap = |left: &str, right: &str| replace_exact_once(&replace_exact_once(&replace_exact_once(source, left, "__COMPOSITION_ROUTE_SWAP__"), right, left), "__COMPOSITION_ROUTE_SWAP__", right);
    let mut mutants = Vec::new();
    mutants.extend([
        (
            "snapshot order changed",
            swap(
                "        let replay = read_snapshot(inputs.replay_candidate, MAX_TRAJECTORY_REPLAY_BYTES_V0)\n            .map_err(adapter_code)?;\n",
                "        let replay_receipt = read_snapshot(\n            inputs.replay_authority_receipt,\n            MAX_TRAJECTORY_REPLAY_AUTHORITY_RECEIPT_BYTES_V0,\n        )\n        .map_err(adapter_code)?;\n",
            ),
        ),
        (
            "typed input authority parser substituted",
            replace_exact_once(source, "InputAuthorityReceiptV0::from_json_slice", "GenericAuthorityReceipt::from_json_slice"),
        ),
        (
            "trusted adaptation context parser substituted",
            replace_exact_once(source, "TrustedAdaptationContextV0::from_json_slice", "GenericValidationContext::from_json_slice"),
        ),
        (
            "authority and context parsing reordered",
            swap(
                "                let authority = InputAuthorityReceiptV0::from_json_slice(&input_receipt.bytes)\n                    .map_err(adapter_code)?;\n",
                "                let context =\n                    TrustedAdaptationContextV0::from_json_slice(&adaptation_context.bytes)\n                        .map_err(adapter_code)?;\n",
            ),
        ),
        (
            "adapter raw input substituted",
            mutate_direct_call_argument(source, "adapt_codex_exec_owned_v0", 0, 0, "replay.bytes.to_vec()"),
        ),
        (
            "adapter entry duplicated",
            replace_exact_once(
                source,
                "                let adapted = adapt_codex_exec_owned_v0(\n                    std::mem::take(&mut *raw.bytes),\n                    &authority,\n                    &context,\n                )\n                .map_err(adapter_code)?;",
                "                let adapted = adapt_codex_exec_owned_v0(\n                    std::mem::take(&mut *raw.bytes),\n                    &authority,\n                    &context,\n                )\n                .map_err(adapter_code)?;\n                let adapted = adapt_codex_exec_owned_v0(Vec::new(), &authority, &context)\n                    .map_err(adapter_code)?;",
            ),
        ),
        (
            "validated scope made escaping",
            replace_exact_once(source, "                adapted\n                    .with_validated(|validated| {", "                move || adapted\n                    .with_validated(|validated| {"),
        ),
        (
            "replay candidate inspection removed",
            replace_exact_once(source, "InspectedTrajectoryReplayCandidateV0::from_json_slice", "UncheckedReplayCandidate::from_json_slice"),
        ),
        (
            "replay receipt inspection removed",
            replace_exact_once(source, "UnverifiedReplayAuthorityReceiptV0::from_json_slice", "UncheckedReplayReceipt::from_json_slice"),
        ),
        (
            "replay trust inspection removed",
            replace_exact_once(source, "ReplayAuthorityTrustPolicyV0::from_json_slice", "UncheckedReplayTrust::from_json_slice"),
        ),
        (
            "replay inspections reordered",
            swap(
                "    let inspected =\n        InspectedTrajectoryReplayCandidateV0::from_json_slice(replay).map_err(replay_code)?;\n",
                "    let unverified = UnverifiedReplayAuthorityReceiptV0::from_json_slice(replay_receipt)\n        .map_err(authority_code)?;\n",
            ),
        ),
        (
            "replay authority verification removed",
            replace_exact_once(source, "verify_replay_authority_receipt_v0(unverified, &trust_policy)", "accept_replay_authority_receipt_v0(unverified, &trust_policy)"),
        ),
        (
            "replay authority trust substituted",
            mutate_direct_call_argument(source, "verify_replay_authority_receipt_v0", 0, 1, "&attacker_trust_policy"),
        ),
        (
            "adapter-owned replay verification removed",
            replace_exact_once(source, "verify_trajectory_replay_v0(validated, &inspected, &authorized)", "accept_trajectory_replay_v0(validated, &inspected, &authorized)"),
        ),
        (
            "replay verification trace substituted",
            mutate_direct_call_argument(source, "verify_trajectory_replay_v0", 0, 0, "caller_validated"),
        ),
        (
            "replay verification duplicated",
            replace_exact_once(
                source,
                "    let verified =\n        verify_trajectory_replay_v0(validated, &inspected, &authorized).map_err(replay_code)?;",
                "    let verified =\n        verify_trajectory_replay_v0(validated, &inspected, &authorized).map_err(replay_code)?;\n    let verified = verify_trajectory_replay_v0(validated, &inspected, &authorized)\n        .map_err(replay_code)?;",
            ),
        ),
        (
            "composition evaluator substituted",
            replace_exact_once(source, "evaluate_replay_bound_composition_v0(validated", "evaluate_trajectory_composition_v0(validated"),
        ),
        (
            "composition trace substituted",
            mutate_direct_call_argument(source, "evaluate_replay_bound_composition_v0", 0, 0, "caller_validated"),
        ),
        (
            "canonical result serialization removed",
            replace_exact_once(source, ".to_json_line()", ".to_unchecked_json_line()"),
        ),
        (
            "publication provenance omits policy",
            replace_exact_once(source, "        let mut snapshots = vec![&raw, &replay, &replay_receipt, &replay_trust, &policy];", "        let mut snapshots = vec![&raw, &replay, &replay_receipt, &replay_trust];"),
        ),
        (
            "publication provenance reordered",
            replace_exact_once(source, "        let mut snapshots = vec![&raw, &replay, &replay_receipt, &replay_trust, &policy];", "        let mut snapshots = vec![&replay, &raw, &replay_receipt, &replay_trust, &policy];"),
        ),
    ]);
    mutants
}

pub(super) fn verify_linux_path_route(source: &str) -> Result<(), &'static str> {
    if source_sha256(source) != EXPECTED_LINUX_PATH_SOURCE_SHA256 {
        return Err("route-source");
    }
    verify_linux_path_route_shape(source)
}

pub(super) fn verify_linux_path_route_shape(source: &str) -> Result<(), &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "route-shape")?;
    let imports = flattened_imports_from_syntax(&syntax)?;
    let first_party = imports
        .into_iter()
        .filter(|path| path.starts_with("legitimacy::"))
        .collect::<BTreeSet<_>>();
    if first_party
        != BTreeSet::from([
            "legitimacy::trajectory::codex_exec_v0::AdapterErrorCodeV0".to_string(),
            "legitimacy::trajectory::codex_exec_v0::AdapterErrorV0".to_string(),
        ])
    {
        return Err("route-shape");
    }
    verify_linux_path_test_module_edge(source).map_err(|_| "route-shape")?;
    verify_linux_path_forbidden_shortcuts(source)?;

    let mut parser = rust_parser();
    let tree = parser.parse(source, None).ok_or("route-shape")?;
    if tree.root_node().has_error() {
        return Err("route-shape");
    }
    let calls = call_name_counts(tree.root_node(), source.as_bytes());
    let expected = EXPECTED_LINUX_PATH_CALLS
        .iter()
        .map(|(call, count)| ((*call).to_string(), *count))
        .collect();
    if calls != expected {
        return Err("route-shape");
    }
    if direct_call_argument_profiles(source, "openat")? != expected_openat_profiles()
        || direct_call_argument_profiles(source, "statat")? != expected_statat_profiles()
    {
        return Err("route-shape");
    }
    Ok(())
}

pub(super) fn verify_linux_output_route(source: &str) -> Result<(), &'static str> {
    if source_sha256(source) != EXPECTED_LINUX_OUTPUT_SOURCE_SHA256 {
        return Err("route-source");
    }
    verify_linux_output_route_shape(source)
}

pub(super) fn verify_linux_output_route_shape(source: &str) -> Result<(), &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "route-shape")?;
    let imports = flattened_imports_from_syntax(&syntax)?;
    let first_party = imports
        .into_iter()
        .filter(|path| path.starts_with("legitimacy::"))
        .collect::<BTreeSet<_>>();
    if first_party
        != BTreeSet::from([
            "legitimacy::trajectory::codex_exec_v0::AdapterErrorCodeV0".to_string(),
            "legitimacy::trajectory::codex_exec_v0::AdapterErrorV0".to_string(),
        ])
    {
        return Err("route-shape");
    }
    verify_linux_output_module_edges(source).map_err(|_| "route-shape")?;
    verify_linux_output_forbidden_shortcuts(source)?;
    verify_linux_output_publication_order(source)?;

    let mut parser = rust_parser();
    let tree = parser.parse(source, None).ok_or("route-shape")?;
    if tree.root_node().has_error() {
        return Err("route-shape");
    }
    let calls = call_name_counts(tree.root_node(), source.as_bytes());
    let expected = EXPECTED_LINUX_OUTPUT_CALLS
        .iter()
        .map(|(call, count)| ((*call).to_string(), *count))
        .collect();
    if calls != expected
        || direct_call_argument_profiles(source, "openat")? != expected_output_openat_profiles()
        || direct_call_argument_profiles(source, "statat")? != expected_output_statat_profiles()
        || direct_call_argument_profiles(source, "linkat")? != expected_output_linkat_profiles()
        || !direct_call_argument_profiles(source, "unlinkat")?.is_empty()
        || direct_call_argument_profiles(source, "fchmod")? != expected_output_fchmod_profiles()
        || direct_call_argument_profiles(source, "fsync")? != expected_output_fsync_profiles()
        || direct_call_argument_profiles(source, "rustix::io::write")?
            != vec![compact_profile(&["held", "bytes"])]
        || direct_call_argument_profiles(source, "rustix::io::pread")?
            != vec![compact_profile(&["held", "bytes", "offset"])]
        || direct_call_argument_profiles(source, "hooks.write")?
            != vec![compact_profile(&["held", "&bytes[written..]"])]
        || direct_call_argument_profiles(source, "hooks.pread")?
            != vec![
                compact_profile(&[
                    "held",
                    "&mut chunk[..remaining.min(VERIFY_CHUNK_BYTES)]",
                    "offset",
                ]),
                compact_profile(&["held", "&mut eof", "offset"]),
            ]
    {
        return Err("route-shape");
    }
    Ok(())
}

pub(super) fn verify_transaction_route(source: &str) -> Result<(), &'static str> {
    if source_sha256(source) != EXPECTED_TRANSACTION_SOURCE_SHA256 {
        return Err("route-source");
    }
    verify_transaction_route_shape(source)
}

pub(super) fn verify_transaction_route_shape(source: &str) -> Result<(), &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "route-shape")?;
    if !has_exact_super_glob(&syntax) {
        return Err("route-shape");
    }
    verify_transaction_module_edges(source).map_err(|_| "route-shape")?;
    verify_transaction_forbidden_shortcuts(source)?;
    verify_transaction_publication_order(source)?;
    verify_transaction_pair_order_against_canonical(source)?;

    let mut parser = rust_parser();
    let tree = parser.parse(source, None).ok_or("route-shape")?;
    if tree.root_node().has_error() {
        return Err("route-shape");
    }
    let calls = call_name_counts(tree.root_node(), source.as_bytes());
    let expected = EXPECTED_TRANSACTION_CALLS
        .iter()
        .map(|(call, count)| ((*call).to_string(), *count))
        .collect();
    if calls != expected
        || direct_call_argument_profiles(source, "rustix::process::geteuid")?
            != vec![
                Vec::<String>::new(),
                Vec::<String>::new(),
                Vec::<String>::new(),
                Vec::<String>::new(),
            ]
    {
        return Err("route-shape");
    }
    for forbidden_acquisition in [
        "openat",
        "statat",
        "linkat",
        "fstat",
        "fstatfs",
        "fsync",
        "fchmod",
        "rustix::io::read",
        "rustix::io::pread",
        "rustix::io::write",
    ] {
        if !direct_call_argument_profiles(source, forbidden_acquisition)?.is_empty() {
            return Err("route-shape");
        }
    }
    Ok(())
}

pub(super) fn verify_output_set_route(source: &str) -> Result<(), &'static str> {
    if source_sha256(source) != EXPECTED_OUTPUT_SET_SOURCE_SHA256 {
        return Err("route-source");
    }
    verify_output_set_route_shape(source)
}
