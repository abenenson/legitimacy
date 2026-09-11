use super::normative_contract_support::*;
use super::*;

#[test]
fn sanitizer_contract_registry_matches_independent_ordered_registry() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let document = std::fs::read_to_string(root.join("docs/codex-exec-v0-adapter.md")).unwrap();
    let build = canonical_build_input();
    assert_eq!(
        verify_sanitizer_registry_contract(&document, &build),
        Ok(())
    );
}

#[test]
fn sanitizer_contract_registry_rejects_all_ordered_list_shape_drift() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let document = std::fs::read_to_string(root.join("docs/codex-exec-v0-adapter.md")).unwrap();
    let build = canonical_build_input();
    let contract = load_normative_contract(&build).unwrap();
    let bindings = &contract.facts[0];
    assert_eq!(
        verify_sanitizer_registry_contract(&document, &build),
        Ok(())
    );
    for (attack, sources) in [
        (
            "omitted sanitizer source",
            vec![
                "sanitizer.rs",
                "publication_authority.rs",
                "lineage_sidecar.rs",
            ],
        ),
        (
            "surplus sanitizer source",
            vec![
                "sanitizer.rs",
                "sanitizer_jwt.rs",
                "publication_authority.rs",
                "lineage_sidecar.rs",
                "unexpected.rs",
            ],
        ),
        (
            "duplicated sanitizer source",
            vec![
                "sanitizer.rs",
                "sanitizer_jwt.rs",
                "sanitizer_jwt.rs",
                "publication_authority.rs",
                "lineage_sidecar.rs",
            ],
        ),
        (
            "reordered sanitizer sources",
            vec![
                "sanitizer_jwt.rs",
                "sanitizer.rs",
                "publication_authority.rs",
                "lineage_sidecar.rs",
            ],
        ),
    ] {
        let mut mutant_build = build.clone();
        mutant_build["normative_contract"]["facts"][0]["sanitizer_sources"] =
            serde_json::Value::Array(
                sources
                    .into_iter()
                    .map(|source| serde_json::Value::String(source.to_string()))
                    .collect(),
            );
        let mutant_contract = load_normative_contract(&mutant_build).unwrap();
        let mutant_document = replace_exact_once(
            &document,
            &exact_region(bindings),
            &exact_region(&mutant_contract.facts[0]),
        );
        assert_eq!(
            verify_sanitizer_registry_contract(&mutant_document, &mutant_build),
            Err(NormativeContractError::SanitizerReconciliation),
            "{attack}"
        );
    }
}

#[test]
fn normative_sanitizer_omission_reaches_specific_edge() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let read = |path: &str| std::fs::read_to_string(root.join(path)).unwrap();
    let document = read("docs/codex-exec-v0-adapter.md");
    let sanitizer = read("src/trajectory/codex_exec_v0/sanitizer.rs");
    let nonce = read("src/trajectory/codex_exec_v0/receipt_nonce.rs");
    let trajectory = read("cli/trajectory.rs");
    let linux_output = read("cli/trajectory/linux_output.rs");
    let transaction = read("cli/trajectory/linux_output_transaction.rs");
    let process_supervisor = read("src/trajectory/codex_exec_v0/process_capture_supervisor.rs");
    let process_supervision = read("src/trajectory/codex_exec_v0/process_capture_supervision.rs");
    let process_cleanup = read("src/trajectory/codex_exec_v0/process_capture_cleanup.rs");
    let process_sources = [
        ProcessSource {
            label: PROCESS_SOURCE_IDENTITIES[0].0,
            path: PROCESS_SOURCE_IDENTITIES[0].1,
            source: &process_supervisor,
        },
        ProcessSource {
            label: PROCESS_SOURCE_IDENTITIES[1].0,
            path: PROCESS_SOURCE_IDENTITIES[1].1,
            source: &process_supervision,
        },
        ProcessSource {
            label: PROCESS_SOURCE_IDENTITIES[2].0,
            path: PROCESS_SOURCE_IDENTITIES[2].1,
            source: &process_cleanup,
        },
    ];
    let adapter_error = read("src/trajectory/codex_exec_v0/error.rs");
    let build = canonical_build_input();
    let implementation = NormativeImplementation {
        sanitizer: &sanitizer,
        nonce: &nonce,
        trajectory: &trajectory,
        linux_output: &linux_output,
        transaction: &transaction,
        process_sources: &process_sources,
        adapter_error: &adapter_error,
    };
    let mut baseline_stages = Vec::new();
    let baseline_result = super::normative_contract_support::verify_normative_contract_observed(
        &document,
        &build,
        implementation,
        &mut |stage| baseline_stages.push(stage),
    );
    assert_eq!(baseline_result, Ok(()));
    assert_eq!(
        baseline_stages,
        [
            SanitizerStage::BoundaryInvoked,
            SanitizerStage::ReconciliationStarted,
            SanitizerStage::Compared(SanitizerComparison::Match),
        ]
    );
    let contract = super::normative_contract_support::load_normative_contract(&build).unwrap();
    let bindings = &contract.facts[0];
    let mut sanitizer_mutant_build = build.clone();
    sanitizer_mutant_build["normative_contract"]["facts"][0]["sanitizer_sources"]
        .as_array_mut()
        .unwrap()
        .pop();
    let sanitizer_mutant_contract =
        super::normative_contract_support::load_normative_contract(&sanitizer_mutant_build)
            .unwrap();
    let sanitizer_mutant_document = super::replace_exact_once(
        &document,
        &super::normative_contract_support::exact_region(bindings),
        &super::normative_contract_support::exact_region(&sanitizer_mutant_contract.facts[0]),
    );
    let mut omission_stages = Vec::new();
    let omission_result = super::normative_contract_support::verify_normative_contract_observed(
        &sanitizer_mutant_document,
        &sanitizer_mutant_build,
        implementation,
        &mut |stage| omission_stages.push(stage),
    );
    assert_eq!(
        omission_result,
        Err(NormativeContractError::SanitizerReconciliation)
    );
    assert_eq!(
        omission_stages,
        [
            SanitizerStage::BoundaryInvoked,
            SanitizerStage::ReconciliationStarted,
            SanitizerStage::Compared(SanitizerComparison::Mismatch),
        ]
    );
}

#[test]
fn normative_adapter_contract_matches_security_relevant_implementation() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let read = |path: &str| std::fs::read_to_string(root.join(path)).unwrap();
    let document = read("docs/codex-exec-v0-adapter.md");
    let sanitizer = read("src/trajectory/codex_exec_v0/sanitizer.rs");
    let nonce = read("src/trajectory/codex_exec_v0/receipt_nonce.rs");
    let trajectory = read("cli/trajectory.rs");
    let linux_output = read("cli/trajectory/linux_output.rs");
    let transaction = read("cli/trajectory/linux_output_transaction.rs");
    let process_supervisor = read("src/trajectory/codex_exec_v0/process_capture_supervisor.rs");
    let process_supervision = read("src/trajectory/codex_exec_v0/process_capture_supervision.rs");
    let process_cleanup = read("src/trajectory/codex_exec_v0/process_capture_cleanup.rs");
    let process_sources = [
        ProcessSource {
            label: PROCESS_SOURCE_IDENTITIES[0].0,
            path: PROCESS_SOURCE_IDENTITIES[0].1,
            source: &process_supervisor,
        },
        ProcessSource {
            label: PROCESS_SOURCE_IDENTITIES[1].0,
            path: PROCESS_SOURCE_IDENTITIES[1].1,
            source: &process_supervision,
        },
        ProcessSource {
            label: PROCESS_SOURCE_IDENTITIES[2].0,
            path: PROCESS_SOURCE_IDENTITIES[2].1,
            source: &process_cleanup,
        },
    ];
    let adapter_error = read("src/trajectory/codex_exec_v0/error.rs");
    let build = canonical_build_input();
    let implementation = NormativeImplementation {
        sanitizer: &sanitizer,
        nonce: &nonce,
        trajectory: &trajectory,
        linux_output: &linux_output,
        transaction: &transaction,
        process_sources: &process_sources,
        adapter_error: &adapter_error,
    };
    let verify_with_implementation =
        |document: &str, build: &serde_json::Value, sources: &[ProcessSource<'_>], error: &str| {
            verify_normative_contract(
                document,
                build,
                NormativeImplementation {
                    process_sources: sources,
                    adapter_error: error,
                    ..implementation
                },
            )
        };
    let verify = |document: &str, build: &serde_json::Value| {
        verify_with_implementation(document, build, &process_sources, &adapter_error)
    };
    assert_eq!(verify(&document, &build), Ok(()));

    let contract = load_normative_contract(&build).unwrap();
    let pair = &contract.facts[6];
    for (attack, replacement) in [
        (
            "quoted rejected pair design",
            "The phrase “owner-private sidecar is prepared and linked first” names the\nrejected design; normatively the public output is linked first.",
        ),
        (
            "negated pair contract",
            "It is not true that the owner-private sidecar precedes the public output.",
        ),
        (
            "pair-order exception",
            "Pair order contract: the sidecar is first, except when public output is ready.",
        ),
    ] {
        let replacement = format!(
            "{}\n{replacement}\n{}",
            marker(fact_id(pair), "begin"),
            marker(fact_id(pair), "end"),
        );
        let mutant = replace_exact_once(&document, &exact_region(pair), &replacement);
        assert_eq!(
            verify(&mutant, &build),
            Err(NormativeContractError::Contract),
            "{attack}"
        );
    }

    for (attack, mutant) in [
        (
            "unmarked authority override",
            format!(
                "{document}\nNormative override: the public output is linked before the owner-private sidecar.\n"
            ),
        ),
        (
            "unclassified contract marker",
            format!("{document}\n<!-- codex-exec-v0-contract:override:begin -->\n"),
        ),
        (
            "duplicate marker",
            format!("{}\n{document}", marker("pair-order", "begin")),
        ),
        (
            "missing marker",
            replace_exact_once(&document, &marker("commit-point", "end"), ""),
        ),
    ] {
        assert_eq!(
            verify(&mutant, &build),
            Err(NormativeContractError::Contract),
            "{attack}"
        );
    }

    let process = &contract.facts[2];
    for (attack, replacement) in [
        ("reordered primary", None),
        ("duplicated primary", Some("capture-stdin")),
    ] {
        let mut mutant_build = build.clone();
        if let Some(replacement) = replacement {
            mutant_build["normative_contract"]["facts"][2]["primary"][5] =
                serde_json::Value::String(replacement.to_string());
        } else {
            mutant_build["normative_contract"]["facts"][2]["primary"]
                .as_array_mut()
                .unwrap()
                .swap(2, 5);
        }
        let mutant_contract = load_normative_contract(&mutant_build).unwrap();
        let mutant_document = replace_exact_once(
            &document,
            &exact_region(process),
            &exact_region(&mutant_contract.facts[2]),
        );
        assert_eq!(
            verify(&mutant_document, &mutant_build),
            Err(NormativeContractError::Contract),
            "{attack}"
        );
    }

    let mut weakened_cleanup = build.clone();
    weakened_cleanup["normative_contract"]["facts"][2]["cleanup_dominates"]
        .as_array_mut()
        .unwrap()
        .pop();
    assert_eq!(
        verify(&document, &weakened_cleanup),
        Err(NormativeContractError::Contract),
        "omitted cleanup dominance cause"
    );

    let rank_mutant = replace_exact_once(
        &process_supervision,
        "        Self::Stdin,\n        Self::StreamState,\n        Self::Timeout,\n        Self::LiveDescendant,",
        "        Self::LiveDescendant,\n        Self::Stdin,\n        Self::StreamState,\n        Self::Timeout,",
    );
    assert_eq!(
        verify_with_implementation(
            &document,
            &build,
            &[
                process_sources[0],
                ProcessSource {
                    source: &rank_mutant,
                    ..process_sources[1]
                },
                process_sources[2],
            ],
            &adapter_error,
        ),
        Err(NormativeContractError::Contract),
        "implementation rank mutation"
    );
    let spelling_mutant = replace_exact_once(
        &adapter_error,
        "Self::CaptureLiveDescendant => \"capture-live-descendant\"",
        "Self::CaptureLiveDescendant => \"capture-cleanup\"",
    );
    assert_eq!(
        verify_with_implementation(&document, &build, &process_sources, &spelling_mutant),
        Err(NormativeContractError::Contract),
        "implementation spelling mutation"
    );

    assert_eq!(
        verify_with_implementation(&document, &build, &process_sources[..2], &adapter_error,),
        Err(NormativeContractError::Contract),
        "omitted process source"
    );
    let duplicated_sources = [
        process_sources[0],
        process_sources[1],
        process_sources[1],
        process_sources[2],
    ];
    assert_eq!(
        verify_with_implementation(&document, &build, &duplicated_sources, &adapter_error),
        Err(NormativeContractError::Contract),
        "duplicated process source"
    );
    let mislabeled_sources = [
        ProcessSource {
            label: "process_capture_spawn",
            ..process_sources[0]
        },
        process_sources[1],
        process_sources[2],
    ];
    assert_eq!(
        verify_with_implementation(&document, &build, &mislabeled_sources, &adapter_error),
        Err(NormativeContractError::Contract),
        "mislabeled process source"
    );
    let wrong_path_sources = [
        process_sources[0],
        ProcessSource {
            path: "src/trajectory/codex_exec_v0/process_capture_supervisor.rs",
            ..process_sources[1]
        },
        process_sources[2],
    ];
    assert_eq!(
        verify_with_implementation(&document, &build, &wrong_path_sources, &adapter_error),
        Err(NormativeContractError::Contract),
        "wrong-path process source"
    );

    let authority_start = process_supervision
        .find("impl PrimaryCaptureFailure {")
        .unwrap();
    let authority_end = process_supervision[authority_start..]
        .find("#[derive(Clone, Copy, Default)]")
        .map(|offset| authority_start + offset)
        .unwrap();
    let moved_authority = &process_supervision[authority_start..authority_end];
    let supervision_without_authority =
        replace_exact_once(&process_supervision, moved_authority, "");
    let supervisor_with_authority = format!("{process_supervisor}\n{moved_authority}");
    let moved_authority_sources = [
        ProcessSource {
            source: &supervisor_with_authority,
            ..process_sources[0]
        },
        ProcessSource {
            source: &supervision_without_authority,
            ..process_sources[1]
        },
        process_sources[2],
    ];
    assert_eq!(
        verify_with_implementation(&document, &build, &moved_authority_sources, &adapter_error,),
        Err(NormativeContractError::Contract),
        "moved precedence authority"
    );

    let omitted_cleanup_fragment = replace_exact_once(
        &process_cleanup,
        "if uncertain || status.is_none() || !absent",
        "if false",
    );
    let omitted_cleanup_sources = [
        process_sources[0],
        process_sources[1],
        ProcessSource {
            source: &omitted_cleanup_fragment,
            ..process_sources[2]
        },
    ];
    assert_eq!(
        verify_with_implementation(&document, &build, &omitted_cleanup_sources, &adapter_error,),
        Err(NormativeContractError::Contract),
        "omitted cleanup certainty fragment"
    );
    let duplicated_cleanup_fragment = format!(
        "{process_cleanup}\nconst DUPLICATED_CLEANUP_FRAGMENT: &str = {:?};\n",
        "if uncertain || status.is_none() || !absent"
    );
    let duplicated_cleanup_sources = [
        process_sources[0],
        process_sources[1],
        ProcessSource {
            source: &duplicated_cleanup_fragment,
            ..process_sources[2]
        },
    ];
    assert_eq!(
        verify_with_implementation(
            &document,
            &build,
            &duplicated_cleanup_sources,
            &adapter_error,
        ),
        Err(NormativeContractError::Contract),
        "duplicated cleanup certainty fragment"
    );

    let mut reordered_build = build.clone();
    reordered_build["normative_contract"]["facts"]
        .as_array_mut()
        .unwrap()
        .swap(0, 1);
    let first = exact_region(&contract.facts[0]);
    let second = exact_region(&contract.facts[1]);
    let placeholder = "<!-- contract-region-swap-placeholder -->";
    let reordered_document = replace_exact_once(
        &replace_exact_once(
            &replace_exact_once(&document, &first, placeholder),
            &second,
            &first,
        ),
        placeholder,
        &second,
    );
    assert_eq!(
        verify(&reordered_document, &reordered_build),
        Err(NormativeContractError::Contract),
        "reordered structured fact"
    );

    let mut duplicated_build = build.clone();
    let duplicate = duplicated_build["normative_contract"]["facts"][6].clone();
    duplicated_build["normative_contract"]["facts"]
        .as_array_mut()
        .unwrap()
        .push(duplicate);
    assert_eq!(
        verify(&document, &duplicated_build),
        Err(NormativeContractError::Contract),
        "duplicate structured fact"
    );

    let mut truncated_build = build.clone();
    truncated_build["normative_contract"]["facts"][4]["steps"]
        .as_array_mut()
        .unwrap()
        .pop();
    assert_eq!(
        verify(&document, &truncated_build),
        Err(NormativeContractError::Contract),
        "truncated structured fact"
    );

    let phases = build["normative_contract"]["facts"][6]["phases"]
        .as_array()
        .unwrap()
        .clone();
    let mut permutations = Vec::new();
    collect_permutations(Vec::new(), phases.clone(), &mut permutations);
    for permutation in permutations {
        if permutation == phases {
            continue;
        }
        let mut mutant_build = build.clone();
        mutant_build["normative_contract"]["facts"][6]["phases"] =
            serde_json::Value::Array(permutation);
        let mutant_contract = load_normative_contract(&mutant_build).unwrap();
        let mutant_document = replace_exact_once(
            &document,
            &exact_region(pair),
            &exact_region(&mutant_contract.facts[6]),
        );
        assert_eq!(
            verify_pair_order_contract(&mutant_document, &mutant_build, &transaction),
            Err(NormativeContractError::Contract),
            "term-preserving phase permutation"
        );
    }

    for (attack, phases) in [
        ("missing phase", phases[..5].to_vec()),
        (
            "duplicate phase",
            phases[..5]
                .iter()
                .cloned()
                .chain([phases[4].clone()])
                .collect(),
        ),
        (
            "unknown phase",
            phases[..5]
                .iter()
                .cloned()
                .chain([serde_json::Value::String("unknown-phase".to_string())])
                .collect(),
        ),
    ] {
        let mut mutant_build = build.clone();
        mutant_build["normative_contract"]["facts"][6]["phases"] = serde_json::Value::Array(phases);
        let mutant_contract = load_normative_contract(&mutant_build).unwrap();
        let mutant_document = replace_exact_once(
            &document,
            &exact_region(pair),
            &exact_region(&mutant_contract.facts[6]),
        );
        assert_eq!(
            verify_pair_order_contract(&mutant_document, &mutant_build, &transaction),
            Err(NormativeContractError::Contract),
            "{attack}"
        );
    }
}

fn collect_permutations(
    prefix: Vec<serde_json::Value>,
    remaining: Vec<serde_json::Value>,
    output: &mut Vec<Vec<serde_json::Value>>,
) {
    if remaining.is_empty() {
        output.push(prefix);
        return;
    }
    for index in 0..remaining.len() {
        let mut next_prefix = prefix.clone();
        next_prefix.push(remaining[index].clone());
        let mut next_remaining = remaining.clone();
        next_remaining.remove(index);
        collect_permutations(next_prefix, next_remaining, output);
    }
}
