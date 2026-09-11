use super::*;

#[test]
fn sanitizer_reconciliation_functions_remain_tests() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let source = std::fs::read_to_string(
        root.join("tests/codex_exec_v0/source_binding_registry_normative_contract_tests.rs"),
    )
    .unwrap();
    assert_eq!(verify_sanitizer_reconciliation_tests(&source), Ok(()));
}

#[test]
fn independent_sanitizer_registry_accessor_returns_single_authority() {
    assert_eq!(
        crate::source_bindings::independent_sanitizer_only_paths(),
        crate::source_bindings::SANITIZER_ONLY_PATHS
    );
}

#[test]
fn normative_verifier_propagates_sanitizer_registry_reconciliation() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let support = std::fs::read_to_string(
        root.join("tests/codex_exec_v0/source_binding_registry_normative_contract_support.rs"),
    )
    .unwrap();
    assert_eq!(verify_normative_sanitizer_registry_edge(&support), Ok(()));
}

#[test]
fn recursive_inventory_rejects_every_registry_shape_attack() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let (source_actual, source_directories) =
        collect_inventory(&root.join("src/trajectory/codex_exec_v0"), root);
    let (trajectory_actual, trajectory_directories) =
        collect_inventory(&root.join("cli/trajectory"), root);
    assert!(source_directories.is_empty() && trajectory_directories.is_empty());
    assert_eq!(
        classify_directories(&["nested".to_string()]),
        Err("subdirectory")
    );
    let closure = selected_rust_closure(root).unwrap();
    let production_paths = closure
        .semantic_module_keys()
        .unwrap()
        .into_iter()
        .collect::<Vec<_>>();
    let linux_output_index = production_paths
        .iter()
        .position(|path| path == "cli/trajectory/linux_output.rs")
        .unwrap();
    assert_eq!(
        production_paths[linux_output_index + 1],
        "cli/trajectory/linux_output_rollback.rs",
        "rollback source must be adjacent in the selected source inventory"
    );
    assert_eq!(
        production_paths[linux_output_index + 2],
        "cli/trajectory/linux_output_set.rs",
        "output-set source must be adjacent in the selected source inventory"
    );
    assert_eq!(
        production_paths[linux_output_index + 3],
        "cli/trajectory/linux_output_transaction.rs",
        "transaction source must be adjacent in the selected source inventory"
    );

    let expected_normative = production_paths.iter().cloned().collect::<BTreeSet<_>>();
    let normative = production_paths;
    assert_eq!(
        classify_normative_rust_bindings(&normative, &expected_normative),
        Ok(())
    );
    for forbidden_test_source in [
        "tests/codex_exec_v0/cli.rs",
        "tests/codex_exec_v0/arbitrary.rs",
        "cli/trajectory/linux_output_set_tests.rs",
        "cli/trajectory/linux_output_tests.rs",
        "cli/trajectory/linux_output_transaction_phase_tests.rs",
    ] {
        let mut mutant = normative.clone();
        mutant.push(forbidden_test_source.to_string());
        assert_eq!(
            classify_normative_rust_bindings(&mutant, &expected_normative),
            Err("test-only"),
            "{forbidden_test_source}: arbitrary test source must never become normative"
        );
    }

    let expected_tests = EXPECTED_RELEVANT_TEST_RUST_SOURCES
        .iter()
        .map(|path| (*path).to_string())
        .collect::<BTreeSet<_>>();
    let (test_files, test_directories) = collect_inventory(&root.join("tests/codex_exec_v0"), root);
    assert!(root.join("tests/codex_exec_v0.rs").is_file());
    assert_eq!(
        test_directories,
        [
            "tests/codex_exec_v0/frozen_control_v0".to_string(),
            "tests/codex_exec_v0/support".to_string(),
        ],
        "unexpected recursive test subdirectory"
    );
    let mut relevant_actual = source_actual;
    relevant_actual.extend(trajectory_actual.iter().cloned());
    relevant_actual.extend(test_files);
    relevant_actual.extend([
        "cli/trajectory.rs".to_string(),
        "tests/codex_exec_v0.rs".to_string(),
        "tests/codex_process_capture_cli_v0.rs".to_string(),
    ]);
    let expected_relevant_production = expected_normative
        .iter()
        .filter(|path| {
            path.starts_with("src/trajectory/codex_exec_v0/")
                || path.as_str() == "cli/trajectory.rs"
                || path.starts_with("cli/trajectory/")
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    assert_eq!(
        classify_relevant_rust_inventory(
            &relevant_actual,
            &expected_relevant_production,
            &expected_tests,
        ),
        Ok(())
    );
    let mut omitted = relevant_actual.clone();
    omitted.pop();
    let mut duplicate = relevant_actual.clone();
    duplicate.push(relevant_actual[0].clone());
    let mut alias = relevant_actual.clone();
    alias[0] = format!("./{}", alias[0]);
    let mut helper = relevant_actual.clone();
    helper.push("cli/trajectory/helper.rs".to_string());
    for (name, mutant, error) in [
        ("omitted", omitted, "omitted"),
        ("duplicate", duplicate, "duplicate"),
        ("alias", alias, "unclassified"),
        ("helper", helper, "unclassified"),
    ] {
        assert_eq!(
            classify_relevant_rust_inventory(
                &mutant,
                &expected_relevant_production,
                &expected_tests,
            ),
            Err(error),
            "{name}"
        );
    }
    let mut orphan = relevant_actual.clone();
    orphan.push("tests/codex_exec_v0/orphan.rs".to_string());
    assert_eq!(
        classify_relevant_rust_inventory(&orphan, &expected_relevant_production, &expected_tests,),
        Err("unclassified")
    );
}

#[test]
fn registered_external_modules_and_includes_resolve_to_registered_targets() {
    downstream::assert_borrowed_graph_resolves_external_modules();
}

#[test]
fn codex_publication_routes_are_exact_through_adapter_replay_and_composition() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    assert_registered_route_sources_are_sealed(root);
    let main_source = std::fs::read_to_string(root.join("cli/main.rs")).unwrap();
    let mut parser = rust_parser();
    let tree = parser.parse(&main_source, None).unwrap();
    let arms = named_nodes_containing(
        tree.root_node(),
        main_source.as_bytes(),
        "match_arm",
        "Command::AdaptCodexExecV0",
    );
    assert_eq!(arms.len(), 1, "exactly one AdaptCodexExecV0 dispatch arm");
    let arm = arms[0];
    const EXPECTED_ARM: &str = r#"Command::AdaptCodexExecV0 {
            raw_stdout_jsonl,
            authority_receipt,
            trusted_context,
            output_type,
            output,
            private_lineage_output,
        } => {
            trajectory::run(
                &raw_stdout_jsonl,
                &authority_receipt,
                &trusted_context,
                output_type,
                &output,
                private_lineage_output.as_deref(),
            )
            .map_err(|error| LegitimacyError::invalid_input(error.code().as_str()))?;
            Ok(ExitCode::SUCCESS)
        }"#;
    assert_eq!(
        arm.utf8_text(main_source.as_bytes()).unwrap(),
        EXPECTED_ARM,
        "the selected arm is unguarded and exact"
    );
    assert_eq!(
        direct_call_paths(arm, main_source.as_bytes()),
        BTreeMap::from([
            ("LegitimacyError::invalid_input".to_string(), 1),
            ("Ok".to_string(), 1),
            ("trajectory::run".to_string(), 1),
        ])
    );
    let second_main_call = replace_exact_once(
        &main_source,
        "            .map_err(|error| LegitimacyError::invalid_input(error.code().as_str()))?;\n            Ok(ExitCode::SUCCESS)",
        "            .map_err(|error| LegitimacyError::invalid_input(error.code().as_str()))?;\n            trajectory::run(&raw_stdout_jsonl, &authority_receipt, &trusted_context, output_type, &output, private_lineage_output.as_deref())?;\n            Ok(ExitCode::SUCCESS)",
    );
    assert_source_mutant(
        "duplicate main publication call",
        &main_source,
        &second_main_call,
    );
    assert_eq!(publication_entry_call_count([main_source.as_str()]), 2);
    assert_eq!(publication_entry_call_count([second_main_call.as_str()]), 3);

    let composition_arms = named_nodes_containing(
        tree.root_node(),
        main_source.as_bytes(),
        "match_arm",
        "Command::EvaluateCodexExecCompositionV0",
    );
    assert_eq!(
        composition_arms.len(),
        1,
        "exactly one EvaluateCodexExecCompositionV0 dispatch arm"
    );
    let composition_arm = composition_arms[0];
    const EXPECTED_COMPOSITION_ARM: &str = r#"Command::EvaluateCodexExecCompositionV0 {
            raw_stdout_jsonl,
            input_authority_receipt,
            trusted_adaptation_context,
            shareable_sanitized_bundle,
            private_lineage_sidecar,
            replay_candidate,
            replay_authority_receipt,
            replay_authority_trust_policy,
            composition_policy,
            output,
            trace_output,
            canonical_trace_output,
            output_set,
        } => {
            trajectory_composition::evaluate(
                &trajectory_composition::CodexExecCompositionInputsV0 {
                    raw_stdout_jsonl: &raw_stdout_jsonl,
                    input_authority_receipt: input_authority_receipt.as_deref(),
                    trusted_adaptation_context: trusted_adaptation_context.as_deref(),
                    shareable_sanitized_bundle: shareable_sanitized_bundle.as_deref(),
                    private_lineage_sidecar: private_lineage_sidecar.as_deref(),
                    replay_candidate: &replay_candidate,
                    replay_authority_receipt: &replay_authority_receipt,
                    replay_authority_trust_policy: &replay_authority_trust_policy,
                    composition_policy: &composition_policy,
                },
                &trajectory_composition::CodexExecCompositionOutputsV0 {
                    result: output.as_deref(),
                    trace: trace_output.as_deref(),
                    canonical_trace: canonical_trace_output.as_deref(),
                    output_set: output_set.as_deref(),
                },
            )
            .map_err(LegitimacyError::invalid_input)?;
            Ok(ExitCode::SUCCESS)
        }"#;
    assert_eq!(
        composition_arm.utf8_text(main_source.as_bytes()).unwrap(),
        EXPECTED_COMPOSITION_ARM,
        "the adapter-bound composition arm is unguarded and exact"
    );
    assert_eq!(
        direct_call_paths(composition_arm, main_source.as_bytes()),
        BTreeMap::from([
            ("Ok".to_string(), 1),
            ("trajectory_composition::evaluate".to_string(), 1),
        ])
    );

    let trajectory_source = std::fs::read_to_string(root.join("cli/trajectory.rs")).unwrap();
    assert_eq!(verify_trajectory_route(&trajectory_source), Ok(()));
    let linux_path_source =
        std::fs::read_to_string(root.join("cli/trajectory/linux_path.rs")).unwrap();
    assert_eq!(verify_linux_path_route(&linux_path_source), Ok(()));
    assert_eq!(
        verify_trajectory_module_edge(&trajectory_source),
        Ok(BTreeSet::from([
            "cli/trajectory/linux_output.rs",
            "cli/trajectory/linux_path.rs",
        ]))
    );
    assert_eq!(
        verify_linux_path_test_module_edge(&linux_path_source),
        Ok("cli/trajectory/linux_path_tests.rs")
    );
    let linux_output_source =
        std::fs::read_to_string(root.join("cli/trajectory/linux_output.rs")).unwrap();
    assert_eq!(verify_linux_output_route(&linux_output_source), Ok(()));
    assert_eq!(
        verify_linux_output_module_edges(&linux_output_source),
        Ok(BTreeSet::from([
            "cli/trajectory/linux_output_rollback.rs",
            "cli/trajectory/linux_output_tests.rs",
            "cli/trajectory/linux_output_transaction.rs",
        ]))
    );
    let transaction_source =
        std::fs::read_to_string(root.join("cli/trajectory/linux_output_transaction.rs")).unwrap();
    assert_eq!(verify_transaction_route(&transaction_source), Ok(()));
    assert_eq!(
        verify_transaction_module_edges(&transaction_source),
        Ok(BTreeSet::from([
            "cli/trajectory/linux_output_set.rs",
            "cli/trajectory/linux_output_set_tests.rs",
            "cli/trajectory/linux_output_transaction_tests.rs",
        ]))
    );
    let transaction_tests_source =
        std::fs::read_to_string(root.join("cli/trajectory/linux_output_transaction_tests.rs"))
            .unwrap();
    assert_eq!(
        verify_transaction_phase_test_module_edge(&transaction_tests_source),
        Ok("cli/trajectory/linux_output_transaction_phase_tests.rs")
    );
    assert_eq!(
        verify_after_guard_test_seam(&transaction_tests_source),
        Ok(())
    );
    for (attack, mutation) in trajectory_module_edge_mutants(&trajectory_source) {
        assert_source_mutant(attack, &trajectory_source, &mutation);
        assert_eq!(
            verify_trajectory_module_edge(&mutation),
            Err("module-edge"),
            "{attack}"
        );
    }
    for (attack, mutation) in linux_path_module_edge_mutants(&linux_path_source) {
        assert_source_mutant(attack, &linux_path_source, &mutation);
        assert_eq!(
            verify_linux_path_test_module_edge(&mutation),
            Err("module-edge"),
            "{attack}"
        );
        assert_eq!(
            verify_linux_path_route_shape(&mutation),
            Err("route-shape"),
            "{attack}: whole-file route seal"
        );
    }
    for (attack, mutation) in linux_path_route_mutants(&linux_path_source) {
        assert_source_mutant(attack, &linux_path_source, &mutation);
        assert_eq!(
            verify_linux_path_route_shape(&mutation),
            Err("route-shape"),
            "{attack}"
        );
    }
    for (attack, mutation) in linux_output_route_mutants(&linux_output_source) {
        assert_source_mutant(&attack, &linux_output_source, &mutation);
        assert_eq!(
            verify_linux_output_route_shape(&mutation),
            Err("route-shape"),
            "{attack}"
        );
    }
    for (attack, mutation) in transaction_route_mutants(&transaction_source) {
        assert_source_mutant(attack, &transaction_source, &mutation);
        assert_eq!(
            verify_transaction_route_shape(&mutation),
            Err("route-shape"),
            "{attack}"
        );
    }
    let sanitizer_source =
        std::fs::read_to_string(root.join("src/trajectory/codex_exec_v0/sanitizer.rs")).unwrap();
    let sanitizer_jwt_source =
        std::fs::read_to_string(root.join("src/trajectory/codex_exec_v0/sanitizer_jwt.rs"))
            .unwrap();
    let bundle_wire_source =
        std::fs::read_to_string(root.join("src/trajectory/codex_exec_v0/bundle_wire.rs")).unwrap();
    let publication_authority_source =
        std::fs::read_to_string(root.join("src/trajectory/codex_exec_v0/publication_authority.rs"))
            .unwrap();
    assert_eq!(
        verify_privacy_route_shape(
            &sanitizer_source,
            &sanitizer_jwt_source,
            &bundle_wire_source,
            &publication_authority_source,
        ),
        Ok(())
    );
    for (
        attack,
        sanitizer_mutation,
        sanitizer_jwt_mutation,
        bundle_wire_mutation,
        publication_authority_mutation,
    ) in privacy_route_mutants(
        &sanitizer_source,
        &sanitizer_jwt_source,
        &bundle_wire_source,
        &publication_authority_source,
    ) {
        if sanitizer_mutation != sanitizer_source {
            assert_source_mutant(attack, &sanitizer_source, &sanitizer_mutation);
        }
        if sanitizer_jwt_mutation != sanitizer_jwt_source {
            assert_source_mutant(attack, &sanitizer_jwt_source, &sanitizer_jwt_mutation);
        }
        if bundle_wire_mutation != bundle_wire_source {
            assert_source_mutant(attack, &bundle_wire_source, &bundle_wire_mutation);
        }
        if publication_authority_mutation != publication_authority_source {
            assert_source_mutant(
                attack,
                &publication_authority_source,
                &publication_authority_mutation,
            );
        }
        assert_eq!(
            verify_privacy_route_shape(
                &sanitizer_mutation,
                &sanitizer_jwt_mutation,
                &bundle_wire_mutation,
                &publication_authority_mutation,
            ),
            Err("route-shape"),
            "{attack}"
        );
    }
    let output_set_source =
        std::fs::read_to_string(root.join("cli/trajectory/linux_output_set.rs")).unwrap();
    assert_eq!(verify_output_set_route(&output_set_source), Ok(()));
    for (attack, mutation) in output_set_route_mutants(&output_set_source) {
        assert_source_mutant(attack, &output_set_source, &mutation);
        assert_eq!(
            verify_output_set_route(&mutation),
            Err("route-source"),
            "{attack}: exact source seal"
        );
        assert_eq!(
            verify_output_set_route_shape(&mutation),
            Err("route-shape"),
            "{attack}: output-set semantic seal"
        );
    }
    let rollback_source =
        std::fs::read_to_string(root.join("cli/trajectory/linux_output_rollback.rs")).unwrap();
    assert_eq!(verify_rollback_route(&rollback_source), Ok(()));
    for (attack, mutation) in rollback_route_mutants(&rollback_source) {
        assert_source_mutant(attack, &rollback_source, &mutation);
        assert_eq!(
            verify_rollback_route(&mutation),
            Err("route-source"),
            "{attack}: exact source seal"
        );
        assert_eq!(
            verify_rollback_route_shape(&mutation),
            Err("route-shape"),
            "{attack}: rollback semantic seal"
        );
    }
    for (attack, mutation) in transaction_phase_module_edge_mutants(&transaction_tests_source) {
        assert_source_mutant(attack, &transaction_tests_source, &mutation);
        assert_eq!(
            verify_transaction_phase_test_module_edge(&mutation),
            Err("module-edge"),
            "{attack}"
        );
    }
    for (attack, mutation) in after_guard_test_seam_mutants(&transaction_tests_source) {
        assert_source_mutant(attack, &transaction_tests_source, &mutation);
        assert_eq!(
            verify_after_guard_test_seam(&mutation),
            Err("test-seam"),
            "{attack}"
        );
    }
    for (attack, mutation) in trajectory_route_mutants(&trajectory_source) {
        assert_source_mutant(attack, &trajectory_source, &mutation);
        assert_eq!(
            verify_trajectory_route(&mutation),
            Err("route-source"),
            "{attack}"
        );
        assert_eq!(
            verify_trajectory_route_shape(&mutation),
            Err("route-shape"),
            "{attack}: semantic verifier"
        );
    }
    let composition_source =
        std::fs::read_to_string(root.join("cli/trajectory_composition.rs")).unwrap();
    assert_eq!(verify_composition_route(&composition_source), Ok(()));
    for (attack, mutation) in composition_route_mutants(&composition_source) {
        assert_source_mutant(attack, &composition_source, &mutation);
        assert_eq!(
            verify_composition_route(&mutation),
            Err("route-source"),
            "{attack}: exact source seal"
        );
        assert_eq!(
            verify_composition_route_shape(&mutation),
            Err("route-shape"),
            "{attack}: adapter-bound composition route verifier"
        );
    }

    let (cli_source_paths, _) = collect_inventory(&root.join("cli"), root);
    let mut cli_sources = cli_source_paths
        .into_iter()
        .map(|path| root.join(path))
        .collect::<Vec<_>>();
    cli_sources.sort();
    let mut publication_entry_calls = 0usize;
    let mut publication_entry_paths = 0usize;
    for path in cli_sources {
        let source = std::fs::read_to_string(&path).unwrap();
        let relative_path = relative(root, &path);
        let expected = usize::from(matches!(
            relative_path.as_str(),
            "cli/trajectory.rs" | "cli/trajectory_composition.rs"
        )) * 2;
        assert_eq!(
            identifier_count(&source, "adapt_codex_exec_owned_v0"),
            expected,
            "{relative_path}: adapter entry import/call uniqueness"
        );
        assert_eq!(
            identifier_count(&source, "sanitize_capture_v0"),
            usize::from(relative_path == "cli/trajectory.rs") * 2,
            "{relative_path}: production sanitizer route is unique"
        );
        for alternate in [
            "adapt_codex_exec_v0",
            "sanitize_capture_with_fixed_test_nonce_v0",
        ] {
            assert_eq!(
                identifier_count(&source, alternate),
                0,
                "{relative_path}: {alternate}"
            );
        }
        publication_entry_calls += publication_entry_call_count([source.as_str()]);
        publication_entry_paths += path_suffix_count(&source, "trajectory::run");
        publication_entry_paths += path_suffix_count(&source, "trajectory_composition::evaluate");
        assert!(
            cli_trajectory_imports_are_exact(&relative_path, &source),
            "{relative_path}: trajectory imports are closed"
        );
        if !matches!(
            relative_path.as_str(),
            "cli/trajectory.rs"
                | "cli/trajectory_composition.rs"
                | "cli/trajectory/linux_output.rs"
                | "cli/trajectory/linux_output_transaction.rs"
                | "cli/trajectory/linux_path.rs"
        ) {
            assert!(
                !flattened_imports(&source)
                    .iter()
                    .any(|path| path.starts_with("legitimacy::trajectory::codex_exec_v0")),
                "{relative_path}: no alternate adapter import"
            );
        }
    }
    assert_eq!(
        publication_entry_calls, 2,
        "two exact CLI publication entry edges"
    );
    assert_eq!(
        publication_entry_paths, 2,
        "two CLI publication entry paths, each located in its selected arm"
    );

    let workflow = std::fs::read_to_string(root.join("cli/workflow.rs")).unwrap();
    assert!(workflow.contains("parse_graph_file(policy)"));
    assert!(workflow.contains("compile_graph_with_sacrifices"));
    assert!(
        !trajectory_source.contains("parse_graph_file")
            && !trajectory_source.contains("compile_graph_with_sacrifices")
    );
    let workflow_duplicate =
        format!("{workflow}\nfn duplicate_publication_edge() {{ crate::trajectory::run(); }}\n");
    assert_eq!(
        publication_entry_call_count([main_source.as_str(), workflow_duplicate.as_str()]),
        3,
        "fully qualified duplicate CLI entry is killed"
    );
    for (attack, alias_attack) in [
        (
            "function import alias",
            format!("{workflow}\nuse crate::trajectory::run as x;\nfn duplicate() {{ x(); }}\n"),
        ),
        (
            "module import alias",
            format!("{workflow}\nuse crate::trajectory as t;\nfn duplicate() {{ t::run(); }}\n"),
        ),
    ] {
        assert_source_mutant(attack, &workflow, &alias_attack);
        assert!(
            !cli_trajectory_imports_are_exact("cli/workflow.rs", &alias_attack),
            "{attack}: exact CLI import verifier"
        );
    }
}
