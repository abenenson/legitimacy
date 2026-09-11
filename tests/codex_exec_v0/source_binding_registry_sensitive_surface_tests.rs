use super::*;

#[test]
fn selected_authority_identifiers_are_confined_to_the_derived_owner() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let closure = selected_rust_closure(root).unwrap();
    let sources = closure.semantic_module_sources().unwrap();
    let owner_path = closure.owner_path();
    let owner = sources.get(owner_path).unwrap();
    assert!(owner.contains("struct PublicationMintV0"));
    assert!(owner.contains("pub struct ShareableSanitizedBundleV0"));
    for (path, source) in &sources {
        if path != owner_path {
            assert!(!source.contains("struct PublicationMintV0"), "{path}");
            assert!(
                !source.contains("pub struct ShareableSanitizedBundleV0"),
                "{path}"
            );
        }
    }
    assert_eq!(verify_selected_sensitive_type_surfaces(closure), Ok(()));
}

#[test]
fn private_lineage_sidecar_exposes_no_public_or_minting_capability() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let sidecar_source =
        std::fs::read_to_string(root.join("src/trajectory/codex_exec_v0/lineage_sidecar.rs"))
            .unwrap();
    let sidecar = syn::parse_file(&sidecar_source).unwrap();
    assert_eq!(
        named_struct_fields(&sidecar, "OwnerPrivateLineageSidecarV0"),
        BTreeSet::from([
            "authority".to_string(),
            "bytes".to_string(),
            "child_end".to_string(),
            "child_start".to_string(),
            "context".to_string(),
        ])
    );
    let expected_private_fields = BTreeMap::from([
        ("authority".to_string(), "inherited".to_string()),
        ("bytes".to_string(), "inherited".to_string()),
        ("child_end".to_string(), "inherited".to_string()),
        ("child_start".to_string(), "inherited".to_string()),
        ("context".to_string(), "inherited".to_string()),
    ]);
    assert_eq!(
        named_struct_field_visibilities(&sidecar, "OwnerPrivateLineageSidecarV0"),
        expected_private_fields
    );
    assert!(!named_struct_has_derive(
        &sidecar,
        "OwnerPrivateLineageSidecarV0"
    ));

    let public_field_mutant = replace_exact_once(
        &sidecar_source,
        "    bytes: Vec<u8>,",
        "    pub bytes: Vec<u8>,",
    );
    assert_source_mutant(
        "private lineage bytes become public",
        &sidecar_source,
        &public_field_mutant,
    );
    let public_field_mutant = syn::parse_file(&public_field_mutant).unwrap();
    assert_ne!(
        named_struct_field_visibilities(&public_field_mutant, "OwnerPrivateLineageSidecarV0"),
        expected_private_fields,
        "a public private-lineage field must be killed"
    );
    let derive_mutant = replace_exact_once(
        &sidecar_source,
        "pub struct OwnerPrivateLineageSidecarV0 {",
        "#[derive(serde::Serialize)]\npub struct OwnerPrivateLineageSidecarV0 {",
    );
    assert_source_mutant(
        "private lineage becomes serializable",
        &sidecar_source,
        &derive_mutant,
    );
    let derive_mutant = syn::parse_file(&derive_mutant).unwrap();
    assert!(
        named_struct_has_derive(&derive_mutant, "OwnerPrivateLineageSidecarV0"),
        "a Serialize derive must be killed"
    );
    assert_eq!(
        public_inherent_method_names(&sidecar, "OwnerPrivateLineageSidecarV0"),
        BTreeSet::from([
            "from_binary_slice".to_string(),
            "into_bytes".to_string(),
            "revalidate_public_bundle".to_string(),
            "revalidate_public_bundle_for_jsonl".to_string(),
        ])
    );
    assert_eq!(
        implemented_trait_names(&sidecar, "OwnerPrivateLineageSidecarV0"),
        BTreeSet::from(["fmt::Debug".to_string()])
    );
    for forbidden in [
        "ShareableSanitizedBundleV0",
        "ProductionSanitizationTransactionV0",
        "PublicationMintV0",
        "into_publication_pair",
    ] {
        assert_eq!(
            identifier_count(&sidecar_source, forbidden),
            0,
            "{forbidden}"
        );
    }
}

#[test]
fn registered_sensitive_type_surfaces_match_reviewed_shapes() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let closure = selected_rust_closure(root).unwrap();
    let sources = closure.semantic_module_sources().unwrap();
    assert_eq!(verify_selected_sensitive_type_surfaces(closure), Ok(()));
    for (attack, mutation) in registered_sensitive_surface_mutants(closure, &sources) {
        let changed = mutation
            .iter()
            .filter(|(path, source)| sources.get(*path) != Some(*source))
            .count();
        assert_eq!(changed, 1, "{attack}: exactly one source must change");
        for (path, source) in &mutation {
            assert!(
                syn::parse_file(source).is_ok(),
                "{attack}: {path} must remain syntax-valid"
            );
        }
        let rebuilt = closure.rebuild_with_semantic_module_sources(&mutation);
        match &rebuilt {
            Ok(rebuilt) => assert!(
                verify_selected_sensitive_type_surfaces_internal(rebuilt).is_err(),
                "{attack}: semantic predicate"
            ),
            Err(violation) => assert!(
                matches!(
                    violation,
                    ClosureViolation::ModuleGraph
                        | ClosureViolation::SelectedInputRead
                        | ClosureViolation::SelectedInputAccounting
                        | ClosureViolation::SelectedOwnerMultiplicity
                        | ClosureViolation::OwnerIncomingEdge
                        | ClosureViolation::OwnerBinding
                        | ClosureViolation::OwnerSubtree
                        | ClosureViolation::SanitizerRegistry
                ),
                "{attack}: connected closure predicate"
            ),
        }
        assert_eq!(
            rebuilt
                .as_ref()
                .map_err(|_| "capability-shape")
                .and_then(|closure| verify_selected_sensitive_type_surfaces(closure)),
            Err("capability-shape"),
            "{attack}: registered sensitive-surface verifier"
        );
    }
}

#[test]
fn copied_constructor_owner_macro_is_rejected_by_the_semantic_surface() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let closure = selected_rust_closure(root).unwrap();
    let sources = closure.semantic_module_sources().unwrap();
    let mutation = owner_macro_constructor_witness(closure, &sources);
    let mutation = closure
        .rebuild_with_semantic_module_sources(&mutation)
        .unwrap();
    assert_eq!(
        verify_selected_sensitive_type_surfaces_internal(&mutation),
        Err(SensitiveViolation::ExpansionAuthoritySurface)
    );
    assert_eq!(
        verify_selected_sensitive_type_surfaces(&mutation),
        Err("capability-shape")
    );
}

#[test]
fn all_registered_binding_inputs_are_present_once_in_the_package() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let output = Command::new(env!("CARGO"))
        .args(["package", "--list", "--allow-dirty"])
        .current_dir(root)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "cargo package --list failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let files = String::from_utf8(output.stdout).unwrap();
    let files = files.lines().collect::<Vec<_>>();
    let production_paths = selected_rust_closure(root)
        .unwrap()
        .semantic_module_keys()
        .unwrap()
        .into_iter()
        .collect::<Vec<_>>();
    let mut relevant_package_expected = production_paths
        .iter()
        .filter(|path| relevant_package_rust_candidate(path))
        .cloned()
        .collect::<BTreeSet<_>>();
    relevant_package_expected.extend(
        EXPECTED_RELEVANT_TEST_RUST_SOURCES
            .iter()
            .map(|path| (*path).to_string()),
    );
    assert_eq!(
        classify_relevant_package_candidates(&files, &relevant_package_expected),
        Ok(())
    );
    let mut orphan_package = files.clone();
    orphan_package.push("tests/codex_exec_v0/orphan.rs");
    assert_eq!(
        classify_relevant_package_candidates(&orphan_package, &relevant_package_expected),
        Err("unregistered"),
        "an unknown relevant package source must be rejected"
    );
    let mut aliased_package = files.clone();
    aliased_package.push("./tests/codex_exec_v0/orphan.rs");
    assert_eq!(
        classify_relevant_package_candidates(&aliased_package, &relevant_package_expected),
        Err("noncanonical"),
        "package paths must be canonical before relevance classification"
    );
    assert!(package_path_is_generated("target/debug/generated.rs"));
    assert!(package_path_is_private_output(
        "artifacts/capture.private.jsonl"
    ));
    assert!(package_path_is_owner_only_output(
        "artifacts/owner-private-lineage-sidecar.bin"
    ));
    assert!(package_path_is_named_temporary(
        "artifacts/.legitimacy-tmp-123"
    ));
    let selected_paths = cli_selected_build_paths();
    for path in selected_paths.into_iter().chain(
        [
            "cli/trajectory/linux_output_tests.rs",
            "cli/trajectory/linux_output_transaction_phase_tests.rs",
            "cli/trajectory/linux_output_transaction_tests.rs",
            "cli/trajectory/linux_path_tests.rs",
            "tests/fixtures/codex-exec-v0/source-manifest.json",
            "tests/fixtures/codex-exec-v0/legal-completed.synthetic.jsonl",
            "tests/fixtures/codex-exec-v0/legal-failed.synthetic.jsonl",
            "schemas/trajectory-v0.schema.json",
        ]
        .into_iter()
        .map(str::to_string),
    ) {
        assert_eq!(
            files.iter().filter(|candidate| **candidate == path).count(),
            1,
            "{path} must be packaged exactly once"
        );
    }
    assert!(
        !files.iter().any(|path| package_path_is_generated(path)),
        "generated build artifacts must not be packaged"
    );
    assert!(
        !files
            .iter()
            .any(|path| package_path_is_private_output(path)),
        "private publication outputs must not be packaged"
    );
    assert!(
        !files
            .iter()
            .any(|path| package_path_is_owner_only_output(path)),
        "owner-only lineage artifacts must not be packaged"
    );
    assert!(
        !files
            .iter()
            .any(|path| package_path_is_named_temporary(path)),
        "named publication temporaries must not be packaged"
    );
}

#[test]
fn registered_sources_exclude_forbidden_shortcuts_and_legacy_importer() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let closure = selected_rust_closure(root).unwrap();
    let registered_sources = closure
        .sanitizer_components()
        .iter()
        .filter(|path| **path != "src/trajectory/codex_exec_v0/source_bindings.rs")
        .chain(closure.binary_paths())
        .filter_map(|path| closure.source(path).ok().map(|source| (path, source)))
        .collect::<Vec<_>>();
    let sources = registered_sources
        .iter()
        .map(|(_, source)| *source)
        .collect::<Vec<_>>()
        .join("\n");
    for forbidden in [
        "codex_observed_runtime",
        "validated: bool",
        "enum GenericBundle",
        "TrustedBundleToken",
        "extern \"C\"",
    ] {
        assert!(!sources.contains(forbidden), "{forbidden}");
    }
    for (path, source) in registered_sources {
        if path == "src/trajectory/codex_exec_v0/process_capture_supervisor.rs" {
            assert_eq!(source.matches("unsafe {").count(), 1);
            assert_eq!(source.matches("libc::close").count(), 1);
            assert_eq!(source.matches("libc::fexecve").count(), 1);
            assert_eq!(source.matches("libc::").count(), 2);
            assert!(!source.contains("unsafe fn"));
            continue;
        }
        if path == "src/trajectory/codex_exec_v0/process_capture_signal.rs" {
            assert_eq!(source.matches("unsafe {").count(), 3);
            assert_eq!(source.matches("libc::sigaction").count(), 7);
            assert_eq!(source.matches("libc::pthread_sigmask").count(), 4);
            assert!(source.contains("pidfd_open"));
            assert!(source.contains("pidfd_send_signal"));
            assert!(source.contains("WaitId::PidFd"));
            assert!(!source.contains("kill_process"));
            assert!(!source.contains("kill_process_group"));
            assert!(!source.contains("unsafe fn"));
            continue;
        }
        for forbidden in ["unsafe {", "unsafe fn", "libc::"] {
            assert!(!source.contains(forbidden), "{path}: {forbidden}");
        }
    }
    let bundle_wire =
        std::fs::read_to_string(root.join("src/trajectory/codex_exec_v0/bundle_wire.rs")).unwrap();
    assert!(bundle_wire.contains("TrajectoryTraceV0::from_json_slice"));
    assert!(!bundle_wire.contains("serde_json::from_value::<TrajectoryTraceV0>"));

    let linux_path = std::fs::read_to_string(root.join("cli/trajectory/linux_path.rs")).unwrap();
    assert_eq!(verify_linux_path_forbidden_shortcuts(&linux_path), Ok(()));
    assert_eq!(
        direct_call_argument_profiles(&linux_path, "openat").unwrap(),
        expected_openat_profiles()
    );
    assert_eq!(
        direct_call_argument_profiles(&linux_path, "statat").unwrap(),
        expected_statat_profiles()
    );
    let linux_output =
        std::fs::read_to_string(root.join("cli/trajectory/linux_output.rs")).unwrap();
    assert_eq!(
        verify_linux_output_forbidden_shortcuts(&linux_output),
        Ok(())
    );
    let transaction =
        std::fs::read_to_string(root.join("cli/trajectory/linux_output_transaction.rs")).unwrap();
    assert_eq!(verify_transaction_forbidden_shortcuts(&transaction), Ok(()));
    assert_eq!(
        direct_call_argument_profiles(&transaction, "rustix::process::geteuid").unwrap(),
        vec![
            Vec::<String>::new(),
            Vec::<String>::new(),
            Vec::<String>::new(),
            Vec::<String>::new(),
        ]
    );
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
        assert!(
            direct_call_argument_profiles(&transaction, forbidden_acquisition)
                .unwrap()
                .is_empty(),
            "transaction must not directly acquire filesystem authority through {forbidden_acquisition}"
        );
    }
}
