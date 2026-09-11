use super::*;

fn base_closure() -> &'static PortableSelectedRustClosure {
    selected_rust_closure(Path::new(env!("CARGO_MANIFEST_DIR"))).unwrap()
}

fn append_module(source: &str, declaration: &str) -> String {
    format!("{source}\n{declaration}\n")
}

fn assert_public_capability_error(inputs: SyntheticSelectedRustInputs) {
    assert_eq!(
        verify_synthetic_selected_closure(inputs),
        Err("capability-shape")
    );
}

const PROCESS_PLATFORM: &str = "src/trajectory/codex_exec_v0/process_capture_platform.rs";
const PROCESS_SUPERVISOR: &str = "src/trajectory/codex_exec_v0/process_capture_supervisor.rs";
const PROCESS_SUPERVISION: &str = "src/trajectory/codex_exec_v0/process_capture_supervision.rs";
const PROCESS_CLEANUP: &str = "src/trajectory/codex_exec_v0/process_capture_cleanup.rs";

fn verify_extracted_process_topology(
    closure: &PortableSelectedRustClosure,
) -> Result<(), &'static str> {
    let expected_roles = BTreeSet::from([
        SelectedInputRole::LibraryModule,
        SelectedInputRole::EmbeddedData,
    ]);
    let edges = closure.module_edges();
    for path in [PROCESS_SUPERVISOR, PROCESS_SUPERVISION, PROCESS_CLEANUP] {
        if closure.input_roles(path) != Some(&expected_roles)
            || closure
                .adapter_components()
                .iter()
                .filter(|component| component.as_str() == path)
                .count()
                != 1
            || !edges.contains(&(PROCESS_PLATFORM.to_string(), path.to_string()))
        {
            return Err("process-topology");
        }
    }
    let platform = closure.source(PROCESS_PLATFORM)?;
    let supervisor = closure.source(PROCESS_SUPERVISOR)?;
    let supervision = closure.source(PROCESS_SUPERVISION)?;
    let cleanup = closure.source(PROCESS_CLEANUP)?;
    for declaration in [
        "#[path = \"process_capture_cleanup.rs\"]\nmod cleanup;",
        "#[path = \"process_capture_supervision.rs\"]\nmod supervision;",
        "#[path = \"process_capture_supervisor.rs\"]\nmod supervisor;",
    ] {
        if platform.matches(declaration).count() != 1 {
            return Err("process-topology");
        }
    }
    if supervisor.matches("supervise_spawned_child(").count() != 1
        || supervisor.matches("contain_pidfd_receipt_failure(").count() != 2
        || supervisor.contains("cleanup_process_tree(")
        || supervisor.contains("PrimaryCaptureFailure")
        || supervision.contains("super::supervisor")
        || supervision.matches("fn cleanup_process_tree(").count() != 0
        || supervision.matches("select_supervision_decision(").count() < 3
        || cleanup
            .matches("pub(super) fn cleanup_process_tree(")
            .count()
            != 1
        || cleanup.contains("PrimaryCaptureFailure")
    {
        return Err("process-topology");
    }
    Ok(())
}

#[test]
fn extracted_process_modules_are_active_registered_single_owners() {
    let closure = base_closure();
    assert_eq!(verify_extracted_process_topology(closure), Ok(()));
    assert_eq!(verify_selected_sensitive_type_surfaces(closure), Ok(()));
}

#[test]
fn extracted_process_topology_mutations_fail_closed() {
    let closure = base_closure();

    let mut compiled_out = closure.synthetic_inputs();
    compiled_out.replace_bytes(PROCESS_PLATFORM, |source| {
        replace_exact_once(
            source,
            "#[path = \"process_capture_cleanup.rs\"]\nmod cleanup;",
            "#[cfg(test)]\n#[path = \"process_capture_cleanup.rs\"]\nmod cleanup;",
        )
    });
    let embedded_only = compiled_out
        .clone()
        .build()
        .expect("compiled-out cleanup remains compiler-read as embedded data");
    assert_eq!(
        embedded_only.input_roles(PROCESS_CLEANUP),
        Some(&BTreeSet::from([SelectedInputRole::EmbeddedData])),
        "compiled-out cleanup"
    );
    assert!(
        !embedded_only
            .module_edges()
            .contains(&(PROCESS_PLATFORM.to_string(), PROCESS_CLEANUP.to_string())),
        "compiled-out cleanup"
    );
    assert_eq!(
        verify_extracted_process_topology(&embedded_only),
        Err("process-topology"),
        "compiled-out cleanup"
    );
    assert_public_capability_error(compiled_out);

    let mut wrong_path = closure.synthetic_inputs();
    wrong_path.replace_bytes(PROCESS_PLATFORM, |source| {
        replace_exact_once(
            source,
            "#[path = \"process_capture_cleanup.rs\"]\nmod cleanup;",
            "#[path = \"process_capture_output.rs\"]\nmod cleanup;",
        )
    });
    let embedded_only = wrong_path
        .clone()
        .build()
        .expect("wrong-path cleanup remains compiler-read as embedded data");
    assert_eq!(
        embedded_only.input_roles(PROCESS_CLEANUP),
        Some(&BTreeSet::from([SelectedInputRole::EmbeddedData])),
        "wrong cleanup module path"
    );
    assert!(
        !embedded_only
            .module_edges()
            .contains(&(PROCESS_PLATFORM.to_string(), PROCESS_CLEANUP.to_string())),
        "wrong cleanup module path"
    );
    assert_eq!(
        verify_extracted_process_topology(&embedded_only),
        Err("process-topology"),
        "wrong cleanup module path"
    );
    assert_public_capability_error(wrong_path);

    let binding = closure.binding_source_path();
    let cleanup_registration = "    (\n        \"src/trajectory/codex_exec_v0/process_capture_cleanup.rs\",\n        include_bytes!(\"process_capture_cleanup.rs\"),\n    ),\n";
    let mut omitted = closure.synthetic_inputs();
    omitted.replace_bytes(binding, |source| {
        replace_exact_once(source, cleanup_registration, "")
    });
    let unregistered = omitted
        .clone()
        .build()
        .expect("omitted cleanup registry remains an active library module");
    assert_eq!(
        unregistered.input_roles(PROCESS_CLEANUP),
        Some(&BTreeSet::from([SelectedInputRole::LibraryModule])),
        "omitted cleanup registry component"
    );
    assert!(
        unregistered
            .module_edges()
            .contains(&(PROCESS_PLATFORM.to_string(), PROCESS_CLEANUP.to_string())),
        "omitted cleanup registry component"
    );
    assert_eq!(
        unregistered
            .adapter_components()
            .iter()
            .filter(|component| component.as_str() == PROCESS_CLEANUP)
            .count(),
        0,
        "omitted cleanup registry component"
    );
    assert_eq!(
        unregistered
            .sanitizer_components()
            .iter()
            .filter(|component| component.as_str() == PROCESS_CLEANUP)
            .count(),
        0,
        "omitted cleanup registry component"
    );
    assert_eq!(
        verify_extracted_process_topology(&unregistered),
        Err("process-topology"),
        "omitted cleanup registry component"
    );
    assert_public_capability_error(omitted);

    let mut duplicated = closure.synthetic_inputs();
    duplicated.replace_bytes(binding, |source| {
        replace_exact_once(
            source,
            cleanup_registration,
            &cleanup_registration.repeat(2),
        )
    });
    assert_eq!(
        duplicated.clone().build(),
        Err(ClosureViolation::SanitizerRegistry),
        "duplicated cleanup registry component"
    );
    assert_public_capability_error(duplicated);

    let mut sources = closure.semantic_module_sources().unwrap();
    let supervisor = sources.get(PROCESS_SUPERVISOR).unwrap();
    let bypass = replace_exact_once(
        supervisor,
        "Ok(main_pidfd) => supervise_spawned_child(",
        "Ok(main_pidfd) => super::cleanup::cleanup_process_tree(",
    );
    sources.insert(PROCESS_SUPERVISOR.to_string(), bypass);
    let bypass = closure
        .rebuild_with_semantic_module_sources(&sources)
        .unwrap();
    assert_eq!(
        verify_extracted_process_topology(&bypass),
        Err("process-topology"),
        "spawn-to-cleanup bypass"
    );
}

#[test]
fn selected_artifacts_propagate_roots_and_reject_duplicate_dependency_entries() {
    let closure = base_closure();
    assert_eq!(closure.library_root(), "src/lib.rs");
    assert_eq!(closure.binary_root(), "cli/main.rs");
    assert!(!closure.library_artifact().profile_test());
    assert!(!closure.binary_artifact().profile_test());
    assert!(closure.library_artifact().features().is_empty());
    assert!(closure.binary_artifact().features().is_empty());
    assert!(
        closure
            .library_artifact()
            .filenames()
            .iter()
            .any(|path| path.ends_with(".rlib"))
    );
    assert!(!closure.binary_artifact().filenames().is_empty());
    assert_eq!(
        closure.selected_paths(),
        closure
            .binary_paths()
            .union(closure.library_paths())
            .cloned()
            .collect()
    );
    assert!(
        closure
            .embedded_data()
            .contains("schemas/trajectory-v0.schema.json")
    );
    assert!(!closure.adapter_components().is_empty());
    assert!(
        closure
            .library_artifact()
            .raw_dep_info_entries()
            .iter()
            .any(|path| path == closure.library_root())
    );

    let mut library_root = closure.synthetic_inputs();
    library_root.set_library_artifact_root("src/error.rs");
    assert_eq!(
        library_root.clone().build(),
        Err(ClosureViolation::ArtifactRoot)
    );
    assert_public_capability_error(library_root);

    let mut binary_root = closure.synthetic_inputs();
    binary_root.set_binary_artifact_root("cli/commands.rs");
    assert_eq!(
        binary_root.clone().build(),
        Err(ClosureViolation::ArtifactRoot)
    );
    assert_public_capability_error(binary_root);

    let mut test_profile = closure.synthetic_inputs();
    test_profile.set_library_profile_test(true);
    assert_eq!(
        test_profile.clone().build(),
        Err(ClosureViolation::ArtifactIdentity)
    );
    assert_public_capability_error(test_profile);

    let owner = closure.owner_path().to_string();
    let mut duplicate = closure.synthetic_inputs();
    duplicate.duplicate_library_dep_info(&owner);
    assert_eq!(
        duplicate.clone().build(),
        Err(ClosureViolation::DuplicateDepInfo)
    );
    assert_public_capability_error(duplicate);
}

#[test]
fn module_resolution_cfg_and_embedded_input_accounting_are_exact() {
    let closure = base_closure();
    let root = closure.library_root();

    for path in ["src/closure_flat.rs", "src/closure_flat/mod.rs"] {
        let mut inputs = closure.synthetic_inputs();
        inputs.replace_bytes(root, |source| append_module(source, "mod closure_flat;"));
        inputs.insert_library_source(path, "pub fn selected() {}\n".to_string());
        assert!(inputs.clone().build().is_ok(), "{path}");
    }

    let mut ambiguous = closure.synthetic_inputs();
    ambiguous.replace_bytes(root, |source| append_module(source, "mod closure_flat;"));
    ambiguous.insert_library_source("src/closure_flat.rs", "pub fn flat() {}\n".to_string());
    ambiguous.insert_library_source(
        "src/closure_flat/mod.rs",
        "pub fn directory() {}\n".to_string(),
    );
    assert_eq!(
        ambiguous.clone().build(),
        Err(ClosureViolation::ModuleGraph)
    );
    assert_public_capability_error(ambiguous);

    let mut inline_path = closure.synthetic_inputs();
    inline_path.replace_bytes(root, |source| {
        append_module(
            source,
            "mod closure_inline { #[path = \"nested.rs\"] mod leaf; }",
        )
    });
    inline_path.insert_library_source(
        "src/closure_inline/nested.rs",
        "pub fn nested() {}\n".to_string(),
    );
    assert!(inline_path.build().is_ok());

    let mut non_mod_inline_path = closure.synthetic_inputs();
    non_mod_inline_path.replace_bytes(root, |source| append_module(source, "mod closure_file;"));
    non_mod_inline_path.insert_library_source(
        "src/closure_file.rs",
        "mod inline { #[path = \"nested.rs\"] mod leaf; }\n".to_string(),
    );
    non_mod_inline_path.insert_library_source(
        "src/closure_file/inline/nested.rs",
        "pub fn nested() {}\n".to_string(),
    );
    assert!(non_mod_inline_path.build().is_ok());

    let mut inactive_test = closure.synthetic_inputs();
    inactive_test.replace_bytes(root, |source| {
        append_module(source, "#[cfg(test)] mod absent_test_module;")
    });
    assert!(inactive_test.build().is_ok());

    let mut active_non_test = closure.synthetic_inputs();
    active_non_test.replace_bytes(root, |source| {
        append_module(source, "#[cfg(not(test))] mod absent_non_test_module;")
    });
    assert_eq!(
        active_non_test.clone().build(),
        Err(ClosureViolation::ModuleGraph)
    );
    assert_public_capability_error(active_non_test);

    let mut feature = closure.synthetic_inputs();
    feature.set_library_features(BTreeSet::from(["closure-feature".to_string()]));
    feature.replace_bytes(root, |source| {
        append_module(
            source,
            "#[cfg(feature = \"closure-feature\")] mod closure_feature;",
        )
    });
    feature.insert_library_source(
        "src/closure_feature.rs",
        "pub fn configured() {}\n".to_string(),
    );
    assert!(feature.build().is_ok());

    for attribute in [
        "#[cfg(target_os = \"linux\")]",
        "#[cfg(arbitrary_route)]",
        "#[cfg_attr(target_os = \"linux\", path = \"closure_target.rs\")]",
    ] {
        let mut unsupported = closure.synthetic_inputs();
        unsupported.replace_bytes(root, |source| {
            append_module(source, &format!("{attribute} mod closure_target;"))
        });
        assert_eq!(
            unsupported.clone().build(),
            Err(ClosureViolation::ModuleGraph),
            "{attribute}"
        );
        assert_public_capability_error(unsupported);
    }

    let mut cfg_attr_path = closure.synthetic_inputs();
    cfg_attr_path.set_library_features(BTreeSet::from(["closure-feature".to_string()]));
    cfg_attr_path.replace_bytes(root, |source| {
        append_module(
            source,
            "#[cfg_attr(feature = \"closure-feature\", path = \"closure_selected.rs\")] mod closure_named;",
        )
    });
    cfg_attr_path.insert_library_source(
        "src/closure_selected.rs",
        "pub fn selected() {}\n".to_string(),
    );
    assert!(cfg_attr_path.build().is_ok());
}

#[test]
fn includes_role_overlap_and_selected_source_mismatches_fail_closed() {
    let closure = base_closure();
    let root = closure.library_root();

    for invocation in [
        "include!(\"closure_tokens.rs\");",
        "include!(concat!(\"closure_\", \"tokens.rs\"));",
        "include!(\"closure_tokens.txt\");",
        "macro_rules! generated { () => { include!(\"closure_tokens.rs\"); } }",
        "const DYNAMIC_BYTES: &[u8] = include_bytes!(concat!(\"closure_\", \"bytes.bin\"));",
    ] {
        let mut inputs = closure.synthetic_inputs();
        inputs.replace_bytes(root, |source| append_module(source, invocation));
        assert_eq!(
            inputs.clone().build(),
            Err(ClosureViolation::ModuleGraph),
            "{invocation}"
        );
        assert_public_capability_error(inputs);
    }

    let mut overlap = closure.synthetic_inputs();
    overlap.replace_bytes(root, |source| {
        append_module(
            source,
            "mod closure_overlap;\nconst CLOSURE_OVERLAP: &[u8] = include_bytes!(\"closure_overlap.rs\");",
        )
    });
    overlap.insert_library_source(
        "src/closure_overlap.rs",
        "pub fn overlap() {}\n".to_string(),
    );
    let overlap = overlap.build().unwrap();
    assert_eq!(
        overlap.input_roles("src/closure_overlap.rs"),
        Some(&BTreeSet::from([
            SelectedInputRole::LibraryModule,
            SelectedInputRole::EmbeddedData,
        ]))
    );

    let mut embedded_text = closure.synthetic_inputs();
    embedded_text.replace_bytes(root, |source| {
        append_module(
            source,
            "const EMBEDDED_TEXT: &str = include_str!(\"closure_policy.txt\");",
        )
    });
    embedded_text.insert_library_source("src/closure_policy.txt", "selected policy\n".to_string());
    let embedded_text = embedded_text.build().unwrap();
    assert_eq!(
        embedded_text.input_roles("src/closure_policy.txt"),
        Some(&BTreeSet::from([SelectedInputRole::EmbeddedData]))
    );

    let mut selected_omission = closure.synthetic_inputs();
    selected_omission.insert_library_source(
        "src/unreachable_selected.rs",
        "pub fn unreachable() {}\n".to_string(),
    );
    assert_eq!(
        selected_omission.clone().build(),
        Err(ClosureViolation::SelectedInputAccounting)
    );
    assert_public_capability_error(selected_omission);

    let mut active_missing = closure.synthetic_inputs();
    active_missing.replace_bytes(root, |source| {
        append_module(source, "mod missing_selected_source;")
    });
    assert_eq!(
        active_missing.clone().build(),
        Err(ClosureViolation::ModuleGraph)
    );
    assert_public_capability_error(active_missing);

    let mut selected_source_omission = closure.synthetic_inputs();
    selected_source_omission.remove_library_source("src/error.rs");
    assert_eq!(
        selected_source_omission.clone().build(),
        Err(ClosureViolation::ModuleGraph)
    );
    assert_public_capability_error(selected_source_omission);
}

#[test]
fn owner_cardinality_registry_and_descriptor_binding_are_connected() {
    let closure = base_closure();
    let owner = closure.owner_path();
    assert_eq!(closure.owner_incoming_count(), 1);
    assert_eq!(
        closure
            .sanitizer_components()
            .iter()
            .filter(|path| *path == owner)
            .count(),
        1
    );

    let mut zero_owner = closure.synthetic_inputs();
    zero_owner.replace_bytes(owner, |source| {
        replace_exact_once(
            source,
            "struct PublicationMintV0 {",
            "struct RetiredPublicationMintV0 {",
        )
    });
    assert_eq!(
        zero_owner.clone().build(),
        Err(ClosureViolation::SelectedOwnerMultiplicity)
    );
    assert_public_capability_error(zero_owner);

    let owner_parent = closure.owner_parent();
    let sibling = Path::new(owner)
        .with_file_name("duplicate_authority.rs")
        .to_string_lossy()
        .into_owned();
    let mut duplicate_owner = closure.synthetic_inputs();
    duplicate_owner.replace_bytes(owner_parent, |source| {
        append_module(source, "mod duplicate_authority;")
    });
    duplicate_owner.insert_library_source(&sibling, closure.source(owner).unwrap().to_string());
    assert_eq!(
        duplicate_owner.clone().build(),
        Err(ClosureViolation::SelectedOwnerMultiplicity)
    );
    assert_public_capability_error(duplicate_owner);

    let binding_source = closure.binding_source_path();
    let divergent_label = Path::new(owner)
        .with_file_name("divergent_authority.rs")
        .to_string_lossy()
        .into_owned();
    let mut divergence = closure.synthetic_inputs();
    divergence.replace_bytes(binding_source, |source| {
        replace_exact_once(source, owner, &divergent_label)
    });
    assert_eq!(
        divergence.clone().build(),
        Err(ClosureViolation::SanitizerRegistry)
    );
    assert_public_capability_error(divergence);
}

fn switched_owner_parent(source: &str, old_module: &str, sibling_module: &str) -> String {
    let source = replace_exact_once(
        source,
        &format!("mod {old_module};"),
        &format!("mod {old_module};\nmod {sibling_module};"),
    );
    replace_exact_once(
        &source,
        &format!("pub use {old_module}::{{"),
        &format!("pub use {sibling_module}::{{"),
    )
}

#[test]
fn selected_sibling_is_discovered_when_the_manual_universe_omits_it() {
    let closure = base_closure();
    let owner = closure.owner_path();
    let owner_parent = closure.owner_parent();
    let owner_module = Path::new(owner)
        .file_stem()
        .unwrap()
        .to_string_lossy()
        .into_owned();
    let sibling_module = "alternate_authority";
    let sibling = Path::new(owner)
        .with_file_name(format!("{sibling_module}.rs"))
        .to_string_lossy()
        .into_owned();
    let repeated = format!(
        "{}\nimpl ShareableSanitizedBundleV0 {{ pub fn repeated(&self) -> Self {{ Self {{ bytes: self.bytes.clone() }} }} }}\n",
        closure.source(owner).unwrap()
    );
    assert!(syn::parse_file(&repeated).is_ok());

    let mut inputs = closure.synthetic_inputs();
    inputs.replace_bytes(owner_parent, |source| {
        switched_owner_parent(source, &owner_module, sibling_module)
    });
    inputs.insert_library_source(&sibling, repeated);
    assert!(inputs.selected_library_contains(&sibling));
    assert!(
        inputs
            .active_graph()
            .unwrap()
            .module_files()
            .contains(&sibling)
    );
    assert_eq!(
        inputs.clone().build(),
        Err(ClosureViolation::SelectedOwnerMultiplicity)
    );
    assert_public_capability_error(inputs);
}

#[test]
fn relocated_owner_is_path_independent_and_borrowed_reconstruction_is_rejected() {
    let closure = base_closure();
    let owner = closure.owner_path();
    let owner_parent = closure.owner_parent();
    let binding_source = closure.binding_source_path();
    let owner_module = Path::new(owner)
        .file_stem()
        .unwrap()
        .to_string_lossy()
        .into_owned();
    let sibling_module = "relocated_authority";
    let sibling = Path::new(owner)
        .with_file_name(format!("{sibling_module}.rs"))
        .to_string_lossy()
        .into_owned();
    let sibling_filename = Path::new(&sibling)
        .file_name()
        .unwrap()
        .to_string_lossy()
        .into_owned();
    let owner_filename = Path::new(owner)
        .file_name()
        .unwrap()
        .to_string_lossy()
        .into_owned();
    let owner_registration = format!(
        "    (\n        \"{owner}\",\n        include_bytes!(\"{owner_filename}\"),\n    ),\n"
    );
    let sibling_registration = format!(
        "    (\n        \"{sibling}\",\n        include_bytes!(\"{sibling_filename}\"),\n    ),\n"
    );

    let mut relocated = closure.synthetic_inputs();
    relocated.replace_bytes(owner_parent, |source| {
        switched_owner_parent(source, &owner_module, sibling_module)
    });
    relocated.replace_bytes(owner, |_| "pub(crate) fn retained_stub() {}\n".to_string());
    relocated.insert_library_source(&sibling, closure.source(owner).unwrap().to_string());
    relocated.replace_bytes(binding_source, |source| {
        replace_exact_once(
            source,
            &owner_registration,
            &format!("{owner_registration}{sibling_registration}"),
        )
    });
    assert!(relocated.selected_library_contains(&sibling));
    let relocated = relocated.build().unwrap();
    assert_eq!(relocated.owner_path(), sibling);
    assert_eq!(relocated.owner_incoming_count(), 1);
    let active_component_roles = BTreeSet::from([
        SelectedInputRole::LibraryModule,
        SelectedInputRole::EmbeddedData,
    ]);
    for path in [owner, sibling.as_str()] {
        assert_eq!(
            relocated
                .sanitizer_components()
                .iter()
                .filter(|component| component.as_str() == path)
                .count(),
            1,
            "{path}"
        );
        assert_eq!(relocated.input_roles(path), Some(&active_component_roles));
    }
    assert_eq!(verify_selected_sensitive_type_surfaces(&relocated), Ok(()));
    let mut borrowed = relocated.synthetic_inputs();
    borrowed.replace_bytes(&sibling, |source| {
        format!(
            "{source}\nimpl ShareableSanitizedBundleV0 {{ pub fn repeated(&self) -> Self {{ Self {{ bytes: self.bytes.clone() }} }} }}\n"
        )
    });
    let borrowed = borrowed.build().unwrap();
    assert_eq!(borrowed.owner_path(), sibling);
    assert_eq!(borrowed.owner_incoming_count(), 1);
    assert!(
        borrowed
            .sanitizer_components()
            .iter()
            .any(|path| path == &sibling)
    );
    assert_eq!(
        verify_selected_sensitive_type_surfaces_internal(&borrowed),
        Err(SensitiveViolation::BorrowedConstruction)
    );
    assert_eq!(
        verify_selected_sensitive_type_surfaces(&borrowed),
        Err("capability-shape")
    );
}
