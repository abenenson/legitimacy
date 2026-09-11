use super::*;

pub(super) const EXPECTED_TRAJECTORY_SOURCE_SHA256: &str =
    "ecc2a5b969d066639492a4d044a741f27e7692af3fe2ab6fb0929d4c664628a7";
pub(super) const EXPECTED_LINUX_PATH_SOURCE_SHA256: &str =
    "5ba947d640088f622ea37c3940314e9f3368d83b4d65dd8a2cc4eb81382b20f1";
pub(super) const EXPECTED_LINUX_OUTPUT_SOURCE_SHA256: &str =
    "357f2a535d7997404b410569305e3a7132e68406d3b20734274bb7f186de7ab3";
pub(super) const EXPECTED_TRANSACTION_SOURCE_SHA256: &str =
    "fa4191cdb25f79455541e07ea38617000721901d64b20d92edc2395cf2cdb7bc";
pub(super) const EXPECTED_OUTPUT_SET_SOURCE_SHA256: &str =
    "753c539c2df9fe90d59be8ad594ef20cef7025bd562fd1418060aac41aa615de";
pub(super) const EXPECTED_COMPOSITION_SOURCE_SHA256: &str =
    "e7d97add4fe0e8a3d1265788d8572dc4c9d30c49d2e8b020e0f06a679dcce0ad";

pub(super) const EXPECTED_ROUTE_SOURCE_SHA256: &[(&str, &str)] = &[
    ("cli/trajectory.rs", EXPECTED_TRAJECTORY_SOURCE_SHA256),
    (
        "cli/trajectory/linux_path.rs",
        EXPECTED_LINUX_PATH_SOURCE_SHA256,
    ),
    (
        "cli/trajectory/linux_output.rs",
        EXPECTED_LINUX_OUTPUT_SOURCE_SHA256,
    ),
    (
        "cli/trajectory/linux_output_transaction.rs",
        EXPECTED_TRANSACTION_SOURCE_SHA256,
    ),
    (
        "cli/trajectory/linux_output_set.rs",
        EXPECTED_OUTPUT_SET_SOURCE_SHA256,
    ),
    (
        "cli/workflow.rs",
        "f1aef448f20836ae02e916ba98457d47b81d5ec9195d2af03f956593aaa9dd02",
    ),
    (
        "cli/trajectory_composition.rs",
        EXPECTED_COMPOSITION_SOURCE_SHA256,
    ),
    (
        "cli/commands.rs",
        "5406b791c3324a40db1e4a92a2ae45c142330bc3b31c07d48436582535ebaaa8",
    ),
    (
        "cli/main.rs",
        "ecd15925db5b48c2f8cb7eaf838ded085f6fbc57496146c8efaba81b80250516",
    ),
    (
        "src/lib.rs",
        "3d342c8cc5a3b1149e652e9cb75bf8d3900378e89e50ae9a498d2b5c863ec390",
    ),
    (
        "src/error.rs",
        "4f99d8eedeb4488dd6f9470166c2058f32a7e382004c6997b6e9c48df9003545",
    ),
];

pub(super) const EXPECTED_TRAJECTORY_CALLS: &[(&str, usize)] = &[
    ("AdapterErrorV0::from_code", 5),
    ("Err", 4),
    ("InputAuthorityReceiptV0::from_json_slice", 1),
    ("InspectedShareableSanitizedBundleV0::from_json_slice", 1),
    ("Ok", 2),
    ("OwnerPrivateLineageSidecarV0::from_binary_slice", 1),
    ("TrustedAdaptationContextV0::from_json_slice", 1),
    ("adapt_codex_exec_owned_v0", 1),
    ("drop", 6),
    ("linux_output::publish", 1),
    ("linux_output::publish_pair", 1),
    ("linux_path::read_snapshot", 3),
    ("linux_path::reject_duplicate_inodes", 1),
    ("method:into_bytes", 1),
    ("method:into_publication_pair", 1),
    ("method:len", 3),
    ("method:ok_or_else", 1),
    ("method:revalidate_public_bundle", 1),
    ("method:to_json_line", 2),
    ("method:to_private_bundle", 1),
    ("method:validate", 1),
    ("sanitize_capture_v0", 1),
    ("std::mem::take", 1),
    ("validate_semantic_pair", 1),
];

pub(super) const EXPECTED_LINUX_PATH_CALLS: &[(&str, usize)] = &[
    ("AdapterErrorV0::from_code", 1),
    ("Err", 17),
    ("FileType::from_raw_mode", 7),
    ("Mode::empty", 5),
    ("Ok", 7),
    ("Path::new", 3),
    ("Some", 3),
    ("Vec::new", 1),
    ("Vec::with_capacity", 1),
    ("directory_identity", 2),
    ("error", 36),
    ("fcntl_getfd", 1),
    ("fcntl_getfl", 1),
    ("fingerprint", 6),
    ("fstat", 5),
    ("fstatfs", 1),
    ("initial_type_error", 1),
    ("macro:format", 1),
    ("method:after_first_chunk", 1),
    ("method:any", 1),
    ("method:as_bytes", 1),
    ("method:as_os_str", 1),
    ("method:before_ancestor_open", 1),
    ("method:before_final_open", 1),
    ("method:checked_add", 1),
    ("method:components", 1),
    ("method:contains", 4),
    ("method:ends_with", 2),
    ("method:enumerate", 2),
    ("method:extend_from_slice", 1),
    ("method:into", 2),
    ("method:is_empty", 1),
    ("method:is_err", 1),
    ("method:iter", 3),
    ("method:len", 4),
    ("method:map_err", 16),
    ("method:min", 2),
    ("method:ok", 2),
    ("method:ok_or_else", 3),
    ("method:pop", 1),
    ("method:proc_root", 1),
    ("method:push", 1),
    ("method:starts_with", 1),
    ("method:to_os_string", 1),
    ("nonnegative_size", 1),
    ("openat", 5),
    ("parse_path", 1),
    ("pin_start", 1),
    ("read_snapshot_with_hooks", 1),
    ("reopen_gate", 1),
    ("require_initial_type", 2),
    ("rustix::io::read", 1),
    ("statat", 3),
    ("u64::try_from", 2),
    ("validate_reader", 1),
    ("verify_held_and_name", 4),
    ("verify_reader_and_name", 2),
    ("widen_i128", 5),
    ("widen_u64", 11),
];

pub(super) const EXPECTED_LINUX_OUTPUT_CALLS: &[(&str, usize)] = &[
    ("AdapterErrorV0::from_code", 1),
    ("AtFlags::empty", 1),
    ("Box::new", 1),
    ("Err", 39),
    ("FileType::from_raw_mode", 8),
    ("Mode::empty", 4),
    ("Mode::from_raw_mode", 2),
    ("Ok", 16),
    ("Path::new", 5),
    ("PublicationEventV0::Attempted", 1),
    ("PublicationEventV0::Completed", 1),
    ("PublicationStageV0::AncestorOpen", 2),
    ("Sha256::digest", 3),
    ("Some", 41),
    ("Vec::new", 1),
    ("Vec::with_capacity", 1),
    ("attempt", 23),
    ("classify_incumbent", 1),
    ("commit_with_hooks", 1),
    ("complete", 23),
    ("drop", 1),
    ("error", 68),
    ("fchmod", 1),
    ("fcntl_getfd", 2),
    ("fcntl_getfl", 2),
    ("flags_are_exact", 2),
    ("fstat", 7),
    ("fstatfs", 1),
    ("fsync", 3),
    ("guard", 1),
    ("identity", 9),
    ("input_alias", 2),
    ("is_link_profile_errno", 1),
    ("is_profile_errno", 3),
    ("linkat", 1),
    ("macro:format", 1),
    ("macro:matches", 2),
    ("method:and_then", 5),
    ("method:any", 2),
    ("method:as_bytes", 1),
    ("method:as_os_str", 1),
    ("method:as_raw", 5),
    ("method:as_raw_fd", 1),
    ("method:bits", 2),
    ("method:checked_add", 1),
    ("method:components", 1),
    ("method:contains", 2),
    ("method:ends_with", 2),
    ("method:enumerate", 1),
    ("method:event", 2),
    ("method:extend_from_slice", 1),
    ("method:fail_before", 1),
    ("method:into", 6),
    ("method:is_empty", 1),
    ("method:is_err", 4),
    ("method:is_ok", 4),
    ("method:is_some_and", 1),
    ("method:iter", 3),
    ("method:len", 8),
    ("method:map_err", 29),
    ("method:min", 1),
    ("method:map", 1),
    ("method:ok", 3),
    ("method:ok_or_else", 2),
    ("method:parent_sync_name", 1),
    ("method:pop", 1),
    ("method:pread", 2),
    ("method:proc_root", 1),
    ("method:proc_source", 1),
    ("method:push", 1),
    ("method:starts_with", 1),
    ("method:to_os_string", 1),
    ("method:write", 1),
    ("method:write_str", 2),
    ("openat", 5),
    ("parse_output_path", 1),
    ("pin_start", 1),
    ("postlink_checks", 1),
    ("preflight_final", 3),
    ("prepare_with_hooks", 1),
    ("protected_alias", 2),
    ("publication_errno", 3),
    ("publish_with_hooks", 1),
    ("require_directory", 1),
    ("rustix::io::pread", 1),
    ("rustix::io::write", 1),
    ("rustix::process::geteuid", 5),
    ("same_directory", 1),
    ("stable_metadata", 5),
    ("statat", 5),
    ("temporary_properties_are_exact", 1),
    ("u64::from", 4),
    ("u64::try_from", 3),
    ("usize::try_from", 1),
    ("verify_final_identity", 1),
    ("verify_held", 3),
    ("verify_proc_source", 2),
    ("verify_sync_directory", 1),
    ("verify_temporary_flags", 1),
    ("widen_i128", 5),
    ("widen_u64", 14),
    ("write_all", 1),
];

pub(super) const EXPECTED_TRANSACTION_CALLS: &[(&str, usize)] = &[
    ("Err", 11),
    ("Ok", 6),
    ("Self::PreLink", 1),
    ("Sha256::digest", 1),
    ("Some", 11),
    ("attempt", 3),
    ("commit_with_hooks", 2),
    ("committed_error_rank", 1),
    ("complete", 3),
    ("drop", 6),
    ("error", 10),
    ("method:and_then", 4),
    ("method:as_bytes", 4),
    ("method:as_os_str", 4),
    ("method:as_raw", 2),
    ("method:code", 2),
    ("method:err", 6),
    ("method:flatten", 1),
    ("method:into_iter", 1),
    ("method:is_err", 3),
    ("method:is_none", 1),
    ("method:is_ok", 3),
    ("method:is_some", 3),
    ("method:len", 1),
    ("method:map_err", 3),
    ("method:reject_cross_output_alias", 1),
    ("method:unwrap_or_else", 1),
    ("prepare_with_hooks", 2),
    ("publish_pair_with_hooks", 1),
    ("rank_errors", 4),
    ("revalidate_committed", 7),
    ("rustix::process::geteuid", 2),
    ("semantic_pair", 1),
    ("verify_final_identity", 1),
    ("verify_held", 1),
];

pub(super) fn flattened_imports(source: &str) -> BTreeSet<String> {
    let syntax = syn::parse_file(source).unwrap();
    let mut imports = BTreeSet::new();
    for item in &syntax.items {
        let syn::Item::Use(item) = item else {
            continue;
        };
        flatten_use_tree_tolerant(Vec::new(), &item.tree, &mut imports);
    }
    imports
}

pub(super) fn flattened_imports_from_syntax(
    syntax: &syn::File,
) -> Result<BTreeSet<String>, &'static str> {
    let mut imports = BTreeSet::new();
    for item in &syntax.items {
        let syn::Item::Use(item) = item else {
            continue;
        };
        flatten_use_tree(Vec::new(), &item.tree, &mut imports)?;
    }
    Ok(imports)
}

pub(super) fn flatten_use_tree(
    mut prefix: Vec<String>,
    tree: &syn::UseTree,
    output: &mut BTreeSet<String>,
) -> Result<(), &'static str> {
    match tree {
        syn::UseTree::Path(path) => {
            prefix.push(path.ident.to_string());
            flatten_use_tree(prefix, &path.tree, output)
        }
        syn::UseTree::Name(name) => {
            prefix.push(name.ident.to_string());
            output.insert(prefix.join("::"));
            Ok(())
        }
        syn::UseTree::Group(group) => {
            for item in &group.items {
                flatten_use_tree(prefix.clone(), item, output)?;
            }
            Ok(())
        }
        syn::UseTree::Rename(_) | syn::UseTree::Glob(_) => Err("route-shape"),
    }
}

pub(super) fn flatten_use_tree_tolerant(
    mut prefix: Vec<String>,
    tree: &syn::UseTree,
    output: &mut BTreeSet<String>,
) {
    match tree {
        syn::UseTree::Path(path) => {
            prefix.push(path.ident.to_string());
            flatten_use_tree_tolerant(prefix, &path.tree, output);
        }
        syn::UseTree::Name(name) => {
            prefix.push(name.ident.to_string());
            output.insert(prefix.join("::"));
        }
        syn::UseTree::Rename(rename) => {
            prefix.push(rename.ident.to_string());
            output.insert(prefix.join("::"));
        }
        syn::UseTree::Glob(_) => {
            prefix.push("*".to_string());
            output.insert(prefix.join("::"));
        }
        syn::UseTree::Group(group) => {
            for item in &group.items {
                flatten_use_tree_tolerant(prefix.clone(), item, output);
            }
        }
    }
}

pub(super) fn call_name_counts(
    node: tree_sitter::Node<'_>,
    source: &[u8],
) -> BTreeMap<String, usize> {
    let mut calls = BTreeMap::new();
    collect_call_names(node, source, &mut calls);
    calls
}

pub(super) fn direct_call_paths_for_source(source: &str) -> BTreeMap<String, usize> {
    let mut parser = rust_parser();
    let tree = parser.parse(source, None).unwrap();
    direct_call_paths(tree.root_node(), source.as_bytes())
}

pub(super) fn publication_entry_call_count<'a>(
    sources: impl IntoIterator<Item = &'a str>,
) -> usize {
    sources
        .into_iter()
        .map(direct_call_paths_for_source)
        .flat_map(BTreeMap::into_iter)
        .filter(|(path, _)| path.ends_with("trajectory::run"))
        .map(|(_, count)| count)
        .sum()
}

pub(super) fn path_suffix_count(source: &str, suffix: &str) -> usize {
    let mut parser = rust_parser();
    let tree = parser.parse(source, None).unwrap();
    count_path_suffix(tree.root_node(), source.as_bytes(), suffix)
}

pub(super) fn count_path_suffix(node: tree_sitter::Node<'_>, source: &[u8], suffix: &str) -> usize {
    let here = usize::from(
        matches!(node.kind(), "identifier" | "scoped_identifier")
            && node.utf8_text(source).unwrap().ends_with(suffix),
    );
    let mut cursor = node.walk();
    here + node
        .named_children(&mut cursor)
        .map(|child| count_path_suffix(child, source, suffix))
        .sum::<usize>()
}

pub(super) fn cli_trajectory_imports_are_exact(relative_path: &str, source: &str) -> bool {
    let actual = flattened_imports(source)
        .into_iter()
        .filter(|path| {
            ["crate::trajectory", "self::trajectory", "super::trajectory"]
                .iter()
                .any(|prefix| path == prefix || path.starts_with(&format!("{prefix}::")))
        })
        .collect::<BTreeSet<_>>();
    let expected = match relative_path {
        "cli/commands.rs" => {
            BTreeSet::from(["crate::trajectory::CodexExecOutputTypeV0".to_string()])
        }
        "cli/trajectory/linux_output_tests.rs" => {
            BTreeSet::from(["crate::trajectory::linux_path::read_snapshot".to_string()])
        }
        _ => BTreeSet::new(),
    };
    actual == expected
}

pub(super) fn collect_call_names(
    node: tree_sitter::Node<'_>,
    source: &[u8],
    calls: &mut BTreeMap<String, usize>,
) {
    if matches!(node.kind(), "call_expression" | "macro_invocation") {
        let callee = if node.kind() == "call_expression" {
            node.child_by_field_name("function").unwrap()
        } else {
            node.child_by_field_name("macro")
                .or_else(|| node.named_child(0))
                .unwrap()
        };
        let name = if node.kind() == "macro_invocation" {
            format!("macro:{}", callee.utf8_text(source).unwrap())
        } else if matches!(callee.kind(), "identifier" | "scoped_identifier") {
            callee.utf8_text(source).unwrap().to_string()
        } else {
            callee
                .child_by_field_name("field")
                .and_then(|field| field.utf8_text(source).ok())
                .map_or_else(
                    || format!("indirect:{}", callee.kind()),
                    |field| format!("method:{field}"),
                )
        };
        *calls.entry(name).or_default() += 1;
    }
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_call_names(child, source, calls);
    }
}

pub(super) fn identifier_count(source: &str, expected: &str) -> usize {
    let mut parser = rust_parser();
    let tree = parser.parse(source, None).unwrap();
    count_identifier(tree.root_node(), source.as_bytes(), expected)
}

pub(super) fn assert_registered_route_sources_are_sealed(root: &Path) {
    for (path, expected) in EXPECTED_ROUTE_SOURCE_SHA256 {
        let source = std::fs::read_to_string(root.join(path)).unwrap();
        assert_eq!(source_sha256(&source), *expected, "{path}");
    }
}

pub(super) fn source_sha256(source: &str) -> String {
    format!("{:x}", Sha256::digest(source.as_bytes()))
}

pub(super) fn registered_rust_sources(root: &Path) -> BTreeMap<String, String> {
    const ROUTE_ONLY_PATHS: &[&str] = &[
        "cli/trajectory.rs",
        "cli/trajectory/linux_path.rs",
        "cli/trajectory/linux_output.rs",
        "cli/trajectory/linux_output_rollback.rs",
        "cli/trajectory/linux_output_transaction.rs",
        "cli/trajectory/linux_output_set.rs",
        "cli/workflow.rs",
        "cli/trajectory_composition.rs",
        "cli/commands.rs",
        "cli/main.rs",
        "src/lib.rs",
        "src/error.rs",
    ];
    ADAPTER_CORE_PATHS
        .iter()
        .chain(SANITIZER_ONLY_PATHS)
        .chain(ROUTE_ONLY_PATHS)
        .map(|path| {
            (
                (*path).to_string(),
                std::fs::read_to_string(root.join(path)).unwrap(),
            )
        })
        .collect()
}

pub(super) fn registered_capability_inventory(root: &Path) -> BTreeMap<(String, String), usize> {
    capability_inventory(&registered_rust_sources(root))
}

pub(super) fn capability_inventory(
    sources: &BTreeMap<String, String>,
) -> BTreeMap<(String, String), usize> {
    const CAPABILITIES: &[&str] = &[
        "adapt_codex_exec_owned_v0",
        "adapt_codex_exec_v0",
        "sanitize_capture_v0",
        "sanitize_capture_with_fixed_test_nonce_v0",
        "ProductionSanitizationTransactionV0",
        "PublicationMintV0",
        "ShareableSanitizedBundleV0",
        "into_publication_pair",
        "OwnerPrivateLineageSidecarV0",
        "from_binary_slice",
        "into_bytes",
        "revalidate_public_bundle",
        "publish_pair",
        "PreparedPublicationV0",
        "CommittedPublicationV0",
        "CommitFailureV0",
        "linkat",
    ];
    let mut inventory = BTreeMap::new();
    for (path, source) in sources {
        for capability in CAPABILITIES {
            let count = identifier_count(source, capability);
            if count > 0 {
                inventory.insert(((*capability).to_string(), path.clone()), count);
            }
        }
    }
    inventory
}

pub(super) fn count_identifier(
    node: tree_sitter::Node<'_>,
    source: &[u8],
    expected: &str,
) -> usize {
    let here = usize::from(
        matches!(
            node.kind(),
            "identifier" | "field_identifier" | "type_identifier"
        ) && node.utf8_text(source).unwrap() == expected,
    );
    let mut cursor = node.walk();
    here + node
        .named_children(&mut cursor)
        .map(|child| count_identifier(child, source, expected))
        .sum::<usize>()
}

pub(super) fn replace_exact_once(source: &str, needle: &str, replacement: &str) -> String {
    assert_eq!(
        source.matches(needle).count(),
        1,
        "mutant source needle must occur exactly once: {needle}"
    );
    source.replacen(needle, replacement, 1)
}

pub(super) fn replace_exact_nth(
    source: &str,
    needle: &str,
    expected_count: usize,
    index: usize,
    replacement: &str,
) -> String {
    let offsets = source
        .match_indices(needle)
        .map(|(offset, _)| offset)
        .collect::<Vec<_>>();
    assert_eq!(
        offsets.len(),
        expected_count,
        "mutant source needle count: {needle}"
    );
    let offset = offsets[index];
    format!(
        "{}{replacement}{}",
        &source[..offset],
        &source[offset + needle.len()..]
    )
}

pub(super) fn assert_source_mutant(attack: &str, source: &str, mutation: &str) {
    assert_ne!(mutation, source, "{attack}: mutation must differ");
    assert!(
        syn::parse_file(mutation).is_ok(),
        "{attack}: mutation must remain syntax-valid"
    );
}
