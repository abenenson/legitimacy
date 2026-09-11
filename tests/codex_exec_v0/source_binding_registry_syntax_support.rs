use super::*;

pub(super) fn verify_linux_path_forbidden_shortcuts(source: &str) -> Result<(), &'static str> {
    syn::parse_file(source).map_err(|_| "route-shape")?;
    for forbidden in [
        "std::fs::metadata(",
        "std::fs::symlink_metadata(",
        "std::fs::read(",
        "File::open(",
        "OpenOptions::new()",
        "libc::",
        "unsafe {",
        "unsafe fn",
    ] {
        if source.contains(forbidden) {
            return Err("route-shape");
        }
    }
    if source
        .matches("let source = format!(\"self/fd/{}\", gate.as_raw_fd());")
        .count()
        != 1
        || source
            .matches("// This verified procfs gate is the sole intentional follow")
            .count()
            != 1
    {
        return Err("route-shape");
    }
    let mut parser = rust_parser();
    let tree = parser.parse(source, None).ok_or("route-shape")?;
    if tree.root_node().has_error() {
        return Err("route-shape");
    }
    let calls = call_name_counts(tree.root_node(), source.as_bytes());
    if ["macro:include", "macro:include_bytes", "macro:include_str"]
        .iter()
        .any(|name| calls.contains_key(*name))
    {
        return Err("route-shape");
    }
    Ok(())
}

pub(super) fn verify_trajectory_module_edge(
    source: &str,
) -> Result<BTreeSet<&'static str>, &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "module-edge")?;
    let modules = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Mod(module) if module.content.is_none() => Some(module),
            _ => None,
        })
        .collect::<Vec<_>>();
    if modules.len() != 2 {
        return Err("module-edge");
    }
    let mut targets = BTreeSet::new();
    for module in modules {
        if !matches!(module.vis, syn::Visibility::Inherited)
            || module.attrs.len() != 1
            || !cfg_attribute_is(&module.attrs[0], "target_os = \"linux\"")
        {
            return Err("module-edge");
        }
        match module.ident.to_string().as_str() {
            "linux_path" => {
                targets.insert("cli/trajectory/linux_path.rs");
            }
            "linux_output" => {
                targets.insert("cli/trajectory/linux_output.rs");
            }
            _ => return Err("module-edge"),
        }
    }
    Ok(targets)
}

pub(super) fn verify_linux_path_test_module_edge(
    source: &str,
) -> Result<&'static str, &'static str> {
    verify_test_module_edge(
        source,
        "tests",
        "linux_path_tests.rs",
        "cli/trajectory/linux_path_tests.rs",
    )
}

pub(super) fn verify_linux_output_module_edges(
    source: &str,
) -> Result<BTreeSet<&'static str>, &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "module-edge")?;
    let modules = external_modules(&syntax);
    if modules.len() != 3 {
        return Err("module-edge");
    }
    let rollback = modules[0];
    let transaction = modules[1];
    let tests = modules[2];
    if rollback.ident != "rollback"
        || !matches!(rollback.vis, syn::Visibility::Inherited)
        || rollback.attrs.len() != 1
        || path_attribute_value(&rollback.attrs[0]).as_deref() != Some("linux_output_rollback.rs")
        || transaction.ident != "transaction"
        || !matches!(transaction.vis, syn::Visibility::Inherited)
        || transaction.attrs.len() != 1
        || path_attribute_value(&transaction.attrs[0]).as_deref()
            != Some("linux_output_transaction.rs")
        || tests.ident != "tests"
        || !matches!(tests.vis, syn::Visibility::Inherited)
        || !attributes_are_exact_test_path(&tests.attrs, "linux_output_tests.rs")
    {
        return Err("module-edge");
    }
    Ok(BTreeSet::from([
        "cli/trajectory/linux_output_rollback.rs",
        "cli/trajectory/linux_output_transaction.rs",
        "cli/trajectory/linux_output_tests.rs",
    ]))
}

pub(super) fn verify_transaction_module_edges(
    source: &str,
) -> Result<BTreeSet<&'static str>, &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "module-edge")?;
    let modules = external_modules(&syntax);
    if modules.len() != 3 {
        return Err("module-edge");
    }
    let output_set = modules[0];
    let output_set_tests = modules[1];
    let tests = modules[2];
    if output_set.ident != "output_set"
        || !matches!(output_set.vis, syn::Visibility::Inherited)
        || output_set.attrs.len() != 1
        || path_attribute_value(&output_set.attrs[0]).as_deref() != Some("linux_output_set.rs")
        || output_set_tests.ident != "output_set_tests"
        || !matches!(output_set_tests.vis, syn::Visibility::Inherited)
        || !attributes_are_exact_test_path(&output_set_tests.attrs, "linux_output_set_tests.rs")
        || tests.ident != "tests"
        || !matches!(tests.vis, syn::Visibility::Inherited)
        || !attributes_are_exact_test_path(&tests.attrs, "linux_output_transaction_tests.rs")
    {
        return Err("module-edge");
    }
    Ok(BTreeSet::from([
        "cli/trajectory/linux_output_set.rs",
        "cli/trajectory/linux_output_set_tests.rs",
        "cli/trajectory/linux_output_transaction_tests.rs",
    ]))
}

pub(super) fn verify_transaction_phase_test_module_edge(
    source: &str,
) -> Result<&'static str, &'static str> {
    verify_test_module_edge(
        source,
        "phase_tests",
        "linux_output_transaction_phase_tests.rs",
        "cli/trajectory/linux_output_transaction_phase_tests.rs",
    )
}

pub(super) fn verify_test_module_edge(
    source: &str,
    expected_ident: &str,
    expected_file: &str,
    expected_target: &'static str,
) -> Result<&'static str, &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "module-edge")?;
    let modules = external_modules(&syntax);
    let Some(module) = modules.first() else {
        return Err("module-edge");
    };
    if modules.len() != 1
        || module.ident != expected_ident
        || !matches!(module.vis, syn::Visibility::Inherited)
        || !attributes_are_exact_test_path(&module.attrs, expected_file)
    {
        return Err("module-edge");
    }
    Ok(expected_target)
}

pub(super) fn external_modules(syntax: &syn::File) -> Vec<&syn::ItemMod> {
    syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Mod(module) if module.content.is_none() => Some(module),
            _ => None,
        })
        .collect()
}

pub(super) fn attributes_are_exact_test_path(
    attributes: &[syn::Attribute],
    expected_file: &str,
) -> bool {
    attributes.len() == 2
        && cfg_attribute_is(&attributes[0], "test")
        && path_attribute_value(&attributes[1]).as_deref() == Some(expected_file)
}

pub(super) fn cfg_attribute_is(attribute: &syn::Attribute, expected: &str) -> bool {
    let syn::Meta::List(list) = &attribute.meta else {
        return false;
    };
    list.path.is_ident("cfg") && list.tokens.to_string() == expected
}

pub(super) fn path_attribute_value(attribute: &syn::Attribute) -> Option<String> {
    let syn::Meta::NameValue(value) = &attribute.meta else {
        return None;
    };
    if !value.path.is_ident("path") {
        return None;
    }
    let syn::Expr::Lit(syn::ExprLit {
        lit: syn::Lit::Str(value),
        ..
    }) = &value.value
    else {
        return None;
    };
    Some(value.value())
}

pub(super) fn direct_call_argument_profiles(
    source: &str,
    expected_callee: &str,
) -> Result<Vec<Vec<String>>, &'static str> {
    let mut parser = rust_parser();
    let tree = parser.parse(source, None).ok_or("route-shape")?;
    if tree.root_node().has_error() {
        return Err("route-shape");
    }
    let mut profiles = Vec::new();
    collect_direct_call_argument_profiles(
        tree.root_node(),
        source.as_bytes(),
        expected_callee,
        &mut profiles,
    )?;
    Ok(profiles)
}

pub(super) fn collect_direct_call_argument_profiles(
    node: tree_sitter::Node<'_>,
    source: &[u8],
    expected_callee: &str,
    profiles: &mut Vec<Vec<String>>,
) -> Result<(), &'static str> {
    if node.kind() == "call_expression" {
        let callee = node.child_by_field_name("function").ok_or("route-shape")?;
        if callee.utf8_text(source).map_err(|_| "route-shape")? == expected_callee {
            let arguments = node.child_by_field_name("arguments").ok_or("route-shape")?;
            let mut cursor = arguments.walk();
            profiles.push(
                arguments
                    .named_children(&mut cursor)
                    .map(|argument| {
                        argument
                            .utf8_text(source)
                            .map(compact_source)
                            .map_err(|_| "route-shape")
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
        }
    }
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_direct_call_argument_profiles(child, source, expected_callee, profiles)?;
    }
    Ok(())
}

pub(super) fn compact_source(source: &str) -> String {
    source.split_whitespace().collect()
}

pub(super) fn expected_openat_profiles() -> Vec<Vec<String>> {
    [
        [
            "&parent",
            "component",
            "OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC",
            "Mode::empty()",
        ],
        [
            "&parent",
            "&parsed.final_name",
            "OFlags::PATH | OFlags::NOFOLLOW | OFlags::CLOEXEC",
            "Mode::empty()",
        ],
        [
            "rustix::fs::CWD",
            "proc_root",
            "OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC",
            "Mode::empty()",
        ],
        [
            "&proc",
            "source",
            "OFlags::RDONLY | OFlags::NONBLOCK | OFlags::CLOEXEC",
            "Mode::empty()",
        ],
        [
            "rustix::fs::CWD",
            "if absolute { Path::new(\"/\") } else { Path::new(\".\") }",
            "OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC",
            "Mode::empty()",
        ],
    ]
    .into_iter()
    .map(|profile| profile.into_iter().map(compact_source).collect())
    .collect()
}

pub(super) fn expected_statat_profiles() -> Vec<Vec<String>> {
    [
        ["&parent", "component", "AtFlags::SYMLINK_NOFOLLOW"],
        ["&parent", "&parsed.final_name", "AtFlags::SYMLINK_NOFOLLOW"],
        ["parent", "final_name", "AtFlags::SYMLINK_NOFOLLOW"],
    ]
    .into_iter()
    .map(|profile| profile.into_iter().map(compact_source).collect())
    .collect()
}

pub(super) fn compact_profile(arguments: &[&str]) -> Vec<String> {
    arguments
        .iter()
        .map(|argument| compact_source(argument))
        .collect()
}

pub(super) fn expected_transaction_revalidation_profiles() -> Vec<Vec<String>> {
    [
        ["prior", "bytes", "&mut NoPublicationHooksV0"],
        ["publication", "bytes", "&mut NoPublicationHooksV0"],
        ["publication", "bytes", "&mut NoPublicationHooksV0"],
        ["&committed", "sidecar_bytes", "sidecar_hooks"],
        ["&sidecar", "sidecar_bytes", "sidecar_hooks"],
        ["&sidecar", "sidecar_bytes", "sidecar_hooks"],
        ["&sidecar", "sidecar_bytes", "sidecar_hooks"],
        ["&public", "public_bytes", "public_hooks"],
        ["&sidecar", "sidecar_bytes", "sidecar_hooks"],
        ["&public", "public_bytes", "public_hooks"],
    ]
    .into_iter()
    .map(|profile| compact_profile(&profile))
    .collect()
}

pub(super) fn expected_output_openat_profiles() -> Vec<Vec<String>> {
    [
        [
            "&parent_path",
            "component",
            "OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC",
            "Mode::empty()",
        ],
        [
            "&parent_path",
            "hooks.parent_sync_name()",
            "OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC",
            "Mode::empty()",
        ],
        [
            "directory",
            "Path::new(\".\")",
            "OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC",
            "Mode::empty()",
        ],
        [
            "directory",
            "Path::new(\".\")",
            "OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC",
            "Mode::empty()",
        ],
        [
            "&parent_sync",
            "Path::new(\".\")",
            "OFlags::TMPFILE | OFlags::RDWR | OFlags::CLOEXEC",
            "Mode::from_raw_mode(OUTPUT_MODE)",
        ],
        [
            "rustix::fs::CWD",
            "hooks.proc_root()",
            "OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC",
            "Mode::empty()",
        ],
        [
            "rustix::fs::CWD",
            "if absolute { Path::new(\"/\") } else { Path::new(\".\") }",
            "OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC",
            "Mode::empty()",
        ],
    ]
    .into_iter()
    .map(|profile| compact_profile(&profile))
    .collect()
}

pub(super) fn expected_output_statat_profiles() -> Vec<Vec<String>> {
    [
        ["&parent_path", "component", "AtFlags::SYMLINK_NOFOLLOW"],
        ["parent", "name", "AtFlags::SYMLINK_NOFOLLOW"],
        ["proc", "source", "AtFlags::empty()"],
        ["parent", "name", "AtFlags::SYMLINK_NOFOLLOW"],
        ["parent", "name", "AtFlags::SYMLINK_NOFOLLOW"],
    ]
    .into_iter()
    .map(|profile| compact_profile(&profile))
    .collect()
}

pub(super) fn expected_output_linkat_profiles() -> Vec<Vec<String>> {
    vec![compact_profile(&[
        "&proc",
        "&proc_source",
        "&parent_sync",
        "&name",
        "AtFlags::SYMLINK_FOLLOW",
    ])]
}

pub(super) fn expected_output_fchmod_profiles() -> Vec<Vec<String>> {
    vec![compact_profile(&[
        "&held",
        "Mode::from_raw_mode(OUTPUT_MODE)",
    ])]
}

pub(super) fn expected_output_fsync_profiles() -> Vec<Vec<String>> {
    vec![
        compact_profile(&["&held"]),
        compact_profile(&["&parent_sync"]),
        compact_profile(&["&committed.parent_sync"]),
    ]
}
