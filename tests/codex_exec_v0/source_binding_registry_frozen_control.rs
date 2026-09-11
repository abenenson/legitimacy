use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

use super::{
    BUILD_INPUT_PATH, ClosureViolation, replace_exact_once, selected_rust_closure,
    verify_normative_sanitizer_registry_edge, verify_sanitizer_reconciliation_tests,
    verify_sanitizer_registry_authority, verify_sanitizer_structural_controls,
    verify_selected_sensitive_type_surfaces, verify_synthetic_selected_closure,
};

#[path = "frozen_control_v0/mod.rs"]
mod frozen_control_v0;
use frozen_control_v0 as frozen;

struct FrozenBlob {
    path: &'static str,
    bytes: &'static [u8],
    sha256: &'static str,
}

const BLOBS: [FrozenBlob; 6] = [
    FrozenBlob {
        path: "tests/codex_exec_v0/source_binding_registry_sensitive_verification.rs",
        bytes: include_bytes!(
            "../fixtures/selected-authority-frozen-control-v0/source_binding_registry_sensitive_verification.rs"
        ),
        sha256: "521d66c2361cb3b1af37e3f8b3380a691f939f97e35e83f502eea177e1ab88f4",
    },
    FrozenBlob {
        path: "tests/codex_exec_v0/source_binding_registry_sensitive_shapes.rs",
        bytes: include_bytes!(
            "../fixtures/selected-authority-frozen-control-v0/source_binding_registry_sensitive_shapes.rs"
        ),
        sha256: "9692bb61983f7bdc0e384fe05e1d985965e6cdefe9385d9c95fc8feab241956f",
    },
    FrozenBlob {
        path: "tests/codex_exec_v0/source_binding_registry_syntax_support.rs",
        bytes: include_bytes!(
            "../fixtures/selected-authority-frozen-control-v0/source_binding_registry_syntax_support.rs"
        ),
        sha256: "1833ca491cc3caced67ea4ff642b7d5267d51303bb46841bec28fcee64941df8",
    },
    FrozenBlob {
        path: "tests/codex_exec_v0/source_binding_registry_inventory_support.rs",
        bytes: include_bytes!(
            "../fixtures/selected-authority-frozen-control-v0/source_binding_registry_inventory_support.rs"
        ),
        sha256: "b26af557ed7cb6442dc7d2eec7339aae3842779b5fc14d55e9e4a5dc0ee0cef4",
    },
    FrozenBlob {
        path: "tests/codex_exec_v0/source_binding_registry_route_bindings.rs",
        bytes: include_bytes!(
            "../fixtures/selected-authority-frozen-control-v0/source_binding_registry_route_bindings.rs"
        ),
        sha256: "7509446f5f4b3f6f49833c60eacaa259fab085a7322f4b40e7cdba1be7908bc3",
    },
    FrozenBlob {
        path: "tests/codex_exec_v0/source_bindings.rs",
        bytes: include_bytes!(
            "../fixtures/selected-authority-frozen-control-v0/source_bindings.rs"
        ),
        sha256: "bafa14b08146fe5fce61de7a160ae4d2418f28df8fd9d4f53ac7ce451d340f26",
    },
];

const ROUTE_ONLY_PATHS: [&str; 12] = [
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

pub(crate) fn assert_frozen_base_blobs_and_dependency_closure_are_exact() {
    for blob in &BLOBS {
        assert_eq!(hex(Sha256::digest(blob.bytes).as_slice()), blob.sha256);
        assert!(std::str::from_utf8(blob.bytes).is_ok(), "{}", blob.path);
        assert!(syn::parse_file(std::str::from_utf8(blob.bytes).unwrap()).is_ok());
    }
    let raw_bindings = std::str::from_utf8(BLOBS[5].bytes).unwrap();
    let syntax = syn::parse_file(raw_bindings).unwrap();
    assert_eq!(
        frozen_array(&syntax, "ADAPTER_CORE_PATHS"),
        frozen::adapter_core_paths()
    );
    assert_eq!(
        frozen_array(&syntax, "SANITIZER_ONLY_PATHS"),
        frozen::sanitizer_only_paths()
    );
    let route = std::str::from_utf8(BLOBS[4].bytes).unwrap();
    let route_start = route.find("const ROUTE_ONLY_PATHS").unwrap();
    let route_end = route[route_start..].find("];").unwrap() + route_start + 2;
    let route_constant = syn::parse_str::<syn::ItemConst>(&route[route_start..route_end]).unwrap();
    assert_eq!(
        expression_array(route_constant.expr.as_ref()),
        ROUTE_ONLY_PATHS
    );
    assert_exact_lock_dependency(
        "syn",
        "2.0.117",
        "e665b8803e7b1d2a727f4023456bbbbe74da67099c585258af0ad9c5013b9b99",
    );
    assert_exact_lock_dependency(
        "tree-sitter",
        "0.25.10",
        "78f873475d258561b06f1c595d93308a7ed124d9977cb26b148c2084a4a3cc87",
    );
    assert_exact_lock_dependency(
        "tree-sitter-rust",
        "0.24.2",
        "439e577dbe07423ec2582ac62c7531120dbfccfa6e5f92406f93dd271a120e45",
    );
    assert_exact_lock_dependency(
        "sha2",
        "0.10.9",
        "a7507d819769d01a365ab707794a4084392c824f54a7a6a7862f8c3d0892b283",
    );
    assert_frozen_module_wiring_is_exact();
    assert_frozen_dependency_namespace_is_sealed();
}

pub(crate) fn assert_sanitizer_structural_controls_are_live() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let publication_tests = std::fs::read_to_string(
        root.join("tests/codex_exec_v0/source_binding_registry_publication_route_tests.rs"),
    )
    .unwrap();
    let normative_tests = std::fs::read_to_string(
        root.join("tests/codex_exec_v0/source_binding_registry_normative_contract_tests.rs"),
    )
    .unwrap();
    let normative_support = std::fs::read_to_string(
        root.join("tests/codex_exec_v0/source_binding_registry_normative_contract_support.rs"),
    )
    .unwrap();
    let registry =
        std::fs::read_to_string(root.join("tests/codex_exec_v0/source_bindings.rs")).unwrap();
    assert_eq!(
        verify_sanitizer_structural_controls(&publication_tests),
        Ok(())
    );
    assert_eq!(
        verify_sanitizer_reconciliation_tests(&normative_tests),
        Ok(())
    );
    assert_eq!(verify_sanitizer_registry_authority(&registry), Ok(()));
    assert_eq!(
        verify_normative_sanitizer_registry_edge(&normative_support),
        Ok(())
    );
}

pub(crate) fn assert_frozen_sibling_projection_is_exact() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let closure = selected_rust_closure(root).unwrap();
    let base = frozen::adapter_core_paths()
        .iter()
        .chain(frozen::sanitizer_only_paths())
        .chain(ROUTE_ONLY_PATHS.iter())
        .copied()
        .collect::<BTreeSet<_>>();
    let parent = "src/trajectory/codex_exec_v0/mod.rs";
    let old_owner = "src/trajectory/codex_exec_v0/publication_authority.rs";
    let sibling = "src/trajectory/codex_exec_v0/alternate_authority.rs";
    let canonical_object = BUILD_INPUT_PATH;
    assert!(base.contains(parent));
    assert!(base.contains(old_owner));
    assert!(!base.contains(sibling));
    assert!(!base.contains(canonical_object));

    let clean = closure.semantic_module_sources().unwrap();
    let baseline_projection = base
        .iter()
        .map(|path| {
            (
                (*path).to_string(),
                clean
                    .get(*path)
                    .unwrap_or_else(|| panic!("{path}: baseline frozen projection key"))
                    .clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    assert_eq!(frozen::verify(&baseline_projection), Ok(()));
    assert_eq!(verify_selected_sensitive_type_surfaces(closure), Ok(()));
    let clean_parent = clean.get(parent).unwrap();
    let hostile_parent = replace_exact_once(
        &replace_exact_once(
            clean_parent,
            "mod publication_authority;",
            "mod publication_authority;\nmod alternate_authority;",
        ),
        "pub use publication_authority::{",
        "pub use alternate_authority::{",
    );
    let old_owner_bytes = clean.get(old_owner).unwrap().clone();
    let mut hostile = clean.clone();
    hostile.insert(parent.to_string(), hostile_parent.clone());
    assert!(
        hostile
            .insert(sibling.to_string(), old_owner_bytes.clone())
            .is_none()
    );

    let changed_full_materialized_paths = BTreeSet::from([parent, sibling, canonical_object]);
    let changed_selected_semantic_module_paths = BTreeSet::from([parent, sibling]);
    assert_eq!(
        changed_full_materialized_paths,
        BTreeSet::from([parent, sibling, canonical_object])
    );
    assert_eq!(
        changed_selected_semantic_module_paths,
        BTreeSet::from([parent, sibling])
    );
    let projection = base
        .iter()
        .map(|path| {
            (
                (*path).to_string(),
                hostile
                    .get(*path)
                    .unwrap_or_else(|| panic!("{path}: frozen projection key"))
                    .clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        projection
            .keys()
            .map(String::as_str)
            .collect::<BTreeSet<_>>(),
        base
    );
    assert_eq!(projection.len(), 39);
    assert!(projection.contains_key(parent));
    assert!(projection.contains_key(old_owner));
    assert!(!projection.contains_key(sibling));
    assert!(!projection.contains_key(canonical_object));
    assert_eq!(projection.get(parent), Some(&hostile_parent));
    assert_ne!(projection.get(parent), Some(clean_parent));
    assert!(hostile_parent.contains("mod alternate_authority;"));
    assert!(hostile_parent.contains("pub use alternate_authority::{"));
    assert_eq!(projection.get(old_owner), clean.get(old_owner));
    assert_eq!(hostile.get(old_owner), clean.get(old_owner));
    assert_eq!(hostile.get(sibling), Some(&old_owner_bytes));
    assert_eq!(frozen::verify(&projection), Ok(()));

    let mut inputs = closure.synthetic_inputs();
    inputs.replace_bytes(parent, |_| hostile_parent);
    inputs.insert_library_source(sibling, old_owner_bytes);
    inputs.replace_bytes(canonical_object, |source| format!("{source} "));
    assert!(inputs.selected_library_contains(sibling));
    assert!(
        inputs
            .active_graph()
            .unwrap()
            .module_files()
            .contains(sibling)
    );
    assert_eq!(
        inputs.clone().build(),
        Err(ClosureViolation::SelectedOwnerMultiplicity)
    );
    assert_eq!(
        verify_synthetic_selected_closure(inputs),
        Err("capability-shape")
    );
}

pub(crate) fn assert_legacy_arrays_have_exactly_two_authorized_consumers() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut observed = BTreeSet::new();
    for path in rust_sources_below(&root.join("tests/codex_exec_v0")) {
        let source = std::fs::read_to_string(&path).unwrap();
        let syntax = syn::parse_file(&source).unwrap();
        let mut consumer = LegacyArrayConsumer::default();
        syn::visit::Visit::visit_file(&mut consumer, &syntax);
        if consumer.found {
            observed.insert(
                path.strip_prefix(root)
                    .unwrap()
                    .to_string_lossy()
                    .to_string(),
            );
        }
    }
    assert_eq!(
        observed,
        BTreeSet::from([
            "tests/codex_exec_v0/frozen_control_v0/mod.rs".to_string(),
            "tests/codex_exec_v0/source_bindings.rs".to_string(),
        ])
    );
}

#[derive(Default)]
struct LegacyArrayConsumer {
    found: bool,
}

impl<'ast> syn::visit::Visit<'ast> for LegacyArrayConsumer {
    fn visit_expr_path(&mut self, path: &'ast syn::ExprPath) {
        if path.path.segments.last().is_some_and(|segment| {
            matches!(
                segment.ident.to_string().as_str(),
                "ADAPTER_CORE_PATHS" | "SANITIZER_ONLY_PATHS"
            )
        }) {
            self.found = true;
        }
        syn::visit::visit_expr_path(self, path);
    }
}

fn assert_frozen_dependency_namespace_is_sealed() {
    let allowed = BTreeSet::from([
        "std",
        "syn",
        "tree_sitter",
        "tree_sitter_rust",
        "sha2",
        "super",
        "crate",
    ]);
    for blob in &BLOBS[..5] {
        let syntax = syn::parse_file(std::str::from_utf8(blob.bytes).unwrap()).unwrap();
        for item in syntax.items {
            if let syn::Item::Use(item) = item {
                let root = use_root(&item.tree);
                assert!(allowed.contains(root.as_str()), "{}: {root}", blob.path);
            }
        }
    }
}

fn assert_frozen_module_wiring_is_exact() {
    let source = include_str!("frozen_control_v0/mod.rs");
    let syntax = syn::parse_file(source).unwrap();
    let expected = BTreeMap::from([
        ("frozen_manual_paths", None),
        (
            "inventory_support",
            Some(
                "../../fixtures/selected-authority-frozen-control-v0/source_binding_registry_inventory_support.rs",
            ),
        ),
        (
            "route_bindings",
            Some(
                "../../fixtures/selected-authority-frozen-control-v0/source_binding_registry_route_bindings.rs",
            ),
        ),
        (
            "sensitive_shapes",
            Some(
                "../../fixtures/selected-authority-frozen-control-v0/source_binding_registry_sensitive_shapes.rs",
            ),
        ),
        (
            "syntax_support",
            Some(
                "../../fixtures/selected-authority-frozen-control-v0/source_binding_registry_syntax_support.rs",
            ),
        ),
        (
            "sensitive_verification",
            Some(
                "../../fixtures/selected-authority-frozen-control-v0/source_binding_registry_sensitive_verification.rs",
            ),
        ),
    ]);
    let actual = syntax
        .items
        .iter()
        .filter_map(|item| {
            let syn::Item::Mod(module) = item else {
                return None;
            };
            let path = module.attrs.iter().find_map(|attribute| {
                if !attribute.path().is_ident("path") {
                    return None;
                }
                let syn::Meta::NameValue(value) = &attribute.meta else {
                    panic!("frozen path shape");
                };
                let syn::Expr::Lit(value) = &value.value else {
                    panic!("frozen path expression");
                };
                let syn::Lit::Str(value) = &value.lit else {
                    panic!("frozen path literal");
                };
                Some(value.value())
            });
            Some((module.ident.to_string(), path))
        })
        .collect::<BTreeMap<_, _>>();
    assert_eq!(
        actual,
        expected
            .into_iter()
            .map(|(name, path)| (name.to_string(), path.map(str::to_string)))
            .collect()
    );

    let allowed_use_roots = BTreeSet::from([
        "frozen_manual_paths",
        "inventory_support",
        "route_bindings",
        "sensitive_shapes",
        "sensitive_verification",
        "sha2",
        "std",
        "syntax_support",
    ]);
    for item in &syntax.items {
        if let syn::Item::Use(item) = item {
            let root = use_root(&item.tree);
            assert!(allowed_use_roots.contains(root.as_str()), "{root}");
        }
    }
    assert!(!source.contains("super::super"));
    assert!(!source.contains("crate::source_binding_registry"));
    let verify = syntax
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == "verify" => Some(function),
            _ => None,
        })
        .unwrap();
    #[derive(Default)]
    struct Calls(Vec<String>);
    impl<'ast> syn::visit::Visit<'ast> for Calls {
        fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
            if let syn::Expr::Path(path) = call.func.as_ref() {
                self.0.push(
                    path.path
                        .segments
                        .iter()
                        .map(|segment| segment.ident.to_string())
                        .collect::<Vec<_>>()
                        .join("::"),
                );
            }
            syn::visit::visit_expr_call(self, call);
        }
    }
    let mut calls = Calls::default();
    syn::visit::Visit::visit_block(&mut calls, &verify.block);
    assert_eq!(
        calls.0,
        ["verify_registered_sensitive_type_surfaces".to_string()]
    );
}

fn frozen_array(syntax: &syn::File, name: &str) -> Vec<String> {
    let expression = syntax
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == name => Some(item.expr.as_ref()),
            _ => None,
        })
        .unwrap();
    let syn::Expr::Reference(reference) = expression else {
        panic!("frozen array reference");
    };
    expression_array(reference.expr.as_ref())
}

fn expression_array(expression: &syn::Expr) -> Vec<String> {
    if let syn::Expr::Reference(reference) = expression {
        return expression_array(reference.expr.as_ref());
    }
    let syn::Expr::Array(array) = expression else {
        panic!("frozen array");
    };
    array
        .elems
        .iter()
        .map(|item| match item {
            syn::Expr::Lit(item) => match &item.lit {
                syn::Lit::Str(item) => item.value(),
                _ => panic!("frozen string"),
            },
            _ => panic!("frozen literal"),
        })
        .collect()
}

fn assert_exact_lock_dependency(name: &str, version: &str, checksum: &str) {
    let lock: toml::Value = toml::from_str(include_str!("../../Cargo.lock")).unwrap();
    let matches = lock["package"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|package| {
            package["name"].as_str() == Some(name)
                && package["version"].as_str() == Some(version)
                && package["checksum"].as_str() == Some(checksum)
        })
        .count();
    assert_eq!(matches, 1, "{name} {version}");
}

fn use_root(tree: &syn::UseTree) -> String {
    match tree {
        syn::UseTree::Path(path) => path.ident.to_string(),
        syn::UseTree::Name(name) => name.ident.to_string(),
        syn::UseTree::Rename(rename) => rename.ident.to_string(),
        syn::UseTree::Glob(_) => "*".to_string(),
        syn::UseTree::Group(_) => "group".to_string(),
    }
}

fn rust_sources_below(root: &std::path::Path) -> Vec<std::path::PathBuf> {
    let mut paths = Vec::new();
    for entry in std::fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            paths.extend(rust_sources_below(&path));
        } else if path.extension().and_then(|extension| extension.to_str()) == Some("rs") {
            paths.push(path);
        }
    }
    paths.sort();
    paths
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
