use super::{PortableSelectedRustClosure, selected_rust_closure};
use std::collections::BTreeSet;
use std::path::Path;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DownstreamClosureCoverage {
    library_keys: BTreeSet<String>,
    binary_keys: BTreeSet<String>,
    module_edges: BTreeSet<(String, String)>,
    embedded_targets: BTreeSet<String>,
    resolved_first_party_keys: BTreeSet<String>,
    checked_adapter_keys: BTreeSet<String>,
    checked_sanitizer_keys: BTreeSet<String>,
}

struct BorrowedSelectedModule<'a> {
    logical_key: &'a str,
    bytes: &'a [u8],
}

fn check_selected_module(module: BorrowedSelectedModule<'_>) -> Result<String, &'static str> {
    let source = std::str::from_utf8(module.bytes).map_err(|_| "capability-shape")?;
    syn::parse_file(source).map_err(|_| "capability-shape")?;
    Ok(module.logical_key.to_string())
}

fn check_selected_component(key: &str, bytes: &[u8]) -> Result<String, &'static str> {
    if key.is_empty() || bytes.is_empty() {
        return Err("capability-shape");
    }
    Ok(key.to_string())
}

fn collect_downstream_coverage(
    closure: &PortableSelectedRustClosure,
) -> Result<DownstreamClosureCoverage, &'static str> {
    let semantic = closure.semantic_module_sources()?;
    let mut resolved_first_party_keys = BTreeSet::new();
    for (key, source) in &semantic {
        resolved_first_party_keys.insert(check_selected_module(BorrowedSelectedModule {
            logical_key: key,
            bytes: source.as_bytes(),
        })?);
    }
    let mut checked_adapter_keys = BTreeSet::new();
    for key in closure.adapter_components() {
        checked_adapter_keys.insert(check_selected_component(
            key,
            closure.source(key)?.as_bytes(),
        )?);
    }
    let mut checked_sanitizer_keys = BTreeSet::new();
    for key in closure.sanitizer_components() {
        checked_sanitizer_keys.insert(check_selected_component(
            key,
            closure.source(key)?.as_bytes(),
        )?);
    }
    let library_keys = closure.module_files().clone();
    let binary_keys = closure.binary_paths().clone();
    Ok(DownstreamClosureCoverage {
        library_keys,
        binary_keys,
        module_edges: closure.module_edges(),
        embedded_targets: closure.embedded_data().clone(),
        resolved_first_party_keys,
        checked_adapter_keys,
        checked_sanitizer_keys,
    })
}

pub(crate) fn assert_downstream_selected_checkers_have_no_reopen_capability() {
    let source = include_str!("source_binding_registry_downstream.rs");
    let syntax = syn::parse_file(source).unwrap();
    for item in &syntax.items {
        let syn::Item::Fn(function) = item else {
            continue;
        };
        if !function
            .sig
            .ident
            .to_string()
            .starts_with("check_selected_")
        {
            continue;
        }
        let signature = function
            .sig
            .inputs
            .iter()
            .map(|input| match input {
                syn::FnArg::Receiver(_) => "receiver".to_string(),
                syn::FnArg::Typed(argument) => super::type_shape(&argument.ty),
            })
            .collect::<Vec<_>>()
            .join(",");
        for forbidden in ["Path", "PathBuf", "OwnedFd", "File", "Fn(", "dyn", "impl"] {
            assert!(!signature.contains(forbidden), "{signature}: {forbidden}");
        }
        let mut capabilities = CapabilityVisitor::default();
        syn::visit::Visit::visit_block(&mut capabilities, &function.block);
        assert!(
            capabilities.forbidden.is_empty(),
            "{:?}",
            capabilities.forbidden
        );
    }
}

pub(crate) fn assert_downstream_coverage_equals_all_graph_and_component_keys() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let closure = selected_rust_closure(root).unwrap();
    let coverage = collect_downstream_coverage(closure).unwrap();
    assert_eq!(coverage.library_keys, closure.module_files().clone());
    assert_eq!(coverage.binary_keys, closure.binary_paths().clone());
    assert_eq!(coverage.module_edges, closure.module_edges());
    assert_eq!(coverage.embedded_targets, closure.embedded_data().clone());
    assert_eq!(
        coverage.resolved_first_party_keys,
        closure.semantic_module_keys().unwrap()
    );
    assert_eq!(
        coverage.checked_adapter_keys,
        closure.adapter_components().iter().cloned().collect()
    );
    assert_eq!(
        coverage.checked_sanitizer_keys,
        closure.sanitizer_components().iter().cloned().collect()
    );
}

pub(crate) fn assert_borrowed_graph_resolves_external_modules() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let closure = selected_rust_closure(root).unwrap();
    let coverage = collect_downstream_coverage(closure).unwrap();
    assert_eq!(coverage.module_edges, closure.module_edges());
    assert!(coverage.module_edges.iter().all(|(from, to)| {
        coverage.library_keys.contains(from) && coverage.library_keys.contains(to)
    }));
}

#[derive(Default)]
struct CapabilityVisitor {
    forbidden: BTreeSet<String>,
}

impl<'ast> syn::visit::Visit<'ast> for CapabilityVisitor {
    fn visit_path(&mut self, path: &'ast syn::Path) {
        let rendered = path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect::<Vec<_>>()
            .join("::");
        if [
            "std::fs",
            "read_repository_file",
            "read_to_string",
            "File::open",
            "open",
            "openat",
        ]
        .iter()
        .any(|forbidden| rendered == *forbidden || rendered.ends_with(forbidden))
        {
            self.forbidden.insert(rendered);
        }
        syn::visit::visit_path(self, path);
    }
}
