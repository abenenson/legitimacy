use legitimacy::trajectory::codex_exec_v0::{
    codex_exec_sanitizer_binding_v0, codex_exec_sanitizer_compiled_attestation_v0,
};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

const SOURCE_BINDINGS: &str = "src/trajectory/codex_exec_v0/source_bindings.rs";
const PUBLIC_MODULE: &str = "src/trajectory/codex_exec_v0/mod.rs";
const SCHEMA_IDENTITY: &str = "legitimacy.codex-exec-v0.sanitizer-compiled-attestation";

pub(crate) fn assert_compiled_attestation_api_is_exactly_read_only_v0() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let source = std::fs::read_to_string(root.join(SOURCE_BINDINGS)).unwrap();
    let public_module = std::fs::read_to_string(root.join(PUBLIC_MODULE)).unwrap();
    let syntax = syn::parse_file(&source).unwrap();
    let public_syntax = syn::parse_file(&public_module).unwrap();

    assert_exact_struct(
        &syntax,
        "CodexExecSanitizerCompiledComponentV0",
        &[
            ("component_key", "&'static str"),
            ("byte_length", "u64"),
            ("sha256", "[u8;32]"),
        ],
    );
    assert_exact_struct(
        &syntax,
        "CodexExecSanitizerCompiledAttestationV0",
        &[
            ("schema_identity", "&'static str"),
            ("schema_version", "u16"),
            ("components", "Box<[CodexExecSanitizerCompiledComponentV0]>"),
            ("aggregate", "ArtifactBindingV0"),
        ],
    );
    assert_exact_impl(
        &syntax,
        "CodexExecSanitizerCompiledComponentV0",
        &[
            ("component_key", "&'static str"),
            ("byte_length", "u64"),
            ("sha256", "[u8;32]"),
        ],
    );
    assert_exact_impl(
        &syntax,
        "CodexExecSanitizerCompiledAttestationV0",
        &[
            ("aggregate", "&ArtifactBindingV0"),
            ("components", "&[CodexExecSanitizerCompiledComponentV0]"),
            ("schema_identity", "&'static str"),
            ("schema_version", "u16"),
        ],
    );
    assert_no_other_impls(
        &syntax,
        &[
            "CodexExecSanitizerCompiledComponentV0",
            "CodexExecSanitizerCompiledAttestationV0",
        ],
    );

    let function = syntax
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function)
                if function.sig.ident == "codex_exec_sanitizer_compiled_attestation_v0" =>
            {
                Some(function)
            }
            _ => None,
        })
        .unwrap();
    assert!(matches!(function.vis, syn::Visibility::Public(_)));
    assert!(function.sig.inputs.is_empty());
    assert!(function.sig.generics.params.is_empty());
    assert!(function.sig.generics.where_clause.is_none());
    assert_eq!(
        return_type(&function.sig.output),
        "CodexExecSanitizerCompiledAttestationV0"
    );
    let function_start = source
        .find("pub fn codex_exec_sanitizer_compiled_attestation_v0")
        .unwrap();
    let function_end = source[function_start..]
        .find("\nconst ADAPTER_CORE_SOURCES_V0")
        .map(|offset| function_start + offset)
        .unwrap();
    let body = compact(&source[function_start..function_end]);
    for required in [
        "ADAPTER_CORE_SOURCES_V0.iter().chain(SANITIZER_ONLY_SOURCES_V0)",
        "u64::try_from(bytes.len())",
        "Sha256::digest(bytes)",
        "aggregate:sanitizer_binding()",
    ] {
        assert!(body.contains(&compact(required)), "missing {required}");
    }
    for forbidden in [
        "std::fs",
        "std::env",
        "Path",
        "File",
        "read",
        "parse",
        "deserialize",
        "PublicationMintV0",
        "ProductionSanitizationTransactionV0",
        "ShareableSanitizedBundleV0",
    ] {
        assert!(!body.contains(forbidden), "forbidden {forbidden}");
    }
    assert_semver_docs(function.attrs.as_slice());

    let mut public_reexports = Vec::new();
    for item in &public_syntax.items {
        if let syn::Item::Use(item) = item
            && matches!(item.vis, syn::Visibility::Public(_))
        {
            use_names(&item.tree, &mut public_reexports);
        }
    }
    for name in [
        "CodexExecSanitizerCompiledComponentV0",
        "CodexExecSanitizerCompiledAttestationV0",
        "codex_exec_sanitizer_compiled_attestation_v0",
    ] {
        assert_eq!(
            public_reexports
                .iter()
                .filter(|candidate| candidate == &name)
                .count(),
            1,
            "{name}"
        );
    }

    let expected = parsed_registry_components(root, &syntax);
    let attestation = codex_exec_sanitizer_compiled_attestation_v0();
    assert_eq!(attestation.schema_identity(), SCHEMA_IDENTITY);
    assert_eq!(attestation.schema_version(), 0);
    assert_eq!(attestation.components().len(), expected.len());
    for (component, (path, bytes)) in attestation.components().iter().zip(expected) {
        assert_eq!(component.component_key(), path);
        assert_eq!(component.byte_length(), u64::try_from(bytes.len()).unwrap());
        assert_eq!(component.sha256(), <[u8; 32]>::from(Sha256::digest(bytes)));
    }
    assert_eq!(attestation.aggregate(), &codex_exec_sanitizer_binding_v0());
}

fn assert_exact_struct(syntax: &syn::File, name: &str, expected: &[(&str, &str)]) {
    let item = syntax
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Struct(item) if item.ident == name => Some(item),
            _ => None,
        })
        .unwrap();
    assert!(matches!(item.vis, syn::Visibility::Public(_)));
    assert!(item.generics.params.is_empty());
    assert!(item.generics.where_clause.is_none());
    assert!(!item.attrs.iter().any(|attr| attr.path().is_ident("derive")));
    assert_semver_docs(item.attrs.as_slice());
    let fields = item
        .fields
        .iter()
        .map(|field| {
            assert!(matches!(field.vis, syn::Visibility::Inherited));
            (
                field.ident.as_ref().unwrap().to_string(),
                render_type(&field.ty),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        fields,
        expected
            .iter()
            .map(|(field, ty)| ((*field).to_string(), compact(ty)))
            .collect::<Vec<_>>()
    );
}

fn assert_exact_impl(syntax: &syn::File, target: &str, expected: &[(&str, &str)]) {
    let implementations = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Impl(item)
                if item.trait_.is_none() && render_type(&item.self_ty) == target =>
            {
                Some(item)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(implementations.len(), 1);
    let implementation = implementations[0];
    assert!(implementation.attrs.is_empty());
    assert!(implementation.generics.params.is_empty());
    let methods = implementation
        .items
        .iter()
        .map(|item| {
            let syn::ImplItem::Fn(method) = item else {
                panic!("only methods are permitted");
            };
            assert!(matches!(method.vis, syn::Visibility::Public(_)));
            assert!(method.attrs.is_empty());
            assert_eq!(method.sig.inputs.len(), 1);
            assert!(matches!(
                method.sig.inputs.first(),
                Some(syn::FnArg::Receiver(receiver))
                    if receiver.reference.is_some() && receiver.mutability.is_none()
            ));
            (
                method.sig.ident.to_string(),
                return_type(&method.sig.output),
            )
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        methods,
        expected
            .iter()
            .map(|(name, ty)| ((*name).to_string(), compact(ty)))
            .collect()
    );
}

fn assert_no_other_impls(syntax: &syn::File, targets: &[&str]) {
    for item in &syntax.items {
        let syn::Item::Impl(item) = item else {
            continue;
        };
        let target = render_type(&item.self_ty);
        if targets.contains(&target.as_str()) {
            assert!(item.trait_.is_none(), "{target}: explicit trait impl");
        }
    }
}

fn assert_semver_docs(attrs: &[syn::Attribute]) {
    let docs = attrs
        .iter()
        .filter(|attribute| attribute.path().is_ident("doc"))
        .filter_map(|attribute| match &attribute.meta {
            syn::Meta::NameValue(value) => match &value.value {
                syn::Expr::Lit(expression) => match &expression.lit {
                    syn::Lit::Str(value) => Some(value.value()),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        })
        .collect::<Vec<_>>()
        .join(" ");
    for required in [
        "supported additive SemVer surface",
        "Version 0",
        "new versioned",
    ] {
        assert!(
            compact(&docs).contains(&compact(required)),
            "missing rustdoc promise: {required}"
        );
    }
}

fn return_type(output: &syn::ReturnType) -> String {
    match output {
        syn::ReturnType::Default => String::new(),
        syn::ReturnType::Type(_, ty) => render_type(ty),
    }
}

fn compact(value: &str) -> String {
    value.split_whitespace().collect()
}

fn render_type(ty: &syn::Type) -> String {
    match ty {
        syn::Type::Path(path) => path
            .path
            .segments
            .iter()
            .map(|segment| {
                let mut rendered = segment.ident.to_string();
                if let syn::PathArguments::AngleBracketed(arguments) = &segment.arguments {
                    rendered.push('<');
                    rendered.push_str(
                        &arguments
                            .args
                            .iter()
                            .map(|argument| match argument {
                                syn::GenericArgument::Type(ty) => render_type(ty),
                                syn::GenericArgument::Lifetime(lifetime) => lifetime.to_string(),
                                _ => "unsupported".to_string(),
                            })
                            .collect::<Vec<_>>()
                            .join(","),
                    );
                    rendered.push('>');
                }
                rendered
            })
            .collect::<Vec<_>>()
            .join("::"),
        syn::Type::Reference(reference) => {
            let mut rendered = "&".to_string();
            if let Some(lifetime) = &reference.lifetime {
                rendered.push_str(&lifetime.to_string());
            }
            if reference.mutability.is_some() {
                rendered.push_str("mut ");
            }
            rendered.push_str(&render_type(&reference.elem));
            rendered
        }
        syn::Type::Slice(slice) => format!("[{}]", render_type(&slice.elem)),
        syn::Type::Array(array) => {
            let length = match &array.len {
                syn::Expr::Lit(expression) => match &expression.lit {
                    syn::Lit::Int(value) => value.base10_digits().to_string(),
                    _ => "unsupported".to_string(),
                },
                _ => "unsupported".to_string(),
            };
            format!("[{};{length}]", render_type(&array.elem))
        }
        _ => "unsupported".to_string(),
    }
}

fn use_names(tree: &syn::UseTree, names: &mut Vec<String>) {
    match tree {
        syn::UseTree::Path(path) => use_names(&path.tree, names),
        syn::UseTree::Name(name) => names.push(name.ident.to_string()),
        syn::UseTree::Rename(rename) => names.push(rename.rename.to_string()),
        syn::UseTree::Group(group) => {
            for item in &group.items {
                use_names(item, names);
            }
        }
        syn::UseTree::Glob(_) => names.push("*".to_string()),
    }
}

fn parsed_registry_components(root: &Path, syntax: &syn::File) -> Vec<(String, Vec<u8>)> {
    ["ADAPTER_CORE_SOURCES_V0", "SANITIZER_ONLY_SOURCES_V0"]
        .into_iter()
        .flat_map(|name| parse_registry(root, syntax, name))
        .collect()
}

fn parse_registry(root: &Path, syntax: &syn::File, name: &str) -> Vec<(String, Vec<u8>)> {
    let expression = syntax
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == name => Some(item.expr.as_ref()),
            _ => None,
        })
        .unwrap();
    let syn::Expr::Reference(reference) = expression else {
        panic!("registry must be a reference");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("registry must be an array");
    };
    array
        .elems
        .iter()
        .map(|element| {
            let syn::Expr::Tuple(tuple) = element else {
                panic!("registry entry must be a tuple");
            };
            let syn::Expr::Lit(label) = &tuple.elems[0] else {
                panic!("registry label must be literal");
            };
            let syn::Lit::Str(label) = &label.lit else {
                panic!("registry label must be a string");
            };
            let syn::Expr::Macro(include) = &tuple.elems[1] else {
                panic!("registry bytes must be included");
            };
            assert!(include.mac.path.is_ident("include_bytes"));
            let literal = syn::parse2::<syn::LitStr>(include.mac.tokens.clone()).unwrap();
            let included = PathBuf::from(SOURCE_BINDINGS)
                .parent()
                .unwrap()
                .join(literal.value());
            let included = lexical_normalize(&included);
            let label = label.value();
            assert_eq!(included.to_string_lossy(), label);
            (label, std::fs::read(root.join(included)).unwrap())
        })
        .collect()
}

fn lexical_normalize(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            std::path::Component::ParentDir => {
                normalized.pop();
            }
            std::path::Component::CurDir => {}
            std::path::Component::Normal(component) => normalized.push(component),
            _ => panic!("non-relative component"),
        }
    }
    normalized
}
