use super::sensitive_verification::{
    SensitiveViolation, owner_has_borrowed_bundle_construction, owner_has_expansion_surface,
};
use std::collections::BTreeSet;

const BASELINE: &str = r#"
struct NonceMaterialV0;
struct SanitizedCaptureV0;
struct SanitizationBindingsV0;
struct PublicationMintV0 {
    publication_parent_reblinding_nonce: NonceMaterialV0,
}
pub struct ShareableSanitizedBundleV0 {
    bytes: Vec<u8>,
}
impl ShareableSanitizedBundleV0 {
    pub fn to_json_line(&self) -> Vec<u8> { self.bytes.clone() }
    pub fn into_bytes(self) -> Vec<u8> { self.bytes }
}
pub struct ProductionSanitizationTransactionV0 {
    sanitized: SanitizedCaptureV0,
    bindings: SanitizationBindingsV0,
    mint: PublicationMintV0,
}
impl ProductionSanitizationTransactionV0 {
    pub fn into_publication_pair(self) -> (Vec<u8>, Vec<u8>) { (Vec::new(), Vec::new()) }
}
"#;

pub(crate) fn assert_selected_sensitive_attack_matrix_policy_only() {
    assert_eq!(verify_selected_sensitive_policy_fixture(BASELINE), Ok(()));
    for (needle, replacement) in [
        ("struct PublicationMintV0", "pub struct PublicationMintV0"),
        ("bytes: Vec<u8>", "pub bytes: Vec<u8>"),
        (
            "pub struct ShareableSanitizedBundleV0",
            "#[derive(Clone)]\npub struct ShareableSanitizedBundleV0",
        ),
        (
            "pub fn into_bytes(self)",
            "pub fn repeat(&self) -> Vec<u8> { Vec::new() }\n    pub fn into_bytes(self)",
        ),
        (
            "pub fn into_publication_pair(self)",
            "pub fn into_publication_pair(&self)",
        ),
    ] {
        let hostile = BASELINE.replacen(needle, replacement, 1);
        assert_eq!(
            verify_selected_sensitive_policy_fixture(&hostile),
            Err(SensitiveViolation::Shape)
        );
    }

    let borrowed = BASELINE.replacen(
        "pub fn into_bytes(self) -> Vec<u8> { self.bytes }",
        "pub fn repeat(&self) -> Self { Self { bytes: self.bytes.clone() } }\n    pub fn into_bytes(self) -> Vec<u8> { self.bytes }",
        1,
    );
    assert_eq!(
        verify_selected_sensitive_policy_fixture(&borrowed),
        Err(SensitiveViolation::BorrowedConstruction)
    );

    let macro_owner = format!(
        "{BASELINE}\nmacro_rules! construct_bundle {{ () => {{ ShareableSanitizedBundleV0 {{ bytes: Vec::new() }} }}; }}\n"
    );
    assert_eq!(
        verify_selected_sensitive_policy_fixture(&macro_owner),
        Err(SensitiveViolation::ExpansionAuthoritySurface)
    );
}

fn verify_selected_sensitive_policy_fixture(source: &str) -> Result<(), SensitiveViolation> {
    let syntax = syn::parse_file(source).map_err(|_| SensitiveViolation::Shape)?;
    if owner_has_borrowed_bundle_construction(&syntax) {
        return Err(SensitiveViolation::BorrowedConstruction);
    }
    if owner_has_expansion_surface(&syntax) {
        return Err(SensitiveViolation::ExpansionAuthoritySurface);
    }
    let mint = structs(&syntax, "PublicationMintV0");
    let bundle = structs(&syntax, "ShareableSanitizedBundleV0");
    let transaction = structs(&syntax, "ProductionSanitizationTransactionV0");
    if !matches!(
        (mint.as_slice(), bundle.as_slice(), transaction.as_slice()),
        ([mint], [bundle], [transaction])
            if matches!(mint.vis, syn::Visibility::Inherited)
                && matches!(bundle.vis, syn::Visibility::Public(_))
                && matches!(transaction.vis, syn::Visibility::Public(_))
                && mint.fields.iter().all(|field| matches!(field.vis, syn::Visibility::Inherited))
                && bundle.fields.iter().all(|field| matches!(field.vis, syn::Visibility::Inherited))
                && transaction.fields.iter().all(|field| matches!(field.vis, syn::Visibility::Inherited))
    ) || [
        "PublicationMintV0",
        "ShareableSanitizedBundleV0",
        "ProductionSanitizationTransactionV0",
    ]
    .iter()
    .any(|name| has_derive(&syntax, name))
        || public_methods(&syntax, "ShareableSanitizedBundleV0")
            != BTreeSet::from(["into_bytes".to_string(), "to_json_line".to_string()])
        || public_methods(&syntax, "ProductionSanitizationTransactionV0")
            != BTreeSet::from(["into_publication_pair".to_string()])
        || !method_consumes_self(
            &syntax,
            "ProductionSanitizationTransactionV0",
            "into_publication_pair",
        )
    {
        return Err(SensitiveViolation::Shape);
    }
    Ok(())
}

fn structs<'a>(syntax: &'a syn::File, name: &str) -> Vec<&'a syn::ItemStruct> {
    syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Struct(item) if item.ident == name => Some(item),
            _ => None,
        })
        .collect()
}

fn has_derive(syntax: &syn::File, name: &str) -> bool {
    structs(syntax, name)
        .iter()
        .flat_map(|item| &item.attrs)
        .any(|attribute| attribute.path().is_ident("derive"))
}

fn public_methods(syntax: &syn::File, name: &str) -> BTreeSet<String> {
    syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Impl(item)
                if item.trait_.is_none()
                    && matches!(
                        item.self_ty.as_ref(),
                        syn::Type::Path(path)
                            if path.path.segments.last().is_some_and(|part| part.ident == name)
                    ) =>
            {
                Some(item)
            }
            _ => None,
        })
        .flat_map(|item| &item.items)
        .filter_map(|item| match item {
            syn::ImplItem::Fn(function) if matches!(function.vis, syn::Visibility::Public(_)) => {
                Some(function.sig.ident.to_string())
            }
            _ => None,
        })
        .collect()
}

fn method_consumes_self(syntax: &syn::File, owner: &str, method: &str) -> bool {
    syntax.items.iter().any(|item| {
        let syn::Item::Impl(item) = item else {
            return false;
        };
        let matches_owner = matches!(
            item.self_ty.as_ref(),
            syn::Type::Path(path)
                if path.path.segments.last().is_some_and(|part| part.ident == owner)
        );
        matches_owner
            && item.items.iter().any(|member| {
                matches!(
                    member,
                    syn::ImplItem::Fn(function)
                        if function.sig.ident == method
                            && matches!(
                                function.sig.inputs.first(),
                                Some(syn::FnArg::Receiver(receiver))
                                    if receiver.reference.is_none()
                            )
                )
            })
    })
}
