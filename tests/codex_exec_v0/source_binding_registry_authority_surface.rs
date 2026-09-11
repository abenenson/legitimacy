use super::compiler_protocol::EXACT_RUSTC_VV;
use super::direct_graph::{LogicalModuleId, TargetRole};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) const PROTECTED_TYPES: [&str; 9] = [
    "PreparedPublicationV0",
    "CommittedPublicationV0",
    "CommitFailureV0",
    "PublicationSpecV0",
    "SnapshotV0",
    "PublicationMintV0",
    "ProductionSanitizationTransactionV0",
    "ShareableSanitizedBundleV0",
    "RevalidatedShareableSanitizedBundleV0",
];

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct AuthorityFact {
    pub(crate) target: TargetRole,
    pub(crate) logical_module: LogicalModuleId,
    pub(crate) protected_type: String,
    pub(crate) enclosing_item: String,
    pub(crate) kind: String,
    pub(crate) signature: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DirectAuthoritySurface(pub(crate) BTreeMap<AuthorityFact, u32>);

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ExpandedAuthoritySurface(pub(crate) BTreeMap<AuthorityFact, u32>);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum AllowanceIdentity {
    RedactedDebug,
    PublicationSpecDerives,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct AllowanceSiteEvidence {
    pub(crate) target: TargetRole,
    pub(crate) logical_module: LogicalModuleId,
    pub(crate) protected_type: String,
    pub(crate) source_key: String,
    pub(crate) complete_file_digest: [u8; 32],
    pub(crate) definition_digest: Option<[u8; 32]>,
    pub(crate) invocation_or_site_digest: [u8; 32],
    pub(crate) parsed_arguments: Vec<String>,
    pub(crate) compiler_identity: Vec<u8>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ExpansionAllowance {
    pub(crate) identity: AllowanceIdentity,
    pub(crate) site: AllowanceSiteEvidence,
    pub(crate) generated: BTreeMap<AuthorityFact, u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DeclaredExpansionAllowanceV1 {
    entries: [ExpansionAllowance; 2],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AuthorityFailure {
    ProtectedInventory,
    ExpansionAuthoritySurface,
}

impl DeclaredExpansionAllowanceV1 {
    pub(crate) fn canonical() -> Self {
        Self {
            entries: [redacted_debug_allowance(), publication_spec_allowance()],
        }
    }

    pub(crate) fn entries(&self) -> &[ExpansionAllowance; 2] {
        &self.entries
    }

    pub(crate) fn reconcile(
        &self,
        direct: &DirectAuthoritySurface,
        expanded: &ExpandedAuthoritySurface,
        observed_sites: &BTreeMap<AllowanceIdentity, AllowanceSiteEvidence>,
    ) -> Result<(), AuthorityFailure> {
        if self.entries[0].identity != AllowanceIdentity::RedactedDebug
            || self.entries[1].identity != AllowanceIdentity::PublicationSpecDerives
            || self.entries[0].generated.is_empty()
            || self.entries[1].generated.is_empty()
        {
            return Err(AuthorityFailure::ExpansionAuthoritySurface);
        }
        let mut remainder = expanded.0.clone();
        for allowance in &self.entries {
            if observed_sites.get(&allowance.identity) != Some(&allowance.site) {
                return Err(AuthorityFailure::ExpansionAuthoritySurface);
            }
            for (fact, expected_count) in &allowance.generated {
                let count = remainder
                    .get_mut(fact)
                    .ok_or(AuthorityFailure::ExpansionAuthoritySurface)?;
                if count != expected_count {
                    return Err(AuthorityFailure::ExpansionAuthoritySurface);
                }
                remainder.remove(fact);
            }
        }
        if remainder == direct.0 {
            Ok(())
        } else {
            Err(AuthorityFailure::ExpansionAuthoritySurface)
        }
    }
}

pub(crate) fn collect_direct_authority_surface(
    target: TargetRole,
    logical_module: &LogicalModuleId,
    items: &[syn::Item],
) -> Result<DirectAuthoritySurface, AuthorityFailure> {
    Ok(DirectAuthoritySurface(collect_surface(
        target,
        logical_module,
        items,
    )?))
}

pub(crate) fn collect_expanded_authority_surface(
    target: TargetRole,
    logical_module: &LogicalModuleId,
    items: &[syn::Item],
) -> Result<ExpandedAuthoritySurface, AuthorityFailure> {
    Ok(ExpandedAuthoritySurface(collect_surface(
        target,
        logical_module,
        items,
    )?))
}

fn collect_surface(
    target: TargetRole,
    logical_module: &LogicalModuleId,
    items: &[syn::Item],
) -> Result<BTreeMap<AuthorityFact, u32>, AuthorityFailure> {
    let mut facts = BTreeMap::new();
    for item in items {
        match item {
            syn::Item::Struct(item) if protected(&item.ident.to_string()) => {
                insert_fact(
                    &mut facts,
                    fact(
                        target,
                        logical_module,
                        &item.ident.to_string(),
                        &item.ident.to_string(),
                        "declaration",
                        &format!("{}:{}", visibility(&item.vis), render_fields(&item.fields)),
                    ),
                )?;
            }
            syn::Item::Enum(item) if protected(&item.ident.to_string()) => {
                insert_fact(
                    &mut facts,
                    fact(
                        target,
                        logical_module,
                        &item.ident.to_string(),
                        &item.ident.to_string(),
                        "declaration",
                        &format!("{}:{}", visibility(&item.vis), render_variants(item)),
                    ),
                )?;
            }
            syn::Item::Impl(item) => {
                let Some(protected_type) = protected_type(&item.self_ty) else {
                    continue;
                };
                let trait_name = item
                    .trait_
                    .as_ref()
                    .map(|(_, path, _)| render_path(path))
                    .unwrap_or_else(|| "inherent".to_string());
                insert_fact(
                    &mut facts,
                    fact(
                        target,
                        logical_module,
                        &protected_type,
                        &format!("impl:{trait_name}"),
                        "impl",
                        &trait_name,
                    ),
                )?;
                for member in &item.items {
                    match member {
                        syn::ImplItem::Fn(function) => insert_fact(
                            &mut facts,
                            fact(
                                target,
                                logical_module,
                                &protected_type,
                                &format!("impl:{trait_name}"),
                                "method",
                                &render_signature(&function.sig, &function.vis),
                            ),
                        )?,
                        syn::ImplItem::Type(associated) => insert_fact(
                            &mut facts,
                            fact(
                                target,
                                logical_module,
                                &protected_type,
                                &format!("impl:{trait_name}"),
                                "associated-type",
                                &format!("{}={}", associated.ident, render_type(&associated.ty)),
                            ),
                        )?,
                        syn::ImplItem::Verbatim(_) => {
                            return Err(AuthorityFailure::ProtectedInventory);
                        }
                        _ => {}
                    }
                }
            }
            syn::Item::Fn(function) => {
                for protected_type in signature_protected_types(&function.sig) {
                    insert_fact(
                        &mut facts,
                        fact(
                            target,
                            logical_module,
                            &protected_type,
                            &function.sig.ident.to_string(),
                            "callable",
                            &render_signature(&function.sig, &function.vis),
                        ),
                    )?;
                }
            }
            syn::Item::Type(alias) => {
                for protected_type in type_protected_types(&alias.ty) {
                    insert_fact(
                        &mut facts,
                        fact(
                            target,
                            logical_module,
                            &protected_type,
                            &alias.ident.to_string(),
                            "alias",
                            &format!("{}={}", visibility(&alias.vis), render_type(&alias.ty)),
                        ),
                    )?;
                }
            }
            syn::Item::Use(item) => {
                let mut names = Vec::new();
                use_names(&item.tree, &mut names);
                for protected_type in names.into_iter().filter(|name| protected(name)) {
                    insert_fact(
                        &mut facts,
                        fact(
                            target,
                            logical_module,
                            &protected_type,
                            "use",
                            "reexport",
                            visibility(&item.vis),
                        ),
                    )?;
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, nested)) = &module.content {
                    let mut child = logical_module.clone();
                    child.0.push(normalize_ident(&module.ident));
                    merge(&mut facts, collect_surface(target, &child, nested)?)?;
                }
            }
            syn::Item::Verbatim(_) => return Err(AuthorityFailure::ProtectedInventory),
            _ => {}
        }
    }
    let syntax = syn::File {
        shebang: None,
        attrs: Vec::new(),
        items: items.to_vec(),
    };
    let mut constructions = ConstructionVisitor {
        target,
        logical_module,
        facts: BTreeMap::new(),
        failure: None,
        enclosing: Vec::new(),
        protected_self: Vec::new(),
    };
    syn::visit::Visit::visit_file(&mut constructions, &syntax);
    if let Some(failure) = constructions.failure {
        return Err(failure);
    }
    merge(&mut facts, constructions.facts)?;
    Ok(facts)
}

struct ConstructionVisitor<'a> {
    target: TargetRole,
    logical_module: &'a LogicalModuleId,
    facts: BTreeMap<AuthorityFact, u32>,
    failure: Option<AuthorityFailure>,
    enclosing: Vec<String>,
    protected_self: Vec<String>,
}

impl<'ast> syn::visit::Visit<'ast> for ConstructionVisitor<'_> {
    fn visit_item_mod(&mut self, _module: &'ast syn::ItemMod) {}

    fn visit_item_impl(&mut self, implementation: &'ast syn::ItemImpl) {
        let protected_self = protected_type(&implementation.self_ty);
        let enclosing = implementation
            .trait_
            .as_ref()
            .map(|(_, path, _)| format!("impl:{}", render_path(path)))
            .unwrap_or_else(|| "impl:inherent".to_string());
        self.enclosing.push(enclosing);
        if let Some(protected_self) = protected_self {
            self.protected_self.push(protected_self);
            syn::visit::visit_item_impl(self, implementation);
            self.protected_self.pop();
        } else {
            syn::visit::visit_item_impl(self, implementation);
        }
        self.enclosing.pop();
    }

    fn visit_item_fn(&mut self, function: &'ast syn::ItemFn) {
        self.enclosing.push(function.sig.ident.to_string());
        syn::visit::visit_item_fn(self, function);
        self.enclosing.pop();
    }

    fn visit_expr_struct(&mut self, expression: &'ast syn::ExprStruct) {
        if let Some(name) = expression
            .path
            .segments
            .last()
            .map(|part| part.ident.to_string())
            && (protected(&name) || name == "Self")
        {
            let protected_type = if name == "Self" {
                let Some(protected_self) = self.protected_self.last() else {
                    syn::visit::visit_expr_struct(self, expression);
                    return;
                };
                protected_self.clone()
            } else {
                name
            };
            let result = insert_fact(
                &mut self.facts,
                fact(
                    self.target,
                    self.logical_module,
                    &protected_type,
                    self.enclosing
                        .last()
                        .map(String::as_str)
                        .unwrap_or("expression"),
                    "construction",
                    &render_construction(expression),
                ),
            );
            if result.is_err() {
                self.failure = Some(AuthorityFailure::ProtectedInventory);
                return;
            }
        }
        syn::visit::visit_expr_struct(self, expression);
    }
}

fn render_construction(expression: &syn::ExprStruct) -> String {
    let name = expression
        .path
        .segments
        .last()
        .map(|segment| normalize_ident(&segment.ident))
        .unwrap_or_default();
    let fields = expression
        .fields
        .iter()
        .map(|field| {
            let member = match &field.member {
                syn::Member::Named(name) => normalize_ident(name),
                syn::Member::Unnamed(index) => index.index.to_string(),
            };
            format!("{member}={}", render_expression(&field.expr))
        })
        .collect::<Vec<_>>()
        .join(",");
    format!("{name}:{fields}")
}

fn render_expression(expression: &syn::Expr) -> String {
    match expression {
        syn::Expr::Field(field) => format!(
            "{}.{}",
            render_expression(&field.base),
            match &field.member {
                syn::Member::Named(name) => normalize_ident(name),
                syn::Member::Unnamed(index) => index.index.to_string(),
            }
        ),
        syn::Expr::Path(path) => render_path(&path.path),
        _ => "expression".to_string(),
    }
}

fn redacted_debug_allowance() -> ExpansionAllowance {
    let module = LogicalModuleId(vec![
        "trajectory".to_string(),
        "codex_exec_v0".to_string(),
        "bundle_wire".to_string(),
    ]);
    let generated = BTreeMap::from([
        (
            fact(
                TargetRole::Library,
                &module,
                "RevalidatedShareableSanitizedBundleV0",
                "impl:fmt::Debug",
                "impl",
                "fmt::Debug",
            ),
            1,
        ),
        (
            fact(
                TargetRole::Library,
                &module,
                "RevalidatedShareableSanitizedBundleV0",
                "impl:fmt::Debug",
                "method",
                "inherited:fmt(&self,&mut fmt::Formatter<'_>)->fmt::Result",
            ),
            1,
        ),
    ]);
    ExpansionAllowance {
        identity: AllowanceIdentity::RedactedDebug,
        site: AllowanceSiteEvidence {
            target: TargetRole::Library,
            logical_module: module,
            protected_type: "RevalidatedShareableSanitizedBundleV0".to_string(),
            source_key: "src/trajectory/codex_exec_v0/bundle_wire.rs".to_string(),
            complete_file_digest: hex32(
                "8ffdef12899cac4237da9c4dafa941d62789ead3bb8ea52f52d09fd25db291b3",
            ),
            definition_digest: Some(hex32(
                "d11ca827670e22f5f1c6b1806c1713f78af7870cd9c4ff1f127125896beabb35",
            )),
            invocation_or_site_digest: hex32(
                "deada18fea9e49d9bf9e8f79aacb3c2d079ad08daa0d0c7d749b49a7ed7961b9",
            ),
            parsed_arguments: vec!["RevalidatedShareableSanitizedBundleV0".to_string()],
            compiler_identity: EXACT_RUSTC_VV.to_vec(),
        },
        generated,
    }
}

fn publication_spec_allowance() -> ExpansionAllowance {
    let module = LogicalModuleId(vec![
        "trajectory".to_string(),
        "linux_output_transaction".to_string(),
    ]);
    let mut generated = BTreeMap::new();
    for (enclosing, kind, signature) in [
        ("impl:core::clone::Clone", "impl", "core::clone::Clone"),
        (
            "impl:core::clone::Clone",
            "method",
            "inherited:clone(&self)->Self",
        ),
        (
            "impl:core::clone::Clone",
            "construction",
            "Self:output=self.output,bytes=self.bytes",
        ),
        ("impl:core::marker::Copy", "impl", "core::marker::Copy"),
        (
            "impl:core::clone::TrivialClone",
            "impl",
            "core::clone::TrivialClone",
        ),
    ] {
        generated.insert(
            fact(
                TargetRole::Binary,
                &module,
                "PublicationSpecV0",
                enclosing,
                kind,
                signature,
            ),
            1,
        );
    }
    ExpansionAllowance {
        identity: AllowanceIdentity::PublicationSpecDerives,
        site: AllowanceSiteEvidence {
            target: TargetRole::Binary,
            logical_module: module,
            protected_type: "PublicationSpecV0".to_string(),
            source_key: "cli/trajectory/linux_output_transaction.rs".to_string(),
            complete_file_digest: hex32(
                "fa4191cdb25f79455541e07ea38617000721901d64b20d92edc2395cf2cdb7bc",
            ),
            definition_digest: None,
            invocation_or_site_digest: hex32(
                "69a33374ada6652bf926761058e3fc064b0b362586cb905b3f90b9e946abdf30",
            ),
            parsed_arguments: vec!["Clone".to_string(), "Copy".to_string()],
            compiler_identity: EXACT_RUSTC_VV.to_vec(),
        },
        generated,
    }
}

fn fact(
    target: TargetRole,
    logical_module: &LogicalModuleId,
    protected_type: &str,
    enclosing_item: &str,
    kind: &str,
    signature: &str,
) -> AuthorityFact {
    AuthorityFact {
        target,
        logical_module: logical_module.clone(),
        protected_type: protected_type.to_string(),
        enclosing_item: enclosing_item.to_string(),
        kind: kind.to_string(),
        signature: signature.to_string(),
    }
}

fn insert_fact(
    facts: &mut BTreeMap<AuthorityFact, u32>,
    fact: AuthorityFact,
) -> Result<(), AuthorityFailure> {
    let count = facts.entry(fact).or_default();
    *count = count
        .checked_add(1)
        .ok_or(AuthorityFailure::ProtectedInventory)?;
    Ok(())
}

fn merge(
    destination: &mut BTreeMap<AuthorityFact, u32>,
    source: BTreeMap<AuthorityFact, u32>,
) -> Result<(), AuthorityFailure> {
    for (fact, count) in source {
        let current = destination.entry(fact).or_default();
        *current = current
            .checked_add(count)
            .ok_or(AuthorityFailure::ProtectedInventory)?;
    }
    Ok(())
}

fn protected(name: &str) -> bool {
    PROTECTED_TYPES.contains(&name)
}

fn protected_type(ty: &syn::Type) -> Option<String> {
    let syn::Type::Path(path) = ty else {
        return None;
    };
    let name = path.path.segments.last()?.ident.to_string();
    protected(&name).then_some(name)
}

fn type_protected_types(ty: &syn::Type) -> BTreeSet<String> {
    let rendered = render_type(ty);
    PROTECTED_TYPES
        .iter()
        .filter(|name| {
            rendered
                .split(|character: char| !character.is_alphanumeric() && character != '_')
                .any(|part| part == **name)
        })
        .map(|name| (*name).to_string())
        .collect()
}

fn signature_protected_types(signature: &syn::Signature) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for input in &signature.inputs {
        if let syn::FnArg::Typed(input) = input {
            names.extend(type_protected_types(&input.ty));
        }
    }
    if let syn::ReturnType::Type(_, output) = &signature.output {
        names.extend(type_protected_types(output));
    }
    names
}

fn render_signature(signature: &syn::Signature, vis: &syn::Visibility) -> String {
    let inputs = signature
        .inputs
        .iter()
        .map(|input| match input {
            syn::FnArg::Receiver(receiver) => {
                if receiver.reference.is_some() {
                    if receiver.mutability.is_some() {
                        "&mut self".to_string()
                    } else {
                        "&self".to_string()
                    }
                } else {
                    "self".to_string()
                }
            }
            syn::FnArg::Typed(input) => render_type(&input.ty),
        })
        .collect::<Vec<_>>()
        .join(",");
    let output = match &signature.output {
        syn::ReturnType::Default => String::new(),
        syn::ReturnType::Type(_, output) => format!("->{}", render_type(output)),
    };
    format!(
        "{}:{}({}){}",
        visibility(vis),
        signature.ident,
        inputs,
        output
    )
}

fn render_fields(fields: &syn::Fields) -> String {
    fields
        .iter()
        .enumerate()
        .map(|(index, field)| {
            format!(
                "{}:{}:{}",
                field
                    .ident
                    .as_ref()
                    .map(normalize_ident)
                    .unwrap_or_else(|| index.to_string()),
                visibility(&field.vis),
                render_type(&field.ty)
            )
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn render_variants(item: &syn::ItemEnum) -> String {
    item.variants
        .iter()
        .map(|variant| format!("{}({})", variant.ident, render_fields(&variant.fields)))
        .collect::<Vec<_>>()
        .join(",")
}

fn render_type(ty: &syn::Type) -> String {
    match ty {
        syn::Type::Path(path) => {
            let mut rendered = render_path(&path.path);
            if let Some(last) = path.path.segments.last()
                && let syn::PathArguments::AngleBracketed(arguments) = &last.arguments
            {
                let arguments = arguments
                    .args
                    .iter()
                    .map(|argument| match argument {
                        syn::GenericArgument::Type(ty) => render_type(ty),
                        syn::GenericArgument::Lifetime(lifetime) => lifetime.to_string(),
                        _ => "unsupported".to_string(),
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                rendered.push('<');
                rendered.push_str(&arguments);
                rendered.push('>');
            }
            rendered
        }
        syn::Type::Reference(reference) => format!(
            "&{}{}",
            if reference.mutability.is_some() {
                "mut "
            } else {
                ""
            },
            render_type(&reference.elem)
        ),
        syn::Type::Tuple(tuple) => format!(
            "({})",
            tuple
                .elems
                .iter()
                .map(render_type)
                .collect::<Vec<_>>()
                .join(",")
        ),
        syn::Type::Slice(slice) => format!("[{}]", render_type(&slice.elem)),
        syn::Type::Array(array) => format!("[{};const]", render_type(&array.elem)),
        syn::Type::Paren(paren) => render_type(&paren.elem),
        syn::Type::Group(group) => render_type(&group.elem),
        syn::Type::Never(_) => "!".to_string(),
        syn::Type::Infer(_) => "_".to_string(),
        _ => "unsupported".to_string(),
    }
}

fn render_path(path: &syn::Path) -> String {
    path.segments
        .iter()
        .map(|part| normalize_ident(&part.ident))
        .collect::<Vec<_>>()
        .join("::")
}

fn visibility(vis: &syn::Visibility) -> &'static str {
    match vis {
        syn::Visibility::Public(_) => "public",
        syn::Visibility::Restricted(_) => "restricted",
        syn::Visibility::Inherited => "inherited",
    }
}

fn use_names(tree: &syn::UseTree, names: &mut Vec<String>) {
    match tree {
        syn::UseTree::Path(path) => use_names(&path.tree, names),
        syn::UseTree::Name(name) => names.push(normalize_ident(&name.ident)),
        syn::UseTree::Rename(rename) => names.push(normalize_ident(&rename.ident)),
        syn::UseTree::Group(group) => {
            for item in &group.items {
                use_names(item, names);
            }
        }
        syn::UseTree::Glob(_) => {}
    }
}

fn normalize_ident(ident: &syn::Ident) -> String {
    let value = ident.to_string();
    value.strip_prefix("r#").unwrap_or(&value).to_string()
}

fn hex32(value: &str) -> [u8; 32] {
    assert_eq!(value.len(), 64);
    let mut bytes = [0; 32];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        bytes[index] = (nibble(pair[0]) << 4) | nibble(pair[1]);
    }
    bytes
}

fn nibble(value: u8) -> u8 {
    match value {
        b'0'..=b'9' => value - b'0',
        b'a'..=b'f' => value - b'a' + 10,
        _ => panic!("non-hex allowance digest"),
    }
}

pub(crate) fn assert_authority_allowance_contains_only_two_canonical_sites() {
    let allowance = DeclaredExpansionAllowanceV1::canonical();
    assert_eq!(allowance.entries().len(), 2);
    assert_eq!(
        allowance
            .entries()
            .iter()
            .map(|entry| entry.identity)
            .collect::<Vec<_>>(),
        [
            AllowanceIdentity::RedactedDebug,
            AllowanceIdentity::PublicationSpecDerives
        ]
    );
    assert_eq!(allowance.entries()[0].generated.values().sum::<u32>(), 2);
    assert_eq!(allowance.entries()[1].generated.values().sum::<u32>(), 5);
    assert!(
        allowance
            .entries()
            .iter()
            .all(|entry| entry.site.compiler_identity == EXACT_RUSTC_VV)
    );

    let source =
        syn::parse_file("pub struct SnapshotV0 { pub(crate) bytes: Vec<u8>, _reader: OwnedFd }\n")
            .unwrap();
    let surface = collect_direct_authority_surface(
        TargetRole::Library,
        &LogicalModuleId(vec!["snapshot".to_string()]),
        &source.items,
    )
    .unwrap();
    assert_eq!(surface.0.len(), 1);
    assert_eq!(
        collect_expanded_authority_surface(
            TargetRole::Library,
            &LogicalModuleId(vec!["snapshot".to_string()]),
            &source.items
        )
        .unwrap()
        .0,
        surface.0
    );
}

pub(crate) fn assert_removing_either_expansion_allowance_rejects_the_baseline_fixture() {
    let allowance = DeclaredExpansionAllowanceV1::canonical();
    let base = fact(
        TargetRole::Library,
        &LogicalModuleId(vec!["base".to_string()]),
        "SnapshotV0",
        "SnapshotV0",
        "declaration",
        "baseline-fixture",
    );
    let direct = DirectAuthoritySurface(BTreeMap::from([(base.clone(), 1)]));
    let mut expanded_facts = direct.0.clone();
    let mut sites = BTreeMap::new();
    for entry in allowance.entries() {
        merge(&mut expanded_facts, entry.generated.clone()).unwrap();
        sites.insert(entry.identity, entry.site.clone());
    }
    let expanded = ExpandedAuthoritySurface(expanded_facts);
    assert_eq!(allowance.reconcile(&direct, &expanded, &sites), Ok(()));
    for removed in [
        AllowanceIdentity::RedactedDebug,
        AllowanceIdentity::PublicationSpecDerives,
    ] {
        let mut incomplete = sites.clone();
        incomplete.remove(&removed);
        assert_eq!(
            allowance.reconcile(&direct, &expanded, &incomplete),
            Err(AuthorityFailure::ExpansionAuthoritySurface)
        );
    }
}
