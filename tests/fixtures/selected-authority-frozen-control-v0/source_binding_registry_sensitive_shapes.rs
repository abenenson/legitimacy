use super::*;

pub(super) fn named_struct_fields(syntax: &syn::File, name: &str) -> BTreeSet<String> {
    syntax
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Struct(item) if item.ident == name => Some(
                item.fields
                    .iter()
                    .map(|field| field.ident.as_ref().unwrap().to_string())
                    .collect(),
            ),
            _ => None,
        })
        .unwrap()
}

pub(super) fn named_struct_field_visibilities(
    syntax: &syn::File,
    name: &str,
) -> BTreeMap<String, String> {
    syntax
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Struct(item) if item.ident == name => Some(
                item.fields
                    .iter()
                    .map(|field| {
                        let visibility = match field.vis {
                            syn::Visibility::Inherited => "inherited",
                            syn::Visibility::Public(_) => "public",
                            syn::Visibility::Restricted(_) => "restricted",
                        };
                        (
                            field.ident.as_ref().unwrap().to_string(),
                            visibility.to_string(),
                        )
                    })
                    .collect(),
            ),
            _ => None,
        })
        .unwrap()
}

pub(super) fn named_struct_has_derive(syntax: &syn::File, name: &str) -> bool {
    syntax.items.iter().any(|item| match item {
        syn::Item::Struct(item) if item.ident == name => item
            .attrs
            .iter()
            .any(|attribute| attribute.path().is_ident("derive")),
        _ => false,
    })
}

pub(super) fn inherent_method_names(syntax: &syn::File, name: &str) -> BTreeSet<String> {
    syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Impl(item) if item.trait_.is_none() => {
                let syn::Type::Path(path) = item.self_ty.as_ref() else {
                    return None;
                };
                (path.path.segments.last().unwrap().ident == name).then_some(item)
            }
            _ => None,
        })
        .flat_map(|item| &item.items)
        .filter_map(|item| match item {
            syn::ImplItem::Fn(method) => Some(method.sig.ident.to_string()),
            _ => None,
        })
        .collect()
}

pub(super) fn public_inherent_method_names(syntax: &syn::File, name: &str) -> BTreeSet<String> {
    syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Impl(item) if item.trait_.is_none() => {
                let syn::Type::Path(path) = item.self_ty.as_ref() else {
                    return None;
                };
                (path.path.segments.last().unwrap().ident == name).then_some(item)
            }
            _ => None,
        })
        .flat_map(|item| &item.items)
        .filter_map(|item| match item {
            syn::ImplItem::Fn(method) if matches!(method.vis, syn::Visibility::Public(_)) => {
                Some(method.sig.ident.to_string())
            }
            _ => None,
        })
        .collect()
}

pub(super) fn implemented_trait_names(syntax: &syn::File, name: &str) -> BTreeSet<String> {
    syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Impl(item) => {
                let (_, trait_path, _) = item.trait_.as_ref()?;
                let syn::Type::Path(self_path) = item.self_ty.as_ref() else {
                    return None;
                };
                (self_path.path.segments.last().unwrap().ident == name).then(|| {
                    trait_path
                        .segments
                        .iter()
                        .map(|segment| segment.ident.to_string())
                        .collect::<Vec<_>>()
                        .join("::")
                })
            }
            _ => None,
        })
        .collect()
}

pub(super) const SENSITIVE_AUTHORITY_TYPES: &[&str] = &[
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

pub(super) fn normalize_rust_ident(ident: impl ToString) -> String {
    let ident = ident.to_string();
    ident.strip_prefix("r#").unwrap_or(&ident).to_string()
}

pub(super) fn named_struct_shape(
    syntax: &syn::File,
    name: &str,
) -> Vec<(String, String, &'static str)> {
    syntax
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Struct(item) if normalize_rust_ident(&item.ident) == name => Some(
                item.fields
                    .iter()
                    .map(|field| {
                        (
                            normalize_rust_ident(field.ident.as_ref().unwrap()),
                            type_shape(&field.ty),
                            visibility_shape(&field.vis),
                        )
                    })
                    .collect(),
            ),
            _ => None,
        })
        .unwrap_or_default()
}

pub(super) fn item_derive_names(syntax: &syn::File, name: &str) -> BTreeSet<String> {
    let attributes = syntax.items.iter().find_map(|item| match item {
        syn::Item::Struct(item) if normalize_rust_ident(&item.ident) == name => Some(&item.attrs),
        syn::Item::Enum(item) if normalize_rust_ident(&item.ident) == name => Some(&item.attrs),
        _ => None,
    });
    let Some(attributes) = attributes else {
        return BTreeSet::new();
    };
    attributes
        .iter()
        .filter(|attribute| attribute.path().is_ident("derive"))
        .flat_map(|attribute| {
            let syn::Meta::List(list) = &attribute.meta else {
                return Vec::new();
            };
            list.parse_args_with(
                syn::punctuated::Punctuated::<syn::Path, syn::Token![,]>::parse_terminated,
            )
            .map(|paths| paths.iter().map(path_shape).collect::<Vec<_>>())
            .unwrap_or_default()
        })
        .collect()
}

pub(super) fn authority_boundary_has_unreviewed_syntax(syntax: &syn::File) -> bool {
    use syn::visit::Visit;

    let mut visitor = AuthorityBoundarySyntaxVisitor::default();
    visitor.visit_file(syntax);
    visitor.has_unreviewed_syntax
}

#[derive(Default)]
struct AuthorityBoundarySyntaxVisitor {
    item_depth: usize,
    has_unreviewed_syntax: bool,
}

impl<'ast> syn::visit::Visit<'ast> for AuthorityBoundarySyntaxVisitor {
    fn visit_attribute(&mut self, attribute: &'ast syn::Attribute) {
        if !attribute.path().is_ident("doc") {
            self.has_unreviewed_syntax = true;
        }
        syn::visit::visit_attribute(self, attribute);
    }

    fn visit_macro(&mut self, syntax_macro: &'ast syn::Macro) {
        self.has_unreviewed_syntax = true;
        syn::visit::visit_macro(self, syntax_macro);
    }

    fn visit_item(&mut self, item: &'ast syn::Item) {
        if self.item_depth > 0
            || matches!(
                item,
                syn::Item::Macro(_) | syn::Item::Mod(_) | syn::Item::Verbatim(_)
            )
        {
            self.has_unreviewed_syntax = true;
        }
        self.item_depth += 1;
        syn::visit::visit_item(self, item);
        self.item_depth -= 1;
    }

    fn visit_expr(&mut self, expression: &'ast syn::Expr) {
        if matches!(expression, syn::Expr::Verbatim(_)) {
            self.has_unreviewed_syntax = true;
        }
        syn::visit::visit_expr(self, expression);
    }

    fn visit_foreign_item(&mut self, item: &'ast syn::ForeignItem) {
        if matches!(item, syn::ForeignItem::Verbatim(_)) {
            self.has_unreviewed_syntax = true;
        }
        syn::visit::visit_foreign_item(self, item);
    }

    fn visit_impl_item(&mut self, item: &'ast syn::ImplItem) {
        if matches!(item, syn::ImplItem::Verbatim(_)) {
            self.has_unreviewed_syntax = true;
        }
        syn::visit::visit_impl_item(self, item);
    }

    fn visit_lit(&mut self, literal: &'ast syn::Lit) {
        if matches!(literal, syn::Lit::Verbatim(_)) {
            self.has_unreviewed_syntax = true;
        }
        syn::visit::visit_lit(self, literal);
    }

    fn visit_pat(&mut self, pattern: &'ast syn::Pat) {
        if matches!(pattern, syn::Pat::Verbatim(_)) {
            self.has_unreviewed_syntax = true;
        }
        syn::visit::visit_pat(self, pattern);
    }

    fn visit_trait_item(&mut self, item: &'ast syn::TraitItem) {
        if matches!(item, syn::TraitItem::Verbatim(_)) {
            self.has_unreviewed_syntax = true;
        }
        syn::visit::visit_trait_item(self, item);
    }

    fn visit_type(&mut self, ty: &'ast syn::Type) {
        if matches!(ty, syn::Type::Verbatim(_)) {
            self.has_unreviewed_syntax = true;
        }
        syn::visit::visit_type(self, ty);
    }

    fn visit_type_param_bound(&mut self, bound: &'ast syn::TypeParamBound) {
        if matches!(bound, syn::TypeParamBound::Verbatim(_)) {
            self.has_unreviewed_syntax = true;
        }
        syn::visit::visit_type_param_bound(self, bound);
    }
}

pub(super) fn signature_shape(signature: &syn::Signature, visibility: &syn::Visibility) -> String {
    let arguments = signature
        .inputs
        .iter()
        .map(|argument| match argument {
            syn::FnArg::Receiver(receiver) => {
                if receiver.colon_token.is_some() {
                    format!("self:{}", type_shape(&receiver.ty))
                } else {
                    let mut shape = String::new();
                    if receiver.reference.is_some() {
                        shape.push('&');
                    }
                    if receiver.mutability.is_some() {
                        shape.push_str("mut ");
                    }
                    shape.push_str("self");
                    shape
                }
            }
            syn::FnArg::Typed(argument) => {
                let name = match argument.pat.as_ref() {
                    syn::Pat::Ident(ident) => normalize_rust_ident(&ident.ident),
                    _ => "non-ident".to_string(),
                };
                format!("{name}:{}", type_shape(&argument.ty))
            }
        })
        .collect::<Vec<_>>()
        .join(",");
    let output = match &signature.output {
        syn::ReturnType::Default => String::new(),
        syn::ReturnType::Type(_, ty) => format!("->{}", type_shape(ty)),
    };
    format!(
        "{} fn {}({arguments}){output}",
        visibility_shape(visibility),
        normalize_rust_ident(&signature.ident),
    )
}

pub(super) fn sensitive_impl_surface(
    sources: &BTreeMap<String, String>,
) -> Result<BTreeSet<String>, &'static str> {
    let sensitive = SENSITIVE_AUTHORITY_TYPES
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut surface = BTreeSet::new();
    for (source_path, source) in sources {
        if !SENSITIVE_AUTHORITY_TYPES
            .iter()
            .any(|name| source.contains(name))
        {
            continue;
        }
        let syntax = syn::parse_file(source).map_err(|_| "capability-shape")?;
        for item in &syntax.items {
            let syn::Item::Impl(item) = item else {
                continue;
            };
            let syn::Type::Path(self_path) = item.self_ty.as_ref() else {
                continue;
            };
            let Some(segment) = self_path.path.segments.last() else {
                continue;
            };
            let target = normalize_rust_ident(&segment.ident);
            let trait_contains_sensitive = item.trait_.as_ref().is_some_and(|(_, path, _)| {
                path_contains_any_type(path, SENSITIVE_AUTHORITY_TYPES)
            });
            if !sensitive.contains(target.as_str()) && !trait_contains_sensitive {
                continue;
            }
            let implementation = item.trait_.as_ref().map_or_else(
                || "inherent".to_string(),
                |(_, path, _)| format!("trait:{}", path_shape(path)),
            );
            surface.insert(format!(
                "{source_path}|{target}|{implementation}|impl-attributes:{}",
                item.attrs.len()
            ));
            for member in &item.items {
                match member {
                    syn::ImplItem::Fn(method) => {
                        surface.insert(format!(
                            "{source_path}|{target}|{implementation}|{}",
                            signature_shape(&method.sig, &method.vis)
                        ));
                    }
                    _ => {
                        surface.insert(format!(
                            "{source_path}|{target}|{implementation}|non-function-member"
                        ));
                    }
                }
            }
        }
    }
    Ok(surface)
}

pub(super) fn path_contains_any_type(path: &syn::Path, names: &[&str]) -> bool {
    path.segments.iter().any(|segment| {
        names.contains(&normalize_rust_ident(&segment.ident).as_str())
            || match &segment.arguments {
                syn::PathArguments::AngleBracketed(arguments) => {
                    arguments.args.iter().any(|argument| {
                        matches!(
                            argument,
                            syn::GenericArgument::Type(ty) if type_contains_any(ty, names)
                        )
                    })
                }
                _ => false,
            }
    })
}

pub(super) fn collect_sensitive_reexports(
    source_path: &str,
    source: &str,
    output: &mut Vec<String>,
) -> Result<(), &'static str> {
    if !SENSITIVE_AUTHORITY_TYPES
        .iter()
        .any(|name| source.contains(name))
    {
        return Ok(());
    }
    let syntax = syn::parse_file(source).map_err(|_| "capability-shape")?;
    for item in &syntax.items {
        let syn::Item::Use(item) = item else {
            continue;
        };
        if matches!(item.vis, syn::Visibility::Inherited) {
            continue;
        }
        collect_sensitive_reexport_tree(
            source_path,
            visibility_shape(&item.vis),
            Vec::new(),
            &item.tree,
            output,
        )?;
    }
    Ok(())
}

pub(super) fn collect_sensitive_reexport_tree(
    source_path: &str,
    visibility: &str,
    mut prefix: Vec<String>,
    tree: &syn::UseTree,
    output: &mut Vec<String>,
) -> Result<(), &'static str> {
    match tree {
        syn::UseTree::Path(path) => {
            prefix.push(normalize_rust_ident(&path.ident));
            collect_sensitive_reexport_tree(source_path, visibility, prefix, &path.tree, output)
        }
        syn::UseTree::Name(name) => {
            let exposed = normalize_rust_ident(&name.ident);
            prefix.push(exposed.clone());
            if SENSITIVE_AUTHORITY_TYPES.contains(&exposed.as_str()) {
                output.push(format!(
                    "{source_path}|{visibility}|{}->{exposed}",
                    prefix.join("::")
                ));
            }
            Ok(())
        }
        syn::UseTree::Rename(rename) => {
            let original = normalize_rust_ident(&rename.ident);
            let exposed = normalize_rust_ident(&rename.rename);
            prefix.push(original.clone());
            if SENSITIVE_AUTHORITY_TYPES.contains(&original.as_str())
                || SENSITIVE_AUTHORITY_TYPES.contains(&exposed.as_str())
            {
                output.push(format!(
                    "{source_path}|{visibility}|{}->{exposed}",
                    prefix.join("::")
                ));
            }
            Ok(())
        }
        syn::UseTree::Group(group) => {
            for nested in &group.items {
                collect_sensitive_reexport_tree(
                    source_path,
                    visibility,
                    prefix.clone(),
                    nested,
                    output,
                )?;
            }
            Ok(())
        }
        syn::UseTree::Glob(_) => {
            output.push(format!(
                "{source_path}|{visibility}|{}::*->*",
                prefix.join("::")
            ));
            Ok(())
        }
    }
}

pub(super) fn sensitive_reexport_surface(
    sources: &BTreeMap<String, String>,
) -> Result<Vec<String>, &'static str> {
    let mut output = Vec::new();
    for (source_path, source) in sources {
        collect_sensitive_reexports(source_path, source, &mut output)?;
    }
    output.sort();
    Ok(output)
}

pub(super) fn callable_surface_for_types(
    sources: &BTreeMap<String, String>,
    names: &[&str],
) -> Result<BTreeSet<String>, &'static str> {
    let mut surface = BTreeSet::new();
    for (source_path, source) in sources {
        if !names.iter().any(|name| source.contains(name)) {
            continue;
        }
        let syntax = syn::parse_file(source).map_err(|_| "capability-shape")?;
        for item in &syntax.items {
            match item {
                syn::Item::Fn(function) if signature_contains_any_type(&function.sig, names) => {
                    surface.insert(format!(
                        "{source_path}|free|{}",
                        signature_shape(&function.sig, &function.vis)
                    ));
                }
                syn::Item::Impl(item) if item.trait_.is_none() => {
                    let syn::Type::Path(self_path) = item.self_ty.as_ref() else {
                        continue;
                    };
                    let target = self_path
                        .path
                        .segments
                        .last()
                        .map(|segment| normalize_rust_ident(&segment.ident))
                        .unwrap_or_default();
                    for member in &item.items {
                        let syn::ImplItem::Fn(method) = member else {
                            continue;
                        };
                        if signature_contains_any_type(&method.sig, names) {
                            surface.insert(format!(
                                "{source_path}|impl:{target}|{}",
                                signature_shape(&method.sig, &method.vis)
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
    }
    Ok(surface)
}

pub(super) fn signature_contains_any_type(signature: &syn::Signature, names: &[&str]) -> bool {
    signature.inputs.iter().any(|argument| {
        matches!(
            argument,
            syn::FnArg::Typed(argument) if type_contains_any(&argument.ty, names)
        )
    }) || matches!(
        &signature.output,
        syn::ReturnType::Type(_, ty) if type_contains_any(ty, names)
    )
}

pub(super) fn sensitive_struct_literal_counts(
    sources: &BTreeMap<String, String>,
    names: &[&str],
) -> Result<BTreeMap<(String, String), usize>, &'static str> {
    let mut counts = BTreeMap::new();
    for (source_path, source) in sources {
        if !names.iter().any(|name| source.contains(name)) {
            continue;
        }
        syn::parse_file(source).map_err(|_| "capability-shape")?;
        let mut parser = rust_parser();
        let tree = parser.parse(source, None).ok_or("capability-shape")?;
        if tree.root_node().has_error() {
            return Err("capability-shape");
        }
        for name in names {
            let count = count_named_struct_expressions(tree.root_node(), source.as_bytes(), name);
            if count > 0 {
                counts.insert((source_path.clone(), (*name).to_string()), count);
            }
        }
    }
    Ok(counts)
}

pub(super) fn count_named_struct_expressions(
    node: tree_sitter::Node<'_>,
    source: &[u8],
    name: &str,
) -> usize {
    let here = if node.kind() == "struct_expression" {
        node.child_by_field_name("name")
            .or_else(|| node.named_child(0))
            .and_then(|candidate| candidate.utf8_text(source).ok())
            .is_some_and(|candidate| {
                candidate
                    .rsplit("::")
                    .next()
                    .is_some_and(|candidate| candidate == name)
            }) as usize
    } else {
        0
    };
    let mut cursor = node.walk();
    here + node
        .named_children(&mut cursor)
        .map(|child| count_named_struct_expressions(child, source, name))
        .sum::<usize>()
}

pub(super) fn registered_method_call_count(
    sources: &BTreeMap<String, String>,
    method: &str,
) -> Result<usize, &'static str> {
    let mut total = 0usize;
    for source in sources.values() {
        if !source.contains(method) {
            continue;
        }
        let mut parser = rust_parser();
        let tree = parser.parse(source, None).ok_or("capability-shape")?;
        if tree.root_node().has_error() {
            return Err("capability-shape");
        }
        total = total
            .checked_add(
                call_name_counts(tree.root_node(), source.as_bytes())
                    .get(&format!("method:{method}"))
                    .copied()
                    .unwrap_or(0),
            )
            .ok_or("capability-shape")?;
    }
    Ok(total)
}

pub(super) fn type_contains_sensitive(ty: &syn::Type) -> bool {
    type_contains_any(ty, SENSITIVE_AUTHORITY_TYPES)
}

pub(super) fn type_contains_live_fd(ty: &syn::Type) -> bool {
    type_contains_any(ty, &["OwnedFd", "BorrowedFd", "RawFd"])
}

pub(super) fn type_contains_any(ty: &syn::Type, names: &[&str]) -> bool {
    match ty {
        syn::Type::Path(path) => path.path.segments.iter().any(|segment| {
            names.contains(&normalize_rust_ident(&segment.ident).as_str())
                || match &segment.arguments {
                    syn::PathArguments::AngleBracketed(arguments) => {
                        arguments.args.iter().any(|argument| {
                            matches!(
                                argument,
                                syn::GenericArgument::Type(ty) if type_contains_any(ty, names)
                            )
                        })
                    }
                    _ => false,
                }
        }),
        syn::Type::Reference(reference) => type_contains_any(&reference.elem, names),
        syn::Type::Slice(slice) => type_contains_any(&slice.elem, names),
        syn::Type::Tuple(tuple) => tuple.elems.iter().any(|ty| type_contains_any(ty, names)),
        syn::Type::Paren(paren) => type_contains_any(&paren.elem, names),
        syn::Type::Group(group) => type_contains_any(&group.elem, names),
        _ => false,
    }
}

pub(super) fn source_has_sensitive_alias_or_fd_leak(source: &str) -> Result<bool, &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "capability-shape")?;
    for item in &syntax.items {
        match item {
            syn::Item::Type(alias) if type_contains_sensitive(&alias.ty) => return Ok(true),
            syn::Item::Use(item) if use_tree_renames_sensitive(&item.tree) => return Ok(true),
            syn::Item::Fn(function) => {
                let input_has_sensitive = function.sig.inputs.iter().any(|argument| {
                    matches!(
                        argument,
                        syn::FnArg::Typed(argument) if type_contains_sensitive(&argument.ty)
                    )
                });
                let returns_live_fd = matches!(
                    &function.sig.output,
                    syn::ReturnType::Type(_, ty) if type_contains_live_fd(ty)
                );
                if input_has_sensitive && returns_live_fd {
                    return Ok(true);
                }
            }
            _ => {}
        }
    }
    Ok(false)
}

pub(super) fn use_tree_renames_sensitive(tree: &syn::UseTree) -> bool {
    match tree {
        syn::UseTree::Path(path) => use_tree_renames_sensitive(&path.tree),
        syn::UseTree::Rename(rename) => {
            SENSITIVE_AUTHORITY_TYPES.contains(&normalize_rust_ident(&rename.ident).as_str())
                || SENSITIVE_AUTHORITY_TYPES
                    .contains(&normalize_rust_ident(&rename.rename).as_str())
        }
        syn::UseTree::Group(group) => group.items.iter().any(use_tree_renames_sensitive),
        syn::UseTree::Name(_) | syn::UseTree::Glob(_) => false,
    }
}
