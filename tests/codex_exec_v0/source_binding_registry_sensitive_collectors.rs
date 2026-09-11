use super::*;

pub(super) fn named_struct_field_types(syntax: &syn::File, name: &str) -> BTreeMap<String, String> {
    syntax
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Struct(item) if item.ident == name => Some(
                item.fields
                    .iter()
                    .map(|field| {
                        (
                            field.ident.as_ref().unwrap().to_string(),
                            type_shape(&field.ty),
                        )
                    })
                    .collect(),
            ),
            _ => None,
        })
        .unwrap_or_default()
}

pub(super) fn type_shape(ty: &syn::Type) -> String {
    match ty {
        syn::Type::Path(path) => path_shape(&path.path),
        syn::Type::Reference(reference) => {
            let mut shape = "&".to_string();
            if let Some(lifetime) = &reference.lifetime {
                shape.push_str(&lifetime.to_string());
                shape.push(' ');
            }
            if reference.mutability.is_some() {
                shape.push_str("mut ");
            }
            shape.push_str(&type_shape(&reference.elem));
            shape
        }
        syn::Type::Slice(slice) => format!("[{}]", type_shape(&slice.elem)),
        syn::Type::Tuple(tuple) => format!(
            "({})",
            tuple
                .elems
                .iter()
                .map(type_shape)
                .collect::<Vec<_>>()
                .join(",")
        ),
        syn::Type::Array(array) => format!("[{};const]", type_shape(&array.elem)),
        syn::Type::Paren(paren) => format!("({})", type_shape(&paren.elem)),
        syn::Type::Group(group) => type_shape(&group.elem),
        syn::Type::Never(_) => "!".to_string(),
        _ => "non-path".to_string(),
    }
}

pub(super) fn path_shape(path: &syn::Path) -> String {
    path.segments
        .iter()
        .map(|segment| {
            let mut shape = normalize_rust_ident(&segment.ident);
            if let syn::PathArguments::AngleBracketed(arguments) = &segment.arguments {
                let nested = arguments
                    .args
                    .iter()
                    .map(|argument| match argument {
                        syn::GenericArgument::Type(ty) => type_shape(ty),
                        syn::GenericArgument::Lifetime(lifetime) => lifetime.to_string(),
                        syn::GenericArgument::Const(_) => "const".to_string(),
                        _ => "non-type".to_string(),
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                shape.push('<');
                shape.push_str(&nested);
                shape.push('>');
            }
            shape
        })
        .collect::<Vec<_>>()
        .join("::")
}

pub(super) fn inherited_visibilities(
    fields: &BTreeMap<String, String>,
) -> BTreeMap<String, String> {
    fields
        .keys()
        .map(|field| (field.clone(), "inherited".to_string()))
        .collect()
}

pub(super) fn item_visibility(syntax: &syn::File, name: &str) -> Option<&'static str> {
    syntax.items.iter().find_map(|item| match item {
        syn::Item::Struct(item) if normalize_rust_ident(&item.ident) == name => {
            Some(visibility_shape(&item.vis))
        }
        syn::Item::Enum(item) if normalize_rust_ident(&item.ident) == name => {
            Some(visibility_shape(&item.vis))
        }
        _ => None,
    })
}

pub(super) fn visibility_shape(visibility: &syn::Visibility) -> &'static str {
    match visibility {
        syn::Visibility::Inherited => "inherited",
        syn::Visibility::Public(_) => "public",
        syn::Visibility::Restricted(restricted) if restricted.path.is_ident("crate") => "crate",
        syn::Visibility::Restricted(restricted) if restricted.path.is_ident("super") => "super",
        syn::Visibility::Restricted(_) => "restricted",
    }
}

pub(super) fn enum_variant_shapes(
    syntax: &syn::File,
    name: &str,
) -> BTreeMap<String, BTreeMap<String, String>> {
    syntax
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Enum(item) if normalize_rust_ident(&item.ident) == name => Some(
                item.variants
                    .iter()
                    .map(|variant| {
                        let fields = variant
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(index, field)| {
                                (
                                    field
                                        .ident
                                        .as_ref()
                                        .map_or_else(|| index.to_string(), ToString::to_string),
                                    type_shape(&field.ty),
                                )
                            })
                            .collect();
                        (normalize_rust_ident(&variant.ident), fields)
                    })
                    .collect(),
            ),
            _ => None,
        })
        .unwrap_or_default()
}

pub(super) fn normalize(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            std::path::Component::ParentDir => {
                normalized.pop();
            }
            other => normalized.push(other.as_os_str()),
        }
    }
    normalized
}

pub(super) fn relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap()
        .to_string_lossy()
        .replace('\\', "/")
}
