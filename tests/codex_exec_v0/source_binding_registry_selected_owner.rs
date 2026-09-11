use super::direct_graph::{DirectModuleGraph, LogicalModuleId, TargetRole};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SelectedOwner {
    pub(crate) logical_module: LogicalModuleId,
    pub(crate) source_path: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OwnerFailure {
    SemanticModuleParse,
    SelectedOwnerMultiplicity,
    OwnerIncomingEdge,
    OwnerSubtree,
    OwnerBinding,
}

pub(crate) fn derive_selected_owner(
    library: &DirectModuleGraph,
    selected_bytes: &BTreeMap<String, Vec<u8>>,
    sanitizer_components: &[String],
) -> Result<SelectedOwner, OwnerFailure> {
    if library.target() != TargetRole::Library {
        return Err(OwnerFailure::SelectedOwnerMultiplicity);
    }
    let mut candidates = Vec::new();
    for (logical, path) in library.modules() {
        let source = selected_bytes
            .get(path)
            .and_then(|bytes| std::str::from_utf8(bytes).ok())
            .ok_or(OwnerFailure::SemanticModuleParse)?;
        let syntax = syn::parse_file(source).map_err(|_| OwnerFailure::SemanticModuleParse)?;
        let items = logical_items(library, logical, path, &syntax)?;
        let mint = items
            .iter()
            .filter_map(|item| match item {
                syn::Item::Struct(item) if item.ident == "PublicationMintV0" => Some(item),
                _ => None,
            })
            .collect::<Vec<_>>();
        let bundle = items
            .iter()
            .filter_map(|item| match item {
                syn::Item::Struct(item) if item.ident == "ShareableSanitizedBundleV0" => Some(item),
                _ => None,
            })
            .collect::<Vec<_>>();
        if matches!(
            (mint.as_slice(), bundle.as_slice()),
            ([mint], [bundle])
                if matches!(mint.vis, syn::Visibility::Inherited)
                    && matches!(bundle.vis, syn::Visibility::Public(_))
                    && bundle
                        .fields
                        .iter()
                        .all(|field| matches!(field.vis, syn::Visibility::Inherited))
        ) {
            candidates.push(SelectedOwner {
                logical_module: logical.clone(),
                source_path: path.clone(),
            });
        }
    }
    let [owner] = candidates.as_slice() else {
        return Err(OwnerFailure::SelectedOwnerMultiplicity);
    };
    if library
        .edges()
        .iter()
        .filter(|edge| edge.to == owner.logical_module)
        .count()
        != 1
    {
        return Err(OwnerFailure::OwnerIncomingEdge);
    }
    if library
        .edges()
        .iter()
        .any(|edge| edge.from == owner.logical_module)
        || library.modules().iter().any(|(logical, path)| {
            logical.0.len() == owner.logical_module.0.len() + 1
                && logical
                    .0
                    .strip_suffix(&logical.0[owner.logical_module.0.len()..])
                    == Some(owner.logical_module.0.as_slice())
                && path == &owner.source_path
        })
    {
        return Err(OwnerFailure::OwnerSubtree);
    }
    if sanitizer_components
        .iter()
        .filter(|path| *path == &owner.source_path)
        .count()
        != 1
    {
        return Err(OwnerFailure::OwnerBinding);
    }
    Ok(owner.clone())
}

fn logical_items<'a>(
    graph: &DirectModuleGraph,
    logical: &LogicalModuleId,
    path: &str,
    syntax: &'a syn::File,
) -> Result<&'a [syn::Item], OwnerFailure> {
    let base = graph
        .modules()
        .iter()
        .filter(|(candidate, candidate_path)| {
            candidate_path == &path
                && candidate.0.len() <= logical.0.len()
                && logical.0.starts_with(&candidate.0)
        })
        .min_by_key(|(candidate, _)| candidate.0.len())
        .map(|(candidate, _)| candidate)
        .ok_or(OwnerFailure::SemanticModuleParse)?;
    let mut items = syntax.items.as_slice();
    for segment in &logical.0[base.0.len()..] {
        let matches = items
            .iter()
            .filter_map(|item| match item {
                syn::Item::Mod(module)
                    if normalized_ident(&module.ident) == *segment && module.content.is_some() =>
                {
                    module.content.as_ref().map(|(_, items)| items.as_slice())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        let [nested] = matches.as_slice() else {
            return Err(OwnerFailure::SemanticModuleParse);
        };
        items = nested;
    }
    Ok(items)
}

fn normalized_ident(ident: &syn::Ident) -> String {
    let value = ident.to_string();
    value.strip_prefix("r#").unwrap_or(&value).to_string()
}

pub(crate) fn assert_selected_owner_is_structural_and_graph_bound() {
    let active = super::selected_cfg::ActiveCfgAtoms::parse(b"target_os=\"linux\"\n").unwrap();
    let grammar = super::selected_cfg::RecognizedCfgGrammar::parse(
        b"cfg(target_os, values(\"linux\", \"windows\"))\n",
    )
    .unwrap();
    let bytes = BTreeMap::from([
        (
            "lib/root.fixture".to_string(),
            b"#[path=\"owner.fixture\"] mod authority;\n".to_vec(),
        ),
        (
            "lib/owner.fixture".to_string(),
            b"struct PublicationMintV0 { nonce: [u8; 32] }\n\
pub struct ShareableSanitizedBundleV0 { bytes: Vec<u8> }\n"
                .to_vec(),
        ),
        ("bin/root.fixture".to_string(), b"fn main() {}\n".to_vec()),
    ]);
    let graphs = super::direct_graph::derive_target_graphs(
        "lib/root.fixture",
        "bin/root.fixture",
        &bytes,
        (&active, &grammar),
        (&active, &grammar),
    )
    .unwrap();
    let owner =
        derive_selected_owner(&graphs.library, &bytes, &["lib/owner.fixture".to_string()]).unwrap();
    assert_eq!(owner.logical_module.0, ["authority"]);
    assert_eq!(owner.source_path, "lib/owner.fixture");

    let duplicate_source = bytes["lib/owner.fixture"].clone();
    let mut duplicate = bytes;
    duplicate.insert(
        "lib/root.fixture".to_string(),
        b"#[path=\"owner.fixture\"] mod authority;\n#[path=\"sibling.fixture\"] mod sibling;\n"
            .to_vec(),
    );
    duplicate.insert("lib/sibling.fixture".to_string(), duplicate_source);
    let duplicate_graph = super::direct_graph::derive_graph(
        TargetRole::Library,
        "lib/root.fixture",
        &duplicate,
        &active,
        &grammar,
    )
    .unwrap();
    assert_eq!(
        derive_selected_owner(
            &duplicate_graph,
            &duplicate,
            &[
                "lib/owner.fixture".to_string(),
                "lib/sibling.fixture".to_string()
            ]
        ),
        Err(OwnerFailure::SelectedOwnerMultiplicity)
    );

    let unique_components = BTreeSet::from(["lib/owner.fixture".to_string()]);
    assert_eq!(unique_components.len(), 1);
}
