use super::{BindingFailure, Bound, SelectedRole, SyntheticSelectedTree};
use crate::source_binding_registry::compiler_envelope::CompilerEvidenceEnvelopeV1;
use crate::source_binding_registry::direct_graph::{DirectModuleGraph, DirectTargetGraphs};
use crate::source_binding_registry::selected_artifacts::AssociatedCargoRecords;
use crate::source_binding_registry::selected_owner::{SelectedOwner, derive_selected_owner};

pub(super) struct FinalClosureStages {
    pub(crate) bound_tree: SyntheticSelectedTree<Bound>,
    pub(crate) envelope: CompilerEvidenceEnvelopeV1,
    pub(crate) artifacts: AssociatedCargoRecords,
    pub(crate) graphs: DirectTargetGraphs,
    pub(crate) adapter_components: Vec<String>,
    pub(crate) sanitizer_components: Vec<String>,
    pub(crate) owner: SelectedOwner,
}

pub(super) struct VerifiedSelectedRustClosure {
    artifacts: AssociatedCargoRecords,
    envelope: CompilerEvidenceEnvelopeV1,
    table: super::SelectedByteRoleTable,
    graphs: DirectTargetGraphs,
    adapter_components: Vec<String>,
    sanitizer_components: Vec<String>,
    compiled_binding: super::CompiledBindingTranscript,
    owner: SelectedOwner,
}

pub(super) fn construct_verified_selected_rust_closure(
    stages: FinalClosureStages,
) -> Result<VerifiedSelectedRustClosure, BindingFailure> {
    let FinalClosureStages {
        bound_tree,
        envelope,
        artifacts,
        graphs,
        adapter_components,
        sanitizer_components,
        owner,
    } = stages;
    if envelope.digest() != bound_tree.state.envelope_digest
        || bound_tree.table.digest() != bound_tree.state.table_digest
        || sanitizer_components
            != bound_tree
                .state
                .compiled
                .components
                .iter()
                .map(|component| component.path.clone())
                .collect::<Vec<_>>()
        || adapter_components.is_empty()
        || !sanitizer_components.starts_with(&adapter_components)
    {
        return Err(BindingFailure::EvidenceEnvelope);
    }
    super::validate_compiled_transcript(&bound_tree.state.compiled, &bound_tree.table)?;
    validate_graph_roles(&graphs.library, &bound_tree, SelectedRole::LibraryModule)?;
    validate_graph_roles(&graphs.binary, &bound_tree, SelectedRole::BinaryModule)?;
    let selected_bytes = bound_tree
        .table
        .entries
        .iter()
        .map(|(path, entry)| (path.clone(), entry.bytes.to_vec()))
        .collect();
    if derive_selected_owner(&graphs.library, &selected_bytes, &sanitizer_components)
        .map_err(|_| BindingFailure::CompiledTranscript)?
        != owner
    {
        return Err(BindingFailure::CompiledTranscript);
    }
    Ok(VerifiedSelectedRustClosure {
        artifacts,
        envelope,
        table: bound_tree.table,
        graphs,
        adapter_components,
        sanitizer_components,
        compiled_binding: bound_tree.state.compiled,
        owner,
    })
}

fn validate_graph_roles(
    graph: &DirectModuleGraph,
    tree: &SyntheticSelectedTree<Bound>,
    expected_role: SelectedRole,
) -> Result<(), BindingFailure> {
    for path in graph.modules().values() {
        if !tree.table.roles(path)?.contains(&expected_role) {
            return Err(BindingFailure::SelectedInputAccounting);
        }
    }
    for edge in graph.embedded_data() {
        if !tree
            .table
            .roles(&edge.data_path)?
            .contains(&SelectedRole::EmbeddedData)
        {
            return Err(BindingFailure::SelectedInputAccounting);
        }
    }
    Ok(())
}

impl VerifiedSelectedRustClosure {
    pub(super) fn envelope(&self) -> &CompilerEvidenceEnvelopeV1 {
        &self.envelope
    }

    pub(super) fn artifacts(&self) -> &AssociatedCargoRecords {
        &self.artifacts
    }

    pub(super) fn graphs(&self) -> &DirectTargetGraphs {
        &self.graphs
    }

    pub(super) fn component_keys(&self) -> (&[String], &[String]) {
        (&self.adapter_components, &self.sanitizer_components)
    }

    pub(super) fn compiled_binding(&self) -> &super::CompiledBindingTranscript {
        &self.compiled_binding
    }

    pub(super) fn owner(&self) -> &SelectedOwner {
        &self.owner
    }

    pub(super) fn selected_bytes(&self, path: &str) -> Result<&[u8], BindingFailure> {
        self.table.bytes(path)
    }
}

pub(super) fn assert_final_closure_has_one_private_constructor() {
    let source = include_str!("source_binding_registry_selected_final_closure.rs");
    let syntax = syn::parse_file(source).unwrap();
    let declarations = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Struct(item) if item.ident == "VerifiedSelectedRustClosure" => Some(item),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(matches!(
        declarations.as_slice(),
        [declaration]
            if matches!(declaration.vis, syn::Visibility::Restricted(_))
                && declaration
                    .fields
                    .iter()
                    .all(|field| matches!(field.vis, syn::Visibility::Inherited))
    ));
    let constructors = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(function)
                if matches!(
                    &function.sig.output,
                    syn::ReturnType::Type(_, output)
                        if type_mentions_final(output)
                ) =>
            {
                Some(function.sig.ident.to_string())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        constructors,
        ["construct_verified_selected_rust_closure".to_string()]
    );
    let _constructor: fn(
        FinalClosureStages,
    ) -> Result<VerifiedSelectedRustClosure, BindingFailure> =
        construct_verified_selected_rust_closure;
    let _accessors = (
        VerifiedSelectedRustClosure::envelope,
        VerifiedSelectedRustClosure::artifacts,
        VerifiedSelectedRustClosure::graphs,
        VerifiedSelectedRustClosure::component_keys,
        VerifiedSelectedRustClosure::compiled_binding,
        VerifiedSelectedRustClosure::owner,
        VerifiedSelectedRustClosure::selected_bytes,
    );
}

fn type_mentions_final(ty: &syn::Type) -> bool {
    match ty {
        syn::Type::Path(path) => path.path.segments.iter().any(|segment| {
            segment.ident == "VerifiedSelectedRustClosure"
                || matches!(
                    &segment.arguments,
                    syn::PathArguments::AngleBracketed(arguments)
                        if arguments.args.iter().any(|argument| {
                            matches!(
                                argument,
                                syn::GenericArgument::Type(ty) if type_mentions_final(ty)
                            )
                        })
                )
        }),
        syn::Type::Tuple(tuple) => tuple.elems.iter().any(type_mentions_final),
        _ => false,
    }
}
