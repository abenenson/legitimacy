use super::*;

fn fixture_tree() -> SyntheticSelectedTree<Bound> {
    let bytes = b"component-v1".to_vec();
    let digest: [u8; 32] = Sha256::digest(&bytes).into();
    let table = SelectedByteRoleTable::new(BTreeMap::from([(
        "src/component.data".to_string(),
        (bytes, BTreeSet::from([SelectedRole::LibraryModule])),
    )]))
    .unwrap();
    let component = CompiledComponentObservation {
        index: 0,
        path: "src/component.data".to_string(),
        byte_length: 12,
        digest,
    };
    let compiled = CompiledBindingTranscript {
        schema_identity: ATTESTATION_IDENTITY.to_string(),
        schema_version: 0,
        components: vec![component.clone()],
        aggregate_identity: SANITIZER_AGGREGATE_IDENTITY.to_string(),
        aggregate_version: SANITIZER_AGGREGATE_VERSION.to_string(),
        aggregate_hash: aggregate_hash(&[component], &table).unwrap(),
        rlib: RlibIdentity {
            canonical_path: "/target/liblegitimacy.rlib".to_string(),
            device: 1,
            inode: 2,
            byte_length: 3,
            digest: [4; 32],
        },
    };
    SyntheticSelectedTree {
        state: Bound {
            compiled,
            envelope_digest: [5; 32],
            table_digest: table.digest(),
        },
        table,
        marker: PhantomData,
    }
}

pub(super) fn assert_stale_compiled_binding_policy_only_fails_at_binding_comparison() {
    assert_binding_protocol_fixtures();
    let clean = fixture_tree();
    let stale = clean.compiled().clone();
    let unbound = clean
        .refresh_component_bytes(0, "src/component.data", b"component-v2".to_vec())
        .unwrap();
    assert_eq!(
        preserve_stale_compiled_sanitizer_binding_for_rejection_witness(&unbound.table, &stale),
        BindingFailure::SanitizerBindingMismatch
    );
    assert_eq!(unbound.edits().len(), 1);
    let ordered_stage = BindingFailure::StaleCompilerEvidence;
    assert!(matches!(
        ordered_stage,
        BindingFailure::StaleCompilerEvidence
    ));
}

pub(super) fn assert_unbound_synthetic_tree_has_no_final_constructor() {
    super::final_closure::assert_final_closure_has_one_private_constructor();
    let bound = fixture_tree();
    assert_eq!(bound.table().keys().count(), 1);
    assert_eq!(bound.table().roles("src/component.data").unwrap().len(), 1);
    assert_eq!(bound.envelope_digest(), [5; 32]);
    assert_eq!(bound.state.table_digest, bound.table().digest());
    let unbound = bound
        .refresh_component_bytes(0, "src/component.data", b"component-v2".to_vec())
        .unwrap();
    let refreshed = CompiledBindingTranscript {
        components: unbound.state.transformed.clone(),
        aggregate_hash: aggregate_hash(&unbound.state.transformed, &unbound.table).unwrap(),
        ..unbound.state.prior.clone()
    };
    let table_digest = unbound.table.digest();
    let rebound = unbound
        .bind_after_complete_compile_and_probe(refreshed, [6; 32], table_digest)
        .unwrap();
    assert_eq!(rebound.envelope_digest(), [6; 32]);

    let edited = fixture_tree()
        .refresh_component_bytes(0, "src/component.data", b"component-v2".to_vec())
        .unwrap()
        .refresh_component_bytes(0, "src/component.data", b"component-v3".to_vec())
        .unwrap()
        .replace_component(
            0,
            "src/component.data",
            "src/replacement.data".to_string(),
            b"replacement".to_vec(),
            BTreeSet::from([SelectedRole::BinaryModule]),
        )
        .unwrap()
        .insert_component(
            1,
            "contracts/canonical.data".to_string(),
            b"canonical".to_vec(),
            BTreeSet::from([SelectedRole::CanonicalObject]),
        )
        .unwrap()
        .remove_component(1, "contracts/canonical.data")
        .unwrap();
    assert_eq!(edited.edits().len(), 5);

    let source = include_str!("source_binding_registry_selected_binding.rs");
    let syntax = syn::parse_file(source).unwrap();
    let unbound_impls = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Impl(item)
                if matches!(
                    item.self_ty.as_ref(),
                    syn::Type::Path(path)
                        if path.path.segments.last().is_some_and(|segment| {
                            segment.ident == "SyntheticSelectedTree"
                                && argument_names(&segment.arguments).contains("Unbound")
                        })
                ) =>
            {
                Some(item)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(unbound_impls.len(), 1);
    assert!(unbound_impls[0].items.iter().all(|member| {
        !matches!(
            member,
            syn::ImplItem::Fn(function)
                if matches!(
                    &function.sig.output,
                    syn::ReturnType::Type(_, ty) if render_type_mentions_final(ty)
                )
        )
    }));
}

fn assert_binding_protocol_fixtures() {
    let fixture = fixture_tree();
    let encoded = encode_probe_fixture(fixture.compiled());
    assert_eq!(
        parse_probe_record(&encoded).unwrap(),
        fixture.compiled().clone()
    );
    let mut trailing = encoded;
    trailing.push(0);
    assert_eq!(
        parse_probe_record(&trailing),
        Err(BindingFailure::RlibProbe)
    );

    let binding_source = b"const ADAPTER_CORE_SOURCES_V0: &[(&str, &[u8])] = &[(\"src/a.data\", include_bytes!(\"a.data\"))];\n\
const SANITIZER_ONLY_SOURCES_V0: &[(&str, &[u8])] = &[(\"src/b.data\", include_bytes!(\"b.data\"))];\n"
        .to_vec();
    let table = SelectedByteRoleTable::new(BTreeMap::from([
        (
            "src/bindings.fixture".to_string(),
            (
                binding_source,
                BTreeSet::from([SelectedRole::LibraryModule]),
            ),
        ),
        (
            "src/a.data".to_string(),
            (b"a".to_vec(), BTreeSet::from([SelectedRole::LibraryModule])),
        ),
        (
            "src/b.data".to_string(),
            (b"b".to_vec(), BTreeSet::from([SelectedRole::EmbeddedData])),
        ),
        (
            "cli/main.fixture".to_string(),
            (
                b"fn main() {}\n".to_vec(),
                BTreeSet::from([SelectedRole::BinaryModule]),
            ),
        ),
        (
            "contracts/canonical.fixture".to_string(),
            (
                b"{}".to_vec(),
                BTreeSet::from([SelectedRole::CanonicalObject]),
            ),
        ),
    ]))
    .unwrap();
    let registry = registry_transcript("src/bindings.fixture", &table).unwrap();
    assert_eq!(
        registry
            .iter()
            .map(|component| component.path.as_str())
            .collect::<Vec<_>>(),
        ["src/a.data", "src/b.data"]
    );
}

fn encode_probe_fixture(transcript: &CompiledBindingTranscript) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(PROBE_MAGIC);
    bytes.extend_from_slice(&1u16.to_be_bytes());
    encode_frame(&mut bytes, transcript.schema_identity.as_bytes());
    bytes.extend_from_slice(&transcript.schema_version.to_be_bytes());
    bytes.extend_from_slice(&(transcript.components.len() as u32).to_be_bytes());
    for component in &transcript.components {
        bytes.extend_from_slice(&component.index.to_be_bytes());
        encode_frame(&mut bytes, component.path.as_bytes());
        bytes.extend_from_slice(&component.byte_length.to_be_bytes());
        bytes.extend_from_slice(&component.digest);
    }
    encode_frame(&mut bytes, transcript.aggregate_identity.as_bytes());
    encode_frame(&mut bytes, transcript.aggregate_version.as_bytes());
    encode_frame(&mut bytes, transcript.aggregate_hash.as_bytes());
    encode_frame(&mut bytes, transcript.rlib.canonical_path.as_bytes());
    bytes.extend_from_slice(&transcript.rlib.device.to_be_bytes());
    bytes.extend_from_slice(&transcript.rlib.inode.to_be_bytes());
    bytes.extend_from_slice(&transcript.rlib.byte_length.to_be_bytes());
    bytes.extend_from_slice(&transcript.rlib.digest);
    bytes
}

fn encode_frame(output: &mut Vec<u8>, bytes: &[u8]) {
    output.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
    output.extend_from_slice(bytes);
}

fn argument_names(arguments: &syn::PathArguments) -> BTreeSet<String> {
    match arguments {
        syn::PathArguments::AngleBracketed(arguments) => arguments
            .args
            .iter()
            .filter_map(|argument| match argument {
                syn::GenericArgument::Type(syn::Type::Path(path)) => path
                    .path
                    .segments
                    .last()
                    .map(|segment| segment.ident.to_string()),
                _ => None,
            })
            .collect(),
        _ => BTreeSet::new(),
    }
}

fn render_type_mentions_final(ty: &syn::Type) -> bool {
    match ty {
        syn::Type::Path(path) => path
            .path
            .segments
            .iter()
            .any(|segment| segment.ident == "VerifiedSelectedRustClosure"),
        syn::Type::Tuple(tuple) => tuple.elems.iter().any(render_type_mentions_final),
        _ => false,
    }
}
