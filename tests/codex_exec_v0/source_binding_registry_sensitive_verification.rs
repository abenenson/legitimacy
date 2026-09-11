use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SensitiveViolation {
    BorrowedConstruction,
    ExpansionAuthoritySurface,
    Shape,
}

pub(super) fn verify_selected_sensitive_type_surfaces(
    closure: &PortableSelectedRustClosure,
) -> Result<(), &'static str> {
    verify_selected_sensitive_type_surfaces_internal(closure).map_err(|_| "capability-shape")
}

pub(super) fn verify_selected_sensitive_type_surfaces_internal(
    closure: &PortableSelectedRustClosure,
) -> Result<(), SensitiveViolation> {
    let sources = closure
        .semantic_module_sources()
        .map_err(|_| SensitiveViolation::Shape)?;
    let owner_path = closure.owner_path();
    let source = closure
        .source(owner_path)
        .map_err(|_| SensitiveViolation::Shape)?;
    let syntax = syn::parse_file(source).map_err(|_| SensitiveViolation::Shape)?;
    if owner_has_borrowed_bundle_construction(&syntax) {
        return Err(SensitiveViolation::BorrowedConstruction);
    }
    if owner_has_expansion_surface(&syntax) {
        return Err(SensitiveViolation::ExpansionAuthoritySurface);
    }
    verify_selected_sensitive_shapes(closure, &sources, owner_path)
        .map_err(|_| SensitiveViolation::Shape)
}

fn verify_selected_sensitive_shapes(
    closure: &PortableSelectedRustClosure,
    sources: &BTreeMap<String, String>,
    owner_path: &str,
) -> Result<(), &'static str> {
    verify_compiled_attestation_role_binding(closure)?;
    verify_filesystem_handles(closure)?;
    let candidates = sources
        .iter()
        .filter_map(|(path, source)| {
            let syntax = syn::parse_file(source).ok()?;
            let names = syntax
                .items
                .iter()
                .filter_map(|item| match item {
                    syn::Item::Struct(item) => Some(normalize_rust_ident(&item.ident)),
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            (names.contains("PublicationMintV0") && names.contains("ShareableSanitizedBundleV0"))
                .then_some(path.as_str())
        })
        .collect::<Vec<_>>();
    if candidates != [owner_path] || closure.owner_incoming_count() != 1 {
        return Err("capability-shape");
    }
    let source = sources.get(owner_path).ok_or("capability-shape")?;
    let syntax = syn::parse_file(source).map_err(|_| "capability-shape")?;
    verify_publication_entropy_and_reblinding(source)?;
    verify_fixed_test_route(closure)?;
    let reexports = sensitive_reexport_surface(sources)?;
    let callable = callable_surface_for_types(
        sources,
        &["PublicationMintV0", "ShareableSanitizedBundleV0"],
    )?;
    let constructions = sensitive_struct_literal_counts(
        sources,
        &["PublicationMintV0", "ShareableSanitizedBundleV0"],
    )?;
    if authority_boundary_has_unreviewed_syntax(&syntax)
        || sensitive_impl_surface(sources)?.is_empty()
        || reexports
            .iter()
            .any(|item| item.contains("PublicationMintV0"))
        || callable.iter().any(|item| !item.starts_with(owner_path))
        || constructions
            != BTreeMap::from([
                ((owner_path.to_string(), "PublicationMintV0".to_string()), 1),
                (
                    (
                        owner_path.to_string(),
                        "ShareableSanitizedBundleV0".to_string(),
                    ),
                    1,
                ),
            ])
        || registered_method_call_count(sources, "into_publication_pair")? != 2
        || sources
            .values()
            .filter(|candidate| source_mentions_authority(candidate))
            .any(|candidate| source_has_sensitive_alias_or_fd_leak(candidate).unwrap_or(true))
        || owner_item_inventory(&syntax)
            != BTreeSet::from([
                "const:PRIVATE_LINEAGE_COMMITMENT_DOMAIN_V0".to_string(),
                "fn:has_expected_private_lineage_commitment:super".to_string(),
                "fn:private_lineage_commitment:inherited".to_string(),
                "fn:render_expected_publication_bytes:super".to_string(),
                "fn:render_publication:inherited".to_string(),
                "fn:sanitize_capture_v0:public".to_string(),
                "impl:ProductionSanitizationTransactionV0:inherent".to_string(),
                "impl:ProductionSanitizationTransactionV0:trait".to_string(),
                "impl:ShareableSanitizedBundleV0:inherent".to_string(),
                "impl:ShareableSanitizedBundleV0:trait".to_string(),
                "struct:ProductionSanitizationTransactionV0".to_string(),
                "struct:PublicationMintV0".to_string(),
                "struct:RenderedPublicationV0".to_string(),
                "struct:SanitizationBindingsV0".to_string(),
                "struct:ShareableSanitizedBundleV0".to_string(),
            ])
        || named_struct_fields(&syntax, "PublicationMintV0")
            != BTreeSet::from(["publication_parent_reblinding_nonce".to_string()])
        || named_struct_fields(&syntax, "ProductionSanitizationTransactionV0")
            != BTreeSet::from([
                "bindings".to_string(),
                "mint".to_string(),
                "sanitized".to_string(),
            ])
        || named_struct_fields(&syntax, "ShareableSanitizedBundleV0")
            != BTreeSet::from(["bytes".to_string()])
        || named_struct_shape(&syntax, "PublicationMintV0")
            != vec![(
                "publication_parent_reblinding_nonce".to_string(),
                "NonceMaterialV0".to_string(),
                "inherited",
            )]
        || item_visibility(&syntax, "PublicationMintV0") != Some("inherited")
        || item_visibility(&syntax, "ProductionSanitizationTransactionV0") != Some("public")
        || item_visibility(&syntax, "ShareableSanitizedBundleV0") != Some("public")
        || named_struct_has_derive(&syntax, "PublicationMintV0")
        || named_struct_has_derive(&syntax, "ProductionSanitizationTransactionV0")
        || named_struct_has_derive(&syntax, "ShareableSanitizedBundleV0")
        || named_struct_field_visibilities(&syntax, "PublicationMintV0")
            != inherited_visibilities(&named_struct_field_types(&syntax, "PublicationMintV0"))
        || named_struct_field_visibilities(&syntax, "ProductionSanitizationTransactionV0")
            != inherited_visibilities(&named_struct_field_types(
                &syntax,
                "ProductionSanitizationTransactionV0",
            ))
        || named_struct_field_visibilities(&syntax, "ShareableSanitizedBundleV0")
            != inherited_visibilities(&named_struct_field_types(
                &syntax,
                "ShareableSanitizedBundleV0",
            ))
        || public_inherent_method_names(&syntax, "ProductionSanitizationTransactionV0")
            != BTreeSet::from([
                "adapted".to_string(),
                "authority".to_string(),
                "derived_context".to_string(),
                "into_publication_pair".to_string(),
                "jsonl".to_string(),
                "private_receipt".to_string(),
            ])
        || public_inherent_method_names(&syntax, "ShareableSanitizedBundleV0")
            != BTreeSet::from(["into_bytes".to_string(), "to_json_line".to_string()])
        || !method_consumes_self(
            &syntax,
            "ProductionSanitizationTransactionV0",
            "into_publication_pair",
        )
        || !inherent_method_names(&syntax, "PublicationMintV0").is_empty()
        || implemented_trait_names(&syntax, "PublicationMintV0") != BTreeSet::new()
        || implemented_trait_names(&syntax, "ProductionSanitizationTransactionV0")
            != BTreeSet::from(["fmt::Debug".to_string()])
        || implemented_trait_names(&syntax, "ShareableSanitizedBundleV0")
            != BTreeSet::from(["fmt::Debug".to_string()])
        || source.matches("PublicationMintV0 {").count() != 2
        || !expected_renderer_returns_only_bytes(&syntax)
        || source.contains("to_shareable_sanitized_bundle")
        || source.contains("try_into_public_shareable")
        || source.contains("impl Clone")
        || source.contains("impl Copy")
        || source.contains("impl serde::Serialize")
    {
        return Err("capability-shape");
    }
    Ok(())
}

fn verify_compiled_attestation_role_binding(
    closure: &PortableSelectedRustClosure,
) -> Result<(), &'static str> {
    let required_roles = BTreeSet::from([
        SelectedInputRole::LibraryModule,
        SelectedInputRole::EmbeddedData,
    ]);
    let compiled_attestation = closure.sanitizer_components();
    if compiled_attestation
        .iter()
        .any(|component| closure.input_roles(component) != Some(&required_roles))
        || closure
            .module_files()
            .iter()
            .filter(|module| module.starts_with("src/trajectory/codex_exec_v0/"))
            .any(|module| {
                compiled_attestation
                    .iter()
                    .filter(|component| *component == module)
                    .count()
                    != 1
            })
    {
        return Err("capability-shape");
    }
    Ok(())
}

fn source_mentions_authority(source: &str) -> bool {
    [
        "PublicationMintV0",
        "ProductionSanitizationTransactionV0",
        "ShareableSanitizedBundleV0",
    ]
    .iter()
    .any(|name| source.contains(name))
}

pub(super) fn owner_has_borrowed_bundle_construction(syntax: &syn::File) -> bool {
    syntax.items.iter().any(|item| {
        let syn::Item::Impl(implementation) = item else {
            return false;
        };
        if type_shape(&implementation.self_ty) != "ShareableSanitizedBundleV0" {
            return false;
        }
        implementation.items.iter().any(|member| {
            let syn::ImplItem::Fn(function) = member else {
                return false;
            };
            let borrowed = matches!(
                function.sig.inputs.first(),
                Some(syn::FnArg::Receiver(receiver)) if receiver.reference.is_some()
            );
            let returns_bundle = matches!(
                &function.sig.output,
                syn::ReturnType::Type(_, output)
                    if matches!(type_shape(output).as_str(), "Self" | "ShareableSanitizedBundleV0")
            );
            borrowed && returns_bundle
        })
    })
}

pub(super) fn owner_has_expansion_surface(syntax: &syn::File) -> bool {
    syntax
        .items
        .iter()
        .any(|item| matches!(item, syn::Item::Macro(_)))
}

fn verify_publication_entropy_and_reblinding(source: &str) -> Result<(), &'static str> {
    if direct_call_argument_profiles(source, "NonceMaterialV0::capture_random")
        .map_err(|_| "capability-shape")?
        != vec![Vec::<String>::new(), Vec::<String>::new()]
    {
        return Err("capability-shape");
    }
    let compact = compact_source(source);
    ordered_unique_fragments(
        &compact,
        &[
            "letderived_capture_nonce=NonceMaterialV0::capture_random()?;",
            "letpublication_parent_reblinding_nonce=NonceMaterialV0::capture_random()?;",
            "ifderived_capture_nonce.bytes()==publication_parent_reblinding_nonce.bytes(){",
            "letmint=PublicationMintV0{publication_parent_reblinding_nonce,};",
            "letsanitized=sanitize_capture_with_nonce_v0(parent_jsonl,parent_authority,parent_trusted_context,derived_capture_nonce,)?;",
            "ProductionSanitizationTransactionV0::new(parent_authority,parent_trusted_context,sanitized,mint,)",
        ],
    )
    .map_err(|_| "capability-shape")?;
    if direct_call_argument_profiles(source, "framed_sha256").map_err(|_| "capability-shape")?
        != vec![compact_profile(&[
            "PRIVATE_LINEAGE_COMMITMENT_DOMAIN_V0",
            "&[b\"version=0\", original_parent_receipt_commitment.as_bytes(), publication_parent_reblinding_nonce, asserted_origin.as_bytes(), asserted_parent.label().as_bytes(), asserted_derived_nonce_source.label().as_bytes(), downstream_policy.identity.as_bytes(), downstream_policy.version.as_bytes(), downstream_policy.hash.as_bytes(), adapter.identity.as_bytes(), adapter.version.as_bytes(), adapter.hash.as_bytes(), schema.identity.as_bytes(), schema.version.as_bytes(), schema.hash.as_bytes(), sanitizer_policy.identity.as_bytes(), sanitizer_policy.version.as_bytes(), sanitizer_policy.hash.as_bytes(), sanitizer_implementation.identity.as_bytes(), sanitizer_implementation.version.as_bytes(), sanitizer_implementation.hash.as_bytes(),]",
        ])]
    {
        return Err("capability-shape");
    }
    Ok(())
}

fn verify_fixed_test_route(closure: &PortableSelectedRustClosure) -> Result<(), &'static str> {
    let source = closure
        .module_files()
        .iter()
        .filter_map(|path| closure.source(path).ok())
        .find(|source| source.contains("struct FixedTestSanitizationMaterialV0"))
        .ok_or("capability-shape")?;
    let syntax = syn::parse_file(source).map_err(|_| "capability-shape")?;
    if named_struct_shape(&syntax, "FixedTestSanitizationMaterialV0")
        != vec![
            (
                "derived_capture_nonce".to_string(),
                "FixedSyntheticTestNonceV0".to_string(),
                "inherited",
            ),
            (
                "publication_parent_reblinding_nonce".to_string(),
                "FixedSyntheticTestNonceV0".to_string(),
                "inherited",
            ),
        ]
        || named_struct_fields(&syntax, "FixedTestSanitizedCaptureV0")
            != BTreeSet::from(["sanitized".to_string()])
        || source
            .matches("material.derived_capture_nonce.into_material()")
            .count()
            != 1
        || source
            .matches("material.publication_parent_reblinding_nonce.bytes()")
            .count()
            != 1
        || source.contains("PublicationMintV0")
        || source.contains("ShareableSanitizedBundleV0")
        || source.contains("ProductionSanitizationTransactionV0")
        || source.contains("into_publication_pair")
    {
        return Err("capability-shape");
    }
    Ok(())
}

pub(super) fn method_consumes_self(syntax: &syn::File, owner: &str, method: &str) -> bool {
    syntax.items.iter().any(|item| {
        let syn::Item::Impl(implementation) = item else {
            return false;
        };
        if implementation.trait_.is_some() || type_shape(&implementation.self_ty) != owner {
            return false;
        }
        implementation.items.iter().any(|member| {
            let syn::ImplItem::Fn(function) = member else {
                return false;
            };
            function.sig.ident == method
                && matches!(
                    function.sig.inputs.first(),
                    Some(syn::FnArg::Receiver(receiver))
                        if receiver.reference.is_none() && receiver.mutability.is_none()
                )
        })
    })
}

fn verify_filesystem_handles(closure: &PortableSelectedRustClosure) -> Result<(), &'static str> {
    let sources = closure.semantic_module_sources()?;
    let output = syn::parse_file(
        sources
            .get("cli/trajectory/linux_output.rs")
            .ok_or("capability-shape")?,
    )
    .map_err(|_| "capability-shape")?;
    let transaction = syn::parse_file(
        sources
            .get("cli/trajectory/linux_output_transaction.rs")
            .ok_or("capability-shape")?,
    )
    .map_err(|_| "capability-shape")?;
    let path = syn::parse_file(
        sources
            .get("cli/trajectory/linux_path.rs")
            .ok_or("capability-shape")?,
    )
    .map_err(|_| "capability-shape")?;
    if named_struct_fields(&path, "SnapshotV0")
        != BTreeSet::from([
            "baseline".to_string(),
            "bytes".to_string(),
            "dev".to_string(),
            "expected_len".to_string(),
            "expected_sha256".to_string(),
            "ino".to_string(),
            "mode".to_string(),
            "reader".to_string(),
            "uid".to_string(),
        ])
        || named_struct_has_derive(&path, "SnapshotV0")
        || named_struct_field_visibilities(&path, "SnapshotV0").get("reader")
            != Some(&"inherited".to_string())
        || named_struct_has_derive(&output, "PreparedPublicationV0")
        || named_struct_has_derive(&output, "CommittedPublicationV0")
        || named_struct_has_derive(&output, "CommitFailureV0")
        || named_struct_field_visibilities(&output, "CommittedPublicationV0").get("held")
            != Some(&"inherited".to_string())
        || named_struct_field_types(&output, "CommittedPublicationV0").get("held")
            != Some(&"OwnedFd".to_string())
        || enum_variant_shapes(&output, "CommitFailureV0")
            .get("PostLink")
            .and_then(|fields| fields.get("committed"))
            != Some(&"Box<CommittedPublicationV0>".to_string())
        || named_struct_fields(&transaction, "PublicationSpecV0")
            != BTreeSet::from(["bytes".to_string(), "output".to_string()])
        || item_derive_names(&transaction, "PublicationSpecV0")
            != BTreeSet::from(["Clone".to_string(), "Copy".to_string()])
        || named_struct_fields(&transaction, "RelativeSetFailureV0")
            != BTreeSet::from(["committed".to_string(), "error".to_string()])
        || named_struct_field_types(&transaction, "RelativeSetFailureV0").get("committed")
            != Some(&"Vec<CommittedPublicationV0>".to_string())
        || named_struct_has_derive(&transaction, "RelativeSetFailureV0")
    {
        return Err("capability-shape");
    }
    Ok(())
}

fn expected_renderer_returns_only_bytes(syntax: &syn::File) -> bool {
    syntax.items.iter().any(|item| {
        let syn::Item::Fn(function) = item else {
            return false;
        };
        if function.sig.ident != "render_expected_publication_bytes" {
            return false;
        }
        matches!(
            &function.sig.output,
            syn::ReturnType::Type(_, output)
                if type_shape(output) == "AdapterResultV0<Vec<u8>>"
        )
    })
}

fn owner_item_inventory(syntax: &syn::File) -> BTreeSet<String> {
    syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Use(_) => None,
            syn::Item::Const(item) => Some(format!("const:{}", item.ident)),
            syn::Item::Struct(item) => Some(format!("struct:{}", item.ident)),
            syn::Item::Fn(item) => Some(format!(
                "fn:{}:{}",
                item.sig.ident,
                visibility_shape(&item.vis)
            )),
            syn::Item::Impl(item) => {
                let target = type_shape(&item.self_ty);
                Some(format!(
                    "impl:{target}:{}",
                    if item.trait_.is_some() {
                        "trait"
                    } else {
                        "inherent"
                    }
                ))
            }
            _ => Some("forbidden".to_string()),
        })
        .collect()
}

pub(super) fn registered_sensitive_surface_mutants(
    closure: &PortableSelectedRustClosure,
    sources: &BTreeMap<String, String>,
) -> Vec<(&'static str, BTreeMap<String, String>)> {
    let owner_path = closure.owner_path();
    let owner_parent = closure.owner_parent();
    let replace = |path, before, after| {
        mutate_registered_source(sources, path, |source| {
            replace_exact_once(source, before, after)
        })
    };
    let append = |path, suffix| append_registered_source(sources, path, suffix);
    vec![
        (
            "first publication entropy draw is bypassed",
            replace(
                owner_path,
                "    let derived_capture_nonce = NonceMaterialV0::capture_random()?;",
                "    let derived_capture_nonce = parent_authority.imported_nonce_material()?;",
            ),
        ),
        (
            "second publication entropy draw is bypassed",
            replace(
                owner_path,
                "    let publication_parent_reblinding_nonce = NonceMaterialV0::capture_random()?;",
                "    let publication_parent_reblinding_nonce = parent_authority.imported_nonce_material()?;",
            ),
        ),
        (
            "publication entropy roles reuse one draw",
            replace(
                owner_path,
                "    let publication_parent_reblinding_nonce = NonceMaterialV0::capture_random()?;",
                "    let publication_parent_reblinding_nonce = derived_capture_nonce;",
            ),
        ),
        (
            "publication entropy roles derive one from the other",
            replace(
                owner_path,
                "    let publication_parent_reblinding_nonce = NonceMaterialV0::capture_random()?;",
                "    let publication_parent_reblinding_nonce = derive_nonce(&derived_capture_nonce)?;",
            ),
        ),
        (
            "equal publication role material is accepted",
            replace(
                owner_path,
                "    if derived_capture_nonce.bytes() == publication_parent_reblinding_nonce.bytes() {\n        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::EntropyUnavailable));\n    }\n",
                "",
            ),
        ),
        (
            "publication mint is constructed before distinctness",
            replace(
                owner_path,
                "    if derived_capture_nonce.bytes() == publication_parent_reblinding_nonce.bytes() {\n        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::EntropyUnavailable));\n    }\n    let mint = PublicationMintV0 {\n        publication_parent_reblinding_nonce,\n    };",
                "    let mint = PublicationMintV0 {\n        publication_parent_reblinding_nonce,\n    };\n    if derived_capture_nonce.bytes() == mint.publication_parent_reblinding_nonce.bytes() {\n        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::EntropyUnavailable));\n    }",
            ),
        ),
        (
            "derived and reblinding entropy roles are swapped",
            replace(
                owner_path,
                "        derived_capture_nonce,\n    )?;",
                "        mint.publication_parent_reblinding_nonce,\n    )?;",
            ),
        ),
        (
            "fixed material enters production derived role",
            replace(
                owner_path,
                "    let derived_capture_nonce = NonceMaterialV0::capture_random()?;",
                "    let derived_capture_nonce = FixedSyntheticTestNonceV0::new([7; 32]).into_material();",
            ),
        ),
        (
            "fixed material enters production reblinding role",
            replace(
                owner_path,
                "    let publication_parent_reblinding_nonce = NonceMaterialV0::capture_random()?;",
                "    let publication_parent_reblinding_nonce = FixedSyntheticTestNonceV0::new([9; 32]).into_material();",
            ),
        ),
        (
            "publication parent commitment domain is substituted",
            replace(
                owner_path,
                "        PRIVATE_LINEAGE_COMMITMENT_DOMAIN_V0,",
                "        \"substituted-domain\",",
            ),
        ),
        (
            "original parent is omitted from reblinding frame",
            replace(
                owner_path,
                "            original_parent_receipt_commitment.as_bytes(),\n",
                "",
            ),
        ),
        (
            "reblinding nonce is omitted from reblinding frame",
            replace(
                owner_path,
                "            publication_parent_reblinding_nonce,\n",
                "",
            ),
        ),
        (
            "asserted evidence declaration is omitted from reblinding frame",
            replace(owner_path, "            asserted_origin.as_bytes(),\n", ""),
        ),
        (
            "downstream policy is omitted from reblinding frame",
            replace(
                owner_path,
                "            downstream_policy.identity.as_bytes(),\n",
                "",
            ),
        ),
        (
            "adapter is omitted from reblinding frame",
            replace(owner_path, "            adapter.identity.as_bytes(),\n", ""),
        ),
        (
            "schema is omitted from reblinding frame",
            replace(owner_path, "            schema.identity.as_bytes(),\n", ""),
        ),
        (
            "sanitizer policy is omitted from reblinding frame",
            replace(
                owner_path,
                "            sanitizer_policy.identity.as_bytes(),\n",
                "",
            ),
        ),
        (
            "sanitizer implementation is omitted from reblinding frame",
            replace(
                owner_path,
                "            sanitizer_implementation.identity.as_bytes(),\n",
                "",
            ),
        ),
        (
            "publication mint becomes cloneable",
            replace(
                owner_path,
                "struct PublicationMintV0 {",
                "#[derive(Clone)]\nstruct PublicationMintV0 {",
            ),
        ),
        (
            "publication mint field becomes visible",
            replace(
                owner_path,
                "    publication_parent_reblinding_nonce: NonceMaterialV0,",
                "    pub(super) publication_parent_reblinding_nonce: NonceMaterialV0,",
            ),
        ),
        (
            "transaction becomes cloneable",
            replace(
                owner_path,
                "pub struct ProductionSanitizationTransactionV0 {",
                "#[derive(Clone)]\npub struct ProductionSanitizationTransactionV0 {",
            ),
        ),
        (
            "bundle storage becomes serializable",
            replace(
                owner_path,
                "pub struct ShareableSanitizedBundleV0 {",
                "#[derive(serde::Serialize)]\npub struct ShareableSanitizedBundleV0 {",
            ),
        ),
        (
            "consuming transition becomes borrowed",
            replace(
                owner_path,
                "        self,\n    ) -> AdapterResultV0<(OwnerPrivateLineageSidecarV0, ShareableSanitizedBundleV0)> {",
                "        &self,\n    ) -> AdapterResultV0<(OwnerPrivateLineageSidecarV0, ShareableSanitizedBundleV0)> {",
            ),
        ),
        (
            "sibling obtains inferred mint factory result",
            append(
                owner_path,
                "\npub(super) fn inferred_publication_mint(mint: PublicationMintV0) -> impl Sized { mint }\n",
            ),
        ),
        (
            "bundle constructor is copied behind an owner macro",
            owner_macro_constructor_witness(closure, sources),
        ),
        (
            "free function reconstructs bundle",
            append(
                owner_path,
                "\nfn reconstruct(bytes: Vec<u8>) -> ShareableSanitizedBundleV0 { ShareableSanitizedBundleV0 { bytes } }\n",
            ),
        ),
        (
            "const contains nested construction",
            append(
                owner_path,
                "\nconst EXTRA: () = { fn nested(bytes: Vec<u8>) -> ShareableSanitizedBundleV0 { ShareableSanitizedBundleV0 { bytes } } };\n",
            ),
        ),
        (
            "static adds authority surface",
            append(
                owner_path,
                "\nstatic EXTRA_AUTHORITY: Option<PublicationMintV0> = None;\n",
            ),
        ),
        (
            "async function accepts mint",
            append(
                owner_path,
                "\nasync fn retain_mint(mint: PublicationMintV0) { drop(mint); }\n",
            ),
        ),
        (
            "closure contains nested impl",
            append(
                owner_path,
                "\nfn install() { let _installer = || { impl ShareableSanitizedBundleV0 { fn repeated(&self) {} } }; }\n",
            ),
        ),
        (
            "trait exposes mint conversion",
            append(
                owner_path,
                "\ntrait MintConversion { fn convert(self) -> PublicationMintV0; }\n",
            ),
        ),
        (
            "type alias exposes mint",
            append(
                owner_path,
                "\ntype PublicationMintAlias = PublicationMintV0;\n",
            ),
        ),
        (
            "reexport exposes mint",
            append(
                owner_path,
                "\npub(super) use PublicationMintV0 as ExportedMint;\n",
            ),
        ),
        (
            "conversion consumes mint",
            append(
                owner_path,
                "\nimpl From<PublicationMintV0> for () { fn from(_: PublicationMintV0) -> Self {} }\n",
            ),
        ),
        (
            "owner gains external child",
            append(owner_path, "\nmod authority_child;\n"),
        ),
        (
            "owner gains path child",
            append(
                owner_path,
                "\n#[path = \"authority_child.rs\"] mod authority_child;\n",
            ),
        ),
        (
            "owner gains inline child",
            append(owner_path, "\nmod authority_child { use super::*; }\n"),
        ),
        (
            "owner includes another source",
            append(owner_path, "\ninclude!(\"authority_child.rs\");\n"),
        ),
        (
            "owner gains non-documentation attribute",
            replace(
                owner_path,
                "struct PublicationMintV0 {",
                "#[repr(C)]\nstruct PublicationMintV0 {",
            ),
        ),
        (
            "expected renderer returns authoritative bundle",
            replace(
                owner_path,
                "    _context: &TrustedAdaptationContextV0,\n) -> AdapterResultV0<Vec<u8>> {",
                "    _context: &TrustedAdaptationContextV0,\n) -> AdapterResultV0<ShareableSanitizedBundleV0> {",
            ),
        ),
        (
            "owner module is relocated through path override",
            replace(
                owner_parent,
                "mod publication_authority;",
                "#[path = \"relocated_publication_authority.rs\"]\nmod publication_authority;",
            ),
        ),
        (
            "unreachable second owner is omitted from graph derivation",
            {
                let mut mutation = sources.clone();
                mutation.insert(
                    "src/trajectory/codex_exec_v0/omitted_owner.rs".to_string(),
                    "struct PublicationMintV0; struct ShareableSanitizedBundleV0 { bytes: Vec<u8> }\n"
                        .to_string(),
                );
                mutation
            },
        ),
        (
            "prepared handle becomes cloneable",
            replace(
                "cli/trajectory/linux_output.rs",
                "pub(crate) struct PreparedPublicationV0 {",
                "#[derive(Clone)]\npub(crate) struct PreparedPublicationV0 {",
            ),
        ),
        (
            "committed descriptor becomes visible",
            replace(
                "cli/trajectory/linux_output.rs",
                "    held: OwnedFd,",
                "    pub held: OwnedFd,",
            ),
        ),
        (
            "committed descriptor becomes raw integer",
            replace(
                "cli/trajectory/linux_output.rs",
                "    held: OwnedFd,",
                "    held: i32,",
            ),
        ),
        (
            "post-link handle loses unique box",
            replace(
                "cli/trajectory/linux_output.rs",
                "        committed: Box<CommittedPublicationV0>,",
                "        committed: CommittedPublicationV0,",
            ),
        ),
        (
            "input snapshot becomes cloneable",
            replace(
                "cli/trajectory/linux_path.rs",
                "pub(crate) struct SnapshotV0 {",
                "#[derive(Clone)]\npub(crate) struct SnapshotV0 {",
            ),
        ),
    ]
}

pub(super) fn owner_macro_constructor_witness(
    closure: &PortableSelectedRustClosure,
    sources: &BTreeMap<String, String>,
) -> BTreeMap<String, String> {
    let owner_path = closure.owner_path();
    append_registered_source(
        sources,
        owner_path,
        "\nmacro_rules! repeat_bundle { () => { impl ShareableSanitizedBundleV0 { pub fn repeated(&self) -> Self { Self { bytes: self.bytes.clone() } } } } }\nrepeat_bundle!();\n",
    )
}

fn mutate_registered_source(
    sources: &BTreeMap<String, String>,
    path: &str,
    mutate: impl FnOnce(&str) -> String,
) -> BTreeMap<String, String> {
    let mut mutation = sources.clone();
    let source = mutation.get(path).unwrap();
    let changed = mutate(source);
    assert_source_mutant(path, source, &changed);
    mutation.insert(path.to_string(), changed);
    mutation
}

fn append_registered_source(
    sources: &BTreeMap<String, String>,
    path: &str,
    suffix: &str,
) -> BTreeMap<String, String> {
    mutate_registered_source(sources, path, |source| format!("{source}{suffix}"))
}
