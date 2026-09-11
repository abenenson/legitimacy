use super::*;

const OWNER_ROOT: &str = "src/trajectory/codex_exec_v0/mod.rs";
const OWNER_PATH: &str = "src/trajectory/codex_exec_v0/publication_authority.rs";

pub(super) fn verify_registered_sensitive_type_surfaces(
    sources: &BTreeMap<String, String>,
) -> Result<(), &'static str> {
    verify_filesystem_handles(sources)?;
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
    if candidates != [OWNER_PATH]
        || reachable_count(sources, OWNER_ROOT, OWNER_PATH, &mut vec![]) != 1
    {
        return Err("capability-shape");
    }
    let source = sources.get(OWNER_PATH).ok_or("capability-shape")?;
    let syntax = syn::parse_file(source).map_err(|_| "capability-shape")?;
    verify_publication_entropy_and_reblinding(source)?;
    verify_fixed_test_route(sources)?;
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
        || callable.iter().any(|item| !item.starts_with(OWNER_PATH))
        || constructions
            != BTreeMap::from([
                ((OWNER_PATH.to_string(), "PublicationMintV0".to_string()), 1),
                (
                    (
                        OWNER_PATH.to_string(),
                        "ShareableSanitizedBundleV0".to_string(),
                    ),
                    1,
                ),
            ])
        || registered_method_call_count(sources, "into_publication_pair")? != 2
        || sources
            .values()
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

fn verify_fixed_test_route(sources: &BTreeMap<String, String>) -> Result<(), &'static str> {
    let source = sources
        .get("src/trajectory/codex_exec_v0/sanitizer.rs")
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

fn method_consumes_self(syntax: &syn::File, owner: &str, method: &str) -> bool {
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

fn verify_filesystem_handles(sources: &BTreeMap<String, String>) -> Result<(), &'static str> {
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

fn reachable_count(
    sources: &BTreeMap<String, String>,
    current: &str,
    target: &str,
    stack: &mut Vec<String>,
) -> usize {
    if stack.iter().any(|path| path == current) {
        return 0;
    }
    let Some(source) = sources.get(current) else {
        return 0;
    };
    let Ok(syntax) = syn::parse_file(source) else {
        return 0;
    };
    stack.push(current.to_string());
    let count = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Mod(module) if module.content.is_none() => {
                resolve_external_module(current, module)
            }
            _ => None,
        })
        .map(|path| usize::from(path == target) + reachable_count(sources, &path, target, stack))
        .sum();
    stack.pop();
    count
}

fn resolve_external_module(current: &str, module: &syn::ItemMod) -> Option<String> {
    let current_path = Path::new(current);
    let parent = current_path.parent()?;
    let explicit = module.attrs.iter().find_map(|attribute| {
        if !attribute.path().is_ident("path") {
            return None;
        }
        let syn::Meta::NameValue(value) = &attribute.meta else {
            return None;
        };
        let syn::Expr::Lit(expression) = &value.value else {
            return None;
        };
        let syn::Lit::Str(path) = &expression.lit else {
            return None;
        };
        Some(path.value())
    });
    if let Some(explicit) = explicit {
        return Some(relative(Path::new(""), &normalize(&parent.join(explicit))));
    }
    let base = if current_path.file_name()?.to_str()? == "mod.rs" {
        parent.to_path_buf()
    } else {
        parent.join(current_path.file_stem()?)
    };
    Some(relative(
        Path::new(""),
        &normalize(&base.join(format!("{}.rs", module.ident))),
    ))
}

pub(super) fn registered_sensitive_surface_mutants(
    sources: &BTreeMap<String, String>,
) -> Vec<(&'static str, BTreeMap<String, String>)> {
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
                OWNER_PATH,
                "    let derived_capture_nonce = NonceMaterialV0::capture_random()?;",
                "    let derived_capture_nonce = parent_authority.imported_nonce_material()?;",
            ),
        ),
        (
            "second publication entropy draw is bypassed",
            replace(
                OWNER_PATH,
                "    let publication_parent_reblinding_nonce = NonceMaterialV0::capture_random()?;",
                "    let publication_parent_reblinding_nonce = parent_authority.imported_nonce_material()?;",
            ),
        ),
        (
            "publication entropy roles reuse one draw",
            replace(
                OWNER_PATH,
                "    let publication_parent_reblinding_nonce = NonceMaterialV0::capture_random()?;",
                "    let publication_parent_reblinding_nonce = derived_capture_nonce;",
            ),
        ),
        (
            "publication entropy roles derive one from the other",
            replace(
                OWNER_PATH,
                "    let publication_parent_reblinding_nonce = NonceMaterialV0::capture_random()?;",
                "    let publication_parent_reblinding_nonce = derive_nonce(&derived_capture_nonce)?;",
            ),
        ),
        (
            "equal publication role material is accepted",
            replace(
                OWNER_PATH,
                "    if derived_capture_nonce.bytes() == publication_parent_reblinding_nonce.bytes() {\n        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::EntropyUnavailable));\n    }\n",
                "",
            ),
        ),
        (
            "publication mint is constructed before distinctness",
            replace(
                OWNER_PATH,
                "    if derived_capture_nonce.bytes() == publication_parent_reblinding_nonce.bytes() {\n        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::EntropyUnavailable));\n    }\n    let mint = PublicationMintV0 {\n        publication_parent_reblinding_nonce,\n    };",
                "    let mint = PublicationMintV0 {\n        publication_parent_reblinding_nonce,\n    };\n    if derived_capture_nonce.bytes() == mint.publication_parent_reblinding_nonce.bytes() {\n        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::EntropyUnavailable));\n    }",
            ),
        ),
        (
            "derived and reblinding entropy roles are swapped",
            replace(
                OWNER_PATH,
                "        derived_capture_nonce,\n    )?;",
                "        mint.publication_parent_reblinding_nonce,\n    )?;",
            ),
        ),
        (
            "fixed material enters production derived role",
            replace(
                OWNER_PATH,
                "    let derived_capture_nonce = NonceMaterialV0::capture_random()?;",
                "    let derived_capture_nonce = FixedSyntheticTestNonceV0::new([7; 32]).into_material();",
            ),
        ),
        (
            "fixed material enters production reblinding role",
            replace(
                OWNER_PATH,
                "    let publication_parent_reblinding_nonce = NonceMaterialV0::capture_random()?;",
                "    let publication_parent_reblinding_nonce = FixedSyntheticTestNonceV0::new([9; 32]).into_material();",
            ),
        ),
        (
            "publication parent commitment domain is substituted",
            replace(
                OWNER_PATH,
                "        PRIVATE_LINEAGE_COMMITMENT_DOMAIN_V0,",
                "        \"substituted-domain\",",
            ),
        ),
        (
            "original parent is omitted from reblinding frame",
            replace(
                OWNER_PATH,
                "            original_parent_receipt_commitment.as_bytes(),\n",
                "",
            ),
        ),
        (
            "reblinding nonce is omitted from reblinding frame",
            replace(
                OWNER_PATH,
                "            publication_parent_reblinding_nonce,\n",
                "",
            ),
        ),
        (
            "asserted evidence declaration is omitted from reblinding frame",
            replace(OWNER_PATH, "            asserted_origin.as_bytes(),\n", ""),
        ),
        (
            "downstream policy is omitted from reblinding frame",
            replace(
                OWNER_PATH,
                "            downstream_policy.identity.as_bytes(),\n",
                "",
            ),
        ),
        (
            "adapter is omitted from reblinding frame",
            replace(OWNER_PATH, "            adapter.identity.as_bytes(),\n", ""),
        ),
        (
            "schema is omitted from reblinding frame",
            replace(OWNER_PATH, "            schema.identity.as_bytes(),\n", ""),
        ),
        (
            "sanitizer policy is omitted from reblinding frame",
            replace(
                OWNER_PATH,
                "            sanitizer_policy.identity.as_bytes(),\n",
                "",
            ),
        ),
        (
            "sanitizer implementation is omitted from reblinding frame",
            replace(
                OWNER_PATH,
                "            sanitizer_implementation.identity.as_bytes(),\n",
                "",
            ),
        ),
        (
            "publication mint becomes cloneable",
            replace(
                OWNER_PATH,
                "struct PublicationMintV0 {",
                "#[derive(Clone)]\nstruct PublicationMintV0 {",
            ),
        ),
        (
            "publication mint field becomes visible",
            replace(
                OWNER_PATH,
                "    publication_parent_reblinding_nonce: NonceMaterialV0,",
                "    pub(super) publication_parent_reblinding_nonce: NonceMaterialV0,",
            ),
        ),
        (
            "transaction becomes cloneable",
            replace(
                OWNER_PATH,
                "pub struct ProductionSanitizationTransactionV0 {",
                "#[derive(Clone)]\npub struct ProductionSanitizationTransactionV0 {",
            ),
        ),
        (
            "bundle storage becomes serializable",
            replace(
                OWNER_PATH,
                "pub struct ShareableSanitizedBundleV0 {",
                "#[derive(serde::Serialize)]\npub struct ShareableSanitizedBundleV0 {",
            ),
        ),
        (
            "consuming transition becomes borrowed",
            replace(
                OWNER_PATH,
                "        self,\n    ) -> AdapterResultV0<(OwnerPrivateLineageSidecarV0, ShareableSanitizedBundleV0)> {",
                "        &self,\n    ) -> AdapterResultV0<(OwnerPrivateLineageSidecarV0, ShareableSanitizedBundleV0)> {",
            ),
        ),
        (
            "sibling obtains inferred mint factory result",
            append(
                OWNER_PATH,
                "\npub(super) fn inferred_publication_mint(mint: PublicationMintV0) -> impl Sized { mint }\n",
            ),
        ),
        (
            "bundle constructor is copied behind an owner macro",
            owner_macro_constructor_witness(sources),
        ),
        (
            "free function reconstructs bundle",
            append(
                OWNER_PATH,
                "\nfn reconstruct(bytes: Vec<u8>) -> ShareableSanitizedBundleV0 { ShareableSanitizedBundleV0 { bytes } }\n",
            ),
        ),
        (
            "const contains nested construction",
            append(
                OWNER_PATH,
                "\nconst EXTRA: () = { fn nested(bytes: Vec<u8>) -> ShareableSanitizedBundleV0 { ShareableSanitizedBundleV0 { bytes } } };\n",
            ),
        ),
        (
            "static adds authority surface",
            append(
                OWNER_PATH,
                "\nstatic EXTRA_AUTHORITY: Option<PublicationMintV0> = None;\n",
            ),
        ),
        (
            "async function accepts mint",
            append(
                OWNER_PATH,
                "\nasync fn retain_mint(mint: PublicationMintV0) { drop(mint); }\n",
            ),
        ),
        (
            "closure contains nested impl",
            append(
                OWNER_PATH,
                "\nfn install() { let _installer = || { impl ShareableSanitizedBundleV0 { fn repeated(&self) {} } }; }\n",
            ),
        ),
        (
            "trait exposes mint conversion",
            append(
                OWNER_PATH,
                "\ntrait MintConversion { fn convert(self) -> PublicationMintV0; }\n",
            ),
        ),
        (
            "type alias exposes mint",
            append(
                OWNER_PATH,
                "\ntype PublicationMintAlias = PublicationMintV0;\n",
            ),
        ),
        (
            "reexport exposes mint",
            append(
                OWNER_PATH,
                "\npub(super) use PublicationMintV0 as ExportedMint;\n",
            ),
        ),
        (
            "conversion consumes mint",
            append(
                OWNER_PATH,
                "\nimpl From<PublicationMintV0> for () { fn from(_: PublicationMintV0) -> Self {} }\n",
            ),
        ),
        (
            "owner gains external child",
            append(OWNER_PATH, "\nmod authority_child;\n"),
        ),
        (
            "owner gains path child",
            append(
                OWNER_PATH,
                "\n#[path = \"authority_child.rs\"] mod authority_child;\n",
            ),
        ),
        (
            "owner gains inline child",
            append(OWNER_PATH, "\nmod authority_child { use super::*; }\n"),
        ),
        (
            "owner includes another source",
            append(OWNER_PATH, "\ninclude!(\"authority_child.rs\");\n"),
        ),
        (
            "owner gains non-documentation attribute",
            replace(
                OWNER_PATH,
                "struct PublicationMintV0 {",
                "#[repr(C)]\nstruct PublicationMintV0 {",
            ),
        ),
        (
            "expected renderer returns authoritative bundle",
            replace(
                OWNER_PATH,
                "    publication_parent_reblinding_nonce: &[u8; 32],\n) -> AdapterResultV0<Vec<u8>> {\n    Ok(render_publication(",
                "    publication_parent_reblinding_nonce: &[u8; 32],\n) -> AdapterResultV0<ShareableSanitizedBundleV0> {\n    Ok(render_publication(",
            ),
        ),
        (
            "owner module is relocated through path override",
            replace(
                OWNER_ROOT,
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
    sources: &BTreeMap<String, String>,
) -> BTreeMap<String, String> {
    append_registered_source(
        sources,
        OWNER_PATH,
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

fn inherited_visibilities(fields: &BTreeMap<String, String>) -> BTreeMap<String, String> {
    fields
        .keys()
        .map(|field| (field.clone(), "inherited".to_string()))
        .collect()
}

fn item_visibility(syntax: &syn::File, name: &str) -> Option<&'static str> {
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

fn enum_variant_shapes(
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

pub(super) fn crate_edges(source: &str) -> BTreeSet<String> {
    source
        .match_indices("crate::")
        .map(|(offset, _)| {
            source[offset..]
                .chars()
                .take_while(|ch| ch.is_ascii_alphanumeric() || *ch == '_' || *ch == ':')
                .collect::<String>()
        })
        .map(|edge| {
            if edge.starts_with("crate::trajectory::codex_exec_v0") {
                "crate::trajectory::codex_exec_v0".to_string()
            } else if edge.starts_with("crate::trajectory::duplicate_json") {
                "crate::trajectory::duplicate_json".to_string()
            } else if edge.starts_with("crate::trajectory") {
                "crate::trajectory".to_string()
            } else if edge.starts_with("crate::LegitimacyError") {
                "crate::LegitimacyError".to_string()
            } else {
                edge
            }
        })
        .collect()
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
