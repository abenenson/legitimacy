use super::*;

pub(super) fn verify_transaction_pair_order_against_canonical(
    source: &str,
) -> Result<(), &'static str> {
    let build = canonical_build_input();
    let fact = build["normative_contract"]["facts"]
        .as_array()
        .and_then(|facts| facts.iter().find(|fact| fact["id"] == "pair-order"))
        .ok_or("route-shape")?;
    let precondition = fact["precondition"].as_str().ok_or("route-shape")?;
    let phases = fact["phases"]
        .as_array()
        .ok_or("route-shape")?
        .iter()
        .map(|phase| phase.as_str().map(str::to_string).ok_or("route-shape"))
        .collect::<Result<Vec<_>, _>>()?;
    let extracted = extract_transaction_pair_order(source)?;
    if extracted.precondition != precondition || extracted.phases != phases {
        return Err("route-shape");
    }
    Ok(())
}

pub(super) struct ExtractedPairOrder {
    pub(super) precondition: String,
    pub(super) phases: Vec<String>,
}

pub(super) fn extract_transaction_pair_order(
    source: &str,
) -> Result<ExtractedPairOrder, &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "route-shape")?;
    if !function_starts_with_unconditional_try_call(
        &syntax,
        "publish_pair_with_hooks",
        "semantic_pair",
    ) {
        return Err("route-shape");
    }
    let compact = compact_source(source);
    let alias_check = compact
        .find("sidecar_prepared.reject_cross_output_alias(&public_prepared)?;")
        .ok_or("route-shape")?;
    let mut events = [
        (
            compact
                .find("letsidecar_prepared=prepare_with_hooks(")
                .ok_or("route-shape")?,
            vec!["prepare-owner-private-sidecar".to_string()],
        ),
        (
            compact
                .find("letpublic_prepared=prepare_with_hooks(")
                .ok_or("route-shape")?,
            vec!["prepare-public-output".to_string()],
        ),
        (
            compact
                .find("letsidecar=matchcommit_with_hooks(")
                .ok_or("route-shape")?,
            vec!["link-owner-private-sidecar".to_string()],
        ),
        (
            compact
                .find("letpublic_result=commit_with_hooks(")
                .ok_or("route-shape")?,
            vec![
                "revalidate-committed-sidecar-immediately-before-public-link".to_string(),
                "link-public-output".to_string(),
            ],
        ),
        (
            compact
                .find("Ok(public)=>{letsidecar_error=revalidate_committed(")
                .ok_or("route-shape")?,
            vec!["revalidate-sidecar-and-public-output".to_string()],
        ),
    ];
    let preparation_end = events[0].0.max(events[1].0);
    if alias_check <= preparation_end || alias_check >= events[2].0 {
        return Err("route-shape");
    }
    events.sort_by_key(|(offset, _)| *offset);
    Ok(ExtractedPairOrder {
        precondition: "validate-semantic-pair".to_string(),
        phases: events.into_iter().flat_map(|(_, phases)| phases).collect(),
    })
}

pub(super) fn verify_linux_output_forbidden_shortcuts(source: &str) -> Result<(), &'static str> {
    syn::parse_file(source).map_err(|_| "route-shape")?;
    for forbidden in [
        "OFlags::EXCL",
        "AtFlags::EMPTY_PATH",
        ".legitimacy-tmp-",
        "create_new(",
        "OpenOptions::new(",
        "File::open(",
        "std::fs::hard_link(",
        "std::fs::rename(",
        "std::fs::remove_file(",
        "renameat(",
        "libc::",
        "unsafe {",
        "unsafe fn",
    ] {
        if source.contains(forbidden) {
            return Err("route-shape");
        }
    }
    let mut parser = rust_parser();
    let tree = parser.parse(source, None).ok_or("route-shape")?;
    if tree.root_node().has_error() {
        return Err("route-shape");
    }
    let calls = call_name_counts(tree.root_node(), source.as_bytes());
    if ["macro:include", "macro:include_bytes", "macro:include_str"]
        .iter()
        .any(|name| calls.contains_key(*name))
    {
        return Err("route-shape");
    }
    Ok(())
}

pub(super) fn verify_transaction_forbidden_shortcuts(source: &str) -> Result<(), &'static str> {
    syn::parse_file(source).map_err(|_| "route-shape")?;
    for forbidden in [
        "std::fs::",
        "File::open(",
        "OpenOptions::new(",
        "rustix::fs::",
        "rustix::io::",
        "openat(",
        "statat(",
        "linkat(",
        "fstat(",
        "fstatfs(",
        "fsync(",
        "fchmod(",
        "OFlags::",
        "AtFlags::",
        "Mode::",
        "IdentityV0",
        "StableMetadataV0",
        ".legitimacy-tmp-",
        "named-temporary",
        "libc::",
        "unsafe {",
        "unsafe fn",
        "include!(",
        "include_bytes!(",
        "include_str!(",
        "after_complete",
    ] {
        if source.contains(forbidden) {
            return Err("route-shape");
        }
    }
    Ok(())
}

pub(super) fn verify_linux_output_publication_order(source: &str) -> Result<(), &'static str> {
    let compact = compact_source(source);
    let fragments = [
        "attempt(hooks,PublicationStageV0::Link,Some(&held))?;",
        "attempt(hooks,PublicationStageV0::PostHookFinalPreflight,Some(&held),)?;",
        "complete(hooks,PublicationStageV0::PostHookFinalPreflight,Some(&held),);",
        "attempt(hooks,PublicationStageV0::RealLink,Some(&held))?;",
        "attempt(hooks,PublicationStageV0::ProtectedGuard,Some(&held))?;",
        "guard()?;",
        "complete(hooks,PublicationStageV0::ProtectedGuard,Some(&held));",
        "ifletErr(errno)=linkat(",
        "complete(hooks,PublicationStageV0::RealLink,Some(&held));",
        "complete(hooks,PublicationStageV0::Link,Some(&committed.held));",
    ];
    ordered_unique_fragments(&compact, &fragments)?;
    if compact
        .matches("structNoPublicationHooksV0;implPublicationHooksV0forNoPublicationHooksV0{}")
        .count()
        != 1
        || direct_call_argument_profiles(source, "linkat")?.len() != 1
        || identifier_count(source, "classify_incumbent") != 2
        || source.contains("after_complete")
    {
        return Err("route-shape");
    }
    let guard_completion = compact
        .find("complete(hooks,PublicationStageV0::ProtectedGuard,Some(&held));")
        .ok_or("route-shape")?;
    let link = compact
        .find("ifletErr(errno)=linkat(")
        .ok_or("route-shape")?;
    let between = &compact[guard_completion..link];
    if between.matches("?;").count() != 0 {
        return Err("route-shape");
    }
    Ok(())
}

pub(super) fn verify_transaction_publication_order(source: &str) -> Result<(), &'static str> {
    let _ = extract_transaction_pair_order(source)?;
    let compact = compact_source(source);
    for exact in [
        "ifpublications.is_empty(){returnErr(error(AdapterErrorCodeV0::OutputPublish));}",
        "forpublicationinpublications{prepared.push(prepare_with_hooks(publication.output,inputs,expected_uid,&mutNoPublicationHooksV0,)?);}",
        "for(index,left)inprepared.iter().enumerate(){forrightin&prepared[index+1..]{left.reject_cross_output_alias(right)?;}}",
        "}}revalidate_inputs(inputs)?;letmutcommitted:Vec<(CommittedPublicationV0,&[u8])>=Vec::with_capacity(publications.len());",
        "Err(CommitFailureV0::PreLink(original))=>{returnrollback_after_error(committed,original);}",
        "committed.push((*publication,publication_bytes));returnrollback_after_error(committed,original);",
        "letfinal_result=late_verifier().and_then(|()|revalidate_inputs(inputs))",
        "Err(original)=>rollback_after_error(committed,original)",
        "for(name,_)inpublications{prepared.push(prepare_relative(directory,name,inputs,expected_uid).map_err(|error|{RelativeSetFailureV0{committed:Vec::new(),error,}})?,);}",
        "ifletErr(error)=late_verifier(){returnErr(RelativeSetFailureV0{committed,error});}",
        "for(publication,(_,bytes))incommitted.iter().zip(publications){ifletErr(error)=revalidate_committed(publication,bytes,&mutNoPublicationHooksV0){returnErr(RelativeSetFailureV0{committed,error});}}Ok(committed)",
        "semantic_pair()?;",
        "&mutNoPublicationHooksV0,&mutNoPublicationHooksV0,semantic_pair,",
        "letsidecar_bytes=sidecar.bytes;",
        "letpublic_bytes=public.bytes;",
        "&[&sidecar]",
        "||revalidate_committed(&sidecar,sidecar_bytes,sidecar_hooks)",
        "Ok(public)=>{letsidecar_error=revalidate_committed(&sidecar,sidecar_bytes,sidecar_hooks).err();letpublic_error=revalidate_committed(&public,public_bytes,public_hooks).err();",
        "ifeuid.is_err()||identity.is_err(){Err(error(AdapterErrorCodeV0::OutputIdentityUncertain))}elseifintegrity.is_err(){Err(error(AdapterErrorCodeV0::OutputIntegrityUncertain))}else{Ok(())}",
        "Ok((sidecar,public))",
    ] {
        if compact.matches(exact).count() != 1 {
            return Err("route-shape");
        }
    }
    if identifier_count(source, "FnOnce") != 4
        || direct_call_argument_profiles(source, "semantic_pair")? != vec![Vec::<String>::new()]
        || direct_call_argument_profiles(source, "publish_pair_with_hooks")?
            != vec![compact_profile(&[
                "PublicationSpecV0 { output: sidecar_output, bytes: sidecar_bytes, }",
                "PublicationSpecV0 { output: public_output, bytes: public_bytes, }",
                "inputs",
                "&mut NoPublicationHooksV0",
                "&mut NoPublicationHooksV0",
                "semantic_pair",
            ])]
        || direct_call_argument_profiles(source, "prepare_with_hooks")?
            != vec![
                compact_profile(&[
                    "publication.output",
                    "inputs",
                    "expected_uid",
                    "&mut NoPublicationHooksV0",
                ]),
                compact_profile(&["sidecar.output", "inputs", "expected_uid", "sidecar_hooks"]),
                compact_profile(&["public.output", "inputs", "expected_uid", "public_hooks"]),
            ]
        || direct_call_argument_profiles(source, "prepare_relative")?
            != vec![compact_profile(&[
                "directory",
                "name",
                "inputs",
                "expected_uid",
            ])]
        || direct_call_argument_profiles(source, "commit_with_hooks")?
            != vec![
                compact_profile(&[
                    "prepared",
                    "publication_bytes",
                    "inputs",
                    "&protected",
                    "&mut NoPublicationHooksV0",
                    "|| { revalidate_inputs(inputs)?; for (prior, bytes) in &committed { revalidate_committed(prior, bytes, &mut NoPublicationHooksV0)?; } Ok(()) }",
                ]),
                compact_profile(&[
                    "prepared",
                    "bytes",
                    "inputs",
                    "&protected",
                    "&mut NoPublicationHooksV0",
                    "|| Ok(())",
                ]),
                compact_profile(&[
                    "sidecar_prepared",
                    "sidecar_bytes",
                    "inputs",
                    "&[]",
                    "sidecar_hooks",
                    "|| Ok(())",
                ]),
                compact_profile(&[
                    "public_prepared",
                    "public_bytes",
                    "inputs",
                    "&[&sidecar]",
                    "public_hooks",
                    "|| revalidate_committed(&sidecar, sidecar_bytes, sidecar_hooks)",
                ]),
            ]
        || direct_call_argument_profiles(source, "revalidate_committed")?
            != expected_transaction_revalidation_profiles()
        || direct_call_argument_profiles(source, "sidecar_prepared.reject_cross_output_alias")?
            != vec![compact_profile(&["&public_prepared"])]
    {
        return Err("route-shape");
    }
    Ok(())
}

pub(super) fn ordered_unique_fragments(
    source: &str,
    fragments: &[&str],
) -> Result<(), &'static str> {
    let mut previous = 0;
    for fragment in fragments {
        if source.matches(fragment).count() != 1 {
            return Err("route-shape");
        }
        let offset = source.find(fragment).ok_or("route-shape")?;
        if offset < previous {
            return Err("route-shape");
        }
        previous = offset + fragment.len();
    }
    Ok(())
}

pub(super) fn has_exact_super_glob(syntax: &syn::File) -> bool {
    let uses = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Use(item) => Some(item),
            _ => None,
        })
        .collect::<Vec<_>>();
    if uses.len() != 2
        || !matches!(uses[0].vis, syn::Visibility::Inherited)
        || !matches!(
            &uses[1].vis,
            syn::Visibility::Restricted(restricted) if restricted.path.is_ident("crate")
        )
        || !matches!(
            &uses[1].tree,
            syn::UseTree::Path(path)
                if path.ident == "output_set"
                    && matches!(
                        path.tree.as_ref(),
                        syn::UseTree::Name(name) if name.ident == "publish_directory_set"
                    )
        )
    {
        return false;
    }
    matches!(
        &uses[0].tree,
        syn::UseTree::Path(path)
            if path.ident == "super" && matches!(path.tree.as_ref(), syn::UseTree::Glob(_))
    )
}

pub(super) fn verify_after_guard_test_seam(source: &str) -> Result<(), &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "test-seam")?;
    if named_struct_field_types(&syntax, "Hooks").get("after_complete")
        != Some(&"Option<StageAction>".to_string())
    {
        return Err("test-seam");
    }
    let compact = compact_source(source);
    if compact
        .matches(
            "fnevent(&mutself,event:PublicationEventV0,held:Option<&OwnedFd>){self.events.push(event);ifletPublicationEventV0::Completed(stage)=event&&letSome(action)=&mutself.after_complete{action(stage,held);}}",
        )
        .count()
        != 1
    {
        return Err("test-seam");
    }
    for test in [
        "actual_linkat_eexist_classifies_every_incumbent_without_clobbering",
        "cross_output_alias_precedence_is_explicit_when_sidecar_is_also_corrupt",
        "external_content_mutation_after_guard_can_link_but_final_revalidation_fails_closed",
    ] {
        if named_function_binary_expression_count(
            source,
            test,
            "stage==PublicationStageV0::ProtectedGuard",
        ) != Ok(1)
        {
            return Err("test-seam");
        }
    }
    Ok(())
}

pub(super) fn function_starts_with_unconditional_try_call(
    syntax: &syn::File,
    function_name: &str,
    callee_name: &str,
) -> bool {
    let Some(function) = syntax.items.iter().find_map(|item| match item {
        syn::Item::Fn(function) if function.sig.ident == function_name => Some(function),
        _ => None,
    }) else {
        return false;
    };
    let Some(syn::Stmt::Expr(syn::Expr::Try(expression), Some(_))) = function.block.stmts.first()
    else {
        return false;
    };
    if !expression.attrs.is_empty() {
        return false;
    }
    let syn::Expr::Call(call) = expression.expr.as_ref() else {
        return false;
    };
    if !call.attrs.is_empty() || !call.args.is_empty() {
        return false;
    }
    matches!(
        call.func.as_ref(),
        syn::Expr::Path(path)
            if path.attrs.is_empty()
                && path.path.segments.len() == 1
                && path.path.segments[0].ident == callee_name
    )
}

pub(super) fn named_function_binary_expression_count(
    source: &str,
    function_name: &str,
    expected_expression: &str,
) -> Result<usize, &'static str> {
    let mut parser = rust_parser();
    let tree = parser.parse(source, None).ok_or("test-seam")?;
    if tree.root_node().has_error() {
        return Err("test-seam");
    }
    let functions = named_function_nodes(tree.root_node(), source.as_bytes(), function_name)?;
    if functions.len() != 1 {
        return Err("test-seam");
    }
    Ok(count_nodes_with_compact_text(
        functions[0],
        source.as_bytes(),
        "binary_expression",
        expected_expression,
    ))
}

pub(super) fn named_function_nodes<'tree>(
    node: tree_sitter::Node<'tree>,
    source: &[u8],
    function_name: &str,
) -> Result<Vec<tree_sitter::Node<'tree>>, &'static str> {
    let mut functions = Vec::new();
    collect_named_function_nodes(node, source, function_name, &mut functions)?;
    Ok(functions)
}

pub(super) fn collect_named_function_nodes<'tree>(
    node: tree_sitter::Node<'tree>,
    source: &[u8],
    function_name: &str,
    functions: &mut Vec<tree_sitter::Node<'tree>>,
) -> Result<(), &'static str> {
    if node.kind() == "function_item"
        && node
            .child_by_field_name("name")
            .is_some_and(|name| name.utf8_text(source) == Ok(function_name))
    {
        functions.push(node);
    }
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_named_function_nodes(child, source, function_name, functions)?;
    }
    Ok(())
}

pub(super) fn count_nodes_with_compact_text(
    node: tree_sitter::Node<'_>,
    source: &[u8],
    kind: &str,
    expected: &str,
) -> usize {
    let here = usize::from(
        node.kind() == kind
            && node
                .utf8_text(source)
                .is_ok_and(|text| compact_source(text) == expected),
    );
    let mut cursor = node.walk();
    here + node
        .named_children(&mut cursor)
        .map(|child| count_nodes_with_compact_text(child, source, kind, expected))
        .sum::<usize>()
}
