use super::*;

pub(super) fn transaction_route_mutants(source: &str) -> Vec<(&'static str, String)> {
    let raw_compare = concat!(
        "    if sidecar.output.as_os_str().as_bytes() == public.output.as_os_str().as_bytes() {\n",
        "        return Err(error(AdapterErrorCodeV0::CrossOutputAlias));\n",
        "    }\n"
    );
    let mut mutants = vec![
        (
            "transaction super authority replaced by crate glob",
            replace_exact_once(source, "use super::*;", "use crate::*;"),
        ),
        (
            "transaction gains filesystem authority import",
            replace_exact_once(source, "use super::*;", "use super::*;\nuse std::fs::File;"),
        ),
        (
            "set resolved-alias preflight removed",
            replace_exact_once(
                source,
                "            left.reject_cross_output_alias(right)?;",
                "            accept_cross_output_alias(left, right)?;",
            ),
        ),
        (
            "set input preflight removed",
            replace_exact_nth(
                source,
                "revalidate_inputs(inputs)",
                5,
                0,
                "accept_inputs(inputs)",
            ),
        ),
        (
            "set commit mechanism bypassed",
            replace_exact_once(
                source,
                "        let result = commit_with_hooks(",
                "        let result = link_without_transaction(",
            ),
        ),
        (
            "set pre-link rollback removed",
            replace_exact_once(
                source,
                "            Err(CommitFailureV0::PreLink(original)) => {\n                return rollback_after_error(committed, original);\n            }",
                "            Err(CommitFailureV0::PreLink(original)) => {\n                return Err(original);\n            }",
            ),
        ),
        (
            "set post-link rollback removed",
            replace_exact_once(
                source,
                "                committed.push((*publication, publication_bytes));\n                return rollback_after_error(committed, original);",
                "                drop(publication);\n                return Err(original);",
            ),
        ),
        (
            "set late verifier removed",
            replace_exact_once(
                source,
                "    let final_result = late_verifier()",
                "    let final_result = Ok(())",
            ),
        ),
        (
            "set rollback deletion removed",
            replace_exact_once(
                source,
                "        if rollback_committed(publication, bytes).is_err() {",
                "        if abandon_committed(publication, bytes).is_err() {",
            ),
        ),
        (
            "FnOnce authority weakened to FnMut",
            replace_exact_nth(source, "FnOnce", 4, 0, "FnMut"),
        ),
        (
            "semantic validation deleted",
            replace_exact_once(
                source,
                "    semantic_pair()?;",
                "    Ok::<(), AdapterErrorV0>(())?;",
            ),
        ),
        (
            "semantic validation made unreachable",
            replace_exact_once(
                source,
                "    semantic_pair()?;\n",
                "    if false {\n        semantic_pair()?;\n    }\n",
            ),
        ),
        (
            "semantic validation compiled out",
            replace_exact_once(
                source,
                "    semantic_pair()?;\n",
                "    #[cfg(any())]\n    semantic_pair()?;\n",
            ),
        ),
        (
            "semantic validation moved after raw alias comparison",
            replace_exact_once(
                source,
                &format!("    semantic_pair()?;\n{raw_compare}"),
                &format!("{raw_compare}    semantic_pair()?;\n"),
            ),
        ),
        (
            "euid captured before semantic validation",
            replace_exact_once(
                source,
                "    semantic_pair()?;\n",
                "    let _early_uid = rustix::process::geteuid().as_raw();\n    semantic_pair()?;\n",
            ),
        ),
        (
            "raw byte alias comparison deleted",
            replace_exact_once(source, raw_compare, ""),
        ),
        (
            "wrapper PublicationSpec roles swapped",
            replace_exact_once(
                source,
                concat!(
                    "        PublicationSpecV0 {\n",
                    "            output: sidecar_output,\n",
                    "            bytes: sidecar_bytes,\n",
                    "        },\n",
                    "        PublicationSpecV0 {\n",
                    "            output: public_output,\n",
                    "            bytes: public_bytes,\n",
                    "        },"
                ),
                concat!(
                    "        PublicationSpecV0 {\n",
                    "            output: public_output,\n",
                    "            bytes: public_bytes,\n",
                    "        },\n",
                    "        PublicationSpecV0 {\n",
                    "            output: sidecar_output,\n",
                    "            bytes: sidecar_bytes,\n",
                    "        },"
                ),
            ),
        ),
        (
            "transaction sidecar byte alias swapped",
            replace_exact_once(
                source,
                "    let sidecar_bytes = sidecar.bytes;",
                "    let sidecar_bytes = public.bytes;",
            ),
        ),
        (
            "transaction public byte alias swapped",
            replace_exact_once(
                source,
                "    let public_bytes = public.bytes;",
                "    let public_bytes = sidecar.bytes;",
            ),
        ),
        (
            "transaction byte aliases pair-swapped",
            replace_exact_once(
                source,
                "    let sidecar_bytes = sidecar.bytes;\n    let public_bytes = public.bytes;",
                "    let sidecar_bytes = public.bytes;\n    let public_bytes = sidecar.bytes;",
            ),
        ),
        (
            "public preparation moved first",
            replace_exact_once(
                source,
                concat!(
                    "    let sidecar_prepared = prepare_with_hooks(sidecar.output, inputs, expected_uid, sidecar_hooks)?;\n",
                    "    let public_prepared = prepare_with_hooks(public.output, inputs, expected_uid, public_hooks)?;"
                ),
                concat!(
                    "    let public_prepared = prepare_with_hooks(public.output, inputs, expected_uid, public_hooks)?;\n",
                    "    let sidecar_prepared = prepare_with_hooks(sidecar.output, inputs, expected_uid, sidecar_hooks)?;"
                ),
            ),
        ),
        (
            "resolved alias check moved before both prepares",
            replace_exact_once(
                source,
                concat!(
                    "    let public_prepared = prepare_with_hooks(public.output, inputs, expected_uid, public_hooks)?;\n",
                    "    sidecar_prepared.reject_cross_output_alias(&public_prepared)?;"
                ),
                concat!(
                    "    sidecar_prepared.reject_cross_output_alias(&public_prepared)?;\n",
                    "    let public_prepared = prepare_with_hooks(public.output, inputs, expected_uid, public_hooks)?;"
                ),
            ),
        ),
        (
            "sidecar commit authority bypassed",
            replace_exact_once(
                source,
                "    let sidecar = match commit_with_hooks(",
                "    let sidecar = match bypassed_commit_with_hooks(",
            ),
        ),
        (
            "public commit authority bypassed",
            replace_exact_once(
                source,
                "    let public_result = commit_with_hooks(",
                "    let public_result = bypassed_commit_with_hooks(",
            ),
        ),
        (
            "protected sidecar removed from public commit",
            replace_exact_once(source, "        &[&sidecar],", "        &[],"),
        ),
        (
            "live sidecar guard replaced with success",
            replace_exact_once(
                source,
                "        || revalidate_committed(&sidecar, sidecar_bytes, sidecar_hooks),",
                "        || Ok(()),",
            ),
        ),
        (
            "final sidecar revalidation deleted",
            replace_exact_once(
                source,
                "            let sidecar_error = revalidate_committed(&sidecar, sidecar_bytes, sidecar_hooks).err();\n            let public_error = revalidate_committed(&public, public_bytes, public_hooks).err();\n            if sidecar_error.is_some() || public_error.is_some() {",
                "            let sidecar_error = None;\n            let public_error = revalidate_committed(&public, public_bytes, public_hooks).err();\n            if sidecar_error.is_some() || public_error.is_some() {",
            ),
        ),
        (
            "final public revalidation deleted",
            replace_exact_once(
                source,
                "            let sidecar_error = revalidate_committed(&sidecar, sidecar_bytes, sidecar_hooks).err();\n            let public_error = revalidate_committed(&public, public_bytes, public_hooks).err();\n            if sidecar_error.is_some() || public_error.is_some() {",
                "            let sidecar_error = revalidate_committed(&sidecar, sidecar_bytes, sidecar_hooks).err();\n            let public_error = None;\n            if sidecar_error.is_some() || public_error.is_some() {",
            ),
        ),
        (
            "semantic callback invoked again after public commit",
            replace_exact_once(
                source,
                "        Ok(public) => {",
                "        Ok(public) => {\n            semantic_pair()?;",
            ),
        ),
        (
            "committed identity predicate weakened to conjunction",
            replace_exact_once(
                source,
                "    if euid.is_err() || identity.is_err() {",
                "    if euid.is_err() && identity.is_err() {",
            ),
        ),
        (
            "committed integrity precedence promoted over identity",
            replace_exact_once(
                source,
                concat!(
                    "    if euid.is_err() || identity.is_err() {\n",
                    "        Err(error(AdapterErrorCodeV0::OutputIdentityUncertain))\n",
                    "    } else if integrity.is_err() {\n",
                    "        Err(error(AdapterErrorCodeV0::OutputIntegrityUncertain))"
                ),
                concat!(
                    "    if integrity.is_err() {\n",
                    "        Err(error(AdapterErrorCodeV0::OutputIntegrityUncertain))\n",
                    "    } else if euid.is_err() || identity.is_err() {\n",
                    "        Err(error(AdapterErrorCodeV0::OutputIdentityUncertain))"
                ),
            ),
        ),
        (
            "successful pair return handles swapped",
            replace_exact_once(
                source,
                "                Ok((sidecar, public))",
                "                Ok((public, sidecar))",
            ),
        ),
        (
            "transaction test module path redirected",
            replace_exact_once(
                source,
                "linux_output_transaction_tests.rs",
                "linux_output_transaction_helper.rs",
            ),
        ),
        (
            "transaction test gate removed",
            replace_exact_once(
                source,
                "#[cfg(test)]\n#[path = \"linux_output_transaction_tests.rs\"]",
                "#[path = \"linux_output_transaction_tests.rs\"]",
            ),
        ),
    ];
    for (attack, callee, call, argument, replacement) in [
        (
            "wrapper sidecar PublicationSpec path swapped",
            "publish_pair_with_hooks",
            0,
            0,
            "PublicationSpecV0 { output: public_output, bytes: sidecar_bytes }",
        ),
        (
            "wrapper sidecar PublicationSpec bytes swapped",
            "publish_pair_with_hooks",
            0,
            0,
            "PublicationSpecV0 { output: sidecar_output, bytes: public_bytes }",
        ),
        (
            "wrapper sidecar hooks swapped",
            "publish_pair_with_hooks",
            0,
            3,
            "&mut public_hooks",
        ),
        (
            "wrapper public hooks swapped",
            "publish_pair_with_hooks",
            0,
            4,
            "&mut sidecar_hooks",
        ),
        (
            "sidecar prepare uses public path",
            "prepare_with_hooks",
            1,
            0,
            "public.output",
        ),
        (
            "sidecar prepare uses public hooks",
            "prepare_with_hooks",
            1,
            3,
            "public_hooks",
        ),
        (
            "public prepare uses sidecar hooks",
            "prepare_with_hooks",
            2,
            3,
            "sidecar_hooks",
        ),
        (
            "sidecar commit uses public bytes",
            "commit_with_hooks",
            2,
            1,
            "public_bytes",
        ),
        (
            "sidecar commit uses public hooks",
            "commit_with_hooks",
            2,
            4,
            "public_hooks",
        ),
        (
            "public commit uses sidecar prepared handle",
            "commit_with_hooks",
            3,
            0,
            "sidecar_prepared",
        ),
        (
            "public commit uses sidecar bytes",
            "commit_with_hooks",
            3,
            1,
            "sidecar_bytes",
        ),
        (
            "public commit protects public handle",
            "commit_with_hooks",
            3,
            3,
            "&[&public]",
        ),
        (
            "public commit uses sidecar hooks",
            "commit_with_hooks",
            3,
            4,
            "sidecar_hooks",
        ),
        (
            "live sidecar guard uses public bytes",
            "revalidate_committed",
            4,
            1,
            "public_bytes",
        ),
        (
            "live sidecar guard uses public hooks",
            "revalidate_committed",
            4,
            2,
            "public_hooks",
        ),
        (
            "post-link public revalidation uses sidecar handle",
            "revalidate_committed",
            7,
            0,
            "&sidecar",
        ),
        (
            "final sidecar revalidation uses public handle",
            "revalidate_committed",
            8,
            0,
            "&public",
        ),
        (
            "final public revalidation uses sidecar hooks",
            "revalidate_committed",
            9,
            2,
            "sidecar_hooks",
        ),
    ] {
        mutants.push((
            attack,
            mutate_direct_call_argument(source, callee, call, argument, replacement),
        ));
    }
    mutants
}

pub(super) fn transaction_phase_module_edge_mutants(source: &str) -> Vec<(&'static str, String)> {
    vec![
        (
            "phase sibling cfg(test) removed",
            replace_exact_once(
                source,
                "#[cfg(test)]\n#[path = \"linux_output_transaction_phase_tests.rs\"]",
                "#[path = \"linux_output_transaction_phase_tests.rs\"]",
            ),
        ),
        (
            "phase sibling redirected",
            replace_exact_once(
                source,
                "linux_output_transaction_phase_tests.rs",
                "linux_output_transaction_phase_helper.rs",
            ),
        ),
    ]
}

pub(super) fn after_guard_test_seam_mutants(source: &str) -> Vec<(&'static str, String)> {
    let redirected_with_unrelated_decoy = format!(
        "{}\nfn unrelated_guard_predicate(stage: PublicationStageV0) -> bool {{\n    stage == PublicationStageV0::ProtectedGuard\n}}\n",
        replace_exact_nth(
            source,
            "if stage == PublicationStageV0::ProtectedGuard",
            2,
            0,
            "if stage == PublicationStageV0::RealLink",
        )
    );
    vec![
        (
            "after-complete field renamed",
            replace_exact_once(
                source,
                "    after_complete: Option<StageAction>,",
                "    after_guard: Option<StageAction>,",
            ),
        ),
        (
            "completion seam listens to attempts",
            replace_exact_once(
                source,
                "if let PublicationEventV0::Completed(stage) = event",
                "if let PublicationEventV0::Attempted(stage) = event",
            ),
        ),
        (
            "completion callback removed",
            replace_exact_nth(
                source,
                "            action(stage, held);",
                2,
                0,
                "            drop((stage, held));",
            ),
        ),
        (
            "after-guard seam redirected",
            replace_exact_once(
                source,
                "incumbent == Incumbent::Sidecar && stage == PublicationStageV0::ProtectedGuard",
                "incumbent == Incumbent::Sidecar && stage == PublicationStageV0::RealLink",
            ),
        ),
        (
            "after-guard predicate replaced by unrelated decoy",
            redirected_with_unrelated_decoy,
        ),
    ]
}

pub(super) fn mutate_direct_call_argument(
    source: &str,
    callee: &str,
    call_index: usize,
    argument_index: usize,
    replacement: &str,
) -> String {
    let mut parser = rust_parser();
    let tree = parser.parse(source, None).unwrap();
    let mut ranges = Vec::new();
    collect_direct_call_argument_ranges(tree.root_node(), source.as_bytes(), callee, &mut ranges);
    assert!(
        call_index < ranges.len(),
        "mutant callee index must exist: {callee}[{call_index}]"
    );
    assert!(
        argument_index < ranges[call_index].len(),
        "mutant argument index must exist: {callee}[{call_index}][{argument_index}]"
    );
    let range = &ranges[call_index][argument_index];
    assert_ne!(
        &source[range.clone()],
        replacement,
        "mutant argument replacement must differ"
    );
    format!(
        "{}{replacement}{}",
        &source[..range.start],
        &source[range.end..]
    )
}

pub(super) fn collect_direct_call_argument_ranges(
    node: tree_sitter::Node<'_>,
    source: &[u8],
    expected_callee: &str,
    ranges: &mut Vec<Vec<std::ops::Range<usize>>>,
) {
    if node.kind() == "call_expression" {
        let callee = node.child_by_field_name("function").unwrap();
        if callee.utf8_text(source).unwrap() == expected_callee {
            let arguments = node.child_by_field_name("arguments").unwrap();
            let mut cursor = arguments.walk();
            ranges.push(
                arguments
                    .named_children(&mut cursor)
                    .map(|argument| argument.byte_range())
                    .collect(),
            );
        }
    }
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_direct_call_argument_ranges(child, source, expected_callee, ranges);
    }
}

pub(super) fn linux_path_route_mutants(source: &str) -> Vec<(&'static str, String)> {
    let remove_ancestor_nofollow = replace_exact_nth(
        source,
        "OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC",
        3,
        0,
        "OFlags::PATH | OFlags::DIRECTORY | OFlags::CLOEXEC",
    );
    let relocate_ancestor_nofollow = replace_exact_once(
        &replace_exact_nth(
            source,
            "OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC",
            3,
            0,
            "OFlags::PATH | OFlags::DIRECTORY | OFlags::CLOEXEC",
        ),
        "OFlags::RDONLY | OFlags::NONBLOCK | OFlags::CLOEXEC",
        "OFlags::RDONLY | OFlags::NONBLOCK | OFlags::NOFOLLOW | OFlags::CLOEXEC",
    );
    let duplicate_controlled_follow = replace_exact_once(
        source,
        "OFlags::RDONLY | OFlags::NONBLOCK | OFlags::CLOEXEC",
        "OFlags::RDONLY | OFlags::NONBLOCK | OFlags::NOFOLLOW | OFlags::CLOEXEC",
    );
    let remove_final_stat_nofollow = replace_exact_once(
        source,
        "statat(&parent, &parsed.final_name, AtFlags::SYMLINK_NOFOLLOW)",
        "statat(&parent, &parsed.final_name, AtFlags::empty())",
    );
    let duplicate_final_stat_nofollow = replace_exact_once(
        source,
        "statat(&parent, &parsed.final_name, AtFlags::SYMLINK_NOFOLLOW)",
        "statat(\n        &parent,\n        &parsed.final_name,\n        AtFlags::SYMLINK_NOFOLLOW | AtFlags::SYMLINK_NOFOLLOW,\n    )",
    );
    vec![
        ("ancestor NOFOLLOW removed", remove_ancestor_nofollow),
        ("ancestor NOFOLLOW relocated", relocate_ancestor_nofollow),
        (
            "controlled procfs follow receives NOFOLLOW",
            duplicate_controlled_follow,
        ),
        ("final stat NOFOLLOW removed", remove_final_stat_nofollow),
        (
            "final stat NOFOLLOW duplicated",
            duplicate_final_stat_nofollow,
        ),
        (
            "forbidden File open after test gate",
            format!("{source}\nfn hidden() {{ let _ = File::open(\"input\"); }}\n"),
        ),
        (
            "cfg-not-test forbidden read",
            replace_exact_once(
                source,
                "#[cfg(test)]",
                "#[cfg(not(test))]\nfn hidden() { let _ = std::fs::read(\"input\"); }\n#[cfg(test)]",
            ),
        ),
        (
            "unbound test-source include",
            replace_exact_once(
                source,
                "#[cfg(test)]",
                "const HIDDEN: &[u8] = include_bytes!(\"linux_path_tests.rs\");\n#[cfg(test)]",
            ),
        ),
    ]
}

pub(super) fn trajectory_route_mutants(source: &str) -> Vec<(&'static str, String)> {
    let adapter_call = concat!(
        "adapt_codex_exec_owned_v0(\n",
        "                    std::mem::take(&mut *raw.bytes),\n",
        "                    &authority,\n",
        "                    &trusted,\n",
        "                )?"
    );
    let mutate_adapter = |replacement: &str| replace_exact_once(source, adapter_call, replacement);
    let mut mutants = vec![
        ("neutral context name", mutate_adapter("eval(context)?")),
        (
            "assignment alias",
            mutate_adapter("{ let p = context; eval(p)? }"),
        ),
        (
            "aliased policy import",
            replace_exact_once(
                &mutate_adapter("decode(raw.bytes, &authority, &trusted)?"),
                "adapt_codex_exec_owned_v0,",
                "parse_graph_file as decode,",
            ),
        ),
        (
            "neutral wrapper",
            format!(
                "{}\nfn neutral<A, B, C>(_: A, _: B, context: C) -> Result<(), AdapterErrorV0> {{ eval(context) }}\n",
                mutate_adapter("neutral(raw.bytes, &authority, &trusted)?")
            ),
        ),
        (
            "attacker inert-name shadow",
            format!("{source}\nfn validate_binding<T>(policy: T) {{ eval(policy) }}\n"),
        ),
        (
            "duplicate policy run",
            mutate_adapter("policy::run(raw.bytes, &authority, &trusted)?"),
        ),
        ("macro indirection", mutate_adapter("evil!(context)?")),
        (
            "shadowed adapter function pointer",
            mutate_adapter(
                "{ let adapt_codex_exec_owned_v0 = eval; adapt_codex_exec_owned_v0(raw.bytes, &authority, &trusted)? }",
            ),
        ),
        (
            "fully qualified policy function item through existing callback",
            replace_exact_once(
                source,
                "linux_path::read_snapshot(raw_stdout_jsonl, MAX_CODEX_JSONL_BYTES_V0)?",
                "legitimacy::policy::parse_policy_file(raw_stdout_jsonl)?",
            ),
        ),
        (
            "fixed-test sanitizer routed into production",
            replace_exact_once(
                source,
                "sanitize_capture_v0(&raw.bytes, &authority, &trusted)?",
                "sanitize_capture_with_fixed_test_nonce_v0(&raw.bytes, &authority, &trusted)?",
            ),
        ),
        (
            "production sanitizer bypassed",
            replace_exact_once(
                source,
                "sanitize_capture_v0(&raw.bytes, &authority, &trusted)?",
                "bypass_sanitize_capture_v0(&raw.bytes, &authority, &trusted)?",
            ),
        ),
        (
            "owner lineage construction bypassed",
            replace_exact_once(
                source,
                ".into_publication_pair()?",
                ".bypass_owner_private_lineage_sidecar()?",
            ),
        ),
        (
            "public upgrade bypassed",
            replace_exact_once(
                source,
                ".into_publication_pair()?",
                ".bypass_public_shareable()?",
            ),
        ),
        (
            "semantic pair validation callback bypassed",
            replace_exact_once(
                source,
                "|| validate_semantic_pair(&sidecar_bytes, &public_bytes)",
                "|| Ok(())",
            ),
        ),
        (
            "sidecar and public pair roles swapped",
            replace_exact_once(
                source,
                concat!(
                    "                let (sidecar, public) = linux_output::publish_pair(\n",
                    "                    sidecar_output,\n",
                    "                    &sidecar_bytes,\n",
                    "                    output,\n",
                    "                    &public_bytes,"
                ),
                concat!(
                    "                let (sidecar, public) = linux_output::publish_pair(\n",
                    "                    output,\n",
                    "                    &public_bytes,\n",
                    "                    sidecar_output,\n",
                    "                    &sidecar_bytes,"
                ),
            ),
        ),
        (
            "semantic pair revalidation deleted",
            replace_exact_once(
                source,
                ".revalidate_public_bundle(inspected)?",
                ".bypass_revalidate_public_bundle(inspected)?",
            ),
        ),
    ];
    for (attack, argument, replacement) in [
        ("sidecar output path replaced by public path", 0, "output"),
        ("sidecar bytes replaced by public bytes", 1, "&public_bytes"),
        (
            "public output path replaced by sidecar path",
            2,
            "sidecar_output",
        ),
        (
            "public bytes replaced by sidecar bytes",
            3,
            "&sidecar_bytes",
        ),
        (
            "publication provenance reordered",
            4,
            "&[&raw, &context, &receipt]",
        ),
        (
            "semantic pair callback roles swapped",
            5,
            "|| validate_semantic_pair(&public_bytes, &sidecar_bytes)",
        ),
    ] {
        mutants.push((
            attack,
            mutate_direct_call_argument(
                source,
                "linux_output::publish_pair",
                0,
                argument,
                replacement,
            ),
        ));
    }
    mutants
}
