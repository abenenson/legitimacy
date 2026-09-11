use super::*;

pub(super) fn verify_privacy_route_shape(
    sanitizer: &str,
    sanitizer_jwt: &str,
    bundle_wire: &str,
    publication_authority: &str,
) -> Result<(), &'static str> {
    syn::parse_file(sanitizer).map_err(|_| "route-shape")?;
    syn::parse_file(sanitizer_jwt).map_err(|_| "route-shape")?;
    syn::parse_file(bundle_wire).map_err(|_| "route-shape")?;
    syn::parse_file(publication_authority).map_err(|_| "route-shape")?;
    let sanitizer = compact_source(sanitizer);
    let sanitizer_jwt = compact_source(sanitizer_jwt);
    let bundle_wire = compact_source(bundle_wire);
    let publication_authority = compact_source(publication_authority);
    for required in [
        "super::super::sanitizer::scan_public_child_jsonl(jsonl)?;",
        "#[path=\"sanitizer_jwt.rs\"]modjwt;usejwt::contains_jwt_like;",
        "contains_url_scheme(bytes)||contains_access_key_like(bytes)||contains_jwt_like(bytes)||contains_private_home_path(bytes)",
        "surface.get(separator+1..separator+3)==Some(b\"//\")||scheme.eq_ignore_ascii_case(b\"data\")||scheme.eq_ignore_ascii_case(b\"javascript\")",
        "token[..3].eq_ignore_ascii_case(b\"sk-\")||token[..3].eq_ignore_ascii_case(b\"sk_\")",
        "constJWT_JSON_SEGMENT_MAX_ENCODED_BYTES_V0:usize=4*1024;",
        "let(Some(header),Some(payload),Some(signature),None)=(parts.next(),parts.next(),parts.next(),parts.next())",
        "Ok(Value::Object(_))=>JwtJsonEvidenceV0::Object",
        "header_evidence==JwtJsonEvidenceV0::ResourceBoundExceeded||payload_evidence==JwtJsonEvidenceV0::ResourceBoundExceeded||(header_evidence==JwtJsonEvidenceV0::Object&&payload_evidence==JwtJsonEvidenceV0::Object)",
        "lower.windows(5).enumerate().any(|(index,window)|{window==b\"/root\"&&matches!(lower.get(index+5),None|Some(b'/'))",
    ] {
        if !(sanitizer.contains(required)
            || sanitizer_jwt.contains(required)
            || bundle_wire.contains(required)
            || publication_authority.contains(required))
        {
            return Err("route-shape");
        }
    }
    if sanitizer
        .matches("scan_public_child_jsonl(&output)?;")
        .count()
        != 1
        || sanitizer
            .matches("scan_public_child_jsonl(&derived.bytes)?;")
            .count()
            != 1
        || publication_authority
            .matches("scan_publication_bundle_json(&bytes)?;")
            .count()
            != 2
        || bundle_wire
            .matches("super::super::sanitizer::scan_public_child_jsonl(jsonl)?;")
            .count()
            != 1
    {
        return Err("route-shape");
    }
    Ok(())
}

pub(super) fn privacy_route_mutants(
    sanitizer: &str,
    sanitizer_jwt: &str,
    bundle_wire: &str,
    publication_authority: &str,
) -> Vec<(&'static str, String, String, String, String)> {
    vec![
        (
            "public import scanner removed",
            sanitizer.to_string(),
            sanitizer_jwt.to_string(),
            replace_exact_once(
                bundle_wire,
                "        super::super::sanitizer::scan_public_child_jsonl(jsonl)?;",
                "        accept_public_child_jsonl(jsonl)?;",
            ),
            publication_authority.to_string(),
        ),
        (
            "generated child scanner removed",
            replace_exact_once(
                sanitizer,
                "    scan_public_child_jsonl(&output)?;",
                "    accept_public_child_jsonl(&output)?;",
            ),
            sanitizer_jwt.to_string(),
            bundle_wire.to_string(),
            publication_authority.to_string(),
        ),
        (
            "generated publication scanner removed",
            sanitizer.to_string(),
            sanitizer_jwt.to_string(),
            bundle_wire.to_string(),
            replace_exact_nth(
                publication_authority,
                "    scan_publication_bundle_json(&bytes)?;",
                2,
                0,
                "    accept_publication_bundle_json(&bytes)?;",
            ),
        ),
        (
            "scheme recognizer weakened",
            replace_exact_once(
                sanitizer,
                "                || scheme.eq_ignore_ascii_case(b\"javascript\"))",
                "                || scheme.eq_ignore_ascii_case(b\"data\"))",
            ),
            sanitizer_jwt.to_string(),
            bundle_wire.to_string(),
            publication_authority.to_string(),
        ),
        (
            "access-key recognizer weakened",
            replace_exact_once(
                sanitizer,
                "                    || token[..3].eq_ignore_ascii_case(b\"sk_\"))",
                "                    || token[..3].eq_ignore_ascii_case(b\"sk-\"))",
            ),
            sanitizer_jwt.to_string(),
            bundle_wire.to_string(),
            publication_authority.to_string(),
        ),
        (
            "JWT recognizer weakened",
            sanitizer.to_string(),
            replace_exact_once(
                sanitizer_jwt,
                "            let (Some(header), Some(payload), Some(signature), None) =",
                "            let (Some(header), Some(payload), Some(signature), Some(_)) =",
            ),
            bundle_wire.to_string(),
            publication_authority.to_string(),
        ),
        (
            "decoded JWT object evidence removed",
            sanitizer.to_string(),
            replace_exact_once(
                sanitizer_jwt,
                "        Ok(Value::Object(_)) => JwtJsonEvidenceV0::Object,",
                "        Ok(Value::Array(_)) => JwtJsonEvidenceV0::Object,",
            ),
            bundle_wire.to_string(),
            publication_authority.to_string(),
        ),
        (
            "JWT recognizer regressed to lexical only",
            sanitizer.to_string(),
            replace_exact_once(
                sanitizer_jwt,
                "            header_evidence == JwtJsonEvidenceV0::ResourceBoundExceeded\n                || payload_evidence == JwtJsonEvidenceV0::ResourceBoundExceeded\n                || (header_evidence == JwtJsonEvidenceV0::Object\n                    && payload_evidence == JwtJsonEvidenceV0::Object)",
                "            true",
            ),
            bundle_wire.to_string(),
            publication_authority.to_string(),
        ),
        (
            "root-home recognizer weakened",
            replace_exact_once(
                sanitizer,
                "    lower.windows(5).enumerate().any(|(index, window)| {",
                "    lower.get(..5).into_iter().enumerate().any(|(index, window)| {",
            ),
            sanitizer_jwt.to_string(),
            bundle_wire.to_string(),
            publication_authority.to_string(),
        ),
    ]
}

pub(super) fn verify_output_set_route_shape(source: &str) -> Result<(), &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "route-shape")?;
    if flattened_imports(source)
        != BTreeSet::from([
            "super::*".to_string(),
            "rustix::fs::Dir".to_string(),
            "rustix::fs::RenameFlags".to_string(),
            "rustix::fs::mkdirat".to_string(),
            "rustix::fs::renameat_with".to_string(),
            "std::collections::BTreeSet".to_string(),
            "std::ffi::OsStr".to_string(),
        ])
        || syntax
            .items
            .iter()
            .any(|item| matches!(item, syn::Item::Mod(_)))
    {
        return Err("route-shape");
    }
    for forbidden in [
        "std::fs::",
        "File::open(",
        "OpenOptions::new(",
        "libc::",
        "unsafe {",
        "unsafe fn",
        "renameat(",
        "RenameFlags::EXCHANGE",
        "include!(",
        "include_bytes!(",
        "include_str!(",
    ] {
        if source.contains(forbidden) {
            return Err("route-shape");
        }
    }
    if identifier_count(source, "FnOnce") != 2
        || direct_call_argument_profiles(source, "publish_relative_set")?
            != vec![compact_profile(&[
                "&staging",
                "members",
                "inputs",
                "late_verifier",
            ])]
        || direct_call_argument_profiles(source, "renameat_with")?
            != vec![
                compact_profile(&[
                    "parent",
                    "staging_name",
                    "parent",
                    "final_name",
                    "RenameFlags::NOREPLACE",
                ]),
                compact_profile(&[
                    "&publication.parent_path",
                    "*name",
                    "&publication.parent_path",
                    "&quarantine",
                    "RenameFlags::NOREPLACE",
                ]),
            ]
        || direct_call_argument_profiles(source, "preflight_final")?
            != vec![
                compact_profile(&["&parent_path", "&parsed.final_name", "inputs", "&[]"]),
                compact_profile(&["parent", "&final_name.to_os_string()", "inputs", "&[]"]),
                compact_profile(&["parent", "&final_name.to_os_string()", "inputs", "&[]"]),
                compact_profile(&["parent", "&final_name.to_os_string()", "inputs", "&[]"]),
            ]
        || direct_call_argument_profiles(source, "revalidate_inputs")?
            != vec![
                compact_profile(&["inputs"]),
                compact_profile(&["inputs"]),
                compact_profile(&["inputs"]),
                compact_profile(&["inputs"]),
            ]
        || direct_call_argument_profiles(source, "verify_staging_name")?
            != vec![
                compact_profile(&["parent", "staging_name", "staging_identity"]),
                compact_profile(&["parent", "staging_name", "staging_identity"]),
                compact_profile(&["parent", "staging_name", "staging_identity"]),
                compact_profile(&["parent", "staging_name", "staging_identity"]),
                compact_profile(&["parent", "staging_name", "staging_identity"]),
            ]
        || direct_call_argument_profiles(source, "verify_staging_directory")?
            != vec![
                compact_profile(&["staging", "staging_identity", "members", "committed"]),
                compact_profile(&["staging", "staging_identity", "members", "committed"]),
                compact_profile(&["staging", "staging_identity", "members", "committed"]),
            ]
        || direct_call_argument_profiles(source, "cleanup_staging")?
            != vec![compact_profile(&[
                "&parent_path",
                "&parent_sync",
                "&staging_name",
                "&staging",
                "staging_identity",
                "members",
                "&committed",
                "hooks",
            ])]
        || direct_call_argument_profiles(source, "verify_empty_staging_directory")?
            != vec![
                compact_profile(&["staging", "staging_identity"]),
                compact_profile(&["staging", "staging_identity"]),
            ]
        || direct_call_argument_profiles(source, "mkdirat")?
            != vec![compact_profile(&[
                "parent",
                "&name",
                "Mode::from_raw_mode(SET_DIRECTORY_MODE)",
            ])]
        || direct_call_argument_profiles(source, "rustix::rand::getrandom")?
            != vec![compact_profile(&[
                "&mut random",
                "rustix::rand::GetRandomFlags::empty()",
            ])]
        || direct_call_argument_profiles(source, "unlinkat")?
            != vec![
                compact_profile(&[
                    "&publication.parent_path",
                    "&quarantine",
                    "AtFlags::empty()",
                ]),
                compact_profile(&["parent", "staging_name", "AtFlags::REMOVEDIR"]),
            ]
    {
        return Err("route-shape");
    }
    let compact = compact_source(source);
    ordered_unique_fragments(
        &compact,
        &[
            "preflight_final(&parent_path,&parsed.final_name,inputs,&[])?;revalidate_inputs(inputs)?;",
            "letstaging_name=create_staging_directory(&parent_path)?;",
            "letstaging_identity=identity(&staging_stat);hooks.event(OutputSetStageV0::StagingOpened,&staging_name,&staging);",
            "matchpublish_relative_set(&staging,members,inputs,late_verifier)",
            "ifpublication_result.is_err(){hooks.event(OutputSetStageV0::BeforeCleanup,&staging_name,&staging);ifcleanup_staging(",
            "verify_staging_name(parent,staging_name,staging_identity)?;verify_staging_directory(staging,staging_identity,members,committed)?;revalidate_inputs(inputs)?;preflight_final(parent,&final_name.to_os_string(),inputs,&[])?;fsync(staging)",
            "hooks.event(OutputSetStageV0::BeforeRename,staging_name,staging);verify_staging_name(parent,staging_name,staging_identity)?;verify_staging_directory(staging,staging_identity,members,committed)?;",
            "hooks.event(OutputSetStageV0::FinalProofComplete,staging_name,staging);verify_staging_name(parent,staging_name,staging_identity)?;verify_staging_directory(staging,staging_identity,members,committed)?;revalidate_inputs(inputs)?;preflight_final(parent,&final_name.to_os_string(),inputs,&[])?;",
            "renameat_with(parent,staging_name,parent,final_name,RenameFlags::NOREPLACE,)",
            "let_=fsync(parent_sync);Ok(())",
            "renameat_with(&publication.parent_path,*name,&publication.parent_path,&quarantine,RenameFlags::NOREPLACE,)",
            "verify_final_identity(&publication.parent_path,&quarantine,publication.identity,None,publication.expected_uid,bytes.len(),)",
            "verify_empty_staging_directory(staging,staging_identity)?;hooks.event(OutputSetStageV0::CleanupBeforeFinalProof,staging_name,staging,);verify_staging_name(parent,staging_name,staging_identity).map_err(|_|uncertain())?;verify_empty_staging_directory(staging,staging_identity)?;unlinkat(parent,staging_name,AtFlags::REMOVEDIR)",
        ],
    )?;
    Ok(())
}

pub(super) fn output_set_route_mutants(source: &str) -> Vec<(&'static str, String)> {
    vec![
        (
            "output-set first preflight removed",
            replace_exact_nth(source, "preflight_final", 4, 0, "bypass_preflight_final"),
        ),
        (
            "output-set final preflight removed",
            replace_exact_nth(source, "preflight_final", 4, 3, "bypass_preflight_final"),
        ),
        (
            "output-set descriptor-relative publication bypassed",
            replace_exact_once(
                source,
                "publish_relative_set(&staging, members, inputs, late_verifier)",
                "publish_by_staging_path(&staging, members, inputs, late_verifier)",
            ),
        ),
        (
            "output-set staging identity verification removed",
            replace_exact_nth(
                source,
                "verify_staging_name(parent, staging_name, staging_identity)",
                5,
                2,
                "accept_staging_name(parent, staging_name, staging_identity)",
            ),
        ),
        (
            "output-set held member validation removed",
            replace_exact_nth(
                source,
                "verify_staging_directory(staging, staging_identity, members, committed)",
                3,
                2,
                "accept_staging_members(staging, staging_identity, members, committed)",
            ),
        ),
        (
            "output-set no-replace flag removed",
            replace_exact_nth(
                source,
                "RenameFlags::NOREPLACE",
                2,
                0,
                "RenameFlags::empty()",
            ),
        ),
        (
            "output-set commit renamed through unchecked API",
            replace_exact_nth(source, "renameat_with", 3, 1, "renameat_unchecked"),
        ),
        (
            "output-set rollback removed",
            replace_exact_once(
                source,
                "cleanup_staging(\n            &parent_path,\n            &parent_sync,\n            &staging_name,\n            &staging,\n            staging_identity,\n            members,\n            &committed,\n            hooks,\n        )",
                "abandon_staging(\n            &parent_path,\n            &parent_sync,\n            &staging_name,\n            &staging,\n            staging_identity,\n            members,\n            &committed,\n            hooks,\n        )",
            ),
        ),
        (
            "output-set cleanup quarantine removed",
            replace_exact_once(
                source,
                "renameat_with(\n            &publication.parent_path,\n            *name,\n            &publication.parent_path,\n            &quarantine,\n            RenameFlags::NOREPLACE,\n        )",
                "unlink_expected_member(\n            &publication.parent_path,\n            *name,\n            &publication.parent_path,\n            &quarantine,\n            RenameFlags::NOREPLACE,\n        )",
            ),
        ),
        (
            "output-set cleanup final name proof removed",
            replace_exact_nth(
                source,
                "verify_staging_name(parent, staging_name, staging_identity)",
                5,
                4,
                "accept_staging_name(parent, staging_name, staging_identity)",
            ),
        ),
        (
            "output-set cleanup final held-empty proof removed",
            replace_exact_nth(
                source,
                "verify_empty_staging_directory(staging, staging_identity)",
                2,
                1,
                "accept_empty_staging_directory(staging, staging_identity)",
            ),
        ),
        (
            "output-set cleanup scheduler moved before earlier proof",
            replace_exact_once(
                source,
                "    verify_empty_staging_directory(staging, staging_identity)?;\n    hooks.event(\n        OutputSetStageV0::CleanupBeforeFinalProof,\n        staging_name,\n        staging,\n    );",
                "    hooks.event(\n        OutputSetStageV0::CleanupBeforeFinalProof,\n        staging_name,\n        staging,\n    );\n    verify_empty_staging_directory(staging, staging_identity)?;",
            ),
        ),
    ]
}

pub(super) fn verify_rollback_route(source: &str) -> Result<(), &'static str> {
    if source_sha256(source) != EXPECTED_ROLLBACK_SOURCE_SHA256 {
        return Err("route-source");
    }
    verify_rollback_route_shape(source)
}

pub(super) fn verify_rollback_route_shape(source: &str) -> Result<(), &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| "route-shape")?;
    if flattened_imports(source)
        != BTreeSet::from([
            "super::*".to_string(),
            "rustix::fs::RenameFlags".to_string(),
            "rustix::fs::renameat_with".to_string(),
            "sha2::Digest".to_string(),
            "sha2::Sha256".to_string(),
        ])
        || syntax
            .items
            .iter()
            .any(|item| matches!(item, syn::Item::Mod(_)))
    {
        return Err("route-shape");
    }
    for forbidden in [
        "std::fs::",
        "File::open(",
        "OpenOptions::new(",
        "libc::",
        "unsafe {",
        "unsafe fn",
        "renameat(",
        "RenameFlags::EXCHANGE",
        "include!(",
        "include_bytes!(",
        "include_str!(",
    ] {
        if source.contains(forbidden) {
            return Err("route-shape");
        }
    }
    if direct_call_argument_profiles(source, "verify_final_identity")?
        != vec![
            compact_profile(&[
                "&publication.parent_path",
                "&publication.name",
                "publication.identity",
                "publication.metadata",
                "publication.expected_uid",
                "expected_len",
            ]),
            compact_profile(&[
                "&publication.parent_path",
                "&quarantine",
                "publication.identity",
                "None",
                "publication.expected_uid",
                "expected_len",
            ]),
            compact_profile(&[
                "&publication.parent_path",
                "&quarantine",
                "publication.identity",
                "None",
                "publication.expected_uid",
                "expected_len",
            ]),
        ]
        || direct_call_argument_profiles(source, "renameat_with")?
            != vec![compact_profile(&[
                "&publication.parent_path",
                "&publication.name",
                "&publication.parent_path",
                "&quarantine",
                "RenameFlags::NOREPLACE",
            ])]
        || direct_call_argument_profiles(source, "unlinkat")?
            != vec![compact_profile(&[
                "&publication.parent_path",
                "&quarantine",
                "AtFlags::empty()",
            ])]
        || direct_call_argument_profiles(source, "attempt")?
            != vec![
                compact_profile(&[
                    "hooks",
                    "PublicationStageV0::RollbackQuarantine",
                    "Some(&publication.held)",
                ]),
                compact_profile(&[
                    "hooks",
                    "PublicationStageV0::RollbackBeforeUnlink",
                    "Some(&publication.held)",
                ]),
            ]
        || direct_call_argument_profiles(source, "complete")?
            != vec![
                compact_profile(&[
                    "hooks",
                    "PublicationStageV0::RollbackQuarantine",
                    "Some(&publication.held)",
                ]),
                compact_profile(&[
                    "hooks",
                    "PublicationStageV0::RollbackBeforeUnlink",
                    "Some(&publication.held)",
                ]),
            ]
        || direct_call_argument_profiles(source, "verify_quarantined_content")?
            != vec![
                compact_profile(&["&publication", "bytes"]),
                compact_profile(&["&publication", "bytes"]),
            ]
    {
        return Err("route-shape");
    }
    ordered_unique_fragments(
        &compact_source(source),
        &[
            "verify_final_identity(&publication.parent_path,&publication.name,publication.identity,publication.metadata,publication.expected_uid,expected_len,)",
            "attempt(hooks,PublicationStageV0::RollbackQuarantine,Some(&publication.held),)",
            "renameat_with(&publication.parent_path,&publication.name,&publication.parent_path,&quarantine,RenameFlags::NOREPLACE,)",
            "verify_final_identity(&publication.parent_path,&quarantine,publication.identity,None,publication.expected_uid,expected_len,).map_err(|_|uncertain())?;verify_quarantined_content(&publication,bytes)?;complete(hooks,PublicationStageV0::RollbackQuarantine,Some(&publication.held),);",
            "attempt(hooks,PublicationStageV0::RollbackBeforeUnlink,Some(&publication.held),).map_err(|_|uncertain())?;verify_final_identity(&publication.parent_path,&quarantine,publication.identity,None,publication.expected_uid,expected_len,).map_err(|_|uncertain())?;verify_quarantined_content(&publication,bytes)?;",
            "unlinkat(&publication.parent_path,&quarantine,AtFlags::empty())",
        ],
    )
}

pub(super) fn rollback_route_mutants(source: &str) -> Vec<(&'static str, String)> {
    vec![
        (
            "rollback pre-quarantine identity verification removed",
            replace_exact_nth(
                source,
                "verify_final_identity",
                3,
                0,
                "accept_final_identity",
            ),
        ),
        (
            "rollback quarantine rename removed",
            replace_exact_nth(source, "renameat_with", 2, 1, "leave_name_in_place"),
        ),
        (
            "rollback post-quarantine identity verification removed",
            replace_exact_nth(
                source,
                "verify_final_identity",
                3,
                1,
                "accept_final_identity",
            ),
        ),
        (
            "rollback pre-unlink identity verification removed",
            replace_exact_nth(
                source,
                "verify_final_identity",
                3,
                2,
                "accept_final_identity",
            ),
        ),
        (
            "rollback pre-unlink content verification removed",
            replace_exact_nth(
                source,
                "verify_quarantined_content",
                3,
                1,
                "accept_quarantined_content",
            ),
        ),
    ]
}
