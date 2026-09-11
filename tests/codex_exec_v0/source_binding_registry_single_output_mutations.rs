use super::*;

pub(super) fn trajectory_module_edge_mutants(source: &str) -> Vec<(&'static str, String)> {
    vec![
        (
            "unexpected helper module",
            format!("{source}\nmod helper;\n"),
        ),
        (
            "registered module renamed to helper",
            replace_exact_once(source, "mod linux_path;", "mod helper;"),
        ),
        (
            "output module renamed to helper",
            replace_exact_once(source, "mod linux_output;", "mod helper;"),
        ),
        (
            "path Linux gate removed",
            replace_exact_once(
                source,
                "#[cfg(target_os = \"linux\")]\nmod linux_path;",
                "mod linux_path;",
            ),
        ),
        (
            "path Linux gate inverted",
            replace_exact_once(
                source,
                "#[cfg(target_os = \"linux\")]\nmod linux_path;",
                "#[cfg(not(target_os = \"linux\"))]\nmod linux_path;",
            ),
        ),
        (
            "output Linux gate removed",
            replace_exact_once(
                source,
                "#[cfg(target_os = \"linux\")]\nmod linux_output;",
                "mod linux_output;",
            ),
        ),
        (
            "output Linux gate inverted",
            replace_exact_once(
                source,
                "#[cfg(target_os = \"linux\")]\nmod linux_output;",
                "#[cfg(not(target_os = \"linux\"))]\nmod linux_output;",
            ),
        ),
    ]
}

pub(super) fn linux_path_module_edge_mutants(source: &str) -> Vec<(&'static str, String)> {
    vec![
        (
            "unexpected helper module",
            format!("{source}\nmod helper;\n"),
        ),
        (
            "test module path redirected",
            replace_exact_once(source, "linux_path_tests.rs", "helper.rs"),
        ),
        (
            "test module file gate removed",
            replace_exact_once(source, "#[cfg(test)]\n", ""),
        ),
        (
            "test module gate inverted",
            replace_exact_once(source, "#[cfg(test)]", "#[cfg(not(test))]"),
        ),
    ]
}

pub(super) fn linux_output_route_mutants(source: &str) -> Vec<(String, String)> {
    let mut mutants = vec![
        (
            "production transaction module path redirected",
            replace_exact_once(
                source,
                "linux_output_transaction.rs",
                "linux_output_helper.rs",
            ),
        ),
        (
            "production transaction edge gains test gate",
            replace_exact_once(
                source,
                "#[path = \"linux_output_transaction.rs\"]",
                "#[cfg(test)]\n#[path = \"linux_output_transaction.rs\"]",
            ),
        ),
        (
            "test module path redirected",
            replace_exact_once(source, "linux_output_tests.rs", "helper.rs"),
        ),
        (
            "test module gate removed",
            replace_exact_once(
                source,
                "#[cfg(test)]\n#[path = \"linux_output_tests.rs\"]",
                "#[path = \"linux_output_tests.rs\"]",
            ),
        ),
        (
            "Link hook removed",
            replace_exact_once(
                source,
                "attempt(hooks, PublicationStageV0::Link, Some(&held))?;",
                "Ok::<(), AdapterErrorV0>(())?;",
            ),
        ),
        (
            "post-hook final preflight removed",
            replace_exact_once(
                source,
                "    preflight_final(&parent_path, &name, inputs, protected)?;\n    complete(\n        hooks,\n        PublicationStageV0::PostHookFinalPreflight,\n        Some(&held),\n    );",
                "    complete(\n        hooks,\n        PublicationStageV0::PostHookFinalPreflight,\n        Some(&held),\n    );",
            ),
        ),
        (
            "RealLink instrumentation moved after guard",
            replace_exact_once(
                source,
                "    attempt(hooks, PublicationStageV0::RealLink, Some(&held))?;\n    attempt(hooks, PublicationStageV0::ProtectedGuard, Some(&held))?;",
                "    attempt(hooks, PublicationStageV0::ProtectedGuard, Some(&held))?;\n    attempt(hooks, PublicationStageV0::RealLink, Some(&held))?;",
            ),
        ),
        (
            "protected live guard bypassed",
            replace_exact_once(
                source,
                "    guard()?;",
                "    Ok::<(), AdapterErrorV0>(())?;",
            ),
        ),
        (
            "fallible authority call inserted after guard",
            replace_exact_once(
                source,
                "    complete(hooks, PublicationStageV0::ProtectedGuard, Some(&held));\n    if let Err(errno) = linkat(",
                "    complete(hooks, PublicationStageV0::ProtectedGuard, Some(&held));\n    guard()?;\n    if let Err(errno) = linkat(",
            ),
        ),
        (
            "incumbent classifier removed",
            replace_exact_once(
                source,
                "let error = classify_incumbent(&parent_path, &name, inputs, protected);",
                "let error = error(AdapterErrorCodeV0::OutputExists);",
            ),
        ),
        (
            "production no-hooks completion becomes active",
            replace_exact_once(
                source,
                "impl PublicationHooksV0 for NoPublicationHooksV0 {}",
                "impl PublicationHooksV0 for NoPublicationHooksV0 {\n    fn event(&mut self, event: PublicationEventV0, _held: Option<&OwnedFd>) { drop(event); }\n}",
            ),
        ),
        (
            "extra linkat call inserted",
            replace_exact_once(
                source,
                "    if let Err(errno) = linkat(",
                "    let _ = linkat(&proc, &proc_source, &parent_sync, &name, AtFlags::SYMLINK_FOLLOW);\n    if let Err(errno) = linkat(",
            ),
        ),
        (
            "Link completion moved before syscall",
            replace_exact_once(
                source,
                "    if let Err(errno) = linkat(",
                "    complete(hooks, PublicationStageV0::Link, Some(&held));\n    if let Err(errno) = linkat(",
            ),
        ),
        (
            "O_TMPFILE removed",
            replace_exact_once(
                source,
                "OFlags::TMPFILE | OFlags::RDWR | OFlags::CLOEXEC",
                "OFlags::RDWR | OFlags::CLOEXEC",
            ),
        ),
        (
            "O_EXCL added",
            replace_exact_once(
                source,
                "OFlags::TMPFILE | OFlags::RDWR | OFlags::CLOEXEC",
                "OFlags::TMPFILE | OFlags::RDWR | OFlags::EXCL | OFlags::CLOEXEC",
            ),
        ),
        (
            "named temporary path",
            replace_exact_once(
                source,
                "        &parent_sync,\n        Path::new(\".\"),\n        OFlags::TMPFILE",
                "        &parent_sync,\n        Path::new(\".named-temporary\"),\n        OFlags::TMPFILE",
            ),
        ),
        (
            "temporary dirfd detached",
            replace_exact_once(
                source,
                "        &parent_sync,\n        Path::new(\".\"),\n        OFlags::TMPFILE",
                "        rustix::fs::CWD,\n        Path::new(\".\"),\n        OFlags::TMPFILE",
            ),
        ),
        (
            "proc root replaced",
            replace_exact_once(source, "        hooks.proc_root(),", "        Path::new(\"/tmp\"),"),
        ),
        (
            "proc NOFOLLOW removed",
            replace_exact_once(
                source,
                "hooks.proc_root(),\n        OFlags::PATH | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC",
                "hooks.proc_root(),\n        OFlags::PATH | OFlags::DIRECTORY | OFlags::CLOEXEC",
            ),
        ),
        (
            "link source dirfd detached",
            replace_exact_once(
                source,
                "        &proc,\n        &proc_source,",
                "        rustix::fs::CWD,\n        &proc_source,",
            ),
        ),
        (
            "link target dirfd detached",
            replace_exact_once(
                source,
                "        &parent_sync,\n        &name,\n        AtFlags::SYMLINK_FOLLOW",
                "        rustix::fs::CWD,\n        &name,\n        AtFlags::SYMLINK_FOLLOW",
            ),
        ),
        (
            "link procfd source replaced",
            replace_exact_once(
                source,
                "        &proc_source,",
                "        Path::new(\"self/fd/0\"),",
            ),
        ),
        (
            "link follow flag removed",
            replace_exact_once(source, "AtFlags::SYMLINK_FOLLOW,", "AtFlags::empty(),"),
        ),
        (
            "fchmod mode weakened",
            replace_exact_once(
                source,
                "fchmod(&held, Mode::from_raw_mode(OUTPUT_MODE))",
                "fchmod(&held, Mode::from_raw_mode(0o644))",
            ),
        ),
        (
            "file fsync relocated",
            replace_exact_once(source, "fsync(&held)", "fsync(&parent_sync)"),
        ),
        (
            "directory fsync duplicated",
            replace_exact_once(
                source,
                "fsync(&parent_sync).map_err",
                "fsync(&parent_sync).map_err(|errno| publication_errno(errno, is_profile_errno(errno)))?;\n    fsync(&parent_sync).map_err",
            ),
        ),
        (
            "write source truncated",
            replace_exact_once(
                source,
                "rustix::io::write(held, bytes)",
                "rustix::io::write(held, &bytes[..0])",
            ),
        ),
        (
            "pread offset shifted",
            replace_exact_once(
                source,
                "rustix::io::pread(held, bytes, offset)",
                "rustix::io::pread(held, bytes, offset.saturating_add(1))",
            ),
        ),
        (
            "EMPTY_PATH shortcut",
            replace_exact_once(
                source,
                "AtFlags::SYMLINK_FOLLOW,",
                "AtFlags::SYMLINK_FOLLOW | AtFlags::EMPTY_PATH,",
            ),
        ),
        (
            "named rename fallback",
            format!(
                "{source}\nfn named_fallback() {{ let _ = std::fs::rename(\"temporary\", \"final\"); }}\n"
            ),
        ),
        (
            "named hard-link fallback",
            format!(
                "{source}\nfn named_hard_link() {{ let _ = std::fs::hard_link(\"temporary\", \"final\"); }}\n"
            ),
        ),
        (
            "named remove fallback",
            format!(
                "{source}\nfn named_remove() {{ let _ = std::fs::remove_file(\"temporary\"); }}\n"
            ),
        ),
        (
            "unlinkat cleanup fallback",
            format!(
                "{source}\nfn unlink_cleanup() {{ let _ = rustix::fs::unlinkat(rustix::fs::CWD, Path::new(\"temporary\"), AtFlags::empty()); }}\n"
            ),
        ),
        (
            "unbound include",
            replace_exact_once(
                source,
                "#[cfg(test)]\n#[path = \"linux_output_tests.rs\"]",
                "const HIDDEN: &[u8] = include_bytes!(\"linux_output_tests.rs\");\n#[cfg(test)]\n#[path = \"linux_output_tests.rs\"]",
            ),
        ),
    ]
    .into_iter()
    .map(|(attack, mutation)| (attack.to_string(), mutation))
    .collect::<Vec<_>>();
    for call_index in 0..5 {
        for (argument, replacement) in [
            (0, "std::fs::File::open(\".\").unwrap()"),
            (1, "Path::new(\"mutant\")"),
            (2, "OFlags::empty()"),
        ] {
            let attack = format!("openat[{call_index}] argument[{argument}]");
            mutants.push((
                attack,
                mutate_direct_call_argument(source, "openat", call_index, argument, replacement),
            ));
        }
    }
    mutants.push((
        "openat[2] temporary mode".to_string(),
        mutate_direct_call_argument(source, "openat", 2, 3, "Mode::from_raw_mode(0o777)"),
    ));
    for call_index in 0..5 {
        for (argument, replacement) in [
            (0, "std::fs::File::open(\".\").unwrap()"),
            (1, "Path::new(\"mutant\")"),
            (
                2,
                if call_index == 2 {
                    "AtFlags::SYMLINK_NOFOLLOW"
                } else {
                    "AtFlags::empty()"
                },
            ),
        ] {
            let attack = format!("statat[{call_index}] argument[{argument}]");
            mutants.push((
                attack,
                mutate_direct_call_argument(source, "statat", call_index, argument, replacement),
            ));
        }
    }
    for (attack, call_index, argument_index, replacement) in [
        ("hooks.write held handle swapped", 0, 0, "&other_held"),
        ("hooks.write written slice reset", 0, 1, "bytes"),
        ("hooks.pread chunk held handle swapped", 0, 0, "&other_held"),
        (
            "hooks.pread chunk bound loses remaining cap",
            0,
            1,
            "&mut chunk[..VERIFY_CHUNK_BYTES]",
        ),
        (
            "hooks.pread chunk offset shifted",
            0,
            2,
            "offset.saturating_add(1)",
        ),
        ("hooks.pread EOF held handle swapped", 1, 0, "&other_held"),
        (
            "hooks.pread EOF offset rewound",
            1,
            2,
            "offset.saturating_sub(1)",
        ),
    ] {
        let callee = if attack.starts_with("hooks.write") {
            "hooks.write"
        } else {
            "hooks.pread"
        };
        mutants.push((
            attack.to_string(),
            mutate_direct_call_argument(source, callee, call_index, argument_index, replacement),
        ));
    }
    mutants
}
