use super::*;

const BUILD_ROUTE_ERROR: &str = "build-route";

pub(super) fn verify_manifest_route(source: &str) -> Result<(), &'static str> {
    let manifest: toml::Value = toml::from_str(source).map_err(|_| BUILD_ROUTE_ERROR)?;
    let root = manifest.as_table().ok_or(BUILD_ROUTE_ERROR)?;
    if root.keys().map(String::as_str).collect::<BTreeSet<_>>()
        != BTreeSet::from(["bin", "dependencies", "dev-dependencies", "lib", "package"])
    {
        return Err(BUILD_ROUTE_ERROR);
    }
    let package = root["package"].as_table().ok_or(BUILD_ROUTE_ERROR)?;
    if package.keys().map(String::as_str).collect::<BTreeSet<_>>()
        != BTreeSet::from([
            "authors",
            "autobins",
            "autolib",
            "build",
            "categories",
            "description",
            "edition",
            "keywords",
            "license",
            "name",
            "readme",
            "repository",
            "version",
        ])
        || package["name"].as_str() != Some("legitimacy")
        || package["version"].as_str() != Some("1.1.1")
        || package["edition"].as_str() != Some("2024")
        || package["autolib"].as_bool() != Some(false)
        || package["autobins"].as_bool() != Some(false)
        || package["build"].as_str() != Some("build.rs")
    {
        return Err(BUILD_ROUTE_ERROR);
    }
    let library = root["lib"].as_table().ok_or(BUILD_ROUTE_ERROR)?;
    if library.keys().map(String::as_str).collect::<BTreeSet<_>>() != BTreeSet::from(["path"])
        || library["path"].as_str() != Some("src/lib.rs")
    {
        return Err(BUILD_ROUTE_ERROR);
    }
    let binaries = root["bin"].as_array().ok_or(BUILD_ROUTE_ERROR)?;
    if binaries.len() != 5 {
        return Err(BUILD_ROUTE_ERROR);
    }
    let expected = [
        ("legitimacy", "cli/main.rs"),
        (
            "legitimacy-audit-agent",
            "src/bin/legitimacy-audit-agent.rs",
        ),
        (
            "import_codex_observed_runtime",
            "src/bin/import_codex_observed_runtime.rs",
        ),
        (
            "legitimacy-codex-capture-v0",
            "src/bin/legitimacy-codex-capture-v0.rs",
        ),
        (
            "legitimacy-executed-composition",
            "src/bin/legitimacy-executed-composition.rs",
        ),
    ];
    for (target, (name, path)) in binaries.iter().zip(expected) {
        let target = target.as_table().ok_or(BUILD_ROUTE_ERROR)?;
        if target.keys().map(String::as_str).collect::<BTreeSet<_>>()
            != BTreeSet::from(["name", "path"])
            || target["name"].as_str() != Some(name)
            || target["path"].as_str() != Some(path)
        {
            return Err(BUILD_ROUTE_ERROR);
        }
    }
    Ok(())
}

pub(super) fn verify_build_script_route(source: &str) -> Result<(), &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| BUILD_ROUTE_ERROR)?;
    if !syntax.attrs.is_empty()
        || syntax.items.len() != 6
        || compact_source(source)
            .matches("usestd::{env,process::Command};")
            .count()
            != 1
    {
        return Err(BUILD_ROUTE_ERROR);
    }
    let functions = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(function) => Some((
                function.sig.ident.to_string(),
                signature_shape(&function.sig, &function.vis),
            )),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let functions_are_plain = syntax.items.iter().all(|item| match item {
        syn::Item::Fn(function) => {
            function.attrs.is_empty()
                && function.sig.constness.is_none()
                && function.sig.asyncness.is_none()
                && function.sig.unsafety.is_none()
                && function.sig.abi.is_none()
                && function.sig.variadic.is_none()
                && function.sig.generics.params.is_empty()
                && function.sig.generics.where_clause.is_none()
        }
        syn::Item::Use(item) => item.attrs.is_empty(),
        syn::Item::Const(item) => item.attrs.is_empty() && item.ident == "GRAPH_FIXTURES",
        _ => false,
    });
    if functions
        != BTreeSet::from([
            (
                "dirty_suffix".to_string(),
                "inherited fn dirty_suffix(commit:&str)->String".to_string(),
            ),
            (
                "git_output".to_string(),
                "inherited fn git_output(manifest_dir:&str,args:&[&str])->Result<String,String>"
                    .to_string(),
            ),
            (
                "git_path_is_dirty".to_string(),
                "inherited fn git_path_is_dirty(manifest_dir:&str,path:&str)->Result<bool,String>"
                    .to_string(),
            ),
            (
                "main".to_string(),
                "inherited fn main()->Result<(),String>".to_string(),
            ),
        ])
        || !functions_are_plain
    {
        return Err(BUILD_ROUTE_ERROR);
    }
    let compact = compact_source(source);
    let expected_fixtures = "constGRAPH_FIXTURES:&[(&str,&str)]=&[(\"LEGITIMACY_CODEX_GRAPH_COMMIT\",\"examples/graphs/codex-graph.json\",),(\"LEGITIMACY_CLAUDE_AGENT_SDK_GRAPH_COMMIT\",\"examples/graphs/claude-agent-sdk-graph.json\",),(\"LEGITIMACY_CLAUDE_CODE_GRAPH_COMMIT\",\"examples/graphs/claude-code-graph.json\",),];";
    if compact.matches(expected_fixtures).count() != 1 {
        return Err(BUILD_ROUTE_ERROR);
    }
    for required in [
        "println!(\"cargo:rerun-if-changed=build.rs\")",
        "println!(\"cargo:rerun-if-changed=.git/HEAD\")",
        "println!(\"cargo:rerun-if-changed=.git/index\")",
        "println!(\"cargo:rerun-if-changed=.git/refs/heads/master\")",
        "println!(\"cargo:rerun-if-changed=src\")",
        "println!(\"cargo:rustc-env=LEGITIMACY_BUILD_GIT_COMMIT={build_commit}\")",
        "println!(\"cargo:rerun-if-changed={fixture_path}\")",
        "println!(\"cargo:rustc-env={env_var}={commit}\")",
    ] {
        if compact.matches(required).count() != 1 {
            return Err(BUILD_ROUTE_ERROR);
        }
    }
    let mut parser = rust_parser();
    let tree = parser.parse(source, None).ok_or(BUILD_ROUTE_ERROR)?;
    if tree.root_node().has_error() {
        return Err(BUILD_ROUTE_ERROR);
    }
    let calls = call_name_counts(tree.root_node(), source.as_bytes());
    if calls
        != BTreeMap::from([
            ("Command::new".to_string(), 1),
            ("Err".to_string(), 3),
            ("Ok".to_string(), 2),
            ("String::from_utf8".to_string(), 1),
            ("dirty_suffix".to_string(), 2),
            ("env::var".to_string(), 1),
            ("git_output".to_string(), 3),
            ("git_path_is_dirty".to_string(), 2),
            ("macro:format".to_string(), 3),
            ("macro:println".to_string(), 8),
            ("method:args".to_string(), 1),
            ("method:current_dir".to_string(), 1),
            ("method:is_empty".to_string(), 3),
            ("method:map".to_string(), 1),
            ("method:map_err".to_string(), 3),
            ("method:output".to_string(), 1),
            ("method:success".to_string(), 1),
            ("method:to_string".to_string(), 5),
            ("method:trim".to_string(), 1),
        ])
        || source.matches("cargo:").count() != 8
        || direct_call_argument_profiles(source, "env::var").map_err(|_| BUILD_ROUTE_ERROR)?
            != vec![compact_profile(&["\"CARGO_MANIFEST_DIR\""])]
        || direct_call_argument_profiles(source, "Command::new").map_err(|_| BUILD_ROUTE_ERROR)?
            != vec![compact_profile(&["\"git\""])]
        || direct_call_argument_profiles(source, "git_output").map_err(|_| BUILD_ROUTE_ERROR)?
            != vec![
                compact_profile(&["&manifest_dir", "&[\"rev-parse\",\"--short=7\",\"HEAD\"]"]),
                compact_profile(&[
                    "&manifest_dir",
                    "&[\"log\",\"-n\",\"1\",\"--format=%H\",\"--\",fixture_path]",
                ]),
                compact_profile(&["manifest_dir", "&[\"status\",\"--porcelain\",\"--\",path]"]),
            ]
        || direct_call_argument_profiles(source, "git_path_is_dirty")
            .map_err(|_| BUILD_ROUTE_ERROR)?
            != vec![
                compact_profile(&["&manifest_dir", "\"src/\""]),
                compact_profile(&["&manifest_dir", "fixture_path"]),
            ]
    {
        return Err(BUILD_ROUTE_ERROR);
    }
    Ok(())
}
