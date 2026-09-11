use super::*;
use crate::repository_object::read_repository_file;

const BUILD_ROUTE_ERROR: &str = "build-route";

fn verify_build_input_contract(build: &serde_json::Value) -> Result<(), &'static str> {
    let contract = build["cargo_contract"]
        .as_object()
        .ok_or(BUILD_ROUTE_ERROR)?;
    if contract.keys().map(String::as_str).collect::<BTreeSet<_>>()
        != BTreeSet::from([
            "automatic_discovery",
            "binary_targets",
            "bound_inputs_sha256",
            "build_script",
            "canonical_object",
            "compiler_read_inputs",
            "library_target",
            "manifest",
            "normative_contract",
            "repository_configuration",
            "selected_noncompiler_inputs",
            "test_only_cli_rust_sources",
        ])
        || contract["manifest"].as_str() != Some("Cargo.toml")
        || contract["build_script"].as_str() != Some("build.rs")
        || contract["canonical_object"].as_str() != Some(BUILD_INPUT_PATH)
        || contract["normative_contract"].as_str() != Some("docs/codex-exec-v0-adapter.md")
        || !contract["bound_inputs_sha256"]
            .as_str()
            .is_some_and(valid_sha256)
        || contract["automatic_discovery"] != serde_json::json!({"lib": false, "bin": false})
        || contract["library_target"]
            != serde_json::json!({"name": "legitimacy", "path": "src/lib.rs"})
        || contract["binary_targets"]
            != serde_json::json!([
                {"name": "legitimacy", "path": "cli/main.rs"},
                {
                    "name": "legitimacy-audit-agent",
                    "path": "src/bin/legitimacy-audit-agent.rs"
                },
                {
                    "name": "import_codex_observed_runtime",
                    "path": "src/bin/import_codex_observed_runtime.rs"
                },
                {
                    "name": "legitimacy-codex-capture-v0",
                    "path": "src/bin/legitimacy-codex-capture-v0.rs"
                },
                {
                    "name": "legitimacy-executed-composition",
                    "path": "src/bin/legitimacy-executed-composition.rs"
                }
            ])
    {
        return Err(BUILD_ROUTE_ERROR);
    }
    let compiler_inputs = contract["compiler_read_inputs"]
        .as_object()
        .ok_or(BUILD_ROUTE_ERROR)?;
    if compiler_inputs
        .keys()
        .map(String::as_str)
        .collect::<BTreeSet<_>>()
        != BTreeSet::from(["binary", "library"])
    {
        return Err(BUILD_ROUTE_ERROR);
    }
    let noncompiler_inputs = contract["selected_noncompiler_inputs"]
        .as_object()
        .ok_or(BUILD_ROUTE_ERROR)?;
    if noncompiler_inputs
        .keys()
        .map(String::as_str)
        .collect::<BTreeSet<_>>()
        != BTreeSet::from(["build_script", "cargo", "review_contract"])
        || noncompiler_inputs["cargo"] != serde_json::json!(["Cargo.lock", "Cargo.toml"])
        || noncompiler_inputs["build_script"]
            != serde_json::json!([
                "build.rs",
                "examples/graphs/claude-agent-sdk-graph.json",
                "examples/graphs/claude-code-graph.json",
                "examples/graphs/codex-graph.json"
            ])
        || noncompiler_inputs["review_contract"]
            != serde_json::json!(["docs/codex-exec-v0-adapter.md"])
    {
        return Err(BUILD_ROUTE_ERROR);
    }
    let configuration = contract["repository_configuration"]
        .as_object()
        .ok_or(BUILD_ROUTE_ERROR)?;
    if configuration
        .keys()
        .map(String::as_str)
        .collect::<BTreeSet<_>>()
        != BTreeSet::from(["classified_absent", "present"])
        || configuration["present"] != serde_json::json!([])
        || configuration["classified_absent"]
            != serde_json::json!([
                ".cargo/config",
                ".cargo/config.toml",
                "rust-toolchain",
                "rust-toolchain.toml"
            ])
    {
        return Err(BUILD_ROUTE_ERROR);
    }
    let mut all_paths = BTreeSet::new();
    for paths in [
        &compiler_inputs["binary"],
        &compiler_inputs["library"],
        &noncompiler_inputs["cargo"],
        &noncompiler_inputs["build_script"],
        &noncompiler_inputs["review_contract"],
        &configuration["present"],
    ] {
        let paths = paths.as_array().ok_or(BUILD_ROUTE_ERROR)?;
        let strings = paths
            .iter()
            .map(|path| path.as_str().ok_or(BUILD_ROUTE_ERROR))
            .collect::<Result<Vec<_>, _>>()?;
        if strings.windows(2).any(|window| window[0] >= window[1])
            || strings.iter().any(|path| {
                Path::new(path).is_absolute()
                    || Path::new(path)
                        .components()
                        .any(|component| !matches!(component, std::path::Component::Normal(_)))
            })
            || strings
                .iter()
                .any(|path| !all_paths.insert((*path).to_string()))
        {
            return Err(BUILD_ROUTE_ERROR);
        }
    }
    let tests = contract["test_only_cli_rust_sources"]
        .as_array()
        .ok_or(BUILD_ROUTE_ERROR)?;
    let tests = tests
        .iter()
        .map(|path| path.as_str().ok_or(BUILD_ROUTE_ERROR))
        .collect::<Result<Vec<_>, _>>()?;
    if tests.windows(2).any(|window| window[0] >= window[1])
        || tests.iter().any(|path| !path.ends_with(".rs"))
    {
        return Err(BUILD_ROUTE_ERROR);
    }
    Ok(())
}

fn valid_sha256(value: &str) -> bool {
    value.len() == 71
        && value.starts_with("sha256:")
        && value[7..]
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

#[derive(Clone, Debug)]
struct SelectedBuildEvidence {
    binary_inputs: BTreeSet<String>,
    library_inputs: BTreeSet<String>,
    build_script_output: String,
    build_script_env: Vec<(String, String)>,
    build_script_cfgs: Vec<String>,
    build_script_linked_libs: Vec<String>,
    build_script_linked_paths: Vec<String>,
    build_script_out_dir: PathBuf,
    selected_packages: BTreeSet<(String, String)>,
}

fn selected_build_evidence(root: &Path) -> Result<SelectedBuildEvidence, &'static str> {
    let messages = connected_selected_cargo_messages(root)?;
    let closure = selected_rust_closure(root).map_err(|_| BUILD_ROUTE_ERROR)?;
    let mut build_script = None;
    let mut selected_packages = BTreeSet::new();
    for message in messages {
        if message["reason"] == "compiler-artifact" {
            if let Some(package) = package_identity(message["package_id"].as_str().unwrap_or("")) {
                selected_packages.insert(package);
            }
        } else if message["reason"] == "build-script-executed"
            && Path::new(message["package_id"].as_str().unwrap_or(""))
                .to_string_lossy()
                .contains("legitimacy")
        {
            build_script = Some(message);
        }
    }
    let build_script = build_script.ok_or(BUILD_ROUTE_ERROR)?;
    let out_dir = PathBuf::from(build_script["out_dir"].as_str().ok_or(BUILD_ROUTE_ERROR)?);
    let output_path = out_dir.parent().ok_or(BUILD_ROUTE_ERROR)?.join("output");
    let build_script_output =
        std::fs::read_to_string(output_path).map_err(|_| BUILD_ROUTE_ERROR)?;
    let build_script_env = build_script["env"]
        .as_array()
        .ok_or(BUILD_ROUTE_ERROR)?
        .iter()
        .map(|entry| {
            let pair = entry.as_array().ok_or(BUILD_ROUTE_ERROR)?;
            if pair.len() != 2 {
                return Err(BUILD_ROUTE_ERROR);
            }
            Ok((
                pair[0].as_str().ok_or(BUILD_ROUTE_ERROR)?.to_string(),
                pair[1].as_str().ok_or(BUILD_ROUTE_ERROR)?.to_string(),
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SelectedBuildEvidence {
        binary_inputs: closure.binary_paths().clone(),
        library_inputs: closure.library_paths().clone(),
        build_script_output,
        build_script_env,
        build_script_cfgs: json_string_array(&build_script["cfgs"])?,
        build_script_linked_libs: json_string_array(&build_script["linked_libs"])?,
        build_script_linked_paths: json_string_array(&build_script["linked_paths"])?,
        build_script_out_dir: out_dir,
        selected_packages,
    })
}

fn package_identity(package_id: &str) -> Option<(String, String)> {
    let package = package_id.rsplit('#').next()?;
    let (name, version) = package.rsplit_once('@')?;
    Some((name.to_string(), version.to_string()))
}

fn json_string_array(value: &serde_json::Value) -> Result<Vec<String>, &'static str> {
    value
        .as_array()
        .ok_or(BUILD_ROUTE_ERROR)?
        .iter()
        .map(|value| value.as_str().map(str::to_string).ok_or(BUILD_ROUTE_ERROR))
        .collect()
}

pub(crate) fn dep_info_inputs(
    root: &Path,
    dep_info: &Path,
) -> Result<BTreeSet<String>, &'static str> {
    let dep_info = std::fs::read_to_string(dep_info).map_err(|_| BUILD_ROUTE_ERROR)?;
    let first_rule = dep_info.lines().next().ok_or(BUILD_ROUTE_ERROR)?;
    let (_, dependencies) = first_rule.split_once(": ").ok_or(BUILD_ROUTE_ERROR)?;
    let root = std::fs::canonicalize(root).map_err(|_| BUILD_ROUTE_ERROR)?;
    dependencies
        .split_ascii_whitespace()
        .map(|dependency| {
            if dependency.contains('\\') {
                return Err(BUILD_ROUTE_ERROR);
            }
            let dependency = Path::new(dependency);
            let absolute = if dependency.is_absolute() {
                normalize(dependency)
            } else {
                normalize(&root.join(dependency))
            };
            if !absolute.starts_with(&root) {
                return Err(BUILD_ROUTE_ERROR);
            }
            let relative = relative(&root, &absolute);
            read_repository_file(&root, &relative, 64 * 1024 * 1024)?;
            Ok(relative)
        })
        .collect()
}

fn contract_role_paths(
    build: &serde_json::Value,
    role: &str,
) -> Result<BTreeSet<String>, &'static str> {
    build["cargo_contract"]["compiler_read_inputs"][role]
        .as_array()
        .ok_or(BUILD_ROUTE_ERROR)?
        .iter()
        .map(|path| path.as_str().map(str::to_string).ok_or(BUILD_ROUTE_ERROR))
        .collect()
}

fn verify_compiler_closure(
    build: &serde_json::Value,
    evidence: &SelectedBuildEvidence,
) -> Result<(), &'static str> {
    let binary = contract_role_paths(build, "binary")?;
    let mut library = contract_role_paths(build, "library")?;
    let canonical = build["cargo_contract"]["canonical_object"]
        .as_str()
        .ok_or(BUILD_ROUTE_ERROR)?;
    if !library.insert(canonical.to_string())
        || binary != evidence.binary_inputs
        || library != evidence.library_inputs
        || !binary.is_disjoint(&library)
    {
        return Err("compiler-closure");
    }
    Ok(())
}

fn verify_repository_configuration(
    root: &Path,
    build: &serde_json::Value,
) -> Result<(), &'static str> {
    let contract = &build["cargo_contract"]["repository_configuration"];
    let present = contract["present"]
        .as_array()
        .ok_or(BUILD_ROUTE_ERROR)?
        .iter()
        .map(|path| path.as_str().ok_or(BUILD_ROUTE_ERROR))
        .collect::<Result<BTreeSet<_>, _>>()?;
    let absent = contract["classified_absent"]
        .as_array()
        .ok_or(BUILD_ROUTE_ERROR)?
        .iter()
        .map(|path| path.as_str().ok_or(BUILD_ROUTE_ERROR))
        .collect::<Result<BTreeSet<_>, _>>()?;
    let actual = present
        .union(&absent)
        .filter(|path| root.join(path).is_file())
        .copied()
        .collect::<BTreeSet<_>>();
    classify_repository_configuration(&actual, &present, &absent)
}

fn classify_repository_configuration(
    actual: &BTreeSet<&str>,
    present: &BTreeSet<&str>,
    absent: &BTreeSet<&str>,
) -> Result<(), &'static str> {
    if !present.is_disjoint(absent) || actual != present {
        Err("configuration-closure")
    } else {
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq)]
enum BuildDirective {
    Rerun(String),
    RustcEnv(String, String),
}

fn parse_build_directives(output: &str) -> Result<Vec<BuildDirective>, &'static str> {
    if !output.ends_with('\n') || output.contains('\r') {
        return Err("build-effect");
    }
    output
        .lines()
        .map(|line| {
            if let Some(path) = line.strip_prefix("cargo:rerun-if-changed=") {
                if path.is_empty() {
                    return Err("build-effect");
                }
                Ok(BuildDirective::Rerun(path.to_string()))
            } else if let Some(binding) = line.strip_prefix("cargo:rustc-env=") {
                let (name, value) = binding.split_once('=').ok_or("build-effect")?;
                if name.is_empty() || value.is_empty() {
                    return Err("build-effect");
                }
                Ok(BuildDirective::RustcEnv(
                    name.to_string(),
                    value.to_string(),
                ))
            } else {
                Err("build-effect")
            }
        })
        .collect()
}

fn git_stdout(root: &Path, args: &[&str]) -> Result<String, &'static str> {
    let output = Command::new("git")
        .args(args)
        .current_dir(root)
        .output()
        .map_err(|_| "build-effect")?;
    if !output.status.success() {
        return Err("build-effect");
    }
    String::from_utf8(output.stdout)
        .map(|stdout| stdout.trim().to_string())
        .map_err(|_| "build-effect")
}

fn expected_build_directives(root: &Path) -> Result<Vec<BuildDirective>, &'static str> {
    let mut commit = git_stdout(root, &["rev-parse", "--short=7", "HEAD"])?;
    if !git_stdout(root, &["status", "--porcelain", "--", "src/"])?.is_empty() {
        commit.push_str("-dirty");
    }
    let mut expected = vec![
        BuildDirective::Rerun("build.rs".to_string()),
        BuildDirective::Rerun(".git/HEAD".to_string()),
        BuildDirective::Rerun(".git/index".to_string()),
        BuildDirective::Rerun(".git/refs/heads/master".to_string()),
        BuildDirective::Rerun("src".to_string()),
        BuildDirective::RustcEnv("LEGITIMACY_BUILD_GIT_COMMIT".to_string(), commit),
    ];
    for (name, path) in [
        (
            "LEGITIMACY_CODEX_GRAPH_COMMIT",
            "examples/graphs/codex-graph.json",
        ),
        (
            "LEGITIMACY_CLAUDE_AGENT_SDK_GRAPH_COMMIT",
            "examples/graphs/claude-agent-sdk-graph.json",
        ),
        (
            "LEGITIMACY_CLAUDE_CODE_GRAPH_COMMIT",
            "examples/graphs/claude-code-graph.json",
        ),
    ] {
        let mut commit = git_stdout(root, &["log", "-n", "1", "--format=%H", "--", path])?;
        if !git_stdout(root, &["status", "--porcelain", "--", path])?.is_empty() {
            commit.push_str("-dirty");
        }
        expected.push(BuildDirective::Rerun(path.to_string()));
        expected.push(BuildDirective::RustcEnv(name.to_string(), commit));
    }
    Ok(expected)
}

fn verify_build_script_evidence(
    root: &Path,
    evidence: &SelectedBuildEvidence,
) -> Result<(), &'static str> {
    let directives = parse_build_directives(&evidence.build_script_output)?;
    let expected = expected_build_directives(root)?;
    let env = directives
        .iter()
        .filter_map(|directive| match directive {
            BuildDirective::RustcEnv(name, value) => Some((name.clone(), value.clone())),
            BuildDirective::Rerun(_) => None,
        })
        .collect::<Vec<_>>();
    let out_dir_is_empty = std::fs::read_dir(&evidence.build_script_out_dir)
        .map_err(|_| "build-effect")?
        .next()
        .is_none();
    if directives != expected
        || env != evidence.build_script_env
        || !evidence.build_script_cfgs.is_empty()
        || !evidence.build_script_linked_libs.is_empty()
        || !evidence.build_script_linked_paths.is_empty()
        || !out_dir_is_empty
    {
        return Err("build-effect");
    }
    Ok(())
}

fn locked_package_version(lock: &str, name: &str) -> Result<String, &'static str> {
    let lock: toml::Value = toml::from_str(lock).map_err(|_| "lock-selection")?;
    let matches = lock["package"]
        .as_array()
        .ok_or("lock-selection")?
        .iter()
        .filter(|package| package["name"].as_str() == Some(name))
        .collect::<Vec<_>>();
    if matches.len() != 1 {
        return Err("lock-selection");
    }
    matches[0]["version"]
        .as_str()
        .map(str::to_string)
        .ok_or("lock-selection")
}

fn verify_selected_lock_package(
    lock: &str,
    name: &str,
    evidence: &SelectedBuildEvidence,
) -> Result<(), &'static str> {
    let version = locked_package_version(lock, name)?;
    if evidence
        .selected_packages
        .contains(&(name.to_string(), version))
    {
        Ok(())
    } else {
        Err("lock-selection")
    }
}

fn replace_manifest_once(source: &str, needle: &str, replacement: &str) -> String {
    let mutant = replace_exact_once(source, needle, replacement);
    assert!(toml::from_str::<toml::Value>(&mutant).is_ok());
    mutant
}

#[test]
fn cargo_target_and_build_script_authority_is_semantically_closed() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let manifest = std::fs::read_to_string(root.join("Cargo.toml")).unwrap();
    let build_script = std::fs::read_to_string(root.join("build.rs")).unwrap();
    let build_input = canonical_build_input();
    assert_eq!(verify_manifest_route(&manifest), Ok(()));
    assert_eq!(verify_build_script_route(&build_script), Ok(()));
    assert_eq!(verify_build_input_contract(&build_input), Ok(()));
    assert_eq!(verify_repository_configuration(root, &build_input), Ok(()));
    let evidence = selected_build_evidence(root).unwrap();
    assert_eq!(verify_compiler_closure(&build_input, &evidence), Ok(()));
    assert_eq!(verify_build_script_evidence(root, &evidence), Ok(()));
    assert_eq!(
        classify_repository_configuration(
            &BTreeSet::from([".cargo/config.toml"]),
            &BTreeSet::new(),
            &BTreeSet::from([
                ".cargo/config",
                ".cargo/config.toml",
                "rust-toolchain",
                "rust-toolchain.toml",
            ]),
        ),
        Err("configuration-closure"),
        "new repository Cargo configuration"
    );

    for (attack, mutant) in [
        (
            "main binary path substitution",
            replace_manifest_once(
                &manifest,
                "path = \"cli/main.rs\"",
                "path = \"cli/shim.rs\"",
            ),
        ),
        (
            "main binary name substitution",
            replace_manifest_once(
                &manifest,
                "name = \"legitimacy\"\npath = \"cli/main.rs\"",
                "name = \"legitimacy-shadow\"\npath = \"cli/main.rs\"",
            ),
        ),
        (
            "duplicate main binary name",
            replace_manifest_once(
                &manifest,
                "name = \"legitimacy-audit-agent\"",
                "name = \"legitimacy\"",
            ),
        ),
        (
            "alternate library root",
            replace_manifest_once(
                &manifest,
                "path = \"src/lib.rs\"",
                "path = \"src/alternate.rs\"",
            ),
        ),
        (
            "implicit binary discovery",
            replace_manifest_once(&manifest, "autobins = false", "autobins = true"),
        ),
        (
            "implicit library discovery",
            replace_manifest_once(&manifest, "autolib = false", "autolib = true"),
        ),
        (
            "target-local feature gate",
            replace_manifest_once(
                &manifest,
                "path = \"cli/main.rs\"",
                "path = \"cli/main.rs\"\nrequired-features = [\"alternate\"]",
            ),
        ),
        (
            "build script path substitution",
            replace_manifest_once(
                &manifest,
                "build = \"build.rs\"",
                "build = \"build/alternate.rs\"",
            ),
        ),
    ] {
        assert_eq!(
            verify_manifest_route(&mutant),
            Err(BUILD_ROUTE_ERROR),
            "{attack}"
        );
    }

    for (attack, addition) in [
        (
            "rustc cfg injection",
            "\nfn inject() { println!(\"cargo:rustc-cfg=alternate_route\"); }\n",
        ),
        (
            "rustc flags injection",
            "\nfn inject() { println!(\"cargo:rustc-flags=-C link-arg=alternate\"); }\n",
        ),
        (
            "link directive injection",
            "\nfn inject() { println!(\"cargo:rustc-link-arg=alternate\"); }\n",
        ),
        (
            "generated source inclusion",
            "\ninclude!(concat!(env!(\"OUT_DIR\"), \"/alternate.rs\"));\n",
        ),
        (
            "generated route environment injection",
            "\nfn inject() { println!(\"cargo:rustc-env=RUSTFLAGS=--cfg alternate\"); }\n",
        ),
        (
            "encoded byte stdout directive",
            "\nfn inject() { use std::io::{self, Write as _}; let mut hidden = io::stdout(); hidden.write_all(b\"cargo\\x3Arustc\\x2Dcfg=alternate_route\\n\").unwrap(); }\n",
        ),
        (
            "helper byte sink directive",
            "\nfn emit(bytes: &[u8]) { use std::io::Write as _; std::io::stdout().write_all(bytes).unwrap(); }\nfn inject() { emit(b\"cargo:rustc-cfg=alternate_route\\n\"); }\n",
        ),
        (
            "macro byte sink directive",
            "\nmacro_rules! emit { ($bytes:expr) => {{ use std::io::Write as _; std::io::stdout().write_all($bytes).unwrap(); }}; }\nfn inject() { emit!(b\"cargo:rustc-cfg=alternate_route\\n\"); }\n",
        ),
    ] {
        let mutant = format!("{build_script}{addition}");
        assert!(syn::parse_file(&mutant).is_ok(), "{attack}: syntax");
        assert_eq!(
            verify_build_script_route(&mutant),
            Err(BUILD_ROUTE_ERROR),
            "{attack}"
        );
    }
    let encoded_stdout = replace_exact_once(
        &replace_exact_once(
            &build_script,
            "use std::{env, process::Command};",
            "use std::{env, io::{self, Write as _}, process::Command};",
        ),
        "fn main() -> Result<(), String> {",
        "fn main() -> Result<(), String> {\n    let mut hidden = io::stdout();\n    hidden.write_all(b\"cargo\\x3Arustc\\x2Dcfg=alternate_route\\n\").map_err(|_| \"stdout failure\".to_string())?;",
    );
    assert!(syn::parse_file(&encoded_stdout).is_ok());
    assert_eq!(
        verify_build_script_route(&encoded_stdout),
        Err(BUILD_ROUTE_ERROR),
        "encoded stdout witness"
    );
    for directive in [
        "cargo:rustc-cfg=alternate_route\n",
        "cargo::rustc-cfg=alternate_route\n",
        "cargo:rustc-link-arg=alternate\n",
        "cargo:rustc-flags=-Ctarget-feature=+crt-static\n",
        "cargo:rerun-if-env-changed=ALTERNATE\n",
    ] {
        let mut output = evidence.build_script_output.clone();
        output.push_str(directive);
        assert_ne!(
            parse_build_directives(&output),
            expected_build_directives(root),
            "unpermitted directive bytes"
        );
    }

    for (attack, pointer, replacement) in [
        (
            "canonical main path substitution",
            "/cargo_contract/binary_targets/0/path",
            serde_json::json!("cli/shim.rs"),
        ),
        (
            "canonical build script substitution",
            "/cargo_contract/build_script",
            serde_json::json!("build/alternate.rs"),
        ),
        (
            "canonical automatic binary discovery",
            "/cargo_contract/automatic_discovery/bin",
            serde_json::json!(true),
        ),
        (
            "canonical target-local feature gate",
            "/cargo_contract/binary_targets/0",
            serde_json::json!({
                "name": "legitimacy",
                "path": "cli/main.rs",
                "required_features": ["alternate"]
            }),
        ),
    ] {
        let mut mutant = build_input.clone();
        *mutant.pointer_mut(pointer).unwrap() = replacement;
        assert_eq!(
            verify_build_input_contract(&mutant),
            Err(BUILD_ROUTE_ERROR),
            "{attack}"
        );
    }
    for (attack, path) in [
        (
            "duplicate compiler input",
            "src/trajectory/codex_exec_v0/source_bindings.rs",
        ),
        ("non-normalized compiler input", "src/../src/lib.rs"),
    ] {
        let mut mutant = build_input.clone();
        mutant["cargo_contract"]["compiler_read_inputs"]["library"]
            .as_array_mut()
            .unwrap()
            .push(serde_json::json!(path));
        assert_eq!(
            verify_build_input_contract(&mutant),
            Err(BUILD_ROUTE_ERROR),
            "{attack}"
        );
    }

    for (attack, source, path) in [
        (
            "dynamic non-Rust authority include",
            "include!(concat!(\"mint_\", \"escape.inc\"));",
            "src/trajectory/codex_exec_v0/mint_escape.inc",
        ),
        (
            "embedded text input",
            "const POLICY: &str = include_str!(\"embedded-policy.txt\");",
            "src/trajectory/codex_exec_v0/embedded-policy.txt",
        ),
        (
            "embedded byte input",
            "const POLICY: &[u8] = include_bytes!(\"embedded-policy.bin\");",
            "src/trajectory/codex_exec_v0/embedded-policy.bin",
        ),
    ] {
        assert!(syn::parse_file(source).is_ok(), "{attack}: syntax");
        let mut reported = evidence.library_inputs.clone();
        reported.insert(path.to_string());
        let reported = SelectedBuildEvidence {
            library_inputs: reported,
            ..evidence.clone()
        };
        assert_eq!(
            verify_compiler_closure(&build_input, &reported),
            Err("compiler-closure"),
            "{attack}: compiler-reported non-Rust input"
        );
    }
    let mut surplus = build_input.clone();
    surplus["cargo_contract"]["compiler_read_inputs"]["library"]
        .as_array_mut()
        .unwrap()
        .push(serde_json::json!("src/unread-input.txt"));
    assert_eq!(
        verify_compiler_closure(&surplus, &evidence),
        Err("compiler-closure"),
        "registered input absent from compiler closure"
    );
    let mut registry_omission = build_input.clone();
    let library = registry_omission["cargo_contract"]["compiler_read_inputs"]["library"]
        .as_array_mut()
        .unwrap();
    let omitted_index = library
        .iter()
        .position(|path| path == "schemas/trajectory-v0.schema.json")
        .unwrap();
    library.remove(omitted_index);
    assert_eq!(
        verify_compiler_closure(&registry_omission, &evidence),
        Err("compiler-closure"),
        "compiler-reported local input omitted from registry"
    );
    let mut role_drift = build_input.clone();
    let moved = role_drift["cargo_contract"]["compiler_read_inputs"]["binary"]
        .as_array_mut()
        .unwrap()
        .remove(0);
    role_drift["cargo_contract"]["compiler_read_inputs"]["library"]
        .as_array_mut()
        .unwrap()
        .push(moved);
    assert_eq!(
        verify_compiler_closure(&role_drift, &evidence),
        Err("compiler-closure"),
        "compiler input role drift"
    );
    let lock = std::fs::read_to_string(root.join("Cargo.lock")).unwrap();
    assert_eq!(
        verify_selected_lock_package(&lock, "serde_json", &evidence),
        Ok(())
    );
    let lock_mutant = replace_exact_once(
        &lock,
        "name = \"serde_json\"\nversion = \"1.0.149\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\nchecksum = \"83fc039473c5595ace860d8c4fafa220ff474b3fc6bfdb4293327f1a37e94d86\"",
        "name = \"serde_json\"\nversion = \"1.0.150\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\nchecksum = \"e8014e44b4736ed0538adeecded0fce2a272f22dc9578a7eb6b2d9993c74cfb9\"",
    );
    assert!(toml::from_str::<toml::Value>(&lock_mutant).is_ok());
    assert_eq!(
        verify_selected_lock_package(&lock_mutant, "serde_json", &evidence),
        Err("lock-selection"),
        "compatible lock update disagrees with the selected compiler artifacts"
    );

    let production = selected_rust_closure(root)
        .unwrap()
        .semantic_module_keys()
        .unwrap()
        .into_iter()
        .filter(|path| path.starts_with("cli/"))
        .collect::<BTreeSet<_>>();
    let tests = cli_test_only_rust_paths()
        .into_iter()
        .collect::<BTreeSet<_>>();
    let mut actual = production.iter().cloned().collect::<Vec<_>>();
    actual.extend(tests.iter().cloned());
    for (attack, path, source) in [
        (
            "shim includes selected main",
            "cli/shim.rs",
            "include!(\"main.rs\");",
        ),
        (
            "shim delegates selected main",
            "cli/shim.rs",
            "mod main_route { include!(\"main.rs\"); } fn main() { main_route::main(); }",
        ),
        (
            "unclassified CLI module",
            "cli/alternate.rs",
            "pub fn alternate() {}",
        ),
    ] {
        assert!(syn::parse_file(source).is_ok(), "{attack}: syntax");
        let mut mutant = actual.clone();
        mutant.push(path.to_string());
        assert_eq!(
            classify_relevant_rust_inventory(&mutant, &production, &tests),
            Err("unclassified"),
            "{attack}"
        );
    }
}

#[test]
fn compiler_dep_info_reports_dynamic_and_non_rust_inputs() {
    use std::time::{SystemTime, UNIX_EPOCH};

    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = root
        .join("target")
        .join("compiler-input-evidence")
        .join(format!("{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source = directory.join("closure.rs");
    let fragment = directory.join("mint_escape.inc");
    let text = directory.join("policy.txt");
    let bytes = directory.join("policy.bin");
    std::fs::write(
        &source,
        b"include!(concat!(\"mint_\", \"escape.inc\"));\nconst TEXT: &str = include_str!(\"policy.txt\");\nconst BYTES: &[u8] = include_bytes!(\"policy.bin\");\nfn main() { authority_fragment(); assert!(!TEXT.is_empty()); assert!(!BYTES.is_empty()); }\n",
    )
    .unwrap();
    std::fs::write(&fragment, b"fn authority_fragment() {}\n").unwrap();
    std::fs::write(&text, b"policy\n").unwrap();
    std::fs::write(&bytes, b"\0policy\n").unwrap();
    let dep_info = directory.join("closure.d");
    let emit = format!("metadata,dep-info={}", dep_info.display());
    let output = Command::new(
        std::env::var_os("RUSTC").unwrap_or_else(|| std::ffi::OsString::from("rustc")),
    )
    .args(["--edition=2024", "--emit"])
    .arg(emit)
    .arg(&source)
    .current_dir(&directory)
    .output()
    .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let evidence = std::fs::read_to_string(dep_info).unwrap();
    for input in ["mint_escape.inc", "policy.txt", "policy.bin"] {
        assert!(
            evidence
                .split_ascii_whitespace()
                .any(|field| field.trim_end_matches(':').ends_with(input)),
            "{input}: compiler dep-info"
        );
    }
    std::fs::remove_dir_all(directory).unwrap();
}
