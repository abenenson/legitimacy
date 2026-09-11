use super::compiler_protocol::{
    CargoProtocolEvidence, CargoRecord, ProtocolFailure, UniqueValue, parse_cargo_stream,
    parse_unique,
};
use super::module_graph::normalize_repository_path;
use super::selected_closure::{CargoArtifactRecord, ClosureViolation};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

pub(super) struct CanonicalInputs {
    pub(super) binary: Vec<String>,
    pub(super) library: Vec<String>,
    pub(super) canonical_object: String,
    pub(super) expected_library_root: String,
    pub(super) expected_binary_root: String,
}

pub(super) fn parse_canonical_inputs(
    value: &serde_json::Value,
) -> Result<CanonicalInputs, ClosureViolation> {
    let contract = value
        .get("cargo_contract")
        .and_then(serde_json::Value::as_object)
        .ok_or(ClosureViolation::CompilerClosure)?;
    let compiler = contract
        .get("compiler_read_inputs")
        .and_then(serde_json::Value::as_object)
        .ok_or(ClosureViolation::CompilerClosure)?;
    let binary = json_paths(
        compiler
            .get("binary")
            .ok_or(ClosureViolation::CompilerClosure)?,
    )?;
    let library = json_paths(
        compiler
            .get("library")
            .ok_or(ClosureViolation::CompilerClosure)?,
    )?;
    let canonical_object = contract
        .get("canonical_object")
        .and_then(serde_json::Value::as_str)
        .ok_or(ClosureViolation::CompilerClosure)?
        .to_string();
    let expected_library_root = contract
        .get("library_target")
        .and_then(|target| target.get("path"))
        .and_then(serde_json::Value::as_str)
        .ok_or(ClosureViolation::CompilerClosure)?
        .to_string();
    let selected_binaries = contract
        .get("binary_targets")
        .and_then(serde_json::Value::as_array)
        .ok_or(ClosureViolation::CompilerClosure)?
        .iter()
        .filter(|target| {
            target.get("name").and_then(serde_json::Value::as_str) == Some("legitimacy")
        })
        .collect::<Vec<_>>();
    if selected_binaries.len() != 1 {
        return Err(ClosureViolation::CompilerClosure);
    }
    let expected_binary_root = selected_binaries[0]
        .get("path")
        .and_then(serde_json::Value::as_str)
        .ok_or(ClosureViolation::CompilerClosure)?
        .to_string();
    Ok(CanonicalInputs {
        binary,
        library,
        canonical_object,
        expected_library_root,
        expected_binary_root,
    })
}

fn json_paths(value: &serde_json::Value) -> Result<Vec<String>, ClosureViolation> {
    value
        .as_array()
        .ok_or(ClosureViolation::CompilerClosure)?
        .iter()
        .map(|path| {
            path.as_str()
                .map(str::to_string)
                .ok_or(ClosureViolation::CompilerClosure)
        })
        .collect()
}

pub(super) fn selected_cargo_artifacts(
    root: &Path,
) -> Result<(CargoArtifactRecord, CargoArtifactRecord), ClosureViolation> {
    parse_selected_artifacts(root, selected_cargo_messages(root)?)
}

pub(super) fn selected_cargo_messages(
    root: &Path,
) -> Result<&'static [serde_json::Value], ClosureViolation> {
    static MESSAGES: OnceLock<Result<Vec<serde_json::Value>, ClosureViolation>> = OnceLock::new();
    let expected = std::fs::canonicalize(env!("CARGO_MANIFEST_DIR"))
        .map_err(|_| ClosureViolation::ArtifactMultiplicity)?;
    let supplied =
        std::fs::canonicalize(root).map_err(|_| ClosureViolation::ArtifactMultiplicity)?;
    if supplied != expected {
        return Err(ClosureViolation::ArtifactMultiplicity);
    }
    MESSAGES
        .get_or_init(|| execute_selected_cargo(root))
        .as_ref()
        .map(Vec::as_slice)
        .map_err(Clone::clone)
}

fn execute_selected_cargo(root: &Path) -> Result<Vec<serde_json::Value>, ClosureViolation> {
    let output = Command::new(env!("CARGO"))
        .args([
            "build",
            "--locked",
            "--bin",
            "legitimacy",
            "--message-format=json-render-diagnostics",
        ])
        .current_dir(root)
        .output()
        .map_err(|_| ClosureViolation::ArtifactMultiplicity)?;
    if !output.status.success() {
        return Err(ClosureViolation::ArtifactMultiplicity);
    }
    let stdout =
        String::from_utf8(output.stdout).map_err(|_| ClosureViolation::ArtifactMultiplicity)?;
    stdout
        .lines()
        .map(|line| serde_json::from_str(line).map_err(|_| ClosureViolation::ArtifactMultiplicity))
        .collect()
}

fn parse_selected_artifacts(
    root: &Path,
    messages: &[serde_json::Value],
) -> Result<(CargoArtifactRecord, CargoArtifactRecord), ClosureViolation> {
    let manifest = std::fs::canonicalize(root.join("Cargo.toml"))
        .map_err(|_| ClosureViolation::ArtifactMultiplicity)?;
    let mut libraries = Vec::new();
    let mut binaries = Vec::new();
    for message in messages {
        if message["reason"] != "compiler-artifact"
            || Path::new(message["manifest_path"].as_str().unwrap_or("")) != manifest
        {
            continue;
        }
        let profile_test = message["profile"]["test"]
            .as_bool()
            .ok_or(ClosureViolation::ArtifactIdentity)?;
        let target = &message["target"];
        let kinds = target["kind"]
            .as_array()
            .ok_or(ClosureViolation::ArtifactIdentity)?;
        let name = target["name"]
            .as_str()
            .ok_or(ClosureViolation::ArtifactIdentity)?;
        let kind = match kinds.as_slice() {
            [kind] if kind == "lib" && name == "legitimacy" && !profile_test => "lib",
            [kind] if kind == "bin" && name == "legitimacy" && !profile_test => "bin",
            _ => continue,
        };
        let src_path = artifact_repository_path(
            root,
            target["src_path"]
                .as_str()
                .ok_or(ClosureViolation::ArtifactRoot)?,
        )?;
        let filenames = message["filenames"]
            .as_array()
            .ok_or(ClosureViolation::ArtifactIdentity)?
            .iter()
            .map(|path| {
                path.as_str()
                    .map(|path| Path::new(path).to_string_lossy().into_owned())
                    .ok_or(ClosureViolation::ArtifactIdentity)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let features = message["features"]
            .as_array()
            .ok_or(ClosureViolation::ArtifactIdentity)?
            .iter()
            .map(|feature| {
                feature
                    .as_str()
                    .map(str::to_string)
                    .ok_or(ClosureViolation::ArtifactIdentity)
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        let dep_info = if kind == "lib" {
            library_dep_info(&filenames)?
        } else {
            let executable = message["executable"]
                .as_str()
                .ok_or(ClosureViolation::ArtifactIdentity)?;
            matching_binary_dep_info(Path::new(executable))?
        };
        let raw_dep_info_entries = read_raw_dep_info(&dep_info)?;
        let normalized_dep_info_entries = raw_dep_info_entries
            .iter()
            .map(|path| normalize_dep_info_entry(root, path))
            .collect::<Result<Vec<_>, _>>()?;
        let artifact = CargoArtifactRecord {
            target_name: name.to_string(),
            target_kind: kind.to_string(),
            src_path,
            profile_test,
            features,
            filenames,
            raw_dep_info_entries,
            normalized_dep_info_entries,
        };
        if kind == "lib" {
            libraries.push(artifact);
        } else {
            binaries.push(artifact);
        }
    }
    if libraries.len() != 1 || binaries.len() != 1 {
        return Err(ClosureViolation::ArtifactMultiplicity);
    }
    Ok((libraries.remove(0), binaries.remove(0)))
}

fn normalize_dep_info_entry(root: &Path, path: &str) -> Result<String, ClosureViolation> {
    let canonical_root =
        std::fs::canonicalize(root).map_err(|_| ClosureViolation::CompilerClosure)?;
    let path = Path::new(path);
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        canonical_root.join(path)
    };
    let relative = absolute
        .strip_prefix(&canonical_root)
        .map_err(|_| ClosureViolation::CompilerClosure)?;
    normalize_repository_path(relative).map_err(|_| ClosureViolation::CompilerClosure)
}

fn artifact_repository_path(root: &Path, path: &str) -> Result<String, ClosureViolation> {
    let root = std::fs::canonicalize(root).map_err(|_| ClosureViolation::ArtifactRoot)?;
    let path = Path::new(path);
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        root.join(path)
    };
    let relative = absolute
        .strip_prefix(&root)
        .map_err(|_| ClosureViolation::ArtifactRoot)?;
    normalize_repository_path(relative).map_err(|_| ClosureViolation::ArtifactRoot)
}

fn library_dep_info(filenames: &[String]) -> Result<PathBuf, ClosureViolation> {
    let candidates = filenames
        .iter()
        .filter_map(|filename| {
            let path = Path::new(filename);
            (path.extension().and_then(|extension| extension.to_str()) == Some("rlib"))
                .then(|| {
                    let stem = path.file_stem()?.to_str()?.strip_prefix("lib")?;
                    Some(path.with_file_name(format!("{stem}.d")))
                })
                .flatten()
        })
        .collect::<Vec<_>>();
    if candidates.len() != 1 {
        return Err(ClosureViolation::ArtifactIdentity);
    }
    Ok(candidates[0].clone())
}

fn matching_binary_dep_info(executable: &Path) -> Result<PathBuf, ClosureViolation> {
    use std::os::unix::fs::MetadataExt;

    let metadata = std::fs::metadata(executable).map_err(|_| ClosureViolation::ArtifactIdentity)?;
    let deps = executable
        .parent()
        .ok_or(ClosureViolation::ArtifactIdentity)?
        .join("deps");
    let mut matches = Vec::new();
    for entry in std::fs::read_dir(deps).map_err(|_| ClosureViolation::ArtifactIdentity)? {
        let path = entry
            .map_err(|_| ClosureViolation::ArtifactIdentity)?
            .path();
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if !name.starts_with("legitimacy-") || path.extension().is_some() {
            continue;
        }
        let candidate = std::fs::metadata(&path).map_err(|_| ClosureViolation::ArtifactIdentity)?;
        if candidate.dev() == metadata.dev() && candidate.ino() == metadata.ino() {
            matches.push(path.with_extension("d"));
        }
    }
    if matches.len() != 1 {
        return Err(ClosureViolation::ArtifactIdentity);
    }
    Ok(matches.remove(0))
}

fn read_raw_dep_info(path: &Path) -> Result<Vec<String>, ClosureViolation> {
    let dep_info = std::fs::read_to_string(path).map_err(|_| ClosureViolation::CompilerClosure)?;
    let first_rule = dep_info
        .lines()
        .next()
        .ok_or(ClosureViolation::CompilerClosure)?;
    let (_, dependencies) = first_rule
        .split_once(": ")
        .ok_or(ClosureViolation::CompilerClosure)?;
    let entries = dependencies
        .split_ascii_whitespace()
        .map(str::to_string)
        .collect::<Vec<_>>();
    if entries.is_empty() || entries.iter().any(|entry| entry.contains('\\')) {
        return Err(ClosureViolation::CompilerClosure);
    }
    let mut spellings = BTreeSet::new();
    if entries.iter().any(|entry| !spellings.insert(entry.clone())) {
        return Err(ClosureViolation::DuplicateDepInfo);
    }
    Ok(entries)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AssociationFailure {
    CargoProtocol,
    ArtifactMultiplicity,
    ArtifactIdentity,
    ArtifactRoot,
}

impl From<ProtocolFailure> for AssociationFailure {
    fn from(_: ProtocolFailure) -> Self {
        Self::CargoProtocol
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MetadataPackageMap {
    pub(crate) raw: Vec<u8>,
    pub(crate) manifests: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct AssociatedCargoRecords {
    pub(crate) package_id: String,
    pub(crate) manifest_path: String,
    pub(crate) build_script: CargoRecord,
    pub(crate) custom_build: CargoRecord,
    pub(crate) library: CargoRecord,
    pub(crate) binary: CargoRecord,
}

pub(crate) fn parse_metadata_package_map(
    bytes: &[u8],
) -> Result<MetadataPackageMap, AssociationFailure> {
    if bytes.is_empty() || bytes.contains(&b'\r') {
        return Err(AssociationFailure::CargoProtocol);
    }
    let value = parse_unique(bytes)?;
    let root = value.object()?;
    exact_metadata_keys(
        root,
        &[
            "build_directory",
            "metadata",
            "packages",
            "resolve",
            "target_directory",
            "version",
            "workspace_default_members",
            "workspace_members",
            "workspace_root",
        ],
    )?;
    match root.get("version") {
        Some(UniqueValue::Number(value)) if value == "1" => {}
        _ => return Err(AssociationFailure::CargoProtocol),
    }
    for name in ["build_directory", "target_directory", "workspace_root"] {
        metadata_field(root, name)?.string()?;
    }
    match metadata_field(root, "metadata")? {
        UniqueValue::Null | UniqueValue::Object(_) => {}
        _ => return Err(AssociationFailure::CargoProtocol),
    }
    if !matches!(metadata_field(root, "resolve")?, UniqueValue::Null) {
        return Err(AssociationFailure::CargoProtocol);
    }
    for name in ["workspace_default_members", "workspace_members"] {
        string_values(metadata_field(root, name)?)?;
    }
    let mut manifests = BTreeMap::new();
    for package in metadata_field(root, "packages")?.array()? {
        let package = package.object()?;
        exact_metadata_keys(
            package,
            &[
                "authors",
                "categories",
                "default_run",
                "dependencies",
                "description",
                "documentation",
                "edition",
                "features",
                "homepage",
                "id",
                "keywords",
                "license",
                "license_file",
                "links",
                "manifest_path",
                "metadata",
                "name",
                "publish",
                "readme",
                "repository",
                "rust_version",
                "source",
                "targets",
                "version",
            ],
        )?;
        let package_id = metadata_field(package, "id")?.string()?.to_string();
        let manifest = metadata_field(package, "manifest_path")?
            .string()?
            .to_string();
        if package_id.is_empty()
            || !manifest.starts_with('/')
            || manifests.insert(package_id, manifest).is_some()
        {
            return Err(AssociationFailure::CargoProtocol);
        }
        for target in metadata_field(package, "targets")?.array()? {
            validate_metadata_target(target)?;
        }
    }
    if manifests.is_empty() {
        return Err(AssociationFailure::CargoProtocol);
    }
    Ok(MetadataPackageMap {
        raw: bytes.to_vec(),
        manifests,
    })
}

pub(crate) fn associate_current_package(
    metadata: &MetadataPackageMap,
    cargo: &CargoProtocolEvidence,
    package_id: &str,
    canonical_source_root: &str,
) -> Result<AssociatedCargoRecords, AssociationFailure> {
    let manifest = metadata
        .manifests
        .get(package_id)
        .ok_or(AssociationFailure::ArtifactIdentity)?;
    let expected_manifest = format!("{canonical_source_root}/Cargo.toml");
    if manifest != &expected_manifest {
        return Err(AssociationFailure::ArtifactRoot);
    }
    let mut build_scripts = Vec::new();
    let mut custom_builds = Vec::new();
    let mut libraries = Vec::new();
    let mut binaries = Vec::new();
    for record in &cargo.records {
        match record {
            CargoRecord::BuildScriptExecuted {
                package_id: record_package,
                ..
            } if record_package == package_id => build_scripts.push(record.clone()),
            CargoRecord::CompilerArtifact {
                package_id: record_package,
                manifest_path,
                target,
                profile,
                fresh,
                ..
            } if record_package == package_id => {
                if manifest_path != manifest || *fresh || profile.test {
                    return Err(AssociationFailure::ArtifactIdentity);
                }
                let expected_root = match target.kinds.as_slice() {
                    [kind] if kind == "custom-build" => {
                        custom_builds.push(record.clone());
                        format!("{canonical_source_root}/build.rs")
                    }
                    [kind] if kind == "lib" && target.name == "legitimacy" => {
                        libraries.push(record.clone());
                        format!("{canonical_source_root}/src/lib.rs")
                    }
                    [kind] if kind == "bin" && target.name == "legitimacy" => {
                        binaries.push(record.clone());
                        format!("{canonical_source_root}/cli/main.rs")
                    }
                    _ => return Err(AssociationFailure::ArtifactIdentity),
                };
                if target.src_path != expected_root || target.edition != "2024" {
                    return Err(AssociationFailure::ArtifactRoot);
                }
            }
            _ => {}
        }
    }
    if build_scripts.len() != 1
        || custom_builds.len() != 1
        || libraries.len() != 1
        || binaries.len() != 1
    {
        return Err(AssociationFailure::ArtifactMultiplicity);
    }
    Ok(AssociatedCargoRecords {
        package_id: package_id.to_string(),
        manifest_path: manifest.clone(),
        build_script: build_scripts.remove(0),
        custom_build: custom_builds.remove(0),
        library: libraries.remove(0),
        binary: binaries.remove(0),
    })
}

fn validate_metadata_target(value: &UniqueValue) -> Result<(), AssociationFailure> {
    let target = value.object()?;
    exact_metadata_keys(
        target,
        &[
            "crate_types",
            "doc",
            "doctest",
            "edition",
            "kind",
            "name",
            "src_path",
            "test",
        ],
    )?;
    string_values(metadata_field(target, "crate_types")?)?;
    string_values(metadata_field(target, "kind")?)?;
    for name in ["edition", "name", "src_path"] {
        metadata_field(target, name)?.string()?;
    }
    for name in ["doc", "doctest", "test"] {
        metadata_field(target, name)?.bool()?;
    }
    Ok(())
}

fn metadata_field<'a>(
    object: &'a BTreeMap<String, UniqueValue>,
    name: &str,
) -> Result<&'a UniqueValue, AssociationFailure> {
    object.get(name).ok_or(AssociationFailure::CargoProtocol)
}

fn exact_metadata_keys(
    object: &BTreeMap<String, UniqueValue>,
    expected: &[&str],
) -> Result<(), AssociationFailure> {
    let actual = object.keys().map(String::as_str).collect::<BTreeSet<_>>();
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    if actual == expected {
        Ok(())
    } else {
        Err(AssociationFailure::CargoProtocol)
    }
}

fn string_values(value: &UniqueValue) -> Result<Vec<String>, AssociationFailure> {
    value
        .array()?
        .iter()
        .map(|value| {
            value
                .string()
                .map(str::to_string)
                .map_err(AssociationFailure::from)
        })
        .collect()
}

pub(crate) fn assert_package_and_artifact_association_is_exact() {
    let metadata = br#"{"packages":[{"name":"legitimacy","version":"1.0.0","id":"path+file:///case#legitimacy@1.0.0","license":null,"license_file":null,"description":null,"source":null,"dependencies":[],"targets":[{"kind":["lib"],"crate_types":["lib"],"name":"legitimacy","src_path":"/case/src/lib.rs","edition":"2024","doc":true,"doctest":true,"test":true},{"kind":["bin"],"crate_types":["bin"],"name":"legitimacy","src_path":"/case/cli/main.rs","edition":"2024","doc":true,"doctest":false,"test":true},{"kind":["custom-build"],"crate_types":["bin"],"name":"build-script-build","src_path":"/case/build.rs","edition":"2024","doc":false,"doctest":false,"test":false}],"features":{},"manifest_path":"/case/Cargo.toml","metadata":{},"publish":[],"authors":[],"categories":[],"default_run":null,"rust_version":null,"keywords":[],"readme":null,"repository":null,"homepage":null,"documentation":null,"edition":"2024","links":null}],"workspace_members":["path+file:///case#legitimacy@1.0.0"],"workspace_default_members":["path+file:///case#legitimacy@1.0.0"],"resolve":null,"target_directory":"/target","build_directory":"/target","version":1,"workspace_root":"/case","metadata":null}"#;
    let map = parse_metadata_package_map(metadata).unwrap();
    let object_metadata = String::from_utf8(metadata.to_vec())
        .unwrap()
        .strip_suffix("\"metadata\":null}")
        .unwrap()
        .to_string()
        + "\"metadata\":{}}";
    assert!(parse_metadata_package_map(object_metadata.as_bytes()).is_ok());
    let invalid_metadata = String::from_utf8(metadata.to_vec())
        .unwrap()
        .strip_suffix("\"metadata\":null}")
        .unwrap()
        .to_string()
        + "\"metadata\":[]}";
    assert_eq!(
        parse_metadata_package_map(invalid_metadata.as_bytes()),
        Err(AssociationFailure::CargoProtocol)
    );
    let target = |kind: &str, crate_type: &str, name: &str, path: &str| {
        format!(
            "{{\"kind\":[\"{kind}\"],\"crate_types\":[\"{crate_type}\"],\"name\":\"{name}\",\"src_path\":\"{path}\",\"edition\":\"2024\",\"doc\":false,\"doctest\":false,\"test\":false}}"
        )
    };
    let profile = "{\"opt_level\":\"0\",\"debuginfo\":2,\"debug_assertions\":true,\"overflow_checks\":true,\"test\":false}";
    let artifact = |target: String, filenames: &str, executable: &str| {
        format!(
            "{{\"reason\":\"compiler-artifact\",\"package_id\":\"path+file:///case#legitimacy@1.0.0\",\"manifest_path\":\"/case/Cargo.toml\",\"target\":{target},\"profile\":{profile},\"features\":[],\"filenames\":{filenames},\"executable\":{executable},\"fresh\":false}}\n"
        )
    };
    let stream = format!(
        "{}{}{}{}{}",
        artifact(
            target(
                "custom-build",
                "bin",
                "build-script-build",
                "/case/build.rs"
            ),
            "[\"/target/build-script-build\"]",
            "\"/target/build-script-build\""
        ),
        "{\"reason\":\"build-script-executed\",\"package_id\":\"path+file:///case#legitimacy@1.0.0\",\"linked_libs\":[],\"linked_paths\":[],\"cfgs\":[],\"env\":[],\"out_dir\":\"/target/build/out\"}\n",
        artifact(
            target("lib", "lib", "legitimacy", "/case/src/lib.rs"),
            "[\"/target/liblegitimacy.rlib\",\"/target/liblegitimacy.rmeta\"]",
            "null"
        ),
        artifact(
            target("bin", "bin", "legitimacy", "/case/cli/main.rs"),
            "[\"/target/legitimacy\"]",
            "\"/target/legitimacy\""
        ),
        "{\"reason\":\"build-finished\",\"success\":true}\n"
    );
    let cargo = parse_cargo_stream(stream.as_bytes(), true).unwrap();
    let associated =
        associate_current_package(&map, &cargo, "path+file:///case#legitimacy@1.0.0", "/case")
            .unwrap();
    assert_eq!(associated.manifest_path, "/case/Cargo.toml");

    let duplicate = format!(
        "{}{}",
        stream
            .strip_suffix("{\"reason\":\"build-finished\",\"success\":true}\n")
            .unwrap(),
        stream
    );
    assert_eq!(
        associate_current_package(
            &map,
            &parse_cargo_stream(duplicate.as_bytes(), true).unwrap(),
            "path+file:///case#legitimacy@1.0.0",
            "/case"
        ),
        Err(AssociationFailure::ArtifactMultiplicity)
    );
}
