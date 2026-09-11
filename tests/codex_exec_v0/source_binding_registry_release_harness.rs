use super::compiler_protocol::{
    CargoProtocolEvidence, EXACT_CARGO_VV, EXACT_RUSTC_VV, parse_cargo_stream,
    validate_cargo_identity, validate_compiler_identity,
};
use super::process::{ProcessResult, ProcessSupervisor};
use super::selected_artifacts::{associate_current_package, parse_metadata_package_map};
#[path = "source_binding_registry_release_lifecycle.rs"]
mod lifecycle;
use lifecycle::*;
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::fs::{self, File, OpenOptions};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};
use uuid::Uuid;

const CASE_MANIFEST_MAGIC: &str = "legitimacy.selected-authority-case-manifest.v1\n";
const CASE_IDS: [&str; 12] = [
    "baseline_selected_closure",
    "macro_generated_non_rs_overlap",
    "benign_direct_non_rs_overlap",
    "frozen_manual_sibling_escape",
    "inactive_duplicate_owner",
    "zero_candidate_fallback_owner",
    "active_linux_duplicate_owner",
    "recognized_false_duplicate_owner",
    "unrecognized_cfg_owner",
    "independent_binary_cfg",
    "clean_owner_relocation",
    "borrowed_owner_relocation",
];
const SELECTED_PACKAGE_ENTRIES: [&str; 12] = [
    "Cargo.toml",
    "Cargo.lock",
    "build.rs",
    "README.md",
    "src",
    "cli",
    "schemas",
    "examples",
    "fixtures/trajectory-composition-v0/policy.toml",
    "fixtures/executed-composition-v1/policy.json",
    "fixtures/executed-composition-v1/generated/table.json",
    "tests/fixtures/codex-exec-v0",
];
const SUITE_WALL_CAP: Duration = Duration::from_secs(1_800);
const SOURCE_BYTE_CAP: u64 = 256 * 1024 * 1024;
const CARGO_STREAM_CAP: usize = 64 * 1024 * 1024;
const METADATA_STREAM_CAP: usize = 8 * 1024 * 1024;
const IDENTITY_TIMEOUT: Duration = Duration::from_secs(10);
const SUPPORT_COMPILE_TIMEOUT: Duration = Duration::from_secs(60);
const METADATA_TIMEOUT: Duration = Duration::from_secs(60);
const EXPECTED_RUSTC_SHA256: &str =
    "8aef3883da0e960e5dc63c59a02a8be391d28a8585171aa3e380f67f18b1c1e9";
const EXPECTED_CARGO_SHA256: &str =
    "f5276e159a687a8d156e8c032644bc9c2759a8c5b8533da2141cf8d4bad84f67";

pub(crate) fn run_selected_authority_full_tree_release_gate() -> Result<(), String> {
    let deadline = SuiteDeadline::new();
    let invocation = ReleaseInvocation::from_environment()?;
    invocation.preflight(&deadline)?;

    let suite = SuiteRoot::create(&invocation.parent)?;
    let result = run_selected_cases(&invocation, &suite, &deadline);
    let cleanup = suite.finish();
    match (result, cleanup) {
        (_, Err(cleanup)) => Err(cleanup),
        (result, Ok(())) => result,
    }
}

fn run_selected_cases(
    invocation: &ReleaseInvocation,
    suite: &SuiteRoot,
    deadline: &SuiteDeadline,
) -> Result<(), String> {
    let tools = compile_tools(invocation, suite.path(), deadline)?;
    let target = suite.create_directory("target")?;
    require_empty_directory(&target)?;
    let mut package_ids = BTreeSet::new();
    let mut manifest = String::from(CASE_MANIFEST_MAGIC);
    manifest.push_str(&format!(
        "repository_head\t{}\n",
        invocation.repository_head
    ));
    manifest.push_str(&format!(
        "repository_tree\t{}\n",
        invocation.repository_tree
    ));
    manifest.push_str(&format!(
        "source_manifest_sha256\t{}\n",
        hex::encode(&invocation.source_manifest)
    ));
    manifest.push_str(&format!(
        "rustc_sha256\t{}\n",
        hex::encode(&invocation.rustc_identity.digest)
    ));
    manifest.push_str(&format!(
        "cargo_sha256\t{}\n",
        hex::encode(&invocation.cargo_identity.digest)
    ));

    for (index, case_id) in CASE_IDS.iter().enumerate() {
        deadline.remaining(Duration::MAX)?;
        let case = CaseRoot::create(suite, index, case_id)?;
        invocation.verify_inputs()?;
        materialize_selected_package(
            &invocation.repository,
            &case.source,
            &invocation.package_manifest,
        )?;
        let package_id = metadata_package_id(invocation, &tools, &case.source, &target, deadline)?;
        if !package_ids.insert(package_id.clone()) {
            return Err("ArtifactIdentity: package ID reused".to_string());
        }
        build_case(
            invocation,
            &tools,
            &case.source,
            &target,
            &package_id,
            index == 0,
            deadline,
        )?;
        assert_case_predicate(case_id)?;
        case.cleanup()?;
        cleanup_selected_outputs(&target)?;
        manifest.push_str(case_id);
        manifest.push_str("\t1\n");
    }
    manifest.push_str("complete\t12\n");
    invocation.verify_inputs()?;
    publish_create_once_file(&invocation.case_manifest_path, manifest.as_bytes())?;
    Ok(())
}

struct ReleaseInvocation {
    repository: PathBuf,
    parent: PathBuf,
    case_manifest_path: PathBuf,
    cargo: PathBuf,
    rustc: PathBuf,
    python: PathBuf,
    supervisor: PathBuf,
    repository_head: String,
    repository_tree: String,
    source_manifest: [u8; 32],
    package_manifest: [u8; 32],
    cargo_identity: Identity,
    rustc_identity: Identity,
}

impl ReleaseInvocation {
    fn from_environment() -> Result<Self, String> {
        let repository = canonical_regular_directory(Path::new(env!("CARGO_MANIFEST_DIR")))?;
        let parent = required_path("LEGITIMACY_SELECTED_AUTHORITY_SUITE_PARENT")?;
        let parent = canonical_regular_directory(&parent)?;
        let case_manifest_path = required_path("LEGITIMACY_SELECTED_AUTHORITY_CASE_MANIFEST_PATH")?;
        if case_manifest_path.exists() || case_manifest_path.parent() != Some(parent.as_path()) {
            return Err("ReleaseLaneInvocation: case manifest path".to_string());
        }
        let cargo = canonical_regular_file(&required_path("LEGITIMACY_SELECTED_AUTHORITY_CARGO")?)?;
        let rustc = canonical_regular_file(&required_path("LEGITIMACY_SELECTED_AUTHORITY_RUSTC")?)?;
        let python =
            canonical_regular_file(&required_path("LEGITIMACY_SELECTED_AUTHORITY_PYTHON")?)?;
        let supervisor = canonical_regular_file(&required_path(
            "LEGITIMACY_SELECTED_AUTHORITY_PROCESS_SUPERVISOR",
        )?)?;
        let repository_head = required_ascii("LEGITIMACY_SELECTED_AUTHORITY_REPOSITORY_HEAD", 40)?;
        let repository_tree = required_ascii("LEGITIMACY_SELECTED_AUTHORITY_REPOSITORY_TREE", 40)?;
        let source_manifest = selected_source_manifest(&repository, true)?;
        let package_manifest = selected_source_manifest(&repository, false)?;
        let cargo_identity = file_identity(&cargo)?;
        let rustc_identity = file_identity(&rustc)?;
        Ok(Self {
            repository,
            parent,
            case_manifest_path,
            cargo,
            rustc,
            python,
            supervisor,
            repository_head,
            repository_tree,
            source_manifest,
            package_manifest,
            cargo_identity,
            rustc_identity,
        })
    }

    fn preflight(&self, deadline: &SuiteDeadline) -> Result<(), String> {
        if validate_expected_tool_bytes(&self.rustc, EXPECTED_RUSTC_SHA256)? != self.rustc_identity
            || validate_expected_tool_bytes(&self.cargo, EXPECTED_CARGO_SHA256)?
                != self.cargo_identity
        {
            return Err("CompilerIdentity: executable bytes".to_string());
        }
        self.verify_inputs()?;
        validate_tool_identity(self, &self.rustc, "-vV", EXACT_RUSTC_VV, true, deadline)?;
        validate_tool_identity(self, &self.cargo, "-vV", EXACT_CARGO_VV, false, deadline)?;
        Ok(())
    }

    fn verify_inputs(&self) -> Result<(), String> {
        if file_identity(&self.rustc)? != self.rustc_identity
            || file_identity(&self.cargo)? != self.cargo_identity
            || selected_source_manifest(&self.repository, true)? != self.source_manifest
        {
            return Err("ReleaseLaneInvocation: selected inputs changed".to_string());
        }
        Ok(())
    }

    fn process_supervisor(&self) -> Result<ProcessSupervisor, String> {
        ProcessSupervisor::new(
            self.python.clone(),
            self.supervisor.clone(),
            self.parent.clone(),
        )
        .map_err(|failure| format!("ProcessSupervisor: {failure:?}"))
    }
}

fn validate_expected_tool_bytes(path: &Path, expected: &str) -> Result<Identity, String> {
    let identity = file_identity(path)?;
    if hex::encode(&identity.digest) != expected {
        return Err("CompilerIdentity: executable bytes".to_string());
    }
    Ok(identity)
}

struct SuiteDeadline {
    started: Instant,
}

impl SuiteDeadline {
    fn new() -> Self {
        Self {
            started: Instant::now(),
        }
    }

    fn remaining(&self, stage_cap: Duration) -> Result<Duration, String> {
        let remaining = SUITE_WALL_CAP
            .checked_sub(self.started.elapsed())
            .filter(|remaining| !remaining.is_zero())
            .ok_or_else(|| "SuiteLifecycle: suite wall-clock cap".to_string())?;
        Ok(remaining.min(stage_cap))
    }
}

struct SuiteRoot {
    parent: PathBuf,
    parent_device: u64,
    parent_inode: u64,
    device: u64,
    inode: u64,
    path: PathBuf,
    finished: bool,
}

impl SuiteRoot {
    fn create(parent: &Path) -> Result<Self, String> {
        verify_owned_mode(parent, 0o700)?;
        let parent_metadata = fs::symlink_metadata(parent)
            .map_err(|_| "SuiteLifecycle: parent identity".to_string())?;
        let uid = rustix::process::geteuid().as_raw();
        let run_id = Uuid::new_v4().simple().to_string();
        let path = parent.join(format!("legitimacy-selected-authority-v1.{uid}.{run_id}"));
        create_owned_directory(&path)?;
        write_owned_marker(&path, parent, uid, &run_id)?;
        let metadata =
            fs::symlink_metadata(&path).map_err(|_| "SuiteLifecycle: root identity".to_string())?;
        Ok(Self {
            parent: parent.to_path_buf(),
            parent_device: parent_metadata.dev(),
            parent_inode: parent_metadata.ino(),
            device: metadata.dev(),
            inode: metadata.ino(),
            path,
            finished: false,
        })
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn create_directory(&self, name: &str) -> Result<PathBuf, String> {
        let path = self.path.join(name);
        create_owned_directory(&path)?;
        Ok(path)
    }

    fn locate(&mut self) -> Result<(), String> {
        verify_owned_mode(&self.parent, 0o700)?;
        let parent = fs::symlink_metadata(&self.parent)
            .map_err(|_| "SuiteLifecycle: parent inventory".to_string())?;
        if (parent.dev(), parent.ino()) != (self.parent_device, self.parent_inode) {
            return Err("SuiteLifecycle: parent identity changed".to_string());
        }
        let mut matches = Vec::new();
        for entry in fs::read_dir(&self.parent)
            .map_err(|_| "SuiteLifecycle: parent inventory".to_string())?
        {
            let path = entry
                .map_err(|_| "SuiteLifecycle: parent entry".to_string())?
                .path();
            let metadata = fs::symlink_metadata(&path)
                .map_err(|_| "SuiteLifecycle: parent entry stat".to_string())?;
            if (metadata.dev(), metadata.ino()) == (self.device, self.inode) {
                matches.push(path);
            }
        }
        if let [path] = matches.as_slice() {
            verify_owned_mode(path, 0o700)?;
            self.path = path.clone();
            Ok(())
        } else {
            Err("SuiteLifecycle: owned root missing".to_string())
        }
    }

    fn finish(mut self) -> Result<(), String> {
        self.locate()?;
        remove_owned_tree(&self.path)?;
        self.finished = true;
        Ok(())
    }
}

impl Drop for SuiteRoot {
    fn drop(&mut self) {
        if !self.finished {
            let _ = self.locate();
            let _ = remove_owned_tree(&self.path);
        }
    }
}

struct CaseRoot {
    root: PathBuf,
    source: PathBuf,
}

impl CaseRoot {
    fn create(suite: &SuiteRoot, index: usize, case_id: &str) -> Result<Self, String> {
        let identity = Uuid::new_v4().simple().to_string();
        let root = suite.create_directory(&format!("case-{index:02}-{case_id}-{identity}"))?;
        let source = root.join("source");
        create_owned_directory(&source)?;
        create_owned_directory(&root.join("evidence"))?;
        create_owned_directory(&root.join("probe"))?;
        Ok(Self { root, source })
    }

    fn cleanup(self) -> Result<(), String> {
        remove_owned_tree(&self.root)
    }
}

struct ToolPaths {
    git: PathBuf,
    proxy: PathBuf,
}

fn compile_tools(
    invocation: &ReleaseInvocation,
    suite: &Path,
    deadline: &SuiteDeadline,
) -> Result<ToolPaths, String> {
    let tools = suite.join("tools");
    create_owned_directory(&tools)?;
    let git = tools.join("git");
    let proxy = tools.join("selected-authority-proxy");
    compile_tool(
        invocation,
        &invocation.rustc,
        &invocation
            .repository
            .join("tests/codex_exec_v0/support/selected_authority_git_answer.rs"),
        &git,
        deadline,
    )?;
    compile_tool(
        invocation,
        &invocation.rustc,
        &invocation
            .repository
            .join("tests/codex_exec_v0/support/selected_authority_compiler_proxy.rs"),
        &proxy,
        deadline,
    )?;
    Ok(ToolPaths { git, proxy })
}

fn compile_tool(
    invocation: &ReleaseInvocation,
    rustc: &Path,
    source: &Path,
    output: &Path,
    deadline: &SuiteDeadline,
) -> Result<(), String> {
    let result = bounded_output(
        invocation,
        Command::new(rustc)
            .arg("--edition=2024")
            .arg(source)
            .arg("-o")
            .arg(output),
        "CompilerIdentity",
        deadline.remaining(SUPPORT_COMPILE_TIMEOUT)?,
        CARGO_STREAM_CAP,
        CARGO_STREAM_CAP,
    )?;
    if !result.status.success() || !result.stdout.is_empty() || !result.stderr.is_empty() {
        return Err("CompilerIdentity: support tool compile".to_string());
    }
    canonical_regular_file(output)?;
    Ok(())
}

fn metadata_package_id(
    invocation: &ReleaseInvocation,
    tools: &ToolPaths,
    source: &Path,
    target: &Path,
    deadline: &SuiteDeadline,
) -> Result<String, String> {
    let output = bounded_output(
        invocation,
        configured_cargo(invocation, tools, source, target).args([
            "metadata",
            "--locked",
            "--no-deps",
            "--format-version=1",
        ]),
        "CargoProtocol",
        deadline.remaining(METADATA_TIMEOUT)?,
        METADATA_STREAM_CAP,
        METADATA_STREAM_CAP,
    )?;
    if !output.status.success() {
        return Err("CargoProtocol: metadata execution".to_string());
    }
    let map = parse_metadata_package_map(&output.stdout)
        .map_err(|_| "CargoProtocol: metadata bytes".to_string())?;
    let manifest = canonical_regular_file(&source.join("Cargo.toml"))?;
    let manifest = manifest
        .to_str()
        .ok_or_else(|| "ArtifactRoot: manifest UTF-8".to_string())?;
    let matches = map
        .manifests
        .iter()
        .filter(|(_, candidate)| candidate.as_str() == manifest)
        .map(|(package, _)| package.clone())
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [package] => Ok(package.clone()),
        _ => Err("ArtifactIdentity: metadata package".to_string()),
    }
}

fn build_case(
    invocation: &ReleaseInvocation,
    tools: &ToolPaths,
    source: &Path,
    target: &Path,
    package_id: &str,
    cold: bool,
    deadline: &SuiteDeadline,
) -> Result<(), String> {
    let cap = if cold {
        Duration::from_secs(900)
    } else {
        Duration::from_secs(300)
    };
    let output = bounded_output(
        invocation,
        configured_cargo(invocation, tools, source, target).args([
            "build",
            "--locked",
            "--bin",
            "legitimacy",
            "--message-format=json-render-diagnostics",
        ]),
        "CargoExecution",
        deadline.remaining(cap)?,
        CARGO_STREAM_CAP,
        CARGO_STREAM_CAP,
    )?;
    let protocol = parse_cargo_stream(&output.stdout, output.status.success())
        .map_err(|_| "CargoProtocol: stream".to_string())?;
    continue_after_successful_cargo_execution(&protocol, || {
        let metadata = bounded_output(
            invocation,
            configured_cargo(invocation, tools, source, target).args([
                "metadata",
                "--locked",
                "--no-deps",
                "--format-version=1",
            ]),
            "CargoProtocol",
            deadline.remaining(METADATA_TIMEOUT)?,
            METADATA_STREAM_CAP,
            METADATA_STREAM_CAP,
        )?;
        let metadata = parse_metadata_package_map(&metadata.stdout)
            .map_err(|_| "CargoProtocol: metadata replay bytes".to_string())?;
        let canonical_source = source
            .to_str()
            .ok_or_else(|| "ArtifactRoot: source UTF-8".to_string())?;
        associate_current_package(&metadata, &protocol, package_id, canonical_source)
            .map_err(|failure| format!("{failure:?}: selected package association"))?;
        Ok(())
    })
}

fn continue_after_successful_cargo_execution<T>(
    protocol: &CargoProtocolEvidence,
    continuation: impl FnOnce() -> Result<T, String>,
) -> Result<T, String> {
    if !protocol.terminal_success {
        return Err("CargoExecution: build status".to_string());
    }
    continuation()
}

fn configured_cargo(
    invocation: &ReleaseInvocation,
    tools: &ToolPaths,
    source: &Path,
    target: &Path,
) -> Command {
    let mut command = Command::new(&invocation.cargo);
    let tool_dir = tools.git.parent().expect("tool directory");
    let inherited_path = std::env::var("PATH").unwrap_or_default();
    command
        .current_dir(source)
        .env("CARGO_TARGET_DIR", target)
        .env("CARGO_BUILD_JOBS", "1")
        .env("CARGO_INCREMENTAL", "0")
        .env("RUSTC", &invocation.rustc)
        .env("RUSTC_WORKSPACE_WRAPPER", &tools.proxy)
        .env_remove("RUSTC_WRAPPER")
        .env("PATH", format!("{}:{inherited_path}", tool_dir.display()))
        .env("LEGITIMACY_GIT_ANSWER_SHORT", "0000000")
        .env("LEGITIMACY_GIT_ANSWER_DIRTY_PATHS", "")
        .env(
            "LEGITIMACY_GIT_ANSWER_COMMITS",
            concat!(
                "examples/graphs/codex-graph.json\t0000000000000000000000000000000000000001\n",
                "examples/graphs/claude-agent-sdk-graph.json\t0000000000000000000000000000000000000002\n",
                "examples/graphs/claude-code-graph.json\t0000000000000000000000000000000000000003\n"
            ),
        );
    command
}

fn assert_case_predicate(case_id: &str) -> Result<(), String> {
    match case_id {
        "baseline_selected_closure" => {
            super::selected_binding::assert_unbound_synthetic_tree_has_no_final_constructor();
            super::authority_surface::assert_authority_allowance_contains_only_two_canonical_sites(
            );
        }
        "macro_generated_non_rs_overlap" | "benign_direct_non_rs_overlap" => {
            super::direct_graph::assert_direct_graph_parsing_is_suffix_independent_and_fail_closed(
            );
            super::selected_expansion::assert_expanded_topology_fixture_is_whole_stream_and_target_separate();
        }
        "inactive_duplicate_owner"
        | "active_linux_duplicate_owner"
        | "recognized_false_duplicate_owner"
        | "unrecognized_cfg_owner"
        | "independent_binary_cfg"
        | "zero_candidate_fallback_owner" => {
            super::selected_cfg::assert_selected_cfg_uses_active_atoms_and_recognized_false_grammar(
            );
            super::selected_owner::assert_selected_owner_is_structural_and_graph_bound();
        }
        "clean_owner_relocation" | "borrowed_owner_relocation" => {
            super::selected_binding::assert_stale_compiled_binding_policy_only_fails_at_binding_comparison();
            super::sensitive_policy_tests::assert_selected_sensitive_attack_matrix_policy_only();
        }
        "frozen_manual_sibling_escape" => {
            super::selected_owner::assert_selected_owner_is_structural_and_graph_bound();
        }
        _ => return Err("SuiteLifecycle: unknown release case".to_string()),
    }
    Ok(())
}

fn materialize_selected_package(
    repository: &Path,
    destination: &Path,
    expected_manifest: &[u8; 32],
) -> Result<(), String> {
    for directory in [
        "fixtures",
        "fixtures/trajectory-composition-v0",
        "fixtures/executed-composition-v1",
        "fixtures/executed-composition-v1/generated",
        "tests",
        "tests/fixtures",
    ] {
        create_owned_directory(&destination.join(directory))?;
    }
    for name in SELECTED_PACKAGE_ENTRIES {
        copy_entry(&repository.join(name), &destination.join(name))?;
    }
    if regular_tree_bytes(destination)? > SOURCE_BYTE_CAP {
        return Err("SuiteLifecycle: materialized source cap".to_string());
    }
    if &selected_source_manifest(destination, false)? != expected_manifest {
        return Err("SuiteLifecycle: materialized source identity".to_string());
    }
    Ok(())
}

fn selected_source_manifest(root: &Path, include_support: bool) -> Result<[u8; 32], String> {
    let mut hasher = Sha256::new();
    hasher.update(b"legitimacy.selected-authority-source-manifest.v1\0");
    let mut total = 0_u64;
    for name in SELECTED_PACKAGE_ENTRIES {
        hash_source_entry(root, Path::new(name), &mut hasher, &mut total)?;
    }
    if include_support {
        for name in [
            "tests/codex_exec_v0/support/selected_authority_git_answer.rs",
            "tests/codex_exec_v0/support/selected_authority_compiler_proxy.rs",
        ] {
            hash_source_entry(root, Path::new(name), &mut hasher, &mut total)?;
        }
    }
    Ok(hasher.finalize().into())
}

fn hash_source_entry(
    root: &Path,
    relative: &Path,
    hasher: &mut Sha256,
    total: &mut u64,
) -> Result<(), String> {
    let path = root.join(relative);
    let metadata = fs::symlink_metadata(&path)
        .map_err(|_| "SuiteLifecycle: source manifest stat".to_string())?;
    let name = relative
        .to_str()
        .ok_or_else(|| "SuiteLifecycle: source manifest path".to_string())?;
    let name_length = u64::try_from(name.len())
        .map_err(|_| "SuiteLifecycle: source manifest length".to_string())?;
    hasher.update(name_length.to_be_bytes());
    hasher.update(name.as_bytes());
    if metadata.file_type().is_symlink() {
        return Err("SuiteLifecycle: source manifest symlink".to_string());
    }
    if metadata.is_dir() {
        hasher.update(b"D");
        let mut entries = fs::read_dir(&path)
            .map_err(|_| "SuiteLifecycle: source manifest directory".to_string())?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| "SuiteLifecycle: source manifest entry".to_string())?;
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            hash_source_entry(root, &relative.join(entry.file_name()), hasher, total)?;
        }
    } else if metadata.is_file() {
        hasher.update(b"F");
        *total = total
            .checked_add(metadata.len())
            .filter(|total| *total <= SOURCE_BYTE_CAP)
            .ok_or_else(|| "SuiteLifecycle: source manifest cap".to_string())?;
        hasher.update(metadata.len().to_be_bytes());
        let bytes =
            fs::read(path).map_err(|_| "SuiteLifecycle: source manifest read".to_string())?;
        if u64::try_from(bytes.len()).ok() != Some(metadata.len()) {
            return Err("SuiteLifecycle: source manifest changed".to_string());
        }
        hasher.update(bytes);
    } else {
        return Err("SuiteLifecycle: source manifest object".to_string());
    }
    Ok(())
}

fn copy_entry(source: &Path, destination: &Path) -> Result<(), String> {
    let metadata =
        std::fs::symlink_metadata(source).map_err(|_| "SuiteLifecycle: source stat".to_string())?;
    if metadata.file_type().is_symlink() {
        return Err("SuiteLifecycle: materialization symlink".to_string());
    }
    if metadata.is_dir() {
        create_owned_directory(destination)?;
        let mut entries = std::fs::read_dir(source)
            .map_err(|_| "SuiteLifecycle: source directory".to_string())?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| "SuiteLifecycle: source entry".to_string())?;
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            copy_entry(&entry.path(), &destination.join(entry.file_name()))?;
        }
    } else if metadata.is_file() {
        let mut input =
            File::open(source).map_err(|_| "SuiteLifecycle: source open".to_string())?;
        let mut output = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(destination)
            .map_err(|_| "SuiteLifecycle: destination create".to_string())?;
        std::io::copy(&mut input, &mut output)
            .map_err(|_| "SuiteLifecycle: source copy".to_string())?;
        output
            .sync_all()
            .map_err(|_| "SuiteLifecycle: source sync".to_string())?;
    } else {
        return Err("SuiteLifecycle: unsupported source object".to_string());
    }
    Ok(())
}

fn cleanup_selected_outputs(target: &Path) -> Result<(), String> {
    for relative in ["debug/legitimacy", "debug/legitimacy.d"] {
        let path = target.join(relative);
        if path.exists() {
            std::fs::remove_file(path)
                .map_err(|_| "SuiteLifecycle: selected output cleanup".to_string())?;
        }
    }
    for relative in ["debug/deps", "debug/.fingerprint", "debug/build"] {
        let directory = target.join(relative);
        if !directory.is_dir() {
            continue;
        }
        for entry in std::fs::read_dir(&directory)
            .map_err(|_| "SuiteLifecycle: target inventory".to_string())?
        {
            let entry = entry.map_err(|_| "SuiteLifecycle: target entry".to_string())?;
            let name = entry.file_name();
            let name = name
                .to_str()
                .ok_or_else(|| "SuiteLifecycle: target name".to_string())?;
            if name.starts_with("legitimacy-") || name.starts_with("liblegitimacy-") {
                let path = entry.path();
                if path.is_dir() {
                    remove_owned_tree(&path)?;
                } else {
                    std::fs::remove_file(path)
                        .map_err(|_| "SuiteLifecycle: target file cleanup".to_string())?;
                }
            }
        }
    }
    Ok(())
}

fn validate_tool_identity(
    invocation: &ReleaseInvocation,
    executable: &Path,
    argument: &str,
    expected: &[u8],
    rustc: bool,
    deadline: &SuiteDeadline,
) -> Result<(), String> {
    let before = file_identity(executable)?;
    let output = bounded_output(
        invocation,
        Command::new(executable).arg(argument),
        "CompilerIdentity",
        deadline.remaining(IDENTITY_TIMEOUT)?,
        CARGO_STREAM_CAP,
        CARGO_STREAM_CAP,
    )?;
    if !output.status.success() || !output.stderr.is_empty() {
        return Err("CompilerIdentity: identity command".to_string());
    }
    let accepted = if rustc {
        validate_compiler_identity(&output.stdout)
    } else {
        validate_cargo_identity(&output.stdout)
    };
    if output.stdout != expected || accepted.is_err() || before != file_identity(executable)? {
        return Err(if rustc {
            "CompilerIdentity: complete bytes".to_string()
        } else {
            "CargoProtocol: complete Cargo bytes".to_string()
        });
    }
    Ok(())
}

fn bounded_output(
    invocation: &ReleaseInvocation,
    command: &mut Command,
    stage: &str,
    timeout: Duration,
    stdout_cap: usize,
    stderr_cap: usize,
) -> Result<Output, String> {
    invocation.verify_inputs()?;
    let outcome = invocation
        .process_supervisor()?
        .run(command, timeout, stdout_cap, stderr_cap)
        .map_err(|failure| format!("{stage}: process supervisor {failure:?}"))?;
    invocation.verify_inputs()?;
    match outcome.result {
        ProcessResult::Success | ProcessResult::NonzeroExit => Ok(outcome.output),
        ProcessResult::Timeout => Err(format!("{stage}: process timeout")),
        ProcessResult::StdoutCap => Err(format!("{stage}: stdout cap")),
        ProcessResult::StderrCap => Err(format!("{stage}: stderr cap")),
        ProcessResult::LiveDescendant => Err(format!("{stage}: live descendant")),
        ProcessResult::SupervisorSignal => Err(format!("{stage}: supervisor signal")),
        ProcessResult::SpawnFailure => Err(format!("{stage}: process spawn")),
    }
}

pub(crate) fn assert_release_gate_wiring_is_exact() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let build = super::super::source_bindings::canonical_build_input();
    for role in ["binary", "library"] {
        for input in build["cargo_contract"]["compiler_read_inputs"][role]
            .as_array()
            .unwrap()
        {
            let input = Path::new(input.as_str().unwrap());
            assert!(
                SELECTED_PACKAGE_ENTRIES.iter().any(|entry| {
                    input == Path::new(entry)
                        || (root.join(entry).is_dir() && input.starts_with(entry))
                }),
                "isolated release package omits compiler input: {}",
                input.display()
            );
        }
    }
    let expected_manifest = selected_source_manifest(root, false).unwrap();
    let destination = std::env::temp_dir().join(format!(
        "legitimacy-selected-package-materialization.{}",
        Uuid::new_v4().simple()
    ));
    create_owned_directory(&destination).unwrap();
    let materialized = materialize_selected_package(root, &destination, &expected_manifest);
    let cleanup = remove_owned_tree(&destination);
    assert_eq!(materialized, Ok(()));
    cleanup.unwrap();
    assert_repository_and_tool_controls_are_behavioral();
    assert_failed_cargo_status_stops_before_artifact_association();
    let verify = include_str!("../../scripts/verify.sh");
    let global = include_str!("../../scripts/release-gate.sh");
    let dedicated = include_str!("../../scripts/selected-authority-release-gate.sh");
    let selector = include_str!("../../scripts/selected-authority-test-binary.py");
    let tests = include_str!("../../tests/codex_exec_v0.rs");
    assert!(!verify.contains("LEGITIMACY_RELEASE_GATE"));
    assert_eq!(verify.matches("scripts/release-gate.sh").count(), 1);
    let call = "bash \"$ROOT/scripts/selected-authority-release-gate.sh\"";
    assert_eq!(global.matches(call).count(), 1);
    let call_offset = global.find(call).unwrap();
    for prior in [
        "release_gate_step_begin paper-anchor",
        "anchor_commit=\"$(git -C \"$ROOT\" rev-parse",
        "[[ \"$anchor_commit\" == \"$head_commit\" ]]",
        "release_gate_step_begin stale-release-dir-check",
    ] {
        assert!(
            global
                .find(prior)
                .is_some_and(|offset| offset < call_offset)
        );
    }
    assert_eq!(
        dedicated
            .matches("selected_authority_full_tree_release_gate")
            .count(),
        1
    );
    assert_eq!(
        dedicated
            .matches("test --locked --test codex_exec_v0 --no-run")
            .count(),
        1
    );
    assert!(dedicated.contains("--exact --ignored --list --format terse"));
    assert!(dedicated.contains("__definitely_missing_selected_authority_test__"));
    assert!(dedicated.contains("forged-manifest negative control passed"));
    assert!(dedicated.contains("outer-execution-witness."));
    assert!(dedicated.contains("LEGITIMACY_SELECTED_AUTHORITY_CASE_MANIFEST_PATH"));
    assert!(selector.contains("len(artifacts) != 1"));
    let build_offset = dedicated.find("--no-run").unwrap();
    let enumeration_offset = dedicated.find("--list --format terse").unwrap();
    let execution_offset = dedicated
        .find("LEGITIMACY_SELECTED_AUTHORITY_SUITE_PARENT=\"$execution_parent\"")
        .unwrap();
    let witness_offset = dedicated.find("outer-execution-witness.").unwrap();
    assert!(build_offset < enumeration_offset);
    assert!(enumeration_offset < execution_offset);
    assert!(execution_offset < witness_offset);
    assert!(tests.contains("#[ignore = \"requires reviewed compiler compatibility lane\"]"));
}

fn assert_failed_cargo_status_stops_before_artifact_association() {
    let stream = b"{\"reason\":\"build-finished\",\"success\":false}\n";
    let protocol = parse_cargo_stream(stream, false).unwrap();
    let association_reached = std::cell::Cell::new(false);
    let result = continue_after_successful_cargo_execution(&protocol, || {
        association_reached.set(true);
        Err::<(), _>("ArtifactMultiplicity: selected package association".to_string())
    });
    assert_eq!(result, Err("CargoExecution: build status".to_string()));
    assert!(!association_reached.get());
}

fn assert_repository_and_tool_controls_are_behavioral() {
    let root = std::env::temp_dir().join(format!(
        "legitimacy-selected-authority-state-{}",
        Uuid::new_v4().simple()
    ));
    create_owned_directory(&root).unwrap();
    run_git(&root, &["init", "-q", "--initial-branch=main"]);
    let tracked = root.join("tracked");
    fs::write(&tracked, b"committed\n").unwrap();
    run_git(&root, &["add", "tracked"]);
    let status = Command::new("git")
        .current_dir(&root)
        .args(["commit", "-q", "-m", "initial"])
        .env("GIT_AUTHOR_NAME", "Selected Gate")
        .env("GIT_AUTHOR_EMAIL", "selected-gate@example.invalid")
        .env("GIT_COMMITTER_NAME", "Selected Gate")
        .env("GIT_COMMITTER_EMAIL", "selected-gate@example.invalid")
        .status()
        .unwrap();
    assert!(status.success());
    let head = git_text(&root, &["rev-parse", "HEAD"]);
    let tree = git_text(&root, &["rev-parse", "HEAD^{tree}"]);
    let check = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("scripts/selected-authority-repository-state.sh");
    let state = |repository: &Path| {
        Command::new(&check)
            .arg(repository)
            .arg(&head)
            .arg(&tree)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .unwrap()
            .success()
    };
    assert!(state(&root));
    fs::write(&tracked, b"modified\n").unwrap();
    assert!(!state(&root));
    fs::write(&tracked, b"committed\n").unwrap();
    fs::write(root.join("untracked"), b"untracked\n").unwrap();
    assert!(!state(&root));
    fs::remove_file(root.join("untracked")).unwrap();
    fs::write(&tracked, b"staged\n").unwrap();
    run_git(&root, &["add", "tracked"]);
    assert!(!state(&root));
    fs::write(&tracked, b"committed\n").unwrap();
    run_git(&root, &["add", "tracked"]);
    assert!(state(&root));

    let identity = root.join("identity");
    fs::write(&identity, EXACT_RUSTC_VV).unwrap();
    let executable = root.join("alternate-rustc");
    fs::write(
        &executable,
        format!("#!/bin/sh\ncat {}\n", identity.display()),
    )
    .unwrap();
    fs::set_permissions(&executable, fs::Permissions::from_mode(0o700)).unwrap();
    let output = Command::new(&executable).arg("-vV").output().unwrap();
    assert!(output.status.success());
    assert_eq!(output.stdout, EXACT_RUSTC_VV);
    assert!(validate_expected_tool_bytes(&executable, EXPECTED_RUSTC_SHA256).is_err());
    remove_owned_tree(&root).unwrap();
}

fn run_git(root: &Path, arguments: &[&str]) {
    assert!(
        Command::new("git")
            .current_dir(root)
            .args(arguments)
            .status()
            .unwrap()
            .success()
    );
}

fn git_text(root: &Path, arguments: &[&str]) -> String {
    let output = Command::new("git")
        .current_dir(root)
        .args(arguments)
        .output()
        .unwrap();
    assert!(output.status.success());
    String::from_utf8(output.stdout).unwrap().trim().to_string()
}
