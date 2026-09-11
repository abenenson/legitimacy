use crate::repository_object::read_repository_file;
use legitimacy::trajectory::codex_exec_v0::{
    CODEX_EXEC_ADAPTER_BINDING_CONTRACT_V0, CODEX_EXEC_CAPTURE_PRODUCER_BINDING_CONTRACT_V0,
    CODEX_EXEC_CLI_PUBLICATION_BINDING_CONTRACT_V0, CODEX_EXEC_FIXTURE_SPEC_BINDING_CONTRACT_V0,
    CODEX_EXEC_SANITIZER_BINDING_CONTRACT_V0, codex_exec_adapter_binding_v0,
    codex_exec_capture_producer_binding_v0, codex_exec_cli_publication_binding_v0,
    codex_exec_fixture_spec_binding_v0, codex_exec_sanitizer_binding_v0,
};
use sha2::{Digest, Sha256};
use std::path::Path;

const HASH_ENVELOPE_V0: &[u8] = b"legitimacy.trajectory.hash.v0\0";

pub(super) const ADAPTER_CORE_PATHS: &[&str] = &[
    "src/trajectory/codex_exec_v0/source_bindings.rs",
    "src/trajectory/codex_exec_v0/bundle.rs",
    "src/trajectory/codex_exec_v0/bundle_wire.rs",
    "src/trajectory/codex_exec_v0/error.rs",
    "src/trajectory/codex_exec_v0/event.rs",
    "src/trajectory/codex_exec_v0/event_wire.rs",
    "src/trajectory/codex_exec_v0/framing.rs",
    "src/trajectory/codex_exec_v0/fsm.rs",
    "src/trajectory/codex_exec_v0/mapping.rs",
    "src/trajectory/codex_exec_v0/mod.rs",
    "src/trajectory/codex_exec_v0/process_capture.rs",
    "src/trajectory/codex_exec_v0/process_capture_cleanup.rs",
    "src/trajectory/codex_exec_v0/process_capture_output.rs",
    "src/trajectory/codex_exec_v0/process_capture_platform.rs",
    "src/trajectory/codex_exec_v0/process_capture_signal.rs",
    "src/trajectory/codex_exec_v0/process_capture_supervision.rs",
    "src/trajectory/codex_exec_v0/process_capture_supervisor.rs",
    "src/trajectory/codex_exec_v0/receipt.rs",
    "src/trajectory/codex_exec_v0/receipt_canonical.rs",
    "src/trajectory/codex_exec_v0/receipt_context.rs",
    "src/trajectory/codex_exec_v0/receipt_debug.rs",
    "src/trajectory/codex_exec_v0/receipt_hex.rs",
    "src/trajectory/codex_exec_v0/receipt_nonce.rs",
    "src/trajectory/codex_exec_v0/receipt_validate.rs",
    "src/trajectory/codex_exec_v0/receipt_wire.rs",
    "src/trajectory/codex_exec_v0/receipt_workspace.rs",
    "src/trajectory/mod.rs",
    "src/trajectory/duplicate_json.rs",
    "src/trajectory/canonical.rs",
    "src/trajectory/validation.rs",
    "src/trajectory/interchange.rs",
];

pub(super) const SANITIZER_ONLY_PATHS: &[&str] = &[
    "src/trajectory/codex_exec_v0/sanitizer.rs",
    "src/trajectory/codex_exec_v0/sanitizer_jwt.rs",
    "src/trajectory/codex_exec_v0/publication_authority.rs",
    "src/trajectory/codex_exec_v0/lineage_sidecar.rs",
];

pub(super) fn independent_sanitizer_only_paths() -> &'static [&'static str] {
    SANITIZER_ONLY_PATHS
}

pub(super) const CAPTURE_PRODUCER_ONLY_PATHS: &[&str] = &["src/bin/legitimacy-codex-capture-v0.rs"];

pub(super) const BUILD_INPUT_PATH: &str = "tests/fixtures/codex-exec-v0/adapter-build-input.json";

pub(super) fn cli_test_only_rust_paths() -> Vec<String> {
    let build = canonical_build_input();
    build["cargo_contract"]["test_only_cli_rust_sources"]
        .as_array()
        .unwrap()
        .iter()
        .map(|path| path.as_str().unwrap().to_string())
        .collect()
}

pub(super) fn cli_selected_build_paths() -> Vec<String> {
    vec![BUILD_INPUT_PATH.to_string()]
}

pub(super) fn canonical_build_input() -> serde_json::Value {
    super::source_binding_registry::connected_canonical_build_input()
}

fn canonical_contract_input_paths(build: &serde_json::Value) -> Vec<String> {
    let contract = &build["cargo_contract"];
    let mut paths = Vec::new();
    for role in ["binary", "library"] {
        paths.extend(
            contract["compiler_read_inputs"][role]
                .as_array()
                .unwrap()
                .iter()
                .map(|path| path.as_str().unwrap().to_string()),
        );
    }
    for role in ["cargo", "build_script", "review_contract"] {
        paths.extend(
            contract["selected_noncompiler_inputs"][role]
                .as_array()
                .unwrap()
                .iter()
                .map(|path| path.as_str().unwrap().to_string()),
        );
    }
    paths.extend(
        contract["repository_configuration"]["present"]
            .as_array()
            .unwrap()
            .iter()
            .map(|path| path.as_str().unwrap().to_string()),
    );
    paths
}

#[test]
fn registered_bindings_match_independent_ordered_path_framing() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let adapter = read_components(root, ADAPTER_CORE_PATHS);
    let sanitizer_paths = joined(ADAPTER_CORE_PATHS, SANITIZER_ONLY_PATHS);
    let sanitizer = read_components(root, &sanitizer_paths);
    let cli_paths = cli_selected_build_paths();
    let cli_path_refs = cli_paths.iter().map(String::as_str).collect::<Vec<_>>();
    let cli = read_components(root, &cli_path_refs);
    let fixture = read_components(root, &["tests/fixtures/codex-exec-v0/source-manifest.json"]);
    let capture_producer_paths = joined(ADAPTER_CORE_PATHS, CAPTURE_PRODUCER_ONLY_PATHS);
    let capture_producer = read_components(root, &capture_producer_paths);

    assert_eq!(
        codex_exec_adapter_binding_v0().hash,
        framed_hash(
            CODEX_EXEC_ADAPTER_BINDING_CONTRACT_V0.framing_domain,
            &adapter
        )
    );
    assert_eq!(
        codex_exec_sanitizer_binding_v0().hash,
        framed_hash(
            CODEX_EXEC_SANITIZER_BINDING_CONTRACT_V0.framing_domain,
            &sanitizer
        )
    );
    assert_eq!(
        codex_exec_cli_publication_binding_v0().hash,
        framed_hash(
            CODEX_EXEC_CLI_PUBLICATION_BINDING_CONTRACT_V0.framing_domain,
            &cli
        )
    );
    assert_eq!(
        codex_exec_fixture_spec_binding_v0().hash,
        framed_hash(
            CODEX_EXEC_FIXTURE_SPEC_BINDING_CONTRACT_V0.framing_domain,
            &fixture
        )
    );
    assert_eq!(
        codex_exec_capture_producer_binding_v0().hash,
        framed_hash(
            CODEX_EXEC_CAPTURE_PRODUCER_BINDING_CONTRACT_V0.framing_domain,
            &capture_producer
        )
    );

    for (domain, components, compiled) in [
        (
            CODEX_EXEC_ADAPTER_BINDING_CONTRACT_V0.framing_domain,
            adapter,
            codex_exec_adapter_binding_v0().hash,
        ),
        (
            CODEX_EXEC_SANITIZER_BINDING_CONTRACT_V0.framing_domain,
            sanitizer,
            codex_exec_sanitizer_binding_v0().hash,
        ),
        (
            CODEX_EXEC_CLI_PUBLICATION_BINDING_CONTRACT_V0.framing_domain,
            cli,
            codex_exec_cli_publication_binding_v0().hash,
        ),
        (
            CODEX_EXEC_FIXTURE_SPEC_BINDING_CONTRACT_V0.framing_domain,
            fixture,
            codex_exec_fixture_spec_binding_v0().hash,
        ),
        (
            CODEX_EXEC_CAPTURE_PRODUCER_BINDING_CONTRACT_V0.framing_domain,
            capture_producer,
            codex_exec_capture_producer_binding_v0().hash,
        ),
    ] {
        for index in 0..components.len() {
            let mut mutant = components.clone();
            mutant[index][0] ^= 1;
            assert_ne!(
                framed_hash(domain, &mutant),
                compiled,
                "component {index} must be bound"
            );
        }
        if components.len() >= 4 {
            let mut reordered = components;
            reordered.swap(0, 2);
            reordered.swap(1, 3);
            assert_ne!(framed_hash(domain, &reordered), compiled);
        }
    }
}

#[test]
fn pinned_source_manifest_is_the_exact_registered_upstream_object() {
    let manifest: serde_json::Value = serde_json::from_slice(include_bytes!(
        "../fixtures/codex-exec-v0/source-manifest.json"
    ))
    .unwrap();
    assert_eq!(
        manifest,
        serde_json::json!({
            "format": "legitimacy.codex-exec-v0.synthetic-source-manifest",
            "version": "0",
            "evidence_class": "synthetic-fixture",
            "repository": "https://github.com/openai/codex",
            "authoritative_source_tag": "rust-v0.144.0",
            "tag_object_type": "tag",
            "tag_object_sha": "e0a9ff6938d85db1a7b11a693b6aa2bc31fe5a55",
            "peeled_source_commit_sha": "767822446c7a594caa19609ca435281a9ec67e0d",
            "peeled_source_tree_sha": "444a05890bb4f4327dc53f44ad348cfd6431ecc8",
            "source_files": [
                {"path":"codex-rs/exec/src/exec_events.rs","sha256":"fa46724c54076701d04d29415f22398eb1e8c45abc60b54abd95fad0ecbfe201"},
                {"path":"codex-rs/exec/src/event_processor_with_jsonl_output.rs","sha256":"5181d2a5d40d20fdeb41d4fa4eeca751848b572eba82af2391529f9b1baf0cd4"},
                {"path":"codex-rs/app-server-protocol/src/protocol/item_builders.rs","sha256":"c89e5d2271560bd61658df122f5fbe0b85435e2d8e1b2ec8f380cb78be947a6c"},
                {"path":"codex-rs/app-server-protocol/src/protocol/v2/item.rs","sha256":"da4846f64b75a4eb352e1963db763d43b1ddcfdfe834f0b17be51fa81000af3f"},
                {"path":"codex-rs/protocol/src/thread_id.rs","sha256":"b12de60f4ecdbfaf7a4878c349984389764dfa880d9da9339967744d79e7aab0"},
                {"path":"codex-rs/utils/cli/src/sandbox_mode_cli_arg.rs","sha256":"ffc5526811eeb12dea1fdafeea6971d53129bec017b272459d626fe5e394a49b"},
                {"path":"codex-rs/utils/cli/src/shared_options.rs","sha256":"fdec561b127ec4502cca0883e137aa0b84815a04fe0c2e04fd73dc428d645238"},
                {"path":"codex-rs/exec/src/cli.rs","sha256":"e60d93d09929b1e03f62ecc04db363faa9e791f87b2ddf030d2102a3400c6566"},
                {"path":"codex-rs/cli/src/main.rs","sha256":"9f0b17cfea4ffce46fdef5c155d55f85d6a9a0b39fd972e1416b49b26492d999"},
                {"path":"codex-rs/exec/src/lib.rs","sha256":"bb5b8d78b22fddfdb71f5ea3c7ebc73592e7cdc4b881b32163999cd0a4cee8e6"}
            ],
            "claim": "synthetic shapes modeled from the pinned Rust emitter; no process execution is claimed"
        })
    );
}

#[test]
fn canonical_build_input_binds_complete_selected_inputs() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let build_json = canonical_build_input();
    let top_level_keys = build_json
        .as_object()
        .unwrap()
        .keys()
        .map(String::as_str)
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        top_level_keys,
        std::collections::BTreeSet::from([
            "cargo_contract",
            "format",
            "normative_contract",
            "package",
            "version",
        ])
    );
    assert_eq!(
        build_json["format"],
        "legitimacy.codex-exec-v0.adapter-build-input"
    );
    assert_eq!(build_json["version"], "0");
    assert_eq!(
        build_json["package"],
        serde_json::json!({"name":"legitimacy","version":"1.1.1","edition":"2024"})
    );
    let manifest: toml::Value =
        toml::from_str(&std::fs::read_to_string(root.join("Cargo.toml")).unwrap()).unwrap();
    assert_eq!(
        build_json["package"]["name"].as_str(),
        manifest["package"]["name"].as_str()
    );
    assert_eq!(
        build_json["package"]["version"].as_str(),
        manifest["package"]["version"].as_str()
    );
    assert_eq!(
        build_json["package"]["edition"].as_str(),
        manifest["package"]["edition"].as_str()
    );
    let paths = canonical_contract_input_paths(&build_json);
    let path_refs = paths.iter().map(String::as_str).collect::<Vec<_>>();
    let components = read_components(root, &path_refs);
    assert_eq!(
        build_json["cargo_contract"]["bound_inputs_sha256"],
        framed_hash(
            "legitimacy.codex-exec-v0.selected-build-inputs.v0",
            &components
        )
    );
}

fn read_components(root: &Path, paths: &[&str]) -> Vec<Vec<u8>> {
    paths
        .iter()
        .flat_map(|path| {
            [
                path.as_bytes().to_vec(),
                read_repository_file(root, path, 64 * 1024 * 1024).unwrap(),
            ]
        })
        .collect()
}

pub(super) fn joined<'a>(left: &'a [&'a str], right: &'a [&'a str]) -> Vec<&'a str> {
    left.iter().chain(right).copied().collect()
}

fn framed_hash(domain: &str, components: &[Vec<u8>]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(HASH_ENVELOPE_V0);
    frame(&mut hasher, domain.as_bytes());
    hasher.update(u64::try_from(components.len()).unwrap().to_be_bytes());
    for component in components {
        frame(&mut hasher, component);
    }
    format!("sha256:{:x}", hasher.finalize())
}

fn frame(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update(u64::try_from(bytes.len()).unwrap().to_be_bytes());
    hasher.update(bytes);
}
