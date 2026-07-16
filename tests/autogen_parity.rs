use legitimacy::{Decision, Gate, GateLogic, GovernanceGraph, GovernanceNode, NodeId};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

const AUTOGEN_SOURCE: &str = "audits/fixtures/sources/leaderboard/autogen";
const AUTOGEN_NODE_ID: &str = "python/packages/autogen-agentchat/tests/test_code_executor_agent.py::approval_function_deny_dangerous";
const AUTOGEN_NODE_NAME: &str = "python/packages/autogen-agentchat/tests/test_code_executor_agent.py::approval_function_deny_dangerous:446-454";
const SHARED_CANONICAL_INPUTS: &str =
    include_str!("../lean/Legitimacy/Extract/CanonicalInputs.lean");

#[derive(Default)]
struct PartialGraphParityCase {
    name: Option<String>,
    source: Option<String>,
    allow_partial: Option<bool>,
    canonical_graph: Option<String>,
    source_byte_size: Option<u64>,
    source_tree_hash: Option<String>,
    seen: BTreeSet<&'static str>,
}

#[derive(Debug)]
struct GraphParityCase {
    name: String,
    source: String,
    allow_partial: bool,
    canonical_graph: String,
    source_byte_size: u64,
    source_tree_hash: String,
}

fn unique_path(label: &str, extension: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}.{extension}"))
}

fn repo_path(path: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(path)
}

fn parse_lean_string(value: &str) -> Option<String> {
    value
        .strip_prefix('"')
        .and_then(|trimmed| trimmed.strip_suffix('"'))
        .map(str::to_string)
}

fn parse_lean_bool(value: &str) -> Option<bool> {
    match value {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

fn parse_lean_nat(value: &str) -> Option<u64> {
    value.parse().ok()
}

fn assign_shared_field(case: &mut PartialGraphParityCase, key: &str, value: &str) {
    let normalized_key = match key {
        "name" => "name",
        "source" => "source",
        "allowPartial" => "allowPartial",
        "canonicalGraph" => "canonicalGraph",
        "sourceByteSize" => "sourceByteSize",
        "sourceTreeHash" => "sourceTreeHash",
        other => panic!("unexpected shared canonical input field `{other}`"),
    };
    assert!(
        case.seen.insert(normalized_key),
        "duplicate shared canonical input field `{normalized_key}`"
    );

    match normalized_key {
        "name" => case.name = parse_lean_string(value),
        "source" => case.source = parse_lean_string(value),
        "allowPartial" => case.allow_partial = parse_lean_bool(value),
        "canonicalGraph" => case.canonical_graph = parse_lean_string(value),
        "sourceByteSize" => case.source_byte_size = parse_lean_nat(value),
        "sourceTreeHash" => case.source_tree_hash = parse_lean_string(value),
        _ => unreachable!(),
    }
}

fn finalize_shared_case(case: PartialGraphParityCase) -> GraphParityCase {
    GraphParityCase {
        name: case.name.expect("shared canonical input missing name"),
        source: case.source.expect("shared canonical input missing source"),
        allow_partial: case
            .allow_partial
            .expect("shared canonical input missing allowPartial"),
        canonical_graph: case
            .canonical_graph
            .expect("shared canonical input missing canonicalGraph"),
        source_byte_size: case
            .source_byte_size
            .expect("shared canonical input missing sourceByteSize"),
        source_tree_hash: case
            .source_tree_hash
            .expect("shared canonical input missing sourceTreeHash"),
    }
}

fn canonical_graph_cases() -> Vec<GraphParityCase> {
    let mut cases = Vec::new();
    let mut current: Option<PartialGraphParityCase> = None;
    let mut pending_key: Option<String> = None;
    let mut in_records = false;

    for line in SHARED_CANONICAL_INPUTS.lines() {
        if line.contains("def canonicalExtractorParityRecords") {
            in_records = true;
            continue;
        }
        if !in_records {
            continue;
        }

        let uncommented = line.split_once("--").map_or(line, |(code, _comment)| code);
        let mut trimmed = uncommented.trim();
        if trimmed.starts_with(']') {
            break;
        }
        while let Some(rest) = trimmed.strip_prefix([',', '[']) {
            trimmed = rest.trim_start();
        }
        if trimmed.is_empty() {
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix('{') {
            assert!(current.is_none(), "nested shared canonical input record");
            current = Some(PartialGraphParityCase::default());
            trimmed = rest.trim_start();
        }

        let closes_record = trimmed.ends_with('}');
        if closes_record {
            trimmed = trimmed.trim_end_matches('}').trim_end();
        }

        if !trimmed.is_empty() {
            if let Some(key) = pending_key.take() {
                assign_shared_field(
                    current
                        .as_mut()
                        .expect("shared canonical input value outside record"),
                    &key,
                    trimmed,
                );
            } else if let Some((key, value)) = trimmed.split_once(":=") {
                let key = key.trim();
                let value = value.trim();
                if value.is_empty() {
                    pending_key = Some(key.to_string());
                } else {
                    assign_shared_field(
                        current
                            .as_mut()
                            .expect("shared canonical input field outside record"),
                        key,
                        value,
                    );
                }
            } else {
                panic!("unrecognized shared canonical input line `{trimmed}`");
            }
        }

        if closes_record {
            cases.push(finalize_shared_case(
                current
                    .take()
                    .expect("shared canonical input close outside record"),
            ));
        }
    }

    assert!(
        pending_key.is_none(),
        "unterminated shared canonical input field"
    );
    assert!(
        !cases.is_empty(),
        "no shared canonical input records parsed"
    );
    cases
}

fn autogen_canonical_graph() -> GovernanceGraph {
    let node_id = NodeId::new(AUTOGEN_NODE_ID).unwrap();
    let node = GovernanceNode::Binary {
        id: node_id.clone(),
        name: AUTOGEN_NODE_NAME.to_string(),
        gates: vec![
            Gate::ContentMatch {
                regex: "Approval function that denies potentially dangerous code\\.".to_string(),
                decision: Decision::Permit,
            },
            Gate::ExactMatch {
                value: "rm".to_string(),
                decision: Decision::Permit,
            },
            Gate::ExactMatch {
                value: "del".to_string(),
                decision: Decision::Permit,
            },
            Gate::ExactMatch {
                value: "format".to_string(),
                decision: Decision::Permit,
            },
            Gate::ExactMatch {
                value: "delete".to_string(),
                decision: Decision::Permit,
            },
            Gate::ContentMatch {
                regex: "DROP TABLE".to_string(),
                decision: Decision::Permit,
            },
            Gate::ContentMatch {
                regex: "f\"Code contains potentially dangerous keyword: \\{keyword\\}".to_string(),
                decision: Decision::Permit,
            },
            Gate::ContentMatch {
                regex: "Code appears safe".to_string(),
                decision: Decision::Permit,
            },
        ],
        default: Decision::Deny,
        combination: GateLogic::FirstMatch,
    };

    GovernanceGraph {
        nodes: BTreeMap::from([(node_id, node)]),
        edges: Vec::new(),
    }
}

fn mismatch_context(expected: &[u8], actual: &[u8]) -> String {
    let expected = String::from_utf8_lossy(expected);
    let actual = String::from_utf8_lossy(actual);

    let expected_lines = expected.lines().collect::<Vec<_>>();
    let actual_lines = actual.lines().collect::<Vec<_>>();
    let line_count = expected_lines.len().max(actual_lines.len());

    for line_index in 0..line_count {
        let expected_line = expected_lines
            .get(line_index)
            .copied()
            .unwrap_or("<missing>");
        let actual_line = actual_lines.get(line_index).copied().unwrap_or("<missing>");
        if expected_line != actual_line {
            return format!(
                "first differing line {}:\nexpected: {}\nactual: {}",
                line_index + 1,
                expected_line,
                actual_line
            );
        }
    }

    format!(
        "byte mismatch with identical line rendering (expected {} bytes, actual {} bytes)",
        expected.len(),
        actual.len()
    )
}

fn collect_source_files(root: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        let file_type = entry.file_type().unwrap();
        if file_type.is_dir() {
            collect_source_files(&path, files);
        } else if file_type.is_file() {
            files.push(path);
        }
    }
}

fn hex_digest(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn source_tree_fingerprint(root: &Path) -> (u64, String) {
    let mut files = Vec::new();
    collect_source_files(root, &mut files);
    files.sort_by(|left, right| {
        let left = left.strip_prefix(root).unwrap().to_string_lossy();
        let right = right.strip_prefix(root).unwrap().to_string_lossy();
        left.cmp(&right)
    });

    let mut total_bytes = 0;
    let mut hasher = Sha256::new();
    for file in files {
        let relative = file
            .strip_prefix(root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        let bytes = fs::read(&file).unwrap();
        total_bytes += bytes.len() as u64;
        hasher.update(relative.as_bytes());
        hasher.update([0]);
        hasher.update(&bytes);
        hasher.update([0]);
    }

    (
        total_bytes,
        format!("sha256:{}", hex_digest(&hasher.finalize())),
    )
}

fn assert_graph_parity_fixture_present(case: &GraphParityCase) {
    let source = repo_path(&case.source);
    assert!(
        source.exists(),
        "{} parity fixture missing at {}; refresh {} before running cargo test",
        case.name,
        source.display(),
        case.source
    );
    let (source_byte_size, source_tree_hash) = source_tree_fingerprint(&source);
    assert_eq!(
        source_byte_size, case.source_byte_size,
        "{} source byte count drifted from shared canonical input",
        case.name
    );
    assert_eq!(
        source_tree_hash, case.source_tree_hash,
        "{} source tree hash drifted from shared canonical input",
        case.name
    );

    let canonical_graph = repo_path(&case.canonical_graph);
    assert!(
        canonical_graph.exists(),
        "{} canonical graph snapshot missing at {}",
        case.name,
        canonical_graph.display()
    );
}

fn extract_graph_bytes(case: &GraphParityCase) -> Vec<u8> {
    let graph_path = unique_path(&format!("{}-parity-graph", case.name), "json");
    let mut command = Command::new(env!("CARGO_BIN_EXE_legitimacy"));
    command.current_dir(env!("CARGO_MANIFEST_DIR"));
    command.args(["extract", case.source.as_str()]);
    if case.allow_partial {
        command.arg("--allow-partial");
    }
    command.args(["--emit-graph", graph_path.to_str().unwrap()]);

    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{} extract failed: {}",
        case.name,
        String::from_utf8_lossy(&output.stderr)
    );

    let bytes = fs::read(&graph_path).unwrap();
    fs::remove_file(graph_path).unwrap();
    bytes
}

#[test]
fn autogen_extracted_graph_matches_canonical_rust_encoding() {
    let source = repo_path(AUTOGEN_SOURCE);
    assert!(
        source.exists(),
        "autogen parity fixture missing at {}; refresh audits/fixtures/sources/leaderboard/autogen before running cargo test",
        source.display()
    );

    let graph_path = unique_path("autogen-parity-graph", "json");
    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .args([
            "extract",
            AUTOGEN_SOURCE,
            "--emit-graph",
            graph_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "autogen extract failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let actual_bytes = fs::read(&graph_path).unwrap();
    let actual_graph: GovernanceGraph = serde_json::from_slice(&actual_bytes).unwrap();
    let expected_graph = autogen_canonical_graph();
    assert_eq!(
        actual_graph, expected_graph,
        "autogen extracted graph drifted"
    );

    let expected_bytes = serde_json::to_vec_pretty(&expected_graph).unwrap();
    assert_eq!(
        actual_bytes,
        expected_bytes,
        "autogen extracted graph JSON drifted: {}",
        mismatch_context(&expected_bytes, &actual_bytes)
    );

    fs::remove_file(graph_path).unwrap();
}

#[test]
fn shared_canonical_inputs_include_codex_hooks_fixture() {
    let cases = canonical_graph_cases();
    let case = cases
        .iter()
        .find(|case| case.source == "audits/fixtures/sources/leaderboard/codex-hooks")
        .expect("shared canonical inputs should include the Codex hooks fixture");

    assert_eq!(case.name, "codex");
    assert!(!case.allow_partial);
    assert_eq!(case.canonical_graph, "audits/leaderboard/codex-graph.json");
    assert_eq!(case.source_byte_size, 89739);
    assert_eq!(
        case.source_tree_hash,
        "sha256:120fe31d3e12be227b379b6a12e199d9dbca5fcdb4bcfcd70c79896a372f4741"
    );
}

#[test]
fn shared_canonical_inputs_include_claude_agent_sdk_hooks_fixture() {
    let cases = canonical_graph_cases();
    let case = cases
        .iter()
        .find(|case| case.source == "audits/fixtures/sources/leaderboard/claude-agent-sdk-hooks")
        .expect("shared canonical inputs should include the Claude Agent SDK hooks fixture");

    assert_eq!(case.name, "claude-agent-sdk");
    assert!(!case.allow_partial);
    assert_eq!(
        case.canonical_graph,
        "audits/leaderboard/claude-agent-sdk-graph.json"
    );
    assert_eq!(case.source_byte_size, 123885);
    assert_eq!(
        case.source_tree_hash,
        "sha256:5b3e32a718c1d2655cda0c495317e51a9ae913e50299ea40320b56930e892ec0"
    );
}

#[test]
fn leaderboard_extracted_graphs_are_byte_identical_across_runs_and_match_canonical_snapshots() {
    for case in canonical_graph_cases() {
        assert_graph_parity_fixture_present(&case);

        let first = extract_graph_bytes(&case);
        let second = extract_graph_bytes(&case);
        assert_eq!(
            first,
            second,
            "{} extracted graph JSON is non-deterministic across runs: {}",
            case.name,
            mismatch_context(&first, &second)
        );

        let canonical = fs::read(repo_path(&case.canonical_graph)).unwrap();
        assert_eq!(
            first,
            canonical,
            "{} extracted graph JSON drifted from committed canonical snapshot: {}",
            case.name,
            mismatch_context(&canonical, &first)
        );
    }
}
