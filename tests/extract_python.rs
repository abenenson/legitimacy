use std::path::Path;

use legitimacy::extract_governance;

const PYTHON_FIXTURE_ROOT: &str = "tests/fixtures";
const CLAUDE_AGENT_SDK_FIXTURE_ROOT: &str =
    "audits/fixtures/sources/leaderboard/claude-agent-sdk-hooks";

#[test]
fn extract_python_fixture_discovers_permission_gate_governance() {
    let source_dir = Path::new(PYTHON_FIXTURE_ROOT);
    let graph = extract_governance(source_dir).expect("python governance fixture should extract");
    let discovered_nodes = graph
        .nodes
        .keys()
        .map(ToString::to_string)
        .collect::<Vec<_>>();

    assert!(
        !graph.nodes.is_empty(),
        "expected at least one governance node from {}",
        source_dir.display()
    );
    assert!(
        discovered_nodes.iter().any(|node_id| {
            node_id.contains("sample_governance.py::guard_file_delete")
                || node_id.contains("sample_governance.py::review_write_access")
        }),
        "expected Python fixture governance nodes, got {discovered_nodes:?}"
    );
}

#[test]
fn extract_python_fixture_discovers_claude_agent_sdk_protocol_schema() {
    let source_dir = Path::new(CLAUDE_AGENT_SDK_FIXTURE_ROOT);
    let graph =
        extract_governance(source_dir).expect("Claude Agent SDK hook fixture should extract");
    let discovered_nodes = graph
        .nodes
        .keys()
        .map(ToString::to_string)
        .collect::<Vec<_>>();

    assert!(
        discovered_nodes
            .iter()
            .any(|node_id| node_id.contains("PreToolUseHookSpecificOutput")),
        "expected Claude Agent SDK PreToolUse hook schema node, got {discovered_nodes:?}"
    );
    assert!(
        discovered_nodes
            .iter()
            .any(|node_id| node_id.contains("PermissionResultDeny")),
        "expected Claude Agent SDK permission result schema node, got {discovered_nodes:?}"
    );
}
