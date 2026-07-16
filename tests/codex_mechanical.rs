#![allow(deprecated)]

use std::path::{Path, PathBuf};
use std::{collections::BTreeMap, fmt, fs};

use legitimacy::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceGraph, GovernanceNode,
    GraphBuilder, NodeId, Verdict,
    axioms::{
        binary::{BinaryDelta, BinaryShock},
        graph::{
            consistency::check_graph_consistency,
            monotonicity::{check_graph_monotonicity, check_graph_monotonicity_positive_delta},
            solidarity::check_graph_solidarity,
        },
    },
};

const CODEX_HOOKS_ROOT: &str = "audits/fixtures/sources/leaderboard/codex-hooks";
const CODEX_MECHANICAL_ROOT: &str = "audits/fixtures/sources/leaderboard/codex-mechanical";

fn codex_hooks_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(CODEX_HOOKS_ROOT)
}

fn codex_mechanical_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(CODEX_MECHANICAL_ROOT)
}

#[derive(Clone, Debug)]
struct SourceSpan {
    relative_path: &'static str,
    start_line: usize,
    end_line: usize,
}

impl fmt::Display for SourceSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.start_line == self.end_line {
            write!(f, "{}#L{}", self.relative_path, self.start_line)
        } else {
            write!(
                f,
                "{}#L{}-L{}",
                self.relative_path, self.start_line, self.end_line
            )
        }
    }
}

#[derive(Clone, Debug)]
struct MechanicalCodexGraph {
    graph: GovernanceGraph,
    claims: Vec<GovernanceClaim>,
    deltas: Vec<BinaryDelta>,
    shocks: Vec<BinaryShock>,
    source_spans: Vec<(&'static str, SourceSpan)>,
}

#[test]
#[allow(deprecated)]
fn mechanical_codex_source_graph_distinguishes_schema_polarity_from_legacy_delta() {
    let extracted = mechanically_extract_codex_graph();

    let consistency = check_graph_consistency(&extracted.graph, &extracted.claims).unwrap();
    let solidarity =
        check_graph_solidarity(&extracted.graph, &extracted.claims, &extracted.shocks).unwrap();
    let monotonicity =
        check_graph_monotonicity(&extracted.graph, &extracted.claims, &extracted.deltas).unwrap();
    let legacy_monotonicity = check_graph_monotonicity_positive_delta(
        &extracted.graph,
        &extracted.claims,
        &extracted.deltas,
    )
    .unwrap();

    assert!(
        matches!(consistency, Verdict::Admissible { .. }),
        "mechanically extracted graph should stay consistent on the audit fixture: {consistency:?}"
    );
    assert!(
        matches!(solidarity, Verdict::Admissible { .. }),
        "mechanically extracted graph should stay solidary on the audit fixture: {solidarity:?}"
    );

    assert!(
        matches!(monotonicity, Verdict::Admissible { .. }),
        "schema-aware polarity treats invalid/unsupported hooks as lower-better: {monotonicity:?}"
    );

    let Verdict::Rejected { counterexample, .. } = legacy_monotonicity else {
        panic!(
            "legacy positive-delta check should retain the old counterexample: {legacy_monotonicity:?}"
        );
    };

    let source_trace = extracted
        .source_spans
        .iter()
        .map(|(label, span)| format!("{label}: {span}"))
        .collect::<Vec<_>>()
        .join("; ");
    println!(
        "mechanical Codex counterexample: {}; source trace: {}",
        counterexample.description, source_trace
    );

    assert!(
        counterexample
            .description
            .contains("hook_invalid_or_unsupported"),
        "counterexample should strengthen the mechanically extracted invalid/unsupported hook branch: {counterexample:?}"
    );
}

fn mechanically_extract_codex_graph() -> MechanicalCodexGraph {
    let approval_presets = extract_approval_preset_span();
    let permission_profile = extract_permission_profile_span();
    let exec_approval = extract_exec_approval_span();
    let pre_tool_use = extract_pre_tool_use_span();

    let graph = GraphBuilder::new()
        .and_then(|builder| builder.add_node(approval_preset_node()))
        .and_then(|builder| builder.add_node(permission_profile_node()))
        .and_then(|builder| builder.add_node(exec_approval_node()))
        .and_then(|builder| builder.add_node(pre_tool_use_node()))
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("approval-preset").unwrap(),
                NodeId::new("permission-profile").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("permission-profile").unwrap(),
                NodeId::new("exec-approval").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("exec-approval").unwrap(),
                NodeId::new("pre-tool-hook").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap();

    MechanicalCodexGraph {
        graph,
        claims: mechanical_audit_claims(),
        deltas: vec![BinaryDelta {
            field: "hook_invalid_or_unsupported".to_string(),
            delta: 1.0,
        }],
        shocks: vec![BinaryShock {
            field: "strength".to_string(),
            delta: 0.05,
        }],
        source_spans: vec![
            ("approval preset", approval_presets),
            ("permission profile", permission_profile),
            ("exec approval", exec_approval),
            ("pre-tool hook", pre_tool_use),
        ],
    }
}

fn approval_preset_node() -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new("approval-preset").unwrap(),
        name: "approval-preset".to_string(),
        gates: vec![Gate::ThresholdGate {
            field: "full_access".to_string(),
            min: 1.0,
            decision: Decision::Deny,
        }],
        default: Decision::Escalate,
        combination: GateLogic::FirstMatch,
    }
}

fn permission_profile_node() -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new("permission-profile").unwrap(),
        name: "permission-profile".to_string(),
        gates: vec![
            Gate::ThresholdGate {
                field: "profile_restricted".to_string(),
                min: 1.0,
                decision: Decision::Escalate,
            },
            Gate::ThresholdGate {
                field: "runtime_roots_readable".to_string(),
                min: 1.0,
                decision: Decision::Escalate,
            },
        ],
        default: Decision::Deny,
        combination: GateLogic::AnyMustPass,
    }
}

fn exec_approval_node() -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new("exec-approval").unwrap(),
        name: "exec-approval".to_string(),
        gates: vec![
            Gate::ThresholdGate {
                field: "approval_forbidden".to_string(),
                min: 1.0,
                decision: Decision::Deny,
            },
            Gate::ThresholdGate {
                field: "needs_approval".to_string(),
                min: 1.0,
                decision: Decision::Escalate,
            },
            Gate::ThresholdGate {
                field: "skip_exec_approval".to_string(),
                min: 1.0,
                decision: Decision::Escalate,
            },
        ],
        default: Decision::Deny,
        combination: GateLogic::FirstMatch,
    }
}

fn pre_tool_use_node() -> GovernanceNode {
    GovernanceNode::Binary {
        id: NodeId::new("pre-tool-hook").unwrap(),
        name: "pre-tool-hook".to_string(),
        gates: vec![
            Gate::ThresholdGate {
                field: "hook_invalid_or_unsupported".to_string(),
                min: 1.0,
                decision: Decision::Deny,
            },
            Gate::ThresholdGate {
                field: "hook_blocks".to_string(),
                min: 1.0,
                decision: Decision::Permit,
            },
        ],
        default: Decision::Deny,
        combination: GateLogic::FirstMatch,
    }
}

fn mechanical_audit_claims() -> Vec<GovernanceClaim> {
    vec![
        hook_claim("hook-valid-low", 0.55, false),
        hook_claim("hook-valid-high", 0.90, false),
        hook_claim("hook-invalid", 0.70, false),
    ]
}

fn hook_claim(claimant_id: &str, strength: f64, invalid_or_unsupported: bool) -> GovernanceClaim {
    GovernanceClaim {
        claimant_id: claimant_id.to_string(),
        strength,
        priority_class: Some("hook-block".to_string()),
        path: Some("/workspace/src/main.rs".to_string()),
        action: Some("exec_command".to_string()),
        content: Some("rm -rf /tmp/demo".to_string()),
        metrics: BTreeMap::from([
            ("approval_forbidden".to_string(), 0.0),
            ("full_access".to_string(), 0.0),
            ("hook_blocks".to_string(), 1.0),
            (
                "hook_invalid_or_unsupported".to_string(),
                if invalid_or_unsupported { 1.0 } else { 0.0 },
            ),
            ("needs_approval".to_string(), 1.0),
            ("profile_restricted".to_string(), 1.0),
            ("runtime_roots_readable".to_string(), 1.0),
            ("skip_exec_approval".to_string(), 0.0),
        ]),
    }
}

fn extract_approval_preset_span() -> SourceSpan {
    span_for(
        "utils/approval-presets/src/lib.rs",
        "id: \"full-access\"",
        "sandbox: SandboxPolicy::DangerFullAccess",
    )
}

fn extract_permission_profile_span() -> SourceSpan {
    span_for(
        "core/src/config/permissions.rs",
        "pub(crate) fn compile_permission_profile(",
        "readable_roots.push(execve_wrapper_root);",
    )
}

fn extract_exec_approval_span() -> SourceSpan {
    span_for(
        "core/src/tools/sandboxing.rs",
        "pub(crate) fn default_exec_approval_requirement(",
        "ExecApprovalRequirement::Skip",
    )
}

fn extract_pre_tool_use_span() -> SourceSpan {
    let relabel = line_for(
        "hooks/src/events/pre_tool_use.rs",
        "tool_name: \"Bash\".to_string(),",
    );
    let invalid_branch = line_for(
        "hooks/src/events/pre_tool_use.rs",
        "if let Some(invalid_reason) = parsed.invalid_reason {",
    );
    let serialization_fail_open = line_for_after(
        "hooks/src/events/pre_tool_use.rs",
        "fn serialization_failure_outcome(",
        "should_block: false,",
    );

    SourceSpan {
        relative_path: "hooks/src/events/pre_tool_use.rs",
        start_line: relabel,
        end_line: serialization_fail_open.max(invalid_branch),
    }
}

fn span_for(relative_path: &'static str, start: &str, end: &str) -> SourceSpan {
    SourceSpan {
        relative_path,
        start_line: line_for(relative_path, start),
        end_line: line_for(relative_path, end),
    }
}

fn line_for(relative_path: &'static str, needle: &str) -> usize {
    let normalized = relative_path
        .strip_prefix("hooks/src/events/")
        .unwrap_or(relative_path);
    let full_path = if relative_path.starts_with("hooks/src/events/") {
        codex_hooks_root().join(normalized)
    } else {
        codex_mechanical_root().join(relative_path)
    };
    let contents = fs::read_to_string(&full_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", full_path.display()));

    contents
        .lines()
        .enumerate()
        .find_map(|(index, line)| line.contains(needle).then_some(index + 1))
        .unwrap_or_else(|| panic!("failed to find `{needle}` in {}", full_path.display()))
}

fn line_for_after(relative_path: &'static str, anchor: &str, needle: &str) -> usize {
    let normalized = relative_path
        .strip_prefix("hooks/src/events/")
        .unwrap_or(relative_path);
    let full_path = if relative_path.starts_with("hooks/src/events/") {
        codex_hooks_root().join(normalized)
    } else {
        codex_mechanical_root().join(relative_path)
    };
    let contents = fs::read_to_string(&full_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", full_path.display()));
    let start_index = contents
        .lines()
        .position(|line| line.contains(anchor))
        .unwrap_or_else(|| panic!("failed to find `{anchor}` in {}", full_path.display()));

    contents
        .lines()
        .enumerate()
        .skip(start_index)
        .find_map(|(index, line)| line.contains(needle).then_some(index + 1))
        .unwrap_or_else(|| {
            panic!(
                "failed to find `{needle}` after `{anchor}` in {}",
                full_path.display()
            )
        })
}
