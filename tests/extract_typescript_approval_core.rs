use legitimacy::extract::{
    ExtractionMode, ResolutionIssueKind, TypeScriptApprovalCoreApprovalResult,
    TypeScriptApprovalCorePolicyKind, parse_typescript_approval_core,
};
use legitimacy::{ExtractionOptions, GovernanceNode, extract_governance_artifacts};
use std::{
    fs,
    path::{Path, PathBuf},
    time::{SystemTime, UNIX_EPOCH},
};

const OPENCLAW_FAILOVER_POLICY: &str =
    "audits/fixtures/sources/leaderboard/openclaw-agents/failover-policy.ts";

fn unique_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-ts-approval-core-{label}-{nanos}"))
}

fn theorem_options() -> ExtractionOptions {
    ExtractionOptions {
        allow_partial: false,
        mode: ExtractionMode::TheoremBacked,
    }
}

fn write_source(root: &Path, name: &str, source: &str) {
    fs::create_dir_all(root).unwrap();
    fs::write(root.join(name), source).unwrap();
}

#[test]
fn theorem_backed_typescript_core_extracts_approval_union_handler_and_registration() {
    let source = r#"
export type Approval = "allow" | "deny" | "ask" | "escalate";

export interface Request {
  tool: string;
  decision?: Approval;
}

export const APPROVAL_ALLOWLIST = ["read", "inspect"] as const;

export function approve(req: Request): Approval {
  if (req.tool === "rm") {
    return "deny";
  }
  return "allow";
}

registerApprover("tool", approve);
"#;

    let ast = parse_typescript_approval_core(source).expect("core source should parse");
    assert_eq!(ast.approval_unions[0].name, "Approval");
    assert_eq!(ast.requests[0].fields[1].name, "decision");
    assert!(ast.requests[0].fields[1].approval_position);
    assert_eq!(
        ast.policies[0].kind,
        TypeScriptApprovalCorePolicyKind::Allowlist
    );
    assert_eq!(ast.handlers[0].name, "approve");
    assert_eq!(
        ast.handlers[0].results,
        vec![
            TypeScriptApprovalCoreApprovalResult::Allow,
            TypeScriptApprovalCoreApprovalResult::Deny
        ]
    );
    assert_eq!(ast.registrations[0].surface, "tool");
    assert_eq!(ast.registrations[0].handler, "approve");
    assert!(!ast.canonical_hash.is_empty());
}

#[test]
fn theorem_backed_typescript_core_accepts_async_promise_approval_handlers() {
    let source = r#"
type Approval = "allow" | "deny";

@registerApprover("network")
export async function approveNetwork(req: Request): Promise<Approval> {
  if (await fallback(req)) {
    return "allow";
  }
  return "deny";
}
"#;

    let ast = parse_typescript_approval_core(source).expect("async approval handler should parse");
    let handler = ast
        .handlers
        .iter()
        .find(|handler| handler.name == "approveNetwork")
        .expect("handler should be collected");
    assert!(handler.is_async);
    assert!(handler.calls.contains(&"fallback".to_string()));
    assert_eq!(ast.registrations[0].surface, "network");
    assert!(ast.registrations[0].via_decorator);
}

#[test]
fn theorem_backed_typescript_core_refuses_untyped_approval_literals() {
    let source = r#"
export function approve(req: Request): string {
  return "deny";
}
"#;

    let error = parse_typescript_approval_core(source)
        .expect_err("approval literals need an approval return type");
    assert!(
        error
            .to_string()
            .contains("without an approval return type"),
        "{error}"
    );
}

#[test]
fn theorem_backed_typescript_core_refuses_unsupported_typed_handlers() {
    let source = r#"
type Approval = "allow" | "deny";

export function approve(req: Request): Approval {
  switch (req.tool) {
    case "read":
      return "allow";
    default:
      return "deny";
  }
}
"#;

    let error = parse_typescript_approval_core(source)
        .expect_err("switch approval handlers are outside the modeled core");
    assert!(
        error.to_string().contains("unsupported 'switch'"),
        "{error}"
    );
}

#[test]
fn theorem_backed_typescript_core_ignores_unsupported_words_in_comments_and_strings() {
    let source = r#"
type Approval = "allow" | "deny";

export function approve(req: Request): Approval {
  const note = "switch for while try catch throw";
  // switch for while try catch throw
  return "allow";
}
"#;

    let ast = parse_typescript_approval_core(source)
        .expect("unsupported marker words in trivia and strings must not reject");
    assert_eq!(ast.handlers[0].name, "approve");
}

#[test]
fn theorem_backed_typescript_core_ignores_misleading_register_approver_text() {
    let source = r#"
type Approval = "allow" | "deny";

const marker = "registerApprover(\"tool\", fake)";
// @registerApprover("network")
export function approve(req: Request): Approval {
  return "allow";
}
"#;

    let ast = parse_typescript_approval_core(source)
        .expect("misleading registerApprover text must not register");
    assert!(
        ast.registrations.is_empty(),
        "string/comment markers must not create registrations: {:?}",
        ast.registrations
    );
}

#[test]
fn theorem_backed_typescript_core_accepts_unicode_identifier_names() {
    let source = r#"
type 承認 = "allow" | "deny";

export function 承認する(req: Request): 承認 {
  return "allow";
}

registerApprover("tool", 承認する);
"#;

    let ast = parse_typescript_approval_core(source)
        .expect("Unicode TypeScript identifiers should parse");
    assert_eq!(ast.approval_unions[0].name, "承認");
    assert_eq!(ast.handlers[0].name, "承認する");
    assert_eq!(ast.registrations[0].handler, "承認する");
}

#[test]
fn theorem_backed_typescript_core_discovers_unicode_caller_to_unicode_callee_edges() {
    let root = unique_dir("unicode-call-edge");
    write_source(
        &root,
        "approval.ts",
        r#"
type 承認 = "allow" | "deny";

export function 承認する(req: Request): 承認 {
  return "deny";
}

export function 呼び出し(req: Request): 承認 {
  承認する(req);
  return "allow";
}

registerApprover("unicode-callee", 承認する);
registerApprover("unicode-caller", 呼び出し);
"#,
    );

    let artifacts =
        extract_governance_artifacts(&root, theorem_options()).expect("TS core should extract");
    assert!(artifacts.graph.edges.iter().any(|edge| {
        edge.from.to_string() == "approval.ts::呼び出し"
            && edge.to.to_string() == "approval.ts::承認する"
    }));
}

#[test]
fn theorem_backed_typescript_core_discovers_ascii_caller_to_unicode_callee_edges() {
    let root = unique_dir("ascii-unicode-call-edge");
    write_source(
        &root,
        "approval.ts",
        r#"
type 承認 = "allow" | "deny";

export function 承認する(req: Request): 承認 {
  return "deny";
}

export function approve(req: Request): 承認 {
  承認する(req);
  return "allow";
}

registerApprover("unicode-callee", 承認する);
registerApprover("ascii-caller", approve);
"#,
    );

    let artifacts =
        extract_governance_artifacts(&root, theorem_options()).expect("TS core should extract");
    assert!(artifacts.graph.edges.iter().any(|edge| {
        edge.from.to_string() == "approval.ts::approve"
            && edge.to.to_string() == "approval.ts::承認する"
    }));
}

#[test]
fn theorem_backed_typescript_core_covers_openclaw_failover_policy_fixture() {
    let source = fs::read_to_string(OPENCLAW_FAILOVER_POLICY).unwrap();
    let ast = parse_typescript_approval_core(&source)
        .expect("OpenClaw failover-policy.ts should fit TypeScriptApprovalCore");
    let handlers = ast
        .handlers
        .iter()
        .map(|handler| handler.name.as_str())
        .collect::<Vec<_>>();
    assert!(
        handlers.contains(&"shouldAllowCooldownProbeForReason"),
        "expected OpenClaw failover handler, got {handlers:?}"
    );
    assert!(
        ast.handlers.iter().all(|handler| handler
            .results
            .contains(&TypeScriptApprovalCoreApprovalResult::Allow)
            && handler
                .results
                .contains(&TypeScriptApprovalCoreApprovalResult::Deny)),
        "boolean failover handlers should model allow/deny surfaces: {:?}",
        ast.handlers
    );
}

#[test]
fn theorem_backed_typescript_core_builds_registered_graph() {
    let root = unique_dir("registered");
    write_source(
        &root,
        "approval.ts",
        r#"
type Approval = "allow" | "deny" | "ask" | "escalate";
export function approve(req: Request): Approval {
  if (req.tool === "rm") {
    return "deny";
  }
  return "allow";
}
registerApprover("tool", approve);
"#,
    );

    let artifacts =
        extract_governance_artifacts(&root, theorem_options()).expect("TS core should extract");
    let node_ids = artifacts
        .graph
        .nodes
        .keys()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    assert!(
        node_ids.contains(&"approval.ts::registration::tool::approve".to_string()),
        "expected registration node, got {node_ids:?}"
    );
    assert!(
        node_ids.contains(&"approval.ts::approve".to_string()),
        "expected handler node, got {node_ids:?}"
    );
    assert!(artifacts.recognized_nodes.iter().any(|node| {
        node.rationale
            .iter()
            .any(|line| line.contains("extractTypeScriptApprovalCore_decision_equivalent"))
    }));
    assert!(artifacts.graph.edges.iter().any(|edge| {
        edge.from.to_string() == "approval.ts::registration::tool::approve"
            && edge.to.to_string() == "approval.ts::approve"
    }));
}

#[test]
fn theorem_backed_typescript_core_records_ambiguous_registered_handler_issue() {
    let root = unique_dir("ambiguous-handler");
    write_source(
        &root,
        "primary.ts",
        r#"
type Approval = "allow" | "deny";

export function approve(req: Request): Approval {
  return "allow";
}

registerApprover("tool", approve);
"#,
    );
    write_source(
        &root,
        "secondary.ts",
        r#"
type Approval = "allow" | "deny";

export function approve(req: Request): Approval {
  return "deny";
}
"#,
    );

    let artifacts =
        extract_governance_artifacts(&root, theorem_options()).expect("TS core should extract");
    assert!(
        artifacts.resolution_issues.iter().any(|issue| {
            issue.caller == "primary.ts::registration::tool::approve"
                && issue.target_symbol == "approve"
                && issue.kind == ResolutionIssueKind::Ambiguous
                && issue.candidates.len() == 2
                && issue
                    .candidates
                    .contains(&"primary.ts::approve".to_string())
                && issue
                    .candidates
                    .contains(&"secondary.ts::approve".to_string())
        }),
        "expected ambiguous handler resolution issue, got {:?}",
        artifacts.resolution_issues
    );
    assert!(artifacts.graph.edges.iter().any(|edge| {
        edge.from.to_string() == "primary.ts::registration::tool::approve"
            && edge.to.to_string() == "primary.ts::approve"
    }));
}

#[test]
fn theorem_backed_typescript_core_reports_real_source_spans() {
    let root = unique_dir("real-spans");
    write_source(
        &root,
        "approval.ts",
        r#"
type Approval = "allow" | "deny";

export function approve(req: Request): Approval {
  if (req.tool === "rm") {
    return "deny";
  }
  return "allow";
}

registerApprover("tool", approve);
"#,
    );

    let artifacts =
        extract_governance_artifacts(&root, theorem_options()).expect("TS core should extract");
    let span = node_span(&artifacts.recognized_nodes, "approval.ts::approve")
        .expect("handler node should have provenance");
    assert_ne!(span, (1, 1));
    assert!(span.0 > 1, "expected non-default start line, got {span:?}");
    assert!(
        span.1 > span.0,
        "multi-line handler should report a multi-line span, got {span:?}"
    );
}

#[test]
fn theorem_backed_typescript_core_extracts_openclaw_failover_fixture_graph() {
    let root = unique_dir("openclaw");
    fs::create_dir_all(&root).unwrap();
    fs::copy(OPENCLAW_FAILOVER_POLICY, root.join("failover-policy.ts")).unwrap();

    let artifacts = extract_governance_artifacts(&root, theorem_options())
        .expect("OpenClaw failover fixture should extract through theorem-backed TS lane");
    let handler = artifacts
        .graph
        .nodes
        .iter()
        .find(|(id, _)| id.to_string() == "failover-policy.ts::shouldAllowCooldownProbeForReason")
        .map(|(_, node)| node)
        .expect("OpenClaw shouldAllowCooldownProbeForReason node should exist");
    match handler {
        GovernanceNode::Binary { gates, .. } => {
            assert!(
                gates.len() >= 2,
                "boolean failover handler should expose allow/deny gates"
            );
        }
        _ => panic!("expected binary node"),
    }
}

fn node_span(
    nodes: &[legitimacy::RecognizedNodeProvenance],
    node_id: &str,
) -> Option<(usize, usize)> {
    nodes
        .iter()
        .find(|node| node.node_id == node_id)
        .map(|node| (node.line_start, node.line_end))
}
