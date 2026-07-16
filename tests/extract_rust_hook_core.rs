use legitimacy::{
    Decision, ExtractionOptions, Gate,
    extract::{ExtractionMode, parse_rust_hook_core},
    extract_governance_artifacts,
};
use std::{
    fs,
    path::{Path, PathBuf},
    time::{SystemTime, UNIX_EPOCH},
};

fn unique_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-rust-hook-core-{label}-{nanos}"))
}

fn write_source(root: &Path, source: &str) {
    fs::create_dir_all(root).unwrap();
    fs::write(root.join("hooks.rs"), source).unwrap();
}

fn theorem_options() -> ExtractionOptions {
    ExtractionOptions {
        allow_partial: false,
        mode: ExtractionMode::TheoremBacked,
    }
}

const VALID_CORE: &str = r#"
enum HookResult { Allow, Deny, Ask, Block }

fn on_PreToolUse(input: HookInput) -> HookResult {
    match input.event {
        "PreToolUse" => HookResult::Deny,
        _ => HookResult::Allow,
    }
}

register_hook!("PreToolUse", on_PreToolUse);
"#;

#[test]
fn theorem_backed_rust_core_ignores_misleading_comments_and_dead_code() {
    let root = unique_dir("comments-dead-code");
    write_source(
        &root,
        r#"
// register_hook!("CommentOnly", on_fake);
// HookResult::Block in a comment must not become a gate.
enum HookResult { Allow, Deny, Ask, Block }

fn on_PreToolUse(input: HookInput) -> HookResult {
    return HookResult::Allow;
    HookResult::Block
}

register_hook!("PreToolUse", on_PreToolUse);
"#,
    );

    let graph = extract_governance_artifacts(&root, theorem_options())
        .expect("RustHookCore source should extract")
        .graph;
    let values = graph
        .nodes
        .values()
        .flat_map(|node| match node {
            legitimacy::GovernanceNode::Binary { gates, .. } => gates.clone(),
            _ => Vec::new(),
        })
        .filter_map(|gate| match gate {
            Gate::ExactMatch { value, .. } => Some(value),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(values, vec!["allow".to_string()]);
}

#[test]
fn theorem_backed_rust_core_rejects_renamed_decision_enums() {
    let source = r#"
enum Permission { Allow, Deny }
enum HookResult { Allow, Deny }
fn on_PreToolUse(input: HookInput) -> HookResult {
    Permission::Deny
}
register_hook!("PreToolUse", on_PreToolUse);
"#;

    let error = parse_rust_hook_core(source).expect_err("renamed enum must refuse");
    assert!(error.to_string().contains("decision variants"), "{error}");
}

#[test]
fn theorem_backed_rust_core_rejects_dynamic_dispatch() {
    let source = r#"
enum HookResult { Allow, Deny }
fn on_PreToolUse(input: HookInput) -> HookResult {
    let callback: Box<dyn Fn(HookInput) -> HookResult>;
    HookResult::Allow
}
register_hook!("PreToolUse", on_PreToolUse);
"#;

    let error = parse_rust_hook_core(source).expect_err("dynamic dispatch must refuse");
    assert!(error.to_string().contains("dynamic dispatch"), "{error}");
}

#[test]
fn theorem_backed_rust_core_ignores_dynamic_dispatch_text_in_comments() {
    let source = r#"
// Box<dyn Fn(HookInput) -> HookResult> appears only in a comment.
enum HookResult { Allow, Deny }
fn on_PreToolUse(input: HookInput) -> HookResult {
    HookResult::Allow
}
register_hook!("PreToolUse", on_PreToolUse);
"#;

    let ast =
        parse_rust_hook_core(source).expect("comment-only dynamic dispatch text must not reject");
    assert_eq!(ast.hooks[0].name, "on_PreToolUse");
}

#[test]
fn theorem_backed_rust_core_builds_registered_graph() {
    let root = unique_dir("registered-graph");
    write_source(&root, VALID_CORE);

    let artifacts = extract_governance_artifacts(&root, theorem_options())
        .expect("registered RustHookCore source should extract");
    assert!(
        artifacts
            .recognized_nodes
            .iter()
            .any(|node| node.node_id == "hooks.rs::on_PreToolUse"),
        "expected hook node, got {:?}",
        artifacts.recognized_nodes
    );
    assert!(
        artifacts.graph.nodes.values().any(|node| matches!(
            node,
            legitimacy::GovernanceNode::Binary {
                default: Decision::Permit,
                ..
            }
        )),
        "expected a permitting default for Allow fallback"
    );
}

#[test]
fn theorem_backed_rust_core_reports_real_source_spans() {
    let root = unique_dir("source-spans");
    write_source(
        &root,
        r#"
enum HookResult { Allow, Deny, Ask, Block }

fn on_PreToolUse(input: HookInput) -> HookResult {
    match input.event {
        "PreToolUse" => HookResult::Deny,
        _ => HookResult::Allow,
    }
}

register_hook!(
    "PreToolUse",
    on_PreToolUse
);
"#,
    );

    let artifacts = extract_governance_artifacts(&root, theorem_options())
        .expect("registered RustHookCore source should extract");
    let hook = artifacts
        .recognized_nodes
        .iter()
        .find(|node| node.node_id == "hooks.rs::on_PreToolUse")
        .expect("hook node should be recognized");
    let registration = artifacts
        .recognized_nodes
        .iter()
        .find(|node| node.node_id == "hooks.rs::registration::PreToolUse::on_PreToolUse")
        .expect("registration node should be recognized");

    assert_eq!((hook.line_start, hook.line_end), (4, 9));
    assert_eq!((registration.line_start, registration.line_end), (11, 14));
    assert_ne!((hook.line_start, hook.line_end), (1, 1));
    assert_ne!((registration.line_start, registration.line_end), (1, 1));
}

#[test]
fn theorem_backed_rust_core_covers_codex_user_prompt_submit_fixture() {
    let root = PathBuf::from("tests/fixtures/rust_hook_core_codex_hooks");
    let artifacts = extract_governance_artifacts(&root, theorem_options())
        .expect("codex UserPromptSubmit RustHookCore fixture should extract");
    assert!(
        artifacts.recognized_nodes.iter().any(|node| {
            node.node_id == "user_prompt_submit.rs::on_UserPromptSubmit"
                && node
                    .rationale
                    .iter()
                    .any(|line| line.contains("extractRustHookCore_decision_equivalent"))
        }),
        "expected theorem-backed Codex hook node, got {:?}",
        artifacts.recognized_nodes
    );
}
