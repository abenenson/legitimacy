use legitimacy::extract::parse_rust_hook_core;
use std::{fs, path::PathBuf, process::Command};

const FIXTURE: &str = include_str!("fixtures/rust_hook_core_codex_hooks/user_prompt_submit.rs");

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        let path =
            std::env::temp_dir().join(format!("legitimacy-hook-fidelity-{}", uuid::Uuid::new_v4()));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn hook(body: &str) -> String {
    format!(
        "enum HookResult {{ Allow, Deny, Ask, Block }}\n\
         fn on_UserPromptSubmit(input: HookInput) -> HookResult {{ {body} }}\n\
         register_hook!(\"UserPromptSubmit\", on_UserPromptSubmit);\n"
    )
}

// Invoke the real Rust compiler, not a second implementation of match semantics.
fn execute(source: &str) -> Vec<String> {
    let dir = Scratch::new();
    fs::write(dir.0.join("hook.rs"), source).unwrap();
    fs::write(
        dir.0.join("main.rs"),
        r#"
#![allow(dead_code, non_snake_case, unreachable_code, unreachable_patterns, unused_variables)]
struct HookInput { event: &'static str }
macro_rules! register_hook { ($($tokens:tt)*) => {}; }
include!("hook.rs");
fn main() {
    for event in ["UserPromptSubmit", "OtherEvent", "Unknown"] {
        let result = on_UserPromptSubmit(HookInput { event });
        println!("{}", match result {
            HookResult::Allow => "Allow", HookResult::Deny => "Deny",
            HookResult::Ask => "Ask", HookResult::Block => "Block",
        });
    }
}
"#,
    )
    .unwrap();
    let compiler = Command::new("rustc")
        .args(["--edition=2024", "main.rs", "-o", "execute"])
        .current_dir(&dir.0)
        .output()
        .unwrap();
    assert!(
        compiler.status.success(),
        "{}",
        String::from_utf8_lossy(&compiler.stderr)
    );
    let output = Command::new(dir.0.join("execute")).output().unwrap();
    assert!(output.status.success(), "{output:?}");
    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(str::to_owned)
        .collect()
}

#[test]
fn decision_changing_source_variants_are_refused_before_cli_exports() {
    assert_eq!(execute(FIXTURE), ["Block", "Allow", "Allow"]);
    for (source, reason) in [
        (
            FIXTURE.replace(
                "\"UserPromptSubmit\" =>",
                "\"UserPromptSubmit\" if false =>",
            ),
            "match guards",
        ),
        (
            FIXTURE.replace("match input.event", "match \"OtherEvent\""),
            "match scrutinee",
        ),
    ] {
        assert_eq!(execute(&source), ["Allow", "Allow", "Allow"]);
        let error = parse_rust_hook_core(&source).expect_err("behavior-changing form must refuse");
        assert!(error.to_string().contains(reason), "{error}");
        let dir = Scratch::new();
        let input = dir.0.join("input");
        fs::create_dir(&input).unwrap();
        fs::write(input.join("hook.rs"), source).unwrap();
        let graph = dir.0.join("graph.json");
        let witness = dir.0.join("witness.json");
        let output = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
            .arg("extract")
            .arg(input)
            .args(["--mode", "theorem-backed", "--synthetic", "--emit-graph"])
            .arg(&graph)
            .arg("--emit-theorem-witness")
            .arg(&witness)
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "unsupported source must fail: {output:?}"
        );
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(reason),
            "{output:?}"
        );
        assert!(
            !graph.exists() && !witness.exists(),
            "failed extraction must not export artifacts"
        );
    }
}

#[test]
fn event_precedence_and_discarded_values_cannot_be_erased() {
    for (body, actual, reason) in [
        (
            "match input.event { _ => HookResult::Allow, \"UserPromptSubmit\" => HookResult::Block }",
            "Allow",
            "final arm",
        ),
        (
            "match input.event { \"UserPromptSubmit\" => HookResult::Allow, \"UserPromptSubmit\" => HookResult::Block, _ => HookResult::Deny }",
            "Allow",
            "duplicate event",
        ),
        (
            "match input.event { \"UserPromptSubmit\" => HookResult::Block, _ => HookResult::Allow }; HookResult::Allow",
            "Allow",
            "discarded expressions",
        ),
        (
            "HookResult::Block; HookResult::Allow",
            "Allow",
            "discarded expressions",
        ),
        (
            "match input.event { #[cfg(any())] \"UserPromptSubmit\" => HookResult::Block, _ => HookResult::Allow }",
            "Allow",
            "attributes",
        ),
    ] {
        let source = hook(body);
        assert_eq!(execute(&source)[0], actual, "{body}");
        let error = parse_rust_hook_core(&source).expect_err(body);
        assert!(error.to_string().contains(reason), "{body}: {error}");
    }
}

#[test]
fn accepted_event_summary_agrees_with_rust_execution() {
    let arms = "\"UserPromptSubmit\" => HookResult::Block, \"OtherEvent\" => HookResult::Ask, _ => HookResult::Deny";
    for source in [
        FIXTURE.to_owned(),
        FIXTURE.replace("input", "request"),
        hook("HookResult::Allow"),
        hook("return HookResult::Deny; HookResult::Allow"),
        hook(&format!("match input.event {{ {arms} }}")),
        hook(&format!("return match input.event {{ {arms} }};")),
        hook(
            "match input.event { \"OtherEvent\" => HookResult::Ask, \"UserPromptSubmit\" => HookResult::Block, _ => HookResult::Deny }",
        ),
        hook(
            "match input.event { r#\"UserPromptSubmit\"# => HookResult::Block, _ => HookResult::Allow }",
        ),
    ] {
        let ast = parse_rust_hook_core(&source).unwrap();
        let hook = &ast.hooks[0];
        let summarized: Vec<_> = ["UserPromptSubmit", "OtherEvent", "Unknown"]
            .iter()
            .map(|event| {
                let decision = hook
                    .event_decisions
                    .iter()
                    .find(|arm| arm.event == *event)
                    .map(|arm| &arm.decision)
                    .or(hook.default_decision.as_ref())
                    .unwrap();
                format!("{decision:?}")
            })
            .collect();
        assert_eq!(execute(&source), summarized, "{source}");
    }
}

#[test]
fn unresolved_effects_and_binding_forms_are_refused() {
    for source in [
        hook("std::process::exit(0); HookResult::Allow"),
        hook("let input; HookResult::Allow"),
        hook("Allow"),
        hook("match input.event { _ => HookResult::Block } HookResult::Allow"),
        hook("match input.other { _ => HookResult::Allow }"),
        hook("match unrelated.event { _ => HookResult::Allow }"),
        hook(
            "match input.event { Event::UserPromptSubmit => HookResult::Block, _ => HookResult::Allow }",
        ),
        hook("match input.event { \"UserPromptSubmit\" => HookResult::Block }"),
        hook("match input.event { _ => HookResult::Allow, _ => HookResult::Block }"),
        hook("match input.event { \"A\" | \"B\" => HookResult::Block, _ => HookResult::Allow }"),
        hook("<HookResult as Other>::Allow"),
        FIXTURE.replace("input: HookInput", "HookInput { event }: HookInput"),
        FIXTURE.replace("input: HookInput", "input: other::HookInput"),
        FIXTURE.replace("enum HookResult", "#[cfg(any())]\nenum HookResult"),
        FIXTURE.replace("    Block,", "    Block(String),"),
    ] {
        assert!(
            parse_rust_hook_core(&source).is_err(),
            "unexpectedly accepted: {source}"
        );
    }
}

#[test]
fn registration_arguments_are_parsed_without_erasing_syntax() {
    let original = "register_hook!(\"UserPromptSubmit\", on_UserPromptSubmit);";
    for replacement in [
        "register_hook!(\"UserPromptSubmit\", other::on_UserPromptSubmit);",
        "register_hook!(\"UserPromptSubmit\", on_UserPromptSubmit::<HookInput>);",
        "register_hook!(\"UserPromptSubmit\", on_UserPromptSubmit());",
        "register_hook!(\"UserPromptSubmit\", false, on_UserPromptSubmit);",
        "register_hook!(EVENT, on_UserPromptSubmit);",
        "register_hook!(\"UserPromptSubmit\");",
        "register_hook!(\"UserPromptSubmit\", #[cfg(any())] on_UserPromptSubmit);",
    ] {
        assert!(
            parse_rust_hook_core(&FIXTURE.replace(original, replacement)).is_err(),
            "{replacement}"
        );
    }
    for event in ["r#\"UserPromptSubmit\"#", "\"User\\u{50}romptSubmit\""] {
        let source = FIXTURE.replace(
            original,
            &format!("register_hook!({event}, on_UserPromptSubmit,);"),
        );
        let ast = parse_rust_hook_core(&source).unwrap();
        assert_eq!(ast.registrations[0].event, "UserPromptSubmit");
        assert_eq!(ast.registrations[0].callback, "on_UserPromptSubmit");
        assert_eq!(ast.registrations[0].source_span.line_start, 15);
    }
}

fn extract_sources(
    sources: &[(&str, &str)],
) -> Result<legitimacy::GovernanceExtractionArtifacts, legitimacy::LegitimacyError> {
    let dir = Scratch::new();
    for (name, source) in sources {
        fs::write(dir.0.join(name), source).unwrap();
    }
    legitimacy::extract_governance_artifacts(
        &dir.0,
        legitimacy::ExtractionOptions {
            allow_partial: false,
            mode: legitimacy::extract::ExtractionMode::TheoremBacked,
        },
    )
}

#[test]
fn unresolved_ambiguous_and_duplicate_registrations_fail_the_whole_extraction() {
    let missing = format!("{FIXTURE}\nregister_hook!(\"Other\", on_missing);");
    let duplicate =
        format!("{FIXTURE}\nregister_hook!(\"UserPromptSubmit\", on_UserPromptSubmit);");
    for (sources, reason) in [
        (
            vec![("a.rs", missing.as_str())],
            "unresolved RustHookCore callback",
        ),
        (
            vec![("a.rs", FIXTURE), ("b.rs", FIXTURE)],
            "ambiguous RustHookCore callback",
        ),
        (
            vec![("a.rs", duplicate.as_str())],
            "duplicate RustHookCore registration",
        ),
        (
            vec![
                ("a.rs", FIXTURE),
                (
                    "b.rs",
                    "enum HookResult { Allow, Block }\nregister_hook!(\"UserPromptSubmit\", on_UserPromptSubmit);",
                ),
            ],
            "duplicate RustHookCore registration",
        ),
    ] {
        let error = extract_sources(&sources).expect_err("all registrations must resolve uniquely");
        assert!(error.to_string().contains(reason), "{error}");
    }
    assert!(parse_rust_hook_core(&format!("{FIXTURE}\n{FIXTURE}")).is_err());
}

#[test]
fn distinct_registrations_and_unique_cross_file_callbacks_remain_supported() {
    let two = format!("{FIXTURE}\nregister_hook!(\"OtherEvent\", on_UserPromptSubmit);");
    let artifacts = extract_sources(&[("a.rs", &two)]).unwrap();
    assert_eq!(artifacts.recognized_nodes.len(), 3);
    assert_eq!(artifacts.recognized_edges.len(), 2);
    assert!(artifacts.resolution_issues.is_empty());

    let definition = FIXTURE.replace(
        "register_hook!(\"UserPromptSubmit\", on_UserPromptSubmit);",
        "",
    );
    let registration = "enum HookResult { Allow, Block }\nregister_hook!(\"UserPromptSubmit\", on_UserPromptSubmit);";
    let artifacts = extract_sources(&[("a.rs", &definition), ("b.rs", registration)]).unwrap();
    assert_eq!(artifacts.recognized_nodes.len(), 2);
    assert_eq!(artifacts.recognized_edges.len(), 1);
    assert!(artifacts.resolution_issues.is_empty());
}

#[test]
fn modeled_calls_and_declared_event_variants_remain_explicit() {
    let source = hook(
        "record_observation(); match input.event { HookEvent::UserPromptSubmit => HookResult::Block, _ => HookResult::Allow }",
    );
    let declared = format!("enum HookEvent {{ UserPromptSubmit, OtherEvent }}\n{source}");
    let ast = parse_rust_hook_core(&declared).unwrap();
    assert_eq!(ast.hooks[0].calls, ["record_observation"]);
    assert_eq!(ast.hooks[0].event_decisions[0].event, "UserPromptSubmit");
    // This is a modeled call label, not a proof of its implementation/effects.
    for source in [
        source,
        declared.replace("record_observation();", "record_observation(input);"),
        declared.replace("record_observation();", "other::record_observation();"),
        declared.replace("HookEvent::UserPromptSubmit", "HookEvent::Missing"),
        declared.replace(
            "HookEvent::UserPromptSubmit",
            "OtherEvent::UserPromptSubmit",
        ),
    ] {
        assert!(parse_rust_hook_core(&source).is_err(), "{source}");
    }
}
