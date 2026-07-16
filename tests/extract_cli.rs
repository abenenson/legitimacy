use std::{
    fs,
    path::PathBuf,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

fn unique_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}"))
}

#[test]
fn synthetic_extract_respects_allow_partial() {
    let source_dir = unique_dir("extract-synthetic-partial");
    fs::create_dir_all(&source_dir).unwrap();
    fs::write(
        source_dir.join("policy.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn approval_gate(action: &str) -> Decision {
    if action == "read" {
        return Decision::Permit;
    }
    Decision::Deny
}
"#,
    )
    .unwrap();
    fs::write(
        source_dir.join("broken.py"),
        "class {{ template_syntax }}:\n    pass\n",
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args([
            "extract",
            source_dir.to_str().unwrap(),
            "--synthetic",
            "--allow-partial",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "synthetic extract should honor --allow-partial: {output:?}"
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("EXTRACTION REPORT"), "{stdout}");
    assert!(stdout.contains("coverage:"), "{stdout}");
}

#[test]
fn extract_cli_accepts_theorem_backed_python_hook_core_mode() {
    let source_dir = unique_dir("extract-theorem-backed");
    fs::create_dir_all(&source_dir).unwrap();
    fs::write(
        source_dir.join("hooks.py"),
        r#"
from typing import Literal, NotRequired, TypedDict

class PreToolUseHookSpecificOutput(TypedDict):
    hookEventName: Literal["PreToolUse"]
    permissionDecision: NotRequired[Literal["allow", "deny", "ask"]]
"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_legitimacy"))
        .args([
            "extract",
            source_dir.to_str().unwrap(),
            "--mode",
            "theorem-backed",
        ])
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "theorem-backed extract should succeed: {output:?}"
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("PreToolUseHookSpecificOutput"), "{stdout}");
}
