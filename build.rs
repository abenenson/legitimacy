use std::{env, process::Command};

const GRAPH_FIXTURES: &[(&str, &str)] = &[
    (
        "LEGITIMACY_CODEX_GRAPH_COMMIT",
        "examples/graphs/codex-graph.json",
    ),
    (
        "LEGITIMACY_CLAUDE_AGENT_SDK_GRAPH_COMMIT",
        "examples/graphs/claude-agent-sdk-graph.json",
    ),
    (
        "LEGITIMACY_CLAUDE_CODE_GRAPH_COMMIT",
        "examples/graphs/claude-code-graph.json",
    ),
];

fn main() -> Result<(), String> {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=.git/HEAD");
    println!("cargo:rerun-if-changed=.git/index");
    println!("cargo:rerun-if-changed=.git/refs/heads/master");
    println!("cargo:rerun-if-changed=src");

    let manifest_dir = env::var("CARGO_MANIFEST_DIR")
        .map_err(|_| "CARGO_MANIFEST_DIR is unavailable".to_string())?;
    let mut build_commit = git_output(&manifest_dir, &["rev-parse", "--short=7", "HEAD"])?;
    if build_commit.is_empty() {
        return Err("no git commit found for audit-agent build".to_string());
    }
    if git_path_is_dirty(&manifest_dir, "src/")? {
        build_commit = dirty_suffix(&build_commit);
    }
    println!("cargo:rustc-env=LEGITIMACY_BUILD_GIT_COMMIT={build_commit}");

    for (env_var, fixture_path) in GRAPH_FIXTURES {
        println!("cargo:rerun-if-changed={fixture_path}");
        let commit = git_output(
            &manifest_dir,
            &["log", "-n", "1", "--format=%H", "--", fixture_path],
        )?;
        if commit.is_empty() {
            return Err(format!("no git commit found for {fixture_path}"));
        }
        let commit = if git_path_is_dirty(&manifest_dir, fixture_path)? {
            dirty_suffix(&commit)
        } else {
            commit
        };
        println!("cargo:rustc-env={env_var}={commit}");
    }
    Ok(())
}

fn git_path_is_dirty(manifest_dir: &str, path: &str) -> Result<bool, String> {
    Ok(!git_output(manifest_dir, &["status", "--porcelain", "--", path])?.is_empty())
}

fn dirty_suffix(commit: &str) -> String {
    format!("{commit}-dirty")
}

fn git_output(manifest_dir: &str, args: &[&str]) -> Result<String, String> {
    let output = Command::new("git")
        .args(args)
        .current_dir(manifest_dir)
        .output()
        .map_err(|_| "failed to run git".to_string())?;
    if !output.status.success() {
        return Err(format!(
            "git {} failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    String::from_utf8(output.stdout)
        .map(|stdout| stdout.trim().to_string())
        .map_err(|_| "git output was not UTF-8".to_string())
}
