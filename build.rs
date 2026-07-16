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

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=.git/HEAD");
    println!("cargo:rerun-if-changed=.git/index");
    println!("cargo:rerun-if-changed=.git/refs/heads/master");
    println!("cargo:rerun-if-changed=src");

    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR should be set");
    let mut build_commit = git_output(&manifest_dir, &["rev-parse", "--short=7", "HEAD"]);
    if build_commit.is_empty() {
        panic!("no git commit found for audit-agent build");
    }
    if git_path_is_dirty(&manifest_dir, "src/") {
        build_commit = dirty_suffix(&build_commit);
    }
    println!("cargo:rustc-env=LEGITIMACY_BUILD_GIT_COMMIT={build_commit}");

    for (env_var, fixture_path) in GRAPH_FIXTURES {
        println!("cargo:rerun-if-changed={fixture_path}");
        let commit = git_output(
            &manifest_dir,
            &["log", "-n", "1", "--format=%H", "--", fixture_path],
        );
        if commit.is_empty() {
            panic!("no git commit found for {}", fixture_path);
        }
        let commit = if git_path_is_dirty(&manifest_dir, fixture_path) {
            dirty_suffix(&commit)
        } else {
            commit
        };
        println!("cargo:rustc-env={env_var}={commit}");
    }
}

fn git_path_is_dirty(manifest_dir: &str, path: &str) -> bool {
    !git_output(manifest_dir, &["status", "--porcelain", "--", path]).is_empty()
}

fn dirty_suffix(commit: &str) -> String {
    format!("{commit}-dirty")
}

fn git_output(manifest_dir: &str, args: &[&str]) -> String {
    let output = Command::new("git")
        .args(args)
        .current_dir(manifest_dir)
        .output()
        .expect("failed to run git");
    if !output.status.success() {
        panic!(
            "git {} failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    String::from_utf8(output.stdout)
        .expect("git output should be utf-8")
        .trim()
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::dirty_suffix;

    #[test]
    fn dirty_suffix_marks_stale_fixture_commit_reference() {
        assert_eq!(
            dirty_suffix("f49fa1b4"),
            "f49fa1b4-dirty",
            "dirty fixture builds should distinguish stale committed graph commits"
        );
    }
}
