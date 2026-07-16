use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

struct AuditSnapshotCase {
    name: &'static str,
    source: &'static str,
    allow_partial: bool,
    remediation: &'static str,
    transcript: &'static str,
}

const AUTOGEN_CASE: AuditSnapshotCase = AuditSnapshotCase {
    name: "autogen",
    source: "audits/fixtures/sources/leaderboard/autogen",
    allow_partial: false,
    remediation: "refresh audits/fixtures/sources/leaderboard/autogen before running cargo test",
    transcript: "audits/leaderboard/autogen-extract.txt",
};

const CODEX_CASE: AuditSnapshotCase = AuditSnapshotCase {
    name: "codex",
    source: "audits/fixtures/sources/leaderboard/codex-hooks",
    allow_partial: false,
    remediation: "refresh audits/fixtures/sources/leaderboard/codex-hooks before running cargo test",
    transcript: "audits/leaderboard/codex-extract.txt",
};

const CLAUDE_AGENT_SDK_CASE: AuditSnapshotCase = AuditSnapshotCase {
    name: "claude-agent-sdk",
    source: "audits/fixtures/sources/leaderboard/claude-agent-sdk-hooks",
    allow_partial: false,
    remediation: "refresh audits/fixtures/sources/leaderboard/claude-agent-sdk-hooks before running cargo test",
    transcript: "audits/leaderboard/claude-agent-sdk-extract.txt",
};

const CREWAI_CASE: AuditSnapshotCase = AuditSnapshotCase {
    name: "crewai",
    source: "audits/fixtures/sources/leaderboard/crewai",
    allow_partial: true,
    remediation: "refresh audits/fixtures/sources/leaderboard/crewai before running cargo test",
    transcript: "audits/leaderboard/crewai-extract.txt",
};

const OPENCLAW_CASE: AuditSnapshotCase = AuditSnapshotCase {
    name: "openclaw",
    source: "audits/fixtures/sources/leaderboard/openclaw-infra",
    allow_partial: false,
    remediation: "refresh audits/fixtures/sources/leaderboard/openclaw-infra and rerun ignored audit snapshots",
    transcript: "audits/leaderboard/openclaw-extract.txt",
};

fn repo_path(path: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(path)
}

fn run_extract(case: &AuditSnapshotCase) -> Vec<u8> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_legitimacy"));
    command.current_dir(env!("CARGO_MANIFEST_DIR"));
    command.args(["extract", case.source, "--synthetic"]);
    if case.allow_partial {
        command.arg("--allow-partial");
    }

    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{} extract failed: {}",
        case.name,
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

fn assert_fixture_present(case: &AuditSnapshotCase) {
    let source = repo_path(case.source);
    assert!(
        source.exists(),
        "{} leaderboard snapshot fixture missing at {}; {}",
        case.name,
        source.display(),
        case.remediation
    );
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

fn run_snapshot_case(case: &AuditSnapshotCase) {
    assert_fixture_present(case);

    let expected = fs::read(repo_path(case.transcript)).unwrap();
    let actual = run_extract(case);
    assert_eq!(
        actual,
        expected,
        "{} leaderboard transcript drifted: {}",
        case.name,
        mismatch_context(&expected, &actual)
    );
}

// Per-case `#[test]` functions let cargo's per-binary thread pool run the five
// fixture extractions in parallel. Each case spawns its own `legitimacy extract`
// subprocess; fixtures are independent and the audit-output assertion is
// per-case, so parallel execution preserves correctness.

#[test]
#[ignore = "slow leaderboard snapshot; cargo test --test audit_snapshot -- --ignored to run"]
fn leaderboard_extract_transcript_matches_autogen_snapshot() {
    run_snapshot_case(&AUTOGEN_CASE);
}

#[test]
#[ignore = "slow leaderboard snapshot; cargo test --test audit_snapshot -- --ignored to run"]
fn leaderboard_extract_transcript_matches_codex_snapshot() {
    run_snapshot_case(&CODEX_CASE);
}

#[test]
#[ignore = "slow leaderboard snapshot; cargo test --test audit_snapshot -- --ignored to run"]
fn leaderboard_extract_transcript_matches_claude_agent_sdk_snapshot() {
    run_snapshot_case(&CLAUDE_AGENT_SDK_CASE);
}

#[test]
#[ignore = "slow leaderboard snapshot; cargo test --test audit_snapshot -- --ignored to run"]
fn leaderboard_extract_transcript_matches_crewai_snapshot() {
    run_snapshot_case(&CREWAI_CASE);
}

#[test]
#[ignore = "slow leaderboard snapshot; cargo test --test audit_snapshot -- --ignored to run"]
fn leaderboard_extract_transcript_matches_openclaw_snapshot() {
    run_snapshot_case(&OPENCLAW_CASE);
}
