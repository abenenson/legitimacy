# Leaderboard Fixture Sources

This directory contains frozen source slices used by leaderboard and
leaderboard-adjacent regression tests.

Canonical synthetic-probe leaderboard fixture roots are listed in
`audits/leaderboard/LEADERBOARD.md`:

- `autogen`
- `claude-agent-sdk-hooks`
- `codex-hooks`
- `crewai`
- `openclaw-infra`

Fixture provenance gate: `scripts/check-fixture-provenance.sh` scans extracted
graph artifacts for `/tests/` source paths. Any test-source provenance must be
listed in `test-source-disclosures.txt` and disclosed in the paper, repository
context, and theorem-facing Lean module before the verification gate accepts it.
The current frozen CrewAI and AutoGen regression rows are disclosed test-source
rows, not production-source coverage of those upstream projects.

The following roots remain in this tree because they exercise the same
extraction/audit machinery but are intentionally out of the canonical
leaderboard table:

- `codex-mechanical`: focused mechanical Codex regression used by
  `tests/codex_mechanical.rs`.
- `openclaw-agents`: OpenClaw agent-policy regression fixtures used by
  `tests/openclaw_governance.rs`.
