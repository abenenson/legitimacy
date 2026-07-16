# Audits

Public audit artifacts: graph fixtures, leaderboard extractions, structural-audit findings, and the public-corpus inventory used by the executable diagnostics.

The Lean substrate at `lean/Legitimacy/` and the Rust extractor at `src/` operate on the artifacts in this tree. Reproducibility is evidence-tiered: source-walked graphs (`leaderboard/`) regenerate from source slices or pinned upstream commits; structural case-study fixtures (`ai-control/`, `sleeper-agents/`, `kernelization/`, etc.) are checked-in JSON whose verdicts the pipeline re-runs end-to-end. Every textual finding is anchored to a structural-probe verdict the pipeline can replay.

## Subdirectories

| Path | Contents |
|---|---|
| `corpus/` | The v1 governance corpus inventory (`GROUND_TRUTH_PROTOCOL.md`, `README.md`), per-system directories (`aider/`, `autogen/`, etc.), and the `adversarial/` corpus of misleading-literal probes used to harden the extractor. |
| `fixtures/` | Source slices (`sources/`), generated graph corpora (`corpora/`), the ASI-parity manifest fixtures, and `LICENSES.md` for redistributed slices. |
| `leaderboard/` | Public extracted-graph fixtures and audit transcripts for the source-walked harnesses (Codex, Claude Agent SDK, CrewAI, AutoGen, OpenClaw). `LEADERBOARD.md` is the index. |
| `observed-runtime/` | Observed-runtime graph fixtures spanning two lanes: a repo-contained Codex TUI runtime slice (extracted source kept under `audits/fixtures/sources/observed-runtime/`) and a metadata-only Claude Code entry where the proprietary source is not redistributed. |
| `ai-control/` | Structural-audit graph fixtures and findings for the AI Control protocol family (trusted-monitoring, trusted-monitoring-defer, trusted-editing). |
| `sleeper-agents/` | Sleeper-agent monotonicity-test graph fixture, audit transcript, and finding. |
| `sleeper-characterization/` | Sleeper-characterization structural finding. |
| `polarity-aware-monotonicity/` | Polarity-aware monotonicity diagnostic finding. |
| `kernelization/` | Constructive-decidable-frontier finding for the kernelization layer. |

## Top-level files

- `parity-manifest.toml` — Lean/Rust parity manifest consumed by `scripts/check-asi-parity-manifest.sh`. Pins each ASI-parity claim to the Lean theorem path and the Rust counterpart.
- `info-architecture-gate.toml` — Information-architecture gate manifest consumed by `scripts/canonical-info-architecture.sh`.

## Reproduction

Routine reproduction is `./scripts/verify.sh` from the repository root. To refresh the leaderboard extractions specifically, see `scripts/refresh-fixtures.sh` (does not run by default in `verify.sh` because it requires upstream source mirrors to be present).
