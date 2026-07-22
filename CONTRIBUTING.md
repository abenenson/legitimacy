# Contributing

Contributions are welcome. This document covers how to build, test, and propose changes.

## Build

```bash
cargo build --release
cd lean && lake exe cache get && lake build && cd ..
```

Lean build uses Mathlib via Lake; the first build pulls Mathlib and caches it under `lean/.lake/`.

## Test

```bash
bash scripts/verify.sh
```

`scripts/verify.sh` is the routine fast gate. It runs formatting, `cargo clippy
-- -D warnings`, `cargo test` (with the slow leaderboard snapshots ignored),
the Lean build, the zero-`sorry` / `admit` / `axiom` Lean
scan, and the repo-discipline scripts below. It must pass before opening a PR.

Run `bash scripts/release-gate.sh` (or `bash scripts/verify.sh --release-gate`)
before tagging a release: that adds the slow leaderboard transcript replay
(`cargo test --test audit_snapshot -- --ignored`), the README Lean-gate status
check, the paper verification anchor, and the stale-packaging check.

## Verification scripts

The verification scripts under `scripts/` split between the routine fast gate,
the release-time slow gate, and narrower repo-discipline checks:

- `verify.sh`: routine fast gate; runs the Rust + Lean verification flow
  excluding the slow leaderboard transcript replay. Pre-PR.
- `release-gate.sh`: release-time slow gate; replays the leaderboard
  transcripts, validates the README Lean-gate status line, the paper verification
  anchor, and rejects stale packaging directories. Pre-tag.
- `refresh-fixtures.sh`: updates the frozen leaderboard / observed-runtime
  fixture slices from env-configured upstream repos, then regenerates the
  committed dogfood artifacts. This is for fixture maintenance, not for gating
  commits.
- `check-spectral-fixtures.sh`: release-gating; regenerates the Lean-exported
  spectral fixtures and fails if the committed fixtures drift.
- `check-public-surface.sh`: repo-discipline; detects unintended changes to the
  Lean public theorem/definition surface.
- `check-doc-alignment.sh`: repo-discipline; verifies the five canonical axioms
  are still named in the docs.
- `check-legacy-branding.sh`: repo-discipline; rejects stale legacy project-name
  references.
- `check-publication-polish.sh`: repo-discipline; rejects draft markers,
  publication placeholder URLs, and stale AGENTS/CONTRIBUTING references that
  would make the repo look publication-incomplete.

## Extractor fidelity

Every commit that touches `src/extract/` or adds extractor-emitting Rust code must preserve byte-identical extractor output against the baseline:

```bash
target/release/legitimacy extract audits/fixtures/sources/leaderboard/codex-hooks --synthetic > current.txt
diff audits/leaderboard/codex-extract.txt current.txt
```

A non-empty diff blocks the PR unless the commit message explicitly declares a baseline regeneration and documents why.

**Maintainer-only.** A normal public clone only needs `scripts/verify.sh` and `scripts/release-gate.sh`; the fixture-refresh tooling below is for maintainers regenerating frozen dogfood fixtures from upstream sources.

If the change intentionally updates the frozen dogfood fixtures or their derived
artifacts, run `scripts/refresh-fixtures.sh` with the upstream env vars set and
include the regenerated fixture/artifact files in the same change. Required env
vars (no defaults; the scripts fail-fast with a helpful message if unset):

- `CODEX_REPO`: path to a `codex-rs` checkout (e.g. `$HOME/codex/codex-rs`)
- `OPENCLAW_REPO`: path to an `openclaw-src` checkout
- `TARGETS_DIR`: directory containing the leaderboard targets (`autogen/`,
  `claude-agent-sdk-python/`, `crewai/`)

The leaderboard-only and observed-runtime-only refresh scripts take more
narrowly scoped env vars (`CODEX_SOURCE`, `CODEX_TUI_SOURCE`,
`OPENCLAW_SOURCE`, `CODEX_OSS_STORY`); see the script source for the exact
upstream paths each one expects.

## Lean discipline

- Zero `sorry`, zero `admit` in any committed file.
- Mathlib-standard copyright header on every `.lean` file (Apache-2.0 license reference; see existing files for format).
- Use `lemma` for reusable intermediate results, `theorem` for headline / named-result declarations.
- Private declarations (file-local helpers) may omit doc comments; public declarations must have `/-- ... -/` doc comments in plain mathematical language.

## Commit hygiene

- Format: `feat|fix|refactor|docs|test(scope): short description`.
- No AI co-author trailers or model attribution in commit messages.
- Linear history; rebase, don't merge.

## Proposing changes

Open a PR with a clear description of what the change does and why. If the change touches Lean theorem statements, include a justification for any weakening. Strengthening a theorem is always welcome; weakening requires discussion.

PRs may iterate in review until they meet the same verification bar as
maintainer changes. The development repository is the canonical integration
tree and public `master` is its curated mirror: after a change is accepted, the
maintainer integrates it there, runs the full gate, and publishes the verified
tree through the guarded sync. The public commit records human contributor
credit. Accordingly, an accepted PR may close against the equivalent guarded
commit rather than through GitHub's merge button.

Final acceptance and release decisions rest with the maintainer.
