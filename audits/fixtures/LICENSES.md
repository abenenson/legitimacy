# Frozen Fixture Attributions

This directory contains frozen source slices and runtime fixtures copied from
permissively licensed upstream projects so the canonical `legitimacy` gate can
run against repo-contained inputs.

## Upstream Sources

- `autogen` — SPDX: MIT
  Source: https://github.com/microsoft/autogen
  Upstream license text: `upstream-licenses/autogen-LICENSE`
  Frozen files under `sources/leaderboard/autogen/`
- `crewai` — SPDX: MIT
  Source: https://github.com/crewAIInc/crewAI
  Upstream license text: `upstream-licenses/crewai-LICENSE`
  Frozen files under `sources/leaderboard/crewai/`
- `codex` — SPDX: Apache-2.0
  Source: https://github.com/openai/codex
  Upstream license text: `upstream-licenses/codex-LICENSE`
  Frozen files under `sources/leaderboard/codex-hooks/`,
  `sources/observed-runtime/codex-tui-runtime-slice/`, and
  `corpora/codex-oss-story.jsonl`
- `openclaw` — SPDX: MIT
  Source: https://github.com/openclaw/openclaw
  Upstream license text: `upstream-licenses/openclaw-LICENSE`
  OpenClaw is Peter Steinberger's public open-source agent runtime and was
  recorded as a widely-used open-source agent runtime. It is one of the
  third-party leaderboard audit targets, alongside Codex, Claude Agent SDK,
  CrewAI, and AutoGen. The governance-surface extraction applies the same
  automated structural probe used for the other entries. The legitimacy audit
  tooling runs on OpenClaw; that is a user-of relationship, not authorship of
  OpenClaw.
  Frozen files under `sources/leaderboard/openclaw-infra/`

Each frozen slice is intentionally limited to the source surface needed to
reproduce the committed extractor and audit artifacts. Local refreshes from the
full upstream trees are handled by `scripts/refresh-fixtures.sh`.

## Lean Build Dependency Provenance

The following public Apache-2.0 repositories are fetched by `lean/lakefile.lean`
at pinned revisions. They are load-bearing build dependencies and are not
vendored in-tree.

- `channel-capacity` — SPDX: Apache-2.0
  Source: https://github.com/abenenson/channel-capacity.git
  Pinned revision: `fdb4d1d18dba3e408fbe1969e09a4da3da2e313e`
  Load-bearing use: `capability_scaling_shared_cliff` and
  `channel_capacity_bounds_C_star`.
- `compact-spectral` — SPDX: Apache-2.0
  Source: https://github.com/abenenson/compact-spectral.git
  Pinned revision: `72cd62dbdd4c397d26fc0c5777d60fea2211e938`
  Load-bearing use: paper 04 compact spectral substrate.
- `godel-loeb` — SPDX: Apache-2.0
  Source: https://github.com/abenenson/godel-loeb
  Pinned revision: `60a7a1098c34dbd0ee0833dde94ef5315f22d472`
  Load-bearing use: paper 03 reflective substrate.


## Fixture Size Exception

The repository's general 1000-LOC-per-file convention does not apply to frozen upstream source slices in `audits/fixtures/sources/`. These files are copied byte-faithful from the upstream codex-tui and related projects so that byte-stable extraction parity tests have a stable input. `audits/fixtures/sources/observed-runtime/codex-tui-runtime-slice/app.rs` (1496 lines) is one such frozen slice and is not subject to the project size convention.


## Observed-runtime Corpus Provenance

`audits/fixtures/corpora/codex-oss-story.jsonl` is generated transcript content from a codex-tui session run against an open-source-licensed test scenario, retained as a frozen runtime fixture. The transcript content is synthetic narrative output produced by the model under the test scenario; no personal data is embedded. The corpus is included so the legitimacy gate can run byte-stable observed-runtime audits against repo-contained inputs.
