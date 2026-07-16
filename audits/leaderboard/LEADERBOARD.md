# Governance Admissibility Leaderboard

**Date**: 2026-05-04
**Extractor version**: legitimacy 0.1.0 heuristic corpus lane
**Corpus**: [`audits/corpus/manifest.toml`](../corpus/manifest.toml)

This file separates benchmark evidence by tier. The old frozen leaderboard
fixtures remain in `audits/fixtures/sources/leaderboard/` for regression tests,
but new governance-corpus work is tracked under `audits/corpus/` with pinned
source commits, license records, extractor reports, and placeholders for
reviewed ground truth and observed-runtime claims.

The audit-agent public surface is a separate theorem-backed fixture generation
from the legacy heuristic corpus rows below. For Codex and the Claude Agent SDK,
the Lean witness theorems cited in this file quantify over the committed
`examples/graphs/*.json` audit-agent fixtures, not over the older
`audits/leaderboard/*-graph.json` heuristic extracts.

## Evidence Tiers

- **Theorem-backed modeled (`theorem-backed-modeled`)**: a checked Lean theorem or witness artifact
  ties the modeled source core to the extracted graph semantics. Source
  faithfulness to a pinned upstream harness requires a separate reviewed label
  set or byte/source bridge unless the row explicitly records one.
- **Theorem-backed source-walk (`theorem-backed-source-walk`)**: a checked
  theorem or witness artifact covers the same graph artifact produced by the
  source-walk extraction row, including the same source-relative node set.
- **Theorem-backed (`theorem-backed`)**: deprecated manifest alias; new corpus
  rows must use the modeled or source-walk-specific tier name.
- **Reviewed-ground-truth (`reviewed`)**: a human-reviewed graph label set exists for the
  harness. Reviewer-grade labeling populates this lane.
- **Heuristic (`heuristic`)**: automatic extractor output or pointer-pinned corpus metadata.
  These rows are admissible benchmark inputs but exploratory evidence only.

## Theorem-Backed Modeled Corpus Rows

Five v1 governance-corpus rows carry PythonHookCore theorem-witness artifacts
generated from small Lean-compatible program models. These files are part of the
Lake default build through the corpus theorem witness target.

| System | Corpus id | Witness | Checked Lean artifact |
|--------|-----------|---------|-----------------------|
| AutoGen | `autogen` | `theorem/theorem_witness.json` | `theorem/PythonHookCoreProgram.lean` |
| Claude Agent SDK Python | `claude-agent-sdk-python` | `theorem/theorem_witness.json` | `theorem/PythonHookCoreProgram.lean` |
| CrewAI | `crewai` | `theorem/theorem_witness.json` | `theorem/PythonHookCoreProgram.lean` |
| LangGraph | `langgraph` | `theorem/theorem_witness.json` | `theorem/PythonHookCoreProgram.lean` |
| NeMo Guardrails | `nemo-guardrails` | `theorem/theorem_witness.json` | `theorem/PythonHookCoreProgram.lean` |

## Curated Answer-Key Corpus Rows

Five v1 rows have curated answer-key labels, consensus graphs, and
precision/recall checks against the extractor graph. The current reviewer_a and
reviewer_b files are byte-identical apart from `reviewer_id`; the reported
kappa values therefore validate schema agreement on one curated answer key, not
independent inter-rater agreement.

| System | Corpus id | Node P/R | Edge P/R | Agreement |
|--------|-----------|----------|----------|----------------|
| AutoGen | `autogen` | `1.0 / 1.0` | `1.0 / 1.0` | curated answer key, no independent-review claim |
| Claude Agent SDK Python | `claude-agent-sdk-python` | `1.0 / 1.0` | `1.0 / 1.0` | curated answer key, no independent-review claim |
| CrewAI | `crewai` | `1.0 / 1.0` | `1.0 / 1.0` | curated answer key, no independent-review claim |
| LangGraph | `langgraph` | `1.0 / 1.0` | `1.0 / 1.0` | curated answer key, no independent-review claim |
| NeMo Guardrails | `nemo-guardrails` | `1.0 / 1.0` | `1.0 / 1.0` | curated answer key, no independent-review claim |

## Audit-Agent Public Surface Rows

These rows are the release-front-door audit-agent fixtures. They are distinct
from the legacy heuristic corpus table below and are the graph artifacts cited
by the current Lean theorem fields in audit-agent JSON bundles.

| System | Graph artifact | Nodes | Edges | Gates | Lean rejection witness |
|--------|----------------|------:|------:|------:|------------------------|
| **Codex CLI** | `examples/graphs/codex-graph.json` | 16 | 8 | 28 | `codexHooksGovernanceAdmissibilityRejectsMonotonicity` |
| **Claude Agent SDK** | `examples/graphs/claude-agent-sdk-graph.json` | 22 | 8 | 30 | `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity` |
| **Claude Code public surface** | `examples/graphs/claude-code-graph.json` | 31 | 14 | 37 | `claudeCodeHooksGovernanceAdmissibilityRejectsMonotonicity` |

Claude Code is absent from the heuristic corpus table because this repository
does not redistribute proprietary Claude Code handler implementation. Its public
hook/settings/command metadata fixture is covered through the audit-agent lane
and documented under `docs/audit-bundle-schema.md`.

No leaderboard `C` cell is generated from bounded consistency mode. Public consistency rows use the canonical full graph-diagnostic / Young-consistency surface; bounded consistency is an opt-in approximation and must be labeled as such if used in an auxiliary run.

## Current Results

The table below is the v1 heuristic corpus lane. Rows marked `pointer-pinned`
have pinned commits and license pointers, but no local redistributable source
slice in this corpus revision. Rows marked `observed-runtime extracted` are filled
from their claim-pack traces only; source-tree extraction remains skipped until
a local extraction input is available. Rows marked `extracted` use the existing
frozen source slices and have generated extractor reports.

Provenance disclosure: the frozen CrewAI and AutoGen extracted graph rows are
test-source regression fixtures. CrewAI is extracted from
`lib/crewai/tests/hooks/test_tool_hooks.py`; AutoGen is extracted from
`python/packages/autogen-agentchat/tests/test_code_executor_agent.py`. They are
not production-source coverage of `lib/crewai/src/crewai` or
`python/packages/autogen-agentchat/src/autogen_agentchat`.

Minimal-shape disclosure: Aider, AutoGen, Continue.dev, and LiteLLM proxy policy
are 1-node / 0-edge rows in this table. They are retained as minimal extractor
or observed-runtime smoke rows, not as evidence of multi-node governance-surface
coverage. Panel-size claims should count them separately from connected or
multi-node extracted graphs.

| System | Mode | Nodes | Edges | Connected | λ₂ | C | S | M | SP | Cert | Obs | Corr | Comp | NV | Paradoxes | LFE |
|--------|------|------:|------:|-----------|----|---|---|---|----|------|-----|------|------|----|-----------|-----|
| **Aider** | heuristic corpus; observed-runtime extracted | 1 | 0 | single node | N/A | ok | ok | ok | ok | ok | ok | ok | ok | ok | none | `[0, 0, 0, 0, 0]` |
| **AutoGen** | heuristic corpus; extracted | 1 | 0 | single node | N/A | ok | ok | ok | ok | ok | ok | ok | ok | ok | none | `[0, 0, 0, 0, 0]` |
| **Claude Agent SDK Python** | heuristic corpus; extracted | 15 | 0 | NO | N/A | ok | ok | **FAIL** | ok | ok | ok | ok | ok | ok | none | `[0, 0, 1, 0, 0]` |
| **Cline** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |
| **Codex** | heuristic corpus; extracted | 10 | 5 | NO (5 components) | 0.000 | ok | ok | **FAIL** | ok | ok | ok | ok | ok | **FAIL** | Alabama | `[0, 0, 1, 0, 1]` |
| **Continue.dev** | heuristic corpus; observed-runtime extracted | 1 | 0 | single node | N/A | ok | ok | ok | ok | ok | ok | ok | ok | ok | none | `[0, 0, 0, 0, 0]` |
| **CrewAI** | heuristic corpus; extracted (`--allow-partial`) | 5 | 1 | NO (4 components) | 0.000 | ok | ok | **FAIL** | ok | ok | ok | ok | ok | **FAIL** | Alabama | `[0, 0, 1, 0, 1]` |
| **DSPy agents** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |
| **Guardrails AI** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |
| **LangChain** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |
| **LangGraph** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |
| **Letta** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |
| **LiteLLM proxy policy** | heuristic corpus; observed-runtime extracted | 1 | 0 | single node | N/A | ok | ok | ok | ok | ok | ok | ok | ok | ok | none | `[0, 0, 0, 0, 0]` |
| **LlamaIndex agents** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |
| **NeMo Guardrails** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |
| **OpenHands** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |
| **Qwen-Agent** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |
| **Roo Code** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |
| **Semantic Kernel** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |
| **SWE-agent** | heuristic corpus; pointer-pinned | N/A | N/A | N/A | N/A | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending | pending |

`C,S,M` are the graph-diagnostic primitives: consistency, solidarity, and
monotonicity. `SP` is the derived strategyproofness monitor. `Cert,Obs,Corr,Comp,NV`
are the graph-side kernel projections: certifiability, observable determinacy,
corrigibility, compositional safety, and nonvacuity.

## Observed-Runtime Example

Observed-runtime trace packs are normalized into
`observed_runtime_claims.jsonl` and indexed in
`audits/corpus/observed_runtime_trace_packs.toml`.

| Corpus id | Trace pack | Claims | Heuristic verdict |
|-----------|------------|-------:|-------------------|
| `autogen` | AutoGen code-executor approval multi-claim runtime trace | 4 | passed over 1 nodes and 0 edges |
| `codex` | codex-rs tui oss-story fixture | 9 | failed graph monotonicity and nonvacuity over 10 nodes and 5 edges |
| `crewai` | CrewAI before/after-tool hook multi-claim runtime trace | 4 | failed graph monotonicity and nonvacuity over 5 nodes and 1 edge |
| `langgraph` | LangGraph interrupt/checkpoint representative trace | 1 | skipped: pointer-pinned source has no extraction input |
| `openhands` | OpenHands tool-execution representative trace | 1 | skipped: pointer-pinned source has no extraction input |
| `swe-agent` | SWE-agent patch/test representative trace | 1 | skipped: pointer-pinned source has no extraction input |
| `aider` | Aider file-edit approval representative trace | 1 | observed-runtime claim-pack extraction passed; source extraction still skipped |
| `continue-dev` | Continue.dev tool-call approval representative trace | 1 | observed-runtime claim-pack extraction passed; source extraction still skipped |
| `litellm` | LiteLLM routing/fallback representative trace | 1 | observed-runtime claim-pack extraction passed; source extraction still skipped |
| `nemo-guardrails` | NeMo Guardrails dialogue-policy multi-claim runtime trace | 4 | skipped: pointer-pinned source has no extraction input |

## Legacy Frozen Fixture Regression Rows

The frozen fixture rows below are retained for continuity with the pre-corpus
leaderboard. They remain byte-stable regression targets for
`scripts/refresh-fixtures.sh` and `scripts/verify.sh`.

| System | Mode | Nodes | Edges | Connected | λ₂ | C | S | M | SP | Cert | Obs | Corr | Comp | NV | Paradoxes | LFE |
|--------|------|------:|------:|-----------|----|---|---|---|----|------|-----|------|------|----|-----------|-----|
| **OpenClaw** | legacy frozen fixture; automatic synthetic probe | 53 | 16 | YES | 3.000 | ok | ok | ok | ok | ok | ok | ok | ok | **FAIL** | none | `[0, 0, 0, 0, 1]` |
| **Codex TUI runtime slice** | legacy observed runtime (`oss-story`) | 9 | 7 | YES | 6.051 | ok | ok | **FAIL** | ok | ok | ok | ok | ok | ok | none | `[0, 0, 1, 0, 0]` |
| **Sleeper Agents** | legacy manual paper-graph synthetic probe | 3 | 1 | NO (2 components) | 0.000 | ok | ok | **FAIL** | ok | ok | ok | ok | ok | ok | none | `[0, 0, 1, 0, 0]` |

## Protocol / Boundary Surface

| System | Coverage | Resolution issues | Boundary-relative compositional safety | Live findings |
|--------|----------|------------------:|----------------------------------------|---------------|
| **Codex** | `7 / 7 parsed` | 211 | `10 governance nodes / 202 external deps` | heuristic monotonicity + nonvacuity flags; porous causal boundary; no monitoring |
| **Claude Agent SDK Python** | `3 / 3 parsed` | 5 | `3 governance nodes / 4 external deps` | heuristic monotonicity flag; disconnected MIT SDK schema/callback surface; no monitoring |
| **CrewAI** | `1078 / 1083 parsed` (`5 skipped`) | 20 | `4 governance nodes / 186 external deps` | heuristic monotonicity + nonvacuity flags; porous causal boundary; no monitoring |
| **AutoGen** | `670 / 670 parsed` | 1 | `1 governance nodes / 1 external deps` | heuristic single-node pass; spectral analysis unavailable |




## Per-Harness Lean Theorem Citations

The theorem rows below name the graph artifact each theorem is scoped to. For
Codex and Claude Agent SDK, the current theorem-backed artifact is the
audit-agent `examples/graphs` fixture, not the older heuristic corpus row in
the Current Results table.
Production-ranking rows use `decisionRank deny=0, escalate=1, permit=2`.
The review-required variant treats terminal `.escalate` as equivalent to `permit`
for monotonicity purposes (see §6.7.5 of the companion paper).
Each theorem is `native_decide`-verified against the committed extracted
hook-protocol graph for the corresponding harness.

| System | Graph artifact | Theorem | Module | Verdict |
|--------|----------------|---------|--------|---------|
| Codex | `examples/graphs/codex-graph.json` (16 nodes / 8 edges) | `codexHooksGovernanceAdmissibilityRejectsMonotonicity` | `Legitimacy.Results.CodexAdmissibilityAudit` | Rejects: monotonicity (production ranking) |
| Codex | `examples/graphs/codex-graph.json` (16 nodes / 8 edges) | `codexHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired` | same | Rejects: monotonicity (review-required lattice) |
| Claude Agent SDK | `examples/graphs/claude-agent-sdk-graph.json` (22 nodes / 8 edges) | `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity` | `Legitimacy.Results.ClaudeAgentSDKAdmissibilityAudit` | Rejects: monotonicity (production ranking) |
| Claude Agent SDK | `examples/graphs/claude-agent-sdk-graph.json` (22 nodes / 8 edges) | `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired` | same | Rejects: monotonicity (review-required lattice) |
| Claude Code public surface | `examples/graphs/claude-code-graph.json` (31 nodes / 14 edges) | `claudeCodeHooksGovernanceAdmissibilityRejectsMonotonicity` | `Legitimacy.Results.ClaudeCodeAdmissibilityAudit` | Rejects: monotonicity (production ranking) |
| CrewAI | `audits/leaderboard/crewai-graph.json` (5 nodes / 1 edge) | `crewAIHooksGovernanceAdmissibilityRejectsMonotonicity` | `Legitimacy.Results.CrewAIAdmissibilityAudit` | Rejects: monotonicity (production ranking) |
| CrewAI | `audits/leaderboard/crewai-graph.json` (5 nodes / 1 edge) | `crewAIHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired` | same | Rejects: monotonicity (review-required lattice) |
| OpenClaw | `audits/leaderboard/openclaw-graph.json` (53 nodes / 16 edges) | `openClawInfraNonvacuityCheckFails` | `Legitimacy.Results.OpenClawAdmissibilityAudit` | Rejects: nonvacuity |
| Cross-vendor | Codex + Claude Agent SDK audit-agent fixtures | `codex_claude_sdk_review_required_joint_rejection` | `Legitimacy.Results.ClaudeAgentSDKAdmissibilityAudit` | Joint rejection: both Codex and Claude Agent SDK reject monotonicity under the review-required lattice; per-harness witnesses `codexHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`, `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired` |


## Interpretation

The v1 corpus is deliberately conservative. This release establishes a schema,
twenty license-compatible pinned harness records, generated reports for the
local frozen-source rows, observed-runtime claim-pack fills for three
pointer-pinned rows, and source-extraction placeholders for the remaining
priority harnesses. The table should be read as a benchmark inventory and
exploratory extractor report, not as a theorem-backed claim about upstream
systems.

Broad empirical claims require promotion into the theorem-backed modeled-witness
or reviewed-ground-truth lanes. Until then, heuristic rows are useful for
extractor development, adversarial testing, and prioritizing review, but they
are not a substitute for source-faithfulness proofs or reviewer labels.
