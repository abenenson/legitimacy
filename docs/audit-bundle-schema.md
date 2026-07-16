# Audit Bundle Schema

This page carries the audit-agent JSON shape and lane-specific evidence details
that are too reference-heavy for the root README. Return to the concise entry
point at [README.md](../README.md).

## Reproduce The Audit

```bash
scripts/reproduce-audit.sh
```

The script rebuilds `target/release/legitimacy-audit-agent`, runs all three
source-walked lanes, and writes JSON bundles under
`target/audit-agent-reproduction/`. Rejected verdicts intentionally exit
non-zero when run directly; the reproduction script treats those rejections as
the expected result.

Manual equivalent:

```bash
cargo build --release --bin legitimacy-audit-agent
target/release/legitimacy-audit-agent --target codex-cli examples/codex-cli-fixture || echo "expected rejection exit: $?"
target/release/legitimacy-audit-agent --target claude-agent-sdk examples/claude-agent-sdk-fixture || echo "expected rejection exit: $?"
target/release/legitimacy-audit-agent --target claude-code examples/claude-code-fixture || echo "expected rejection exit: $?"
```

After modifying source or pulling new commits, rebuild with
`cargo build --release --bin legitimacy-audit-agent` before re-running. Or use
`make audit-agent TARGET=codex-cli SRC=examples/codex-cli-fixture`, which
rebuilds for you.

Replay mode is explicit and does not accept a source path:

```bash
target/release/legitimacy-audit-agent --target codex-cli --mode replay-committed || echo "expected rejection exit: $?"
```

In replay mode, `provenance.source_path` is the committed graph fixture path.
Replay bundles emit `provenance.committed_graph_sha256`, which hashes the raw
checked-in graph JSON bytes. Extract bundles emit
`provenance.extracted_graph_sha256`, which hashes the normalized in-memory graph
produced by extraction. `source_pointer.file` points at that graph fixture and
`line_start = line_end = 0` is a documented sentinel, not a source-code span.

## Codex CLI Lane

```bash
target/release/legitimacy-audit-agent --target codex-cli examples/codex-cli-fixture
```

Expected JSON shape:

```json
{
  "target": "codex-cli",
  "verdict": { "kind": "rejected" },
  "provenance": {
    "mode": "extract",
    "source_path": "/abs/path/to/examples/codex-cli-fixture",
    "binary_version": "legitimacy-audit-agent 0.1.0 (<build-sha>)",
    "extracted_graph_sha256": "sha256:9ea01868920ec0efeb9a50974202ceb2ca33507aea761068559052902d304c62"
  },
  "lean": {
    "theorem_class": "codexCliRejectionAndThresholdFacts",
    "file_path": "lean/Legitimacy/CaseStudies/CodexHarness.lean",
    "native_decide_fixture": true,
    "theorem_applicability": "matches_committed_fixture"
  },
  "capability_threshold": {
    "c_star": "1/10",
    "delta": "1/10",
    "c_star_value_proved_on": "codexHarnessDerived_C_star_value on codexHarnessDerivedSpectralGraph: GovGraph ℚ 16 (derived from extracted graph; disconnected, 8 components)",
    "extracted_graph_context": "mode=extract; extracted_node_count=16; edges=8; gates=28",
    "c_star_disclaimer": "the C* carrier graph is derived from the committed extracted graph by symmetrizing the pass-through topology; it is disconnected with 8 components"
  }
}
```

Replay mode emits the same verdict shape with committed-fixture provenance and
uses `replayed_governance_graph` for the top-level graph payload; extract mode
uses `extracted_governance_graph`.

```json
{
  "target": "codex-cli",
  "verdict": { "kind": "rejected" },
  "provenance": {
    "mode": "replay-committed",
    "source_path": "/abs/path/to/examples/graphs/codex-graph.json",
    "binary_version": "legitimacy-audit-agent 0.1.0 (<build-sha>)",
    "committed_graph_sha256": "sha256:7eea523bb24362cbfd8673195e412aea09025509f0f1472ea5dfee94f1d81fb3",
    "committed_graph_path": "examples/graphs/codex-graph.json",
    "committed_graph_commit": "f49fa1b41539f38dcfc6e1031e7293c13489a88a"
  },
  "source_pointer": {
    "file": "examples/graphs/codex-graph.json",
    "line_start": 0,
    "line_end": 0
  }
}
```

Load-bearing theorem names:

- `codexHooksGovernanceAdmissibilityRejectsMonotonicity` in `lean/Legitimacy/Results/CodexAdmissibilityAudit.lean`
- `codexHarnessDerived_C_star_value` in `lean/Legitimacy/CaseStudies/CodexHarness.lean`
- `codexExtractedGraphCardinalityAndCStar` in `lean/Legitimacy/CaseStudies/CodexHarness.lean`
- `codexCliRejectionAndThresholdFacts` in `lean/Legitimacy/CaseStudies/CodexHarness.lean`

## Claude Agent SDK Lane

```bash
target/release/legitimacy-audit-agent --target claude-agent-sdk examples/claude-agent-sdk-fixture
```

Expected JSON shape:

```json
{
  "target": "claude-agent-sdk",
  "verdict": { "kind": "rejected" },
  "provenance": {
    "mode": "extract",
    "source_path": "/abs/path/to/examples/claude-agent-sdk-fixture",
    "binary_version": "legitimacy-audit-agent 0.1.0 (<build-sha>)",
    "extracted_graph_sha256": "sha256:bcafeb05d5011d7ece593d4524a38c830c93a0d131d0a8f8073cb16958162584"
  },
  "lean": {
    "theorem_class": "claudeAgentSdkRejectionAndThresholdFacts",
    "c_star_theorem": "claudeAgentSdkHarnessDerived_C_star_value",
    "file_path": "lean/Legitimacy/CaseStudies/ClaudeAgentSdkHarness.lean",
    "native_decide_fixture": true,
    "theorem_applicability": "matches_committed_fixture"
  },
  "capability_threshold": {
    "c_star": "1/10",
    "delta": "1/10",
    "c_star_value_proved_on": "claudeAgentSdkHarnessDerived_C_star_value on claudeAgentSdkHarnessDerivedSpectralGraph: GovGraph ℚ 22 (derived from extracted graph; disconnected, 8 K₂ pairs + 6 isolated nodes)",
    "extracted_graph_context": "mode=extract; extracted_node_count=22; edges=8; gates=30",
    "c_star_disclaimer": "the C* carrier graph is derived from the committed extracted graph by symmetrizing the pass-through topology; it is disconnected with 8 K₂ components and 6 isolated nodes"
  }
}
```

Load-bearing theorem names:

- `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity`
- `claudeAgentSdkHarnessDerived_C_star_value`
- `claudeAgentSdkExtractedGraphCardinalityAndCStar`
- `claudeAgentSdkRejectionAndThresholdFacts`

The monotonicity theorem and legacy carrier remain in
`lean/Legitimacy/Results/ClaudeAgentSDKAdmissibilityAudit.lean`; the derived C*
and bundle theorems are in `lean/Legitimacy/CaseStudies/ClaudeAgentSdkHarness.lean`.

## Claude Code Public Surface Lane

```bash
target/release/legitimacy-audit-agent --target claude-code examples/claude-code-fixture
```

Expected JSON shape:

```json
{
  "target": "claude-code",
  "verdict": { "kind": "rejected" },
  "provenance": {
    "mode": "extract",
    "source_path": "/abs/path/to/examples/claude-code-fixture",
    "binary_version": "legitimacy-audit-agent 0.1.0 (<build-sha>)",
    "extracted_graph_sha256": "sha256:09daa4687eda7ef4b86b5055cc55f2a8f218a4252ea23732d5645dffd4e08671"
  },
  "lean": {
    "theorem_class": "claudeCodeCliRejectionAndThresholdFacts",
    "c_star_theorem": "claudeCodeHarnessDerived_C_star_value",
    "file_path": "lean/Legitimacy/CaseStudies/ClaudeCodeHarness.lean",
    "native_decide_fixture": true,
    "theorem_applicability": "matches_committed_fixture"
  },
  "capability_threshold": {
    "c_star": "1/10",
    "delta": "1/10",
    "c_star_value_proved_on": "claudeCodeHarnessDerived_C_star_value on claudeCodeHarnessDerivedSpectralGraph: GovGraph ℚ 31 (derived from extracted graph; disconnected, 14 K₂ pairs + 3 isolated nodes)",
    "extracted_graph_context": "mode=extract; extracted_node_count=31; edges=14; gates=37",
    "c_star_disclaimer": "the C* carrier graph is derived from the committed extracted graph by symmetrizing the pass-through topology; it is disconnected with 14 K₂ components and 3 isolated nodes"
  }
}
```

Load-bearing theorem names:

- `claudeCodeHooksGovernanceAdmissibilityRejectsMonotonicity`
- `claudeCodeHarnessDerived_C_star_value`
- `claudeCodeExtractedGraphCardinalityAndCStar`
- `claudeCodeCliRejectionAndThresholdFacts`

The monotonicity theorem and legacy carrier remain in
`lean/Legitimacy/Results/ClaudeCodeAdmissibilityAudit.lean`; the derived C* and
bundle theorems are in `lean/Legitimacy/CaseStudies/ClaudeCodeHarness.lean`.
This lane is a public hook/settings/command-surface fixture. It is not sourced
from Claude Agent SDK code and does not redistribute proprietary Claude Code
handler implementation.

## JSON Schema

- `provenance.mode`: audit mode, either `extract` for source-walked extraction
  or `replay-committed` for checked-in graph replay.
- `provenance.source_path`: canonical source tree path in extract mode, or
  canonical committed graph fixture path in replay mode.
- `provenance.binary_version`: audit-agent package version plus the build git
  SHA, suffixed with `-dirty` when built from uncommitted `src/` changes.
- `provenance.extracted_graph_sha256`: extract-mode SHA-256 over the normalized
  in-memory extracted graph.
- `provenance.committed_graph_sha256`: replay-mode SHA-256 over the raw
  checked-in graph fixture bytes.
- `provenance.committed_graph_path`: replay-mode repository-relative path to
  the committed graph fixture.
- `provenance.committed_graph_commit`: replay-mode last commit touching the
  graph fixture, suffixed with `-dirty` when the fixture has uncommitted edits.
- `lean.native_decide_fixture`: boolean marker that the cited Lean lane uses
  native-decision fixtures for the finite graph facts.
- `capability_threshold.c_star_value_proved_on`: theorem name and spectral
  carrier graph on which the C* value is actually proved.
- `capability_threshold.extracted_graph_context`: extracted-graph mode, node count,
  edge count, and gate count reported alongside the C* value.
- `capability_threshold.c_star_disclaimer`: explicit notice that the C* carrier
  is derived from the committed extracted graph and may be disconnected.

`source_pointer` is the bundle's anchor to the audited source tree:
`source_pointer.file` records where the source-path or replay fixture anchor was
resolved. `verdict.reason.named_feature` is the specific extracted-graph node
that triggered the rejection. These may cite different files when the rejected
node is not at the same handler as the source path resolution.

## Capability Threshold

The Stage 2 C* carrier provenance is graph-derived for all three binary lanes.
`capability_threshold.c_star_value_proved_on` names the Lean theorem and the
spectral carrier graph the theorem actually quantifies over. The Codex lane uses
`codexHarnessDerivedSpectralGraph`, a sixteen-node carrier derived from the
committed extracted graph by symmetrizing the pass-through topology. The SDK and
Claude Code lanes now use the same derived projection pattern on their committed
22-node and 31-node extracted graphs, respectively.
`capability_threshold.extracted_graph_context` records the extracted graph cardinality
and edge/gate facts that the JSON bundle reports beside that C* value. These
derived carriers are disconnected pass-through-pair topologies with isolated
schema nodes where the extracted graph has them.

## Lean Evidence Shape

Each bundle has a `lean` block:

```json
{
  "theorem_class": "claudeCodeCliRejectionAndThresholdFacts",
  "monotonicity_theorem": "claudeCodeHooksGovernanceAdmissibilityRejectsMonotonicity",
  "c_star_theorem": "claudeCodeHarnessDerived_C_star_value",
  "graph_cardinality_with_c_star_carrier_theorem": "claudeCodeExtractedGraphCardinalityAndCStar",
  "module": "Legitimacy.CaseStudies.ClaudeCodeHarness",
  "file_path": "lean/Legitimacy/CaseStudies/ClaudeCodeHarness.lean",
  "native_decide_fixture": true,
  "theorem_applicability": "matches_committed_fixture"
}
```

`graph_cardinality_with_c_star_carrier_theorem` is the scalar bundle theorem in
all three lanes: finite extracted-graph node and edge cardinalities conjoined
with the Stage 2 C* carrier value. In all three lanes that carrier is the
derived projection from the committed extracted graph.

In extract mode, theorem fields are cited only when the normalized extracted
graph hash matches the committed finite fixture for that lane. Divergent
extractions emit `"theorem_applicability": "extracted_diagnostic_only"`,
null theorem fields, and null `capability_threshold.c_star` and
`capability_threshold.delta`. A `lean.divergence` block records the expected and
actual graph hashes and node counts.

`verdict.reason.named_feature` is the canonical lane anchor for reviewer
navigation. It is not a proof that the named node is the unique failing site of
the graph-level monotonicity rejection.
