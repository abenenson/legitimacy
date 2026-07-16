#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="${LEGITIMACY_REPRO_OUT_DIR:-$ROOT/target/audit-agent-reproduction}"
BIN="$ROOT/target/release/legitimacy-audit-agent"

mkdir -p "$OUT_DIR"

if [ -n "$(git -C "$ROOT" status -s src/ examples/graphs/ 2>/dev/null)" ]; then
  echo "WARN: dirty tree detected; provenance fields will carry -dirty suffix"
fi

echo "building legitimacy-audit-agent..."
cargo build --release --bin legitimacy-audit-agent --manifest-path "$ROOT/Cargo.toml"

run_lane() {
  local target="$1"
  local source_path="$2"
  local expected_theorem_class="$3"
  local expected_monotonicity_theorem="$4"
  local expected_nodes="$5"
  local expected_edges="$6"
  local expected_gates="$7"
  local expected_graph_hash="$8"
  local out_file="$OUT_DIR/${target}.json"
  local rc=0

  "$BIN" --target "$target" "$ROOT/$source_path" >"$out_file" || rc=$?
  if [[ "$rc" -eq 0 ]]; then
    echo "ERROR: $target was expected to reject but exited 0" >&2
    return 1
  fi

  python3 - "$target" "$out_file" "$expected_theorem_class" \
    "$expected_monotonicity_theorem" "$expected_nodes" "$expected_edges" \
    "$expected_gates" "$expected_graph_hash" <<'PY'
import json
import sys

(
    target,
    out_file,
    expected_theorem_class,
    expected_monotonicity_theorem,
    expected_nodes,
    expected_edges,
    expected_gates,
    expected_graph_hash,
) = sys.argv[1:9]
expected_nodes = int(expected_nodes)
expected_edges = int(expected_edges)
expected_gates = int(expected_gates)

with open(out_file, encoding="utf-8") as handle:
    bundle = json.load(handle)

reason = bundle.get("verdict", {}).get("reason", {})
kind = bundle.get("verdict", {}).get("kind")
diagnostic = reason.get("diagnostic")
code = reason.get("code")
if bundle.get("target") != target or kind != "rejected" or not diagnostic or not code:
    raise SystemExit(f"{target}: expected structured rejection JSON in {out_file}")

lean = bundle.get("lean", {})
if lean.get("theorem_applicability") != "matches_committed_fixture":
    raise SystemExit(f"{target}: theorem_applicability drifted: {lean.get('theorem_applicability')!r}")
if lean.get("theorem_class") != expected_theorem_class:
    raise SystemExit(f"{target}: theorem_class drifted: {lean.get('theorem_class')!r}")
if lean.get("monotonicity_theorem") != expected_monotonicity_theorem:
    raise SystemExit(f"{target}: monotonicity_theorem drifted: {lean.get('monotonicity_theorem')!r}")

provenance = bundle.get("provenance", {})
if provenance.get("extracted_graph_sha256") != expected_graph_hash:
    raise SystemExit(f"{target}: extracted graph hash drifted: {provenance.get('extracted_graph_sha256')!r}")

graph = bundle.get("extracted_governance_graph") or {}
nodes = graph.get("nodes", {})
edges = graph.get("edges", [])
gate_count = 0
for node in nodes.values():
    gate_count += len(node.get("Binary", {}).get("gates", []))
if len(nodes) != expected_nodes or len(edges) != expected_edges or gate_count != expected_gates:
    raise SystemExit(
        f"{target}: graph shape drifted: nodes={len(nodes)} edges={len(edges)} gates={gate_count}"
    )

threshold = bundle.get("capability_threshold", {})
expected_context = (
    f"mode=extract; extracted_node_count={expected_nodes}; "
    f"edges={expected_edges}; gates={expected_gates}"
)
if threshold.get("extracted_graph_context") != expected_context:
    raise SystemExit(
        f"{target}: extracted_graph_context drifted: "
        f"{threshold.get('extracted_graph_context')!r}"
    )

print(f"{target}: rejected {diagnostic} ({code}) -> {out_file}")
PY
}

run_lane \
  "codex-cli" \
  "examples/codex-cli-fixture" \
  "codexCliRejectionAndThresholdFacts" \
  "codexHooksGovernanceAdmissibilityRejectsMonotonicity" \
  16 8 28 \
  "sha256:9ea01868920ec0efeb9a50974202ceb2ca33507aea761068559052902d304c62"

run_lane \
  "claude-agent-sdk" \
  "examples/claude-agent-sdk-fixture" \
  "claudeAgentSdkRejectionAndThresholdFacts" \
  "claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity" \
  22 8 30 \
  "sha256:bcafeb05d5011d7ece593d4524a38c830c93a0d131d0a8f8073cb16958162584"

run_lane \
  "claude-code" \
  "examples/claude-code-fixture" \
  "claudeCodeCliRejectionAndThresholdFacts" \
  "claudeCodeHooksGovernanceAdmissibilityRejectsMonotonicity" \
  31 14 37 \
  "sha256:09daa4687eda7ef4b86b5055cc55f2a8f218a4252ea23732d5645dffd4e08671"
