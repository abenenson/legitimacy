#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="$ROOT/audits/leaderboard"
BIN="$ROOT/target/release/legitimacy"

CODEX_SOURCE="${CODEX_SOURCE:?set CODEX_SOURCE to <codex-rs>/hooks/src/events}"
CLAUDE_AGENT_SDK_SOURCE="${CLAUDE_AGENT_SDK_SOURCE:-$ROOT/audits/fixtures/sources/leaderboard/claude-agent-sdk-hooks}"
OPENCLAW_SOURCE="${OPENCLAW_SOURCE:?set OPENCLAW_SOURCE to <openclaw-src>/src/infra}"
TARGETS_DIR="${TARGETS_DIR:?set TARGETS_DIR to the leaderboard-targets directory}"

AUTOGEN_SOURCE="${AUTOGEN_SOURCE:-$TARGETS_DIR/autogen}"
CREWAI_SOURCE="${CREWAI_SOURCE:-$TARGETS_DIR/crewai}"
LANGCHAIN_SOURCE="${LANGCHAIN_SOURCE:-$TARGETS_DIR/langchain}"
HAYSTACK_SOURCE="${HAYSTACK_SOURCE:-$TARGETS_DIR/haystack}"
DSPY_SOURCE="${DSPY_SOURCE:-$TARGETS_DIR/dspy}"
METAGPT_SOURCE="${METAGPT_SOURCE:-$TARGETS_DIR/metagpt}"
SEMANTIC_KERNEL_SOURCE="${SEMANTIC_KERNEL_SOURCE:-$TARGETS_DIR/semantic-kernel}"

require_path() {
  local path="$1"
  if [[ ! -e "$path" ]]; then
    echo "missing required audit target: $path" >&2
    exit 1
  fi
}

run_extract() {
  local name="$1"
  local source="$2"
  shift 2

  local transcript="$OUT_DIR/${name}-extract.txt"
  local graph="$OUT_DIR/${name}-graph.json"

  echo "refreshing ${name} from ${source}" >&2
  "$BIN" extract "$source" --synthetic --emit-graph "$graph" "$@" >"$transcript"
}

run_threshold_probe() {
  local name="$1"
  local source="$2"
  shift 2

  local transcript="$OUT_DIR/${name}-extract.txt"

  echo "refreshing ${name} from ${source}" >&2
  if ! "$BIN" extract "$source" --synthetic "$@" >"$transcript" 2>&1; then
    if ! grep -q "no governance-relevant functions were discovered" "$transcript"; then
      echo "unexpected extraction failure for ${name}" >&2
      cat "$transcript" >&2
      exit 1
    fi
  fi
}

mkdir -p "$OUT_DIR"

for path in \
  "$CODEX_SOURCE" \
  "$CLAUDE_AGENT_SDK_SOURCE" \
  "$OPENCLAW_SOURCE" \
  "$AUTOGEN_SOURCE" \
  "$CREWAI_SOURCE" \
  "$LANGCHAIN_SOURCE" \
  "$HAYSTACK_SOURCE" \
  "$DSPY_SOURCE" \
  "$METAGPT_SOURCE" \
  "$SEMANTIC_KERNEL_SOURCE"
do
  require_path "$path"
done

cargo build --release --manifest-path "$ROOT/Cargo.toml"

run_extract codex "$CODEX_SOURCE"
run_extract claude-agent-sdk "$CLAUDE_AGENT_SDK_SOURCE"
run_extract openclaw "$OPENCLAW_SOURCE"
run_extract crewai "$CREWAI_SOURCE" --allow-partial
run_extract autogen "$AUTOGEN_SOURCE"

run_threshold_probe langchain "$LANGCHAIN_SOURCE" --allow-partial
run_threshold_probe haystack "$HAYSTACK_SOURCE" --allow-partial
run_threshold_probe dspy "$DSPY_SOURCE" --allow-partial
run_threshold_probe metagpt "$METAGPT_SOURCE" --allow-partial
run_threshold_probe semantic-kernel "$SEMANTIC_KERNEL_SOURCE" --allow-partial
