#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="$ROOT/audits/observed-runtime"
BIN="$ROOT/target/release/legitimacy"
IMPORT_BIN="$ROOT/target/release/import_codex_observed_runtime"

CODEX_TUI_SOURCE="${CODEX_TUI_SOURCE:?set CODEX_TUI_SOURCE to <codex-rs>/tui/src}"
CODEX_OSS_STORY="${CODEX_OSS_STORY:?set CODEX_OSS_STORY to <codex-rs>/tui/tests/fixtures/oss-story.jsonl}"

require_path() {
  local path="$1"
  if [[ ! -e "$path" ]]; then
    echo "missing required observed-runtime input: $path" >&2
    exit 1
  fi
}

stage_runtime_slice() {
  local source="$1"
  local destination="$2"
  mkdir -p "$destination"
  cp -R "$source"/. "$destination"
  while IFS= read -r tests_dir; do
    rm -rf "$tests_dir"
  done < <(find "$destination" -type d -name tests | sort)
}

require_path "$CODEX_TUI_SOURCE"
require_path "$CODEX_OSS_STORY"

mkdir -p "$OUT_DIR"

cargo build --release --manifest-path "$ROOT/Cargo.toml" --bin legitimacy --bin import_codex_observed_runtime

workdir="$(mktemp -d)"
trap 'rm -rf "$workdir"' EXIT

runtime_slice="$workdir/codex-tui-runtime-slice"
stage_runtime_slice "$CODEX_TUI_SOURCE" "$runtime_slice"

pack_dir="$OUT_DIR/codex-oss-story-pack"
graph_path="$OUT_DIR/codex-tui-runtime-slice-graph.json"
audit_path="$OUT_DIR/codex-tui-runtime-slice-audit.txt"
raw_audit_path="$workdir/codex-tui-runtime-slice-audit.raw.txt"

rm -rf "$pack_dir"
"$IMPORT_BIN" --input "$CODEX_OSS_STORY" --output "$pack_dir" >/dev/null
"$BIN" extract "$runtime_slice" \
  --emit-graph "$graph_path" \
  --claims "$pack_dir" \
  --claims-provenance observed-runtime \
  >"$raw_audit_path"

sed \
  's#^source: .*#source: filtered codex-rs/tui/src runtime slice (in-tree tests removed)#' \
  "$raw_audit_path" >"$audit_path"
