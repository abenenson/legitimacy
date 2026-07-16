#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FIXTURES_DIR="$ROOT/audits/fixtures"
LEADERBOARD_FIXTURES_DIR="$FIXTURES_DIR/sources/leaderboard"
OBSERVED_RUNTIME_FIXTURES_DIR="$FIXTURES_DIR/sources/observed-runtime"
CORPORA_DIR="$FIXTURES_DIR/corpora"
LEADERBOARD_OUT_DIR="$ROOT/audits/leaderboard"
OBSERVED_RUNTIME_OUT_DIR="$ROOT/audits/observed-runtime"
BIN="$ROOT/target/release/legitimacy"
IMPORT_BIN="$ROOT/target/release/import_codex_observed_runtime"

CODEX_REPO="${CODEX_REPO:?set CODEX_REPO to a codex-rs checkout (e.g. \$HOME/codex/codex-rs)}"
OPENCLAW_REPO="${OPENCLAW_REPO:?set OPENCLAW_REPO to an openclaw-src checkout}"
TARGETS_DIR="${TARGETS_DIR:?set TARGETS_DIR to the leaderboard-targets directory containing autogen/, claude-agent-sdk-python/, crewai/}"

AUTOGEN_REPO="${AUTOGEN_REPO:-$TARGETS_DIR/autogen}"
CLAUDE_AGENT_SDK_PYTHON_REPO="${CLAUDE_AGENT_SDK_PYTHON_REPO:-$TARGETS_DIR/claude-agent-sdk-python}"
CREWAI_REPO="${CREWAI_REPO:-$TARGETS_DIR/crewai}"

CODEX_OSS_STORY="${CODEX_OSS_STORY:-$CODEX_REPO/tui/tests/fixtures/oss-story.jsonl}"

require_path() {
  local path="$1"
  if [[ ! -e "$path" ]]; then
    echo "missing required upstream source: $path" >&2
    exit 1
  fi
}

reset_dir() {
  local path="$1"
  rm -rf "$path"
  mkdir -p "$path"
}

copy_curated_files() {
  local source_root="$1"
  local destination_root="$2"
  shift 2

  local relative_path source_path destination_path
  for relative_path in "$@"; do
    source_path="$source_root/$relative_path"
    require_path "$source_path"
  done

  reset_dir "$destination_root"
  for relative_path in "$@"; do
    source_path="$source_root/$relative_path"
    destination_path="$destination_root/$relative_path"
    mkdir -p "$(dirname "$destination_path")"
    cp "$source_path" "$destination_path"
  done
}

refresh_leaderboard_case() {
  local name="$1"
  local fixture_source="$2"
  shift 2

  local transcript="$LEADERBOARD_OUT_DIR/${name}-extract.txt"
  local graph="$LEADERBOARD_OUT_DIR/${name}-graph.json"

  "$BIN" extract "$fixture_source" --synthetic "$@" >"$transcript"
  "$BIN" extract "$fixture_source" --emit-graph "$graph" "$@"
}

refresh_observed_runtime_outputs() {
  local runtime_source="$OBSERVED_RUNTIME_FIXTURES_DIR/codex-tui-runtime-slice"
  local corpus="$CORPORA_DIR/codex-oss-story.jsonl"
  local pack_dir="$OBSERVED_RUNTIME_OUT_DIR/codex-oss-story-pack"
  local graph="$OBSERVED_RUNTIME_OUT_DIR/codex-tui-runtime-slice-graph.json"
  local audit="$OBSERVED_RUNTIME_OUT_DIR/codex-tui-runtime-slice-audit.txt"
  local raw_audit

  raw_audit="$(mktemp)"

  rm -rf "$pack_dir"
  "$IMPORT_BIN" --input "$corpus" --output "$pack_dir" >/dev/null
  "$BIN" extract "$runtime_source" \
    --emit-graph "$graph" \
    --claims "$pack_dir" \
    --claims-provenance observed-runtime \
    >"$raw_audit"

  sed \
    's#^source: .*#source: filtered codex-rs/tui/src runtime slice (in-tree tests removed)#' \
    "$raw_audit" >"$audit"
  rm -f "$raw_audit"
}

mkdir -p "$LEADERBOARD_OUT_DIR" "$OBSERVED_RUNTIME_OUT_DIR" "$CORPORA_DIR"

copy_curated_files \
  "$CODEX_REPO/hooks/src/events" \
  "$LEADERBOARD_FIXTURES_DIR/codex-hooks" \
  common.rs \
  mod.rs \
  post_tool_use.rs \
  pre_tool_use.rs \
  session_start.rs \
  stop.rs \
  user_prompt_submit.rs

copy_curated_files \
  "$CODEX_REPO/core" \
  "$LEADERBOARD_FIXTURES_DIR/codex-mechanical/core" \
  src/config/permissions.rs \
  src/tools/sandboxing.rs

copy_curated_files \
  "$CODEX_REPO/utils/approval-presets" \
  "$LEADERBOARD_FIXTURES_DIR/codex-mechanical/utils/approval-presets" \
  src/lib.rs

copy_curated_files \
  "$AUTOGEN_REPO" \
  "$LEADERBOARD_FIXTURES_DIR/autogen" \
  python/packages/autogen-agentchat/tests/test_code_executor_agent.py

copy_curated_files \
  "$CREWAI_REPO" \
  "$LEADERBOARD_FIXTURES_DIR/crewai" \
  lib/crewai/tests/hooks/test_tool_hooks.py

copy_curated_files \
  "$CLAUDE_AGENT_SDK_PYTHON_REPO" \
  "$LEADERBOARD_FIXTURES_DIR/claude-agent-sdk-hooks/claude-agent-sdk-python" \
  src/claude_agent_sdk/_internal/query.py \
  src/claude_agent_sdk/client.py \
  src/claude_agent_sdk/types.py

cat >"$LEADERBOARD_FIXTURES_DIR/claude-agent-sdk-hooks/LICENSES.md" <<'EOF'
# Claude Agent SDK Hooks Fixture Licenses

This fixture contains a bounded source slice from
`anthropics/claude-agent-sdk-python` at commit
`8348d1f882bc9033aba5d85ac005a2075f812389`.

Upstream repository: https://github.com/anthropics/claude-agent-sdk-python

The upstream repository is licensed under the MIT License. The copied files are:

- `claude-agent-sdk-python/src/claude_agent_sdk/_internal/query.py`
- `claude-agent-sdk-python/src/claude_agent_sdk/client.py`
- `claude-agent-sdk-python/src/claude_agent_sdk/types.py`

MIT notice:

Copyright (c) 2025 Anthropic, PBC

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
EOF

copy_curated_files \
  "$OPENCLAW_REPO/src/infra" \
  "$LEADERBOARD_FIXTURES_DIR/openclaw-infra" \
  approval-errors.ts \
  approval-gateway-resolver.ts \
  approval-handler-bootstrap.ts \
  approval-handler-runtime.ts \
  approval-native-delivery.ts \
  approval-native-route-coordinator.ts \
  approval-native-route-notice.ts \
  approval-native-runtime.ts \
  approval-turn-source.ts \
  approval-view-model.ts \
  channel-approval-auth.ts \
  exec-approval-channel-runtime.ts \
  exec-approval-forwarder.ts \
  exec-approval-reply.ts \
  exec-approval-surface.ts \
  exec-approvals-allowlist.ts \
  exec-approvals-analysis.ts \
  exec-approvals-effective.ts \
  exec-approvals.ts \
  exec-safe-bin-policy-validator.ts \
  net/fetch-guard.ts \
  outbound/outbound-policy.ts \
  path-alias-guards.ts \
  plugin-approvals.ts \
  runtime-guard.ts \
  system-run-approval-binding.ts

copy_curated_files \
  "$OPENCLAW_REPO/src/agents" \
  "$LEADERBOARD_FIXTURES_DIR/openclaw-agents" \
  failover-policy.ts \
  model-fallback.test.ts \
  model-fallback.ts

copy_curated_files \
  "$CODEX_REPO/tui/src" \
  "$OBSERVED_RUNTIME_FIXTURES_DIR/codex-tui-runtime-slice" \
  app.rs \
  bottom_pane/approval_overlay.rs \
  chatwidget.rs \
  history_cell/hook_cell.rs \
  lib.rs \
  status/card.rs

require_path "$CODEX_OSS_STORY"
rg -m 9 '"kind":"codex_event"' "$CODEX_OSS_STORY" >"$CORPORA_DIR/codex-oss-story.jsonl"

cargo build --release --manifest-path "$ROOT/Cargo.toml" --bin legitimacy --bin import_codex_observed_runtime

refresh_leaderboard_case autogen "$LEADERBOARD_FIXTURES_DIR/autogen"
refresh_leaderboard_case codex "$LEADERBOARD_FIXTURES_DIR/codex-hooks"
refresh_leaderboard_case claude-agent-sdk "$LEADERBOARD_FIXTURES_DIR/claude-agent-sdk-hooks"
refresh_leaderboard_case crewai "$LEADERBOARD_FIXTURES_DIR/crewai" --allow-partial
refresh_leaderboard_case openclaw "$LEADERBOARD_FIXTURES_DIR/openclaw-infra"
refresh_observed_runtime_outputs
