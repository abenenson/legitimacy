#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_ROOT="$(mktemp -d)"
trap 'rm -rf "$TMP_ROOT"' EXIT
available_kib="$(df -Pk "$ROOT" | awk 'NR==2 {print $4}')"
if (( available_kib < 12 * 1024 * 1024 )); then
  echo 'ERROR: less than 12 GiB free; refusing Lean artifact build' >&2
  exit 1
fi
(cd "$ROOT/lean" && LEAN_NUM_THREADS=2 lake exe executed_composition_export) > "$TMP_ROOT/table.json"
cmp "$ROOT/fixtures/executed-composition-v1/generated/table.json" "$TMP_ROOT/table.json"
# A byte mutation must fail the same parity gate.
printf ' ' >> "$TMP_ROOT/table.json"
if cmp -s "$ROOT/fixtures/executed-composition-v1/generated/table.json" "$TMP_ROOT/table.json"; then
  echo 'ERROR: generated policy mutation escaped parity gate' >&2; exit 1
fi
# Discover proof roots from Lean module ownership, not a hand-maintained list.
(cd "$ROOT/lean" && LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
  scripts/CheckExecutedAxioms.lean)
python3 "$ROOT/scripts/check-executed-axiom-gate.py"
python3 "$ROOT/scripts/build-executed-composition-reader.py" --output "$TMP_ROOT/reader.html"
cmp "$ROOT/docs/executed-composition-reader.html" "$TMP_ROOT/reader.html"
node "$ROOT/scripts/check-executed-composition-reader.cjs"
echo 'executed composition: generated-table parity, mutation, proof footprints and reader OK'
