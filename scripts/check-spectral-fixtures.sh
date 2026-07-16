#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
EXPECTED="$ROOT/tests/fixtures/spectral_expectations.toml"
TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT

bash "$ROOT/scripts/generate-spectral-fixtures.sh" "$TMP"

if ! cmp -s "$EXPECTED" "$TMP"; then
  echo "ERROR: spectral fixtures drifted from Lean exporter; regenerate $EXPECTED" >&2
  diff -u "$EXPECTED" "$TMP" || true
  exit 1
fi

echo "spectral fixtures: OK"
