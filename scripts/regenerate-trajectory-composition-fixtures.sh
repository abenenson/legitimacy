#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUTPUT_ROOT="${1:-$ROOT}"

python3 "$ROOT/scripts/generate-trajectory-composition-fixtures.py" \
  --repository-root "$ROOT" \
  --output-root "$OUTPUT_ROOT"

mkdir -p "$OUTPUT_ROOT/fixtures/trajectory-composition-v0/generated"
(
  cd "$ROOT/lean"
  lake exe trajectory_composition_fixture_export
) > "$OUTPUT_ROOT/fixtures/trajectory-composition-v0/generated/expected-results.json"
