#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUTPUT="${1:-$ROOT/tests/fixtures/spectral_expectations.toml}"

mkdir -p "$(dirname "$OUTPUT")"
(
  cd "$ROOT/lean"
  lake exe spectral_fixture_export
) > "$OUTPUT"
