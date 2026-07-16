#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT/lean"
lake exe asi_parity_fixture_export \
  > "$ROOT/audits/fixtures/asi-parity/safety-spec-reduction-example-artifact.json"
