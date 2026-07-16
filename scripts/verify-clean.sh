#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_ROOT="$ROOT/lean"
LEAN_BUILD_LIB="$LEAN_ROOT/.lake/build/lib/lean"

echo "verify-clean: deleting first-party Lean oleans" >&2
rm -rf "$LEAN_BUILD_LIB/Legitimacy" "$LEAN_BUILD_LIB"/Legitimacy.*

echo "verify-clean: rebuilding Lean from source" >&2
(
  cd "$LEAN_ROOT"
  lake build
)
