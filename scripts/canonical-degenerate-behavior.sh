#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
DOC="$ROOT/docs/degenerate-behavior.md"

fail() {
  echo "ERROR: $*" >&2
  exit 1
}

[[ -f "$DOC" ]] || fail "missing docs/degenerate-behavior.md"

grep -F -q "| Check | Empty graph behavior | Cyclic graph behavior |" "$DOC" \
  || fail "degenerate behavior doc missing canonical table header"

for check in \
  "graph consistency" \
  "graph solidarity" \
  "graph monotonicity" \
  "graph strategyproofness" \
  "graph certifiability" \
  "graph observable determinacy" \
  "graph corrigibility" \
  "graph compositional safety" \
  "graph nonvacuity"
do
  grep -F -q "| $check |" "$DOC" \
    || fail "degenerate behavior doc missing '$check'"
done

echo "canonical degenerate behavior: OK"
