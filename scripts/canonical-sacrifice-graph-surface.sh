#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
SOURCE="$ROOT/src/sacrifice.rs"
TEST="$ROOT/tests/sacrifice.rs"

fail() {
  echo "ERROR: $*" >&2
  exit 1
}

[[ -f "$SOURCE" ]] || fail "missing src/sacrifice.rs"
[[ -f "$TEST" ]] || fail "missing tests/sacrifice.rs"

for fn in \
  check_graph_consistency \
  check_graph_solidarity \
  check_graph_monotonicity \
  check_graph_certifiability \
  check_graph_observable_determinacy \
  check_graph_corrigibility \
  check_graph_compositional_safety \
  check_graph_nonvacuity \
  check_graph_strategyproofness_verdict
do
  grep -F -q "$fn" "$SOURCE" || fail "graph sacrifice compiler missing $fn"
done

for axiom in \
  "graph consistency" \
  "graph solidarity" \
  "graph monotonicity" \
  "graph certifiability" \
  "graph observable determinacy" \
  "graph corrigibility" \
  "graph compositional safety" \
  "graph nonvacuity"
do
  grep -F -q "$axiom" "$TEST" || fail "graph sacrifice surface test missing '$axiom'"
done

grep -F -q "graph_sacrifice_certificate_carries_canonical_surface" "$TEST" \
  || fail "missing graph sacrifice canonical-surface regression test"

echo "canonical sacrifice graph surface: OK"
