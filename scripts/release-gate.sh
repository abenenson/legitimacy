#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/scripts/canonical-axiom-inventory.sh"

fail() {
  echo "ERROR: $*" >&2
  exit 1
}

__release_gate_step_start=$(date +%s)
__release_gate_step_name=setup
release_gate_step_begin() {
  local now
  now=$(date +%s)
  local elapsed=$(( now - __release_gate_step_start ))
  printf "[step %3ds] %s\n" "$elapsed" "$__release_gate_step_name" >&2
  __release_gate_step_start=$now
  __release_gate_step_name="$1"
}
release_gate_step_done() {
  release_gate_step_begin "(end)"
}
trap release_gate_step_done EXIT

release_gate_step_begin canonical-axiom-inventory
assert_canonical_axiom_inventory "$ROOT"
release_gate_step_begin canonical-info-architecture
bash "$ROOT/scripts/canonical-info-architecture.sh" "$ROOT"

release_gate_step_begin slow-cargo-fixtures
(
  cd "$ROOT"
  cargo test --test audit_snapshot -- --ignored
  cargo test --test extract -- --ignored
)

release_gate_step_begin readme-lean-gate-status
readme_lean_gate="$(
  sed -nE \
    '/^Current Lean gate: `lake build` completes (cleanly|successfully with [0-9]+ jobs)\./p' \
    "$ROOT/README.md"
)"
[[ -n "$readme_lean_gate" ]] || fail "could not parse Lean gate status from README.md"

release_gate_step_begin lean-clean-build
bash "$ROOT/scripts/verify-clean.sh"

release_gate_step_begin paper-anchor
anchor_name="$(
  sed -nE \
    -e 's/^\*\*(Status during review|Artifact status)\*\*:.*verification code anchor is `([^`]+)`.*/\2/p' \
    -e 's/^> \*\*Artifact, data, and companion papers\.\*\*.*Verification code anchor: `([^`]+)`.*/\1/p' \
    "$ROOT/papers/03-impossibility-theorem.md" \
    | tail -n 1
)"
[[ -n "$anchor_name" ]] || fail "could not parse verification code anchor from paper"

# Reject resolver aliases that name the current checkout rather than a durable
# tag, branch, or SHA. Otherwise a paper anchor of `HEAD` or `@` would pass
# tautologically because both sides resolve to the same current commit.
case "$anchor_name" in
  HEAD|HEAD^*|HEAD~*|@|@{*})
    fail "paper verification code anchor '$anchor_name' is tautological"
    ;;
esac

anchor_commit="$(git -C "$ROOT" rev-parse --verify "${anchor_name}^{commit}")" \
  || fail "paper verification code anchor '$anchor_name' does not resolve to a commit"
head_commit="$(git -C "$ROOT" rev-parse HEAD)"
[[ "$anchor_commit" == "$head_commit" ]] \
  || fail "paper verification code anchor $anchor_commit != HEAD $head_commit"

release_gate_step_begin stale-release-dir-check
for stale_dir in "$ROOT/target/package" "$ROOT/target/tmp-crate"; do
  [[ ! -d "$stale_dir" ]] || fail "stale release packaging directory exists: ${stale_dir#$ROOT/}"
done

release_gate_step_begin selected-authority-release-gate
bash "$ROOT/scripts/selected-authority-release-gate.sh"

echo "release gate: OK"
