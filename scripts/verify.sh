#!/usr/bin/env bash
set -euo pipefail

RUN_RELEASE_GATE=0
if [[ "${1:-}" == "--release-gate" ]]; then
  RUN_RELEASE_GATE=1
  shift
fi

# Per-step timing helper. Outputs [step Ns] step-name so a developer running
# verify.sh sees which gate is slow without grepping verbose logs. Set
# VERIFY_QUIET=1 to suppress.
__verify_step_start=$(date +%s)
__verify_step_name=setup
verify_step_begin() {
  local now=$(date +%s)
  local elapsed=$(( now - __verify_step_start ))
  if [[ "${VERIFY_QUIET:-0}" != "1" ]]; then
    printf "[step %3ds] %s\n" "$elapsed" "$__verify_step_name" >&2
  fi
  __verify_step_start=$now
  __verify_step_name="$1"
}
verify_step_done() {
  verify_step_begin "(end)"
}
trap verify_step_done EXIT

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mapfile -t CORPUS_THEOREM_FILES < <(
  find "$ROOT/audits/corpus" -path '*/theorem/*.lean' -type f | sort
)
source "$ROOT/scripts/canonical-axiom-inventory.sh"
verify_step_begin canonical-axiom-inventory
assert_canonical_axiom_inventory "$ROOT"
verify_step_begin canonical-info-architecture
bash "$ROOT/scripts/canonical-info-architecture.sh" "$ROOT"
verify_step_begin canonical-leaderboard-doc-sync
bash "$ROOT/scripts/canonical-leaderboard-doc-sync.sh" "$ROOT"
verify_step_begin check-fixture-provenance
bash "$ROOT/scripts/check-fixture-provenance.sh" "$ROOT"
verify_step_begin canonical-sacrifice-graph-surface
bash "$ROOT/scripts/canonical-sacrifice-graph-surface.sh" "$ROOT"
verify_step_begin canonical-degenerate-behavior
bash "$ROOT/scripts/canonical-degenerate-behavior.sh" "$ROOT"
verify_step_begin canonical-joint-witness-coverage
bash "$ROOT/scripts/canonical-joint-witness-coverage.sh" "$ROOT"
verify_step_begin asi-parity-manifest
bash "$ROOT/scripts/check-asi-parity-manifest.sh" "$ROOT"
verify_step_begin check-spine-rooted
bash "$ROOT/scripts/check-spine-rooted.sh" "$ROOT"
# Fixture exporters need Mathlib before the full library build.
verify_step_begin lean-dependency-cache
(
  cd "$ROOT/lean"
  lake exe cache get >/dev/null 2>&1 || true
)

verify_step_begin check-trajectory-composition-fixtures
bash "$ROOT/scripts/check-trajectory-composition-fixtures.sh"

verify_step_begin check-executed-composition
bash "$ROOT/scripts/check-executed-composition.sh"

verify_step_begin lean-build-and-violations-scan
(
  cd lean
  lake build
  lean_violations="$(
    {
      rg -n "^[[:space:]]*(sorry|admit)\\b|^[[:space:]]*axiom[[:space:]]+[A-Za-z_][A-Za-z0-9_']*([[:space:]]*(:|\\(|\\{|\\[)|\$)" \
        --glob '*.lean' --glob '!.lake/**' Legitimacy.lean Legitimacy/ || true
      rg -n ":=[[:space:]]*(by[[:space:]]+)?(sorry|admit)\\b" \
        --glob '*.lean' --glob '!.lake/**' Legitimacy.lean Legitimacy/ || true
    } | awk '!seen[$0]++'
  )"
  if [[ -n "$lean_violations" ]]; then
    printf '%s\n' "$lean_violations"
    echo "ERROR: sorry/admit/axiom found in Lean proofs"
    exit 1
  fi
)

verify_step_begin check-audit-graph-parity
python3 "$ROOT/scripts/check-audit-graph-parity.py"

verify_step_begin check-axiom-footprint
bash "$ROOT/scripts/check-axiom-footprint.sh"

verify_step_begin cargo-fmt
cargo fmt --check
verify_step_begin cargo-clippy
cargo clippy -- -D warnings
verify_step_begin cargo-test
cargo test

# Run the fixture-mutation probe alone: it restores checked-in bytes before exit.
verify_step_begin audit-agent-runtime-fixture-binding
cargo test --test audit_agent_cli runtime_fixture_substitution_cannot_rebind_lean_theorems -- --ignored --exact --test-threads=1

verify_step_begin corpus-theorem-witness-cleanliness
if [[ "${#CORPUS_THEOREM_FILES[@]}" -gt 0 ]]; then
  corpus_lean_violations="$(
    {
      rg -n "^[[:space:]]*(sorry|admit)\\b|^[[:space:]]*axiom[[:space:]]+[A-Za-z_][A-Za-z0-9_']*([[:space:]]*(:|\\(|\\{|\\[)|\$)" \
        "${CORPUS_THEOREM_FILES[@]}" || true
      rg -n ":=[[:space:]]*(by[[:space:]]+)?(sorry|admit)\\b" \
        "${CORPUS_THEOREM_FILES[@]}" || true
    } | awk '!seen[$0]++'
  )"
  if [[ -n "$corpus_lean_violations" ]]; then
    printf '%s\n' "$corpus_lean_violations"
    echo "ERROR: sorry/admit/axiom found in corpus theorem witnesses"
    exit 1
  fi
fi

verify_step_begin check-spectral-fixtures
bash scripts/check-spectral-fixtures.sh
verify_step_begin check-public-surface
bash scripts/check-public-surface.sh
verify_step_begin check-cited-theorem-identifiers
bash scripts/check-cited-theorem-identifiers.sh
verify_step_begin check-doc-rejection-theorem-claims
bash scripts/check-doc-rejection-theorem-claims.sh "$ROOT"
verify_step_begin check-stale-cardinality-literals
bash scripts/check-stale-cardinality-literals.sh "$ROOT"
verify_step_begin check-doc-alignment
bash scripts/check-doc-alignment.sh
verify_step_begin check-legacy-branding
bash scripts/check-legacy-branding.sh
verify_step_begin check-paper-line-citations
bash scripts/check-paper-line-citations.sh
verify_step_begin check-doc-line-citations
bash scripts/check-doc-line-citations.sh "$ROOT"
verify_step_begin check-readme-theorem-spine-citations
bash scripts/check-readme-theorem-spine-citations.sh "$ROOT"
verify_step_begin check-claim-ledger-anchors
bash scripts/check-claim-ledger-anchors.sh
verify_step_begin check-publication-polish
bash scripts/check-publication-polish.sh
verify_step_begin check-cross-branch-merge
bash scripts/check-cross-branch-merge.sh "$ROOT"

if [[ "$RUN_RELEASE_GATE" == "1" ]]; then
  bash scripts/release-gate.sh
fi
