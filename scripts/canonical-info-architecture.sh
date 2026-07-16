#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"

fail() {
  echo "ERROR: $*" >&2
  exit 1
}

expected_lean_module_for_path() {
  local file="$1"
  local rel="${file#"$ROOT/lean/"}"
  rel="${rel%.lean}"
  rel="${rel//\//.}"
  printf '%s\n' "$rel"
}

check_lean_module_doc_paths() {
  local failed=0
  while IFS= read -r -d '' file; do
    local expected declared requires_path_heading
    expected="$(expected_lean_module_for_path "$file")"
    declared="$(
      sed -nE "s/^[[:space:]]*# (Legitimacy(\\.[A-Za-z0-9_']+)*).*/\\1/p" "$file" \
        | head -n 1
    )"
    requires_path_heading=0
    if grep -q 'Import-stable umbrella' "$file" \
        || grep -q -E '^[[:space:]]*# .*[Pp]ackage' "$file"; then
      requires_path_heading=1
    fi
    if [[ -z "$declared" ]]; then
      if (( requires_path_heading )); then
        echo "ERROR: ${file#"$ROOT/"} has a paper-style module heading but no '# $expected' path heading" >&2
        failed=1
      fi
      continue
    fi
    if [[ "$declared" != "$expected" ]]; then
      echo "ERROR: ${file#"$ROOT/"} declares '$declared' but path is '$expected'" >&2
      failed=1
    fi
  done < <(find "$ROOT/lean/Legitimacy" -type f -name '*.lean' -print0)
  return "$failed"
}

check_orphan_umbrellas() {
  local failed=0
  while IFS= read -r -d '' file; do
    local base sibling module importers
    base="$(basename "$file" .lean)"
    sibling="$ROOT/lean/Legitimacy/$base"
    [[ -d "$sibling" ]] || continue

    module="Legitimacy.$base"
    importers="$(
      grep -R -l -E "^import[[:space:]]+$module$" "$ROOT/lean" \
        --include='*.lean' --exclude-dir='.lake' 2>/dev/null \
        | grep -F -v "$file" || true
    )"
    if [[ -z "$importers" ]] && ! grep -q 'Import-stable umbrella' "$file"; then
      echo "ERROR: ${file#"$ROOT/"} is an unimported umbrella without an Import-stable umbrella docstring" >&2
      failed=1
    fi
  done < <(find "$ROOT/lean/Legitimacy" -maxdepth 1 -type f -name '*.lean' -print0)
  return "$failed"
}

check_paradox_boundary() {
  grep -F -q 'The paradox suite is Rust-only by design' \
    "$ROOT/docs/repository-context.md" \
    || fail "docs/repository-context.md must document the Rust-only paradox diagnostic boundary"
  grep -F -q 'Paradox detection is a Rust-side production diagnostic' \
    "$ROOT/ARCHITECTURE.md" \
    || fail "ARCHITECTURE.md must document the paradox diagnostic boundary"

  if grep -R -n -E 'AuditCheck\.paradox|GovernanceProperty::Paradox|enum GovernanceProperty.*Paradox' \
      "$ROOT/lean/Legitimacy" "$ROOT/src" --include='*.lean' --include='*.rs' >/dev/null; then
    fail "paradox is documented as Rust-only but appears in the canonical axiom inventory"
  fi
}

check_framework_limits_naming_refresh() {
  local framework="$ROOT/FRAMEWORK-LIMITS.md"
  [[ -f "$framework" ]] || fail "missing FRAMEWORK-LIMITS.md"

  if grep -F -n "ArithmeticRealizationPositiveProbe.lean" "$framework" >/dev/null; then
    grep -F -n "ArithmeticRealizationPositiveProbe.lean" "$framework" >&2 || true
    fail "FRAMEWORK-LIMITS.md cites the pre-rename arithmetic-realization module"
  fi
}

check_leaderboard_fixture_scope() {
  local readme="$ROOT/audits/fixtures/sources/leaderboard/README.md"
  local leaderboard="$ROOT/audits/leaderboard/LEADERBOARD.md"
  local failed=0
  [[ -f "$readme" ]] || fail "missing leaderboard fixture scope README"

  while IFS= read -r -d '' dir; do
    local name
    name="$(basename "$dir")"
    if ! grep -F -q "$name" "$leaderboard" && ! grep -F -q "$name" "$readme"; then
      echo "ERROR: leaderboard fixture '$name' is not in LEADERBOARD.md or the fixture README" >&2
      failed=1
    fi
  done < <(find "$ROOT/audits/fixtures/sources/leaderboard" -mindepth 1 -maxdepth 1 -type d -print0)
  return "$failed"
}

warn_folder_cardinality() {
  # Spectral is intentionally allowed a slightly larger root while its public
  # import surface still spans capacity core, positive-procedure, ASI embedding,
  # RG, Stackelberg, and finite-universality families. A full subcluster move
  # would require downstream import and theorem-spine path churn.
  local spectral_threshold="${INFO_ARCH_SPECTRAL_THRESHOLD:-36}"
  # v1.0.0 ships three Results admissibility audit lanes, so the previous
  # two-lane threshold is arithmetically obsolete.
  local results_threshold="${INFO_ARCH_RESULTS_THRESHOLD:-35}"
  local path threshold count

  for entry in \
    "lean/Legitimacy/Spectral:$spectral_threshold" \
    "lean/Legitimacy/Results:$results_threshold"
  do
    path="${entry%%:*}"
    threshold="${entry##*:}"
    count="$(find "$ROOT/$path" -maxdepth 1 -type f -name '*.lean' | wc -l | tr -d ' ')"
    if (( count > threshold )); then
      echo "WARNING: $path has $count Lean files (threshold $threshold); consider sub-clustering or refreshing the documented cluster map" >&2
    fi
  done
}

check_loc_ratchet() {
  local ceiling="${LOC_CEILING:-1000}"
  local failed=0
  local file count

  # Rust files: src/, cli/, tests/, examples/, benches/ (skip target/, generated)
  while IFS= read -r -d '' file; do
    count="$(wc -l < "$file" | tr -d ' ')"
    if (( count > ceiling )); then
      echo "ERROR: ${file#"$ROOT/"} has $count LOC, exceeding the $ceiling LOC ceiling" >&2
      failed=1
    fi
  done < <(find "$ROOT/src" "$ROOT/cli" "$ROOT/tests" "$ROOT/examples" "$ROOT/benches" -type f -name '*.rs' -not -path '*/target/*' -print0 2>/dev/null)

  # Lean files: lean/Legitimacy/ (skip .lake/)
  while IFS= read -r -d '' file; do
    count="$(wc -l < "$file" | tr -d ' ')"
    if (( count > ceiling )); then
      echo "ERROR: ${file#"$ROOT/"} has $count LOC, exceeding the $ceiling LOC ceiling" >&2
      failed=1
    fi
  done < <(find "$ROOT/lean/Legitimacy" -type f -name '*.lean' -not -path '*/.lake/*' -print0 2>/dev/null)

  if (( failed )); then
    fail "files exceed the $ceiling LOC ceiling - split the offenders into cohesive sub-modules"
  fi
}

check_lean_module_doc_paths
check_orphan_umbrellas
check_paradox_boundary
check_framework_limits_naming_refresh
check_leaderboard_fixture_scope
warn_folder_cardinality
check_loc_ratchet

echo "canonical info architecture: OK"
