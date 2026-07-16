#!/usr/bin/env bash

assert_canonical_axiom_inventory() {
  local root="${1:-$(pwd)}"
  local expected_checks expected_properties expected_header

  expected_checks=$'AuditCheck.consistency\nAuditCheck.solidarity\nAuditCheck.monotonicity\nAuditCheck.strategyproofness\nAuditCheck.certifiability\nAuditCheck.observableDeterminacy\nAuditCheck.corrigibility\nAuditCheck.compositionalSafety\nAuditCheck.nonvacuous'
  expected_properties=$'Consistency\nSolidarity\nMonotonicity\nStrategyproofness\nCertifiability\nObservableDeterminacy\nCorrigibility\nCompositionalSafety\nNonVacuous'
  expected_header='| System | Mode | Nodes | Edges | Connected | λ₂ | C | S | M | SP | Cert | Obs | Corr | Comp | NV | Paradoxes | LFE |'
  expected_protocol_header='| System | Coverage | Resolution issues | Boundary-relative compositional safety | Live findings |'

  local actual_checks
  actual_checks="$(
    awk '
      /^def auditCheckOrder : List AuditCheck :=/ { in_order = 1; next }
      in_order && $0 ~ /^[[:space:]]*\]/ { exit }
      in_order && index($0, "AuditCheck.") {
        gsub(/[ ,\[\]]/, "", $0)
        print $0
      }
    ' "$root/lean/Legitimacy/Results/SelfAudit.lean"
  )"
  if [[ "$actual_checks" != "$expected_checks" ]]; then
    echo "ERROR: Lean auditCheckOrder does not match canonical axiom order" >&2
    echo "expected:" >&2
    echo "$expected_checks" >&2
    echo "actual:" >&2
    echo "$actual_checks" >&2
    exit 1
  fi

  local actual_properties
  actual_properties="$(
    awk '
      /^pub enum GovernanceProperty \{/ { in_enum = 1; next }
      in_enum && /^\}/ { exit }
      in_enum {
        gsub(/[ ,]/, "", $0)
        if ($0 != "") print $0
      }
    ' "$root/src/sacrifice.rs"
  )"
  if [[ "$actual_properties" != "$expected_properties" ]]; then
    echo "ERROR: Rust GovernanceProperty variants do not match canonical axiom order" >&2
    echo "expected:" >&2
    echo "$expected_properties" >&2
    echo "actual:" >&2
    echo "$actual_properties" >&2
    exit 1
  fi

  for wire in \
    '"graph certifiability"' \
    '"graph observable determinacy"' \
    '"graph corrigibility"' \
    '"graph compositional safety"' \
    '"graph nonvacuity"'
  do
    if ! grep -F -n "$wire" "$root/src/axioms/kernel/mod.rs" >/dev/null; then
      echo "ERROR: missing reserved kernel projection wire name $wire" >&2
      exit 1
    fi
  done

  local forbidden converse_pattern
  converse_pattern='converse[-_[:space:]]*consistency|converseconsistency'
  forbidden="$(
    grep -R -n -I -i -E "$converse_pattern" \
      "$root/lean/Legitimacy" "$root/src" || true
  )"
  if [[ -n "$forbidden" ]]; then
    echo "ERROR: noncanonical ConverseConsistency surface remains:" >&2
    echo "$forbidden" >&2
    exit 1
  fi

  local audit_forbidden archival_marker
  archival_marker='ARCHIVAL-CONVERSE-CONSISTENCY-SNAPSHOT'
  audit_forbidden="$(
    while IFS= read -r hit; do
      local file="${hit%%:*}"
      if grep -F -q "$archival_marker" "$file"; then
        continue
      fi
      printf '%s\n' "$hit"
    done < <(
      grep -R -n -I -i -E "$converse_pattern" \
        "$root/audits" || true
    )
  )"
  if [[ -n "$audit_forbidden" ]]; then
    echo "ERROR: noncanonical ConverseConsistency audit residue remains:" >&2
    echo "$audit_forbidden" >&2
    echo "Mark true historical snapshots with $archival_marker or refresh them." >&2
    exit 1
  fi

  if ! grep -F -n "$expected_header" "$root/audits/leaderboard/LEADERBOARD.md" >/dev/null; then
    echo "ERROR: LEADERBOARD.md header does not match canonical axiom columns" >&2
    grep -n -F '| System | Mode | Nodes | Edges | Connected | λ₂ |' \
      "$root/audits/leaderboard/LEADERBOARD.md" >&2 || true
    exit 1
  fi

  if ! grep -F -n "$expected_protocol_header" "$root/audits/leaderboard/LEADERBOARD.md" >/dev/null; then
    echo "ERROR: LEADERBOARD.md protocol/boundary header does not match publication-clean wording" >&2
    grep -n -F '| System | Coverage | Resolution issues | Boundary-relative compositional safety |' \
      "$root/audits/leaderboard/LEADERBOARD.md" >&2 || true
    exit 1
  fi
}
