#!/usr/bin/env bash
# Verify the theory doc names the canonical 5 axioms.
# Prevents silent reversion to old 4-axiom version.
set -euo pipefail

DOC="docs/repository-context.md"

for axiom in CERTIFIABLE GOVERNANCE-OBSERVABLE CORRIGIBLE "COMPOSITIONAL SAFETY" NON-VACUOUS; do
  if ! grep -q "${axiom}" "$DOC"; then
    echo "ERROR: $DOC missing axiom '${axiom}' — doc may have drifted from the canonical kernel"
    exit 1
  fi
done

# Guard against legacy name sneaking back in
if grep -q "STATE-TRANSPARENT" "$DOC"; then
  if ! grep -q "Renamed from STATE-TRANSPARENT\|Naming note" "$DOC"; then
    echo "ERROR: $DOC contains STATE-TRANSPARENT without rename note"
    exit 1
  fi
fi

# Guard against "Four axioms" (canonical claim is five)
if grep -qE "Four axioms|^## The Four Axioms" "$DOC"; then
  echo "ERROR: $DOC references 'Four axioms' — canonical doc is five (CERTIFIABLE + GOVERNANCE-OBSERVABLE + CORRIGIBLE + COMPOSITIONAL SAFETY + NON-VACUOUS)"
  exit 1
fi

echo "doc alignment: OK (5 canonical axioms present)"
