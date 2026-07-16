#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_LEAN="$(mktemp "${TMPDIR:-/tmp}/legitimacy-axiom-footprint.XXXXXX.lean")"
trap 'rm -f "$TMP_LEAN"' EXIT

cat >"$TMP_LEAN" <<'LEAN'
import Legitimacy
import Legitimacy.Results.SpineFootprint

#print axioms Legitimacy.reachable_peer_relative_decisive_stage_obstructs_diagnostics
#print axioms Legitimacy.complete_first_effective_implies_reachable_peer_relative_decisive
#print axioms Legitimacy.non_peer_relative_collapse_or_infeasible_or_exits_kernel
#print axioms Legitimacy.decisionSystem_solidarity_monotonicity_imply_strategyproof
#print axioms Legitimacy.semanticKernel_iff_runtime_diagnostic_spectral_layers_unfolded
#print axioms Legitimacy.spineFootprint
#print axioms Legitimacy.bounded_extractor_contract_sound
#print axioms Legitimacy.codexHooksGovernanceAdmissibilityRejectsMonotonicity
LEAN

(
  cd "$ROOT/lean"
  lake build Legitimacy.Results.SpineFootprint >/dev/null
)

raw_output="$(
  cd "$ROOT/lean"
  lake env lean "$TMP_LEAN" 2>&1
)"

actual="$(
  printf '%s\n' "$raw_output" |
    perl -0ne '
      while (/depends on axioms:\s*\[(.*?)\]/sg) {
        my $body = $1;
        $body =~ s/\s+//g;
        for my $axiom (split /,/, $body) {
          next if $axiom eq "";
          $axiom = "Lean.ofReduceBool"
            if $axiom =~ /^Legitimacy\..*_native\.native_decide\.ax_[A-Za-z0-9_]+(?:\P{ASCII}.*)?$/;
          print "$axiom\n";
        }
      }
    ' |
    sort -u
)"

expected=$'Classical.choice\nLean.ofReduceBool\nQuot.sound\npropext'

if [[ "$actual" != "$expected" ]]; then
  echo "ERROR: Lean axiom footprint drifted" >&2
  echo "Expected normalized axiom set:" >&2
  printf '%s\n' "$expected" >&2
  echo "Actual normalized axiom set:" >&2
  printf '%s\n' "$actual" >&2
  echo "Raw #print axioms output:" >&2
  printf '%s\n' "$raw_output" >&2
  exit 1
fi

echo "Axiom footprint OK: {propext, Classical.choice, Quot.sound, Lean.ofReduceBool}"
