#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
MANIFEST="$ROOT/audits/parity-manifest.toml"
LEAN_ONLY_REGISTRY="$ROOT/audits/parity/lean-only-modules.txt"
RUST_ONLY_PROPERTY_REGISTRY="$ROOT/audits/rust-only-property-variants.txt"

if [[ ! -f "$MANIFEST" ]]; then
  echo "ERROR: ASI parity manifest missing at audits/parity-manifest.toml" >&2
  exit 1
fi
if [[ ! -f "$LEAN_ONLY_REGISTRY" ]]; then
  echo "ERROR: Lean-only parity registry missing at audits/parity/lean-only-modules.txt" >&2
  exit 1
fi
if [[ ! -f "$RUST_ONLY_PROPERTY_REGISTRY" ]]; then
  echo "ERROR: Rust-only GovernanceProperty registry missing at audits/rust-only-property-variants.txt" >&2
  exit 1
fi

declare -A manifest_leans=()
declare -a manifest_order=()
declare -A manifest_paths=()
declare -A lean_declarations=()
declare -a lean_only_patterns=()
declare -A lean_only_reasons=()
declare -A lean_property_variants=()
declare -A rust_property_variants=()
declare -A rust_only_property_variants=()
declare -a rust_only_property_order=()
current_lean=""
current_lean_path=""
current_rust_path=""
current_rust_identifier=""

while IFS= read -r line || [[ -n "$line" ]]; do
  [[ -n "$line" ]] || continue
  [[ "$line" =~ ^[[:space:]]*# ]] && continue
  read -r lean_only_path lean_only_reason <<< "$line"
  if [[ -z "$lean_only_path" || -z "$lean_only_reason" ]]; then
    echo "ERROR: malformed Lean-only parity registry line: $line" >&2
    exit 1
  fi
  case "$lean_only_path" in
    /*|*..*|*//*)
      echo "ERROR: invalid Lean-only parity path: $lean_only_path" >&2
      exit 1
      ;;
    *.lean|*/)
      ;;
    *)
      echo "ERROR: Lean-only parity path must be a .lean file or trailing-slash prefix: $lean_only_path" >&2
      exit 1
      ;;
  esac
  lean_only_patterns+=("$lean_only_path")
  lean_only_reasons["$lean_only_path"]="$lean_only_reason"
done < "$LEAN_ONLY_REGISTRY"

while IFS= read -r variant; do
  [[ -n "$variant" ]] || continue
  lean_property_variants["$variant"]=1
done < <(
  awk '
    /^inductive GovernanceProperty where/ { in_enum = 1; next }
    in_enum && /^[[:space:]]*\|/ {
      sub(/^[[:space:]]*\|[[:space:]]*/, "")
      sub(/[[:space:]].*$/, "")
      print
    }
    in_enum && /^[[:space:]]*deriving/ { exit }
  ' "$ROOT/lean/Legitimacy/Protocol/State.lean"
)

while IFS= read -r variant; do
  [[ -n "$variant" ]] || continue
  rust_property_variants["$variant"]=1
done < <(
  awk '
    /^pub enum GovernanceProperty / { in_enum = 1; next }
    in_enum && /^}/ { exit }
    in_enum { print }
  ' "$ROOT/src/sacrifice.rs" |
    sed -nE 's/^[[:space:]]*([A-Za-z][A-Za-z0-9]*),.*/\1/p'
)

while IFS= read -r line || [[ -n "$line" ]]; do
  [[ -n "$line" ]] || continue
  [[ "$line" =~ ^[[:space:]]*# ]] && continue
  read -r variant wire reason extra <<< "$line"
  if [[ -z "${variant:-}" || -z "${wire:-}" || -z "${reason:-}" || -n "${extra:-}" ]]; then
    echo "ERROR: malformed Rust-only GovernanceProperty registry line: $line" >&2
    exit 1
  fi
  if [[ ! "$variant" =~ ^[A-Za-z][A-Za-z0-9]*$ ]]; then
    echo "ERROR: invalid Rust-only GovernanceProperty variant: $variant" >&2
    exit 1
  fi
  if [[ ! "$wire" =~ ^[a-z][a-z0-9_]*$ ]]; then
    echo "ERROR: invalid Rust-only GovernanceProperty wire name: $wire" >&2
    exit 1
  fi
  if [[ -z "${rust_property_variants[$variant]+set}" ]]; then
    echo "ERROR: Rust-only GovernanceProperty variant not declared in Rust: $variant" >&2
    exit 1
  fi
  if [[ -n "${lean_property_variants[$variant]+set}" ]]; then
    echo "ERROR: Rust-only GovernanceProperty variant is already mirrored in Lean: $variant" >&2
    exit 1
  fi
  if ! grep -q "\"$wire\"" "$ROOT/src/sacrifice.rs"; then
    echo "ERROR: Rust-only GovernanceProperty wire name not found in sacrifice.rs: $wire" >&2
    exit 1
  fi
  rust_only_property_variants["$variant"]=1
  rust_only_property_order+=("$variant")
done < "$RUST_ONLY_PROPERTY_REGISTRY"

property_drift=()
for variant in "${!lean_property_variants[@]}"; do
  if [[ -z "${rust_property_variants[$variant]+set}" ]]; then
    property_drift+=("Lean-only GovernanceProperty variant missing in Rust: $variant")
  fi
done
for variant in "${!rust_property_variants[@]}"; do
  if [[ -n "${lean_property_variants[$variant]+set}" ]]; then
    continue
  fi
  if [[ -n "${rust_only_property_variants[$variant]+set}" ]]; then
    continue
  fi
  property_drift+=("Rust-only GovernanceProperty variant missing registry entry: $variant")
done

if [[ "${#property_drift[@]}" -ne 0 ]]; then
  printf 'ERROR: GovernanceProperty parity classification drift:\n' >&2
  printf '  %s\n' "${property_drift[@]}" >&2
  exit 1
fi

if [[ "${#rust_only_property_order[@]}" -eq 0 ]]; then
  echo "ERROR: Rust-only GovernanceProperty registry has no variants" >&2
  exit 1
fi

lean_only_reason_for() {
  local lean_path="$1"
  local pattern
  for pattern in "${lean_only_patterns[@]}"; do
    if [[ "$pattern" == */ ]]; then
      if [[ "$lean_path" == "$pattern"* ]]; then
        printf '%s' "${lean_only_reasons[$pattern]}"
        return 0
      fi
    elif [[ "$lean_path" == "$pattern" ]]; then
      printf '%s' "${lean_only_reasons[$pattern]}"
      return 0
    fi
  done
  return 1
}

while IFS= read -r lean_path; do
  while IFS= read -r name; do
    [[ -n "$name" ]] || continue
    lean_declarations["$lean_path:$name"]=1
  done < <(
    rg -No "^[[:space:]]*((private|noncomputable)[[:space:]]+)*(structure|inductive|abbrev|def|theorem|lemma)[[:space:]]+[A-Za-z_][A-Za-z0-9_?'!]*" \
      "$ROOT/$lean_path" |
      sed -E "s/^([^:]+:)?[[:space:]]*((private|noncomputable)[[:space:]]+)*(structure|inductive|abbrev|def|theorem|lemma)[[:space:]]+//"
  )
done <<'EOF'
lean/Legitimacy/SafetySpecReduction.lean
lean/Legitimacy/Kernelization.lean
lean/Legitimacy/Kernelization/Core.lean
lean/Legitimacy/Spectral/Certificates/PositiveProcedureCertificate.lean
lean/Legitimacy/Results/PositiveProcedure.lean
lean/Legitimacy/Spectral/Channels/NoisyThresholdClosedForm.lean
lean/Legitimacy/Spectral/ASIEmbedding/MeasureTheoretic.lean
lean/Legitimacy/Behavioral/ConstitutionalAILineage.lean
lean/Legitimacy/Behavioral/ConstitutionalAIVerdict.lean
lean/Legitimacy/Spectral/Certificates/ConstitutionalAIPositiveProcedure.lean
lean/Legitimacy/Behavioral/ConstitutionalAIWitnesses.lean
lean/Legitimacy/Spectral/Channels/BinaryDecisionHelpers.lean
lean/Legitimacy/Extract/CompositionalSafetyParity.lean
lean/Legitimacy/Extract/CorrigibilityParity.lean
lean/Legitimacy/Extract/CertifiabilityParity.lean
lean/Legitimacy/Extract/ObservableDeterminacyParity.lean
lean/Legitimacy/Extract/NonVacuityParity.lean
lean/Legitimacy/Extract/DiagnosticParity.lean
EOF

flush_entry() {
  if [[ -z "$current_lean$current_lean_path$current_rust_path$current_rust_identifier" ]]; then
    return
  fi
  if [[ -z "$current_lean" || -z "$current_lean_path" || -z "$current_rust_path" || -z "$current_rust_identifier" ]]; then
    echo "ERROR: incomplete ASI parity manifest entry near '${current_lean:-unknown}'" >&2
    exit 1
  fi

  local lean_file="$ROOT/$current_lean_path"
  local rust_file="$ROOT/$current_rust_path"
  if [[ ! -f "$lean_file" ]]; then
    echo "ERROR: Lean parity path missing for $current_lean: $current_lean_path" >&2
    exit 1
  fi
  if [[ ! -f "$rust_file" ]]; then
    echo "ERROR: Rust parity path missing for $current_lean: $current_rust_path" >&2
    exit 1
  fi
  if [[ -z "${lean_declarations[$current_lean_path:$current_lean]+set}" ]]; then
    echo "ERROR: manifest Lean concept not declared: $current_lean in $current_lean_path" >&2
    exit 1
  fi
  if ! grep -Eq "^((pub[[:space:]]+)?(async[[:space:]]+)?(fn|struct|enum|trait|const|static|type)[[:space:]]+$current_rust_identifier\\b|impl[[:space:]]+([^{}]+[[:space:]]+for[[:space:]]+)?$current_rust_identifier([[:space:]<{]|$)|^[[:space:]]+pub[[:space:]]+(async[[:space:]]+)?fn[[:space:]]+$current_rust_identifier\\b)" "$rust_file"; then
    echo "ERROR: Rust counterpart missing for $current_lean: $current_rust_identifier in $current_rust_path" >&2
    exit 1
  fi

  if [[ -z "${manifest_leans[$current_lean]+set}" ]]; then
    manifest_order+=("$current_lean")
  fi
  manifest_leans["$current_lean"]=1
  manifest_paths["$current_lean_path"]=1
}

while IFS= read -r line || [[ -n "$line" ]]; do
  case "$line" in
    "[[concept]]")
      flush_entry
      current_lean=""
      current_lean_path=""
      current_rust_path=""
      current_rust_identifier=""
      ;;
    lean\ =\ \"*\")
      current_lean="${line#lean = \"}"
      current_lean="${current_lean%\"}"
      ;;
    lean_path\ =\ \"*\")
      current_lean_path="${line#lean_path = \"}"
      current_lean_path="${current_lean_path%\"}"
      ;;
    rust_path\ =\ \"*\")
      current_rust_path="${line#rust_path = \"}"
      current_rust_path="${current_rust_path%\"}"
      ;;
    rust_identifier\ =\ \"*\")
      current_rust_identifier="${line#rust_identifier = \"}"
      current_rust_identifier="${current_rust_identifier%\"}"
      ;;
  esac
done < "$MANIFEST"
flush_entry

if [[ "${#manifest_order[@]}" -eq 0 ]]; then
  echo "ERROR: ASI parity manifest has no concepts" >&2
  exit 1
fi

required_lean_concepts=(
  RuleLayerKernelArtifact
  RuleLayerKernelAuditObligations
  KernelAuditConjunction
  noSilentRuleLayerDegradation
  safety_spec_reduces_to_kernel_audit
  AuthorityNodeId
  AuthorityEdge
  AuthorityGraph
  HasAuthorityEdge
  HasAuthorityOverride
  AuthorityEdgeDifference
  AuthorityOverrideDifference
  pathAuthorityEdges
  AuthorityPathPermitted
  routeTarget?
  routeDirectEdge?
  IsEdgePermittedRoute
  IsEdgePermittedBypass
  routeSublists
  ProperRouteSublist
  AuthorityExtensionallyEquivalent
  SourceDerivesEdge
  SourceEdgeDerivation
  SourceEvidenceDerivable
  SemanticFailureLocus
  GovernanceKernelizationObservation
  SourceEvidenceComplete
  KernelizationClean
  UnmodeledEdgeWitness
  BypassPathWitness
  HiddenOverrideWitness
  SourceEvidenceGapWitness
  SemanticBridgeFailureWitness
  SemanticFailureLocusFails
  SemanticFailureLocusPrecedes
  SemanticFailureLocusMinimal
  HiddenAuthorityCertificate
  BypassPathMinimal
  HiddenOverrideDominatesPair
  MinimalHiddenAuthority
  KernelizationHonesty
  KernelizationCleanWitness
  KernelizationExtractorContract
  kernelization_honesty
  rustCheckGraphCompositionalSafety
  rustCheckGraphCorrigibility
  rustCheckGraphCertifiability
  rustCheckObservableDeterminacy
  rustCheckGraphNonVacuity
)

missing=()
for concept in "${required_lean_concepts[@]}"; do
  if [[ -z "${manifest_leans[$concept]+set}" ]]; then
    missing+=("$concept")
  fi
done

if [[ "${#missing[@]}" -ne 0 ]]; then
  printf 'ERROR: ASI Lean concepts missing Rust parity manifest entries:\n' >&2
  printf '  %s\n' "${missing[@]}" >&2
  exit 1
fi

for lean_only_path in "${lean_only_patterns[@]}"; do
  reason="${lean_only_reasons[$lean_only_path]}"
  if [[ "$lean_only_path" == */ ]]; then
    mapfile -t covered_modules < <(
      find "$ROOT/$lean_only_path" -type f -name '*.lean' 2>/dev/null |
        sed "s|^$ROOT/||" |
        sort
    )
    if [[ "${#covered_modules[@]}" -eq 0 ]]; then
      echo "ERROR: Lean-only parity prefix covers no Lean modules: $lean_only_path" >&2
      exit 1
    fi
    printf 'ACK: %s: %s (per audits/parity/lean-only-modules.txt; covers %d Lean module(s))\n' \
      "$lean_only_path" "$reason" "${#covered_modules[@]}"
  else
    if [[ ! -f "$ROOT/$lean_only_path" ]]; then
      echo "ERROR: Lean-only parity file missing: $lean_only_path" >&2
      exit 1
    fi
    printf 'ACK: %s: %s (per audits/parity/lean-only-modules.txt)\n' \
      "$lean_only_path" "$reason"
  fi
done

mapfile -t added_lean_modules < <(
  {
    git -C "$ROOT" diff --name-only --diff-filter=A -- 'lean/Legitimacy/*.lean'
    git -C "$ROOT" diff --name-only --cached --diff-filter=A -- 'lean/Legitimacy/*.lean'
    git -C "$ROOT" ls-files --others --exclude-standard -- 'lean/Legitimacy/*.lean'
  } | sort -u
)

unclassified_added_modules=()
for lean_path in "${added_lean_modules[@]}"; do
  [[ -n "$lean_path" ]] || continue
  if [[ -n "${manifest_paths[$lean_path]+set}" ]]; then
    continue
  fi
  if lean_only_reason_for "$lean_path" >/dev/null; then
    continue
  fi
  unclassified_added_modules+=("$lean_path")
done

if [[ "${#unclassified_added_modules[@]}" -ne 0 ]]; then
  printf 'ERROR: newly added Lean modules need ASI parity classification:\n' >&2
  printf '  %s\n' "${unclassified_added_modules[@]}" >&2
  printf 'Add a Rust parity manifest entry or a reasoned Lean-only exemption in audits/parity/lean-only-modules.txt.\n' >&2
  exit 1
fi
