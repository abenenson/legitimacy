#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"

check_theorem_line() {
  local theorem="$1"
  local path="$2"
  local line="$3"
  local file="$ROOT/$path"

  if [[ ! -f "$file" ]]; then
    echo "ERROR: README theorem spine path does not exist: $path" >&2
    exit 1
  fi

  local actual
  actual="$(sed -n "${line}p" "$file")"
  if [[ "$actual" != *"theorem $theorem"* ]]; then
    echo "ERROR: README theorem spine citation drifted: $theorem expected at $path:$line" >&2
    echo "actual: $actual" >&2
    exit 1
  fi

  if ! grep -Fq "\`$path:$line\`" "$ROOT/README.md"; then
    echo "ERROR: README theorem spine table is missing $path:$line" >&2
    exit 1
  fi
}

check_theorem_line "C_star_exists" "lean/Legitimacy/Spectral/Capacity/CriticalCapability.lean" 55
check_theorem_line "channel_capacity_bounds_C_star" "lean/Legitimacy/Spectral/Channels/CStarChannelBridge.lean" 551
check_theorem_line "capability_scaling_shared_cliff" "lean/Legitimacy/Results/CapabilityScalingKernelSafety.lean" 639
check_theorem_line "reachable_peer_relative_decisive_stage_obstructs_diagnostics" "lean/Legitimacy/Impossibility/PeerRelativeReachable.lean" 103
check_theorem_line "noUndeclaredSacrificeImplication" "lean/Legitimacy/Safety/KernelSafety/BinaryDecisionPipeline.lean" 145
check_theorem_line "semanticKernel_iff_runtime_diagnostic_spectral_layers" "lean/Legitimacy/Results/SemanticBridge.lean" 74
