#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"

require_theorem() {
  local name="$1"
  if ! grep -R -n -E "^[[:space:]]*theorem[[:space:]]+$name\\b" "$ROOT/lean/Legitimacy/Results" >/dev/null; then
    echo "ERROR: missing formal theorem declaration '$name'" >&2
    return 1
  fi
}

require_theorem "codexHooksGovernanceAdmissibilityRejectsMonotonicity"
require_theorem "claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity"
require_theorem "crewAIHooksGovernanceAdmissibilityRejectsMonotonicity"
require_theorem "openClawInfraNonvacuityCheckFails"

echo "canonical joint-witness coverage: OK"
