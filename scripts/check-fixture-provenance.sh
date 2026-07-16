#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
DISCLOSURES="$ROOT/audits/fixtures/sources/leaderboard/test-source-disclosures.txt"

if [[ ! -f "$DISCLOSURES" ]]; then
  echo "ERROR: missing fixture provenance disclosure registry: ${DISCLOSURES#"$ROOT/"}" >&2
  exit 1
fi

mapfile -t allowed_patterns < <(
  sed -nE 's/^[[:space:]]*allow:[[:space:]]*([^#[:space:]].*[^[:space:]])[[:space:]]*(#.*)?$/\1/p' \
    "$DISCLOSURES"
)

if [[ "${#allowed_patterns[@]}" -eq 0 ]]; then
  echo "ERROR: fixture provenance disclosure registry has no allow entries" >&2
  exit 1
fi

scan_paths=(
  "$ROOT/audits/leaderboard"
  "$ROOT/audits/corpus"
  "$ROOT/lean/Legitimacy/Results"
)

mapfile -t findings < <(
  rg -n '/tests/' "${scan_paths[@]}" \
    --glob '*-graph.json' \
    --glob 'extractor_report.json' \
    --glob '*AdmissibilityAudit*.lean' \
    --glob 'LeaderboardAdmissibilityAudits.lean' \
    2>/dev/null || true
)

failed=0
for finding in "${findings[@]}"; do
  allowed=0
  for pattern in "${allowed_patterns[@]}"; do
    if [[ "$finding" == *"$pattern"* ]]; then
      allowed=1
      break
    fi
  done

  if [[ "$allowed" -eq 0 ]]; then
    echo "ERROR: undisclosed test-source fixture provenance:" >&2
    echo "$finding" >&2
    failed=1
  fi
done

if [[ "$failed" -ne 0 ]]; then
  echo "ERROR: add a prominent disclosure before accepting any /tests/ fixture source" >&2
  exit 1
fi

echo "fixture provenance disclosures: OK"
