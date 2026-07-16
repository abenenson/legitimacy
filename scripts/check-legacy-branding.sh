#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DENYLIST="$ROOT/scripts/maintainer-denylist.sh"

if [[ ! -f "$DENYLIST" ]]; then
  echo "legacy branding: OK (maintainer denylist absent; check skipped)"
  exit 0
fi

# shellcheck source=/dev/null
source "$DENYLIST"

for check in "${LEGACY_BRANDING_CHECKS[@]}"; do
  file="${check%%:::*}"
  pattern="${check#*:::}"
  if grep -Fq "$pattern" "$ROOT/$file"; then
    echo "ERROR: stale legacy wording remains in '$file'" >&2
    exit 1
  fi
done

echo "legacy branding: OK"
