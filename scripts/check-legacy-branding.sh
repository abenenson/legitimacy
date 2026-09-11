#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if git -C "$ROOT" ls-files --error-unmatch scripts/maintainer-denylist.sh >/dev/null 2>&1; then
  echo "ERROR: maintainer-local policy must not be tracked verification authority" >&2
  exit 1
fi

echo "legacy branding: OK (tracked boundary)"
