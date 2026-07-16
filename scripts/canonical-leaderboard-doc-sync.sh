#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
LEADERBOARD="$ROOT/audits/leaderboard/LEADERBOARD.md"
DOC="$ROOT/docs/repository-context.md"

fail() {
  echo "ERROR: $*" >&2
  exit 1
}

[[ -f "$LEADERBOARD" ]] || fail "missing audits/leaderboard/LEADERBOARD.md"
[[ -f "$DOC" ]] || fail "missing docs/repository-context.md"

systems="$(
  awk '
    /^## Current Results/ { in_table = 1; next }
    /^## Observed-Runtime Example/ { in_table = 0 }
    in_table && /^\| \*\*/ {
      line = $0
      sub(/^\| \*\*/, "", line)
      sub(/\*\* .*/, "", line)
      print line
    }
  ' "$LEADERBOARD"
)"

[[ -n "$systems" ]] || fail "could not extract automatic leaderboard system names"

missing=0
while IFS= read -r system; do
  [[ -n "$system" ]] || continue
  if ! grep -F -q "$system" "$DOC"; then
    echo "ERROR: docs/repository-context.md missing leaderboard system '$system'" >&2
    missing=1
  fi
done <<<"$systems"

[[ "$missing" -eq 0 ]] || exit 1

echo "canonical leaderboard/doc sync: OK"
