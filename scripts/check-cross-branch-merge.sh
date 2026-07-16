#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
remote_refs="$(mktemp /tmp/legitimacy-cross-branch-refs.XXXXXX)"
merge_out="$(mktemp /tmp/legitimacy-cross-branch-merge.XXXXXX)"
trap 'rm -f "$remote_refs" "$merge_out"' EXIT

if ! timeout 5 git -C "$ROOT" ls-remote --heads origin >"$remote_refs" 2>&1; then
  echo "INFO: cross-branch merge check skipped (origin unreachable or no network)"
  exit 0
fi

if ! grep -q $'refs/heads/papers$' "$remote_refs"; then
  echo "cross-branch merge: origin/papers absent; skipping"
  exit 0
fi

if ! timeout 20 git -C "$ROOT" fetch -q origin master papers; then
  echo "INFO: cross-branch merge check skipped (origin unreachable or no network)"
  exit 0
fi

if git -C "$ROOT" merge-tree --write-tree --name-only origin/master origin/papers >"$merge_out" 2>&1; then
  echo "cross-branch merge: origin/papers merges cleanly onto origin/master"
  exit 0
fi

echo "ERROR: origin/papers does not merge cleanly onto origin/master" >&2
cat "$merge_out" >&2
exit 1
