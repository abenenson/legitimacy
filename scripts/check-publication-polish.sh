#!/usr/bin/env bash
set -euo pipefail

# Public-artifact release gate.
#
# Fails closed when tracked workspace/process residue or stale release-prep
# markers leak into the public tree: task-tracker files, internal-only docs,
# co-author trailers, and draft/publication markers. Optional maintainer-local
# vocabulary strengthening is outside this tracked verdict.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
failures=0

public_paths=()
for path in "$ROOT/audits" "$ROOT/papers" "$ROOT/docs" "$ROOT/lean/Legitimacy" "$ROOT/src"; do
  if [[ -e "$path" ]]; then
    public_paths+=("$path")
  fi
done

grep_excludes=(
  --exclude-dir=.git
  --exclude-dir=.lake
  --exclude-dir=target
)

run_grep_check() {
  local message="$1"
  local pattern="$2"
  shift 2
  local hits
  hits="$(grep -RInE "${grep_excludes[@]}" -- "$pattern" "$@" 2>/dev/null || true)"
  if [[ -n "$hits" ]]; then
    echo "ERROR: $message" >&2
    echo "$hits" >&2
    failures=1
  fi
}

while IFS= read -r tracked_path; do
  [[ -n "$tracked_path" ]] || continue
  echo "ERROR: tracked .beads/ files must be removed from public artifacts: $tracked_path:1" >&2
  failures=1
done < <(git -C "$ROOT" ls-files .beads)

while IFS= read -r tracked_path; do
  [[ -n "$tracked_path" ]] || continue
  echo "ERROR: tracked internal/ files must be removed from public artifacts: $tracked_path:1" >&2
  failures=1
done < <(git -C "$ROOT" ls-files internal)

if git -C "$ROOT" ls-files --error-unmatch AGENTS.md >/dev/null 2>&1; then
  echo "ERROR: tracked AGENTS.md must be absent from public artifacts: AGENTS.md:1" >&2
  failures=1
fi

if grep -RIn '\*\*Draft\*\*:\|\*Draft —' "$ROOT/papers"; then
  echo "ERROR: papers/ still contains draft markers" >&2
  failures=1
fi

if grep -RIn 'working drafts' "$ROOT/papers"; then
  echo "ERROR: papers/ still describes itself as working drafts" >&2
  failures=1
fi

if grep -RIn 'project URL to insert at publication time' "$ROOT/papers"; then
  echo "ERROR: papers/ still contains a publication placeholder URL" >&2
  failures=1
fi

if [[ -f "$ROOT/AGENTS.md" ]] && grep -q 'SOUL.md' "$ROOT/AGENTS.md"; then
  echo "ERROR: AGENTS.md references missing SOUL.md" >&2
  failures=1
fi

if grep -q 'cargo test --release' "$ROOT/CONTRIBUTING.md"; then
  echo "ERROR: CONTRIBUTING.md still documents the old test command" >&2
  failures=1
fi

if grep -q 'cargo clippy --release -- -D warnings' "$ROOT/CONTRIBUTING.md"; then
  echo "ERROR: CONTRIBUTING.md still documents the old clippy command" >&2
  failures=1
fi

if ((${#public_paths[@]} > 0)); then
  run_grep_check \
    "remove task-tracker trailers from public prose/code trees" \
    '^Bead:[[:space:]]' \
    "${public_paths[@]}"

  run_grep_check \
    "remove Co-authored-by trailers from public prose/code trees" \
    '^Co-authored-by:' \
    "${public_paths[@]}"
fi

if [[ -f "$ROOT/papers/README.md" ]] && grep -RInHE 'Draft Paper Candidates' "$ROOT/papers/README.md"; then
  echo "ERROR: remove Draft Paper Candidates from papers/README.md" >&2
  failures=1
fi

if ((failures)); then
  exit 1
fi

echo "publication polish: OK"
