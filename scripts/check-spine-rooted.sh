#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
README="$ROOT/README.md"
FACADE="$ROOT/lean/Legitimacy.lean"

if [[ ! -f "$README" ]]; then
  echo "ERROR: README not found: $README" >&2
  exit 1
fi

if [[ ! -f "$FACADE" ]]; then
  echo "ERROR: Lean facade not found: $FACADE" >&2
  exit 1
fi

mapfile -t spine_entries < <(
  awk '
    /^\| Role \| Spine theorem \|/ { in_table = 1; next }
    in_table && /^\| ---/ { next }
    in_table && /^\|/ {
      split($0, cols, "|")
      theorem_col = cols[3]
      path = cols[5]
      theorem_match = match(theorem_col, /`[^`]+`/)
      if (theorem_match) {
        theorem = substr(theorem_col, RSTART + 1, RLENGTH - 2)
      }
      path_match = match(path, /`lean\/[^`]+\.lean(:[0-9]+)?`/)
      if (theorem_match && path_match) {
        entry = substr(path, RSTART + 1, RLENGTH - 2)
        print theorem "\t" entry
      }
      next
    }
    in_table { exit }
  ' "$README"
)

if [[ "${#spine_entries[@]}" -eq 0 ]]; then
  echo "ERROR: no Lean paths found in README Theorem Spine table" >&2
  exit 1
fi

declare -A direct_imports=()
while IFS= read -r module; do
  direct_imports["$module"]=1
done < <(awk '/^import / { print $2 }' "$FACADE")

missing=()
for spine_entry in "${spine_entries[@]}"; do
  IFS=$'\t' read -r theorem_name path_entry <<< "$spine_entry"

  if [[ ! "$path_entry" =~ :[0-9]+$ ]]; then
    missing+=("$theorem_name -> $path_entry (missing line number)")
    continue
  fi

  path="${path_entry%:*}"
  line="${path_entry##*:}"
  lean_file="$ROOT/$path"
  if [[ ! -f "$lean_file" ]]; then
    missing+=("$theorem_name -> $path_entry (file missing)")
    continue
  fi

  module="${path#lean/}"
  module="${module%.lean}"
  module="${module//\//.}"
  if [[ -z "${direct_imports[$module]:-}" ]]; then
    missing+=("$theorem_name -> $path_entry -> import $module")
    continue
  fi

  declaration_name="${theorem_name##*.}"
  line_text="$(sed -n "${line}p" "$lean_file")"
  if ! grep -Eq "^[[:space:]]*(theorem|def|lemma|structure)[[:space:]]+${declaration_name}([^[:alnum:]_']|$)" <<< "$line_text"; then
    missing+=("$theorem_name -> $path_entry (line does not declare $declaration_name)")
  fi
done

if [[ "${#missing[@]}" -gt 0 ]]; then
  echo "ERROR: README Theorem Spine entries must be directly imported and line-accurate" >&2
  printf '  %s\n' "${missing[@]}" >&2
  exit 1
fi

echo "spine rooted: OK"
