#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_ROOT="$(mktemp -d)"
trap 'rm -rf "$TMP_ROOT"' EXIT

python3 "$ROOT/scripts/generate-trajectory-composition-fixtures.py" \
  --repository-root "$ROOT" \
  --output-root "$TMP_ROOT"

discover_projection_files() {
  local base="$1"
  find \
    "$base/fixtures/trajectory-composition-v0/benign" \
    "$base/fixtures/trajectory-composition-v0/red" \
    "$base/lean/Legitimacy/Protocol/TrajectoryCompositionGenerated" \
    -type f -print | sed "s#^$base/##" | sort
}

mapfile -t committed_projection_files < <(discover_projection_files "$ROOT")
mapfile -t regenerated_projection_files < <(discover_projection_files "$TMP_ROOT")
if [[ "${committed_projection_files[*]}" != "${regenerated_projection_files[*]}" ]]; then
  echo "ERROR: trajectory composition generated projection set drifted" >&2
  diff -u \
    <(printf '%s\n' "${committed_projection_files[@]}") \
    <(printf '%s\n' "${regenerated_projection_files[@]}") || true
  exit 1
fi
for relative in "${committed_projection_files[@]}"; do
  if ! cmp -s "$ROOT/$relative" "$TMP_ROOT/$relative"; then
    echo "ERROR: trajectory composition generated projection drifted: $relative" >&2
    diff -u "$ROOT/$relative" "$TMP_ROOT/$relative" || true
    exit 1
  fi
done

mkdir -p "$TMP_ROOT/fixtures/trajectory-composition-v0/generated"
(
  cd "$ROOT/lean"
  lake exe trajectory_composition_fixture_export
) > "$TMP_ROOT/fixtures/trajectory-composition-v0/generated/expected-results.json"

discover_export_files() {
  local base="$1"
  find "$base/fixtures/trajectory-composition-v0/generated" \
    -type f -print | sed "s#^$base/##" | sort
}

mapfile -t committed_export_files < <(discover_export_files "$ROOT")
mapfile -t regenerated_export_files < <(discover_export_files "$TMP_ROOT")
if [[ "${committed_export_files[*]}" != "${regenerated_export_files[*]}" ]]; then
  echo "ERROR: trajectory composition generated export set drifted" >&2
  diff -u \
    <(printf '%s\n' "${committed_export_files[@]}") \
    <(printf '%s\n' "${regenerated_export_files[@]}") || true
  exit 1
fi
for relative in "${committed_export_files[@]}"; do
  if ! cmp -s "$ROOT/$relative" "$TMP_ROOT/$relative"; then
    echo "ERROR: trajectory composition Lean export drifted: $relative" >&2
    diff -u "$ROOT/$relative" "$TMP_ROOT/$relative" || true
    exit 1
  fi
done

# Prove that the same complete-set byte gate detects an owned-artifact mutation.
control_file="$TMP_ROOT/fixtures/trajectory-composition-v0/generated/expected-results.json"
printf ' ' >> "$control_file"
if cmp -s \
  "$ROOT/fixtures/trajectory-composition-v0/generated/expected-results.json" \
  "$control_file"; then
  echo "ERROR: trajectory composition generated-drift mutation was not detected" >&2
  exit 1
fi

echo "trajectory composition fixtures: OK"
