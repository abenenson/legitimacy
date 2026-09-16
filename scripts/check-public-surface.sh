#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DOCS=("$ROOT/README.md" "$ROOT/docs/formal-overview.md")
for doc in "${DOCS[@]}"; do
  [[ -f "$doc" ]] || { echo "ERROR: missing public document: $doc" >&2; exit 1; }
done

CLI_HELP="$(cargo run --quiet --manifest-path "$ROOT/Cargo.toml" --bin legitimacy -- --help)"
PROTO_HELP="$(cargo run --quiet --manifest-path "$ROOT/Cargo.toml" --bin legitimacy -- protocol --help)"

for command in extract audit-graph compile paradox certify protocol; do
  if ! grep -Eq "(^|[[:space:]])${command}([[:space:]]|$)" <<<"$CLI_HELP"; then
    echo "ERROR: CLI help missing documented command '${command}'" >&2
    exit 1
  fi
done

for command in init measure activate status audit; do
  if ! grep -Eq "(^|[[:space:]])${command}([[:space:]]|$)" <<<"$PROTO_HELP"; then
    echo "ERROR: protocol help missing documented command '${command}'" >&2
    exit 1
  fi
done

if grep -q '\.legitimacy' "${DOCS[@]}"; then
  echo "ERROR: public documentation references legacy .legitimacy files" >&2
  exit 1
fi

if grep -q '\.verdict' "${DOCS[@]}"; then
  echo "ERROR: public documentation references legacy .verdict files" >&2
  exit 1
fi

for fragment in \
  "legitimacy audit-graph" \
  "--review-overlay" \
  "--claims-provenance" \
  "legitimacy protocol init" \
  "legitimacy protocol measure" \
  "legitimacy protocol activate" \
  "legitimacy protocol status" \
  "legitimacy protocol audit" \
  "observed-runtime"
do
  if ! grep -q -- "$fragment" "${DOCS[@]}"; then
    echo "ERROR: public documentation missing documented workflow fragment '$fragment'" >&2
    exit 1
  fi
done

for suffix in ".rule.toml" ".graph.toml"; do
  if ! grep -q "$suffix" "${DOCS[@]}"; then
    echo "ERROR: public documentation should demonstrate canonical '$suffix' policy files" >&2
    exit 1
  fi
done

while IFS= read -r path; do
  [[ -z "$path" ]] && continue
  if [[ ! -e "$ROOT/$path" ]]; then
    echo "ERROR: public documentation references missing path '$path'" >&2
    exit 1
  fi
done < <(
  grep -h -oE '(audits|docs|examples|lean|papers|reviews|scripts|src|tests/fixtures)/[A-Za-z0-9._/-]+' "${DOCS[@]}" \
    | sed 's/[.),;:]*$//' \
    | sort -u
)

echo "public surface: OK"
