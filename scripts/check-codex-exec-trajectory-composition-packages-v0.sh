#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 1 ]]; then
  echo "usage: $0 <already-built-legitimacy-binary>|--self-test" >&2
  exit 2
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BINARY="$1"
PACKAGE_ROOT="$ROOT/fixtures/codex-exec-trajectory-composition-packages-v0"
SANITIZED="$PACKAGE_ROOT/sanitized-derived-capture"
SYNTHETIC="$PACKAGE_ROOT/synthetic-fixture"

if [[ "$BINARY" != --self-test && (! -f "$BINARY" || ! -x "$BINARY" || -L "$BINARY") ]]; then
  echo "ERROR: production binary must be an executable regular file" >&2
  exit 1
fi

TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/legitimacy-codex-packages-v0.XXXXXXXX")"
chmod 700 "$TMP_ROOT"
cleanup() {
  case "$TMP_ROOT" in
    "${TMPDIR:-/tmp}"/legitimacy-codex-packages-v0.*) rm -rf -- "$TMP_ROOT" ;;
    *) echo "ERROR: refusing unsafe temporary cleanup" >&2; return 1 ;;
  esac
}
trap cleanup EXIT

fail() {
  echo "ERROR: $*" >&2
  exit 1
}

declare -Ar MUTATION_DIAGNOSTICS=(
  [bundle]=bundle-mismatch
  [input-authority]=receipt-mismatch
  [trusted-context]=trusted-context-mismatch
  [replay-candidate]=replay-candidate-mismatch
  [replay-signature]=authority-receipt-rejected
  [replay-trust]=authority-receipt-rejected
)

mutate_json_field() {
  python3 - "$1" "$2" <<'PY'
import json, sys
path, dotted = sys.argv[1:]
with open(path, "rb") as handle: value = json.load(handle)
target = value
parts = dotted.split(".")
for part in parts[:-1]: target = target[int(part)] if part.isdigit() else target[part]
key = int(parts[-1]) if parts[-1].isdigit() else parts[-1]
old = target[key]
if isinstance(old, str):
    if old.startswith("sha256:"):
        assert len(old) == 71 and all(c in "0123456789abcdef" for c in old[7:])
        target[key] = old[:-1] + ("0" if old[-1] != "0" else "1")
    elif ":" in old and all(c in "0123456789abcdef" for c in old.rsplit(":", 1)[1]):
        prefix, payload = old.rsplit(":", 1)
        assert payload
        target[key] = prefix + ":" + payload[:-1] + ("0" if payload[-1] != "0" else "1")
    elif old and all(c in "0123456789abcdef" for c in old):
        target[key] = old[:-1] + ("0" if old[-1] != "0" else "1")
    elif old:
        target[key] = ("0" if old[0] != "0" else "1") + old[1:]
    else:
        target[key] = "0"
elif isinstance(old, int): target[key] = old + 1
elif isinstance(old, list): target[key] = list(reversed(old))
else: target[key] = None
assert target[key] != old
with open(path, "wb") as handle:
    handle.write(json.dumps(value, separators=(",", ":")).encode() + b"\n")
PY
}

mutate_replay_trust_key() {
  python3 - "$1" <<'PY'
import json, re, sys
path = sys.argv[1]
original = "ed25519:d62f016a1efd1e4fdf793eb42cd84471e1ba9f0cf04d1287b5cc71f616287cb8"
alternate = "ed25519:a6d2455ea3a5771aba9fcb037924114c92f9f325049f6b4269e739d9048bb869"
with open(path, "rb") as handle: value = json.load(handle)
assert value["verification_key"] == original
assert alternate != original
assert re.fullmatch(r"ed25519:[0-9a-f]{64}", alternate)
value["verification_key"] = alternate
with open(path, "wb") as handle:
    handle.write(json.dumps(value, separators=(",", ":")).encode() + b"\n")
PY
}

mutation_self_test() {
  local sample="$TMP_ROOT/mutation-self-test.json"
  printf '%s\n' '{"digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","commitment":"sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb","signature":"ed25519:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc","verification_key":"ed25519:d62f016a1efd1e4fdf793eb42cd84471e1ba9f0cf04d1287b5cc71f616287cb8","name":"policy.example","items":[1,2]}' > "$sample"
  local field before after
  for field in digest commitment signature name items; do
    before="$(sha256sum "$sample")"
    mutate_json_field "$sample" "$field"
    after="$(sha256sum "$sample")"
    [[ "$before" != "$after" ]] || fail "mutation self-test produced an identical file for $field"
  done
  mutate_replay_trust_key "$sample"
  python3 - "$sample" <<'PY' || fail "mutation helper self-test rejected syntax preservation"
import json, re, sys
value = json.load(open(sys.argv[1], "rb"))
assert re.fullmatch(r"sha256:[0-9a-f]{64}", value["digest"])
assert re.fullmatch(r"sha256:[0-9a-f]{64}", value["commitment"])
assert re.fullmatch(r"ed25519:[0-9a-f]{128}", value["signature"])
assert value["verification_key"] == "ed25519:a6d2455ea3a5771aba9fcb037924114c92f9f325049f6b4269e739d9048bb869"
assert value["name"] and value["items"] == [2, 1]
PY
  [[ "${MUTATION_DIAGNOSTICS[input-authority]}" == receipt-mismatch ]]
  [[ "${MUTATION_DIAGNOSTICS[trusted-context]}" == trusted-context-mismatch ]]
  [[ "${MUTATION_DIAGNOSTICS[replay-candidate]}" == replay-candidate-mismatch ]]
  [[ "${MUTATION_DIAGNOSTICS[replay-signature]}" == authority-receipt-rejected ]]
  [[ "${MUTATION_DIAGNOSTICS[replay-trust]}" == authority-receipt-rejected ]]
  local verifier_output="$TMP_ROOT/mutation-verifier.stdout"
  if ! cargo test --quiet --manifest-path "$ROOT/Cargo.toml" --test codex_exec_v0 \
      bundles::checker_mutations_reach_production_authority_rejection -- --exact --nocapture \
      >"$verifier_output" 2>"$TMP_ROOT/mutation-verifier.stderr"; then
    fail "production mutation reachability test failed"
  fi
  for reached in \
    "checker mutation replay-trust authority-receipt-rejected" \
    "checker mutation replay-signature authority-receipt-rejected"; do
    grep -Fx "$reached" "$verifier_output" >/dev/null \
      || fail "production mutation reachability diagnostic was not recorded"
    printf '%s\n' "$reached" >> "$TMP_ROOT/reached-diagnostics.log"
  done
}

if [[ "$BINARY" == --self-test ]]; then
  mutation_self_test
  echo "mutation self-test: ok"
  exit 0
fi

if [[ ! -d "$SANITIZED" || ! -d "$SYNTHETIC" ]]; then
  echo "ERROR: package root is incomplete" >&2
  exit 1
fi

SANITIZED_FILES=(
  SHA256SUMS
  authority/shareable-sanitized-bundle.json
  derived/canonical-trace.bin
  derived/composition-result.json
  derived/trace.json
  replay/authority-receipt.json
  replay/authority-trust-policy.json
  replay/candidate.json
  source/composition-policy.toml
  source/raw-stdout.jsonl
)
SANITIZED_DIRS=(authority derived replay source)
SYNTHETIC_FILES=(
  SHA256SUMS
  authority/input-authority-receipt.json
  authority/trusted-adaptation-context.json
  derived/canonical-trace.bin
  derived/composition-result.json
  derived/trace.json
  replay/authority-receipt.json
  replay/authority-trust-policy.json
  replay/candidate.json
  source/composition-policy.toml
  source/raw-stdout.jsonl
)
SYNTHETIC_DIRS=(authority derived replay source)

validate_package() {
  local package="$1" kind="$2"
  local -n expected_files="$3" expected_dirs="$4"
  local actual expected relative stat_value

  [[ -d "$package" && ! -L "$package" ]] || return 1
  actual="$(find -P "$package" -mindepth 1 -type f -printf '%P\n' | LC_ALL=C sort)"
  expected="$(printf '%s\n' "${expected_files[@]}" | LC_ALL=C sort)"
  [[ "$actual" == "$expected" ]] || return 1
  actual="$(find -P "$package" -mindepth 1 -type d -printf '%P\n' | LC_ALL=C sort)"
  expected="$(printf '%s\n' "${expected_dirs[@]}" | LC_ALL=C sort)"
  [[ "$actual" == "$expected" ]] || return 1
  [[ -z "$(find -P "$package" -mindepth 1 ! -type f ! -type d -print -quit)" ]] || return 1
  [[ -z "$(find -P "$package" -mindepth 1 -type l -print -quit)" ]] || return 1

  for relative in "${expected_files[@]}"; do
    [[ -f "$package/$relative" && ! -L "$package/$relative" ]] || return 1
    stat_value="$(stat -c '%u:%h:%F' "$package/$relative")"
    [[ "$stat_value" == "$(id -u):1:regular file" ]] || return 1
  done
  for relative in "${expected_dirs[@]}"; do
    [[ -d "$package/$relative" && ! -L "$package/$relative" ]] || return 1
  done

  (
    cd "$package"
    for relative in "${expected_files[@]}"; do
      [[ "$relative" == SHA256SUMS ]] || sha256sum -- "$relative"
    done | LC_ALL=C sort -k2
  ) > "$TMP_ROOT/$kind.expected-sha256"
  cmp -s "$package/SHA256SUMS" "$TMP_ROOT/$kind.expected-sha256" || return 1
}

validate_package "$SANITIZED" sanitized SANITIZED_FILES SANITIZED_DIRS \
  || fail "sanitized-derived-capture package shape or manifest is invalid"
validate_package "$SYNTHETIC" synthetic SYNTHETIC_FILES SYNTHETIC_DIRS \
  || fail "synthetic-fixture package shape or manifest is invalid"

run_package() {
  local package="$1" kind="$2" output_root="$3"
  mkdir -m 700 -p "$(dirname "$output_root")"
  [[ ! -e "$output_root" ]] || fail "$kind output-set destination already exists"
  local -a authority_args
  if [[ "$kind" == sanitized ]]; then
    authority_args=(--shareable-sanitized-bundle "$package/authority/shareable-sanitized-bundle.json")
  else
    authority_args=(
      --input-authority-receipt "$package/authority/input-authority-receipt.json"
      --trusted-adaptation-context "$package/authority/trusted-adaptation-context.json"
    )
  fi
  "$BINARY" evaluate-codex-exec-composition-v0 \
    --raw-stdout-jsonl "$package/source/raw-stdout.jsonl" \
    "${authority_args[@]}" \
    --replay-candidate "$package/replay/candidate.json" \
    --replay-authority-receipt "$package/replay/authority-receipt.json" \
    --replay-authority-trust-policy "$package/replay/authority-trust-policy.json" \
    --composition-policy "$package/source/composition-policy.toml" \
    --output-set "$output_root"
}

assert_result() {
  python3 - "$1" "$2" <<'PY'
import json, sys
path, expected_count = sys.argv[1], int(sys.argv[2])
with open(path, "rb") as handle:
    result = json.load(handle)
receipts = result["event_receipts"]
prefixes = result["temporal"]["observed_prefix_receipts"]
classification = result["temporal"]["classification"]
assert len(receipts) == expected_count
assert all(receipt["singleton_decision"] == "permit" for receipt in receipts)
assert [receipt["decision"] for receipt in prefixes[:3]] == ["permit", "permit", "deny"]
assert classification["classification"] == "all-singletons-permit-and-earliest-violation"
assert classification["transition_index"] == 2
assert classification["prefix_length"] == 3
assert classification["denied_occurrence_index"] == 0
assert classification["denied_event_id"] == receipts[0]["claim"]["event_id"]
assert classification["denied_event_id"] != "caller-authored-event-id"
PY
}

for kind in sanitized synthetic; do
  if [[ "$kind" == sanitized ]]; then package="$SANITIZED"; count=4; else package="$SYNTHETIC"; count=3; fi
  rebuild="$TMP_ROOT/rebuild-$kind"
  run_package "$package" "$kind" "$rebuild"
  for relative in trace.json canonical-trace.bin composition-result.json; do
    cmp -s "$package/derived/$relative" "$rebuild/$relative" \
      || fail "$kind production regeneration drifted: derived/$relative"
  done
  assert_result "$rebuild/composition-result.json" "$count" \
    || fail "$kind activation tuple is not exact"
done

# Structural package inventories above are the filename allowlist and primary
# privacy boundary. This bounded scan is defense in depth over text bytes and
# printable strings extracted from canonical binary bytes. It reports only the
# category and path, never the matching value.
python3 - "$PACKAGE_ROOT" <<'PY' || fail "public package privacy scan rejected a surface"
import json, pathlib, re, sys

root = pathlib.Path(sys.argv[1])
patterns = {
    "account-or-email": re.compile(rb"(?:[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}|account(?:_id)?=)", re.I),
    "credential-or-token": re.compile(rb"(?:sk-|bearer |api[_-]?key|access_token|refresh_token|client_secret|private_key|password|passwd|authorization:|cookie=|github_pat_|ghp_|xox[aboprs]-)", re.I),
    "network-or-url": re.compile(rb"(?:https?://|(?<![0-9])(?:[0-9]{1,3}\.){3}[0-9]{1,3}(?![0-9]))", re.I),
    "home-host-environment": re.compile(rb"(?:/home/|/users/|\\\\home\\\\|\.local/state|(?:user|host|hostname|env|environment)=)", re.I),
    "private-custody": re.compile(rb"(?:private-lineage|owner-private|genuine-process-capture)", re.I),
}
uuid = re.compile(rb"(?<![0-9A-Fa-f])[0-9A-Fa-f]{8}-[0-9A-Fa-f]{4}-([0-9A-Fa-f])[0-9A-Fa-f]{3}-([0-9A-Fa-f])[0-9A-Fa-f]{3}-[0-9A-Fa-f]{12}(?![0-9A-Fa-f])")

def printable_runs(data):
    for match in re.finditer(rb"[\x20-\x7e]{4,}", data):
        yield match.group(0)

for path in sorted(root.rglob("*")):
    if not path.is_file() or path.is_symlink():
        continue
    data = path.read_bytes()
    if path.name != "canonical-trace.bin" and any(
        byte < 0x20 and byte not in (0x09, 0x0a, 0x0d) or byte == 0x7f for byte in data
    ):
        print(f"privacy category control-byte in {path.relative_to(root)}", file=sys.stderr)
        raise SystemExit(1)
    surfaces = printable_runs(data) if path.name == "canonical-trace.bin" else (data,)
    for surface in surfaces:
        for category, pattern in patterns.items():
            if pattern.search(surface):
                print(f"privacy category {category} in {path.relative_to(root)}", file=sys.stderr)
                raise SystemExit(1)
        for match in uuid.finditer(surface):
            if match.group(1).lower() != b"7" or match.group(2).lower() not in b"89ab":
                print(f"privacy category non-v7-uuid in {path.relative_to(root)}", file=sys.stderr)
                raise SystemExit(1)
    if "sanitized-derived-capture" in path.parts and path.suffix in (".json", ".jsonl"):
        try:
            values = [json.loads(line) for line in data.splitlines() if line.strip()] if path.suffix == ".jsonl" else [json.loads(data)]
        except Exception:
            print(f"privacy category malformed-json in {path.relative_to(root)}", file=sys.stderr)
            raise SystemExit(1)
        pending = list(values)
        while pending:
            value = pending.pop()
            if isinstance(value, dict): pending.extend(value.values())
            elif isinstance(value, list): pending.extend(value)
            elif isinstance(value, str):
                candidate = value.replace(" \n", "")
                if re.search(r"\s", candidate):
                    print(f"privacy category unexpected-prose in {path.relative_to(root)}", file=sys.stderr)
                    raise SystemExit(1)
PY

expect_cli_failure() {
  local label="$1" package="$2" kind="$3" expected="$4"
  local output_root="$TMP_ROOT/failure-$label"
  if run_package "$package" "$kind" "$output_root" \
      >"$TMP_ROOT/$label.stdout" 2>"$TMP_ROOT/$label.stderr"; then
    fail "$label mutation was accepted"
  fi
  [[ ! -e "$output_root" ]] || fail "$label published a partial or complete output set"
  [[ ! -s "$TMP_ROOT/$label.stdout" ]] || fail "$label wrote stdout"
  [[ "$(<"$TMP_ROOT/$label.stderr")" == "legitimacy: $expected" ]] \
    || fail "$label did not reach expected verifier $expected"
  printf '%s %s\n' "$label" "$expected" >> "$TMP_ROOT/reached-diagnostics.log"
}

copy_package() {
  local source="$1" label="$2"
  local destination="$TMP_ROOT/mutation-$label"
  cp -a -- "$source" "$destination"
  printf '%s\n' "$destination"
}

mutate_raw() {
  python3 - "$1" "$2" <<'PY'
import json, sys
path, operation = sys.argv[1:]
data = open(path, "rb").read()
lines = data.splitlines(keepends=True)
if operation == "insert": lines.insert(1, lines[0])
elif operation == "delete": del lines[1]
elif operation == "reorder": lines[0], lines[1] = lines[1], lines[0]
elif operation == "truncate": data = data[:-1]; lines = None
elif operation == "bit":
    pos = next(i for i, value in enumerate(data) if value not in (10, 13))
    data = data[:pos] + bytes([data[pos] ^ 1]) + data[pos + 1:]
    lines = None
else: raise AssertionError(operation)
open(path, "wb").write(b"".join(lines) if lines is not None else data)
PY
}

for operation in insert delete reorder truncate bit; do
  mutation="$(copy_package "$SANITIZED" "source-$operation")"
  mutate_raw "$mutation/source/raw-stdout.jsonl" "$operation"
  expect_cli_failure "source-$operation" "$mutation" sanitized receipt-mismatch
done

bundle_fields=(
  bundle_version
  schema.identity
  adapter.identity
  sanitizer.identity
  sanitizer.hash
  downstream_governance_policy.hash
  official_trace_json
  canonical_trace_lower_hex
  trajectory_digest
  payload_manifest.0.digest
  public_derived_receipt.derived_raw_capture_seal.digest
  public_derived_receipt.sanitizer_policy.hash
  public_derived_receipt.sanitizer_artifact.hash
  public_transformation.adapter.hash
  public_transformation.schema.hash
  public_transformation.downstream_governance_policy.hash
  public_transformation.sanitizer_policy.hash
  public_transformation.normalized_trace_digest
  public_transformation.derived_capture_seal.digest
  public_transformation.payload_manifest.0.digest
)
index=0
for field in "${bundle_fields[@]}"; do
  label="bundle-$index"
  mutation="$(copy_package "$SANITIZED" "$label")"
  mutate_json_field "$mutation/authority/shareable-sanitized-bundle.json" "$field"
  expect_cli_failure "$label" "$mutation" sanitized "${MUTATION_DIAGNOSTICS[bundle]}"
  index=$((index + 1))
done

inject_public_assertions() {
  python3 - "$1" "$2" <<'PY'
import json, sys
path, operation = sys.argv[1:]
with open(path, "rb") as handle: value = json.load(handle)
zero = "sha256:" + ("0" * 64)
if operation == "origin":
    value["public_derived_receipt"]["asserted_origin_evidence_class"] = "genuine-process-capture"
    value["public_derived_receipt"]["asserted_parent_receipt"] = "asserted-parent-receipt-process-capture-capture-random"
elif operation == "receipt":
    value["public_derived_receipt"]["derived_receipt_commitment"] = zero
    value["public_transformation"]["derived_authority_commitment"] = zero
elif operation == "parent":
    value["public_parent_commitment"] = zero
    value["public_derived_receipt"]["public_parent_commitment"] = zero
    value["public_transformation"]["public_parent_commitment"] = zero
else: raise AssertionError(operation)
with open(path, "wb") as handle:
    handle.write(json.dumps(value, separators=(",", ":")).encode() + b"\n")
PY
}

for operation in origin receipt parent; do
  label="coordinated-public-$operation"
  mutation="$(copy_package "$SANITIZED" "$label")"
  inject_public_assertions "$mutation/authority/shareable-sanitized-bundle.json" "$operation"
  expect_cli_failure "$label" "$mutation" sanitized json-shape
done

mutation="$(copy_package "$SYNTHETIC" input-authority)"
mutate_json_field "$mutation/authority/input-authority-receipt.json" full_jsonl_digest
expect_cli_failure input-authority "$mutation" synthetic "${MUTATION_DIAGNOSTICS[input-authority]}"

mutation="$(copy_package "$SYNTHETIC" trusted-context)"
mutate_json_field "$mutation/authority/trusted-adaptation-context.json" authority_commitment
expect_cli_failure trusted-context "$mutation" synthetic "${MUTATION_DIAGNOSTICS[trusted-context]}"

mutation="$(copy_package "$SYNTHETIC" replay-candidate)"
mutate_json_field "$mutation/replay/candidate.json" trajectory_digest
expect_cli_failure replay-candidate "$mutation" synthetic "${MUTATION_DIAGNOSTICS[replay-candidate]}"

mutation="$(copy_package "$SYNTHETIC" replay-signature)"
mutate_json_field "$mutation/replay/authority-receipt.json" signature
expect_cli_failure replay-signature "$mutation" synthetic "${MUTATION_DIAGNOSTICS[replay-signature]}"

mutation="$(copy_package "$SYNTHETIC" replay-trust)"
mutate_replay_trust_key "$mutation/replay/authority-trust-policy.json"
expect_cli_failure replay-trust "$mutation" synthetic "${MUTATION_DIAGNOSTICS[replay-trust]}"

mutation="$(copy_package "$SYNTHETIC" compiled-policy)"
printf ' ' >> "$mutation/source/composition-policy.toml"
expect_cli_failure compiled-policy "$mutation" synthetic policy-digest-mismatch

structural_control() {
  local label="$1" package="$2" kind="$3" files_name="$4" dirs_name="$5"
  if validate_package "$package" "$kind-$label" "$files_name" "$dirs_name"; then
    fail "$label package-structure mutation was accepted"
  fi
}

mutation="$(copy_package "$SANITIZED" incomplete)"; rm -- "$mutation/replay/candidate.json"
structural_control incomplete "$mutation" sanitized SANITIZED_FILES SANITIZED_DIRS
mutation="$(copy_package "$SANITIZED" extra)"; : > "$mutation/extra"
structural_control extra "$mutation" sanitized SANITIZED_FILES SANITIZED_DIRS
mutation="$(copy_package "$SANITIZED" stale-manifest)"; printf ' ' >> "$mutation/derived/trace.json"
structural_control stale-manifest "$mutation" sanitized SANITIZED_FILES SANITIZED_DIRS
mutation="$(copy_package "$SANITIZED" symlink)"; rm -- "$mutation/replay/candidate.json"; ln -s ../derived/trace.json "$mutation/replay/candidate.json"
structural_control symlink "$mutation" sanitized SANITIZED_FILES SANITIZED_DIRS
mutation="$(copy_package "$SANITIZED" hardlink)"; rm -- "$mutation/replay/candidate.json"; ln "$mutation/derived/trace.json" "$mutation/replay/candidate.json"
structural_control hardlink "$mutation" sanitized SANITIZED_FILES SANITIZED_DIRS
mutation="$(copy_package "$SANITIZED" special)"; rm -- "$mutation/replay/candidate.json"; mkfifo "$mutation/replay/candidate.json"
structural_control special "$mutation" sanitized SANITIZED_FILES SANITIZED_DIRS

# Changed-after-snapshot behavior is exercised against the production snapshot
# and output-set transaction in the Rust publication tests. Keep this checker
# focused on package bytes and late production verifiers.
for false_field in transition_index prefix_length denied_occurrence_index denied_event_id; do
  if python3 - "$SANITIZED/derived/composition-result.json" "$false_field" <<'PY'
import json, sys
result = json.load(open(sys.argv[1], "rb"))
field = sys.argv[2]
actual = result["temporal"]["classification"][field]
false = "caller-authored-event-id" if field == "denied_event_id" else actual + 1
assert actual == false
PY
  then fail "false $false_field assertion was accepted"
  fi
done

echo "codex-exec trajectory composition packages v0: OK"
