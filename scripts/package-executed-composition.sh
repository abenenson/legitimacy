#!/usr/bin/env bash
# Build and package a clean checkout; never accept an externally selected binary.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUTPUT="${1:?usage: package-executed-composition.sh NEW_OUTPUT_DIRECTORY}"
OUTPUT="$(realpath -m "$OUTPUT")"
if [[ -e "$OUTPUT" ]]; then echo 'output must be a new directory' >&2; exit 1; fi
if [[ -n "${EXECUTED_COMPOSITION_BINARY:-}" ]]; then
  echo 'binary overrides are forbidden; packaging owns the locked source build' >&2; exit 1
fi
cd "$ROOT"
exec 9>"$(git rev-parse --git-path executed-composition-package.lock)"
flock -n 9 || { echo 'another package build owns this checkout' >&2; exit 1; }
assert_clean() {
  if [[ -n "$(git status --porcelain --untracked-files=all)" ]]; then
    echo 'packaging requires a clean committed checkout throughout the build' >&2; exit 1
  fi
}
assert_clean
SOURCE_COMMIT="$(git rev-parse HEAD)"
SOURCE_TREE="$(git rev-parse HEAD^{tree})"
WORK="$(mktemp -d)"
trap 'rm -rf -- "$WORK"' EXIT
export CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}"
cargo build --locked --profile dev --bin legitimacy-executed-composition --message-format=json > "$WORK/cargo-artifacts.jsonl"
assert_clean
[[ "$(git rev-parse HEAD)" == "$SOURCE_COMMIT" && "$(git rev-parse HEAD^{tree})" == "$SOURCE_TREE" ]] || {
  echo 'source identity changed during build' >&2; exit 1;
}
BINARY="$(python3 - "$WORK/cargo-artifacts.jsonl" <<'PY'
import json, pathlib, sys
artifacts = [json.loads(line) for line in pathlib.Path(sys.argv[1]).read_text().splitlines()]
paths = {a['executable'] for a in artifacts if a.get('reason') == 'compiler-artifact'
         and a.get('target', {}).get('name') == 'legitimacy-executed-composition'
         and a.get('target', {}).get('kind') == ['bin'] and a.get('executable')}
assert len(paths) == 1, 'Cargo did not identify exactly one checker executable'
print(paths.pop())
PY
)"
mkdir -p "$OUTPUT/capture" "$OUTPUT/generated"
strip -o "$OUTPUT/legitimacy-executed-composition" "$BINARY"
chmod +x "$OUTPUT/legitimacy-executed-composition"
cp "$ROOT"/fixtures/executed-composition-v1/capture/*.json "$OUTPUT/capture/"
cp "$ROOT/fixtures/executed-composition-v1/generated/table.json" "$OUTPUT/generated/"
cp "$ROOT/fixtures/executed-composition-v1/policy.json" "$OUTPUT/"
cp "$ROOT/docs/executed-composition-reader.html" "$OUTPUT/reader.html"
cp "$ROOT/docs/executed-composition-v1.md" "$OUTPUT/CONTRACT.md"
cp "$ROOT/scripts/reproduce-executed-composition.sh" "$OUTPUT/reproduce.sh"
chmod +x "$OUTPUT/reproduce.sh"
printf '%s\n' "$SOURCE_COMMIT" > "$OUTPUT/SOURCE_COMMIT"
printf '%s\n' "$SOURCE_TREE" > "$OUTPUT/SOURCE_TREE"
python3 - "$OUTPUT" "$BINARY" <<'PY'
import hashlib, json, os, pathlib, platform, subprocess, sys
out, binary = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
def command(*args): return subprocess.check_output(args, text=True).strip()
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
provenance = {
    'format': 'legitimacy.executed-composition.trusted-builder.v1',
    'checkout_commit': (out / 'SOURCE_COMMIT').read_text().strip(),
    'source_tree': (out / 'SOURCE_TREE').read_text().strip(),
    'source_identity_scope': 'Builder checkout identity; public availability is not asserted by this record. Release publication must resolve the commit in the public repository.',
    'trust_boundary': 'Trusted builder, Cargo dependency cache, compiler, linker and strip tool. This is build provenance, not a reproducible-build or compiler-refinement proof.',
    'build_command': ['cargo', 'build', '--locked', '--profile', 'dev', '--bin', 'legitimacy-executed-composition', '--message-format=json'],
    'rustc': command('rustc', '-Vv'), 'cargo': command('cargo', '-V'),
    'strip': command('strip', '--version').splitlines()[0],
    'system': platform.platform(),
    'cargo_lock_sha256': digest(pathlib.Path('Cargo.lock')),
    'environment': {k: v for k, v in sorted(os.environ.items()) if k.startswith(('CARGO_PROFILE_', 'CARGO_TARGET_')) or k in ['CARGO_BUILD_JOBS', 'CARGO_INCREMENTAL', 'RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'RUSTC', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER', 'RUSTUP_TOOLCHAIN']},
    'unstripped_binary_sha256': digest(binary),
    'packaged_binary_sha256': digest(out / 'legitimacy-executed-composition'),
}
(out / 'BUILD_PROVENANCE.json').write_text(json.dumps(provenance, indent=2) + '\n')
PY
assert_clean
[[ "$(git rev-parse HEAD)" == "$SOURCE_COMMIT" ]] || { echo 'source changed during packaging' >&2; exit 1; }
(cd "$OUTPUT" && sha256sum legitimacy-executed-composition capture/*.json generated/table.json policy.json reader.html CONTRACT.md reproduce.sh SOURCE_COMMIT SOURCE_TREE BUILD_PROVENANCE.json > SHA256SUMS)
"$OUTPUT/reproduce.sh"
echo "Offline bundle: $OUTPUT (Linux $(uname -m); requires compatible libc, bash, Python 3)"
