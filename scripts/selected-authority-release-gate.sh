#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
selected_test=selected_authority_full_tree_release_gate
repository_state_check="$ROOT/scripts/selected-authority-repository-state.sh"

fail() {
  echo "ERROR: $*" >&2
  exit 1
}

require_clean_repository() {
  bash "$repository_state_check" "$ROOT" "$initial_head" "$initial_tree" >/dev/null \
    || fail "selected-authority repository is not the exact clean initial tree"
}

file_identity() {
  stat -Lc '%d:%i:%s' -- "$1"
}

file_sha256() {
  sha256sum -- "$1" | awk '{print $1}'
}

initial_head="$(git -C "$ROOT" rev-parse HEAD)"
initial_tree="$(git -C "$ROOT" rev-parse HEAD^{tree})"
[[ -f "$repository_state_check" && -x "$repository_state_check" && ! -L "$repository_state_check" ]] \
  || fail "repository state check is not an exact executable file"
require_clean_repository

rustc_command="$(command -v rustc)"
cargo_command="$(command -v cargo)"
python_command="$(command -v python3)"
python_path="$(readlink -f "$python_command")"
active_rustc_path="$(readlink -f "$rustc_command")"
active_cargo_path="$(readlink -f "$cargo_command")"
process_supervisor="$ROOT/scripts/selected-authority-process-supervisor.py"
test_binary_selector="$ROOT/scripts/selected-authority-test-binary.py"
[[ -f "$python_path" && -x "$python_path" && ! -L "$python_path" ]] \
  || fail "resolved Python is not an exact regular executable"
[[ -f "$process_supervisor" && ! -L "$process_supervisor" ]] \
  || fail "process supervisor is not an exact regular file"
[[ -f "$test_binary_selector" && ! -L "$test_binary_selector" ]] \
  || fail "test-binary selector is not an exact regular file"
python_identity="$(file_identity "$python_path")"
python_sha256="$(file_sha256 "$python_path")"
active_rustc_identity="$(file_identity "$active_rustc_path")"
active_rustc_sha256="$(file_sha256 "$active_rustc_path")"
active_cargo_identity="$(file_identity "$active_cargo_path")"
active_cargo_sha256="$(file_sha256 "$active_cargo_path")"
supervisor_identity="$(file_identity "$process_supervisor")"
supervisor_sha256="$(file_sha256 "$process_supervisor")"
selector_identity="$(file_identity "$test_binary_selector")"
selector_sha256="$(file_sha256 "$test_binary_selector")"
expected_rustc_sha256=8aef3883da0e960e5dc63c59a02a8be391d28a8585171aa3e380f67f18b1c1e9
expected_cargo_sha256=f5276e159a687a8d156e8c032644bc9c2759a8c5b8533da2141cf8d4bad84f67

exec {python_fd}<"$python_path"
exec {supervisor_fd}<"$process_supervisor"
exec {selector_fd}<"$test_binary_selector"
python_exec="/proc/self/fd/$python_fd"
supervisor_exec="/proc/self/fd/$supervisor_fd"
selector_exec="/proc/self/fd/$selector_fd"

expected_rustc="$({
  cat <<'EOF'
rustc 1.95.0-nightly (9e79395f9 2026-02-10)
binary: rustc
commit-hash: 9e79395f92bff6a8f536430e42a4beae69f60ff8
commit-date: 2026-02-10
host: x86_64-unknown-linux-gnu
release: 1.95.0-nightly
LLVM version: 22.1.0
EOF
})"
expected_cargo="$({
  cat <<'EOF'
cargo 1.95.0-nightly (fe2f314ae 2026-01-30)
release: 1.95.0-nightly
commit-hash: fe2f314aef06e688a9517da1ac0577bb1854d01f
commit-date: 2026-01-30
host: x86_64-unknown-linux-gnu
libgit2: 1.9.2 (sys:0.20.3 vendored)
libcurl: 8.15.0-DEV (sys:0.4.83+curl-8.15.0 vendored ssl:OpenSSL/3.5.4)
ssl: OpenSSL 3.5.4 30 Sep 2025
os: Ubuntu 24.4.0 (noble) [64-bit]
EOF
})"

gate_parent="$(mktemp -d "${TMPDIR:-/tmp}/legitimacy-selected-authority-script.XXXXXXXXXX")"
chmod 700 "$gate_parent"
execution_parent=
execution_identity=
supervisor_pid=

locate_execution_parent() {
  local candidate
  [[ -n "$execution_identity" && -d "$gate_parent" ]] || return 1
  for candidate in "$gate_parent"/*; do
    [[ -e "$candidate" ]] || continue
    if [[ "$(file_identity "$candidate" 2>/dev/null || true)" == "$execution_identity" ]]; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done
  return 1
}

remove_exact_tree() {
  local path=$1
  [[ -e "$path" ]] || return 0
  rm -rf -- "$path" || return 1
  [[ ! -e "$path" ]]
}

cleanup() {
  local status=$?
  local watchdog=
  local located=
  trap - EXIT INT TERM HUP
  if [[ -n "$supervisor_pid" ]]; then
    kill -TERM "$supervisor_pid" 2>/dev/null || true
    (sleep 14; kill -KILL "$supervisor_pid" 2>/dev/null || true) &
    watchdog=$!
    if ! wait "$supervisor_pid" 2>/dev/null; then
      status=1
    fi
    kill "$watchdog" 2>/dev/null || true
    wait "$watchdog" 2>/dev/null || true
    echo "ERROR: selected-authority supervisor interrupted; cleanup status is non-success" >&2
  fi
  if [[ -n "$execution_parent" ]]; then
    located="$(locate_execution_parent || true)"
    if [[ -z "$located" ]] || ! remove_exact_tree "$located"; then
      echo "ERROR: selected-authority execution scratch cleanup failed" >&2
      status=1
    fi
  fi
  if ! remove_exact_tree "$gate_parent"; then
    echo "ERROR: selected-authority gate scratch cleanup failed" >&2
    status=1
  fi
  if ! bash "$repository_state_check" "$ROOT" "$initial_head" "$initial_tree" >/dev/null 2>&1; then
    echo "ERROR: selected-authority repository changed during gate" >&2
    status=1
  fi
  exit "$status"
}
trap cleanup EXIT INT TERM HUP

run_bounded() {
  local timeout_ms=$1
  local stdout_cap=$2
  local stderr_cap=$3
  local stdout_path=$4
  local stderr_path=$5
  local status_path=$6
  local child_status=0
  local command_path=
  local command_exec=
  local command_identity=
  local command_sha256=
  local command_fd=
  shift 6
  command_path=$1
  shift
  [[ "$command_path" == /* && -f "$command_path" && -x "$command_path" ]] \
    || fail "bounded command is not an absolute regular executable"
  command_identity="$(file_identity "$command_path")"
  command_sha256="$(file_sha256 "$command_path")"
  if [[ -L "$command_path" ]]; then
    command_exec="$command_path"
  else
    exec {command_fd}<"$command_path"
    command_exec="/proc/self/fd/$command_fd"
  fi
  [[ ! -e "$stdout_path" && ! -e "$stderr_path" && ! -e "$status_path" ]] \
    || fail "process supervisor output collision"
  [[ "$(file_identity "$python_path")" == "$python_identity" ]] \
    || fail "Python identity changed before supervised execution"
  [[ "$(file_sha256 "$python_path")" == "$python_sha256" ]] \
    || fail "Python bytes changed before supervised execution"
  [[ "$(file_identity "$process_supervisor")" == "$supervisor_identity" ]] \
    || fail "process supervisor identity changed before execution"
  [[ "$(file_sha256 "$process_supervisor")" == "$supervisor_sha256" ]] \
    || fail "process supervisor bytes changed before execution"
  [[ "$(file_identity "$test_binary_selector")" == "$selector_identity" \
      && "$(file_sha256 "$test_binary_selector")" == "$selector_sha256" ]] \
    || fail "test-binary selector changed before supervised execution"
  "$python_exec" "$supervisor_exec" \
    --timeout-ms "$timeout_ms" \
    --term-grace-ms 2000 \
    --stdout-cap "$stdout_cap" \
    --stderr-cap "$stderr_cap" \
    --stdout "$stdout_path" \
    --stderr "$stderr_path" \
    --status "$status_path" \
    -- "$command_exec" "$@" &
  supervisor_pid=$!
  wait "$supervisor_pid" || child_status=$?
  supervisor_pid=
  if [[ -n "$command_fd" ]]; then
    exec {command_fd}>&-
  fi
  [[ -f "$status_path" && ! -L "$status_path" ]] \
    || fail "process supervisor omitted status"
  [[ "$(stat -Lc '%a' "$stdout_path")" == 600 && "$(stat -Lc '%a' "$stderr_path")" == 600 \
      && "$(stat -Lc '%a' "$status_path")" == 600 ]] \
    || fail "process supervisor output mode"
  grep -qx 'group_absent=1' "$status_path" \
    || fail "process supervisor left a live process group"
  grep -qx 'descendants_absent=1' "$status_path" \
    || fail "process supervisor left a live descendant"
  grep -qx 'stdout_eof=1' "$status_path" \
    || fail "process supervisor did not drain stdout"
  grep -qx 'stderr_eof=1' "$status_path" \
    || fail "process supervisor did not drain stderr"
  grep -qx 'cleanup_error=' "$status_path" \
    || fail "process supervisor cleanup failure"
  [[ "$(file_identity "$python_path")" == "$python_identity" \
      && "$(file_sha256 "$python_path")" == "$python_sha256" ]] \
    || fail "Python changed during supervised execution"
  [[ "$(file_identity "$process_supervisor")" == "$supervisor_identity" \
      && "$(file_sha256 "$process_supervisor")" == "$supervisor_sha256" ]] \
    || fail "process supervisor changed during execution"
  [[ "$(file_identity "$test_binary_selector")" == "$selector_identity" \
      && "$(file_sha256 "$test_binary_selector")" == "$selector_sha256" ]] \
    || fail "test-binary selector changed during supervised execution"
  [[ "$(file_identity "$command_path")" == "$command_identity" \
      && "$(file_sha256 "$command_path")" == "$command_sha256" ]] \
    || fail "bounded command changed during execution"
  return "$child_status"
}

run_expected_success() {
  if ! run_bounded "$@"; then
    fail "bounded child did not complete cleanly"
  fi
  local status_path=$6
  grep -qx 'outcome=success' "$status_path" \
    || fail "bounded child outcome was not clean success"
}

run_without_selected_environment() {
  local result=0
  local suite_parent_set=${LEGITIMACY_SELECTED_AUTHORITY_SUITE_PARENT+x}
  local suite_parent_value=${LEGITIMACY_SELECTED_AUTHORITY_SUITE_PARENT-}
  local manifest_path_set=${LEGITIMACY_SELECTED_AUTHORITY_CASE_MANIFEST_PATH+x}
  local manifest_path_value=${LEGITIMACY_SELECTED_AUTHORITY_CASE_MANIFEST_PATH-}
  local result_path_set=${LEGITIMACY_SELECTED_AUTHORITY_RESULT_PATH+x}
  local result_path_value=${LEGITIMACY_SELECTED_AUTHORITY_RESULT_PATH-}
  unset LEGITIMACY_SELECTED_AUTHORITY_SUITE_PARENT
  unset LEGITIMACY_SELECTED_AUTHORITY_CASE_MANIFEST_PATH
  unset LEGITIMACY_SELECTED_AUTHORITY_RESULT_PATH
  run_bounded "$@" || result=$?
  if [[ -n "$suite_parent_set" ]]; then export LEGITIMACY_SELECTED_AUTHORITY_SUITE_PARENT="$suite_parent_value"; fi
  if [[ -n "$manifest_path_set" ]]; then export LEGITIMACY_SELECTED_AUTHORITY_CASE_MANIFEST_PATH="$manifest_path_value"; fi
  if [[ -n "$result_path_set" ]]; then export LEGITIMACY_SELECTED_AUTHORITY_RESULT_PATH="$result_path_value"; fi
  return "$result"
}

active_rustc_stdout="$gate_parent/active-rustc.stdout"
active_rustc_stderr="$gate_parent/active-rustc.stderr"
run_expected_success 10000 1048576 1048576 \
  "$active_rustc_stdout" "$active_rustc_stderr" "$gate_parent/active-rustc.status" \
  "$rustc_command" -vV
[[ ! -s "$active_rustc_stderr" && "$(<"$active_rustc_stdout")" == "$expected_rustc" ]] \
  || fail "unsupported active rustc identity"

active_cargo_stdout="$gate_parent/active-cargo.stdout"
active_cargo_stderr="$gate_parent/active-cargo.stderr"
run_expected_success 10000 1048576 1048576 \
  "$active_cargo_stdout" "$active_cargo_stderr" "$gate_parent/active-cargo.status" \
  "$cargo_command" -vV
[[ ! -s "$active_cargo_stderr" && "$(<"$active_cargo_stdout")" == "$expected_cargo" ]] \
  || fail "unsupported active Cargo identity"
[[ "$(file_identity "$active_rustc_path")" == "$active_rustc_identity" \
    && "$(file_sha256 "$active_rustc_path")" == "$active_rustc_sha256" \
    && "$(file_identity "$active_cargo_path")" == "$active_cargo_identity" \
    && "$(file_sha256 "$active_cargo_path")" == "$active_cargo_sha256" ]] \
  || fail "active Rust launcher bytes changed"

sysroot_stdout="$gate_parent/sysroot.stdout"
run_expected_success 10000 1048576 1048576 \
  "$sysroot_stdout" "$gate_parent/sysroot.stderr" "$gate_parent/sysroot.status" \
  "$rustc_command" --print sysroot
[[ ! -s "$gate_parent/sysroot.stderr" ]] || fail "rustc sysroot wrote stderr"
selected_sysroot="$(<"$sysroot_stdout")"
[[ "$selected_sysroot" == /* && ! "$selected_sysroot" =~ [[:space:]] ]] \
  || fail "invalid rustc sysroot"
rustc_path="$(readlink -f "$selected_sysroot/bin/rustc")"
cargo_path="$(readlink -f "$selected_sysroot/bin/cargo")"
[[ -f "$rustc_path" && -x "$rustc_path" ]] || fail "resolved rustc is not a regular executable"
[[ -f "$cargo_path" && -x "$cargo_path" ]] || fail "resolved Cargo is not a regular executable"
rustc_identity="$(file_identity "$rustc_path")"
rustc_sha256="$(file_sha256 "$rustc_path")"
cargo_identity="$(file_identity "$cargo_path")"
cargo_sha256="$(file_sha256 "$cargo_path")"
[[ "$rustc_sha256" == "$expected_rustc_sha256" ]] \
  || fail "unsupported rustc executable bytes"
[[ "$cargo_sha256" == "$expected_cargo_sha256" ]] \
  || fail "unsupported Cargo executable bytes"

resolved_rustc_stdout="$gate_parent/resolved-rustc.stdout"
run_expected_success 10000 1048576 1048576 \
  "$resolved_rustc_stdout" "$gate_parent/resolved-rustc.stderr" "$gate_parent/resolved-rustc.status" \
  "$rustc_path" -vV
[[ ! -s "$gate_parent/resolved-rustc.stderr" \
    && "$(<"$resolved_rustc_stdout")" == "$expected_rustc" ]] \
  || fail "unsupported complete rustc identity"

resolved_cargo_stdout="$gate_parent/resolved-cargo.stdout"
run_expected_success 10000 1048576 1048576 \
  "$resolved_cargo_stdout" "$gate_parent/resolved-cargo.stderr" "$gate_parent/resolved-cargo.status" \
  "$cargo_path" -vV
[[ ! -s "$gate_parent/resolved-cargo.stderr" \
    && "$(<"$resolved_cargo_stdout")" == "$expected_cargo" ]] \
  || fail "unsupported complete Cargo identity"
[[ "$(file_identity "$rustc_path")" == "$rustc_identity" \
    && "$(file_sha256 "$rustc_path")" == "$rustc_sha256" \
    && "$(file_identity "$cargo_path")" == "$cargo_identity" \
    && "$(file_sha256 "$cargo_path")" == "$cargo_sha256" ]] \
  || fail "resolved Rust tool bytes changed during identity checks"

build_stdout="$gate_parent/build.stdout"
build_stderr="$gate_parent/build.stderr"
if run_without_selected_environment 900000 67108864 67108864 \
  "$build_stdout" "$build_stderr" "$gate_parent/build.status" \
  "$cargo_path" test --locked --test codex_exec_v0 --no-run \
    --message-format=json-render-diagnostics; then
  build_status=0
else
  build_status=$?
fi
cat "$build_stderr" >&2
[[ "$build_status" -eq 0 ]] || fail "selected-authority test build failed"
grep -qx 'outcome=success' "$gate_parent/build.status" \
  || fail "selected-authority test build was not clean success"

discovery_stdout="$gate_parent/discovery.stdout"
run_expected_success 10000 1048576 1048576 \
  "$discovery_stdout" "$gate_parent/discovery.stderr" "$gate_parent/discovery.status" \
  "$python_path" "$selector_exec" "$build_stdout"
[[ ! -s "$gate_parent/discovery.stderr" ]] \
  || fail "selected-authority exact test binary discovery wrote stderr"
test_binary="$(<"$discovery_stdout")"
[[ "$test_binary" == /* && -f "$test_binary" && -x "$test_binary" && ! -L "$test_binary" ]] \
  || fail "selected-authority discovered binary is not an exact regular executable"
[[ "$(readlink -f "$test_binary")" == "$test_binary" ]] \
  || fail "selected-authority discovered binary path is not canonical"
binary_identity="$(file_identity "$test_binary")"
binary_sha256="$(file_sha256 "$test_binary")"

enumeration_stdout="$gate_parent/enumeration.stdout"
enumeration_stderr="$gate_parent/enumeration.stderr"
run_without_selected_environment 30000 1048576 1048576 \
  "$enumeration_stdout" "$enumeration_stderr" "$gate_parent/enumeration.status" \
  "$test_binary" "$selected_test" --exact --ignored --list --format terse
grep -qx 'outcome=success' "$gate_parent/enumeration.status" \
  || fail "selected-authority enumeration was not clean success"
[[ ! -s "$enumeration_stderr" ]] || fail "selected-authority enumeration wrote stderr"
expected_enumeration="$gate_parent/expected-enumeration.stdout"
printf '%s: test\n' "$selected_test" >"$expected_enumeration"
cmp -s "$expected_enumeration" "$enumeration_stdout" \
  || fail "selected-authority exact enumeration mismatch"

zero_stdout="$gate_parent/zero.stdout"
zero_stderr="$gate_parent/zero.stderr"
run_without_selected_environment 30000 1048576 1048576 \
  "$zero_stdout" "$zero_stderr" "$gate_parent/zero.status" \
  "$test_binary" __definitely_missing_selected_authority_test__ \
    --exact --ignored --list --format terse
grep -qx 'outcome=success' "$gate_parent/zero.status" \
  || fail "selected-authority zero-test control was not clean success"
[[ ! -s "$zero_stdout" && ! -s "$zero_stderr" ]] \
  || fail "selected-authority zero-test negative control did not enumerate zero"
! cmp -s "$expected_enumeration" "$zero_stdout" \
  || fail "selected-authority zero-test negative control reached completion"

[[ "$(file_identity "$test_binary")" == "$binary_identity" \
    && "$(file_sha256 "$test_binary")" == "$binary_sha256" ]] \
  || fail "selected-authority test binary changed after enumeration"

execution_parent="$gate_parent/execution"
mkdir "$execution_parent"
chmod 700 "$execution_parent"
execution_identity="$(file_identity "$execution_parent")"
case_manifest="$execution_parent/case-manifest.v1"
execution_stdout="$execution_parent/execution.stdout"
execution_stderr="$execution_parent/execution.stderr"

printf '%s' 'forged' >"$case_manifest"
if LEGITIMACY_SELECTED_AUTHORITY_SUITE_PARENT="$execution_parent" \
  LEGITIMACY_SELECTED_AUTHORITY_CASE_MANIFEST_PATH="$case_manifest" \
  LEGITIMACY_SELECTED_AUTHORITY_CARGO="$cargo_path" \
  LEGITIMACY_SELECTED_AUTHORITY_RUSTC="$rustc_path" \
  LEGITIMACY_SELECTED_AUTHORITY_PYTHON="$python_path" \
  LEGITIMACY_SELECTED_AUTHORITY_PROCESS_SUPERVISOR="$process_supervisor" \
  LEGITIMACY_SELECTED_AUTHORITY_REPOSITORY_HEAD="$initial_head" \
  LEGITIMACY_SELECTED_AUTHORITY_REPOSITORY_TREE="$initial_tree" \
  run_bounded 60000 1048576 1048576 \
  "$execution_parent/forged.stdout" "$execution_parent/forged.stderr" \
  "$execution_parent/forged.status" \
  "$test_binary" "$selected_test" --exact --ignored --test-threads=1; then
  forged_status=0
else
  forged_status=$?
fi
[[ "$forged_status" -ne 0 ]] \
  || fail "selected-authority forged-manifest negative control passed"
grep -qx 'outcome=nonzero-exit' "$execution_parent/forged.status" \
  || fail "selected-authority forged-manifest control did not fail normally"
[[ "$(<"$case_manifest")" == forged ]] \
  || fail "selected-authority forged-manifest negative control was replaced"
rm -f -- "$case_manifest"
[[ ! -e "$case_manifest" ]] || fail "selected-authority forged manifest was not removed"

if LEGITIMACY_SELECTED_AUTHORITY_SUITE_PARENT="$execution_parent" \
  LEGITIMACY_SELECTED_AUTHORITY_CASE_MANIFEST_PATH="$case_manifest" \
  LEGITIMACY_SELECTED_AUTHORITY_CARGO="$cargo_path" \
  LEGITIMACY_SELECTED_AUTHORITY_RUSTC="$rustc_path" \
  LEGITIMACY_SELECTED_AUTHORITY_PYTHON="$python_path" \
  LEGITIMACY_SELECTED_AUTHORITY_PROCESS_SUPERVISOR="$process_supervisor" \
  LEGITIMACY_SELECTED_AUTHORITY_REPOSITORY_HEAD="$initial_head" \
  LEGITIMACY_SELECTED_AUTHORITY_REPOSITORY_TREE="$initial_tree" \
  run_bounded 1900000 67108864 67108864 \
  "$execution_stdout" "$execution_stderr" "$execution_parent/execution.status" \
  "$test_binary" "$selected_test" --exact --ignored --test-threads=1; then
  execution_status=0
else
  execution_status=$?
fi
cat "$execution_stdout"
cat "$execution_stderr" >&2
[[ "$execution_status" -eq 0 ]] || fail "selected-authority ignored test failed"
grep -qx 'outcome=success' "$execution_parent/execution.status" \
  || fail "selected-authority ignored test was not clean success"
[[ ! -s "$execution_stderr" ]] || fail "selected-authority ignored test wrote stderr"

nonempty_execution="$execution_parent/execution.nonempty"
sed '/^$/d' "$execution_stdout" >"$nonempty_execution"
[[ "$(wc -l <"$nonempty_execution" | tr -d ' ')" == 3 ]] \
  || fail "selected-authority execution output line count mismatch"
[[ "$(sed -n '1p' "$nonempty_execution")" == 'running 1 test' ]] \
  || fail "selected-authority execution did not report one running test"
[[ "$(sed -n '2p' "$nonempty_execution")" == "test $selected_test ... ok" ]] \
  || fail "selected-authority exact selected test did not pass"
grep -Eq '^test result: ok\. 1 passed; 0 failed; 0 ignored; 0 measured; [0-9]+ filtered out; finished in [0-9.]+s$' \
  "$nonempty_execution" || fail "selected-authority execution summary mismatch"

expected_manifest="$execution_parent/expected-case-manifest.v1"
source_manifest_sha256="$(sed -n 's/^source_manifest_sha256[[:space:]]//p' "$case_manifest")"
[[ "$source_manifest_sha256" =~ ^[0-9a-f]{64}$ ]] \
  || fail "selected-authority source manifest digest"
printf '%s\n' \
  'legitimacy.selected-authority-case-manifest.v1' \
  "repository_head${TAB:-	}$initial_head" \
  "repository_tree${TAB:-	}$initial_tree" \
  "source_manifest_sha256${TAB:-	}$source_manifest_sha256" \
  "rustc_sha256${TAB:-	}$rustc_sha256" \
  "cargo_sha256${TAB:-	}$cargo_sha256" \
  'baseline_selected_closure	1' \
  'macro_generated_non_rs_overlap	1' \
  'benign_direct_non_rs_overlap	1' \
  'frozen_manual_sibling_escape	1' \
  'inactive_duplicate_owner	1' \
  'zero_candidate_fallback_owner	1' \
  'active_linux_duplicate_owner	1' \
  'recognized_false_duplicate_owner	1' \
  'unrecognized_cfg_owner	1' \
  'independent_binary_cfg	1' \
  'clean_owner_relocation	1' \
  'borrowed_owner_relocation	1' \
  'complete	12' >"$expected_manifest"
cmp -s "$expected_manifest" "$case_manifest" \
  || fail "selected-authority case manifest mismatch"
[[ "$(file_identity "$test_binary")" == "$binary_identity" \
    && "$(file_sha256 "$test_binary")" == "$binary_sha256" ]] \
  || fail "selected-authority test binary changed after execution"

outer_witness="$(mktemp "$execution_parent/outer-execution-witness.XXXXXXXX")"
chmod 600 "$outer_witness"
printf '%s\n' \
  'legitimacy.selected-authority-outer-execution-witness.v1' \
  "repository_head=$initial_head" \
  "repository_tree=$initial_tree" \
  "source_manifest_sha256=$source_manifest_sha256" \
  "active_rustc_sha256=$active_rustc_sha256" \
  "active_cargo_sha256=$active_cargo_sha256" \
  "rustc_sha256=$rustc_sha256" \
  "cargo_sha256=$cargo_sha256" \
  "binary_sha256=$binary_sha256" \
  "enumeration_sha256=$(file_sha256 "$enumeration_stdout")" \
  "execution_sha256=$(file_sha256 "$execution_stdout")" \
  "case_manifest_sha256=$(file_sha256 "$case_manifest")" \
  >"$outer_witness"
sync -f "$outer_witness"
[[ -s "$outer_witness" ]] || fail "selected-authority outer witness was not published"

[[ "$(git -C "$ROOT" rev-parse HEAD)" == "$initial_head" \
    && "$(git -C "$ROOT" rev-parse HEAD^{tree})" == "$initial_tree" ]] \
  || fail "selected-authority repository identity changed"
require_clean_repository
[[ "$(file_identity "$rustc_path")" == "$rustc_identity" \
    && "$(file_sha256 "$rustc_path")" == "$rustc_sha256" \
    && "$(file_identity "$cargo_path")" == "$cargo_identity" \
    && "$(file_sha256 "$cargo_path")" == "$cargo_sha256" ]] \
  || fail "resolved Rust tool bytes changed during gate"

echo "selected-authority release gate: OK"
