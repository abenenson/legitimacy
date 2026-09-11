#!/usr/bin/env bash
set -euo pipefail

[[ $# -eq 3 ]] || exit 2
root=$1
expected_head=$2
expected_tree=$3

[[ "$root" == /* && "$(git -C "$root" rev-parse --show-toplevel)" == "$root" ]]
[[ "$(git -C "$root" rev-parse HEAD)" == "$expected_head" ]]
[[ "$(git -C "$root" rev-parse HEAD^{tree})" == "$expected_tree" ]]
[[ "$(git -C "$root" write-tree)" == "$expected_tree" ]]
[[ -z "$(git -C "$root" status --porcelain=v1 --untracked-files=all)" ]]

printf '%s\n%s\n' "$expected_head" "$expected_tree"
