#!/usr/bin/env bash
# Credential-free supplied-bundle path. Does not invoke Cargo, Lean, or a network.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
(cd "$ROOT" && sha256sum --check --status SHA256SUMS)
python3 - "$ROOT" <<'PY'
import hashlib, json, pathlib, subprocess, sys, time
root = pathlib.Path(sys.argv[1])
start = time.monotonic()
checker = str(root / "legitimacy-executed-composition")
provenance = json.loads((root / "BUILD_PROVENANCE.json").read_text())
assert provenance["checkout_commit"] == (root / "SOURCE_COMMIT").read_text().strip()
assert provenance["source_tree"] == (root / "SOURCE_TREE").read_text().strip()
assert provenance["packaged_binary_sha256"] == hashlib.sha256(pathlib.Path(checker).read_bytes()).hexdigest()
actual = json.loads(subprocess.check_output([checker, "check", str(root / "capture/bundle.json"), "--trust", str(root / "capture/trust-policy.json")]))
expected = json.loads((root / "capture/reports.json").read_text())
assert actual == expected, "independent checker disagrees with supplied results"
assert all(r["capture_authenticated"] for r in actual)
assert actual[0]["knowledge"] == "Violated" and actual[0]["per_call_baseline"] == "Permit"
assert all(actual[i]["governance"] == "Permit" for i in [1, 3, 4])
assert actual[5]["governance"] == "Deny"
assert actual[6]["knowledge"] == "Inconclusive"
fresh = json.loads(subprocess.check_output([checker, "demo"]))
assert [(r["knowledge"], r["governance"]) for r in fresh] == [(r["knowledge"], r["governance"]) for r in actual]
for r in actual:
    print(f'{r["id"]}: {r["knowledge"]} / {r["governance"]}')
print(f'PASS: signed replay, effects, same-property repair, and fresh host execution ({time.monotonic()-start:.3f}s)')
print('Open reader.html locally to inspect actions and challenge the evidence.')
PY
