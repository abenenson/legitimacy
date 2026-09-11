#!/usr/bin/env python3
"""Refresh only the digest of already declared selected build inputs.

Does not discover, admit, or remove source paths. Changes to the canonical
source/target inventory must be reviewed explicitly; the existing tests compare
it with actual compiler dependency information and reject omissions.
"""
import hashlib
import json
import struct
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
path = ROOT / "tests/fixtures/codex-exec-v0/adapter-build-input.json"
data = json.loads(path.read_text())
contract = data["cargo_contract"]
paths = []
for role in ["binary", "library"]:
    paths.extend(contract["compiler_read_inputs"][role])
for role in ["cargo", "build_script", "review_contract"]:
    paths.extend(contract["selected_noncompiler_inputs"][role])
paths.extend(contract["repository_configuration"]["present"])
def frame(b): return struct.pack(">Q", len(b)) + b
components = [part for p in paths for part in [p.encode(), (ROOT / p).read_bytes()]]
body = b"legitimacy.trajectory.hash.v0\0" + frame(b"legitimacy.codex-exec-v0.selected-build-inputs.v0")
body += struct.pack(">Q", len(components)) + b"".join(frame(b) for b in components)
contract["bound_inputs_sha256"] = "sha256:" + hashlib.sha256(body).hexdigest()
path.write_text(json.dumps(data, indent=2) + "\n")
print(contract["bound_inputs_sha256"])
