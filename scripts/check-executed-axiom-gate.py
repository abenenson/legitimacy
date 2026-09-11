#!/usr/bin/env python3
"""Exercise module-wide axiom checking against compilable proof mutations."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "lean"
MODULE = Path("Legitimacy/Protocol/ExecutedComposition.lean")
CHECKER = LEAN_ROOT / "scripts/CheckExecutedAxioms.lean"


def command(args, env=None):
    result = subprocess.run(args, cwd=LEAN_ROOT, env=env, text=True,
                            capture_output=True, timeout=120)
    return result, result.stdout + result.stderr


def main():
    source = (LEAN_ROOT / MODULE).read_text()
    result, output = command(["lake", "env", "printenv", "LEAN_PATH"])
    if result.returncode:
        raise RuntimeError(output)
    base_path = result.stdout.strip()
    start = source.index("theorem equal_length_action_control")
    end = source.index("theorem useful_repair", start)
    segment = source[start:end]
    if "by decide" not in segment:
        raise RuntimeError("omitted-root mutation no longer matches the source")
    cases = [
        ("new-clean-theorem", source + "\ntheorem auditGateClean : True := True.intro\n", None),
        ("new-clean-proof-definition", source +
         "\ndef auditGateCleanDef : True := True.intro\n", None),
        ("new-clean-opaque-proof", source +
         "\nopaque auditGateCleanOpaque : True := True.intro\n", None),
        ("proof-valued-definition", source +
         "\ndef auditGateProofAsDef : False := sorryAx False true\n", ("disallowed axiom sorryAx",)),
        ("opaque-proof", source +
         "\nopaque auditGateOpaqueProof : False := sorryAx False true\n", ("disallowed axiom sorryAx",)),
        ("formerly-omitted-root", source[:start] + segment.replace(
            "by decide", "by native_decide", 1) + source[end:], ("disallowed axiom", "declares an axiom")),
        ("new-private-outside-namespace", source +
         "\nprivate theorem auditGateNative : (1 : Nat) = 1 := by native_decide\n", ("disallowed axiom", "declares an axiom")),
        ("unused-axiom", source + "\naxiom auditGateUnused : True\n", ("declares an axiom",)),
    ]
    for name, changed, rejection in cases:
        with tempfile.TemporaryDirectory(prefix="executed-axiom-gate-") as directory:
            scratch = Path(directory)
            # Lean resolves a package from one search root. Populate sibling
            # imports with links so only this module is replaced by the probe.
            built = LEAN_ROOT / ".lake/build/lib/lean/Legitimacy"
            package = scratch / "Legitimacy"
            package.mkdir()
            for entry in built.iterdir():
                if entry.name != "Protocol":
                    (package / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
            protocol = package / "Protocol"
            protocol.mkdir()
            for entry in (built / "Protocol").iterdir():
                if not entry.name.startswith("ExecutedComposition."):
                    (protocol / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
            path = scratch / MODULE
            path.write_text(changed)
            result, output = command(["lake", "env", "lean", "-R", str(scratch),
                                      "-o", str(path.with_suffix(".olean")), str(path)])
            if result.returncode:
                raise RuntimeError(f"{name}: mutation must compile before testing the gate\n{output}")
            compile_output = output.strip()
            environment = dict(os.environ, LEAN_PATH=str(scratch) + ":" + base_path,
                               LEAN_NUM_THREADS="2")
            result, output = command(["lean", "-DwarningAsError=true", str(CHECKER)], environment)
            if rejection is None:
                if result.returncode or not re.search(r"footprints: [1-9][0-9]* module theorems", output):
                    raise RuntimeError(f"{name}: clean extension rejected\n{output}")
            elif result.returncode == 0 or not any(message in output for message in rejection):
                raise RuntimeError(f"{name}: expected rejection {rejection!r}\n{output}")
            print(json.dumps({"case": name, "compiled": True,
                              "source_sha256": hashlib.sha256(changed.encode()).hexdigest(),
                              "compiler_output": compile_output,
                              "checker_exit": result.returncode, "output": output.strip()}), flush=True)


if __name__ == "__main__":
    main()
