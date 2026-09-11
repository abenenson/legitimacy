#!/usr/bin/env python3
"""Select the one exact codex_exec_v0 test executable from Cargo JSON lines."""

import json
import pathlib
import sys


def main() -> int:
    if len(sys.argv) != 2:
        return 2
    artifacts = []
    for line in pathlib.Path(sys.argv[1]).read_text(encoding="utf-8").splitlines():
        value = json.loads(line)
        target = value.get("target", {})
        if (
            value.get("reason") == "compiler-artifact"
            and target.get("name") == "codex_exec_v0"
            and target.get("kind") == ["test"]
            and value.get("profile", {}).get("test") is True
            and isinstance(value.get("executable"), str)
        ):
            artifacts.append(value["executable"])
    if len(artifacts) != 1:
        return 1
    print(artifacts[0])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
