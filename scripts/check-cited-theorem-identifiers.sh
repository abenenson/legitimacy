#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

python3 - "$ROOT" <<'PY'
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
decl_re = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
ctor_re = re.compile(r"^\s*\|\s+([A-Za-z_][A-Za-z0-9_']*)\b")
ident_re = re.compile(r"`([A-Za-z_][A-Za-z0-9_']*)`")
lean_ident_re = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.]*)`")

lean_files = list((root / "lean").rglob("*.lean"))
lean_files.extend((root / "audits" / "corpus").glob("*/theorem/*.lean"))

decls = set()
def add_decl(name):
    parts = name.split(".")
    for idx in range(len(parts)):
        decls.add(".".join(parts[idx:]))

for path in lean_files:
    for line in path.read_text(encoding="utf-8").splitlines():
        match = decl_re.match(line)
        if match:
            add_decl(match.group(1))
            continue
        match = ctor_re.match(line)
        if match:
            add_decl(match.group(1))

citations = []

def citation_name(ident):
    return ident

def add_citation(path, lineno, ident):
    citations.append((path, lineno, ident, citation_name(ident)))

def add_lean_citations_from_text(path, lineno, text):
    # Some paper tables use `foo_`\linebreak`bar` to wrap long identifiers.
    text = re.sub(
        r"`([A-Za-z_][A-Za-z0-9_']*)`\\linebreak`([A-Za-z_][A-Za-z0-9_']*)`",
        r"`\1\2`",
        text,
    )
    for ident in lean_ident_re.findall(text):
        add_citation(path, lineno, ident)

readme = root / "README.md"
readme_lines = readme.read_text(encoding="utf-8").splitlines()
capture_table = False
for lineno, line in enumerate(readme_lines, start=1):
    if "Lean witness" in line or "Spine theorem" in line:
        capture_table = True
    elif capture_table and line and not line.startswith("|"):
        capture_table = False
    if capture_table or "Lean theorem" in line:
        for ident in ident_re.findall(line):
            add_citation(readme, lineno, ident)

leaderboard = root / "audits" / "leaderboard" / "LEADERBOARD.md"
leaderboard_lines = leaderboard.read_text(encoding="utf-8").splitlines()
capture_section = False
for lineno, line in enumerate(leaderboard_lines, start=1):
    if line.startswith("## Per-Harness Lean Theorem Citations"):
        capture_section = True
        continue
    if capture_section and line.startswith("## "):
        capture_section = False
    if capture_section and line.startswith("|"):
        for ident in ident_re.findall(line):
            if ident.startswith("Legitimacy"):
                continue
            add_citation(leaderboard, lineno, ident)

for paper in sorted((root / "papers").glob("*.md")):
    paper_lines = paper.read_text(encoding="utf-8").splitlines()
    table_lean_columns = None
    for lineno, line in enumerate(paper_lines, start=1):
        if line.startswith("|") and "Lean identifier" in line:
            cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
            table_lean_columns = [
                idx for idx, cell in enumerate(cells)
                if "Lean identifier" in cell or "Formal anchor" in cell
            ]
            continue
        if table_lean_columns is not None:
            if not line.startswith("|"):
                table_lean_columns = None
            elif not re.match(r"^\|\s*:?-{3,}:?\s*(\|\s*:?-{3,}:?\s*)+\|?$", line):
                cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
                for idx in table_lean_columns:
                    if idx < len(cells):
                        add_lean_citations_from_text(paper, lineno, cells[idx])

        if "Lean identifiers:" in line:
            text = line.split("Lean identifiers:", 1)[1]
            text = text.split("Modules:", 1)[0]
            text = text.split("Rust mirror:", 1)[0]
            text = text.split(" in `", 1)[0]
            add_lean_citations_from_text(paper, lineno, text)
        elif "Lean identifier:" in line:
            text = line.split("Lean identifier:", 1)[1]
            text = text.split("Modules:", 1)[0]
            add_lean_citations_from_text(paper, lineno, text)
        elif "Lean:" in line:
            text = line.split("Lean:", 1)[1]
            match = lean_ident_re.search(text)
            if match:
                add_citation(paper, lineno, match.group(1))

missing = [
    (path, lineno, ident)
    for path, lineno, ident, name in citations
    if name not in decls and ident.split(".")[-1] not in decls
    and ident not in {"Set.univ", "True", "False", "Equiv"}
]

if missing:
    for path, lineno, ident in missing:
        rel = path.relative_to(root)
        print(f"ERROR: cited Lean identifier `{ident}` is not declared ({rel}:{lineno})", file=sys.stderr)
    raise SystemExit(1)

print("cited theorem identifiers: OK")
PY
