#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"

python3 - "$ROOT" <<'PY'
from pathlib import Path
import re
import sys

root = Path(sys.argv[1]).resolve()

docs = [
    root / "README.md",
    root / "audits/leaderboard/LEADERBOARD.md",
]
docs.extend(sorted((root / "papers").glob("*.md")))

for doc in docs:
    if not doc.is_file():
        print(f"ERROR: missing doc checked for rejection theorem claims: {doc}", file=sys.stderr)
        sys.exit(1)

declared_theorems = set()
decl_re = re.compile(r"^(?:theorem|lemma)\s+([A-Za-z0-9_']+)\b")
for lean_file in (root / "lean" / "Legitimacy").rglob("*.lean"):
    for line in lean_file.read_text(encoding="utf-8").splitlines():
        match = decl_re.match(line)
        if match:
            declared_theorems.add(match.group(1))

properties = [
    ("Consistency", r"consistency"),
    ("Solidarity", r"solidarity"),
    ("Monotonicity", r"monotonicity"),
    ("Strategyproofness", r"strategyproofness"),
    ("Certifiability", r"certifiability"),
    ("ObservableDeterminacy", r"observable[ -]?determinacy"),
    ("Corrigibility", r"corrigibility"),
    ("CompositionalSafety", r"compositional[ -]?safety"),
    ("Nonvacuity", r"non[- ]?vacuity"),
]

reject_word = r"(?:reject|rejects|rejected|rejection|rejections)"
window = r"[^`|;.?!]{0,120}"
code_span_re = re.compile(r"`([A-Za-z][A-Za-z0-9_']*)`")


def line_claims_property_rejection(text: str, term: str) -> bool:
    lower = text.lower()
    before = re.compile(rf"\b{reject_word}\b{window}\b{term}\b")
    after = re.compile(rf"\b{term}\b{window}\b{reject_word}\b")
    return before.search(lower) is not None or after.search(lower) is not None


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    sys.exit(1)


for doc in docs:
    for line_no, text in enumerate(doc.read_text(encoding="utf-8").splitlines(), start=1):
        if "reject" not in text.lower() and "Rejects" not in text:
            continue

        cited_rejections = [
            ident for ident in code_span_re.findall(text)
            if "Rejects" in ident or "CheckFails" in ident
        ]

        for ident in cited_rejections:
            if ident not in declared_theorems:
                fail(
                    f"{doc}:{line_no} cites rejection theorem '{ident}' "
                    "but no Lean theorem/lemma with that name exists"
                )

        for camel, term in properties:
            if not line_claims_property_rejection(text, term):
                continue

            expected = [f"Rejects{camel}"]
            if camel == "Nonvacuity":
                expected.append("NonvacuityCheckFails")
            if not any(
                expected_fragment in ident
                for ident in cited_rejections
                for expected_fragment in expected
            ):
                near = ", ".join(cited_rejections) if cited_rejections else "no cited rejection theorem"
                fail(
                    f"{doc}:{line_no} claims '{camel}' rejection near {near}, "
                    f"but no cited theorem contains one of {', '.join(expected)}"
                )

print("doc rejection theorem claims: OK")
PY
