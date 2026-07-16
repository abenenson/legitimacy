#!/usr/bin/env bash
set -euo pipefail

ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"

python3 - "$ROOT" <<'PY'
import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])

path_re = re.compile(r"(?:audits/leaderboard|examples/graphs)/[A-Za-z0-9_./-]+\.json")
number_words = {
    "zero": 0,
    "one": 1,
    "two": 2,
    "three": 3,
    "four": 4,
    "five": 5,
    "six": 6,
    "seven": 7,
    "eight": 8,
    "nine": 9,
    "ten": 10,
    "eleven": 11,
    "twelve": 12,
    "thirteen": 13,
    "fourteen": 14,
    "fifteen": 15,
    "sixteen": 16,
    "seventeen": 17,
    "eighteen": 18,
    "nineteen": 19,
    "twenty": 20,
    "thirty": 30,
    "forty": 40,
    "fifty": 50,
    "sixty": 60,
}
number_token = r"(?:\d+|" + "|".join(sorted(number_words, key=len, reverse=True)) + r")"
node_re = re.compile(rf"\b({number_token})[- ]+(?:[A-Za-z-]+[ -]+)?nodes?\b", re.IGNORECASE)
edge_re = re.compile(rf"\b({number_token})[- ]+(?:[A-Za-z-]+[ -]+)?edges?\b", re.IGNORECASE)


def parse_number(token: str) -> int:
    token = token.lower()
    if token.isdigit():
        return int(token)
    return number_words[token]


def graph_counts(path: str) -> tuple[int, int]:
    graph_path = root / path
    with graph_path.open(encoding="utf-8") as handle:
        graph = json.load(handle)
    return len(graph.get("nodes", [])), len(graph.get("edges", []))


def check_assignment(rel_file: Path, start: int, graph_path: str, cited_nodes, cited_edges) -> None:
    try:
        actual_nodes, actual_edges = graph_counts(graph_path)
    except FileNotFoundError:
        failures.append(f"{rel_file}:{start}: cited graph path does not exist: {graph_path}")
        return

    if cited_nodes is not None and cited_nodes != actual_nodes:
        failures.append(
            f"{rel_file}:{start}: {graph_path} cites {cited_nodes} nodes; "
            f"actual count is {actual_nodes}"
        )
    if cited_edges is not None and cited_edges != actual_edges:
        failures.append(
            f"{rel_file}:{start}: {graph_path} cites {cited_edges} edges; "
            f"actual count is {actual_edges}"
        )


def scan_files() -> list[Path]:
    files = [root / "README.md"]
    files.extend(sorted((root / "papers").glob("*.md")))
    for path in sorted((root / "lean").rglob("*.lean")):
        if ".lake" not in path.parts:
            files.append(path)
    return [path for path in files if path.exists()]


def paragraphs(path: Path):
    start = 1
    current: list[str] = []
    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line_paths = path_re.findall(line)
        line_node_counts = [parse_number(match.group(1)) for match in node_re.finditer(line)]
        line_edge_counts = [parse_number(match.group(1)) for match in edge_re.finditer(line)]
        if len(line_paths) == 1 and (line_node_counts or line_edge_counts):
            check_assignment(
                path.relative_to(root),
                lineno,
                line_paths[0],
                line_node_counts[0] if line_node_counts else None,
                line_edge_counts[0] if line_edge_counts else None,
            )
            line = ""

        if line.strip():
            current.append(line)
            continue
        if current:
            yield start, "\n".join(current)
            current = []
        start = lineno + 1
    if current:
        yield start, "\n".join(current)


failures: list[str] = []

for file_path in scan_files():
    rel_file = file_path.relative_to(root)
    for start, paragraph in paragraphs(file_path):
        paths = path_re.findall(paragraph)
        if not paths:
            continue
        node_counts = [parse_number(match.group(1)) for match in node_re.finditer(paragraph)]
        edge_counts = [parse_number(match.group(1)) for match in edge_re.finditer(paragraph)]
        if not node_counts and not edge_counts:
            continue

        if len(paths) == 1:
            assignments = [(paths[0], node_counts[0] if node_counts else None, edge_counts[0] if edge_counts else None)]
        elif len(paths) == len(node_counts) == len(edge_counts):
            assignments = list(zip(paths, node_counts, edge_counts))
        else:
            failures.append(
                f"{rel_file}:{start}: ambiguous JSON path/cardinality prose; "
                f"put each graph path and its node/edge counts in the same sentence"
            )
            continue

        for graph_path, cited_nodes, cited_edges in assignments:
            check_assignment(rel_file, start, graph_path, cited_nodes, cited_edges)

if failures:
    for failure in failures:
        print(failure, file=sys.stderr)
    print("ERROR: graph path/cardinality prose is stale", file=sys.stderr)
    sys.exit(1)

print("graph path/cardinality literals: OK")
PY
