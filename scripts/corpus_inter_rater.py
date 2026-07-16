#!/usr/bin/env python3
"""Compute corpus ground-truth inter-rater agreement.

Inputs are two reviewer `ground_truth.graph.toml` files following
audits/corpus/GROUND_TRUTH_PROTOCOL.md. Output is JSON with Cohen's kappa for
nodes, edges, and decisions.
"""

from __future__ import annotations

import argparse
import json
import sys
import tomllib
from pathlib import Path
from typing import Any


def load_toml(path: Path) -> dict[str, Any]:
    with path.open("rb") as handle:
        return tomllib.load(handle)


def as_list(document: dict[str, Any], key: str) -> list[dict[str, Any]]:
    value = document.get(key, [])
    if isinstance(value, list):
        return [item for item in value if isinstance(item, dict)]
    return []


def node_items(document: dict[str, Any]) -> set[str]:
    return {str(node["id"]) for node in as_list(document, "node") if "id" in node}


def edge_items(document: dict[str, Any]) -> set[str]:
    items: set[str] = set()
    for edge in as_list(document, "edge"):
        if "from" not in edge or "to" not in edge:
            continue
        kind = str(edge.get("kind", "edge"))
        items.add(f"{edge['from']} -> {edge['to']} [{kind}]")
    return items


def decision_items(document: dict[str, Any]) -> set[str]:
    items: set[str] = set()
    for decision in as_list(document, "decision"):
        if "node" not in decision or "predicate" not in decision or "decision" not in decision:
            continue
        items.add(
            f"{decision['node']} :: {decision['predicate']} => {decision['decision']}"
        )
    return items


def cohen_kappa(left: set[str], right: set[str]) -> dict[str, Any]:
    universe = sorted(left | right)
    if not universe:
        return {
            "kappa": 1.0,
            "observed_agreement": 1.0,
            "expected_agreement": 1.0,
            "items": 0,
            "agreements": 0,
            "disagreements": 0,
            "note": "both reviewers supplied the same empty label set",
        }

    both_present = len(left & right)
    left_only = len(left - right)
    right_only = len(right - left)
    total = len(universe)
    agreements = both_present
    disagreements = left_only + right_only
    observed = agreements / total

    left_present = (both_present + left_only) / total
    right_present = (both_present + right_only) / total
    left_absent = 1.0 - left_present
    right_absent = 1.0 - right_present
    expected = (left_present * right_present) + (left_absent * right_absent)

    if expected == 1.0:
        kappa = 1.0 if observed == 1.0 else 0.0
    else:
        kappa = (observed - expected) / (1.0 - expected)

    return {
        "kappa": round(kappa, 6),
        "observed_agreement": round(observed, 6),
        "expected_agreement": round(expected, 6),
        "items": total,
        "agreements": agreements,
        "disagreements": disagreements,
        "left_only": sorted(left - right),
        "right_only": sorted(right - left),
    }


def agreement(left_path: Path, right_path: Path) -> dict[str, Any]:
    left = load_toml(left_path)
    right = load_toml(right_path)
    return {
        "reviewer_a": str(left_path),
        "reviewer_b": str(right_path),
        "nodes": cohen_kappa(node_items(left), node_items(right)),
        "edges": cohen_kappa(edge_items(left), edge_items(right)),
        "decisions": cohen_kappa(decision_items(left), decision_items(right)),
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compute Cohen's kappa for two corpus ground-truth label files."
    )
    parser.add_argument("reviewer_a", type=Path)
    parser.add_argument("reviewer_b", type=Path)
    args = parser.parse_args()

    try:
        result = agreement(args.reviewer_a, args.reviewer_b)
    except (OSError, tomllib.TOMLDecodeError) as error:
        print(f"corpus_inter_rater: {error}", file=sys.stderr)
        return 1

    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
