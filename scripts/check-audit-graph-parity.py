#!/usr/bin/env python3
"""Compare evaluated Lean audit graphs to the complete Rust fixture values.

The Lean exporter preserves gate/edge order and duplicate nodes. Numeric fields
are compared as exact rationals; names, defaults, combination logic, transforms,
and all other fields must agree. This check establishes fixture value parity,
not end-to-end Rust/Lean refinement.
"""
import argparse
import copy
from fractions import Fraction
import json
from pathlib import Path
import subprocess

TARGETS = {
    "codex-cli": "examples/graphs/codex-graph.json",
    "claude-agent-sdk": "examples/graphs/claude-agent-sdk-graph.json",
    "claude-code": "examples/graphs/claude-code-graph.json",
}
NUMERIC = {"min", "percentile", "threshold", "delta"}


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(text):
    # Preserve decimal lexemes instead of passing through binary floating point.
    return json.loads(text, parse_float=str, object_pairs_hook=no_duplicate_keys)


def normalize(value, key=None):
    if key in NUMERIC:
        if isinstance(value, bool):
            raise ValueError(f"boolean numeric field: {key}")
        return Fraction(value)
    if isinstance(value, dict):
        return {k: normalize(v, k) for k, v in value.items()}
    if isinstance(value, list):
        return [normalize(v) for v in value]
    return value


def lean_graph_to_rust(graph):
    if set(graph) != {"nodes", "edges"}:
        raise ValueError("unexpected Lean graph fields")
    nodes = {}
    for node in graph["nodes"]:
        if len(node) != 1:
            raise ValueError("invalid Lean node constructor")
        payload = next(iter(node.values()))
        node_id = payload["id"]
        if node_id in nodes:
            raise ValueError(f"duplicate Lean node id: {node_id}")
        nodes[node_id] = node
    return {"nodes": nodes, "edges": graph["edges"]}


def check_pair(target, lean_graph, rust_graph):
    for node_id, node in rust_graph["nodes"].items():
        if len(node) != 1 or next(iter(node.values()))["id"] != node_id:
            raise ValueError(f"{target}: inconsistent Rust node key/id")
    actual = normalize(lean_graph_to_rust(lean_graph))
    expected = normalize(rust_graph)
    if actual != expected:
        raise ValueError(f"{target}: evaluated Lean graph differs from Rust fixture")


def self_test():
    node = {"Binary": {"id": "n", "name": "name", "gates": [
        {"ExactMatch": {"value": "Read", "decision": "Permit"}},
        {"ThresholdGate": {"field": "strength", "min": "1/10", "decision": "Deny"}},
    ], "default": "Deny", "combination": "FirstMatch"}}
    lean_graph = {"nodes": [node], "edges": [{"from": "n", "to": "n", "transform": "PassThrough"}]}
    rust_graph = lean_graph_to_rust(copy.deepcopy(lean_graph))
    rust_graph["nodes"]["n"]["Binary"]["gates"][1]["ThresholdGate"]["min"] = "0.1"
    check_pair("positive", lean_graph, rust_graph)
    for mutation in ("default", "combination", "gate_order", "name", "numeric", "edge", "extra_node", "duplicate_node"):
        changed = copy.deepcopy(lean_graph)
        payload = changed["nodes"][0]["Binary"]
        if mutation == "default": payload["default"] = "Permit"
        elif mutation == "combination": payload["combination"] = "AnyMustPass"
        elif mutation == "gate_order": payload["gates"].reverse()
        elif mutation == "name": payload["name"] = "other"
        elif mutation == "numeric": payload["gates"][1]["ThresholdGate"]["min"] = "10000000000000001/100000000000000000"
        elif mutation == "edge": changed["edges"][0]["transform"] = {"ClaimModification": {"delta": "1/1"}}
        elif mutation == "extra_node": changed["nodes"].append({"Binary": {**payload, "id": "extra"}})
        elif mutation == "duplicate_node": changed["nodes"].append(copy.deepcopy(node))
        try:
            check_pair(mutation, changed, rust_graph)
        except ValueError:
            continue
        raise AssertionError(f"parity checker missed {mutation}")
    try:
        load_json('{"nodes": {}, "nodes": {}}')
    except ValueError:
        pass
    else:
        raise AssertionError("parity checker accepted duplicate JSON keys")
    print("audit graph parity checker: positive control and 9 adversarial mutations passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    self_test()
    if args.self_test:
        return
    root = Path(__file__).resolve().parent.parent
    exported = subprocess.run(
        ["lake", "env", "lean", "--run", "Legitimacy/Fixtures/ExportAuditGraphs.lean"],
        cwd=root / "lean", text=True, capture_output=True, timeout=300, check=False,
    )
    if exported.returncode != 0:
        raise SystemExit(
            f"Lean audit graph exporter failed (exit {exported.returncode}):\n"
            f"{exported.stdout}{exported.stderr}"
        )
    if exported.stderr.strip():
        raise ValueError(f"Lean exporter produced diagnostics: {exported.stderr}")
    graphs = load_json(exported.stdout)
    if set(graphs) != set(TARGETS):
        raise ValueError("exported graph target coverage differs from CLI target coverage")
    for target, path in TARGETS.items():
        fixture = load_json((root / path).read_text())
        check_pair(target, graphs[target], fixture)
        print(f"audit graph parity: {target}: complete evaluated graph matches ({len(fixture['nodes'])} nodes)")


if __name__ == "__main__":
    main()
