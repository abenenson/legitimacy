# Curated Answer Key: crewai

Scope: theorem-backed PythonHookCore model under `theorem/`, tied to pinned
CrewAI commit `c9100cb51d357f6e3ba7d9969a000571f051ca64` as the modeled
before-tool hook surface.

- Node precision: 1.0
- Node recall: 1.0
- Edge precision: 1.0
- Edge recall: 1.0
- Schema agreement nodes: 1.0
- Schema agreement edges: 1.0
- Disagreements: none

The extracted graph was compared against a curated answer key. The duplicated
reviewer files are schema fixtures, not independent hand labels. All extracted
nodes and edges are present in the consensus graph, and the consensus contains
no additional nodes or edges outside the extracted graph.

The theorem-backed claim is intentionally scoped to the PythonHookCore modeled
program in `theorem/python_hook_core_model.py`. It does not assert a byte-level
completeness proof over every file in the pinned upstream CrewAI revision; the
reviewed files document the source-faithfulness judgment for this modeled
before-tool hook slice.
