# Extractor AST Theorem Witness Protocol

This protocol addresses the extractor-boundary gap where a Rust run emits a
governance graph and a Lean theorem witness, but the artifact did not previously
bind that theorem witness to the parsed source shape and token text.

## Scope

The protocol binds three artifacts:

- the source directory parsed by the Rust extractor;
- the extracted `GovernanceGraph` JSON;
- the Lean theorem name generated for that graph.

It does not prove tree-sitter soundness, Rust operational semantics, SHA-256
inside Lean, or semantic completeness for arbitrary source programs.

## Hashes

`sourceAstHash` uses
`tree-sitter-canonical-shape-and-tokens-sha256:v2`:

1. discover the same supported source files as extraction (`.py`, `.rs`, `.ts`,
   `.tsx`, excluding test/spec/declaration files); symlink entries are skipped
   by the directory walk and are not included in discovered-file counts;
2. sort by repository-relative path;
3. parse each file with the corresponding tree-sitter grammar and reject parser
   errors;
4. build a canonical tree shape from tree-sitter node kinds, excluding comment
   nodes;
5. build a canonical leaf-token stream that records token kind plus token text,
   excluding comment nodes and ordinary whitespace;
6. hash the algorithm label plus each relative path, language tag, canonical
   shape, and canonical token stream.

This means identifier renames and literal-value edits change the witness hash
even when the parse tree shape is unchanged. Ordinary whitespace-only edits do
not change the hash. Comment-only edits also do not change the hash; semantic
text such as Python docstrings remains bound because it is parsed as a string
literal token, not a comment.

`governanceGraphHash` uses `serde-json-pretty-sha256:v1` over the canonical
pretty JSON serialization of the extracted `GovernanceGraph`.
This includes source-location text in node names when the extractor emits it.
A comment or blank line inserted above a Python function can therefore leave
`sourceAstHash` unchanged while changing `governanceGraphHash`. An old witness
will not verify against that newly extracted graph. AST-hash invariance is not
whole-witness invariance; regenerate the graph and witness together after such
an edit. This conservative invalidation does not imply a policy-semantic change.

## Witness

`legitimacy extract SOURCE --emit-graph graph.json --emit-theorem-witness
witness.json --theorem-name theorem_witness_Y` emits:

- schema version;
- Lean theorem name;
- source directory label;
- AST hash algorithm and source shape/token hash;
- graph hash algorithm and graph hash;
- Lean binding type name;
- per-file AST hashes.

`legitimacy verify-witness witness.json --source-dir SOURCE --graph graph.json`
recomputes the AST and graph hashes and exits with code `0` only when both match
the witness.

## Lean Boundary

`Legitimacy.Extract.ASTWitness` defines `ASTTheoremWitnessBinding` and
`HashedGovernanceGraphDerivation`. Lean consumes the externally verified strings
as derivation-step metadata. This keeps the formal claim honest: hash equality is
an empirical verifier result, while the Lean theorem ensures the generated graph
derivation carries the exact verified binding.
