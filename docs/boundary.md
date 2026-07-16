# Boundary

This page records what the repository proves, what it checks empirically, and what remains in the trusted base. Return to the concise entry point at [README.md](../README.md), or use [repository-context.md](repository-context.md) for the full repository map.

## Guarantee Boundary

| Bucket | What it means |
| --- | --- |
| Formally proved | Lean proves the named mathematical statements, runtime-kernel obligations, semantic-bridge obligations, and bounded extractor contract theorems over modeled artifacts. |
| Empirically enforced | Rust executes extraction and graph audits; fixture tests pin deterministic source bytes, graph snapshots, spectral expectations, and byte-stable canonical outputs. |
| Not verified | Lean does not verify Rust execution, arbitrary parser or serializer correctness, or source-to-Lean semantic preservation outside the explicitly modeled fixture and contract surfaces. |

## Extraction Contract

The formal guarantees in this repository govern the *extracted* `GovernanceGraph` model. Source-to-graph extraction through the Rust `src/extract/` pipeline and its tree-sitter parsers is heuristic and empirical, not formally verified.

Lean proves properties of modeled governance artifacts once the graph exists. It does not prove that arbitrary source syntax was faithfully converted into that graph. Extraction faithfulness is therefore part of the trusted base: byte-stable fixtures, parity tests, provenance records, and committed snapshots provide evidence for it, but it is not itself a theorem in the current tree.

Reviewers should treat this source-to-graph boundary as the unverified TCB. Attacks on extraction faithfulness, parser coverage, omitted control flow, or misleading source structure are attacks on the trusted base, not refutations of the Lean proofs over the resulting `GovernanceGraph`.

## Public Graph Coverage Notes

Public graph coverage is intentionally narrower than the full development audit trail. The root package keeps source-walked Codex (`codex-rs`) and Claude Agent SDK (`claude-agent-sdk-python`) graph fixtures as executable examples. The broader public leaderboard also records CrewAI and OpenClaw extracted-graph fixtures with their provenance disclosures.

The public examples instantiate the diagnostic surface on real open-source
agent harness graph fixtures. They are reproducible diagnostic artifacts, not
social rankings of the underlying projects and not refutations of frontier
safety frameworks. Rejection rows are diagnostic-specific: for example,
OpenClaw rejects nonvacuity rather than monotonicity, while the separate
AI-Control fixture family receives `AuditVerdict.legitimate` under the current
polarity-aware audit. Fixture provenance is recorded in
[examples/graphs/README.md](../examples/graphs/README.md); broader dated
cross-checks and proprietary-product metadata can remain outside the public
repository without weakening the formal theorem stack.
