# Degenerate Graph Behavior

This note records the release-gated behavior for empty and cyclic governance
graphs across the canonical graph audit checks. The table is descriptive of the
current Rust production diagnostics; it is not a Lean axiom inventory. Runtime
kernel checks now use an explicit internal `Skipped` verdict for skipped
projection cases, and audit/report JSON surfaces preserve skipped checks with a
recorded reason rather than counting them as passes. `can_extract_compile` is an
extractor substrate-extractability check: it requires at least one
passing axiom, no rejected axioms, and no cycle findings. It is intentionally
weaker than the live-state activation gate, which rejects skipped kernel
evidence before activation.

| Check | Empty graph behavior | Cyclic graph behavior |
| --- | --- | --- |
| graph consistency | No special skip; the standard graph traversal and claimant-reduction check determine the verdict. | No special skip; the standard traversal/cycle validation path determines the verdict. |
| graph solidarity | No special skip; the standard common-shock check determines the verdict. | No special skip; the standard traversal/cycle validation path determines the verdict. |
| graph monotonicity | No special skip; the standard strengthening check determines the verdict. | No special skip; the standard traversal/cycle validation path determines the verdict. |
| graph strategyproofness | No special skip; the standard strength-misreport check determines the verdict. | No special skip; the standard traversal/cycle validation path determines the verdict. |
| graph certifiability | Reject: there is no governance node from which to replay a certificate trace. | Skipped with the cycle reason recorded; cycle behavior is left to cycle and nonvacuity probes. |
| graph observable determinacy | Skipped because there is no order-dependent decision surface; the skip reason is recorded. | Skipped with the cycle reason recorded; cycle behavior is left to cycle and nonvacuity probes. |
| graph corrigibility | Reject: there is no governance surface for supervisory pause, deny, or stop overrides. | Skipped with the cycle reason recorded; cycle behavior is left to cycle and nonvacuity probes. |
| graph compositional safety | Skipped because no denied decision can be revived; the skip reason is recorded. | Skipped with the cycle reason recorded; cycle behavior is left to cycle and nonvacuity probes. |
| graph nonvacuity | Reject: a nonempty governance graph with at least one permitting disposition is required. | Uses the explicit cycle probe when the caller supplies detected cycles; otherwise it follows the acyclic traversal path used by that caller. |
