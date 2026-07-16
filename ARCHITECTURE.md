# Legitimacy Architecture

Legitimacy has one canonical rule-governance pipeline:

`.rule.toml` rule policy -> parser -> `RuleSpec` -> compiler -> `CompiledRule` + runtime context -> certificate / audit ledger`

This document is the anti-split-brain contract for the crate. There is one rule-construction path, one persistence path, and one certification path.
The kernel safety stack is decomposed in
[`docs/architecture/kernel-safety-decomposition.md`](docs/architecture/kernel-safety-decomposition.md).

## Canonical Rule Path

Declarable rules enter through `.rule.toml` rule-policy files only.

1. A `.rule.toml` rule policy is parsed by [`src/policy/parser.rs`](src/policy/parser.rs).
2. The parser validates the file and produces a `ParsedPolicy`.
3. `ParsedPolicy.rule` is always a `Rule` whose executable payload is `RuleSpec`.
4. Declarable rule kinds become `RuleSpec::Declarative(...)`.
5. Programmatic rules must go through `RuleSpec::Programmatic(...)`.
6. The compiler only evaluates rules through `Rule::allocate()`, which delegates to `RuleSpec`.

There are no alternative declarative construction paths.

Rule-policy files are the only declarable entry point for `RuleSpec`.

Programmatic rules are allowed, but they are not a second architecture. They must be wrapped in `RuleSpec::Programmatic`, so they still flow through the same canonical `RuleSpec` boundary as parsed policies.

## Canonical Compile Path

Compilation is centralized in [`src/compiler.rs`](src/compiler.rs):

1. `compile()` receives a `Rule`, claims, estate, claimants, and a declared `Family`.
2. `compile()` runs the axiom checks over that `Rule`.
3. The result is one `CompiledRule`.
4. Every `CompiledRule` is persisted to the ledger.

Consistency is the public Young full sub-coalition diagnostic: release and
leaderboard compilation enumerate every nonempty proper removed coalition and
preserve survivor allocations on the reduced estate. Bounded enumeration is an
explicitly labeled opt-in approximation for operational probes, not the public
consistency signal.

There is no side-channel compiler and no shadow compiled representation.

## Canonical Persistence Path

Persistence is centralized in [`src/ledger.rs`](src/ledger.rs).

The SQLite `Ledger` is the only historical store for:

- compiled rules
- certificates
- paradox results

Audit-chain hashing internals live in the private `src/ledger/chain/`
submodule; callers still enter through `src/ledger.rs`.

All historical audit queries read from the `Ledger`.

There is no parallel JSON log, ad hoc file export, or alternate audit database in the crate's architecture.

## Canonical Certification Path

Certification is centralized in [`src/certificate.rs`](src/certificate.rs):

1. `certify()` accepts a certification context: compiled rule, runtime rule, claims, and estate.
2. The compiled rule must already be admissible.
3. `certify()` re-runs the rule and verifies the claimed outcome matches the actual output.
4. `certify()` emits a `Certificate`.
5. Every certificate is written to the `Ledger`.

The audit surface reads certificate history from the ledger. It does not reconstruct certificates through an alternate runtime path.

## Canonical Audit Path

The CLI audit surface in [`cli/main.rs`](cli/main.rs) reads historical state from the ledger.

That means:

- `compile()` writes compiled rule history
- `certify()` writes certificate history
- `run_paradox_suite()` writes paradox history
- `legitimacy audit` queries that history

The audit path is read-oriented and ledger-backed. Historical inspection does not depend on recompiling a policy to discover prior outcomes.

## Paradox Diagnostic Boundary

Paradox detection is a Rust-side production diagnostic, not a Lean-side
canonical axiom. The `legitimacy paradox` command and the leaderboard
`Paradoxes` column search concrete allocation and governance-graph
perturbations for witness patterns such as claimant-addition loss, population
loss, priority inversion, compositional Alabama, feedback monotonicity failure,
and path dependence.

Those witnesses are deliberately recorded as operational evidence in the
ledger, separate from the Lean `AuditCheck` and Rust `GovernanceProperty`
inventories. The Lean theorem stack owns the canonical graph diagnostics and
runtime-kernel projections; paradoxes are downstream finite-search probes that
help explain or localize failures in those diagnostics. A reviewer should not
expect an `AuditCheck.paradox`, `GovernanceProperty::Paradox`, or Lean
`Alabama` predicate unless the project later promotes paradoxes into a new
formal axiom family.

## Review-Required Lattice

The review-required lattice is formalized as a parallel Lean research axis, not
as a replacement for the canonical graph-audit axioms. The canonical
`decisionRank` remains
`deny < escalate < permit`. The alternate `decisionRankReviewRequired` collapses
terminal `.escalate` into the same non-denial class as `.permit` for
monotonicity, interpreting escalation as review-required and eventually
upgradeable rather than as definitive denial.

The lattice revision is paired with `GraphNonvacuityReviewRequired`: terminal
`.escalate` is also nonvacuous under the same semantics. This prevents a
split-brain result where monotonicity accepts review-required escalation while
nonvacuity still rejects it as unresolved.

The committed leaderboard fixture verdicts are mixed. AutoGen remains
admissible. Claude Agent SDK flips to admissible under the review-required lattice,
showing choice-sensitivity for that hook-protocol witness. Codex and CrewAI
still reject monotonicity even after permit/escalate equivalence, so their
failures are not only permit-to-escalate artifacts. OpenClaw still rejects
nonvacuity because its failing check is all-deny, not terminal escalation.

## Anti-Split-Brain Rules

The following are architectural invariants:

1. One canonical rule boundary: `RuleSpec`.
2. One canonical persistence boundary: `Ledger`.
3. One canonical certification boundary: `certify()`.
4. No alternative declarative entry paths besides `.rule.toml` rule policies.
5. No programmatic bypass around `RuleSpec`; programmatic rules must use `RuleSpec::Programmatic`.
6. No alternative historical store besides the SQLite ledger.

If a future change introduces a second way to declare rules, persist governance history, or issue certificates, it is an architectural regression unless this document and the code are updated together.

## Graph And Protocol Surface

Graph `.graph.toml` policies are a distinct entry surface used for extraction-style governance graphs and the protocol state machine. `.graph.toml` is the canonical graph input format; emitted JSON is a derived artifact for interchange and inspection. They do not bypass the canonical rule pipeline above; they feed the graph compiler and protocol machinery in [`src/policy/graph_parser.rs`](src/policy/graph_parser.rs) and [`src/protocol/`](src/protocol/).

The Lean protocol formalization and the Rust protocol runtime are intended to agree on the state-machine core. Lean currently tracks the formal five-property protocol core: consistency, solidarity, monotonicity, strategyproofness, and non-vacuity. Rust additionally monitors the graph-side runtime projections for certifiability, observable determinacy, corrigibility, and compositional safety, plus operational metadata such as timestamps, certificates, and ledger hashes. Those runtime projections and persistence details are not part of the Lean protocol state until they are promoted into paired Lean protocol predicates and gates.

The crate-level `cli_runtime` module contains rule-policy loading and
compilation helpers shared by CLI commands. It is separate from
`src/protocol/`, which owns the governance protocol state machine.

## Lean Module Convention

Lean umbrellas such as `Legitimacy.Kernelization`,
`Legitimacy.Spectral.RGFlow`, and
`Legitimacy.Results.GovernanceAdmissibilityAudit` are import-stable re-export
surfaces. Child modules named `Core` are not catch-all junk drawers; within an
umbrella, `Core` means the irreducible primitives for that domain: vocabulary,
base predicates, and theorems that sibling modules build on directly.

Focused child modules should hold examples, certificates, concrete finite
tables, robustness sweeps, and extraction fixtures. A serious import boundary
change should preserve the umbrella module and move declarations only when the
new module name explains a responsibility better than the existing `Core`
contract.
