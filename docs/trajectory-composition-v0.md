# Replay-Bound Trajectory Policy Composition v0

## Activated boundary

This contract activates policy evaluation over an already normalized,
validated, single-stream trajectory. It extends the integrity-only
[`trajectory-v0-contract.md`](trajectory-v0-contract.md) without turning a
normalized event into a kernel action or adding a governance-state transition.

The only successful runtime path is:

```text
exact committed policy bytes
  -> fixed composition-policy input boundary
  -> artifact_digest_v0 and trace/replay binding
  -> strict canonical-envelope decode
  -> one compiled GovernanceGraph
  -> ordered validated events paired with ordered replay records
  -> occurrence claims and singleton receipts
  -> increasing nonempty-prefix evaluation with the same graph
  -> output-only temporal result
```

`evaluate_replay_bound_composition_v0` is the sole public evaluator. It accepts
a `ValidatedTrajectoryTraceV0`, a `VerifiedTrajectoryReplayV0`, and exact policy
bytes. It first enforces the v0 policy-input boundary, before replay
recomputation, hashing, UTF-8 decoding, or TOML parsing. It then recomputes the
replay candidate and requires exact equality with the verified replay, checks
the exact policy artifact digest and trace binding, decodes the restricted
envelope, regenerates its one canonical serialization, requires byte equality,
and compiles one graph handle. Singleton and prefix decisions use that handle;
callers cannot supply claims, decisions, expected indices, or another event
vector.

The production `evaluate-codex-exec-composition-v0` command reaches this
evaluator only through an adapter-owned trace. A private input receipt plus
trusted adaptation context remains the direct route. A shareable sanitized
bundle may instead provide a closed `sanitizer-conforming-child-projection`:
the command validates the exact child privacy surface and all deterministic
compiled projection bytes before replay authorization and policy evaluation.
This public route does not prove that the sanitizer produced the child. An
optional
owner-private lineage sidecar adds a separate parent-link admission without
changing the public evidence class. Successful evaluation can materialize the
official compact trace, canonical trace, and composition result; it accepts no
caller-authored normalized trace.

The production command's preferred `--output-set PATH` mode stages exactly
`trace.json`, `canonical-trace.bin`, and `composition-result.json` in an
owner-only sibling directory opened immediately after creation. Every member is
published relative to that held descriptor, and every held regular-file
identity, owner, mode, link count, length, and content commitment is rechecked
together with exact inventory, unchanged inputs, staging-name identity, and
final-name absence immediately before one no-replace rename. That rename is
the sole namespace commit point. The contract is complete-set-or-error during runtime;
it does not claim persistence across a crash after rename because a post-rename
directory-sync failure cannot be reported without contradicting that contract.
On failure, the final cleanup freshly proves the parent-relative staging name,
the held directory's exact properties, and empty inventory immediately before
directory removal. The deterministic substitution schedule preserves an empty
replacement detected before that proof; Linux offers no
unlink-by-open-directory-descriptor operation, so this does not cover an unconstrained same-UID
substitution in the remaining proof-to-`unlinkat` syscall interval.
The compatibility form requires all three of `--trace-output`,
`--canonical-trace-output`, and `--output`. It preflights the complete set and
rolls back every newly linked member on ordinary failure, reporting
`output-rollback-uncertain` if quarantine and post-rename identity-safe rollback
cannot be proved. The deterministic pre-quarantine and post-validation
substitution schedules preserve the detected replacement in quarantine. They
do not exclude an unconstrained same-UID substitution in the final
identity/content-check-to-`unlinkat` syscall interval. This multi-path form is
runtime failure-atomic, not filesystem crash-atomic.

## Canonical policy

The runtime authority is
`fixtures/trajectory-composition-v0/policy.toml`. Its envelope binds:

- policy format `legitimacy.trajectory-composition.policy`, version `0`;
- policy `policy.trajectory-composition.peer-half`, version `0`;
- occurrence encoder
  `legitimacy.trajectory-composition.occurrence-index-strength`, version `0`;
- historical property
  `legitimacy.trajectory-composition.every-observed-prefix-green`, version `0`;
- one restricted graph.

The graph is exactly one first-match binary node, default Deny, with one
`peer_relative` gate on claim strength at percentile `0.5`, producing Permit.
It has no edges, transforms, other gates, or Escalate outcome. Unknown fields,
alternative numeric spellings, semantically equivalent whitespace, changed
identities or versions, and any other graph profile fail closed. General TOML
equivalence is not authority.

## Occurrences and receipts

The validated event vector is enumerated once. Position `i` produces claim ID
`occurrence:i`, claimant index `i`, and positive strength `i + 1`. This is a
policy-specific ordinal probe over the one validated list. It does not encode
actor identity, entitlement, authority, priority, moral weight, or an inference
from payload integers or `source_item_id`.

Each receipt retains its zero-based occurrence index, claim wire ID and exact
integer strength, event ID, normalized kind, optional source-item ID, exact raw
record digest, replay canonical-event digest, and singleton decision. A
repeated source-item ID remains valid and does not alias occurrence claims.
Event identity, source-item identity, occurrence identity, and claim strength
remain separate fields.

Successful result types have private fields, no public deserializer, and no
unchecked constructor. `to_json_line` emits deterministic inspection/sealing
bytes containing the exact policy bytes in lower hexadecimal, but decoding or
possessing such bytes confers no evaluation authority.

## Temporal semantics

`PrefixGreen` means that every claim in one current nonempty prefix receives
Permit. It is not extension-closed for the peer rule: the Lean development
retains a concrete current-prefix recovery example.

`EveryObservedPrefixGreen` means that every nonempty prefix observed so far was
green. The evaluator inspects prefixes in increasing length. Once an observed
prefix fails, the historical property stays false because that prefix remains
in the history.

An earliest composition failure records three deliberately different indices:

- `transition_index = prefix_length - 1`, zero-based;
- `prefix_length`, one-based;
- the least zero-based denied occurrence index inside that prefix.

Singleton denial is classified as local failure, never composition failure.
Only an all-singletons-Permit trajectory with a failing prefix receives the
composition-failure classification.

## Lean and generated parity boundary

`Legitimacy.Protocol.TrajectoryComposition` proves the generic occurrence
encoder and historical search properties. The search proofs reason about the
computed `findIdx?` results: soundness, strict earlier-prefix minimality, least
denied-occurrence minimality, completeness/`none` equivalence, and historical
prefix closure are not projections from stored witness fields. Boolean checks
have propositional reflection theorems.

`Legitimacy.Protocol.TrajectoryCompositionGenerated.Fixtures` is derived data.
It projects the exact selected policy to the existing canonical Lean peer graph
and proves that graph equality. It contains the concrete two-event safe witness
and three-event local-green/global-red witness with first failure exactly
`(2, 3, 0)`. Generic theorems, rather than a generated expected-value table,
establish encoder distinctness and search correctness.

For the selected bounded runtime profile, occurrence strengths are integers
`1..=10000` and the percentile is exactly binary-representable `0.5`. Lean
derives the canonical compiled graph's decision on any in-range occurrence of
an encoded nonempty prefix and rewrites it through the rational half comparison
equivalent to `2 * rank >= total`. The Rust peer evaluator calls one production
rank-comparison helper, and the exhaustive test checks that helper for every
bounded `0 <= rank <= total` pair together with exact integer-to-`f64`
conversion. A source-structure control binds the evaluator's return path to
that helper. This is not a general theorem that Rust `f64` equals Lean rational
arithmetic.

Regenerate and byte-compare every owned derived artifact with:

```sh
scripts/check-trajectory-composition-fixtures.sh
```

The script discovers both complete generated file sets, regenerates in a
temporary directory, compares exact bytes, and verifies that a deliberate
generated-byte mutation is detected. `scripts/verify.sh` runs this gate before
the full Lean and Rust builds.

## Explicit nonclaims

This composition layer does not instantiate `KernelStep` or
`StateActionSpace`, construct or retag a sacrifice certificate, or state a
`GovernanceState` transition. It adds no enforcement, publication, signature,
viewer, CLI command, schedule, concurrency, lease, principal partition, or
sacrifice logic.

Lean does not prove TOML or Rust parsing, canonical byte serialization,
SHA-256, trace validation, replay authorization, Rust graph compilation, or
floating-point evaluation. The generated fixture module is rebuildable parity
evidence for the selected policy and traces, not authority and not a proof of
arbitrary artifact processing.
