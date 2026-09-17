# Extractor Boundary

There are two extraction paths. The production Rust source walker has empirical
and byte-parity evidence. Lean also implements extractors for restricted source
languages and proves properties of those transformations. Connecting either
path to a live harness requires evidence about the source interpretation.

## From source to a checked decision

For the restricted Rust hook language, the proof path is:

1. Represent a program in the modeled source language, with its own
   [decision semantics](../lean/Legitimacy/Extract/RustHookCore/Semantics.lean).
2. [Extract its registered hooks](../lean/Legitimacy/Extract/RustHookCore/Extractor.lean)
   into a governance graph, failing on missing registrations or callbacks.
3. Apply `extractRustHookCore_decision_equivalent`: every successful extraction
   preserves the modeled program's decisions for all claim profiles and subjects.
   The [soundness proof](../lean/Legitimacy/Extract/RustHookCore/Soundness.lean)
   proceeds by induction over registrations.

The [Codex hook fixture](../lean/Legitimacy/Extract/RustHookCore/Fixtures/CodexHooks.lean)
manually supplies such a modeled program. The general transformation theorem
is proved; the interpretation of live source as that program is not. It neither
verifies the production Rust parser nor covers arbitrary Rust execution.
Byte-stable extraction and agreement with saved fixtures alone cannot establish
that the abstraction preserves a live harness's relevant behavior.

## Modeled language versus accepted Rust syntax

The Lean AST is wider than the Rust parser's accepted fragment. Its
[`Expr` and `Stmt` constructors](../lean/Legitimacy/Extract/RustHookCore/Syntax.lean)
include conditionals and expressions that the production parser refuses.
In the [modeled semantics](../lean/Legitimacy/Extract/RustHookCore/Semantics.lean),
`Expr.eventEq` always evaluates to `false`; expression evaluation has no event
argument. This is distinct from `Stmt.matchEvent`, which does compare the
registration event with its arm labels. A matching arm without a direct hook
result falls back to the default; the Rust parser instead requires every arm
to return a direct `HookResult` variant. Modeled calls are also not an execution
of their implementations.

The general decision-equivalence theorem remains a theorem of those explicitly
defined Lean semantics. It does not establish that all Lean constructors model
accepted Rust, or that their extra cases are faithful Rust semantics. A future
mechanical translation must specify its image in this AST and validate the
correspondence on that image. The ordinary-Rust execution tests below provide
evidence for the accepted source fragment, not for the extra Lean constructors.

## Formally Proved

- `BoundedExtractorContract` states the Lean-side source evidence, runtime
  kernel, and semantic bridge obligations for a modeled extractor.
- `bounded_extractor_contract_sound` proves that a contracted extractor maps a
  well-formed bounded source package to a semantic legitimacy kernel.
- `extractor_byte_stable_soundness_boundary` makes the boundary explicit: byte
  equality between a Rust run and Lean-modeled bytes is an external hypothesis,
  while Lean proves the contracted runtime and semantic obligations.
- `EmpiricalParityCertificate` formalizes the finite governance-admissibility audit fixture
  certificate once external byte-equality facts are supplied. AutoGen is the
  currently discharged leaderboard instance.
- `EmpiricalByteParityCertificate` and
  `canonical_leaderboard_fixtures_byte_parity_certificate` formalize byte
  parity for the full canonical leaderboard fixture set without claiming that
  every generated graph has a completed Lean governance-admissibility audit proof.

## Empirically Enforced

- `CanonicalInputs.lean` is the shared canonical fixture source of truth for
  Lean and Rust.
- Rust parity tests parse that shared Lean record list and check fixture source
  presence, deterministic source byte counts, deterministic source-tree hashes,
  repeated extraction byte stability, and byte equality with committed canonical
  graph snapshots.
- The routine verification gate runs the ordinary parity tests; the release gate
  additionally replays the slow leaderboard transcript snapshots and slow Codex
  extraction fixture.

## Not Verified

- Lean does not verify full Rust operational semantics; the checked source
  languages cover explicit restricted cores.
- Lean does not prove Rust parser or serializer correctness for arbitrary
  inputs.
- The canonical fixture certificate is finite. It is not a parser-correctness
  theorem for non-canonical inputs.
- Runtime-kernel claims for non-canonical or ill-formed inputs require their own
  evidence; they are not obtained from the canonical fixture parity certificate.

## Accepted Rust hook source and remaining assumptions

The Rust `--mode theorem-backed` path parses a restricted source model. Its name
refers to the associated Lean model, not a proof of this Rust parser or of the
emitted production audit graph. The parser accepts direct `HookResult` returns
and event matches on the actual `HookInput` parameter. Event arms must be distinct
string literals or locally declared `HookEvent` variants, followed by one final
wildcard. Guards, other scrutinees, discarded decision expressions, local
bindings and conditional compilation are refused. Registration syntax requires
a literal event and an unqualified callback name; extraction refuses missing,
ambiguous or duplicated event/callback registrations instead of selecting or
silently dropping them.

The modeled Codex fixture also contains argument-free, unqualified call
statements. Their names and order are recorded as **opaque labels**. Their
implementations, termination and effects are not verified. Imports, the external
`HookInput` definition, and `register_hook!` implementation remain interpretation
assumptions. Parsing is not Rust type checking. The independent execution tests
exercise call-free hooks with an explicit input type and registration stub;
they do not validate those external dependencies or the whole live harness.

These are separate evidence connections, not an established end-to-end proof
from live source to runtime behavior. **Proved** refers to Lean model semantics;
**tested** refers to executable checks; **open** identifies a correspondence
that still needs evidence.

| Connection | Status | Evidence and limit |
| --- | --- | --- |
| Concrete source → Rust hook summary | Tested | Syntactic restrictions and executable regression tests; no parser-correctness proof. |
| Rust summary → production audit graph | Tested; execution correspondence open | Tested graph construction using decision vocabulary, defaults and registration topology. Event-to-result mappings and opaque call effects are not encoded as execution semantics. Equal graph bytes do not imply equivalent hook behavior. |
| Manually supplied Lean program → binary governance graph | Proved within the modeled language; source interpretation assumed | `extractRustHookCore_decision_equivalent` proves decision equivalence within the modeled Lean language. The current Rust summary is not mechanically translated into that program. |
| Binary graph → production audit verdict | Open for arbitrary production extraction | A separate representation obligation; the conditional [verdict pullback](../lean/Legitimacy/Extract/RustHookCore/VerdictPullback.lean) does not discharge it for arbitrary Rust extraction. |
| Fresh graph → committed fixture theorem | Tested identity check; theorem about matched fixture | The audit agent can reuse fixture theorem applicability on an exact canonical graph match. A different graph is marked `extracted_diagnostic_only`. Neither case verifies source interpretation. |

The [source-fidelity tests](../tests/rust_hook_core_fidelity.rs) include ordinary
Rust execution showing that adding a false match guard or changing a scrutinee
changes the result. Both source variants must fail through the CLI before a
graph or witness is exported. Additional tests cover precedence, discarded
results, declaration/registration binding and accepted event summaries. This
closes concrete accepted-input defects; mechanical translation validation and
the production graph semantics remain distinct work.
