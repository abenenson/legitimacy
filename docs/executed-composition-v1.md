# Executed composition and useful repair (format v1)

Two supplied principals execute two requests through a sequential instrumented
host with harmless synthetic data. Under the identical local policy and forbidden
property, public/public fragment delivery is collectively forbidden;
public/vault fragment delivery is safe. Both complete runs have two locally
permitted events. The difference is the delivered action and channel.

The composition guard preserves the original property and useful work. It denies
B's public fragment after A's public fragment, while allowing B's vault delivery
or public summary. B's public fragment is allowed in an empty exposure context.
A competent full-context conventional checker evaluates each candidate against the
actual preceding deliveries and agrees with the guarded policy. Its aggregate
answer is Deny for the unguarded harmful run; it does not simulate a separate
counterfactual history. No
superior detection result is claimed.

## Run it

With the supplied Linux x86_64 bundle, run `./reproduce.sh`, then open
`reader.html`. Bash, Python 3, and compatible system libc are required. The
bundle contains the executable and public verification key; it needs no model
credentials, private keys, network, Cargo, or Lean build. The command validates
bundle hashes, verifies existing typed signed replay, recomputes all seven
results, compares them with the supplied expectations, and executes the host
again. A hash manifest detects accidental edits; its trust comes from the
separately obtained bundle, not from a self-authenticating hash.

From source, using existing caches:

```sh
CARGO_BUILD_JOBS=2 cargo build --bin legitimacy-executed-composition
target/debug/legitimacy-executed-composition demo
target/debug/legitimacy-executed-composition check \
  fixtures/executed-composition-v1/capture/bundle.json \
  --trust fixtures/executed-composition-v1/capture/trust-policy.json
CARGO_BUILD_JOBS=2 RUST_TEST_THREADS=2 cargo test --test executed_composition
bash scripts/check-executed-composition.sh
LEAN_NUM_THREADS=2 CARGO_BUILD_JOBS=2 RUST_TEST_THREADS=2 bash scripts/verify.sh
```

Package a clean committed checkout with
`bash scripts/package-executed-composition.sh /absolute/new/bundle-directory`.
The package command owns a locked Cargo build and selects its exact executable
from Cargo output. It rejects binary overrides and source changes, and records
the checkout commit, full source tree, toolchain, build settings, and executable
hashes in `BUILD_PROVENANCE.json`. This trusts the builder and toolchain; it is
not a reproducible-build or compiler-refinement proof. A locally built package
may name a private checkout commit; published release bundles must be built from
the curated public commit, whose tree equals the reviewed development tree.

`record NEW_DIRECTORY` is a maintainer operation: it executes the host, signs
captures with a fresh transient key, retains only the public trust policy, and
self-verifies. Existing captures and their receipts are never rewritten. Trust
policies must be obtained independently of an untrusted submitted capture.

## The checked connection

[ExecutedComposition.lean](../lean/Legitimacy/Protocol/ExecutedComposition.lean)
owns the finite semantics. State records whether each principal's synthetic
fragment has actually reached the declared public sink. Summaries and vault
deliveries are real permitted effects, but do not expose fragments. State is
cumulative and repeated deliveries by one principal do not create another
participant. The host supplies order; the model does not infer concurrency.

The projection into the existing Bool-action kernels maps A's public exposure to
`true` and B's public exposure to `false` (the negation of B's exposure bit).
This principal-dependent encoding deliberately retains the exact existing
`boolJointForbiddenList`. It neither edits that predicate nor uses the positive
historical fixture's different `boolTrackedSafeForbiddenList`.

| Lean declaration | Checked statement |
| --- | --- |
| `delivery_log_refines`, `executed_delivery_witness` | The admitted delivery log reconstructs execution state; harm requires actual public fragment deliveries by both principals. |
| `executed_refinement` | The realized exposure/action bundle reaches the original joint forbidden property exactly when both public exposure bits are true. |
| `executed_implies_composed` | An executed violation supplies a witness for the existing three-channel composed violation predicate. |
| `realized_tracked` | The declared `CrossAgentEdge` tracks the realized conjunction in both outcomes. Tracking alone cannot explain repair. |
| `repair_safe`, `executed_repair_same_property` | Every finite sequence guarded by scoped local authorization and preservation of the original property excludes the executed joint violation. |
| `equal_length_action_control`, `useful_repair` | Concrete equal-length discrimination, permits and denials, useful alternatives, authority/profile sensitivity, and prior-context sensitivity. |
| `authentication_not_authorization` | Missing delegation cannot yield Permit, regardless of authentication. |
| `sufficient_iff_factor` | A query factors through observations exactly when it is constant on each observation fiber. This is the classical partition principle. |
| `exact_safe_observation_requires_three`, `one_bit_observation_insufficient` | Exact answers to every next-request query on reachable safe contexts require at least three observation values: one bit cannot suffice. |
| `two_exposure_bits_suffice` | The two public-exposure bits suffice for every request in this model. |
| `authority_observation_insufficient` | Erasing delegation makes two modeled requests observation-identical despite different required decisions. Restoring that fact separates them. |

The old unrestricted `JointCapabilityViolatesForbidden` quantifies over available
capabilities; it remains inhabited even after a safe execution. The new
`ExecutedViolation` restricts the action bundle to the actual accumulated
exposure projection. The forward connection is proved; there is deliberately no
converse and no assertion that the runtime guard removes latent capabilities.
The old kernel trajectory represents kernel evolution, not a tool event log.
The new execution/action refinement is the explicit bridge between those objects.
The repair proves exclusion of this executed conjunction, not universal safety
for arbitrary properties or an inhabitant of every kernel obligation.

The theorem footprints use at most `propext`, `Classical.choice`, and
`Quot.sound`; concrete useful-repair and observation-ambiguity witnesses need
no axioms. No new axiom or `native_decide` is used in these proofs.

## Evidence and checking boundaries

| Layer | Status and trust boundary |
| --- | --- |
| Finite transition, refinement, repair, observation statements | Lean kernel checked. |
| Complete 128-row transition table | Generated by evaluating Lean over all seven Boolean inputs; byte regeneration gate and deliberate drift control. |
| Rust policy execution | Table lookup, not a second handwritten policy. Every row is compared exhaustively against a conventional Boolean checker. Rust itself and its decoding/indexing are not formally verified. |
| Instrumented host | Actual in-memory public/vault sink writes and readback, with supplied principal slots, scoped grants, explicit channels, and sequential order. No model is invoked. The host and effect implementation are trusted to cover this closed experiment. |
| Signed transport | Existing v0 validated trace → independently issued Ed25519 authority receipt → verified replay types. One complete raw host experiment is wrapped as an observation; the old ordinal event policy is not used for semantic inference. |
| Semantic reader | Recomputes exact effects, local decisions, guarded decisions, sink readback, and collective witness; supplied reports confer no authority. Missing load-bearing evidence yields Inconclusive/Review. Contradictions and tampering yield Invalid. |
| Static browser reader | Pins fixture bytes with SHA-256 and recomputes finite semantics. It does not verify the signed receipt. No uploads/network requests; untrusted fields use `textContent`, with a script hash CSP. Interactive edits are labeled unsigned semantic controls. |

A valid host capture signature authenticates those recorded bytes relative to the
supplied public trust root. It does not prove the truth of the host's statements,
a principal's real-world identity, completeness outside the declared host, or
scoped authorization. Principal authentication is a supplied host-session fact;
grants separately bind principal, task, channel, and payload. The signed
missing-delegation fixture has valid capture authentication and known denial;
the signed missing-authority-evidence fixture has valid capture authentication
and Inconclusive knowledge. Safe executed effects can coexist with a Deny for a
requested action. Governance Permit/Deny/Review is separate from monitor
Safe/Violated/Inconclusive/Invalid.

The command exits 2 for invalid input or failed integrity checks. It exits 0 for
successfully checked evidence, including a witnessed violation or an explicitly
inconclusive case; inspect the structured governance and knowledge fields.
Unknown fields, duplicate keys (including escaped duplicates), over-budget JSON,
and noncontiguous order are rejected. Identifiers are presentation only after
consistent binding to the supplied principal slots. Renaming the display ID
changes signed bytes and requires a new receipt, but does not change semantics.

## Comparison, scope, and open work

[Spera](https://arxiv.org/abs/2603.15973) established the conjunctive-capability
non-composition framing already credited by the repository. [PCAS (v1)](https://arxiv.org/abs/2602.16708v1)
provides cross-agent dependency/provenance policies, and
[AgentSpec](https://arxiv.org/abs/2503.18666) provides runtime constraint
specification and enforcement.
[Wang et al., *When Safe Skills Collide*](https://arxiv.org/html/2606.00448v1)
separates static composition candidates, human-adjudicated risk and model-issued
tool actions in a simulated runtime. Its experiments study whether selected
capability combinations become tool-action attempts, including controls that
hold the request fixed and vary the installed skills. Legitimacy's experiment
invokes no model; it proves an execution refinement, a repair preserving the
same forbidden property for every finite request sequence, and the observations
needed for exact decisions in its declared model.

The full-context comparator here is a small conventional implementation of this
task, not a reproduction or benchmark of those systems. The contribution is the
checked executed-action connection, same-property constructive repair, and
concrete missing-observation witness. Neither composition risk nor an executed
composition demonstration is claimed as a first.

The observation bound is operational: the reachable safe contexts (neither public,
only A public, only B public) require different answers to the next public
fragment request. Any observation preserving every such answer must distinguish
all three; at least two fixed-width bits are necessary, and the two exposure bits
are sufficient. This is an exact-decision/selectivity bound. Merely maintaining
safety can require no exposure memory if every request is denied. Authentication
and delegation remain additional request evidence, outside this exposure-state
bit count. The partition/counting principle is classical; the contribution is
its checked specialization to the actual guard and reachable execution contexts.

The finite observation theorem does not establish C*, Shannon capacity, intent
recovery, or discovery of unmodeled channels. The broader B+ capability-scaling
question, scoped stability law, canonical shared-cliff weld, and positive kernel
remain the repository's narrative. Paper 03 remains independently citable.
Existing spectral results retain their stated modeled-carrier assumptions.

This release does not address dynamic principal discovery, Sybil resistance,
concurrent or partially ordered execution, hidden channels, arbitrary coalitions,
secret-sharing security, malicious host attestation, or learned agent behavior.
Generalizing exposure refinement to authenticated concurrent operations and
proving an implementation/compiler refinement are material next research steps.
The older genuine Codex capture/package transport blocker is separate; no
producer binding or historical receipt is weakened by this experiment.
