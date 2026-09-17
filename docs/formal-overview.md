# Formal overview

This is the detailed companion to the [project introduction](../README.md).
For a construction-by-construction evidence map, use the
[claim ledger](claim-ledger.md#read-the-evidence-in-five-minutes).
For source navigation across the full program, use the
[Lean and Rust module map](lean-module-architecture.md).
The sections below separate theorem hypotheses, concrete witnesses,
source-derived diagnostics and operational assumptions. Commands run
from the repository root; code-path citations are root-relative.

## The formal result: capability, tradeoffs and the kernel

The program connects three questions: which guarantees a governance rule can
jointly satisfy, what evidence a kernel must carry, and how removal-vulnerability
limits stability as modeled capability grows. The impossibility theorem is
independent of source extraction. The spectral characterization is proved for
its stated mathematical model. Their shared-cliff construction joins the two
on a specified carrier; the runnable audit supplies source-derived graph models.

The following sections state each result with its hypotheses and constructions.
The [claim ledger](claim-ledger.md) gives the detailed evidence status; the
[theorem spine](#theorem-spine) preserves the exact public Lean anchors.

## The forcing argument: why the kernel must declare a sacrifice

The wider theorem applies to a claimant-symmetric, scarce-coupled allocator
on an effective surface with a complete tail. Under these premises,
`symmetric_scarce_coupled_allocators_obstructed` proves that consistency,
solidarity and cross-claimant monotonicity cannot all hold
([statement](../lean/Legitimacy/Impossibility/SymmetricScarceCoupledObstruction.lean#L129)).
The class includes the median rule. The max-rule separator satisfies consistency
while sacrificing monotonicity, demonstrating why this wider conclusion is a
disjunction rather than a universal consistency failure
([separating theorem](../lean/Legitimacy/Impossibility/SymmetricScarceCoupledTightness.lean#L752)).

A narrower structural class forces stronger individual failures. Its reachable
pipeline theorem requires a transparent prefix, a scarce structurally
peer-relative allocator and a non-denying suffix:
`reachable_peer_relative_decisive_stage_obstructs_diagnostics`
(`lean/Legitimacy/Impossibility/PeerRelativeReachable.lean:103`).
The realistic median example belongs to the wider class and is excluded from
the narrower one. The [canonical manuscript](../papers/03-impossibility-theorem.md)
separates these tiers and their necessity witnesses.

The consequence for the kernel is direct and is itself a theorem. A kernel
deployed over that covered pipeline class cannot keep all three checks silently,
so it must *declare* which guarantees it gives up. That obligation is
`noUndeclaredSacrificeImplication`
(`lean/Legitimacy/Safety/KernelSafety/BinaryDecisionPipeline.lean:145`): once the
surface is live, the forced peer-relative sacrifices are declared rather than
hidden. The artifact does not *solve* the tension — it makes the unavoidable
tradeoff explicit, declared, and monitored, and emits a typed verdict plus a
declared-sacrifice certificate.

The narrow theorem also has an explicit escape witness. `nonPeerRelative_escapes_impossibility`
(`lean/Legitimacy/Results/NonPeerRelative.lean:385`) proves a non-peer-relative
escape exists, with a claimant-constant witness, and
`nonPeerRelative_allAxioms_escape_collapse`
(`lean/Legitimacy/Results/NonPeerRelative.lean:444`) gives the cost: recovering
the full axiom package collapses to threshold/constant behavior rather than
substantive multi-claimant allocation.

### A rank-dependent rule and the SDK graph diagnostic

The concrete theorem witness uses three requests. A threshold gate first
requires strength greater than 0.5. Among requests passing that gate, the peer
gate permits a request when at least half have strength no greater than its own.
The decision therefore depends on the other surviving requests, not only the
request it decides. Here are the two evaluations:

| Request | Original strength | Strength after A improves | Original verdict | New verdict |
| --- | --- | --- | --- | --- |
| A | 0.40 | 0.60 | Deny | Permit |
| B | 0.55 | 0.55 | Permit | Deny |
| C | 0.90 | 0.90 | Permit | Permit |

B passes the absolute threshold in both cases. Initially only B and C survive,
so one of two strengths is no greater than B's. Once A also passes, only one of
three is no greater: B fails the peer gate. Stronger evidence for A changed B's
decision without weakening B's evidence.
These are the rational strengths and rule from the
[formal composition witness](../lean/Legitimacy/Results/Composition.lean), not a
claim about allocating one human-review slot or about an upstream SDK policy.

The extracted Claude Agent SDK graph exhibits a different failure of the same
monotonicity diagnostic
(`claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity`): strengthening
a claim's own registration signal changes its decision from permit to terminal
escalation. This self-flip comes from the extractor's uniform
registration-escalation modeling convention (see Scope), not from recovering
SDK callback decision logic or discovering the synthetic scarce-slot scenario
inside the SDK. The rejection persists even when escalation is ranked as high
as permit
(`claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`).
The audit-agent emits an inspectable certificate for that extracted-model result.

### Why a frontier lab should care

The audit offers an inspectable test of a represented governance rule: which
property fails, a concrete witness where available, and the tradeoff an operator
would need to declare. Applying that test requires validating the representation
and deciding whether the property is appropriate. Intended priority overrides
can be non-monotone. The declared-sacrifice gate makes that choice explicit;
it does not yet distinguish intended priority from manipulation structurally.

## The kernel object

`LegitimacyKernel` (`lean/Legitimacy/Kernel/Unified.lean:29`) bundles a
governed system with proofs of five obligations (`IsLegitimacyKernel`,
`lean/Legitimacy/Kernel/Class.lean:91`): CERTIFIABLE, GOVERNANCE-OBSERVABLE,
CORRIGIBLE, COMPOSITIONAL SAFETY and NON-VACUOUS. These give checking evidence,
preserve decision-relevant observations and supervisory operations, require
safety within the modeled causal boundary, and exclude refusal, permanent
escalation and deadlock on the witnessed claim set.

Concrete inhabitants show different parts of that specification working:

| Construction | What is constructed | Simplified dimension |
| --- | --- | --- |
| [Threshold runtime kernel](../lean/Legitimacy/Safety/KernelSafety/GovernanceExamples.lean#L828) | `exampleThresholdRuntimeKernel` proves support and preservation of the degradation operation; `exampleThresholdAction_replay_changes_state` shows an actual state change. | Edgeless causal graph; the sole action is itself a supervisory operation. |
| [Boundary-exit kernel](../lean/Legitimacy/Kernel/BoundaryExitExamples.lean) | A two-stage graph with an edge from 0 to 1 and a proof of boundary-relative causal soundness. | Identity actions; no causal edge lies wholly inside the governed boundary. |
| [Minimal inhabitant](../lean/Legitimacy/Kernel/Examples.lean#L318) | `permitKernel` inhabits all five obligations and supplies a permit witness. | Always-permit behavior: the five axioms do not require decision selectivity. |

Corrigibility has an exact local meaning: the supervisory algebra survives every
finite sequence of modeled actions, derived from initial support and single-step
preservation ([definition and closure](../lean/Legitimacy/Kernel/Corrigible.lean#L516)).
This proves preservation; it does not construct a supervisor's ability to seize
control of an arbitrary deployed agent. Combining meaningful action dynamics
and causal governance in one useful runtime remains a separate obligation.

The bundle also rules out a specified hidden-authority pipeline through
`hiddenAuthorityExitPipeline_exits_kernel`
(`lean/Legitimacy/Impossibility/PeerRelativeClass/Escape.lean:309`).
Its causal-boundary condition alone does not imply safety for arbitrary action
lists. The [executed composition experiment](executed-composition-v1.md) earns
its finite-sequence execution guarantee separately. Semantic bridge contracts,
graph diagnostics and declared-sacrifice evidence add further obligations;
runtime evidence alone does not discharge them.

## The wider impossibility frontier

The single-surface forcing argument is the spine, but it is one face of a
broader obstruction lattice that builds clean in the same tree. Adding a third
*escalate* verdict does not escape the obstruction
(`three_valued_composition_inadmissibility`,
`lean/Legitimacy/Results/Composition.lean:536`), and a concrete
majority-quorum rule in the multi-principal model fails the Arrow triple
(`majorityQuorumRule_fails_arrow_triple`,
`lean/Legitimacy/Results/MultiPrincipal.lean:695`); both also appear in the
theorem spine below. The graph-diagnostic axioms' independence and tightness
lattice are paper-grade nuance covered in paper 03 / [`docs/claim-ledger.md`](../docs/claim-ledger.md).

## No-silent-degradation safety stack

A governed agent should not be able to quietly lose its guarantees as it keeps
running. A separate stateful safety stack machine-checks exactly this:
no-silent-degradation at the schedule level (including the nondeterministic and fair-infinite cases), with load-bearing countermodels, under the coverage hypothesis that every scheduled
action before the horizon is classified as kernel-governed or
certificate-emitting (`stateful_agent_schedule_safety`; see claim-ledger C33).
The same stack bounds self-modification:
`selfmod_escape_requires_indexed_override_removal_step`
(`lean/Legitimacy/Results/SelfModBoundary.lean:72`) decomposes any escape from
the governed region into an indexed override-removal step, and
`policy_lifecycle_no_silent_degradation`
(`lean/Legitimacy/SelfModificationLifecycle.lean:391`) carries the
no-silent-degradation guarantee across the policy lifecycle. Both results
decompose how an escape must proceed, through an indexed override-removal step, rather than claiming escape is impossible. See the
theorem spine and
[`docs/repository-context.md`](../docs/repository-context.md).

## Capacity and stability under capability scaling

For a fixed finite governance graph G, fixed signal s and positive tolerance δ,
the spectral model treats capability κ as the ability to target perturbations
down to scale δ/κ. A perturbation here is a change in the graph's verdict after
removing one node. Its largest magnitude is the **consistency vulnerability** cv.
**Spectral stability** means no such perturbation reaches the targeted scale.
This is an explicit mathematical model of exploitability, not a measured model
benchmark or a repeated-game equilibrium.

Within that model, stable equilibria exist at arbitrarily large capability
*exactly when* consistency vulnerability is zero
(`stackelberg_convergence_limit_iff_zero_consistency_vulnerability`). Any
positive vulnerability yields the finite, computable stability cliff
C*(G,s,δ) = δ/cv(G,s). The result identifies a structural condition a scaling
safety argument must address; applying its numbers to a deployment would require
justifying the graph, signal, tolerance and capability interpretation.

Two of the three spine rows below stand on their
own mathematics, independent of the impossibility theorem; the third is the
composition that ties the obstruction to the cliff over one shared
substrate. There is a sharp reciprocal threshold, the *critical capability* C*, below which the rule certifies and above which certification must fail, and the graph's connectivity, its *spectral gap*, contributes an explicit
lower bound: δ·gap/(signalRange·maxDeg) ≤ C* for graphs with at least two
vertices, under the theorem's positive tolerance, vulnerability, gap and degree hypotheses (including gap ≤ each
vertex degree and positive minimum degree after removal). The consistency
vulnerability that sets the threshold is not an ad-hoc score: it is
machine-checked equal to the classical gross-error sensitivity of the
graph's verdict map under single-node deletion, in the Cook/Hampel
influence-function lineage (`GovGraph.cv_eq_grossErrorSensitivity`), and the
stability characterization survives adversarially chosen monotone
capability trajectories
(`adversarial_stackelberg_unbounded_stability_iff_zero_consistency_vulnerability`).
The supporting identities are general in the graph size n: the K_{n+1} carrier's spectral gap is
exactly n+1, and the binary-channel capacity has the closed form log 2 − H2 (in
nats). These results stand on their own connected carriers, deliberately separate from the disconnected hook graphs the impossibility runs on, a boundary the Lean makes explicit. The named spine entries are:

| Spectral phase | Spine theorem | One-line role | Lean path |
| --- | --- | --- | --- |
| Capability threshold (standalone) | `C_star_exists` | Positive spectral vulnerability yields a sharp reciprocal critical threshold. | `lean/Legitimacy/Spectral/Capacity/CriticalCapability.lean:55` |
| Channel calibration (standalone) | `GovernanceChannel.channel_capacity_bounds_C_star` | A rational-budget calibration certificate bounds the same C*. | `lean/Legitimacy/Spectral/Channels/CStarChannelBridge.lean:551` |
| Shared scaling cliff (composition) | `capability_scaling_shared_cliff` | Not orthogonal: this is the composition that ties the peer-diagnostic obstruction (the peer-diagnostic obstruction is the first field of its result type) together with positive CV, C* threshold, channel bounds, reachability, and activation-gate fields over one shared substrate; inhabited by `exampleCapabilityScalingSubstrate`. | `lean/Legitimacy/Results/CapabilityScalingKernelSafety.lean:639` |

The first two rows are the standalone contribution; they do not derive the
impossibility from a spectral cliff. The third row is the opposite kind of
object: a composition that deliberately joins the obstruction to the spectral
fields over one shared substrate, which is why it is listed as a composition
rather than a standalone result.

## Worked extractions: the obstruction on real-agent graphs

The impossibility theorem does not depend on the extractor. This section
examines a complementary executable diagnostic on governance graphs extracted
from four agent frameworks. The Codex graph's monotonicity rejection is certified by `codexHooksGovernanceAdmissibilityRejectsMonotonicity`.
The table below gives the corresponding witnesses for the other source-derived
graphs under the same modeling convention; OpenClaw trips a different check.
That demonstrates discrimination within these fixtures, not discovery of the
synthetic theorem mechanism in each upstream implementation. A Lean theorem
packages the four extracted fixtures as concrete verifier-target evidence. Each
row is a statement about an extracted graph model, not a measurement of the live
product and not a ranking of the upstream project.

| Source framework | Extracted graph | Source surface | What the audit shows | Lean witness |
| --- | --- | --- | --- | --- |
| Codex | `examples/graphs/codex-graph.json` | OpenAI `codex-rs/hooks` extracted slice | 16 nodes / 8 edges; exhibits a monotonicity failure [extracted-graph fixture; extractor unverified] | `codexHooksGovernanceAdmissibilityRejectsMonotonicity` |
| Claude Agent SDK | `examples/graphs/claude-agent-sdk-graph.json` | MIT Python SDK hook protocol extracted slice | 22 nodes / 8 edges; exhibits a monotonicity failure [extracted-graph fixture; extractor unverified] | `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity` |
| CrewAI | `audits/leaderboard/crewai-graph.json` | MIT test-source frozen fixture | 5 nodes / 1 edge; exhibits a monotonicity failure [extracted-graph fixture; extractor unverified]; nonvacuity passes review-required | `crewAIHooksGovernanceAdmissibilityRejectsMonotonicity`; `crewAIHooksGovernanceAdmissibilityPassesNonvacuityReviewRequired` |
| OpenClaw | `audits/leaderboard/openclaw-graph.json` | Public open-source agent runtime, `github.com/openclaw/openclaw` | 53 nodes / 16 edges; fails a different check, nonvacuity [extracted-graph fixture; extractor unverified] | `openClawInfraNonvacuityCheckFails` |

The three monotonicity rows are one obstruction demonstrated on three distinct
extracted graphs: Codex, the Claude Agent SDK, and CrewAI each fail monotonicity
under the same registration-escalation modeling convention: one proven obstruction recurring across structurally different real-derived surfaces.
The AutoGen singleton fixture and the AI-Control protocol fixtures pass with
`AuditVerdict.legitimate`, so the audit discriminates rather than rejecting every
input. The Codex lane also carries the program's full detect-price-repair arc, every
stage a named theorem on the derived carrier: the audit detects the monotonicity
failure (`codexHarness_stage1_detects_monotonicity_failure`), the spectral layer
prices it (`codexHarnessDerived_cv_value`, `codexHarnessDerived_C_star_value`) and
proves the capability-scaling cliff
(`codexHarnessDerived_stage2_stackelberg_eventual_instability`), and the explicit
adjudication repair removes it (`codexHarness_repaired_cv_value`,
`codexHarness_stage4_threshold_removed_derives_finite_audit`); OpenClaw's license and provenance are recorded in
[`audits/fixtures/LICENSES.md`](../audits/fixtures/LICENSES.md).

The graph-audit CLI has a narrower binary-first interface: it emits JSON
bundles for Codex CLI, Claude Agent SDK, and the public Claude Code governance
surface, each with a Stage 2 C* carrier derived from the committed extracted
graph and reported separately from the diagnostic.
The bundle schema, per-lane examples, and load-bearing C*-carrier caveats are in
[`docs/audit-bundle-schema.md`](../docs/audit-bundle-schema.md).

## What The Audit Decides

The audit connects source-extracted hook graphs to the repository's legitimacy
kernel substrate:

- `ClaimProfile` metadata carries structured fields such as hook registration,
  permission decisions, and review outcomes.
- Structural `fieldEq` gates expose exact-match and threshold decisions in the
  extracted graph.
- Diagnostic projections run graph consistency, solidarity, monotonicity,
  strategyproofness, and kernel-side obligations including certifiability,
  observability, corrigibility, compositional safety, and non-vacuity.
- The activation evidence records the monitored `DeclaredSacrifice` certificate
  shape that would be required before live promotion.

The source-walked fixtures are derived from public material. Codex reads a
formal slice of OpenAI `codex-rs/hooks`; Claude Agent SDK reads the
MIT-licensed `claude-agent-sdk-python` hook surface; CrewAI and OpenClaw are
disclosed in the leaderboard fixture records. Claude Code is represented only
through public hook, settings, and slash-command governance metadata; the repo
does not redistribute proprietary Claude Code handler implementation.

## Calibration Notes

The formal guarantees govern the extracted `GovernanceGraph` model. Source-to-
graph extraction is part of the trusted base and is guarded by byte-stable
fixtures, parity tests, provenance records, committed graph snapshots, and
binding regressions. The many `native_decide` fixture/verdict proofs also add
Lean's compiled evaluator and `Lean.ofReduceBool` to the trust base; this is
weaker than kernel reduction alone and is tracked by `scripts/verify.sh`.

In extract mode, theorem fields are cited only when the normalized extracted
graph hash matches the committed finite fixture for that lane. Divergent
extractions become diagnostic-only and do not carry theorem-backed C* fields.
Replay mode is explicit: extract bundles hash the normalized in-memory graph;
replay bundles hash the raw checked-in graph JSON bytes.

The Stage 2 C* carrier provenance is graph-derived for all three binary lanes.
Codex, Claude Agent SDK, and Claude Code use 16-, 22-, and 31-node derived
carriers obtained from the committed extracted graphs by symmetrizing their
pass-through topologies. These carriers are disconnected, and the SDK/Code
fixtures retain isolated schema vertices where the extracted graphs have them.

## Scope

The line between what is machine-checked and what is not is firm. The **Lean
theorems are machine-checked** over formal `GovernanceGraph` and kernel models: the kernel axioms, the impossibility forcing argument, the wider impossibility frontier, the safety stack, the semantic-kernel bridge, and the standalone spectral/capacity results. The **Rust source-to-graph extractor is not
verified**: it is part of the trusted base (the unverified component you must trust), guarded by byte-stable fixtures, parity tests, and committed graph snapshots. So a result such as "Codex hooks
reject monotonicity" (`codexHooksGovernanceAdmissibilityRejectsMonotonicity`) is
theorem-backed only once the emitted graph hash matches a committed finite
fixture, and even then it is a claim about *that extracted graph model*, not a
proved claim about live Codex behavior. The monotonicity rejection (`codexHooksGovernanceAdmissibilityRejectsMonotonicity`) is a real and robust property of that extracted model: it survives the review-required lattice, and the impossibility theorem itself does not depend on the extractor at all. What the extractor contributes is a uniform modeling convention: every hook-registration-bearing function is given a `hook_registration ≥ 1 → escalate` gate, exercised by the audit's synthetic probe corpus, rather than the decision being recovered from each upstream callback's own logic. The impossibility itself is sharp:
it holds for reachable, structural, scarce, peer-relative decisive stages under
transparent-prefix and non-denying-suffix hypotheses, and paper 03 shows each of
those hypotheses is necessary. For the complete
boundary map, read [`FRAMEWORK-LIMITS.md`](../FRAMEWORK-LIMITS.md).

The reflective layer is honestly staged, not finished. For the production
self-audit verdict, the reflective (Löb-style) layer does not earn the verdict;
it reflects the already-evaluated certificate in a subject-relative modal box
under a threshold-selected modal target, with the internal-soundness premise
assumed rather than constructed. The ASI-signature derivation of spectral
well-connectedness is **open**: the signature under-determines
well-connectedness, and the complete-rank theorem carries a vestigial `_hasi`
conjunct, so it is not advertised as derived. These are tracked as staged work,
not surfaced as done.

## Boundaries And Gates

For the complete boundary map, read [`FRAMEWORK-LIMITS.md`](../FRAMEWORK-LIMITS.md)
before treating any audit row as a broader safety claim.
For the maintained subsystem ledger and graph-carrier seam map, read
[`docs/lean-module-architecture.md`](../docs/lean-module-architecture.md).

## Theorem Spine

The headline obstruction is `symmetric_scarce_coupled_allocators_obstructed`
(`lean/Legitimacy/Impossibility/SymmetricScarceCoupledObstruction.lean:129`):
the median-inclusive class cannot jointly satisfy consistency, solidarity and
cross-claimant monotonicity. The max-rule separator shows why the conclusion
does not force consistency failure alone. See the [forcing argument](#the-forcing-argument-why-the-kernel-must-declare-a-sacrifice)
for the exact hypotheses and witnesses.

The typed package below retains the narrower reachable-stage specialization.
It does not yet package a concrete application of the wider theorem; the
specialization's stronger structural hypotheses are not the headline's scope.

The packaged spine collects concrete applications of named Lean statements
that connect the artifact, in spine order: the kernel object, its forcing argument, the
activation gate, the semantic bridge, the standalone spectral layer, and the
wider-frontier rows. Supporting lemmas, fixtures, and evidence artifacts are
mapped in [`docs/repository-context.md`](../docs/repository-context.md). All ten
unique anchors in this table and the standalone spectral table are packaged by
`spineFootprint` (`lean/Legitimacy/Results/SpineFootprint.lean:221`) together
with concrete witnesses for every load-bearing premise; the typed manifest is
the explicit maintenance boundary for future public-spine rows.

| Role | Spine theorem | One-line role | Lean path |
| --- | --- | --- | --- |
| Kernel object | `LegitimacyKernel` | The bundled five-axiom kernel structure over a shared governed system; inhabited by `permitKernel`. | `lean/Legitimacy/Kernel/Unified.lean:29` |
| Reachable-stage specialization | `reachable_peer_relative_decisive_stage_obstructs_diagnostics` | Under the narrower structural premises, the reachable decisive stage cannot satisfy all diagnostics. | `lean/Legitimacy/Impossibility/PeerRelativeReachable.lean:103` |
| Activation gate | `noUndeclaredSacrificeImplication` | Interface implication: the complete-surface activation gate projects the deployment direction from the compatibility iff, so the kernel must declare its sacrifice. | `lean/Legitimacy/Safety/KernelSafety/BinaryDecisionPipeline.lean:145` |
| Semantic bridge | `semanticKernel_iff_runtime_diagnostic_spectral_layers` | Compatibility unfolding: the strengthened semantic-kernel contract decomposes into runtime, diagnostic, and spectral conjuncts. | `lean/Legitimacy/Results/SemanticBridge.lean:74` |
| Three-valued frontier | `three_valued_composition_inadmissibility` | A third (escalate) verdict does not escape the obstruction; parametric via `three_valued_escalationPolicyWitness_composition_inadmissibility`. | `lean/Legitimacy/Results/Composition.lean:536` |
| Multi-principal frontier | `majorityQuorumRule_fails_arrow_triple` | The majority-quorum witness fails the Arrow triple; pairwise witnesses are packaged by `multi_principal_pairwise_achievability_with_majorityQuorum_obstruction`. | `lean/Legitimacy/Results/MultiPrincipal.lean:695` |
| Safety stack | `stateful_agent_schedule_safety` | No-silent-degradation schedule-level safety over the reachable state space. | `lean/Legitimacy/Safety/KernelSafety/StatefulScheduleSafety.lean:179` |
| Spectral composition | `capability_scaling_shared_cliff` | Composition package that ties the peer-diagnostic obstruction together with positive CV, C* threshold, channel bounds, reachability, and activation-gate fields over one shared substrate (the peer-diagnostic obstruction is the first field of its result type); inhabited by `exampleCapabilityScalingSubstrate`. | `lean/Legitimacy/Results/CapabilityScalingKernelSafety.lean:639` |

The spine includes a few wrapper-shaped statements. `capability_scaling_shared_cliff`
packages earlier lemmas such as `peer_surface_forces_diagnostic_obstruction`,
`peer_surface_forces_claimant_interaction_positive_cv`, and the channel/C*
bridge fields. It is a theorem about the constructed canonical claimant-interaction
lift, definitionally `uniK5` with fixed signal `sig5`, not a per-input-graph
spectral law. The forced `cv` on that lift is the constant `3/4`. Separate
worked lanes compute graph-derived carriers; the Codex lane has `cv = 1` and
`C* = 1/10`. Its substrate domain is populated by the worked instance
`exampleCapabilityScalingSubstrate`
(`lean/Legitimacy/Results/CapabilityScalingKernelSafety.lean:597`), so this
composition is true over a nonempty capability-scaling deployment class.
`noUndeclaredSacrificeImplication` is the operator-facing
direction of `completePeerRelativeSurface_live_forces_sacrificesDeclared`.
`semanticKernel_iff_runtime_diagnostic_spectral_layers` is the compatibility
name for the unfolded semantic-kernel decomposition; it is not a derivation of
diagnostic or spectral evidence from runtime evidence alone.

## Broader CLI Surface

Alongside the composition experiment and graph-audit CLI, the repository exposes
general extraction, protocol and certificate commands.

The fixture example below explicitly uses heuristic extraction. Its output is
an empirical diagnostic, and can misinterpret source literals. The headline SDK
audits use `--mode theorem-backed`, for example
`legitimacy extract examples/claude-agent-sdk-fixture --mode theorem-backed`.
That mode still has the [declared extraction boundary](../docs/extractor-boundary.md).

```bash
cargo run --release --bin legitimacy -- extract tests/fixtures --mode heuristic --emit-graph /tmp/sample.graph.json
cargo run --release --bin legitimacy -- audit-graph --graph /tmp/sample.graph.json --claims tests/fixtures/sample_governance_claims.jsonl
cargo run --release --bin legitimacy -- compile examples/claude-agent-sdk-permissions.rule.toml
cargo run --release --bin legitimacy -- paradox examples/claude-agent-sdk-hooks.rule.toml
cargo run --release --bin legitimacy -- certify examples/claude-agent-sdk-permissions.rule.toml --claimant Read --outcome 1
cargo run --release --bin legitimacy -- protocol init examples/protocol-gate-graph.graph.toml > state.compiled.json
cargo run --release --bin legitimacy -- protocol measure state.compiled.json > state.measured.json
cargo run --release --bin legitimacy -- protocol activate state.measured.json > state.live.json
cargo run --release --bin legitimacy -- protocol status state.live.json
cargo run --release --bin legitimacy -- protocol audit state.live.json
```

Installed-binary form:

```bash
legitimacy audit-graph --graph /tmp/sample.graph.json --claims tests/fixtures/sample_governance_claims.jsonl --claims-provenance fixture --review-overlay tests/fixtures/sample_governance_review_overlay.json
legitimacy protocol init examples/protocol-gate-graph.graph.toml > state.compiled.json
legitimacy protocol measure state.compiled.json > state.measured.json
legitimacy protocol activate state.measured.json > state.live.json
legitimacy protocol status state.live.json
legitimacy protocol audit state.live.json
```

Use `--claims-provenance observed-runtime` for a corpus captured from actual
execution. This is a caller-declared label; it does not authenticate the corpus.

Protocol `state.*.json` files are trusted operator-local checkpoints.
`protocol audit` checks the certificate hash chain's internal consistency;
`certificate_chain_valid: true` does not authenticate the state or validate its
measurement values. See the [protocol state trust contract](../docs/protocol-state-trust.md).

`compile`, `certify`, `paradox`, and `sacrifice` write a local SQLite ledger.
Its directory must be writable; its location depends on the working directory
([ledger path rules](../docs/operational-gates.md#ledger-location-and-write-access)).

`audit-graph` returns zero when it successfully produces a diagnostic report,
including reports that reject the graph; inspect the verdict and LIVE blockers.
Its exit status is not an acceptance certificate. Graph `CORRIGIBLE: SUPPORTED`
checks the constructed supervisory override projection; it does not establish
that a deployed agent obeys intervention. Observable determinacy is skipped for
graphs above the current exhaustive limit of ten nodes, including the four
headline graphs; skipped checks prevent protocol compilation. The
[graph-to-kernel limits](../FRAMEWORK-LIMITS.md#2-auditsubject-bridge-coverage-is-partial)
distinguish these diagnostics from the kernel's axioms.

The CLI's raw graph `cv` and the worked spectral carrier's `cv` are different
quantities. For Codex, the raw fixture reports `16/1`, while the derived carrier
has `cv = 1` and `C* = 1/10`; see the
[carrier boundary](../docs/audit-bundle-schema.md#capability-threshold).
A bare exported graph carries
no source dependency analysis, so the report marks that boundary as unassessed.
Use `--source-dir tests/fixtures` instead of `--graph /tmp/sample.graph.json` to
include source extraction and dependency evidence.

Canonical policy examples use `.rule.toml` and `.graph.toml` files under
[`examples/`](../examples/).

## Build Dependencies

The Lean build uses Mathlib plus three public Apache-2.0 helper repositories
fetched by Lake git URL, not vendored in this tree:

| Lake dependency | Repository | Pinned revision | Role |
| --- | --- | --- | --- |
| `channel-capacity` | `https://github.com/abenenson/channel-capacity.git` | `fdb4d1d18dba3e408fbe1969e09a4da3da2e313e` | Shannon channel-capacity primitives and information-theory lemmas, consumed by the in-tree spectral spine theorems `channel_capacity_bounds_C_star` and `capability_scaling_shared_cliff`. |
| `compact-spectral` | `https://github.com/abenenson/compact-spectral.git` | `72cd62dbdd4c397d26fc0c5777d60fea2211e938` | Compact spectral substrate used by paper 04. |
| `godel-loeb` | `https://github.com/abenenson/godel-loeb` | `60a7a1098c34dbd0ee0833dde94ef5315f22d472` | Reflective substrate used by paper 03. |

A cold-cache `lake build` reproduces the Lean build from those pinned commits.
For the production self-audit verdict specifically, the reflective layer does
not earn the verdict; it reflects the already-evaluated certificate in a
subject-relative modal box.

## References for deeper review

| Question | Entry point |
| --- | --- |
| What is the kernel object? | [`papers/02-semantic-legitimacy-kernels.md`](../papers/02-semantic-legitimacy-kernels.md) and the [theorem spine](#theorem-spine). |
| Why is the kernel forced to declare a sacrifice? | [`papers/03-impossibility-theorem.md`](../papers/03-impossibility-theorem.md). |
| What subsystem map should reviews consult first? | [`docs/lean-module-architecture.md`](../docs/lean-module-architecture.md), the maintained Lean/Rust subsystem ledger and graph-carrier map. |
| What are the executable audit results? | [`audits/leaderboard/LEADERBOARD.md`](../audits/leaderboard/LEADERBOARD.md), `scripts/reproduce-audit.sh`, and [`docs/audit-bundle-schema.md`](../docs/audit-bundle-schema.md). |
| Where does the claim stop? | [`FRAMEWORK-LIMITS.md`](../FRAMEWORK-LIMITS.md), [`docs/boundary.md`](../docs/boundary.md), [`docs/extractor-boundary.md`](../docs/extractor-boundary.md), and the evidence map in [`docs/claim-ledger.md`](../docs/claim-ledger.md). |
| How do extractor decisions and parity surfaces line up? | [`docs/governance-decision-lattice.md`](../docs/governance-decision-lattice.md), [`docs/rust-lean-governance-property-parity.md`](../docs/rust-lean-governance-property-parity.md), and [`docs/extractor-ast-theorem-witness.md`](../docs/extractor-ast-theorem-witness.md). |
| What are the current audit-boundary design notes? | [`docs/degenerate-behavior.md`](../docs/degenerate-behavior.md), [`docs/production-self-audit-loeb-design.md`](../docs/production-self-audit-loeb-design.md), and [`docs/pillar2-governance-audit-capacity-design.md`](../docs/pillar2-governance-audit-capacity-design.md). |
| How do I cite it? | [`papers/CITATION.bib`](../papers/CITATION.bib). Rendered PDFs are attached to GitHub releases starting with `v1.0.0`; arXiv links are added when identifiers are assigned. |

## Papers

The [paper index](../papers/README.md) provides abstracts and reading routes:
02 introduces the kernel, 03 proves the impossibility results, 04 develops
spectral scaling, 05 describes structural audits, and 06 compares adjacent
research. Paper 01 is the general-audience essay. The numbers are stable
identifiers rather than a required reading order.

### Suggested reading order

For proof review, begin with paper 03; for the governing object, begin with
paper 02. Use paper 06 for contribution-specific prior-art comparisons.
