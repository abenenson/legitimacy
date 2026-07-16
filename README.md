# Legitimacy: A Machine-Checked Kernel for the Governance Layer of AI Agents


[![CI (manual/tag mirror)](https://github.com/abenenson/legitimacy/actions/workflows/ci.yml/badge.svg)](https://github.com/abenenson/legitimacy/actions/workflows/ci.yml)


A chatbot can be behaviorally aligned. An agent that allocates tool access,
memory, escalation rights, review bandwidth, or permission to act is running
an institution, and institutions face a question alignment training does not
answer: **which governance rules keep certifying as the agent's capability
grows without bound?**

This repository machine-checks an answer, in Lean 4, over represented
governance graphs. A graph admits stable equilibria at unbounded modeled
capability *exactly when* its consistency vulnerability is zero
(`stackelberg_convergence_limit_iff_zero_consistency_vulnerability`). Any
positive vulnerability yields a finite, computable stability cliff,
C*(G,s,δ) = δ/cv(G,s).

That vulnerability is not merely an implementation defect. On reachable
scarce, peer-relative pipelines, a classical Arrow/Young-lineage
impossibility forces the governing rule to sacrifice one of consistency,
solidarity, or cross-claimant monotonicity; on the rule's
canonical claimant-interaction lift (definitionally `uniK5` with fixed signal
`sig5`), the same structure forces positive consistency vulnerability. The
theorem `capability_scaling_shared_cliff` carries the
forced sacrifice and the capability cliff on one machine-checked substrate,
and the **legitimacy kernel** turns that unavoidable sacrifice into a
declared, monitored certificate.

The concrete failure behind the forced sacrifice: when one request gathers
stronger evidence and takes the one scarce human-review slot, a second
request that would have been permitted is now denied. Making one decision
more correct silently broke another, and the kernel proves this is
unavoidable on scarce, peer-relative surfaces. The same diagnostic is wired
to an executable extractor over source-extracted graph models of real agent
hook surfaces (Codex, the Claude Agent SDK).

**Start here.** The papers: [the kernel object](papers/02-semantic-legitimacy-kernels.md), [the verified impossibility theorem](papers/03-impossibility-theorem.md), and [capacity and stability under unbounded capability](papers/04-spectral-scaling.md). The full set is in [papers/](papers/). Reproduce the audits with `scripts/reproduce-audit.sh`; run the canonical gate with `bash scripts/verify.sh`. The audit, worked on graphs extracted from real agent frameworks, is in [Worked extractions](#worked-extractions-the-obstruction-on-real-agent-graphs). The Lean substrate carries zero `sorry`, `admit`, or first-party `axiom`, and a single name (`spineFootprint`) conjoins the seven spine theorems.

![The forcing triangle: consistency, solidarity, and cross-claimant monotonicity around a reachable scarce allocation stage](docs/figures/impossibility-triangle.svg)

*The forcing triangle. On a reachable scarce allocation stage (claimant-symmetric, finite-estate-coupled, with an admissible over-subscribed profile), consistency, solidarity, and cross-claimant monotonicity cannot all hold (`symmetric_scarce_coupled_allocators_obstructed`). The kernel records which one is declared sacrificed.*

**For AI-safety readers.** Behavioral alignment (RLHF, Constitutional AI, debate, AI Control) shapes the model's policy; this program audits the *scaffolding around it*: the rule layer that allocates tool access, memory, escalation, and review, which is usually a pile of unverified scripts. Three machine-checked results, one per paper, and the composition that ties them together:

| Paper | Result | Lean anchor |
| --- | --- | --- |
| 04 | A represented governance graph stays stable at unbounded capability exactly when its consistency vulnerability is zero; positive vulnerability gives a finite, computable stability cliff. | `stackelberg_convergence_limit_iff_zero_consistency_vulnerability` |
| 03 | A reachable scarce peer-relative governance stage cannot keep consistency, solidarity, and cross-claimant monotonicity at once, so it must declare a sacrifice. | `reachable_peer_relative_decisive_stage_obstructs_diagnostics` |
| 03+04 | The same peer-relative obstruction forces positive consistency vulnerability on the canonical claimant-interaction lift (definitionally `uniK5` with fixed signal `sig5`), so the forced sacrifice and the capability cliff are carried by one substrate. | `capability_scaling_shared_cliff` |
| 02 | The legitimacy kernel decomposes into a runtime kernel plus an explicit bridge contract, and is inhabited by a concrete instance. | `isSemanticLegitimacyKernel_iff_runtime_and_bridge` |

The audit discriminates: it clears the AutoGen singleton and the five AI-Control fixtures, and the same diagnostic bites on the graphs extracted from Codex, the Claude Agent SDK, and CrewAI. The worked Codex lane runs the full arc on the extracted Codex graph model: detect the monotonicity failure, price the capability-scaling cliff (`cv = 1`, `C* = 1/10`), and repair it to `cv = 0`, every stage a named theorem over the represented graph model.

The shift is concrete: we are moving from chatbots to agents, and agents make *structural* decisions: which tool calls are allowed, what is written to memory,
when a request is escalated to a human, and which of several competing requests
gets the scarce review slot. Those are governance decisions, and this repository
studies them with the tools built for studying institutions: social choice and
fair allocation.

## The kernel object

What makes a governance rule *legitimate* here is not that its verdicts are
correct, but that the rule can be **checked rather than trusted**: an outside party can confirm it allocates authority coherently across the cases it
will face, instead of taking it on faith. The center of the artifact is a
positive object, not a prohibition. The
`LegitimacyKernel` structure
(`lean/Legitimacy/Kernel/Unified.lean:29`) bundles a typed governance system
with machine-checked proofs that **five axioms** hold over it
(`IsLegitimacyKernel`, `lean/Legitimacy/Kernel/Class.lean:91`):
certifiability, observability, corrigibility, compositional safety, and
non-vacuity. In plain terms: verdicts come with checkable witnesses
(*certifiability*); decision-relevant state survives audit (*observability*);
authorized supervisors can intervene without breaking the rule (*corrigibility*);
locally-safe steps do not compose into a global violation (*compositional
safety*); and the rule governs a nonempty claim set with a genuine permit
witness while excluding refuse-everything, permanent escalation, and deadlock
(*non-vacuity*). The current five-axiom kernel does not require decision
selectivity: the honest always-permit `permitKernel`
(`lean/Legitimacy/Kernel/Examples.lean:318`) inhabits the bundle, and its trace
satisfies non-vacuity (`honest_permit_all_trace_satisfies_nonvacuous`,
`lean/Legitimacy/Impossibility/PeerRelativeClass/Escape.lean:322`). What the
kernel polices instead is unobservable authority: `hiddenAuthorityExitPipeline_exits_kernel`
(`lean/Legitimacy/Impossibility/PeerRelativeClass/Escape.lean:309`) proves that
such a pipeline exits the kernel. The five axioms are tied together with the
rest of the public spine by `spineFootprint`
(`lean/Legitimacy/Results/SpineFootprint.lean:28`), a single Lean statement
that conjoins seven named spine theorems: the spectral capacity threshold and
channel-capacity bound, the capability-scaling substrate and its shared cliff,
the impossibility forcing argument, the activation gate, and the
semantic-kernel bridge.

A legitimate kernel is therefore a compiled object: runtime obligations, graph
diagnostics, extraction provenance, and monitored tradeoff declarations,
packaged as evidence that a governance rule can be inspected rather than trusted.
That is the difference from a scalar alignment score or a natural-language
constitution: both ask for trust; a kernel offers a check. When a check fails it
does not emit a scalar verdict but a typed certificate naming the failure class (unmodeled edge, bypass path, hidden override, source-evidence gap, or semantic-bridge failure), so a reviewer learns not only *that* the rule-layer
failed but *what kind* of failure occurred.

## The forcing argument: why the kernel must declare a sacrifice

The impossibility theorem is the kernel's forcing argument, not a separate
headline. Take a recognizable class of governance decisions: those where one request's outcome depends on which other requests are present (*peer-relative*) and the allocated resource is *scarce*. There, three reasonable structural checks (consistency, solidarity, monotonicity) cannot all hold at once. The canonical
statement is `reachable_peer_relative_decisive_stage_obstructs_diagnostics`
(`lean/Legitimacy/Impossibility/PeerRelativeReachable.lean:103`), machine-checked
in Lean 4 (Mathlib, zero `sorry`/`admit`/first-party `axiom`).

The consequence for the kernel is direct and is itself a theorem. A kernel
deployed on a scarce, peer-relative surface cannot keep all three checks
silently, so it must *declare* which one it gives up. That obligation is
`noUndeclaredSacrificeImplication`
(`lean/Legitimacy/Safety/KernelSafety/BinaryDecisionPipeline.lean:145`): once the
surface is live, the forced peer-relative sacrifices are declared rather than
hidden. The artifact does not *solve* the tension — it makes the unavoidable
tradeoff explicit, declared, and monitored, and emits a typed verdict plus a
declared-sacrifice certificate.

Peer-relativity is the exact obstruction. `nonPeerRelative_escapes_impossibility`
(`lean/Legitimacy/Results/NonPeerRelative.lean:385`) proves a non-peer-relative
escape exists, with a claimant-constant witness, and
`nonPeerRelative_allAxioms_escape_collapse`
(`lean/Legitimacy/Results/NonPeerRelative.lean:444`) gives the cost: recovering
the full axiom package collapses to threshold/constant behavior rather than
substantive multi-claimant allocation.

### How it breaks: the Claude Agent SDK tool gate

Picture an agent deciding whether to permit a shell command or escalate it for
human review. Review capacity is finite — say, one slot this cycle. That is the
*scarcity*. The gate weighs all pending requests together to decide who gets the
slot. That is *peer-relativity*. Now suppose Request A gathers *stronger*
evidence and is plainly worth approving. Strengthening A consumes the scarce
review capacity, and Request B, which would have been permitted, is instead forced into escalation for human review, which on the binary decision surface
the scarce-allocation lens records as **Deny** (FRAMEWORK-LIMITS §2a).
Strengthening one correct decision silently changed the outcome of another.
That is the structural failure the forcing argument isolates for scarce,
peer-relative governance: monotonicity cannot survive scarcity here. This
scarce-slot story is the impossibility theorem's own mechanism, staged on
its synthetic pipeline. The extracted Claude Agent SDK hook graph exhibits a
milder failure of the same diagnostic
(`claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity`): a
self-flip in which strengthening a claim's own registration signal lowers
its decision from permit to terminal escalation, triggered through the
extractor's uniform registration-escalation modeling convention (see Scope)
rather than recovered from SDK callback logic. The rejection is robust
rather than a rank-encoding artifact; it persists when escalation is ranked
as high as permit
(`claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`),
and the audit-agent surfaces it as an explicit certificate instead of a
silent production surprise.

### Why a frontier lab should care

A behavioral safety case argues the model resists subversion. It says nothing
about whether the scaffolding around the model (hooks, routing, tool gates, escalation policy) is structurally coherent, and that scaffolding is where
authority is actually allocated. Alignment effort goes into the weights
(Constitutional AI, RLHF, AI Control); the layer that decides which tool call
runs, what is written to memory, and who gets the scarce review slot is usually
a pile of unverified scripts. This work gives that layer a typed kernel object,
a small set of machine-checked theorems about what it can and cannot guarantee,
and an executable check that runs against source-extracted graph models of real agent hook surfaces
(Claude Agent SDK, Codex CLI) and a public-doc-derived Claude Code governance
surface. On those extracted graphs, the theorem-backed diagnostic is the
monotonicity rejection (`claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity`, with Codex CLI and Claude Code counterparts).

The rest of this document is the scope, the evidence, and the open frontier
behind two claims that share one substrate: a legitimate governance kernel on a scarce, peer-relative surface is forced to declare a sacrifice, and the same structure prices out as a finite, computable capability cliff.

## The wider impossibility frontier

The single-surface forcing argument is the spine, but it is one face of a
broader obstruction lattice that builds clean in the same tree. Adding a third
*escalate* verdict does not escape the obstruction
(`three_valued_composition_inadmissibility`,
`lean/Legitimacy/Results/Composition.lean:519`), and when several principals
govern the same surface the Arrow obstruction transports
(`majorityQuorumRule_fails_arrow_triple`,
`lean/Legitimacy/Results/MultiPrincipal.lean:695`); both also appear in the
theorem spine below. The graph-diagnostic axioms' independence and tightness
lattice are paper-grade nuance covered in paper 03 / [`docs/claim-ledger.md`](docs/claim-ledger.md).

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
[`docs/repository-context.md`](docs/repository-context.md).

## Capacity and stability under capability scaling

This layer carries the landing claim's first half: what happens to a
governance rule as the agent it governs grows more capable, and where
certification must fail. Two of the three spine rows below stand on their
own mathematics, independent of the impossibility theorem; the third is the
composition that ties the obstruction to the cliff over one shared
substrate. There is a sharp reciprocal threshold, the *critical capability* C*, below which the rule certifies and above which certification must fail, and C* is bounded below by the
governance graph's own connectivity, its *spectral gap*. The consistency
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
boundary map, read [`FRAMEWORK-LIMITS.md`](FRAMEWORK-LIMITS.md).

The reflective layer is honestly staged, not finished. For the production
self-audit verdict, the reflective (Löb-style) layer does not earn the verdict;
it reflects the already-evaluated certificate in a subject-relative modal box
under a threshold-selected modal target, with the internal-soundness premise
assumed rather than constructed. The ASI-signature derivation of spectral
well-connectedness is **open**: the signature under-determines
well-connectedness, and the complete-rank theorem carries a vestigial `_hasi`
conjunct, so it is not advertised as derived. These are tracked as staged work,
not surfaced as done.

## Verify

```bash
scripts/reproduce-audit.sh
bash scripts/verify.sh
```

`scripts/reproduce-audit.sh` rebuilds `target/release/legitimacy-audit-agent`,
runs the Codex CLI, Claude Agent SDK, and public Claude Code surface lanes, and
writes structured rejection bundles under `target/audit-agent-reproduction/`.
Rejected verdicts intentionally exit non-zero when run directly; the
reproduction script treats those rejections as the expected result.

On a fresh clone, `lake exe cache get` (run inside `lean/`, and invoked
automatically by `scripts/verify.sh`) fetches prebuilt Mathlib artifacts and
turns the first Lean build from hours into minutes.

`bash scripts/verify.sh` is the canonical fast gate. It checks Rust formatting,
clippy, tests, Lean build, zero Lean `sorry`/`admit`/first-party `axiom`, fixture
parity, public documentation, publication polish, and the Lean `lake build`
gate. GitHub Actions is a manual and tag-time mirror of these repository-local
checks, not a per-commit gate. Component gates are in
[`docs/operational-gates.md`](docs/operational-gates.md).

Current Lean gate: `lake build` completes cleanly.

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

## What To Inspect First

| Question | Entry point |
| --- | --- |
| What is the kernel object? | [`papers/02-semantic-legitimacy-kernels.md`](papers/02-semantic-legitimacy-kernels.md) and the theorem spine below. |
| Why is the kernel forced to declare a sacrifice? | [`papers/03-impossibility-theorem.md`](papers/03-impossibility-theorem.md). |
| What subsystem map should reviews consult first? | [`docs/lean-module-architecture.md`](docs/lean-module-architecture.md), the maintained Lean/Rust subsystem ledger and graph-carrier map. |
| What are the executable audit results? | [`audits/leaderboard/LEADERBOARD.md`](audits/leaderboard/LEADERBOARD.md), `scripts/reproduce-audit.sh`, and [`docs/audit-bundle-schema.md`](docs/audit-bundle-schema.md). |
| Where does the claim stop? | [`FRAMEWORK-LIMITS.md`](FRAMEWORK-LIMITS.md), [`docs/boundary.md`](docs/boundary.md), [`docs/extractor-boundary.md`](docs/extractor-boundary.md), and the evidence map in [`docs/claim-ledger.md`](docs/claim-ledger.md). |
| How do extractor decisions and parity surfaces line up? | [`docs/governance-decision-lattice.md`](docs/governance-decision-lattice.md), [`docs/rust-lean-governance-property-parity.md`](docs/rust-lean-governance-property-parity.md), and [`docs/extractor-ast-theorem-witness.md`](docs/extractor-ast-theorem-witness.md). |
| What are the current audit-boundary design notes? | [`docs/degenerate-behavior.md`](docs/degenerate-behavior.md), [`docs/production-self-audit-loeb-design.md`](docs/production-self-audit-loeb-design.md), and [`docs/pillar2-governance-audit-capacity-design.md`](docs/pillar2-governance-audit-capacity-design.md). |
| How do I cite it? | [`papers/CITATION.bib`](papers/CITATION.bib). Rendered PDFs are attached to GitHub releases starting with `v1.0.0`; arXiv links are added when identifiers are assigned. |

## Worked extractions: the obstruction on real-agent graphs

The headline result is the impossibility theorem, and it does not depend on the
extractor. What follows is its worked extraction over source-derived graph fixtures:
the audit run on
governance graphs extracted from four real agent frameworks. The obstruction the
theorem proves is not a paper artifact: the same monotonicity failure recurs
across three structurally distinct real-derived graphs under one modeling
convention, and the fourth (OpenClaw) trips a different check entirely, so the diagnostic discriminates rather than firing on every input. A Lean theorem
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
[`audits/fixtures/LICENSES.md`](audits/fixtures/LICENSES.md).

The audit-agent release front door is narrower and binary-first: it emits JSON
bundles for Codex CLI, Claude Agent SDK, and the public Claude Code governance
surface, each with a Stage 2 C* carrier derived from the committed extracted
graph and reported separately from the diagnostic.
The bundle schema, per-lane examples, and load-bearing C*-carrier caveats are in
[`docs/audit-bundle-schema.md`](docs/audit-bundle-schema.md).

## Boundaries And Gates

For the complete boundary map, read [`FRAMEWORK-LIMITS.md`](FRAMEWORK-LIMITS.md)
before treating any audit row as a broader safety claim.
For the maintained subsystem ledger and graph-carrier seam map, read
[`docs/lean-module-architecture.md`](docs/lean-module-architecture.md).

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

## Papers

Start in [`papers/`](papers/). The paper hierarchy is:

- **Thesis and formal backing**:
  [`02-semantic-legitimacy-kernels.md`](papers/02-semantic-legitimacy-kernels.md)
  gives the kernel object and the conceptual entry point;
  [`03-impossibility-theorem.md`](papers/03-impossibility-theorem.md)
  is the canonical formal manuscript for the forcing argument.
- **Technical companions**:
  [`04-spectral-scaling.md`](papers/04-spectral-scaling.md) develops the capacity and stability layer under capability scaling; [`05-structural-audits.md`](papers/05-structural-audits.md)
  gives the rule-layer audit methodology and case studies.
- **Essay and positioning**:
  [`01-what-the-compiler-found.md`](papers/01-what-the-compiler-found.md) is
  the general-audience essay; [`06-positioning.md`](papers/06-positioning.md)
  places the program against adjacent work.

The landing claim is strongest when read in that order: paper 02 states the
kernel object, paper 03 proves why such a kernel is forced to declare a
sacrifice, paper 04 prices the same structure as a computable capability
cliff, and the executable artifact shows where the diagnostic bites:
impossibility/monotonicity on extracted real-harness graphs, with the
spectral/C* layer reported on its own carriers.

### Suggested reading order

The file numbers are stable identifiers, not a required reading sequence. Two
paths through the same papers, depending on what you want first:

- **Generalist on-ramp** (motivation first): start with the essay
  [`01-what-the-compiler-found.md`](papers/01-what-the-compiler-found.md) for the
  intuition, then [`02-semantic-legitimacy-kernels.md`](papers/02-semantic-legitimacy-kernels.md)
  for the object, then [`03-impossibility-theorem.md`](papers/03-impossibility-theorem.md)
  for the forcing argument.
- **Reviewer track** (proof first): start with the canonical manuscript
  [`03-impossibility-theorem.md`](papers/03-impossibility-theorem.md), then the
  kernel object [`02-semantic-legitimacy-kernels.md`](papers/02-semantic-legitimacy-kernels.md),
  then the audit methodology and case studies
  [`05-structural-audits.md`](papers/05-structural-audits.md), the standalone
  spectral and capacity layer [`04-spectral-scaling.md`](papers/04-spectral-scaling.md),
  and the positioning against adjacent work
  [`06-positioning.md`](papers/06-positioning.md).

## Broader CLI Surface

The audit-agent is the release front door, but the repository still exposes the
general extractor, graph audit, protocol, and certificate commands:

```bash
cargo run --release --bin legitimacy -- extract tests/fixtures --emit-graph /tmp/sample.graph.json
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
legitimacy audit-graph --graph /tmp/sample.graph.json --claims tests/fixtures/sample_governance_claims.jsonl --claims-provenance observed-runtime --review-overlay tests/fixtures/sample_governance_review_overlay.json
legitimacy protocol init examples/protocol-gate-graph.graph.toml > state.compiled.json
legitimacy protocol measure state.compiled.json > state.measured.json
legitimacy protocol activate state.measured.json > state.live.json
legitimacy protocol status state.live.json
legitimacy protocol audit state.live.json
```

Canonical policy examples use `.rule.toml` and `.graph.toml` files under
[`examples/`](examples/).

## Theorem Spine

The public theorem spine is the small set of named Lean statements that carries
the artifact, in spine order: the kernel object, its forcing argument, the
activation gate, the semantic bridge, the standalone spectral layer, and the
wider-frontier rows. Supporting lemmas, fixtures, and evidence artifacts are
mapped in [`docs/repository-context.md`](docs/repository-context.md). Seven of these (the spectral threshold and channel bound, the capability-scaling substrate and its shared cliff, the forcing argument, the activation gate, and the semantic bridge) are conjoined into one axiom-footprint umbrella by
`spineFootprint` (`lean/Legitimacy/Results/SpineFootprint.lean:28`); the kernel
object it inhabits and the three-valued, multi-principal, and safety-stack rows
build in the same tree but are listed separately rather than folded into that
conjunction.

| Role | Spine theorem | One-line role | Lean path |
| --- | --- | --- | --- |
| Kernel object | `LegitimacyKernel` | The bundled five-axiom kernel structure over a shared governed system; inhabited by `permitKernel`. | `lean/Legitimacy/Kernel/Unified.lean:29` |
| Forcing argument (impossibility) | `reachable_peer_relative_decisive_stage_obstructs_diagnostics` | The reachable peer-relative decisive stage cannot satisfy all diagnostics. | `lean/Legitimacy/Impossibility/PeerRelativeReachable.lean:103` |
| Activation gate | `noUndeclaredSacrificeImplication` | Interface implication: the complete-surface activation gate projects the deployment direction from the compatibility iff, so the kernel must declare its sacrifice. | `lean/Legitimacy/Safety/KernelSafety/BinaryDecisionPipeline.lean:145` |
| Semantic bridge | `semanticKernel_iff_runtime_diagnostic_spectral_layers` | Compatibility unfolding: the strengthened semantic-kernel contract decomposes into runtime, diagnostic, and spectral conjuncts. | `lean/Legitimacy/Results/SemanticBridge.lean:74` |
| Three-valued frontier | `three_valued_composition_inadmissibility` | A third (escalate) verdict does not escape the obstruction; parametric via `three_valued_escalationPolicyWitness_composition_inadmissibility`. | `lean/Legitimacy/Results/Composition.lean:519` |
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

## Citation

BibTeX entries for papers 02, 03, and 04 are in
[`papers/CITATION.bib`](papers/CITATION.bib): `benenson2026semantickernels`,
`benenson2026impossibility`, and `benenson2026capacity`.
