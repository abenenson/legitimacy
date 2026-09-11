# Framework limits

This file maps the current boundary of the shipped Legitimacy substrate across
all released versions. These are not bugs or hidden assumptions; they are the
places where the formal claims intentionally stop.

External reviewers should read this file alongside the README theorem spine and
`docs/repository-context.md`. The citations below point to the Lean definitions
or theorems that name each boundary.

## 1. Action-soundness is ambient causal soundness

The kernel's action-soundness is, at present, just its ambient causal soundness:
`KernelCausalSoundness D` is exactly `CausalSoundness sys.dag sys.governed`
(`lean/Legitimacy/Kernel/Data.lean:230`, with `CausalSoundness` defined at
`lean/Legitimacy/Kernel/CompositionalSafety.lean:152`). The datum's
`StateActionSpace.Action` does not currently identify a causal variable, a
boundary-membership change, or a transition on `GovernedSet`.

Until kernel data carries an interpretation `Action -> CausalBoundaryEffect`, an
action-indexed causal theorem would be a structural placeholder rather than a
stronger guarantee.

## 2. AuditSubject bridge coverage is partial

The bridge from extracted hooks to the audit-subject predicate covers four
decision-system checks, not the full kernel. The status check `auditCheckStatus`
runs on `AuditSubject` (`lean/Legitimacy/Results/GovernanceAdmissibilityAudit/Checks.lean:381`),
while hook extractors return binary `GovernanceGraph` values, and the modeled
RustHookCore bridge records pass-direction status pullbacks for the four
decision-system checks only: consistency, solidarity, monotonicity, and
strategyproofness (`lean/Legitimacy/Extract/RustHookCore/VerdictPullback.lean:244`).
The theorem-facing graph predicate `auditCheckHolds` carries additional support
for certifiability, compositional safety, and nonvacuity, while observable
determinacy and corrigibility remain trivial at that graph predicate level
(`lean/Legitimacy/Results/SelfAudit.lean:129`).

That graph-side triviality of observable determinacy and corrigibility is a
property of the *extracted graph diagnostic layer*, not of the kernel. Both
properties are carried as axioms on the `LegitimacyKernel` structure itself:
corrigibility is `LegitimacyKernel.corrigible`
(`lean/Legitimacy/Kernel/Unified.lean:52`, via `KernelCorrigible` at
`lean/Legitimacy/Kernel/Class.lean:63`), and observable determinacy is
`LegitimacyKernel.observable` (`lean/Legitimacy/Kernel/Unified.lean:46`). The
boundary below is that the *graph audit fixture* does not yet re-derive these
two kernel axioms diagnostically; it is not that the substrate lacks them.

The practical boundary is:

- 4 graph-diagnostic constructors have production-status pass pullbacks.
- Certifiability and nonvacuity have graph-side support lemmas, not a full
  arbitrary-`AuditSubject` status bridge.
- Observable determinacy and corrigibility are dispatcher/projection surfaces
  for the current graph-audit fixture layer, not behavior-preserving extractor
  theorems for arbitrary sources. Both are nonetheless kernel-layer axioms (see
  the cross-reference above).

The Rust graph corrigibility check constructs three replacement policies:
constant pause, deny and permit, with pass-through edges. It checks that those
override graphs can be traversed. For well-formed nonempty acyclic graphs this
is a structural capability of the graph representation, not a test of the
original policy's willingness to cooperate or a deployed agent's compliance.
The CLI's `CORRIGIBLE: SUPPORTED (projection verdict passed)` has that limited
meaning. The current observable-determinacy check also has an exhaustive limit
of ten nodes; larger graphs report `SKIPPED`, which blocks protocol compilation.

A faithful `liftGovernanceGraphToAuditSubject` theorem that preserves all
dispatcher semantics for arbitrary extracted graphs remains substrate-extension
work.

The two committed affirmative fixtures establish their graph properties
independently of the runtime audit status: the `GeneratedAuditSubject.reflects`
/ `pass_*` soundness fields decode the pass-status premise to the corresponding
core Boolean, but the general decision-procedure-soundness bridge from
`auditCheckConsistencyCore ... = .ok true` (and the analogous supported core
checks) to `auditCheckHolds check graph` is not proved in this tree. Thus
"executable auditor PASS implies governance property" is witnessed
per-fixture, not as a verified-sound decision procedure.

Round 5 splits the old representation gap into two formal facts. The first is
that the weak `Representable` predicate is not enough:
`no_general_corpus_obstruction_completeness`
(`lean/Legitimacy/Extract/RepresentableAuditSubject/Round4.lean`) keeps the
round-4 witness as proof that an audit/source faithfulness weld is necessary.
The second is that the strengthened predicate
`RepresentableAuditSubject.FaithfulRepresentable`
(`lean/Legitimacy/Extract/RepresentableAuditSubject.lean`) excludes that
unfaithful witness, and `codexHooksFaithfulRepresented` shows the strengthened
class is nonempty on a concrete extracted hooks graph wrapper.

The all-profile soundness bridge now reaches the faithful audit subject's
executable check. `faithful_audit_evalNode_consistent_iff_graphConsistencyP`
(`lean/Legitimacy/Extract/RepresentableAuditSubject/Semantics.lean`) states the
`GraphConsistencyP` diagnostic over a `DecisionSystem` whose `decide` runs the
audit `evalNode` on an all-profile `ClaimQ` encoding and projects the returned
audit decision to the scarce binary surface. Equality to the represented graph
property is proved through the `AuditSourceFaithful.evalNode_all_profiles` weld
and `AuditEvalNodeSemantics.decision_equivalent_sourceSemantics`; the executable
evalNode is the decision procedure on that side of the iff.

The remaining boundary is corpus completeness, not predicate weakness:
`faithful_representable_current_corpus_incompleteness`,
`no_general_faithful_current_corpus_obstruction_completeness`
and
`faithful_shape_derived_self_certification_strictly_weaker_than_all_profile_consistency`
(`lean/Legitimacy/Extract/RepresentableAuditSubject/Round4.lean`) exhibit a
faithful representable peer-relative source whose current finite executable
self-audit, `auditCheckConsistencyCore` over the shape-derived production
`auditGraphClaims` corpus, passes while the represented graph still violates
all-profile `GraphConsistencyP`. This is a narrow current-corpus limit: the
corpus is generated from audit-graph shape, while the obstruction is
profile-relational. It is not a theorem that no finite executable self-audit
can ever be obstruction-complete. Any future general core-to-property bridge
has to prove an obstruction-complete production corpus for the represented
class; it cannot rely on the old weak predicate.

## 2a. Binary projection is one representation lens; the three-valued obstruction is real

The binary surface is a deliberate representation lens, not a collapse of the
three-valued logic. `GovernanceGraph` is binary, while extracted audit graphs
use `AuditDecision.permit`, `AuditDecision.deny`, and `AuditDecision.escalate`.
To represent a three-valued audit on the scarce binary `GovernanceGraph`
surface, the bridge uses an explicit scarce-allocation lens: terminal escalation
is not a grant, so it projects to binary `Deny`
(`AuditDecision.toScarceBinary`, `lean/Legitimacy/Extract/AuditClaimQEncoding.lean:36`,
with the escalate case discharged by `AuditDecision.toScarceBinary_escalate`).
Edge-bearing escalation is represented separately as continuation to downstream
adjudication; if no downstream stage grants the claim, the terminal projection
remains denial.

This projection is a representation choice for one surface. It is **not** a claim
that three-valued audit logic collapses to binary, and it does not contradict the
proved three-valued impossibility. The parametric theorem
`three_valued_composition_inadmissibility`
(`lean/Legitimacy/Results/Composition.lean:536`), parametric through
`three_valued_escalationPolicyWitness_composition_inadmissibility`
(`lean/Legitimacy/Results/Composition.lean:516`), shows the obstruction is real
and irreducible: there exist three-valued governance nodes A and B that each
individually satisfy `NodeMonotonicity3` while the composed graph A→B violates
`GraphMonotonicity3`, because escalate opens a competitive channel that has no
binary counterpart. Escalate carries adjudicative content that the binary surface
cannot host; the projection records how that content lands on a scarce-allocation
graph, it does not erase the content.

The Codex hook harness theorem
`codexHooks_evalNode_matches_repr_on_auditGraphClaims`
(`lean/Legitimacy/Extract/RepresentableAuditSubject/Round2.lean:810`) is scoped
to that projected decision surface. It is the matching fact for the binary lens,
not a claim that every future three-valued audit graph can be compiled to binary
without naming how edge-bearing review nodes continue.

## 2b. `native_decide` expands the executable trust base

Closing a theorem with `native_decide` widens the trusted computing base. Many
finite fixture, spine, and audit-verdict theorems are closed this way. Those
proofs are still kernel-checked, but the proof term includes
`Lean.ofReduceBool`, so the trusted computing base includes Lean's compiled
evaluator for the reduced Boolean computation. This is strictly weaker than
kernel reduction alone.

The native ASI bridge still lacks a derivation from ASI spectral signature to
semantic `SpectralWellConnected`; current carrier instances supply
well-connectedness independently through the bridge lift.

The verify lane runs `scripts/check-axiom-footprint.sh`, which prints and
normalizes a representative `#print axioms` footprint for spine theorems plus a
leaderboard verdict. Its expected trust categories are `propext`,
`Classical.choice`, `Quot.sound`, and `Lean.ofReduceBool`.

## 3. Compositional safety is universal on `List GovernanceNodeFn`

The primary `GovernanceGraph` substrate is a list of node functions. On that
substrate, `graphDecide_append_of_deny` proves that once a graph prefix denies a
claimant, appending any suffix cannot revive that claim
(`lean/Legitimacy/Kernel/CompositionalSafety.lean:164`). The richer
`canonicalGraphCompositionalSafetyProjection` mirrors the Rust graph projection
at the `AuditGovernanceGraph` layer
(`lean/Legitimacy/Results/GovernanceAdmissibilityAudit/Evaluation.lean:566`).

So the current hook-core compositional-safety pullback should be read as
"extraction success implies the source-level projection used by the graph
surface," not as a per-graph diagnostic that distinguishes arbitrary
`GovernanceGraph` lists.

The strategyproofness audit and activation-gating surfaces intentionally use
different perturbation policies: `check_graph_strategyproofness` and the Lean
`auditCheckStrategyproofnessCore` probe additive strength deltas
`[-0.3, -0.1, 0.1, 0.3, 0.5]`, while protocol/sacrifice gating uses
`check_graph_strategyproofness_verdict` with multiplicative reported-strength
factors `[0.5, 0.8, 1.2, 1.5, 2.0]`. This is an audit-vs-gate policy split, not a
parity bug.

## 4. Replay certification is a baseline verifier

Replay certification is the by-construction baseline, not an external verifier.
`graphReplayCertification` defines legitimacy as exact equality with
`graphDecide` (`lean/Legitimacy/Kernel/Examples.lean:128`). Its consistency
proof, `graphReplayCertification_consistent`, has a second conjunct closed by
reflexivity (`lean/Legitimacy/Kernel/Examples.lean:136`).

This is the canonical replay-by-construction baseline. It is not an external
certificate verifier with signed witnesses, cryptographic commitments, or
third-party validation semantics.

## 5. Legacy unsized `canonicalSpectralInvariant` returns size 3

The legacy unsized `canonicalSpectralInvariant` maps every
`GovernanceGraphClass` to a three-point carrier
(`lean/Legitimacy/Results/CanonicalSpectralInvariant.lean:69`), and the theorem
`canonicalSpectralInvariant_governanceGraphClass_size` states that fixed size
explicitly (`lean/Legitimacy/Results/CanonicalSpectralInvariant.lean:116`).
The headline theorem uses the size-retaining
`canonicalSizedSpectralInvariant` instead
(`lean/Legitimacy/Results/CanonicalSpectralInvariant.lean:92`).

The unsized surface remains publicly callable as a coarsening of the sized
variant. Cleanup is cosmetic; it is not load-bearing for the theorem spine.

## 6. The reflective layer is presentational by design

The reflective modal layer is a Gödel-respecting re-presentation of the audit
guarantee, not a second, independent source of it. The operational guarantee is
carried by the audit certificate; the modal box restates it without adding
discriminating power. This is by design, and the structure below names exactly
where the modal content is assumed rather than constructed.

Two facts make the presentational status precise:

- **Internal soundness is a premise, not a construction.** The reflective
  depth-2 discharge consumes `hinternal : reflectiveBox (depth2LatticeAuditSoundFormulaAt s)`
  in `depth2Lattice_audit_implies_box_at`
  (`lean/Legitimacy/Reflective/Depth2.lean:427`), and the critical-capability
  composition carries the same shape via
  `criticalCapabilityReflectiveSystem_stable_audit_unfolds_to_subcritical_under_hinternal`
  (`lean/Legitimacy/Reflective/CriticalCapabilityComposition.lean:356`) and the
  Löb bridge `criticalCapabilityThresholdAudit_implies_box_at`
  (`lean/Legitimacy/Reflective/CriticalCapabilityComposition.lean:118`). The
  shipped theorem is a threshold-selected modal target *under* an
  internal-soundness premise; it does not construct `hinternal` at concrete
  instances. The production self-audit rule
  `ProductionAuditProvable.certifiedInternalSoundness`
  (`lean/Legitimacy/Reflective/ProductionSelfAudit.lean:151`) makes the same move
  in the other direction: it internalizes the box from the certificate rather
  than deriving it from a Kripke-soundness theorem. The only consistency guard
  proved for that proof predicate is empty-frame: `emptyEval_sound` and `not_bot`
  (`lean/Legitimacy/Reflective/ProductionSelfAudit.lean:339`,
  `lean/Legitimacy/Reflective/ProductionSelfAudit.lean:357`) show `⊥` is not
  derivable under empty-frame evaluation. That is the Gödel-respecting form: the
  system does not derive its own provable internal soundness from soundness
  alone, and no Kripke-soundness theorem for `ProductionAuditProvable` over a
  non-degenerate frame exists.

- **The box adds no power over the certificate.** The exported production
  self-certification box's `.1` conjunct, `productionReflectiveProvable`, is not
  consumed by any downstream verdict/iff theorem; every consumer reads the Prop
  certificate `.2`. Concretely,
  `production_self_audit_box_iff_certificate` establishes
  `productionReflectiveBox ⟺ ProductionSelfAuditCertificateHolds`, so the modal
  box is equivalent to the `native_decide`-discharged certificate, not stronger
  than it. The Löb construction is therefore presentational: a Gödel-respecting
  re-presentation of the certificate, not an operationally load-bearing source of
  the audit guarantee.

The arithmetic and boxed-negative probes mark the same boundary from the outside.
`Depth2ArithmeticSoundnessRealization` carries a genuine first-order-language
package — language, theory, atom interpretation, modal-connective interpretation,
represented soundness sentence, derivation witness, and a bridge back to the
modal proof predicate (`lean/Legitimacy/Reflective/ArithmeticRealizationObstructions.lean:98`)
— but the negative theorem `no_depth2Core_arithmeticSoundnessRealization`
(`lean/Legitimacy/Reflective/ArithmeticRealizationObstructions.lean:193`)
consumes only the unboxed non-provability fact
`depth2Core_latticeAuditSoundFormula_not_provable`
(`lean/Legitimacy/Reflective/ArithmeticRealizationObstructions.lean:179`). The
interface names first-order shape; the impossibility does not yet use
arithmetic-semantic content (a PA derivability predicate, Σ₁-completeness, or
Solovay realization). The v0.8 probe additionally blocks three tempting routes to
the boxed negative for the depth-2 core: necessitation from the unboxed target
(refuted by `depth2Core_latticeAuditSoundFormula_not_provable`); empty-frame
soundness, since `emptyEval_box` validates every boxed formula
(`lean/Legitimacy/Reflective/ArithmeticRealizationObstructions.lean:213`); and
the `PropTautSound` Kripke route, since `propTautSound_forces_every_box` and its
specialization `propTautSound_forces_depth2Core_lattice_hinternal`
(`lean/Legitimacy/Reflective/BoxedSoundnessRealization.lean:165`,
`lean/Legitimacy/Reflective/BoxedSoundnessRealization.lean:177`) force every box.
The remaining open target,
`¬ reflectiveBox (depth2LatticeAuditSoundFormulaAt depth2Core)`, requires either
Kripke completeness for the current modal predicate or a stronger arithmetic
interface. These are honestly open; closing them is future work, not a shipped
claim.

## 7. Production self-audit, capacity, and obstruction layers remain orthogonal

The new boundary theorems are honesty assets, not bridge theorems.
`PeerRelativeAuditOrthogonality.lean` proves that a production self-audit
certificate does not identify an arbitrary `GovernanceGraph`, and that there is
no graph-identification-free bridge from passing production audit statuses, or
from `ProductionSelfAuditCertificateHolds`, to the graph diagnostics used by
the peer-relative obstruction layer. The exact boundary points are
`production_self_audit_certificate_does_not_identify_governanceGraph`
(`lean/Legitimacy/Reflective/PeerRelativeAuditOrthogonality.lean:154`),
`no_universal_audit_passes_to_graph_diagnostics_bridge`
(`lean/Legitimacy/Reflective/PeerRelativeAuditOrthogonality.lean:211`),
`no_universal_self_audit_certificate_to_graph_diagnostics_bridge`
(`lean/Legitimacy/Reflective/PeerRelativeAuditOrthogonality.lean:228`), and
`no_graph_identification_free_reachable_obstruction_certificate_bridge`
(`lean/Legitimacy/Reflective/PeerRelativeAuditOrthogonality.lean:255`).

`GovernanceAuditCapacity.lean` marks the analogous capacity boundary:
finite-channel capacity achievement, independent audit legitimacy, and
reportability live on separate fields unless an additional representation map
is supplied. The concrete orthogonality witnesses show capacity achievement
does not force independent legitimacy, and independent legitimacy does not force
capacity achievement
(`lean/Legitimacy/Spectral/Channels/GovernanceAuditCapacity.lean:167`,
`lean/Legitimacy/Spectral/Channels/GovernanceAuditCapacity.lean:182`).

These results formally mark where the audit/extracted layer does not bridge to
the impossibility or capacity layers. The orthogonality is a feature: the
boundary maps are stated and proved, so no claim is smuggled across them. Any
future bridge has to name and prove the missing representation map; it cannot be
carried through a passing audit certificate or a capacity-achieving prior.

## What this list is not

This list is not a roadmap of failed proof attempts. It is the public boundary
map for the current framework: where rule-layer formal methods stop, where
reflective modal assumptions enter, and where future behavioral,
arithmetic-semantic, or agent-self-modeling substrates would need to begin.
