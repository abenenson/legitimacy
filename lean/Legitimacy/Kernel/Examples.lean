/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Unified
import Mathlib.Tactic.NormNum

/-!
# Legitimacy.Kernel.Examples

Concrete governed systems, interfaces, and independence witnesses for the
unified legitimacy kernel.

This module provides:

* reusable permit-style and deny-style governed systems
* concrete certification, observation, corrigibility, and causal-safety witnesses
* independence theorems separating the five kernel axioms
-/

set_option autoImplicit false

namespace Legitimacy

/-- The full supervisory algebra required by the corrigibility axiom. -/
def fullSupervisoryAlgebra : SupervisoryAlgebra := Set.univ

/-- A single inert self-modification action. -/
def idActionSpace : StateActionSpace where
  Action := Unit
  apply _ S := S

/-- A two-action inert self-modification interface. This keeps the governance
state fixed, but exposes nontrivial action content to downstream multi-agent
fixtures. -/
def boolActionSpace : StateActionSpace where
  Action := Bool
  apply _ S := S

/-- A simple permit-friendly governance graph. -/
def permitGraph : GovernanceGraph := [thresholdNode 0]

/-- A concrete claim permitted by `permitGraph`. -/
def permitClaim : ClaimQ := ⟨0, 1, by norm_num, []⟩

/-- A live trace that always permits the witness claim immediately. -/
def permitTrace : GovernanceTrace :=
  fun _ => (permitClaim, some GovernanceOutcome.permit)

/-- The permit graph permits the witness claim in its singleton context. -/
lemma permitGraph_decides_permit :
    graphDecide permitGraph [permitClaim] permitClaim.id =
      BinaryDecision.Permit := by
  -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
  native_decide

/-- The permit trace is consistent with the permit graph. -/
lemma permitTrace_consistent :
    TraceConsistentWithGraph permitTrace permitGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, permitTrace]
  exact ⟨[permitClaim], by simp, permitGraph_decides_permit⟩

/-- A supervisory state that supports the full algebra while keeping the
underlying decision path non-vacuous. -/
def permitState : GovernanceState where
  graph := [liftNode (thresholdNode 0)]
  snapshot := [liftNode (thresholdNode 0)]
  sandboxBoundary := 1
  thresholds := [1]
  degradeFactor := 2
  reroutePrefix := [liftNode (thresholdNode 0)]
  rerouteWindow := 0
  paused := false
  stopped := false

/-- The permit-friendly supervisory state supports every supervisory action. -/
lemma permitState_supports_full_algebra :
    SupportsAlgebra permitState fullSupervisoryAlgebra := by
  intro σ _
  cases σ <;> simp [SupportsSupervisory, permitState]

/-- The inert action space preserves every supported algebra. -/
theorem idActionSpace_single_step_preserved
    (alg : SupervisoryAlgebra) :
    SingleStepPreserved idActionSpace alg := by
  intro a S hsupports
  simpa [idActionSpace] using hsupports

/-- The two-action inert action space preserves every supported algebra while
still exposing distinguishable action values. -/
theorem boolActionSpace_single_step_preserved
    (alg : SupervisoryAlgebra) :
    SingleStepPreserved boolActionSpace alg := by
  intro a S hsupports
  simpa [boolActionSpace] using hsupports

/-- The permit-friendly supervisory state is corrigible. -/
lemma permit_corrigible :
    Corrigible permitState idActionSpace fullSupervisoryAlgebra where
  supports_algebra := permitState_supports_full_algebra
  single_step_preserved :=
    idActionSpace_single_step_preserved fullSupervisoryAlgebra

/-- The permit-friendly supervisory state is corrigible for the nontrivial
inert Bool action interface. -/
lemma permit_bool_corrigible :
    Corrigible permitState boolActionSpace fullSupervisoryAlgebra where
  supports_algebra := permitState_supports_full_algebra
  single_step_preserved :=
    boolActionSpace_single_step_preserved fullSupervisoryAlgebra

/-- A replay tag for graph-decision certification. -/
inductive ReplayWitness where
  | replay
  deriving Repr, DecidableEq

/-- A one-step replay verifier for graph decisions. -/
def graphReplayVerifier {graph : GovernanceGraph}
    (d : GraphDecision graph) (w : ReplayWitness) : Bool :=
  decide
    (w = ReplayWitness.replay ∧
      d.outcome = graphDecide graph d.claims d.claimant)

/-- A concrete certifiable interface for graph decisions. -/
def graphReplayCertification (graph : GovernanceGraph) :
    CertifiableSystem (GraphDecision graph) ReplayWitness where
  legitimate d := d.outcome = graphDecide graph d.claims d.claimant
  verifier := graphReplayVerifier
  verifierSteps := fun _ _ => 1
  bound := fun _ => 1

/-- Replay certification is graph-consistent. -/
lemma graphReplayCertification_consistent
    (graph : GovernanceGraph) :
    GraphCertificationConsistent (graphReplayCertification graph) := by
  constructor
  · intro d hlegit
    exact hlegit
  · intro claims claimant
    rfl

/-- Replay certification is certifiable for graph decisions. -/
lemma graphReplayCertification_certifiable
    (graph : GovernanceGraph) :
    Certifiable (graphReplayCertification graph) := by
  intro d hlegit
  refine ⟨ReplayWitness.replay, ?_, ?_⟩
  · simpa [CertificateAccepted, graphReplayCertification,
      graphReplayVerifier] using hlegit
  · simp [CertificateWithinBound, graphReplayCertification]

/-- Identity observation is observable over the shared state. -/
lemma state_id_observable {n : Nat} (sys : GovernedSystem n) :
    GovernanceObservable (stateGovernanceAnswer sys)
      (stateGovernanceAnswer sys) (fun s : GovernanceState => s) := by
  intro q s
  rfl

/-- Identity answers are consistent with the shared system semantics. -/
lemma state_answer_consistent {n : Nat} (sys : GovernedSystem n) :
    GovernanceAnswerConsistentWithSystem sys (stateGovernanceAnswer sys) := by
  intro q
  rfl

/-- A no-edge causal graph used for concrete safe witnesses. -/
def noEdge (n : Nat) : Fin n → Fin n → Prop := fun _ _ => False

instance noEdge_dec (n : Nat) : DecidableRel (noEdge n) := by
  intro _ _
  unfold noEdge
  infer_instance

/-- A finite DAG with no edges. -/
def noEdgeDAG (n : Nat) : CausalDAG n where
  edge := noEdge n
  acyclic := by
    intro i j hedge
    cases hedge
  edge_dec := noEdge_dec n

/-- No-edge DAGs reflect any governance graph. -/
lemma noEdge_reflects_graph (n : Nat) (graph : GovernanceGraph) :
    DagReflectsGraph (noEdgeDAG n) graph := by
  intro i j hedge
  cases hedge

/-- A fully governed boundary on `n` variables. -/
def allGoverned (n : Nat) : GovernedSet n where
  governed := fun _ => True
  dec := by
    intro _
    infer_instance

/-- With no edges, every boundary-relative safety predicate is trivially
closed under governance. -/
lemma noEdge_boundary_relative_closed
    (n : Nat) (gov : GovernedSet n) :
    ∀ safety : BoundarySafety gov.boundary,
      BoundaryRelativeClosed (noEdgeDAG n) gov safety := by
  intro safety
  constructor
  · intro v w hv hw hedge hsafe
    cases hedge
  · intro v mid w hv hw hmid hedge hreach hsafe
    cases hedge

/-- The no-edge causal model is boundary-relative safe for any declared
governed set. -/
lemma noEdge_causal_soundness
    (n : Nat) (gov : GovernedSet n) :
    CausalSoundness (noEdgeDAG n) gov :=
  causal_closure_sufficient (noEdgeDAG n) gov
    (noEdge_boundary_relative_closed n gov)

/-- The permit-friendly governed system. -/
def permitSystem : GovernedSystem 1 where
  graph := permitGraph
  state := permitState
  trace := permitTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := permitTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 permitGraph

/-- The live permit trace reaches a final disposition immediately. -/
lemma permitTrace_bounded :
    BoundedDisposition permitTrace [permitClaim] := by
  refine ⟨0, ?_⟩
  intro c hc
  simp at hc
  subst hc
  refine ⟨0, le_rfl, Or.inl ?_⟩
  rfl

/-- The witness claim is genuinely permit-eligible. -/
lemma permitTrace_permitEligible :
    PermitEligible permitTrace [permitClaim] := by
  intro c hc
  simp at hc
  subst hc
  exact ⟨0, rfl⟩

/-- The permit trace is not a refusal trace. -/
lemma permitTrace_notRefusal : ¬ Refusal permitTrace := by
  intro hrefusal
  have h0 := hrefusal 0
  simp [permitTrace] at h0

/-- The permit trace is not a permanently escalatory trace. -/
lemma permitTrace_notPermanentEscalation :
    ¬ PermanentEscalation permitTrace := by
  intro hesc
  have h0 := hesc 0
  simp [permitTrace] at h0

/-- The permit trace is not deadlocked. -/
lemma permitTrace_notDeadlock : ¬ Deadlock permitTrace := by
  intro hdead
  have h0 := hdead 0
  simp [permitTrace] at h0

/-- A concrete witness that the permit graph is non-vacuous. -/
def permitNonVacuousWitness : NonVacuousWitness permitGraph permitTrace where
  wellFormed := by
    simp [permitGraph, WellFormed]
  governedClaims := [permitClaim]
  governed_nonempty := by
    simp
  boundedDisposition := permitTrace_bounded
  permitEligibleClaims := [permitClaim]
  eligible_nonempty := by
    simp
  eligible_subset := by
    intro c hc
    simpa using hc
  permitEligible := permitTrace_permitEligible
  notRefusal := permitTrace_notRefusal
  notPermanentEscalation := permitTrace_notPermanentEscalation
  notDeadlock := permitTrace_notDeadlock

/-- The permit-friendly graph satisfies NON-VACUOUS. -/
lemma permit_nonvacuous : NonVacuous permitGraph permitTrace :=
  ⟨permitNonVacuousWitness⟩

/-- Structure-only permit-kernel data, intentionally constructed without any
bundled axiom witness. This demonstrates that the unbundled data layer is
genuine. -/
private def permitSpectralSignal :
    Fin permitSystem.graph.weightedSize → ℚ := fun i => i.val + 1

noncomputable def kernelDataWithoutCorrigibility :
    LegitimacyKernelData permitSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification permitSystem.graph
  certification_consistent := graphReplayCertification_consistent permitSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer permitSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer permitSystem
  answer_consistent := state_answer_consistent permitSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := permitSystem.graph.toWeightedProfiled
  spectralSignal := permitSpectralSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange permitSpectralSignal
  signalRange_spec := rfl
  stratificationLayers := 1
  overrideEval := { eval := fun _ _ _ => true }
  overrideOvs := []

/-- A concrete unified kernel instance for the permit system. -/
noncomputable def permitKernel : LegitimacyKernel permitSystem where
  toLegitimacyKernelData := kernelDataWithoutCorrigibility
  isKernel :=
    { certifiable := graphReplayCertification_certifiable permitSystem.graph
      observable := state_id_observable permitSystem
      corrigible :=
        kernelCorrigible_zero _ permit_corrigible (by intro a; rfl)
      compositionalSafety :=
        LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
          (noEdge_causal_soundness 1 (allGoverned 1))
      nonVacuous :=
        LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
          permit_nonvacuous }

/-- A polynomial verification budget. -/
def quadraticBound (n : Nat) : Nat := n ^ 2 + 1

/-- A graph-decision family whose accepted witnesses have exponential size. -/
def exponentialGraphCertification
    (graph : GovernanceGraph) (bound : Nat → Nat) :
    CertifiableSystem (GraphDecision graph) Nat where
  legitimate d := d.outcome = graphDecide graph d.claims d.claimant
  verifier d w := decide (w = 2 ^ d.claimant)
  verifierSteps _ w := w
  bound d := bound d.claimant

/-- The exponential-only graph-decision witness family is not certifiable
under the stated quadratic bound. -/
lemma exponential_graph_not_certifiable
    (graph : GovernanceGraph) :
    ¬ Certifiable (exponentialGraphCertification graph quadraticBound) := by
  intro hcert
  let d : GraphDecision graph :=
    { claims := [permitClaim]
      claimant := 6
      outcome := graphDecide graph [permitClaim] 6 }
  obtain ⟨w, hwAccepts, hwBound⟩ := hcert d rfl
  have hw : w = 2 ^ 6 := by
    simpa [CertificateAccepted, exponentialGraphCertification, d] using
      hwAccepts
  have hle : 2 ^ 6 ≤ quadraticBound 6 := by
    simp [CertificateWithinBound, exponentialGraphCertification,
      quadraticBound, d, hw] at hwBound
  norm_num [quadraticBound] at hle

/-- One governed system satisfies observability, corrigibility, causal safety,
and liveness while an exponential graph-certification interface is not
certifiable. -/
theorem independent_certifiable :
    ∃ sys : GovernedSystem 1,
      GovernanceObservable (stateGovernanceAnswer sys)
        (stateGovernanceAnswer sys) (fun s : GovernanceState => s) ∧
      Corrigible sys.state idActionSpace fullSupervisoryAlgebra ∧
      CausalSoundness sys.dag sys.governed ∧
      NonVacuous sys.graph sys.trace ∧
      ¬ Certifiable (exponentialGraphCertification sys.graph quadraticBound) := by
  refine ⟨permitSystem, ?_, ?_, ?_, ?_, ?_⟩
  · exact state_id_observable permitSystem
  · exact permit_corrigible
  · exact noEdge_causal_soundness 1 (allGoverned 1)
  · exact permit_nonvacuous
  · exact exponential_graph_not_certifiable permitSystem.graph

/-- A concrete opaque state-answer interface: one governance query is true in
the hidden supervisory state, but the observed interface suppresses it. -/
def opaqueStateAnswer : GovernanceQuery → GovernanceState → Bool
  | GovernanceQuery.PropertyHolds GovernanceProperty.Consistency, S => !S.stopped
  | _, _ => false

/-- The opaque observation map discards the supervisory state. -/
def opaqueObserve : ObservationFunction GovernanceState Unit := fun _ => ()

/-- The observed interface exposes no governance information. -/
def opaqueObserveAnswer : GovernanceQuery → Unit → Bool := fun _ _ => false

/-- The opaque witness is not governance-observable. -/
lemma opaque_not_observable :
    ¬ GovernanceObservable opaqueStateAnswer opaqueObserveAnswer opaqueObserve := by
  intro hobs
  have h :=
    hobs (GovernanceQuery.PropertyHolds GovernanceProperty.Consistency)
      permitState
  simp [opaqueStateAnswer, opaqueObserveAnswer, permitState] at h

/-- One governed system is certifiable, corrigible, causally safe, and live,
while a zero-knowledge-style opaque observation interface is not observable. -/
theorem independent_observable :
    ∃ sys : GovernedSystem 1,
      Certifiable (graphReplayCertification sys.graph) ∧
      Corrigible sys.state idActionSpace fullSupervisoryAlgebra ∧
      CausalSoundness sys.dag sys.governed ∧
      NonVacuous sys.graph sys.trace ∧
      ¬ GovernanceObservable opaqueStateAnswer opaqueObserveAnswer opaqueObserve := by
  refine ⟨permitSystem, ?_, ?_, ?_, ?_, ?_⟩
  · exact graphReplayCertification_certifiable permitSystem.graph
  · exact permit_corrigible
  · exact noEdge_causal_soundness 1 (allGoverned 1)
  · exact permit_nonvacuous
  · exact opaque_not_observable

/-- A read-only monitoring state exposes data but does not support the full
supervisory algebra required for corrigibility. -/
def readOnlyState : GovernanceState where
  graph := [liftNode (thresholdNode 0)]
  snapshot := []
  sandboxBoundary := 2
  thresholds := []
  degradeFactor := 1
  reroutePrefix := []
  rerouteWindow := 0
  paused := false
  stopped := false

/-- The read-only governed system shares the live graph/trace but has a
read-only supervisory state. -/
def readOnlySystem : GovernedSystem 1 where
  graph := permitGraph
  state := readOnlyState
  trace := permitTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := permitTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 permitGraph

/-- The read-only monitor is not corrigible because `degrade` is not
even supported initially. -/
lemma readOnly_not_corrigible :
    ¬ Corrigible readOnlyState idActionSpace fullSupervisoryAlgebra := by
  intro hcorr
  have hdegrade :
      SupportsSupervisory readOnlyState SupervisoryAction.degrade :=
    hcorr.supports_algebra (by simp [fullSupervisoryAlgebra])
  simp [SupportsSupervisory, readOnlyState] at hdegrade

/-- One governed system is certifiable, observable, causally safe, and live,
while its read-only supervisory state is not corrigible. -/
theorem independent_corrigible :
    ∃ sys : GovernedSystem 1,
      Certifiable (graphReplayCertification sys.graph) ∧
      GovernanceObservable (stateGovernanceAnswer sys)
        (stateGovernanceAnswer sys) (fun s : GovernanceState => s) ∧
      CausalSoundness sys.dag sys.governed ∧
      NonVacuous sys.graph sys.trace ∧
      ¬ Corrigible sys.state idActionSpace fullSupervisoryAlgebra := by
  refine ⟨readOnlySystem, ?_, ?_, ?_, ?_, ?_⟩
  · exact graphReplayCertification_certifiable readOnlySystem.graph
  · exact state_id_observable readOnlySystem
  · exact noEdge_causal_soundness 1 (allGoverned 1)
  · exact permit_nonvacuous
  · exact readOnly_not_corrigible

/-- The binary composition-inadmissibility graph from `MathComposition`. -/
def unsafeCompositionGraph : GovernanceGraph :=
  [thresholdNode (1 / 2), peerRelativeNode]

/-- Concrete claims witnessing unsafe composition. -/
def unsafeAlice : ClaimQ := ⟨0, 2 / 5, by norm_num, []⟩
/-- The middle claimant in the unsafe-composition witness profile. -/
def unsafeBob : ClaimQ := ⟨1, 11 / 20, by norm_num, []⟩
/-- The strongest claimant in the unsafe-composition witness profile. -/
def unsafeCarol : ClaimQ := ⟨2, 9 / 10, by norm_num, []⟩

/-- Baseline profile for the unsafe-composition witness. -/
def unsafeClaims : List ClaimQ := [unsafeAlice, unsafeBob, unsafeCarol]

/-- Bob is permitted before strengthening Alice. -/
lemma unsafeBob_permitted :
    graphDecide unsafeCompositionGraph unsafeClaims 1 =
      BinaryDecision.Permit := by
  -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
  native_decide

/-- Bob is denied after strengthening Alice. -/
lemma unsafeBob_denied_after_strengthen :
    graphDecide unsafeCompositionGraph
      (strengthenClaim 0 (3 / 5) (by norm_num) unsafeClaims) 1 =
      BinaryDecision.Deny := by
  native_decide

/-- A trace witnessing that the unsafe-composition graph is still non-vacuous:
Bob receives a genuine permit on the baseline profile. -/
def unsafeCompositionTrace : GovernanceTrace :=
  fun _ => (unsafeBob, some GovernanceOutcome.permit)

/-- The unsafe-composition trace is consistent with the unsafe graph. -/
lemma unsafeCompositionTrace_consistent :
    TraceConsistentWithGraph unsafeCompositionTrace unsafeCompositionGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, unsafeCompositionTrace]
  exact ⟨unsafeClaims, by simp [unsafeClaims], unsafeBob_permitted⟩

/-- A supervisory state for the unsafe composition graph that still supports
the full supervisory algebra. -/
def unsafeCompositionState : GovernanceState where
  graph := [liftNode (thresholdNode (1 / 2)), liftNode peerRelativeNode]
  snapshot := [liftNode (thresholdNode (1 / 2)), liftNode peerRelativeNode]
  sandboxBoundary := 2
  thresholds := [1]
  degradeFactor := 2
  reroutePrefix := [liftNode (thresholdNode 0)]
  rerouteWindow := 1
  paused := false
  stopped := false

/-- The unsafe-composition state supports every supervisory action. -/
lemma unsafeCompositionState_supports_full_algebra :
    SupportsAlgebra unsafeCompositionState fullSupervisoryAlgebra := by
  intro σ _
  cases σ <;> simp [SupportsSupervisory, unsafeCompositionState]

/-- The unsafe-composition supervisory state is corrigible under
inert self-modification. -/
lemma unsafeComposition_corrigible :
    Corrigible unsafeCompositionState idActionSpace fullSupervisoryAlgebra where
  supports_algebra := unsafeCompositionState_supports_full_algebra
  single_step_preserved :=
    idActionSpace_single_step_preserved fullSupervisoryAlgebra

/-- The unsafe-composition graph remains non-vacuous despite failing
compositional safety. -/
def unsafeCompositionNonVacuousWitness :
    NonVacuousWitness unsafeCompositionGraph unsafeCompositionTrace where
  wellFormed := by
    simp [unsafeCompositionGraph, WellFormed]
  governedClaims := [unsafeBob]
  governed_nonempty := by
    simp
  boundedDisposition := by
    refine ⟨0, ?_⟩
    intro c hc
    simp at hc
    subst hc
    refine ⟨0, le_rfl, Or.inl ?_⟩
    rfl
  permitEligibleClaims := [unsafeBob]
  eligible_nonempty := by
    simp
  eligible_subset := by
    intro c hc
    simpa using hc
  permitEligible := by
    intro c hc
    simp at hc
    subst hc
    exact ⟨0, rfl⟩
  notRefusal := by
    intro hrefusal
    have h0 := hrefusal 0
    simp [unsafeCompositionTrace] at h0
  notPermanentEscalation := by
    intro hesc
    have h0 := hesc 0
    simp [unsafeCompositionTrace] at h0
  notDeadlock := by
    intro hdead
    have h0 := hdead 0
    simp [unsafeCompositionTrace] at h0

/-- The unsafe-composition graph satisfies NON-VACUOUS. -/
lemma unsafeComposition_nonvacuous :
    NonVacuous unsafeCompositionGraph unsafeCompositionTrace :=
  ⟨unsafeCompositionNonVacuousWitness⟩

/-- A concrete causal chain used to encode the composition-inadmissibility
counterexample as a boundary-relative safety failure. -/
def unsafeEdge : Fin 3 → Fin 3 → Prop := fun i j =>
  (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 2)

instance unsafeEdge_dec : DecidableRel unsafeEdge := by
  intro i j
  unfold unsafeEdge
  exact instDecidableOr

/-- The unsafe causal chain `0 -> 1 -> 2`. -/
def unsafeDAG : CausalDAG 3 where
  edge := unsafeEdge
  acyclic := by
    intro i j h
    unfold unsafeEdge at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> omega
  edge_dec := unsafeEdge_dec

/-- The unsafe DAG reflects the two-stage unsafe composition graph. -/
lemma unsafeDAG_reflects_graph :
    DagReflectsGraph unsafeDAG unsafeCompositionGraph := by
  intro i j hedge
  refine ⟨0, ?_, unsafeDAG.acyclic i j hedge⟩
  simp [unsafeCompositionGraph]

/-- Every variable in the unsafe causal chain lies within the declared
boundary. -/
def unsafeGoverned : GovernedSet 3 where
  governed := fun _ => True
  dec := by
    intro _
    infer_instance

/-- The governed system that realizes the unsafe composition witness. -/
def unsafeCompositionSystem : GovernedSystem 3 where
  graph := unsafeCompositionGraph
  state := unsafeCompositionState
  trace := unsafeCompositionTrace
  dag := unsafeDAG
  governed := unsafeGoverned
  trace_consistent := unsafeCompositionTrace_consistent
  dag_reflects_graph := unsafeDAG_reflects_graph

/-- The action that targets the start of the unsafe causal chain. -/
def unsafeAction : Action 3 where
  target := ⟨0, by omega⟩

/-- A boundary-relative safety predicate whose endpoint safety is exactly the
post-strengthening Bob-permit condition from the composition witness. -/
def unsafeSafety : BoundarySafety unsafeGoverned.boundary where
  safe := fun v =>
    if v.1.val = 2 then
      graphDecide unsafeCompositionGraph
        (strengthenClaim 0 (3 / 5) (by norm_num) unsafeClaims) 1 =
          BinaryDecision.Permit
    else
      graphDecide unsafeCompositionGraph unsafeClaims 1 =
        BinaryDecision.Permit

/-- The initial node is safe because Bob is initially permitted. -/
lemma unsafeAction_safe :
    unsafeSafety.safe ⟨unsafeAction.target, by trivial⟩ := by
  simp [unsafeSafety, unsafeAction, unsafeBob_permitted]

/-- The unsafe chain reaches its endpoint. -/
lemma unsafeAction_reaches_endpoint :
    CausalReach unsafeDAG unsafeAction.target ⟨2, by omega⟩ := by
  let mid : Fin 3 := ⟨1, by omega⟩
  have h01 : CausalReach unsafeDAG unsafeAction.target mid := by
    exact CausalReach.direct (by
      show unsafeEdge unsafeAction.target mid
      simp [unsafeAction, unsafeEdge, mid])
  have h12 : CausalReach unsafeDAG mid ⟨2, by omega⟩ := by
    exact CausalReach.direct (by
      show unsafeEdge mid ⟨2, by omega⟩
      simp [unsafeEdge, mid])
  exact CausalReach.trans h01 h12

/-- The endpoint is unsafe because Bob is denied after the strengthening
step, matching the composition-inadmissibility witness. -/
lemma unsafeEndpoint_not_safe :
    ¬ unsafeSafety.safe ⟨⟨2, by omega⟩, by trivial⟩ := by
  simp [unsafeSafety, unsafeBob_denied_after_strengthen]

/-- The composition-inadmissibility witness induces a concrete failure of the
boundary-relative compositional-safety formulation. -/
lemma unsafeComposition_not_causally_sound :
    ¬ CausalSoundness unsafeDAG unsafeGoverned := by
  intro hsound
  have hunsafe :=
    hsound unsafeAction unsafeSafety (by trivial) unsafeAction_safe
      ⟨2, by omega⟩ (by trivial) unsafeAction_reaches_endpoint
  exact unsafeEndpoint_not_safe hunsafe

/-- One governed system is certifiable, observable, corrigible, and
live, while its composition-inadmissibility graph induces an unsafe causal
DAG. -/
theorem independent_compositional_safety :
    ∃ sys : GovernedSystem 3,
      Certifiable (graphReplayCertification sys.graph) ∧
      GovernanceObservable (stateGovernanceAnswer sys)
        (stateGovernanceAnswer sys) (fun s : GovernanceState => s) ∧
      Corrigible sys.state idActionSpace fullSupervisoryAlgebra ∧
      NonVacuous sys.graph sys.trace ∧
      ¬ CausalSoundness sys.dag sys.governed := by
  refine ⟨unsafeCompositionSystem, ?_, ?_, ?_, ?_, ?_⟩
  · exact graphReplayCertification_certifiable unsafeCompositionSystem.graph
  · exact state_id_observable unsafeCompositionSystem
  · exact unsafeComposition_corrigible
  · exact unsafeComposition_nonvacuous
  · exact unsafeComposition_not_causally_sound

/-- A deny-all supervisory state that still supports the full supervisory
algebra. -/
def kernelDenyAllState : GovernanceState where
  graph := [denyNode]
  snapshot := [denyNode]
  sandboxBoundary := 1
  thresholds := [1]
  degradeFactor := 2
  reroutePrefix := [denyNode]
  rerouteWindow := 0
  paused := false
  stopped := false

/-- The deny-all state supports every supervisory action. -/
lemma kernelDenyAllState_supports_full_algebra :
    SupportsAlgebra kernelDenyAllState fullSupervisoryAlgebra := by
  intro σ _
  cases σ <;> simp [SupportsSupervisory, kernelDenyAllState]

/-- The deny-all state is corrigible under inert self-modification. -/
lemma kernelDenyAll_corrigible :
    Corrigible kernelDenyAllState idActionSpace fullSupervisoryAlgebra where
  supports_algebra := kernelDenyAllState_supports_full_algebra
  single_step_preserved :=
    idActionSpace_single_step_preserved fullSupervisoryAlgebra

/-- A deny-all trace over the shared witness claim. -/
def kernelDenyAllTrace : GovernanceTrace :=
  fun _ => (permitClaim, some GovernanceOutcome.deny)

/-- The deny-all graph denies the witness claim. -/
lemma kernelDenyAllGraph_denies :
    graphDecide denyAllGraph [permitClaim] permitClaim.id =
      BinaryDecision.Deny := by
  -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
  native_decide

/-- The deny-all trace is graph-consistent. -/
lemma kernelDenyAllTrace_consistent :
    TraceConsistentWithGraph kernelDenyAllTrace denyAllGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, kernelDenyAllTrace]
  exact ⟨[permitClaim], by simp, kernelDenyAllGraph_denies⟩

/-- The deny-all trace is a refusal trace. -/
lemma kernelDenyAllTrace_refusal : Refusal kernelDenyAllTrace := by
  intro t
  rfl

/-- The deny-all governed system. -/
def kernelDenyAllSystem : GovernedSystem 1 where
  graph := denyAllGraph
  state := kernelDenyAllState
  trace := kernelDenyAllTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := kernelDenyAllTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 denyAllGraph

/-- One governed system satisfies certifiability, observability,
corrigibility, and causal safety, while its deny-all trace fails
NON-VACUOUS. -/
theorem independent_nonvacuous :
    ∃ sys : GovernedSystem 1,
      Certifiable (graphReplayCertification sys.graph) ∧
      GovernanceObservable (stateGovernanceAnswer sys)
        (stateGovernanceAnswer sys) (fun s : GovernanceState => s) ∧
      Corrigible sys.state idActionSpace fullSupervisoryAlgebra ∧
      CausalSoundness sys.dag sys.governed ∧
      ¬ NonVacuous sys.graph sys.trace := by
  refine ⟨kernelDenyAllSystem, ?_, ?_, ?_, ?_, ?_⟩
  · exact graphReplayCertification_certifiable kernelDenyAllSystem.graph
  · exact state_id_observable kernelDenyAllSystem
  · exact kernelDenyAll_corrigible
  · exact noEdge_causal_soundness 1 (allGoverned 1)
  · exact refusal_not_nonvacuous kernelDenyAllTrace_refusal

/-! ## Kernel-data axiom independence -/

/-- Shared spectral signal for structure-only kernel-data witnesses. -/
private def kernelExampleSpectralSignal {n : Nat}
    (sys : GovernedSystem n) :
    Fin sys.graph.weightedSize → ℚ := fun i => i.val + 1

/-- Replay/state kernel data over any governed-system example in this file. -/
noncomputable def replayStateKernelData {n : Nat}
    (sys : GovernedSystem n) : LegitimacyKernelData sys where
  Witness := ReplayWitness
  certification := graphReplayCertification sys.graph
  certification_consistent := graphReplayCertification_consistent sys.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer sys
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer sys
  answer_consistent := state_answer_consistent sys
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := sys.graph.toWeightedProfiled
  spectralSignal := kernelExampleSpectralSignal sys
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange (kernelExampleSpectralSignal sys)
  signalRange_spec := rfl
  stratificationLayers := 1
  overrideEval := { eval := fun _ _ _ => true }
  overrideOvs := []

/-- Kernel data over `permitSystem` whose certificate interface is deliberately
not certifiable under the polynomial budget. -/
noncomputable def kernelDataWithoutCertifiable :
    LegitimacyKernelData permitSystem where
  Witness := Nat
  certification := exponentialGraphCertification permitSystem.graph quadraticBound
  certification_consistent := by
    constructor
    · intro d hlegit
      exact hlegit
    · intro claims claimant
      rfl
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer permitSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer permitSystem
  answer_consistent := state_answer_consistent permitSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := permitSystem.graph.toWeightedProfiled
  spectralSignal := permitSpectralSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange permitSpectralSignal
  signalRange_spec := rfl
  stratificationLayers := 1
  overrideEval := { eval := fun _ _ _ => true }
  overrideOvs := []

/-- Kernel data over `permitSystem` whose observation interface discards the
permit query answer. -/
noncomputable def kernelDataWithoutObservable :
    LegitimacyKernelData permitSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification permitSystem.graph
  certification_consistent := graphReplayCertification_consistent permitSystem.graph
  ObservedState := Unit
  answer := stateGovernanceAnswer permitSystem
  observe := fun _ : GovernanceState => ()
  observeAnswer := fun _ _ => false
  answer_consistent := state_answer_consistent permitSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := permitSystem.graph.toWeightedProfiled
  spectralSignal := permitSpectralSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange permitSpectralSignal
  signalRange_spec := rfl
  stratificationLayers := 1
  overrideEval := { eval := fun _ _ _ => true }
  overrideOvs := []

/-- The permit-system answer to the witness permit query is not preserved by a
constant-false observation interface. -/
lemma permit_constantFalse_not_observable :
    ¬ GovernanceObservable (stateGovernanceAnswer permitSystem)
      (fun _ _ => false) (fun _ : GovernanceState => ()) := by
  intro hobs
  have h :=
    hobs (GovernanceQuery.ClaimPermitted permitClaim.id) permitState
  simp [stateGovernanceAnswer, permitSystem, permitTrace, permitClaim] at h

/-- Axiom independence at the kernel-data level: certifiability can fail while
the other four kernel axioms hold. -/
theorem kernel_axiom_independence_certifiable :
    ∃ (n : Nat) (sys : GovernedSystem n) (D : LegitimacyKernelData sys),
      GovernanceObservable D.answer D.observeAnswer D.observe ∧
      KernelCorrigible D ∧
      CausalSoundness sys.dag sys.governed ∧
      NonVacuous sys.graph sys.trace ∧
      ¬ Certifiable D.certification := by
  refine ⟨1, permitSystem, kernelDataWithoutCertifiable, ?_, ?_, ?_, ?_, ?_⟩
  · exact state_id_observable permitSystem
  · exact kernelCorrigible_zero _ permit_corrigible (by intro a; rfl)
  · exact noEdge_causal_soundness 1 (allGoverned 1)
  · exact permit_nonvacuous
  · exact exponential_graph_not_certifiable permitSystem.graph

/-- Axiom independence at the kernel-data level: observability can fail while
the other four kernel axioms hold. -/
theorem kernel_axiom_independence_observable :
    ∃ (n : Nat) (sys : GovernedSystem n) (D : LegitimacyKernelData sys),
      Certifiable D.certification ∧
      KernelCorrigible D ∧
      CausalSoundness sys.dag sys.governed ∧
      NonVacuous sys.graph sys.trace ∧
      ¬ GovernanceObservable D.answer D.observeAnswer D.observe := by
  refine ⟨1, permitSystem, kernelDataWithoutObservable, ?_, ?_, ?_, ?_, ?_⟩
  · exact graphReplayCertification_certifiable permitSystem.graph
  · exact kernelCorrigible_zero _ permit_corrigible (by intro a; rfl)
  · exact noEdge_causal_soundness 1 (allGoverned 1)
  · exact permit_nonvacuous
  · exact permit_constantFalse_not_observable

/-- Axiom independence at the kernel-data level: post-fold kernel
corrigibility can fail while the other four kernel axioms hold. -/
theorem kernel_axiom_independence_corrigible :
    ∃ (n : Nat) (sys : GovernedSystem n) (D : LegitimacyKernelData sys),
      Certifiable D.certification ∧
      GovernanceObservable D.answer D.observeAnswer D.observe ∧
      CausalSoundness sys.dag sys.governed ∧
      NonVacuous sys.graph sys.trace ∧
      ¬ KernelCorrigible D := by
  refine ⟨1, readOnlySystem, replayStateKernelData readOnlySystem,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact graphReplayCertification_certifiable readOnlySystem.graph
  · exact state_id_observable readOnlySystem
  · exact noEdge_causal_soundness 1 (allGoverned 1)
  · exact permit_nonvacuous
  · intro hcorr
    exact readOnly_not_corrigible hcorr.1

/-- Axiom independence at the kernel-data level: compositional safety can fail
while the other four kernel axioms hold. -/
theorem kernel_axiom_independence_compositional_safety :
    ∃ (n : Nat) (sys : GovernedSystem n) (D : LegitimacyKernelData sys),
      Certifiable D.certification ∧
      GovernanceObservable D.answer D.observeAnswer D.observe ∧
      KernelCorrigible D ∧
      NonVacuous sys.graph sys.trace ∧
      ¬ CausalSoundness sys.dag sys.governed := by
  refine ⟨3, unsafeCompositionSystem,
    replayStateKernelData unsafeCompositionSystem, ?_, ?_, ?_, ?_, ?_⟩
  · exact graphReplayCertification_certifiable unsafeCompositionSystem.graph
  · exact state_id_observable unsafeCompositionSystem
  · exact kernelCorrigible_zero _ unsafeComposition_corrigible (by intro a; rfl)
  · exact unsafeComposition_nonvacuous
  · exact unsafeComposition_not_causally_sound

/-- Axiom independence at the kernel-data level: non-vacuity can fail while the
other four kernel axioms hold. -/
theorem kernel_axiom_independence_nonvacuous :
    ∃ (n : Nat) (sys : GovernedSystem n) (D : LegitimacyKernelData sys),
      Certifiable D.certification ∧
      GovernanceObservable D.answer D.observeAnswer D.observe ∧
      KernelCorrigible D ∧
      CausalSoundness sys.dag sys.governed ∧
      ¬ NonVacuous sys.graph sys.trace := by
  refine ⟨1, kernelDenyAllSystem, replayStateKernelData kernelDenyAllSystem,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact graphReplayCertification_certifiable kernelDenyAllSystem.graph
  · exact state_id_observable kernelDenyAllSystem
  · exact kernelCorrigible_zero _ kernelDenyAll_corrigible (by intro a; rfl)
  · exact noEdge_causal_soundness 1 (allGoverned 1)
  · exact refusal_not_nonvacuous kernelDenyAllTrace_refusal

end Legitimacy
