/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Examples

/-!
# Legitimacy.Kernel.BoundaryExitExamples

Concrete two-stage kernel construction whose causal structure contains a real
handoff edge. The governed boundary contains the source of the handoff but not
the sink, and the safety proof depends on the absence of governed re-entry
after that boundary exit.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A two-stage permissive graph, written as an actual composition. -/
def boundaryExitGraph : GovernanceGraph :=
  [thresholdNode 0] ++ [thresholdNode 0]

/-- The composed graph really has two governance stages. -/
lemma boundaryExitGraph_length :
    boundaryExitGraph.length = 2 := by
  rfl

/-- The witness claim survives both stages of the composed graph. -/
lemma boundaryExitGraph_decides_permit :
    graphDecide boundaryExitGraph [permitClaim] permitClaim.id =
      BinaryDecision.Permit := by
  -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
  native_decide

/-- The graph-level denial invariant still holds for arbitrary suffixes. -/
lemma boundaryExitGraph_denial_stable :
    CompositionalSafety boundaryExitGraph :=
  graphDecide_append_of_deny boundaryExitGraph

/-- A live trace for the two-stage graph. -/
def boundaryExitTrace : GovernanceTrace :=
  fun _ => (permitClaim, some GovernanceOutcome.permit)

/-- The live trace is consistent with the two-stage graph. -/
lemma boundaryExitTrace_consistent :
    TraceConsistentWithGraph boundaryExitTrace boundaryExitGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, boundaryExitTrace]
  exact ⟨[permitClaim], by simp, boundaryExitGraph_decides_permit⟩

/-- Supervisory state carrying the same two-stage graph. -/
def boundaryExitState : GovernanceState where
  graph := [liftNode (thresholdNode 0), liftNode (thresholdNode 0)]
  snapshot := [liftNode (thresholdNode 0), liftNode (thresholdNode 0)]
  sandboxBoundary := 2
  thresholds := [1]
  degradeFactor := 2
  reroutePrefix := [liftNode (thresholdNode 0)]
  rerouteWindow := 1
  paused := false
  stopped := false

/-- The two-stage state supports the full supervisory algebra. -/
lemma boundaryExitState_supports_full_algebra :
    SupportsAlgebra boundaryExitState fullSupervisoryAlgebra := by
  intro σ _
  cases σ <;> simp [SupportsSupervisory, boundaryExitState]

/-- The two-stage state is corrigible under inert self-modification. -/
lemma boundaryExit_corrigible :
    Corrigible boundaryExitState idActionSpace fullSupervisoryAlgebra where
  supports_algebra := boundaryExitState_supports_full_algebra
  single_step_preserved :=
    idActionSpace_single_step_preserved fullSupervisoryAlgebra

/-- Causal handoff edge from governed source `0` to ungoverned sink `1`. -/
def boundaryHandoffEdge : Fin 2 → Fin 2 → Prop := fun i j =>
  i.val = 0 ∧ j.val = 1

instance boundaryHandoffEdge_dec : DecidableRel boundaryHandoffEdge := by
  intro i j
  unfold boundaryHandoffEdge
  infer_instance

/-- Two-variable DAG containing the concrete handoff `0 -> 1`. -/
def boundaryExitDAG : CausalDAG 2 where
  edge := boundaryHandoffEdge
  acyclic := by
    intro i j hedge
    unfold boundaryHandoffEdge at hedge
    omega
  edge_dec := boundaryHandoffEdge_dec

/-- The handoff source is the only governed variable. -/
def boundaryExitGoverned : GovernedSet 2 where
  governed := fun v => v.val = 0
  dec := by
    intro v
    infer_instance

/-- The concrete causal handoff exists. -/
lemma boundaryExitDAG_has_handoff :
    boundaryExitDAG.edge ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  show boundaryHandoffEdge ⟨0, by omega⟩ ⟨1, by omega⟩
  exact ⟨rfl, rfl⟩

/-- The handoff starts inside governance. -/
lemma boundaryExit_source_governed :
    boundaryExitGoverned.governed ⟨0, by omega⟩ := by
  rfl

/-- The handoff target is outside governance. -/
lemma boundaryExit_sink_not_governed :
    ¬ boundaryExitGoverned.governed ⟨1, by omega⟩ := by
  decide

/-- The concrete handoff is a boundary exit. -/
lemma boundaryExit_has_boundary_exit :
    ∃ i j : Fin 2,
      boundaryExitDAG.edge i j ∧
      boundaryExitGoverned.governed i ∧
      ¬ boundaryExitGoverned.governed j :=
  ⟨⟨0, by omega⟩, ⟨1, by omega⟩,
    boundaryExitDAG_has_handoff,
    boundaryExit_source_governed,
    boundaryExit_sink_not_governed⟩

/-- Once the handoff leaves governance, it cannot reach a governed variable. -/
lemma boundaryExit_no_governed_reentry
    {mid w : Fin 2}
    (hmid : ¬ boundaryExitGoverned.governed mid)
    (hw : boundaryExitGoverned.governed w) :
    ¬ CausalReach boundaryExitDAG mid w := by
  intro hreach
  have hmid_ne_zero : mid.val ≠ 0 := by
    intro hzero
    exact hmid hzero
  have hmid_one : mid.val = 1 := by
    omega
  have hw_zero : w.val = 0 := hw
  have hlt : mid.val < w.val := hreach.lt
  omega

/-- No direct causal edge stays wholly inside the governed boundary. -/
lemma boundaryExit_governed_edge_closed
    (safety : BoundarySafety boundaryExitGoverned.boundary) :
    GovernedEdgeClosed boundaryExitDAG boundaryExitGoverned safety := by
  intro v w hv hw hedge hsafe
  show safety.safe ⟨w, hw⟩
  have hw_zero : w.val = 0 := hw
  have hw_one : w.val = 1 := by
    change boundaryHandoffEdge v w at hedge
    exact hedge.2
  exact False.elim (by omega)

/-- The only boundary exit has an explicit no-reentry contract. -/
lemma boundaryExit_boundary_contract
    (safety : BoundarySafety boundaryExitGoverned.boundary) :
    BoundaryContract boundaryExitDAG boundaryExitGoverned safety := by
  intro v mid w hv hw hmid hedge hreach hsafe
  exact False.elim (boundaryExit_no_governed_reentry hmid hw hreach)

/-- Boundary-relative closure is proved from the real handoff structure. -/
lemma boundaryExit_boundary_relative_closed
    (safety : BoundarySafety boundaryExitGoverned.boundary) :
    BoundaryRelativeClosed boundaryExitDAG boundaryExitGoverned safety :=
  ⟨boundaryExit_governed_edge_closed safety,
    boundaryExit_boundary_contract safety⟩

/-- The two-stage handoff DAG is causally sound: safety cannot re-enter
governance after the handoff edge leaves the governed boundary. -/
lemma boundaryExit_causal_soundness :
    CausalSoundness boundaryExitDAG boundaryExitGoverned :=
  causal_closure_sufficient boundaryExitDAG boundaryExitGoverned
    boundaryExit_boundary_relative_closed

/-- The concrete handoff DAG is reflected by the two-stage graph. -/
lemma boundaryExitDAG_reflects_graph :
    DagReflectsGraph boundaryExitDAG boundaryExitGraph := by
  intro i j hedge
  refine ⟨0, ?_, boundaryExitDAG.acyclic i j hedge⟩
  simp [boundaryExitGraph]

/-- The governed system combining the composed graph and the handoff DAG. -/
def boundaryExitSystem : GovernedSystem 2 where
  graph := boundaryExitGraph
  state := boundaryExitState
  trace := boundaryExitTrace
  dag := boundaryExitDAG
  governed := boundaryExitGoverned
  trace_consistent := boundaryExitTrace_consistent
  dag_reflects_graph := boundaryExitDAG_reflects_graph

/-- The live trace reaches a final disposition immediately. -/
lemma boundaryExitTrace_bounded :
    BoundedDisposition boundaryExitTrace [permitClaim] := by
  refine ⟨0, ?_⟩
  intro c hc
  simp at hc
  subst hc
  refine ⟨0, le_rfl, Or.inl ?_⟩
  rfl

/-- The witness claim is permit-eligible in the two-stage trace. -/
lemma boundaryExitTrace_permitEligible :
    PermitEligible boundaryExitTrace [permitClaim] := by
  intro c hc
  simp at hc
  subst hc
  exact ⟨0, rfl⟩

/-- The two-stage trace is not a refusal trace. -/
lemma boundaryExitTrace_notRefusal : ¬ Refusal boundaryExitTrace := by
  intro hrefusal
  have h0 := hrefusal 0
  simp [boundaryExitTrace] at h0

/-- The two-stage trace is not permanently escalatory. -/
lemma boundaryExitTrace_notPermanentEscalation :
    ¬ PermanentEscalation boundaryExitTrace := by
  intro hesc
  have h0 := hesc 0
  simp [boundaryExitTrace] at h0

/-- The two-stage trace is not deadlocked. -/
lemma boundaryExitTrace_notDeadlock : ¬ Deadlock boundaryExitTrace := by
  intro hdead
  have h0 := hdead 0
  simp [boundaryExitTrace] at h0

/-- Concrete non-vacuity witness for the two-stage handoff system. -/
def boundaryExitNonVacuousWitness :
    NonVacuousWitness boundaryExitGraph boundaryExitTrace where
  wellFormed := by
    simp [boundaryExitGraph, WellFormed]
  governedClaims := [permitClaim]
  governed_nonempty := by
    simp
  boundedDisposition := boundaryExitTrace_bounded
  permitEligibleClaims := [permitClaim]
  eligible_nonempty := by
    simp
  eligible_subset := by
    intro c hc
    simpa using hc
  permitEligible := boundaryExitTrace_permitEligible
  notRefusal := boundaryExitTrace_notRefusal
  notPermanentEscalation := boundaryExitTrace_notPermanentEscalation
  notDeadlock := boundaryExitTrace_notDeadlock

/-- The two-stage handoff system satisfies NON-VACUOUS. -/
lemma boundaryExit_nonvacuous :
    NonVacuous boundaryExitGraph boundaryExitTrace :=
  ⟨boundaryExitNonVacuousWitness⟩

/-- A spectral signal for the two-stage handoff kernel data. -/
private def boundaryExitSpectralSignal :
    Fin boundaryExitSystem.graph.weightedSize → ℚ := fun i => i.val + 1

/-- Structure-only kernel data for the two-stage handoff system. -/
noncomputable def boundaryExitKernelData :
    LegitimacyKernelData boundaryExitSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification boundaryExitSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent boundaryExitSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer boundaryExitSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer boundaryExitSystem
  answer_consistent := state_answer_consistent boundaryExitSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := boundaryExitSystem.graph.toWeightedProfiled
  spectralSignal := boundaryExitSpectralSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange boundaryExitSpectralSignal
  signalRange_spec := rfl
  stratificationLayers := 1
  overrideEval := { eval := fun _ _ _ => true }
  overrideOvs := []

/-- Full unified kernel witness for the two-stage handoff system. -/
noncomputable def boundaryExitKernel :
    LegitimacyKernel boundaryExitSystem where
  toLegitimacyKernelData := boundaryExitKernelData
  isKernel :=
    { certifiable :=
        graphReplayCertification_certifiable boundaryExitSystem.graph
      observable := state_id_observable boundaryExitSystem
      corrigible :=
        kernelCorrigible_zero _ boundaryExit_corrigible (by intro a; rfl)
      compositionalSafety :=
        LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
          boundaryExit_causal_soundness
      nonVacuous :=
        LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
          boundaryExit_nonvacuous }

/-- Concrete facts a reviewer can inspect: two stages, one causal boundary
exit, no governed re-entry, and all five runtime kernel axioms. -/
theorem boundaryExitKernel_concrete_witnesses :
    boundaryExitSystem.graph.length = 2 ∧
      (∃ i j : Fin 2,
        boundaryExitSystem.dag.edge i j ∧
        boundaryExitSystem.governed.governed i ∧
        ¬ boundaryExitSystem.governed.governed j) ∧
      (∀ mid w : Fin 2,
        ¬ boundaryExitSystem.governed.governed mid →
        boundaryExitSystem.governed.governed w →
        ¬ CausalReach boundaryExitSystem.dag mid w) ∧
      IsLegitimacyKernel boundaryExitKernel.toLegitimacyKernelData := by
  refine ⟨boundaryExitGraph_length, ?_, ?_, boundaryExitKernel.isKernel⟩
  · exact boundaryExit_has_boundary_exit
  · intro mid w hmid hw
    exact boundaryExit_no_governed_reentry hmid hw

/-- The existing threshold-plus-peer-relative construction is the companion
boundary-relative safety failure for a different two-stage composition. -/
theorem thresholdPeerRelative_composition_refutes_causal_soundness :
    ¬ CausalSoundness unsafeDAG unsafeGoverned :=
  unsafeComposition_not_causally_sound

end Legitimacy
