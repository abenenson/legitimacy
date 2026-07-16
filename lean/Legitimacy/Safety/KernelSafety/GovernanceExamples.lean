/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.ReachabilityStack

/-! # Legitimacy.Safety.KernelSafety.GovernanceExamples

Concrete governance examples for kernel-safety theorems.

This module owns the five-node governance datum, widened-signal mutation,
action-driven threshold mutation, and basic kernel-governed trajectories used
by the stateful and extracted-stack examples.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-! ## Concrete GovernanceGraph worked instance -/

/-- A concrete governance node that permits every claimant on every profile. -/
def examplePermitNode : GovernanceNodeFn :=
  fun _ _ => BinaryDecision.Permit

/-- A five-node concrete governance graph, chosen so its canonical weighted
carrier has size five and can use the existing `uniK5` spectral certificate. -/
def exampleGovernanceGraph : GovernanceGraph :=
  [ examplePermitNode
  , examplePermitNode
  , examplePermitNode
  , examplePermitNode
  , examplePermitNode
  ]

/-- The five-node permit graph always permits. -/
lemma exampleGovernanceGraph_decides_permit
    (claims : List ClaimQ) (claimant : ClaimantId) :
    graphDecide exampleGovernanceGraph claims claimant =
      BinaryDecision.Permit := by
  simp [exampleGovernanceGraph, examplePermitNode, graphDecide]

/-- The five-node permit graph satisfies the four graph-diagnostic
legitimacy axioms. -/
lemma exampleGovernanceGraph_allLegitimacyAxioms :
    AllLegitimacyAxioms exampleGovernanceGraph := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro claims k j hk hj hkj hdist hdeny
    have hfalse := hdeny
    simp [exampleGovernanceGraph_decides_permit claims k] at hfalse
  · intro claims α hα j hj
    simp [exampleGovernanceGraph_decides_permit]
  · intro claims k s' hs' j hk hdist hle hperm
    simp [exampleGovernanceGraph_decides_permit]
  · intro claims k s_r hs_r hk hdist hperm
    simp [exampleGovernanceGraph_decides_permit]

/-- The standard permit trace is consistent with the concrete example graph. -/
lemma exampleGovernanceTrace_consistent :
    TraceConsistentWithGraph permitTrace exampleGovernanceGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, permitTrace]
  exact ⟨[permitClaim], by simp,
    exampleGovernanceGraph_decides_permit [permitClaim] permitClaim.id⟩

/-- A governed system backed by the concrete five-node governance graph. -/
def exampleGovernedSystem : GovernedSystem 1 where
  graph := exampleGovernanceGraph
  state := permitState
  trace := permitTrace
  dag := noEdgeDAG 1 -- Edgeless fixture: causal-safety layer is structurally trivial here.
  governed := allGoverned 1
  trace_consistent := exampleGovernanceTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 exampleGovernanceGraph

/-- The concrete example graph is non-vacuous under the standard permit trace. -/
def exampleGovernanceNonVacuousWitness :
    NonVacuousWitness exampleGovernanceGraph permitTrace where
  wellFormed := by
    simp [exampleGovernanceGraph, WellFormed]
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

/-- The example graph satisfies the kernel non-vacuity axiom. -/
lemma exampleGovernance_nonvacuous :
    NonVacuous exampleGovernanceGraph permitTrace :=
  ⟨exampleGovernanceNonVacuousWitness⟩

private def exampleGovernanceLayerEval : LayerEval 0 where
  eval := fun L => nomatch L

/-- Concrete kernel data over the five-node governance graph. -/
noncomputable def exampleGovernanceKernelData :
    LegitimacyKernelData exampleGovernedSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification exampleGovernedSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent exampleGovernedSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer exampleGovernedSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer exampleGovernedSystem
  answer_consistent := state_answer_consistent exampleGovernedSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := uniK5
  spectralSignal := sig5
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange sig5
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := exampleGovernanceLayerEval
  overrideOvs := []

/-- Concrete kernel data over the same five-node governance graph, but with a
nontrivial Bool action alphabet for content-linked joint-capability fixtures. -/
noncomputable def boolGovernanceKernelData :
    LegitimacyKernelData exampleGovernedSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification exampleGovernedSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent exampleGovernedSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer exampleGovernedSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer exampleGovernedSystem
  answer_consistent := state_answer_consistent exampleGovernedSystem
  actionSpace := boolActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun
    | true => 1
    | false => 0
  spectralGraph := uniK5
  spectralSignal := sig5
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange sig5
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := exampleGovernanceLayerEval
  overrideOvs := []

private lemma exampleGovernance_spectralWellConnected_iff :
    SpectralWellConnected exampleGovernanceKernelData.spectralGraph
      exampleGovernanceKernelData.spectralSignal
      exampleGovernedSystem.graph.weightedSize_atLeastTwo ↔
    SpectralWellConnected uniK5 sig5 (by norm_num : 2 ≤ 5) := by
  rfl

/-- Runtime kernel witness for the concrete governance-graph example. -/
@[reducible]
noncomputable def exampleGovernanceRuntimeKernel :
    IsLegitimacyKernel exampleGovernanceKernelData where
  certifiable :=
    graphReplayCertification_certifiable exampleGovernedSystem.graph
  observable := state_id_observable exampleGovernedSystem
  corrigible :=
    kernelCorrigible_zero _ permit_corrigible (by intro a; rfl)
  compositionalSafety :=
    LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
      (noEdge_causal_soundness 1 (allGoverned 1))
  nonVacuous :=
    LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
      exampleGovernance_nonvacuous

/-- Runtime kernel witness for the Bool-action concrete governance example. -/
@[reducible]
noncomputable def boolGovernanceRuntimeKernel :
    IsLegitimacyKernel boolGovernanceKernelData where
  certifiable :=
    graphReplayCertification_certifiable exampleGovernedSystem.graph
  observable := state_id_observable exampleGovernedSystem
  corrigible := by
    refine ⟨permit_bool_corrigible, ?_⟩
    refine ⟨1, by norm_num, ?_⟩
    intro action
    cases action <;> simp [boolGovernanceKernelData]
  compositionalSafety :=
    LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
      (noEdge_causal_soundness 1 (allGoverned 1))
  nonVacuous :=
    LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
      exampleGovernance_nonvacuous

/-- The concrete example uses the discharged `uniK5` spectral certificate. -/
lemma exampleGovernance_spectralWellConnected :
    SpectralWellConnected exampleGovernanceKernelData.spectralGraph
      exampleGovernanceKernelData.spectralSignal
      exampleGovernedSystem.graph.weightedSize_atLeastTwo := by
  exact exampleGovernance_spectralWellConnected_iff.mpr
    ((SpectralWellConnected_iff_at_default uniK5 sig5
      (by norm_num : 2 ≤ 5)).2
      (uniK5_actualSpectralWellConnectedAt_of_le
        (by norm_num : (17 / 20 : ℚ) ≤ 46 / 53)))

/-- The Bool-action example uses the same discharged `uniK5` spectral
certificate; only its action alphabet differs. -/
lemma boolGovernance_spectralWellConnected :
    SpectralWellConnected boolGovernanceKernelData.spectralGraph
      boolGovernanceKernelData.spectralSignal
      exampleGovernedSystem.graph.weightedSize_atLeastTwo := by
  exact exampleGovernance_spectralWellConnected

/-- The concrete `uniK5`/`sig5` carrier is the grounded carrier for the
five-stage permit graph. -/
lemma exampleGovernance_spectralCarrierRepresentsGraph :
    SpectralCarrierRepresentsGraph exampleGovernedSystem.graph
      uniK5
      sig5 where
  claimantProjects := by
    intro i
    refine ⟨⟨i.val, i.val + 1, by exact_mod_cast Nat.succ_pos i.val, []⟩, ?_, rfl⟩
    simp [GovernanceGraph.profileClaims]
  graphSize := by
    simp [GovernanceGraph.weightedSize, exampleGovernedSystem,
      exampleGovernanceGraph]
  canonicalProfileRecovery := by
    intro representative _hsize hclass i
    have hspectral :
        ∀ i : Fin exampleGovernedSystem.graph.weightedSize,
          spectralCarrierDecision uniK5 sig5 i = BinaryDecision.Permit := by
      -- native_decide: finite `uniK5`/`sig5` spectral readout over five nodes.
      native_decide
    calc
      spectralCarrierDecision uniK5 sig5 i = BinaryDecision.Permit :=
        hspectral i
      _ = graphDecide exampleGovernedSystem.graph
          exampleGovernedSystem.graph.profileClaims i.val :=
        (exampleGovernanceGraph_decides_permit
          exampleGovernedSystem.graph.profileClaims i.val).symm
      _ = graphDecide representative representative.profileClaims i.val :=
        (hclass.2 i).symm
  peerSurfacePositiveCV := by
    intro pref tail _hsurface
    change 0 < uniK5.cv sig5
    rw [fiveNode_cv_values.1]
    norm_num

/-- A threshold gate that permits only claimants whose submitted claim strength
is strictly above the supplied threshold. Missing or weak claims are denied. -/
def strengthThresholdNode (threshold : ℚ) : GovernanceNodeFn :=
  fun claims claimant =>
    if ∃ claim ∈ claims, claim.id = claimant ∧ threshold < claim.strength then
      BinaryDecision.Permit
    else
      BinaryDecision.Deny

/-- A claimant-index threshold gate used by the non-constant carrier fixture. It
distinguishes claimants without depending on mutable claim strength, so the
worked semantic-kernel instance can satisfy the scale-invariance diagnostic. -/
def claimantThresholdNode (threshold : ClaimantId) : GovernanceNodeFn :=
  fun _ claimant =>
    if threshold < claimant then BinaryDecision.Permit else BinaryDecision.Deny

/-- A five-stage graph with a non-uniform canonical profile: the threshold gate
denies low-index canonical claimants before the remaining permit stages. -/
def thresholdGovernanceGraph : GovernanceGraph :=
  [ claimantThresholdNode 2
  , examplePermitNode
  , examplePermitNode
  , examplePermitNode
  , examplePermitNode
  ]

lemma thresholdGovernanceGraph_decides
    (claims : List ClaimQ) (claimant : ClaimantId) :
    graphDecide thresholdGovernanceGraph claims claimant =
      if 2 < claimant then BinaryDecision.Permit else BinaryDecision.Deny := by
  by_cases h : 2 < claimant <;>
    simp [thresholdGovernanceGraph, claimantThresholdNode, examplePermitNode,
      graphDecide, h]

lemma thresholdGovernanceGraph_allLegitimacyAxioms :
    AllLegitimacyAxioms thresholdGovernanceGraph := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro claims k j hk hj hkj hdist hdeny
    simp [thresholdGovernanceGraph_decides]
  · intro claims α hα j hj
    simp [thresholdGovernanceGraph_decides]
  · intro claims k s' hs' j hk hdist hle hperm
    simp [thresholdGovernanceGraph_decides] at hperm ⊢
    exact hperm
  · intro claims k s_r hs_r hk hdist hperm
    simp [thresholdGovernanceGraph_decides] at hperm ⊢
    exact hperm

/-- The threshold graph emits both decisions on its canonical profile. -/
lemma thresholdGovernanceGraph_profile_decisions_vary :
    graphDecide thresholdGovernanceGraph
        thresholdGovernanceGraph.profileClaims 0 = BinaryDecision.Deny ∧
      graphDecide thresholdGovernanceGraph
        thresholdGovernanceGraph.profileClaims 3 = BinaryDecision.Permit := by
  native_decide

/-- A concrete signal whose `uniK5` readout denies the first three carrier
nodes and permits the final two carrier nodes. -/
def thresholdSpectralSignal : Fin thresholdGovernanceGraph.weightedSize → ℚ :=
  ![10, 10, 10, -10, -10]

/-- The threshold signal also emits both decisions through the spectral
readout, so the carrier side is not constant. -/
lemma thresholdSpectralSignal_decisions_vary :
    spectralCarrierDecision uniK5 thresholdSpectralSignal ⟨0, by native_decide⟩ =
        BinaryDecision.Deny ∧
      spectralCarrierDecision uniK5 thresholdSpectralSignal
          ⟨3, by native_decide⟩ =
        BinaryDecision.Permit := by
  native_decide

/-- The mixed `uniK5`/threshold-signal carrier represents a threshold
governance graph whose canonical profile contains both deny and permit
outcomes. -/
lemma thresholdGovernance_spectralCarrierRepresentsGraph :
    SpectralCarrierRepresentsGraph thresholdGovernanceGraph
      uniK5
      thresholdSpectralSignal where
  claimantProjects := by
    intro i
    refine ⟨⟨i.val, i.val + 1, by exact_mod_cast Nat.succ_pos i.val, []⟩, ?_, rfl⟩
    simp [GovernanceGraph.profileClaims]
  graphSize := by
    simp [GovernanceGraph.weightedSize, thresholdGovernanceGraph]
  canonicalProfileRecovery := by
    intro representative _hsize hclass i
    have hbase :
        ∀ i : Fin thresholdGovernanceGraph.weightedSize,
          spectralCarrierDecision uniK5 thresholdSpectralSignal i =
            graphDecide thresholdGovernanceGraph
              thresholdGovernanceGraph.profileClaims i.val := by
      -- native_decide: finite non-uniform `uniK5`/threshold graph profile.
      native_decide
    calc
      spectralCarrierDecision uniK5 thresholdSpectralSignal i =
          graphDecide thresholdGovernanceGraph
            thresholdGovernanceGraph.profileClaims i.val := hbase i
      _ = graphDecide representative representative.profileClaims i.val :=
        (hclass.2 i).symm
  peerSurfacePositiveCV := by
    intro pref tail _hsurface
    change 0 < uniK5.cv thresholdSpectralSignal
    native_decide

/-- Downstream client for the mixed threshold carrier: the representation
bridge is used to read back the graph's non-constant canonical profile. -/
lemma thresholdGovernance_carrierBridge_mixedProfile :
    spectralCarrierDecision uniK5 thresholdSpectralSignal
        ⟨0, by native_decide⟩ =
      graphDecide thresholdGovernanceGraph
        thresholdGovernanceGraph.profileClaims 0 ∧
    spectralCarrierDecision uniK5 thresholdSpectralSignal
        ⟨3, by native_decide⟩ =
      graphDecide thresholdGovernanceGraph
        thresholdGovernanceGraph.profileClaims 3 ∧
    graphDecide thresholdGovernanceGraph
        thresholdGovernanceGraph.profileClaims 0 = BinaryDecision.Deny ∧
    graphDecide thresholdGovernanceGraph
        thresholdGovernanceGraph.profileClaims 3 = BinaryDecision.Permit := by
  refine ⟨
    thresholdGovernance_spectralCarrierRepresentsGraph.decisionProfilePreserved
      ⟨0, by native_decide⟩,
    thresholdGovernance_spectralCarrierRepresentsGraph.decisionProfilePreserved
      ⟨3, by native_decide⟩,
    thresholdGovernanceGraph_profile_decisions_vary.1,
    thresholdGovernanceGraph_profile_decisions_vary.2⟩

/-- A concrete claim permitted by the claimant-threshold graph. -/
def thresholdPermitClaim : ClaimQ :=
  ⟨3, 4, by norm_num, []⟩

/-- A live trace for the non-constant threshold graph. -/
def thresholdPermitTrace : GovernanceTrace :=
  fun _ => (thresholdPermitClaim, some GovernanceOutcome.permit)

lemma thresholdGovernanceGraph_decides_thresholdPermitClaim :
    graphDecide thresholdGovernanceGraph [thresholdPermitClaim]
        thresholdPermitClaim.id = BinaryDecision.Permit := by
  simp [thresholdGovernanceGraph_decides, thresholdPermitClaim]

lemma thresholdPermitTrace_consistent :
    TraceConsistentWithGraph thresholdPermitTrace thresholdGovernanceGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, thresholdPermitTrace]
  exact ⟨[thresholdPermitClaim], by simp,
    thresholdGovernanceGraph_decides_thresholdPermitClaim⟩

/-- A governed system backed by the non-constant threshold graph. -/
def thresholdGovernedSystem : GovernedSystem 1 where
  graph := thresholdGovernanceGraph
  state := permitState
  trace := thresholdPermitTrace
  dag := noEdgeDAG 1 -- Edgeless fixture: causal-safety layer is structurally trivial here.
  governed := allGoverned 1
  trace_consistent := thresholdPermitTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 thresholdGovernanceGraph

lemma thresholdPermitTrace_bounded :
    BoundedDisposition thresholdPermitTrace [thresholdPermitClaim] := by
  refine ⟨0, ?_⟩
  intro c hc
  simp [ReachesDispositionWithin, thresholdPermitTrace] at hc ⊢
  exact hc.symm

lemma thresholdPermitTrace_permitEligible :
    PermitEligible thresholdPermitTrace [thresholdPermitClaim] := by
  intro c hc
  refine ⟨0, ?_⟩
  simp [thresholdPermitTrace] at hc ⊢
  exact hc.symm

def thresholdGovernanceNonVacuousWitness :
    NonVacuousWitness thresholdGovernanceGraph thresholdPermitTrace where
  wellFormed := by
    simp [thresholdGovernanceGraph, WellFormed]
  governedClaims := [thresholdPermitClaim]
  governed_nonempty := by
    simp
  boundedDisposition := thresholdPermitTrace_bounded
  permitEligibleClaims := [thresholdPermitClaim]
  eligible_nonempty := by
    simp
  eligible_subset := by
    intro c hc
    simpa using hc
  permitEligible := thresholdPermitTrace_permitEligible
  notRefusal := by
    intro h
    have hdeny := h 0
    simp [thresholdPermitTrace] at hdeny
  notPermanentEscalation := by
    intro h
    have hesc := h 0
    simp [thresholdPermitTrace] at hesc
  notDeadlock := by
    intro h
    have hnone := h 0
    simp [thresholdPermitTrace] at hnone

lemma thresholdGovernance_nonvacuous :
    NonVacuous thresholdGovernanceGraph thresholdPermitTrace :=
  ⟨thresholdGovernanceNonVacuousWitness⟩

noncomputable def thresholdGovernanceKernelData :
    LegitimacyKernelData thresholdGovernedSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification thresholdGovernedSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent thresholdGovernedSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer thresholdGovernedSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer thresholdGovernedSystem
  answer_consistent := state_answer_consistent thresholdGovernedSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := uniK5
  spectralSignal := thresholdSpectralSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange thresholdSpectralSignal
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := exampleGovernanceLayerEval
  overrideOvs := []

@[reducible]
noncomputable def thresholdGovernanceRuntimeKernel :
    IsLegitimacyKernel thresholdGovernanceKernelData where
  certifiable :=
    graphReplayCertification_certifiable thresholdGovernedSystem.graph
  observable := state_id_observable thresholdGovernedSystem
  corrigible :=
    kernelCorrigible_zero _ permit_corrigible (by intro a; rfl)
  compositionalSafety :=
    LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
      (noEdge_causal_soundness 1 (allGoverned 1))
  nonVacuous :=
    LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
      thresholdGovernance_nonvacuous

private lemma thresholdGovernance_spectralWellConnected_iff :
    SpectralWellConnected thresholdGovernanceKernelData.spectralGraph
      thresholdGovernanceKernelData.spectralSignal
      thresholdGovernedSystem.graph.weightedSize_atLeastTwo ↔
    SpectralWellConnected uniK5 thresholdSpectralSignal
      (by norm_num : 2 ≤ 5) := by
  rfl

lemma thresholdGovernance_spectralWellConnected :
    SpectralWellConnected thresholdGovernanceKernelData.spectralGraph
      thresholdGovernanceKernelData.spectralSignal
      thresholdGovernedSystem.graph.weightedSize_atLeastTwo := by
  exact thresholdGovernance_spectralWellConnected_iff.mpr
    ((SpectralWellConnected_iff_at_default uniK5
      thresholdSpectralSignal (by norm_num : 2 ≤ 5)).2 (by
      unfold SpectralWellConnectedAt
      constructor
      · unfold SpectralConnected
        rw [uniK5_spectralGap_eq_certificate]
        norm_num [fiveNodeCompleteSpectralGapCertificate]
      · unfold PositiveGovernanceVulnerabilityAt
        rw [uniK5_spectralGap_eq_certificate]
        have hcv : uniK5.cv thresholdSpectralSignal = 5 := by
          native_decide
        norm_num [fiveNodeCompleteSpectralGapCertificate, hcv]))

/-- Semantic kernel witness whose carrier readout is non-constant on the
canonical threshold profile. -/
@[reducible]
noncomputable def thresholdGovernanceSemanticKernel :
    IsSemanticLegitimacyKernel thresholdGovernanceKernelData where
  runtimeKernel := thresholdGovernanceRuntimeKernel
  semanticBridge :=
    ⟨thresholdGovernanceGraph_allLegitimacyAxioms,
      by
        simpa [thresholdGovernanceKernelData] using
          thresholdGovernance_spectralCarrierRepresentsGraph,
      thresholdGovernance_spectralWellConnected⟩

/-- Semantic kernel witness for the concrete governance-graph example. -/
@[reducible]
noncomputable def exampleGovernanceSemanticKernel :
    IsSemanticLegitimacyKernel exampleGovernanceKernelData where
  runtimeKernel := exampleGovernanceRuntimeKernel
  semanticBridge :=
    ⟨exampleGovernanceGraph_allLegitimacyAxioms,
      by
        simpa using
          exampleGovernance_spectralCarrierRepresentsGraph,
      exampleGovernance_spectralWellConnected⟩

/-- Semantic kernel witness for the nontrivial Bool-action governance example. -/
@[reducible]
noncomputable def boolGovernanceSemanticKernel :
    IsSemanticLegitimacyKernel boolGovernanceKernelData where
  runtimeKernel := boolGovernanceRuntimeKernel
  semanticBridge :=
    ⟨exampleGovernanceGraph_allLegitimacyAxioms,
      by
        simpa [boolGovernanceKernelData] using
          exampleGovernance_spectralCarrierRepresentsGraph,
      boolGovernance_spectralWellConnected⟩

/-- A widened concrete signal over the same five-node governance carrier. -/
def exampleGovernanceWideSignal : Fin exampleGovernedSystem.graph.weightedSize → ℚ :=
  ![2, 4, 6, 8, 10]

/-- The widened signal has a concrete cached range. -/
lemma exampleGovernanceWideSignal_signalRange :
    Legitimacy.signalRange exampleGovernanceWideSignal = 8 := by
  -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
  native_decide

private lemma exampleGovernanceWideSignal_spectralWellConnected_iff :
    SpectralWellConnected exampleGovernanceKernelData.spectralGraph
      exampleGovernanceWideSignal
      exampleGovernedSystem.graph.weightedSize_atLeastTwo ↔
    SpectralWellConnected uniK5 exampleGovernanceWideSignal
      (by norm_num : 2 ≤ 5) := by
  rfl

/-- The widened signal keeps the concrete `uniK5` carrier inside the discharged
spectral well-connected cone. -/
lemma exampleGovernanceWideSignal_spectralWellConnected :
    SpectralWellConnected exampleGovernanceKernelData.spectralGraph
      exampleGovernanceWideSignal
      exampleGovernedSystem.graph.weightedSize_atLeastTwo := by
  exact exampleGovernanceWideSignal_spectralWellConnected_iff.mpr
    ((SpectralWellConnected_iff_at_default uniK5
      exampleGovernanceWideSignal (by norm_num : 2 ≤ 5)).2 (by
      unfold SpectralWellConnectedAt
      constructor
      · unfold SpectralConnected
        rw [uniK5_spectralGap_eq_certificate]
        norm_num [fiveNodeCompleteSpectralGapCertificate]
      · unfold PositiveGovernanceVulnerabilityAt
        rw [uniK5_spectralGap_eq_certificate]
        have hcv : uniK5.cv exampleGovernanceWideSignal = 3 / 2 := by
          -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
          native_decide
        norm_num [fiveNodeCompleteSpectralGapCertificate, hcv]))

/-- The widened signal remains a grounded carrier for the five-stage permit
graph. -/
lemma exampleGovernanceWideSignal_spectralCarrierRepresentsGraph :
    SpectralCarrierRepresentsGraph exampleGovernedSystem.graph
      uniK5
      exampleGovernanceWideSignal where
  claimantProjects := by
    intro i
    refine ⟨⟨i.val, i.val + 1, by exact_mod_cast Nat.succ_pos i.val, []⟩, ?_, rfl⟩
    simp [GovernanceGraph.profileClaims]
  graphSize := by
    simp [GovernanceGraph.weightedSize, exampleGovernedSystem,
      exampleGovernanceGraph]
  canonicalProfileRecovery := by
    intro representative _hsize hclass i
    have hspectral :
        ∀ i : Fin exampleGovernedSystem.graph.weightedSize,
          spectralCarrierDecision uniK5 exampleGovernanceWideSignal i =
            BinaryDecision.Permit := by
      -- native_decide: finite `uniK5` widened-signal spectral readout.
      native_decide
    calc
      spectralCarrierDecision uniK5 exampleGovernanceWideSignal i =
          BinaryDecision.Permit :=
        hspectral i
      _ = graphDecide exampleGovernedSystem.graph
          exampleGovernedSystem.graph.profileClaims i.val :=
        (exampleGovernanceGraph_decides_permit
          exampleGovernedSystem.graph.profileClaims i.val).symm
      _ = graphDecide representative representative.profileClaims i.val :=
        (hclass.2 i).symm
  peerSurfacePositiveCV := by
    intro pref tail _hsurface
    change 0 < uniK5.cv exampleGovernanceWideSignal
    have hcv : uniK5.cv exampleGovernanceWideSignal = 3 / 2 := by
      -- native_decide: finite concrete kernel-safety fixture equality.
      native_decide
    rw [hcv]
    norm_num

/-- Concrete target datum for a non-refl kernel step: the governance graph and
runtime kernel interfaces are unchanged, while the spectral signal and cached
range are mutated. -/
noncomputable def exampleGovernanceWideSignalKernelData :
    LegitimacyKernelData exampleGovernedSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification exampleGovernedSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent exampleGovernedSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer exampleGovernedSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer exampleGovernedSystem
  answer_consistent := state_answer_consistent exampleGovernedSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := uniK5
  spectralSignal := exampleGovernanceWideSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange exampleGovernanceWideSignal
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := exampleGovernanceLayerEval
  overrideOvs := []

private lemma exampleGovernanceWideSignalKernelData_signalRange_eq_iff :
    exampleGovernanceKernelData.signalRange =
      exampleGovernanceWideSignalKernelData.signalRange ↔
    Legitimacy.signalRange sig5 =
      Legitimacy.signalRange exampleGovernanceWideSignal := by
  rfl

/-- Runtime kernel witness for the widened-signal target datum. -/
@[reducible]
noncomputable def exampleGovernanceWideSignalRuntimeKernel :
    IsLegitimacyKernel exampleGovernanceWideSignalKernelData where
  certifiable :=
    graphReplayCertification_certifiable exampleGovernedSystem.graph
  observable := state_id_observable exampleGovernedSystem
  corrigible :=
    kernelCorrigible_zero _ permit_corrigible (by intro a; rfl)
  compositionalSafety :=
    LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
      (noEdge_causal_soundness 1 (allGoverned 1))
  nonVacuous :=
    LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
      exampleGovernance_nonvacuous

/-- Semantic kernel witness for the widened-signal target datum. -/
@[reducible]
noncomputable def exampleGovernanceWideSignalSemanticKernel :
    IsSemanticLegitimacyKernel exampleGovernanceWideSignalKernelData where
  runtimeKernel := exampleGovernanceWideSignalRuntimeKernel
  semanticBridge :=
    ⟨exampleGovernanceGraph_allLegitimacyAxioms,
      by
        simpa [exampleGovernanceWideSignalKernelData] using
          exampleGovernanceWideSignal_spectralCarrierRepresentsGraph,
      exampleGovernanceWideSignal_spectralWellConnected⟩

/-- The widened-signal datum is propositionally distinct from the source datum:
the cached signal range changes from `4` to `8`. -/
lemma exampleGovernanceWideSignalKernelData_ne :
    exampleGovernanceKernelData ≠ exampleGovernanceWideSignalKernelData := by
  intro h
  have hrange := congrArg
    (fun D : LegitimacyKernelData exampleGovernedSystem => D.signalRange) h
  have hrange' :=
    exampleGovernanceWideSignalKernelData_signalRange_eq_iff.mp hrange
  rw [sig5_signalRange, exampleGovernanceWideSignal_signalRange] at hrange'
  norm_num at hrange'

/-- A concrete invariant-preserving kernel step over the example datum. -/
noncomputable def exampleGovernanceInvariantStep :
    KernelStep exampleGovernanceKernelData exampleGovernanceKernelData :=
  KernelStep.refl exampleGovernanceKernelData

/-- A concrete non-refl invariant-preserving kernel step over the example
datum. It mutates spectral signal data while preserving the shared governance
graph and carrying a concrete target semantic-kernel witness. -/
noncomputable def exampleGovernanceWideSignalStep :
    KernelStep exampleGovernanceKernelData
      exampleGovernanceWideSignalKernelData :=
  KernelStep.graphPreservingSpectralMutation
    exampleGovernanceKernelData
    exampleGovernanceWideSignalKernelData
    exampleGovernanceWideSignalSemanticKernel

/-- The widened-signal step is genuinely non-refl at the kernel-data level. -/
lemma exampleGovernanceWideSignalStep_nonrefl :
    exampleGovernanceKernelData ≠ exampleGovernanceWideSignalKernelData :=
  exampleGovernanceWideSignalKernelData_ne

/-- A concrete one-step trajectory using the non-refl widened-signal mutation. -/
noncomputable def exampleGovernanceWideSignalTrajectory :
    KernelGovernedTrajectory exampleGovernedSystem
      exampleGovernanceKernelData exampleGovernanceWideSignalKernelData :=
  KernelGovernedTrajectory.singleInvariantStep
    exampleGovernanceWideSignalStep
    exampleGovernanceSemanticKernel

inductive exampleThresholdAction where
  | raiseThreshold
  deriving Repr, DecidableEq

/-- A concrete state-action interface whose only action applies the
supervisory degradation operation. -/
def exampleThresholdActionSpace : StateActionSpace where
  Action := exampleThresholdAction
  apply _ S := applySupervisory .degrade S

/-- The action-driven worked datum preserves the degradation action. -/
def exampleThresholdAlgebra : SupervisoryAlgebra :=
  {σ | σ = SupervisoryAction.degrade}

lemma exampleThresholdActionSpace_single_step_preserved :
    SingleStepPreserved exampleThresholdActionSpace exampleThresholdAlgebra := by
  intro a S hsupports σ hσ
  have hdegrade : σ = SupervisoryAction.degrade := hσ
  subst hdegrade
  exact applySupervisory_degrade_supported S (hsupports rfl)

lemma exampleGovernedSystem_supports_threshold_algebra :
    SupportsAlgebra exampleGovernedSystem.state exampleThresholdAlgebra := by
  intro σ hσ
  have hdegrade : σ = SupervisoryAction.degrade := hσ
  subst hdegrade
  simp [SupportsSupervisory, exampleGovernedSystem, permitState]

/-- Source datum for an action-driven kernel step. It has the same graph and
spectral package as the base governance example, but exposes the concrete
threshold-raising action instead of the inert action space. -/
noncomputable def exampleThresholdKernelData :
    LegitimacyKernelData exampleGovernedSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification exampleGovernedSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent exampleGovernedSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer exampleGovernedSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer exampleGovernedSystem
  answer_consistent := state_answer_consistent exampleGovernedSystem
  actionSpace := exampleThresholdActionSpace
  algebra := exampleThresholdAlgebra
  actionCapability := fun _ => 1
  spectralGraph := uniK5
  spectralSignal := sig5
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange sig5
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := exampleGovernanceLayerEval
  overrideOvs := []

/-- Target datum selected after the threshold-raising action replay. -/
noncomputable def exampleThresholdWideSignalKernelData :
    LegitimacyKernelData exampleGovernedSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification exampleGovernedSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent exampleGovernedSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer exampleGovernedSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer exampleGovernedSystem
  answer_consistent := state_answer_consistent exampleGovernedSystem
  actionSpace := exampleThresholdActionSpace
  algebra := exampleThresholdAlgebra
  actionCapability := fun _ => 1
  spectralGraph := uniK5
  spectralSignal := exampleGovernanceWideSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange exampleGovernanceWideSignal
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := exampleGovernanceLayerEval
  overrideOvs := []

private lemma exampleThresholdWideSignalKernelData_signalRange_eq_iff :
    exampleThresholdKernelData.signalRange =
      exampleThresholdWideSignalKernelData.signalRange ↔
    Legitimacy.signalRange sig5 =
      Legitimacy.signalRange exampleGovernanceWideSignal := by
  rfl

@[reducible]
noncomputable def exampleThresholdRuntimeKernel :
    IsLegitimacyKernel exampleThresholdKernelData where
  certifiable :=
    graphReplayCertification_certifiable exampleGovernedSystem.graph
  observable := state_id_observable exampleGovernedSystem
  corrigible :=
    kernelCorrigible_const _
      { supports_algebra := exampleGovernedSystem_supports_threshold_algebra
        single_step_preserved :=
          exampleThresholdActionSpace_single_step_preserved }
      1 (by norm_num) (by intro a; rfl)
  compositionalSafety :=
    LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
      (noEdge_causal_soundness 1 (allGoverned 1))
  nonVacuous :=
    LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
      exampleGovernance_nonvacuous

@[reducible]
noncomputable def exampleThresholdWideSignalRuntimeKernel :
    IsLegitimacyKernel exampleThresholdWideSignalKernelData where
  certifiable :=
    graphReplayCertification_certifiable exampleGovernedSystem.graph
  observable := state_id_observable exampleGovernedSystem
  corrigible :=
    kernelCorrigible_const _
      { supports_algebra := exampleGovernedSystem_supports_threshold_algebra
        single_step_preserved :=
          exampleThresholdActionSpace_single_step_preserved }
      1 (by norm_num) (by intro a; rfl)
  compositionalSafety :=
    LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
      (noEdge_causal_soundness 1 (allGoverned 1))
  nonVacuous :=
    LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
      exampleGovernance_nonvacuous

@[reducible]
noncomputable def exampleThresholdSemanticKernel :
    IsSemanticLegitimacyKernel exampleThresholdKernelData where
  runtimeKernel := exampleThresholdRuntimeKernel
  semanticBridge :=
    ⟨exampleGovernanceGraph_allLegitimacyAxioms,
      by
        simpa [exampleThresholdKernelData] using
          exampleGovernance_spectralCarrierRepresentsGraph,
      exampleGovernance_spectralWellConnected⟩

@[reducible]
noncomputable def exampleThresholdWideSignalSemanticKernel :
    IsSemanticLegitimacyKernel exampleThresholdWideSignalKernelData where
  runtimeKernel := exampleThresholdWideSignalRuntimeKernel
  semanticBridge :=
    ⟨exampleGovernanceGraph_allLegitimacyAxioms,
      by
        simpa [exampleThresholdWideSignalKernelData] using
          exampleGovernanceWideSignal_spectralCarrierRepresentsGraph,
      exampleGovernanceWideSignal_spectralWellConnected⟩

/-- Replaying the concrete threshold action changes the supervisory state. -/
lemma exampleThresholdAction_replay_changes_state :
    exampleThresholdActionSpace.applySeq
        [exampleThresholdAction.raiseThreshold] exampleGovernedSystem.state ≠
      exampleGovernedSystem.state := by
  intro h
  have hthresholds := congrArg GovernanceState.thresholds h
  simp [StateActionSpace.applySeq, exampleThresholdActionSpace,
    applySupervisory, exampleGovernedSystem, permitState] at hthresholds

/-- The action replay selects the widened-signal target exactly when the
supervisory thresholds have been raised. -/
noncomputable def exampleThresholdTargetFromReplay
    (S : GovernanceState) : LegitimacyKernelData exampleGovernedSystem :=
  if S.thresholds = [2] then
    exampleThresholdWideSignalKernelData
  else
    exampleThresholdKernelData

lemma exampleThresholdTargetFromReplay_after_raise :
    exampleThresholdTargetFromReplay
        (exampleThresholdActionSpace.applySeq
          [exampleThresholdAction.raiseThreshold] exampleGovernedSystem.state) =
      exampleThresholdWideSignalKernelData := by
  simp [exampleThresholdTargetFromReplay, exampleThresholdActionSpace,
    StateActionSpace.applySeq, applySupervisory, exampleGovernedSystem,
    permitState]

lemma exampleThresholdTargetFromReplay_after_raise_invariant :
    KernelInvariant
      (exampleThresholdTargetFromReplay
        (exampleThresholdActionSpace.applySeq
          [exampleThresholdAction.raiseThreshold]
          exampleGovernedSystem.state)) := by
  rw [exampleThresholdTargetFromReplay_after_raise]
  exact exampleThresholdWideSignalSemanticKernel

/-- Concrete nonempty, state-changing kernel step whose target datum is chosen
from the replayed supervisory action trace. -/
noncomputable def exampleThresholdActionDrivenStep :
    KernelStep exampleThresholdKernelData
      (exampleThresholdTargetFromReplay
        (exampleThresholdActionSpace.applySeq
          [exampleThresholdAction.raiseThreshold]
          exampleGovernedSystem.state)) :=
  KernelStep.actionDrivenSpectralMutation
    exampleThresholdKernelData
    [exampleThresholdAction.raiseThreshold]
    (by simp)
    exampleThresholdTargetFromReplay
    exampleThresholdAction_replay_changes_state
    exampleThresholdTargetFromReplay_after_raise_invariant

private lemma exampleThresholdActionDrivenStep_action_trace_eq :
    exampleThresholdActionDrivenStep.action_trace =
      [exampleThresholdAction.raiseThreshold] := by
  rfl

lemma exampleThresholdActionDrivenStep_trace_nonempty :
    exampleThresholdActionDrivenStep.action_trace ≠ [] := by
  rw [exampleThresholdActionDrivenStep_action_trace_eq]
  simp

lemma exampleThresholdActionDrivenStep_realized_state_changed :
    exampleThresholdActionDrivenStep.realized_state ≠
      exampleGovernedSystem.state := by
  simpa [exampleThresholdActionDrivenStep] using
    exampleThresholdAction_replay_changes_state

lemma exampleThresholdWideSignalKernelData_ne :
    exampleThresholdKernelData ≠ exampleThresholdWideSignalKernelData := by
  intro h
  have hrange := congrArg
    (fun D : LegitimacyKernelData exampleGovernedSystem => D.signalRange) h
  have hrange' :=
    exampleThresholdWideSignalKernelData_signalRange_eq_iff.mp hrange
  rw [sig5_signalRange, exampleGovernanceWideSignal_signalRange] at hrange'
  norm_num at hrange'

lemma exampleThresholdActionDrivenStep_target_nonrefl :
    exampleThresholdKernelData ≠
      exampleThresholdTargetFromReplay
        (exampleThresholdActionSpace.applySeq
          [exampleThresholdAction.raiseThreshold]
          exampleGovernedSystem.state) := by
  rw [exampleThresholdTargetFromReplay_after_raise]
  exact exampleThresholdWideSignalKernelData_ne

/-- Concrete trajectory using the action-driven nonempty kernel step. -/
noncomputable def exampleThresholdActionDrivenTrajectory :
    KernelGovernedTrajectory exampleGovernedSystem
      exampleThresholdKernelData
      (exampleThresholdTargetFromReplay
        (exampleThresholdActionSpace.applySeq
          [exampleThresholdAction.raiseThreshold]
          exampleGovernedSystem.state)) :=
  KernelGovernedTrajectory.singleInvariantStep
    exampleThresholdActionDrivenStep
    exampleThresholdSemanticKernel

/-- A concrete two-step kernel-governed trajectory over the example graph. -/
noncomputable def exampleGovernanceTrajectory :
    KernelGovernedTrajectory exampleGovernedSystem
      exampleGovernanceKernelData exampleGovernanceKernelData :=
  KernelGovernedTrajectory.invariant_step
    exampleGovernanceInvariantStep
    exampleGovernanceSemanticKernel
    exampleGovernanceSemanticKernel
    (KernelGovernedTrajectory.singleInvariantStep
      exampleGovernanceInvariantStep
      exampleGovernanceSemanticKernel)
end Safety

end Legitimacy
