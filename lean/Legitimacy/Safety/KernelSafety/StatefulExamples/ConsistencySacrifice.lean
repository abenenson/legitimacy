/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.StatefulExamples.Conclusions

/-!
# Legitimacy.Safety.KernelSafety.StatefulExamples.ConsistencySacrifice

Concrete peer-relative and length-sensitive surfaces for consistency-sacrifice examples.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-- Singleton graph exposing the length-sensitive consistency-violation
witness node. -/
def lengthThreeSurvivorGraph : GovernanceGraph :=
  [lengthThreeSurvivorNode]

/-- The singleton length-sensitive graph exposes `lengthThreeSurvivorNode` as
its complete first-effective head node. -/
theorem lengthThreeSurvivorGraph_effectiveSurface :
    BinaryDecisionPipeline.EffectiveSurfaceForNode
      (P := GovernanceGraph) lengthThreeSurvivorNode
      lengthThreeSurvivorGraph [] [] := by
  constructor
  · rfl
  · intro node hnode
    cases hnode

/-- The singleton length-sensitive graph has the empty complete tail after its
exposed head node. -/
theorem lengthThreeSurvivorGraph_completeTail :
    BinaryDecisionPipeline.CompleteTailForNode
      (P := GovernanceGraph) lengthThreeSurvivorNode [] := by
  intro claims k _hpermit
  rfl

private def lengthThreePermittedClaim : ClaimQ :=
  ⟨2, 1, by norm_num, []⟩

private def lengthThreeSurvivorTrace : GovernanceTrace :=
  fun _ => (lengthThreePermittedClaim, some GovernanceOutcome.permit)

private lemma lengthThreeSurvivorGraph_decides_permit :
    graphDecide lengthThreeSurvivorGraph
        [lengthThreePermittedClaim] lengthThreePermittedClaim.id =
      BinaryDecision.Permit := by
  -- One-node graph decision on a fixed singleton claim profile.
  -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
  native_decide

private lemma lengthThreeSurvivorTrace_consistent :
    TraceConsistentWithGraph
      lengthThreeSurvivorTrace lengthThreeSurvivorGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, lengthThreeSurvivorTrace]
  exact ⟨[lengthThreePermittedClaim], by simp,
    lengthThreeSurvivorGraph_decides_permit⟩

/-- Governed system whose graph is the concrete length-sensitive consistency
violation surface. This lets the sacrifice-route worked example use the same
graph for the governed system, compiled artifact, and witness node. -/
def lengthThreeSurvivorSystem : GovernedSystem 1 where
  graph := lengthThreeSurvivorGraph
  state := permitState
  trace := lengthThreeSurvivorTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := lengthThreeSurvivorTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 lengthThreeSurvivorGraph

private def lengthThreeLayerEval : LayerEval 0 where
  eval := fun L => nomatch L

/-- The canonical singleton peer-relative graph exposes the peer-relative node
as its first effective surface. -/
theorem peerGraph_effectivePeerRelativeSurface :
    EffectivePeerRelativeSurface peerGraph [] [] := by
  · constructor
    · rfl
    · intro node hnode
      cases hnode

/-- The canonical singleton peer-relative graph has the empty complete tail. -/
theorem peerGraph_completePeerRelativeTail :
    CompletePeerRelativeTail [] := by
  intro claims k _hpermit
  rfl

/-- The canonical singleton peer-relative graph is a complete first-effective
surface with empty transparent prefix and empty complete tail. -/
theorem peerGraph_completePeerRelativeSurface :
    CompletePeerRelativeSurface peerGraph :=
  ⟨[], [], peerGraph_effectivePeerRelativeSurface,
    peerGraph_completePeerRelativeTail⟩

private lemma peerGraph_decides_permitClaim :
    graphDecide peerGraph [permitClaim] permitClaim.id =
      BinaryDecision.Permit := by
  -- native_decide: finite concrete singleton peer-relative graph evaluation.
  native_decide

private lemma peerGraph_permitTrace_consistent :
    TraceConsistentWithGraph permitTrace peerGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, permitTrace]
  exact ⟨[permitClaim], by simp, peerGraph_decides_permitClaim⟩

/-- Governed system for the canonical peer-relative surface used by the twin
headline worked example. -/
def peerSurfaceSystem : GovernedSystem 1 where
  graph := peerGraph
  state := permitState
  trace := permitTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := peerGraph_permitTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 peerGraph

/-- Kernel data over the canonical peer-relative surface. The worked example
uses it to thread the deployment-side consistency certificate into a concrete
one-step sacrifice trajectory. -/
noncomputable def peerSurfaceKernelData :
    LegitimacyKernelData peerSurfaceSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification peerSurfaceSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent peerSurfaceSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer peerSurfaceSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer peerSurfaceSystem
  answer_consistent := state_answer_consistent peerSurfaceSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := uniTriGraph
  spectralSignal := sig
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange sig
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := lengthThreeLayerEval
  overrideOvs := []

/-- Worked twin-headline example. On the deployment side,
`noUndeclaredSacrifice` forces consistency and monotonicity into the live
compiled ledger for the canonical complete peer-relative surface. On the
trajectory side, the emitted consistency certificate is replayed as a concrete
index-zero sacrifice step, and `kernelReachabilitySafety` supplies the
no-silent-degradation conclusion for that trajectory. The Rust integration
test `protocol_compile_rejects_peer_relative_surface_without_forced_sacrifices`
anchors the same empty-ledger gap at the runtime protocol gate. -/
theorem peerSurfaceWorkedExample_noUndeclaredDeployment_and_reachableSacrifice
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (hgraph : compiled.graph = peerSurfaceSystem.graph)
    (hlive : IsLiveCompiled compiled report monitoring) :
    ForcedPeerRelativeSacrificesDeclared compiled ∧
      ∃ cert : MonitoredSacrificeCertificate
          peerSurfaceKernelData peerSurfaceKernelData,
      ∃ h_traj :
          KernelGovernedTrajectory peerSurfaceSystem
            peerSurfaceKernelData peerSurfaceKernelData,
        cert.sacrificed =
          SacrificedAxiom.governance GovernanceProperty.Consistency ∧
          KernelGovernedTrajectory.HasSacrificeStepAt h_traj 0 ∧
          (∀ _hinit : KernelInvariant peerSurfaceKernelData,
            ReachableStateSafetyConclusion h_traj) := by
  have hsurface : CompletePeerRelativeSurface compiled.graph := by
    rw [hgraph]
    exact peerGraph_completePeerRelativeSurface
  have hforced :
      ForcedPeerRelativeSacrificesDeclared compiled :=
    ((noUndeclaredSacrifice hsurface).mp hlive).2
  have heffective :
      EffectivePeerRelativeSurface compiled.graph [] [] := by
    rw [hgraph]
    exact peerGraph_effectivePeerRelativeSurface
  have hcomplete : CompletePeerRelativeTail [] :=
    peerGraph_completePeerRelativeTail
  obtain ⟨hconsCert, _hmonCert⟩ :=
    effectivePeerRelativeSurface_live_forces_sacrifice_via_pipeline
      (KernelStep.refl peerSurfaceKernelData)
      (compiled := compiled) (report := report) (monitoring := monitoring)
      (pref := []) (tail := [])
      hlive heffective hcomplete hgraph
  rcases hconsCert with ⟨cert, hcert⟩
  let h_traj :
      KernelGovernedTrajectory peerSurfaceSystem
        peerSurfaceKernelData peerSurfaceKernelData :=
    KernelGovernedTrajectory.singleSacrificeStep cert
  have hsacrificeAt :
      KernelGovernedTrajectory.HasSacrificeStepAt h_traj 0 := by
    exact KernelGovernedTrajectory.HasSacrificeStepAt.here cert
      (KernelGovernedTrajectory.refl peerSurfaceKernelData)
  have hreachable :
      ∀ _hinit : KernelInvariant peerSurfaceKernelData,
        ReachableStateSafetyConclusion h_traj := by
    intro hinit
    exact kernelReachabilitySafety
      peerSurfaceKernelData peerSurfaceKernelData h_traj hinit
  exact ⟨hforced, cert, h_traj, hcert, hsacrificeAt, hreachable⟩

private def lengthThreeZeroSpectralGraph :
    GovGraph ℚ lengthThreeSurvivorSystem.graph.weightedSize where
  weights := fun _ _ => 0
  weight_symm := by
    intro _ _
    rfl
  weight_nonneg := by
    intro _ _
    norm_num
  weight_self_zero := by
    intro _
    rfl

/-- Kernel data over the length-sensitive consistency witness graph. The
stateful worked example only needs the quantitative datum and action surface;
it does not assume this graph satisfies the semantic kernel invariant. -/
noncomputable def lengthThreeSurvivorKernelData :
    LegitimacyKernelData lengthThreeSurvivorSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification lengthThreeSurvivorSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent lengthThreeSurvivorSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer lengthThreeSurvivorSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer lengthThreeSurvivorSystem
  answer_consistent := state_answer_consistent lengthThreeSurvivorSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := uniTriGraph
  spectralSignal := sig
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange sig
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := lengthThreeLayerEval
  overrideOvs := []

private lemma lengthThreeSurvivor_criticalCapability_normalized :
    kernelDataCriticalCapability lengthThreeSurvivorKernelData =
      C_star uniTriGraph sig (1 / 10) := by
  rfl

private lemma lengthThreeSurvivor_criticalCapability :
    kernelDataCriticalCapability lengthThreeSurvivorKernelData = 1 / 10 := by
  rw [lengthThreeSurvivor_criticalCapability_normalized]
  rw [C_star, concrete_cv_values.1]
  norm_num

private lemma lengthThreeSurvivor_tolerance_pos :
    0 < lengthThreeSurvivorKernelData.toleranceParameter := by
  norm_num [lengthThreeSurvivorKernelData]

private lemma lengthThreeSurvivor_cv_normalized :
    lengthThreeSurvivorKernelData.spectralGraph.cv
      lengthThreeSurvivorKernelData.spectralSignal =
    uniTriGraph.cv sig := by
  rfl

private lemma lengthThreeSurvivor_cv_pos :
    0 < lengthThreeSurvivorKernelData.spectralGraph.cv
      lengthThreeSurvivorKernelData.spectralSignal := by
  rw [lengthThreeSurvivor_cv_normalized]
  exact concrete_cv_pos.1

private lemma lengthThreeZero_spectralDistance_normalized :
    spectralDistance lengthThreeSurvivorKernelData.spectralGraph
        lengthThreeZeroSpectralGraph =
      spectralDistance uniTriGraph lengthThreeZeroSpectralGraph := by
  rfl

private lemma lengthThreeZeroSpectralGraph_not_subcritical :
    ¬ spectralDistance lengthThreeSurvivorKernelData.spectralGraph
        lengthThreeZeroSpectralGraph <
      kernelDataCriticalCapability lengthThreeSurvivorKernelData := by
  rw [lengthThreeSurvivor_criticalCapability]
  rw [lengthThreeZero_spectralDistance_normalized]
  -- Finite rational matrix evaluation over the concrete three-node fixture.
  -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
  native_decide

private def exampleSupercriticalMutatedState : GovernanceState :=
  applySupervisory .degrade lengthThreeSurvivorSystem.state

private lemma exampleSupercriticalMutatedState_ne :
    exampleSupercriticalMutatedState ≠ lengthThreeSurvivorSystem.state := by
  intro h
  have hthresholds := congrArg GovernanceState.thresholds h
  norm_num [exampleSupercriticalMutatedState, lengthThreeSurvivorSystem,
    applySupervisory, permitState] at hthresholds

private noncomputable def exampleSupercriticalStateRealization
    (S : GovernanceState) :
    GovGraph ℚ lengthThreeSurvivorSystem.graph.weightedSize := by
  classical
  exact if S = lengthThreeSurvivorSystem.state then
    lengthThreeSurvivorKernelData.spectralGraph
  else
    lengthThreeZeroSpectralGraph

private lemma lengthThreeSpectralDistance_to_zero_le_supercritical :
    spectralDistance lengthThreeSurvivorKernelData.spectralGraph
        lengthThreeZeroSpectralGraph ≤
      perturbationBound 100 := by
  rw [lengthThreeZero_spectralDistance_normalized]
  -- Finite rational comparison for the concrete supercritical example budget.
  -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
  native_decide

/-- Capability-positive stateful adversary whose proposal installs the concrete
degraded supervisory state and whose one-turn budget exceeds the datum's
critical capability. -/
noncomputable def exampleSupercriticalAdversary :
    StatefulAdversaryLayer lengthThreeSurvivorKernelData where
  Memory := Unit
  initialMemory := ()
  Proposal := Unit
  propose := fun _ _ => ()
  applyProposal := fun _ _ => exampleSupercriticalMutatedState
  capability := fun _ => 100
  observedClaims := fun _ =>
    lengthThreeSurvivorNode_hasConsistencyViolationWitness.claims
  observedClaimant := fun _ =>
    lengthThreeSurvivorNode_hasConsistencyViolationWitness.denied
  update := fun _ _ _ => ()
  stateRealization := exampleSupercriticalStateRealization
  stateCoherent := by
    simp [exampleSupercriticalStateRealization, lengthThreeSurvivorSystem]
  proposalRealization := fun _ _ => lengthThreeZeroSpectralGraph
  proposalRealizationCoherent := by
    intro _ _
    simp [exampleSupercriticalStateRealization,
      exampleSupercriticalMutatedState_ne]
  capabilityPerturbationBound := by
    intro _ S
    classical
    by_cases hS : S = lengthThreeSurvivorSystem.state
    · subst hS
      simpa [exampleSupercriticalStateRealization,
        exampleSupercriticalMutatedState_ne] using
        lengthThreeSpectralDistance_to_zero_le_supercritical
    · simp [exampleSupercriticalStateRealization, hS,
        exampleSupercriticalMutatedState_ne, spectralDistance_self,
        perturbationBound]

private lemma exampleSupercriticalAdversary_capability_normalized :
    exampleSupercriticalAdversary.capability () = (100 : ℚ) := by
  rfl

lemma exampleSupercriticalAdversary_capability_positive :
    0 < exampleSupercriticalAdversary.capability () := by
  rw [exampleSupercriticalAdversary_capability_normalized]
  norm_num

lemma exampleSupercriticalAdversary_mutates_initial_state :
    exampleSupercriticalAdversary.applyProposal ()
        lengthThreeSurvivorSystem.state ≠
      lengthThreeSurvivorSystem.state := by
  simpa [exampleSupercriticalAdversary] using
    exampleSupercriticalMutatedState_ne

noncomputable instance exampleSupercriticalAdversary_kernelPerturbationFree :
    IsKernelPerturbationFreeAdversary
      lengthThreeSurvivorKernelData exampleSupercriticalAdversary where
  kernel_action_zero_distance := by
    intro a S
    cases a
    simp [exampleSupercriticalAdversary, exampleSupercriticalStateRealization,
      lengthThreeSurvivorKernelData, idActionSpace, spectralDistance_self]

noncomputable instance exampleSupercriticalAdversary_locallyStable :
    IsLocallyStableStatefulAdversary
      lengthThreeSurvivorKernelData exampleSupercriticalAdversary
      lengthThreeSurvivorSystem.state
      (kernelDataCriticalCapability lengthThreeSurvivorKernelData) where
  stable_within_realization := by
    intro S hdist
    classical
    by_cases hS : S = lengthThreeSurvivorSystem.state
    · subst hS
      intro claims k
      rfl
    · exfalso
      apply lengthThreeZeroSpectralGraph_not_subcritical
      simpa [exampleSupercriticalAdversary,
        exampleSupercriticalStateRealization, hS] using hdist

def exampleSupercriticalSchedule :
    List (StatefulScheduleStep lengthThreeSurvivorKernelData) :=
  [StatefulScheduleStep.adversary]

lemma exampleSupercriticalTrajectoryPerturbationBound :
    statefulTrajectoryPerturbationBound
        lengthThreeSurvivorKernelData exampleSupercriticalAdversary
        exampleSupercriticalSchedule
        (initialStatefulAdversaryConfig
          lengthThreeSurvivorKernelData exampleSupercriticalAdversary) =
      100 := by
  simp [exampleSupercriticalSchedule, statefulTrajectoryPerturbationBound,
    statefulRealizedProposals, initialStatefulAdversaryConfig,
    exampleSupercriticalAdversary, perturbationBound]

lemma exampleSupercriticalAdversary_critical_le_budget :
    kernelDataCriticalCapability lengthThreeSurvivorKernelData ≤
      statefulTrajectoryPerturbationBound
        lengthThreeSurvivorKernelData exampleSupercriticalAdversary
        exampleSupercriticalSchedule
        (initialStatefulAdversaryConfig
          lengthThreeSurvivorKernelData exampleSupercriticalAdversary) := by
  rw [exampleSupercriticalTrajectoryPerturbationBound,
    lengthThreeSurvivor_criticalCapability]
  norm_num

private lemma exampleSupercriticalFinalRealization :
    exampleSupercriticalAdversary.stateRealization
        (applyStatefulTrajectory
          lengthThreeSurvivorKernelData exampleSupercriticalAdversary
          exampleSupercriticalSchedule
          (initialStatefulAdversaryConfig
            lengthThreeSurvivorKernelData
            exampleSupercriticalAdversary)).state =
      lengthThreeZeroSpectralGraph := by
  simp [exampleSupercriticalSchedule, applyStatefulTrajectory,
    applyStatefulStep, initialStatefulAdversaryConfig,
    exampleSupercriticalAdversary, exampleSupercriticalStateRealization,
    exampleSupercriticalMutatedState_ne]

private lemma exampleSupercriticalAdversary_not_boundedCorrigibility :
    ¬ BoundedCorrigibilityPreservedAt
        lengthThreeSurvivorKernelData exampleSupercriticalAdversary
        exampleSupercriticalSchedule
        (initialStatefulAdversaryConfig
          lengthThreeSurvivorKernelData exampleSupercriticalAdversary) := by
  intro hbounded
  exact lengthThreeZeroSpectralGraph_not_subcritical (by
    simpa [exampleSupercriticalFinalRealization] using hbounded.2.2)

/-- Worked supercritical route: with the length-sensitive consistency witness
as the live compiled surface, the general disjunction lands in the monitored
sacrifice branch and carries both the consistency witness tag and the concrete
stateful critical-capability violation. -/
theorem exampleSupercriticalAdversary_yields_consistency_sacrifice_right
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (hgraph : compiled.graph = lengthThreeSurvivorSystem.graph)
    (hlive : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring)) :
    ∃ cert :
      MonitoredSacrificeCertificate
        lengthThreeSurvivorKernelData lengthThreeSurvivorKernelData,
      WorkedSupercriticalConclusion
        lengthThreeSurvivorKernelData exampleSupercriticalAdversary
        exampleSupercriticalSchedule
        (initialStatefulAdversaryConfig
          lengthThreeSurvivorKernelData exampleSupercriticalAdversary)
        cert
        lengthThreeSurvivorNode_hasConsistencyViolationWitness
        lengthThreeSurvivorGraph_effectiveSurface
        lengthThreeSurvivorGraph_completeTail := by
  have heq :
      DecisionSystem.Equivalent lengthThreeSurvivorGraph compiled.graph := by
    intro claims k
    rw [hgraph]
    rfl
  have hdisj :=
    statefulAdversary_via_consistencyWitnessedAggregator_yields_boundedCorrigibility_or_sacrifice
      lengthThreeSurvivorKernelData
      exampleSupercriticalAdversary
      compiled report monitoring
      lengthThreeSurvivorGraph [] [] lengthThreeSurvivorNode
      lengthThreeSurvivorNode_hasConsistencyViolationWitness
      lengthThreeSurvivorGraph_effectiveSurface
      lengthThreeSurvivorGraph_completeTail
      heq hgraph hlive
      lengthThreeSurvivor_tolerance_pos
      lengthThreeSurvivor_cv_pos
      exampleSupercriticalSchedule
      (initialStatefulAdversaryConfig
        lengthThreeSurvivorKernelData exampleSupercriticalAdversary)
      rfl
  rcases hdisj with hbounded | hsacrifice
  · exact (exampleSupercriticalAdversary_not_boundedCorrigibility hbounded).elim
  · exact hsacrifice

/-- Headline sacrifice-branch stack example. The kernel axis is inhabited by a
path-local sacrifice certificate at transition index zero, and the stateful axis
is inhabited by the concrete critical-capability consistency-sacrifice branch
from `exampleSupercriticalAdversary_yields_consistency_sacrifice_right`. -/
theorem exampleSupercriticalAdversary_sacrificeBranch_kernelGovernanceSafety
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (hgraph : compiled.graph = lengthThreeSurvivorSystem.graph)
    (hlive : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring)) :
    ∃ cert :
      MonitoredSacrificeCertificate
        lengthThreeSurvivorKernelData lengthThreeSurvivorKernelData,
    ∃ h_traj :
      KernelGovernedTrajectory lengthThreeSurvivorSystem
        lengthThreeSurvivorKernelData lengthThreeSurvivorKernelData,
      WorkedSupercriticalConclusion
        lengthThreeSurvivorKernelData exampleSupercriticalAdversary
        exampleSupercriticalSchedule
        (initialStatefulAdversaryConfig
          lengthThreeSurvivorKernelData exampleSupercriticalAdversary)
        cert
        lengthThreeSurvivorNode_hasConsistencyViolationWitness
        lengthThreeSurvivorGraph_effectiveSurface
        lengthThreeSurvivorGraph_completeTail ∧
      KernelGovernedTrajectory.HasSacrificeStepAt h_traj 0 ∧
      ReachableStateSafetyConclusion h_traj ∧
      StatefulCorrigibilityOrConsistencySacrifice
        lengthThreeSurvivorKernelData exampleSupercriticalAdversary
        exampleSupercriticalSchedule
        (initialStatefulAdversaryConfig
          lengthThreeSurvivorKernelData exampleSupercriticalAdversary)
        lengthThreeSurvivorNode_hasConsistencyViolationWitness
        lengthThreeSurvivorGraph_effectiveSurface
        lengthThreeSurvivorGraph_completeTail := by
  obtain ⟨cert, hworked⟩ :=
    exampleSupercriticalAdversary_yields_consistency_sacrifice_right
      compiled report monitoring hgraph hlive
  rcases hworked with ⟨hconsistency, hcritical⟩
  let h_traj :
      KernelGovernedTrajectory lengthThreeSurvivorSystem
        lengthThreeSurvivorKernelData lengthThreeSurvivorKernelData :=
    KernelGovernedTrajectory.singleSacrificeStep cert
  have hsacrificeAt :
      KernelGovernedTrajectory.HasSacrificeStepAt h_traj 0 := by
    exact KernelGovernedTrajectory.HasSacrificeStepAt.here cert
      (KernelGovernedTrajectory.refl lengthThreeSurvivorKernelData)
  have hreachable : ReachableStateSafetyConclusion h_traj :=
    Or.inr ⟨0, hsacrificeAt⟩
  have hstateful :
      StatefulCorrigibilityOrConsistencySacrifice
        lengthThreeSurvivorKernelData exampleSupercriticalAdversary
        exampleSupercriticalSchedule
        (initialStatefulAdversaryConfig
          lengthThreeSurvivorKernelData exampleSupercriticalAdversary)
        lengthThreeSurvivorNode_hasConsistencyViolationWitness
        lengthThreeSurvivorGraph_effectiveSurface
        lengthThreeSurvivorGraph_completeTail :=
    Or.inr ⟨cert, hconsistency, hcritical⟩
  exact ⟨cert, h_traj, ⟨hconsistency, hcritical⟩, hsacrificeAt, hreachable,
    hstateful⟩

end Safety

end Legitimacy
