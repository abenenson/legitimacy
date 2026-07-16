/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.StatefulExamples.Conclusions

/-!
# Legitimacy.Safety.KernelSafety.StatefulExamples.ConcreteAdversaries

Concrete bounded stateful adversary inhabitants over the worked governance datum.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-! ## Concrete bounded stateful adversary inhabitant -/

private def exampleZeroSpectralGraph :
    GovGraph ℚ exampleGovernedSystem.graph.weightedSize where
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

private lemma exampleGovernance_criticalCapability_normalized :
    kernelDataCriticalCapability exampleGovernanceKernelData =
      C_star uniK5 sig5 (1 / 10) := by
  rfl

private lemma exampleGovernance_criticalCapability :
    kernelDataCriticalCapability exampleGovernanceKernelData = 2 / 15 := by
  rw [exampleGovernance_criticalCapability_normalized]
  rw [C_star, fiveNode_cv_values.1]
  norm_num

private lemma exampleGovernance_tolerance_pos :
    0 < exampleGovernanceKernelData.toleranceParameter := by
  norm_num [exampleGovernanceKernelData]

private lemma exampleGovernance_cv_normalized :
    exampleGovernanceKernelData.spectralGraph.cv
      exampleGovernanceKernelData.spectralSignal =
    uniK5.cv sig5 := by
  rfl

private lemma exampleGovernance_cv_pos :
    0 < exampleGovernanceKernelData.spectralGraph.cv
      exampleGovernanceKernelData.spectralSignal := by
  rw [exampleGovernance_cv_normalized]
  rw [fiveNode_cv_values.1]
  norm_num

private lemma exampleGovernanceZero_spectralDistance_normalized :
    spectralDistance exampleGovernanceKernelData.spectralGraph
        exampleZeroSpectralGraph =
      spectralDistance uniK5 exampleZeroSpectralGraph := by
  rfl

private lemma exampleZeroSpectralGraph_not_subcritical :
    ¬ spectralDistance exampleGovernanceKernelData.spectralGraph
        exampleZeroSpectralGraph <
      kernelDataCriticalCapability exampleGovernanceKernelData := by
  rw [exampleGovernance_criticalCapability]
  rw [exampleGovernanceZero_spectralDistance_normalized]
  -- Finite rational matrix evaluation over the concrete five-node fixture.
  -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
  native_decide

private def exampleSubcriticalSpectralGraph : GovGraph ℚ 5 where
  weights := !![
    0, 201 / 200, 1, 1, 1;
    201 / 200, 0, 1, 1, 1;
    1, 1, 0, 1, 1;
    1, 1, 1, 0, 1;
    1, 1, 1, 1, 0
  ]
  -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
  weight_symm := by native_decide
  weight_nonneg := by native_decide
  weight_self_zero := by native_decide

private lemma exampleSubcriticalSpectralDistance :
    spectralDistance exampleGovernanceKernelData.spectralGraph
        exampleSubcriticalSpectralGraph =
      1 / 100 := by
  change spectralDistance uniK5 exampleSubcriticalSpectralGraph = 1 / 100
  native_decide

private lemma exampleSubcriticalSpectralDistance_pos :
    0 < spectralDistance exampleGovernanceKernelData.spectralGraph
        exampleSubcriticalSpectralGraph := by
  rw [exampleSubcriticalSpectralDistance]
  norm_num

private lemma exampleSubcriticalSpectralGraph_subcritical :
    spectralDistance exampleGovernanceKernelData.spectralGraph
        exampleSubcriticalSpectralGraph <
      kernelDataCriticalCapability exampleGovernanceKernelData := by
  rw [exampleSubcriticalSpectralDistance, exampleGovernance_criticalCapability]
  norm_num

private def exampleSubcriticalMutatedState : GovernanceState :=
  { exampleGovernedSystem.state with sandboxBoundary := 2 }

private lemma exampleSubcriticalMutatedState_ne :
    exampleSubcriticalMutatedState ≠ exampleGovernedSystem.state := by
  intro h
  have hboundary := congrArg GovernanceState.sandboxBoundary h
  norm_num [exampleSubcriticalMutatedState, exampleGovernedSystem,
    permitState] at hboundary

private lemma exampleSubcriticalMutatedState_decisions_agree :
    StateClaimDecisionsAgree
      exampleGovernedSystem.state exampleSubcriticalMutatedState := by
  intro claims k
  rfl

private noncomputable def exampleSubcriticalStatefulRealization
    (S : GovernanceState) :
    GovGraph ℚ exampleGovernedSystem.graph.weightedSize := by
  classical
  exact if S = exampleGovernedSystem.state then
    exampleGovernanceKernelData.spectralGraph
  else
    exampleSubcriticalSpectralGraph

private lemma exampleSubcriticalStatefulRealization_mutated :
    exampleSubcriticalStatefulRealization exampleSubcriticalMutatedState =
      exampleSubcriticalSpectralGraph := by
  simp [exampleSubcriticalStatefulRealization,
    exampleSubcriticalMutatedState_ne]

/-- Stateful adversary whose realized proposal mutates supervisory metadata and
produces a positive-but-subcritical spectral perturbation. Unlike the no-op
fixtures, the first adversary turn changes the carried governance state. -/
noncomputable def exampleSubcriticalMutatingStatefulAdversary :
    StatefulAdversaryLayer exampleGovernanceKernelData where
  Memory := Unit
  initialMemory := ()
  Proposal := Unit
  propose := fun _ _ => ()
  applyProposal := fun _ _ => exampleSubcriticalMutatedState
  capability := fun _ => 1 / 100
  observedClaims := fun _ => [permitClaim]
  observedClaimant := fun _ => permitClaim.id
  update := fun _ _ _ => ()
  stateRealization := exampleSubcriticalStatefulRealization
  stateCoherent := by
    simp [exampleSubcriticalStatefulRealization]
  proposalRealization := fun _ _ => exampleSubcriticalSpectralGraph
  proposalRealizationCoherent := by
    intro _ _
    simp [exampleSubcriticalStatefulRealization_mutated]
  capabilityPerturbationBound := by
    intro _ S
    classical
    by_cases hS : S = exampleGovernedSystem.state
    · subst hS
      simp [exampleSubcriticalStatefulRealization,
        exampleSubcriticalMutatedState_ne, perturbationBound,
        exampleSubcriticalSpectralDistance]
    · simp [exampleSubcriticalStatefulRealization, hS,
        exampleSubcriticalMutatedState_ne, spectralDistance_self,
        perturbationBound]

def exampleSubcriticalMutatingSchedule :
    List (StatefulScheduleStep exampleGovernanceKernelData) :=
  [StatefulScheduleStep.adversary]

lemma exampleSubcriticalMutatingStatefulAdversary_mutates_initial_state :
    exampleSubcriticalMutatingStatefulAdversary.applyProposal ()
        exampleGovernedSystem.state ≠
      exampleGovernedSystem.state := by
  simpa [exampleSubcriticalMutatingStatefulAdversary] using
    exampleSubcriticalMutatedState_ne

lemma exampleSubcriticalMutatingStatefulTrajectoryPerturbationBound :
    statefulTrajectoryPerturbationBound
        exampleGovernanceKernelData
        exampleSubcriticalMutatingStatefulAdversary
        exampleSubcriticalMutatingSchedule
        (initialStatefulAdversaryConfig
          exampleGovernanceKernelData
          exampleSubcriticalMutatingStatefulAdversary) =
      1 / 100 := by
  simp [exampleSubcriticalMutatingSchedule,
    statefulTrajectoryPerturbationBound, statefulRealizedProposals,
    initialStatefulAdversaryConfig,
    exampleSubcriticalMutatingStatefulAdversary, perturbationBound]

lemma exampleSubcriticalMutatingStatefulAdversary_budget_positive :
    0 <
      statefulTrajectoryPerturbationBound
        exampleGovernanceKernelData
        exampleSubcriticalMutatingStatefulAdversary
        exampleSubcriticalMutatingSchedule
        (initialStatefulAdversaryConfig
          exampleGovernanceKernelData
          exampleSubcriticalMutatingStatefulAdversary) := by
  rw [exampleSubcriticalMutatingStatefulTrajectoryPerturbationBound]
  norm_num

lemma exampleSubcriticalMutatingStatefulAdversary_budget_subcritical :
    statefulTrajectoryPerturbationBound
        exampleGovernanceKernelData
        exampleSubcriticalMutatingStatefulAdversary
        exampleSubcriticalMutatingSchedule
        (initialStatefulAdversaryConfig
          exampleGovernanceKernelData
          exampleSubcriticalMutatingStatefulAdversary) <
      kernelDataCriticalCapability exampleGovernanceKernelData := by
  rw [exampleSubcriticalMutatingStatefulTrajectoryPerturbationBound,
    exampleGovernance_criticalCapability]
  norm_num

lemma exampleSubcriticalMutatingStatefulAdversary_final_state :
    (applyStatefulTrajectory
        exampleGovernanceKernelData
        exampleSubcriticalMutatingStatefulAdversary
        exampleSubcriticalMutatingSchedule
        (initialStatefulAdversaryConfig
          exampleGovernanceKernelData
          exampleSubcriticalMutatingStatefulAdversary)).state =
      exampleSubcriticalMutatedState := by
  simp [exampleSubcriticalMutatingSchedule, applyStatefulTrajectory,
    applyStatefulStep, initialStatefulAdversaryConfig,
    exampleSubcriticalMutatingStatefulAdversary]

lemma exampleSubcriticalMutatingStatefulAdversary_final_distance_positive :
    0 <
      spectralDistance exampleGovernanceKernelData.spectralGraph
        (exampleSubcriticalMutatingStatefulAdversary.stateRealization
          (applyStatefulTrajectory
            exampleGovernanceKernelData
            exampleSubcriticalMutatingStatefulAdversary
            exampleSubcriticalMutatingSchedule
            (initialStatefulAdversaryConfig
              exampleGovernanceKernelData
              exampleSubcriticalMutatingStatefulAdversary)).state) := by
  rw [exampleSubcriticalMutatingStatefulAdversary_final_state]
  simpa [exampleSubcriticalMutatingStatefulAdversary,
    exampleSubcriticalStatefulRealization_mutated] using
    exampleSubcriticalSpectralDistance_pos

lemma exampleSubcriticalMutatingStatefulAdversary_preserves_stable_state_decisions :
    BoundedCorrigibilityPreservedAt
      exampleGovernanceKernelData
      exampleSubcriticalMutatingStatefulAdversary
      exampleSubcriticalMutatingSchedule
      (initialStatefulAdversaryConfig
        exampleGovernanceKernelData
        exampleSubcriticalMutatingStatefulAdversary) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      kernelDataCriticalCapability_pos exampleGovernanceKernelData
        exampleGovernance_tolerance_pos exampleGovernance_cv_pos
  · rw [exampleSubcriticalMutatingStatefulAdversary_final_state]
    exact exampleSubcriticalMutatedState_decisions_agree
  · rw [exampleSubcriticalMutatingStatefulAdversary_final_state]
    simpa [exampleSubcriticalMutatingStatefulAdversary,
      exampleSubcriticalStatefulRealization_mutated] using
      exampleSubcriticalSpectralGraph_subcritical

/-- Non-degenerate bounded-branch worked example: the adversary mutates the
supervisory state and realizes a positive spectral perturbation, but the
realized budget remains strictly below the concrete critical capability. -/
theorem exampleSubcriticalMutatingStatefulAdversary_yields_boundedCorrigibility_or_sacrifice_left
    {P : Type} [BinaryDecisionPipeline P]
    {G pref tail : P} {node : BinaryDecisionPipeline.NodeOf P}
    (hagg : BinaryDecisionPipeline.IsPeerRelativeAggregator node)
    (heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : BinaryDecisionPipeline.CompleteTailForNode node tail) :
    WorkedSubcriticalConclusion
      exampleGovernanceKernelData
      exampleSubcriticalMutatingStatefulAdversary
      exampleSubcriticalMutatingSchedule
      (initialStatefulAdversaryConfig
        exampleGovernanceKernelData
        exampleSubcriticalMutatingStatefulAdversary)
      hagg heffective hcomplete :=
  Or.inl
    exampleSubcriticalMutatingStatefulAdversary_preserves_stable_state_decisions

private noncomputable def exampleNoOpStatefulRealization
    (S : GovernanceState) :
    GovGraph ℚ exampleGovernedSystem.graph.weightedSize := by
  classical
  exact if S = exampleGovernedSystem.state then
    exampleGovernanceKernelData.spectralGraph
  else
    exampleZeroSpectralGraph

/-- Concrete no-op stateful adversary over the worked governance example. It has
real memory, proposals, feedback update, realized proposal budget, and
state-realization data, but its single proposal leaves the supervisory state
unchanged. -/
noncomputable def exampleNoOpStatefulAdversary :
    StatefulAdversaryLayer exampleGovernanceKernelData where
  Memory := Unit
  initialMemory := ()
  Proposal := Unit
  propose := fun _ _ => ()
  applyProposal := fun _ S => S
  capability := fun _ => 0
  observedClaims := fun _ => []
  observedClaimant := fun _ => 0
  update := fun _ _ _ => ()
  stateRealization := exampleNoOpStatefulRealization
  stateCoherent := by
    simp [exampleNoOpStatefulRealization, exampleGovernedSystem]
  proposalRealization := fun _ G => G
  proposalRealizationCoherent := by
    intro _ _
    rfl
  capabilityPerturbationBound := by
    intro _ S
    simp [spectralDistance_self, perturbationBound]

noncomputable instance exampleNoOpStatefulAdversary_kernelPerturbationFree :
    IsKernelPerturbationFreeAdversary
      exampleGovernanceKernelData exampleNoOpStatefulAdversary where
  kernel_action_zero_distance := by
    intro a S
    cases a
    simp [exampleNoOpStatefulAdversary, exampleNoOpStatefulRealization,
      exampleGovernanceKernelData, idActionSpace, spectralDistance_self]

noncomputable instance exampleNoOpStatefulAdversary_locallyStable :
    IsLocallyStableStatefulAdversary
      exampleGovernanceKernelData exampleNoOpStatefulAdversary
      exampleGovernedSystem.state
      (kernelDataCriticalCapability exampleGovernanceKernelData) where
  stable_within_realization := by
    intro S hdist
    classical
    by_cases hS : S = exampleGovernedSystem.state
    · subst hS
      intro claims k
      rfl
    · exfalso
      apply exampleZeroSpectralGraph_not_subcritical
      simpa [exampleNoOpStatefulAdversary, exampleNoOpStatefulRealization, hS]
        using hdist

private lemma exampleNoOpStatefulTrajectoryPerturbationBound_from :
    ∀ (schedule : List (StatefulScheduleStep exampleGovernanceKernelData))
      (cfg : StatefulAdversaryConfig exampleNoOpStatefulAdversary),
      statefulTrajectoryPerturbationBound
          exampleGovernanceKernelData exampleNoOpStatefulAdversary schedule cfg =
        0
  | [], _ => by
      simp [statefulTrajectoryPerturbationBound, statefulRealizedProposals]
  | step :: rest, cfg => by
      cases step with
      | kernel a =>
          simpa [statefulTrajectoryPerturbationBound, statefulRealizedProposals,
            applyStatefulStep, exampleNoOpStatefulAdversary]
            using exampleNoOpStatefulTrajectoryPerturbationBound_from rest
              (applyStatefulStep exampleGovernanceKernelData
                exampleNoOpStatefulAdversary
                (StatefulScheduleStep.kernel a) cfg)
      | adversary =>
          simp [statefulTrajectoryPerturbationBound, statefulRealizedProposals,
            applyStatefulStep, exampleNoOpStatefulAdversary, perturbationBound]

private lemma exampleNoOpStatefulTrajectoryPerturbationBound
    (schedule : List (StatefulScheduleStep exampleGovernanceKernelData)) :
    statefulTrajectoryPerturbationBound
        exampleGovernanceKernelData exampleNoOpStatefulAdversary schedule
        (initialStatefulAdversaryConfig
          exampleGovernanceKernelData exampleNoOpStatefulAdversary) =
      0 :=
  exampleNoOpStatefulTrajectoryPerturbationBound_from schedule
    (initialStatefulAdversaryConfig
      exampleGovernanceKernelData exampleNoOpStatefulAdversary)

/-- The existing bounded stateful theorem fires against a concrete external
adversary inhabitant over the worked governance example. -/
theorem exampleNoOpStatefulAdversary_preserves_stable_state_decisions
    (schedule : List (StatefulScheduleStep exampleGovernanceKernelData)) :
    0 < kernelDataCriticalCapability exampleGovernanceKernelData ∧
    StateClaimDecisionsAgree exampleGovernedSystem.state
      (applyStatefulTrajectory
        exampleGovernanceKernelData exampleNoOpStatefulAdversary schedule
        (initialStatefulAdversaryConfig
          exampleGovernanceKernelData exampleNoOpStatefulAdversary)).state ∧
    spectralDistance exampleGovernanceKernelData.spectralGraph
      (exampleNoOpStatefulAdversary.stateRealization
        (applyStatefulTrajectory
          exampleGovernanceKernelData exampleNoOpStatefulAdversary schedule
          (initialStatefulAdversaryConfig
            exampleGovernanceKernelData exampleNoOpStatefulAdversary)).state) <
      kernelDataCriticalCapability exampleGovernanceKernelData := by
  refine
    stateful_budgeted_subcritical_trajectory_preserves_stable_state_decisions
      exampleGovernanceKernelData
      exampleNoOpStatefulAdversary
      exampleGovernance_tolerance_pos
      exampleGovernance_cv_pos
      schedule ?_
  have hcrit :
      0 < kernelDataCriticalCapability exampleGovernanceKernelData :=
    kernelDataCriticalCapability_pos exampleGovernanceKernelData
      exampleGovernance_tolerance_pos exampleGovernance_cv_pos
  simpa [exampleNoOpStatefulTrajectoryPerturbationBound schedule] using hcrit

/-- Worked concrete no-op case for the strengthened disjunction: the realized
trajectory is subcritical, so the disjunction is inhabited by the bounded
corrigibility branch. -/
theorem exampleNoOpStatefulAdversary_yields_boundedCorrigibility_or_sacrifice_left
    {P : Type} [BinaryDecisionPipeline P]
    {G pref tail : P} {node : BinaryDecisionPipeline.NodeOf P}
    (hagg : BinaryDecisionPipeline.IsPeerRelativeAggregator node)
    (heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : BinaryDecisionPipeline.CompleteTailForNode node tail)
    (schedule : List (StatefulScheduleStep exampleGovernanceKernelData)) :
    WorkedSubcriticalConclusion
      exampleGovernanceKernelData exampleNoOpStatefulAdversary schedule
      (initialStatefulAdversaryConfig
        exampleGovernanceKernelData exampleNoOpStatefulAdversary)
      hagg heffective hcomplete :=
  Or.inl
    (exampleNoOpStatefulAdversary_preserves_stable_state_decisions schedule)

/-- A structurally nontrivial stateful adversary: its first adversary turn
submits the witness claim, observes the kernel response, records that feedback
by switching memory to halted mode, and then emits empty halted proposals. The
proposal does not mutate the supervisory state, so its spectral perturbation
budget is still zero. -/
noncomputable def exampleClaimObservingStatefulAdversary :
    StatefulAdversaryLayer exampleGovernanceKernelData where
  Memory := Bool
  initialMemory := false
  Proposal := Bool
  propose := fun halted _ => !halted
  applyProposal := fun _ S => S
  capability := fun _ => 0
  observedClaims := fun active => if active then [permitClaim] else []
  observedClaimant := fun _ => permitClaim.id
  update := fun _ _ _ => true
  stateRealization := exampleNoOpStatefulRealization
  stateCoherent := by
    simp [exampleNoOpStatefulRealization, exampleGovernedSystem]
  proposalRealization := fun _ G => G
  proposalRealizationCoherent := by
    intro _ _
    rfl
  capabilityPerturbationBound := by
    intro _ S
    simp [spectralDistance_self, perturbationBound]

/-- The claim-observing adversary really emits a nonempty claim proposal on
its first adversary turn from the initial configuration. -/
lemma exampleClaimObservingStatefulAdversary_firstProposal :
    statefulRealizedProposals
        exampleGovernanceKernelData exampleClaimObservingStatefulAdversary
        [StatefulScheduleStep.adversary]
        (initialStatefulAdversaryConfig
          exampleGovernanceKernelData exampleClaimObservingStatefulAdversary) =
      [true] := by
  rfl

/-- The first concrete proposal observes the witness claim. -/
lemma exampleClaimObservingStatefulAdversary_observedClaims :
    exampleClaimObservingStatefulAdversary.observedClaims true =
      [permitClaim] := by
  rfl

noncomputable instance
    exampleClaimObservingStatefulAdversary_kernelPerturbationFree :
    IsKernelPerturbationFreeAdversary
      exampleGovernanceKernelData exampleClaimObservingStatefulAdversary where
  kernel_action_zero_distance := by
    intro a S
    cases a
    simp [exampleClaimObservingStatefulAdversary,
      exampleNoOpStatefulRealization, exampleGovernanceKernelData,
      idActionSpace, spectralDistance_self]

noncomputable instance exampleClaimObservingStatefulAdversary_locallyStable :
    IsLocallyStableStatefulAdversary
      exampleGovernanceKernelData exampleClaimObservingStatefulAdversary
      exampleGovernedSystem.state
      (kernelDataCriticalCapability exampleGovernanceKernelData) where
  stable_within_realization := by
    intro S hdist
    classical
    by_cases hS : S = exampleGovernedSystem.state
    · subst hS
      intro claims k
      rfl
    · exfalso
      apply exampleZeroSpectralGraph_not_subcritical
      simpa [exampleClaimObservingStatefulAdversary,
        exampleNoOpStatefulRealization, hS] using hdist

private lemma exampleClaimObservingStatefulTrajectoryPerturbationBound_from :
    ∀ (schedule : List (StatefulScheduleStep exampleGovernanceKernelData))
      (cfg : StatefulAdversaryConfig exampleClaimObservingStatefulAdversary),
      statefulTrajectoryPerturbationBound
          exampleGovernanceKernelData exampleClaimObservingStatefulAdversary
          schedule cfg = 0
  | [], _ => by
      simp [statefulTrajectoryPerturbationBound, statefulRealizedProposals]
  | step :: rest, cfg => by
      cases step with
      | kernel a =>
          simpa [statefulTrajectoryPerturbationBound, statefulRealizedProposals,
            applyStatefulStep, exampleClaimObservingStatefulAdversary]
            using exampleClaimObservingStatefulTrajectoryPerturbationBound_from
              rest
              (applyStatefulStep exampleGovernanceKernelData
                exampleClaimObservingStatefulAdversary
                (StatefulScheduleStep.kernel a) cfg)
      | adversary =>
          simp [statefulTrajectoryPerturbationBound, statefulRealizedProposals,
            applyStatefulStep, exampleClaimObservingStatefulAdversary,
            perturbationBound]

private lemma exampleClaimObservingStatefulTrajectoryPerturbationBound
    (schedule : List (StatefulScheduleStep exampleGovernanceKernelData)) :
    statefulTrajectoryPerturbationBound
        exampleGovernanceKernelData exampleClaimObservingStatefulAdversary
        schedule
        (initialStatefulAdversaryConfig
          exampleGovernanceKernelData exampleClaimObservingStatefulAdversary) =
      0 :=
  exampleClaimObservingStatefulTrajectoryPerturbationBound_from schedule
    (initialStatefulAdversaryConfig
      exampleGovernanceKernelData exampleClaimObservingStatefulAdversary)

/-- The unbundled stateful preservation theorem fires for the structurally
nontrivial claim-observing adversary via its concrete typeclass instances. -/
theorem exampleClaimObservingStatefulAdversary_preserves_stable_state_decisions
    (schedule : List (StatefulScheduleStep exampleGovernanceKernelData)) :
    0 < kernelDataCriticalCapability exampleGovernanceKernelData ∧
    StateClaimDecisionsAgree exampleGovernedSystem.state
      (applyStatefulTrajectory
        exampleGovernanceKernelData exampleClaimObservingStatefulAdversary
        schedule
        (initialStatefulAdversaryConfig
          exampleGovernanceKernelData
          exampleClaimObservingStatefulAdversary)).state ∧
    spectralDistance exampleGovernanceKernelData.spectralGraph
      (exampleClaimObservingStatefulAdversary.stateRealization
        (applyStatefulTrajectory
          exampleGovernanceKernelData exampleClaimObservingStatefulAdversary
          schedule
          (initialStatefulAdversaryConfig
            exampleGovernanceKernelData
            exampleClaimObservingStatefulAdversary)).state) <
      kernelDataCriticalCapability exampleGovernanceKernelData := by
  refine
    stateful_budgeted_subcritical_trajectory_preserves_stable_state_decisions
      exampleGovernanceKernelData
      exampleClaimObservingStatefulAdversary
      exampleGovernance_tolerance_pos
      exampleGovernance_cv_pos
      schedule ?_
  have hcrit :
      0 < kernelDataCriticalCapability exampleGovernanceKernelData :=
    kernelDataCriticalCapability_pos exampleGovernanceKernelData
      exampleGovernance_tolerance_pos exampleGovernance_cv_pos
  simpa [exampleClaimObservingStatefulTrajectoryPerturbationBound schedule]
    using hcrit

end Safety

end Legitimacy
