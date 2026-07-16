/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.StatefulExamples.ConcreteAdversaries
import Legitimacy.Safety.KernelSafety.StatefulExamples.ExtractorArtifacts
import Legitimacy.Safety.KernelSafety.StatefulExamples.ConsistencySacrifice

/-!
# Legitimacy.Safety.KernelSafety.StatefulExamples.ScheduleExtraction

Worked safety-stack and multi-step schedule-extraction examples.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-- Worked concrete instantiation of the stack theorem over the existing
example governance datum and no-op stateful adversary. The stateful sidecar
uses the strict length-sensitive consistency-violation witness rather than the
peer-relative aggregator predicate, and the extractor relation is a non-rfl
semantic transfer from the widened-signal extracted datum to the live datum. -/
theorem exampleGovernanceKernelData_safety_stack_fires
    (autogenRustBytes autogenLeanBytes : FixtureBytes)
    (hautogenBytes : autogenRustBytes = autogenLeanBytes)
    (schedule : List (StatefulScheduleStep exampleGovernanceKernelData)) :
    ExtractedKernelReachableSafety
      exampleGovernanceTrajectory ∧
    StatefulCorrigibilityOrConsistencySacrifice
      exampleGovernanceKernelData exampleNoOpStatefulAdversary schedule
      (initialStatefulAdversaryConfig
        exampleGovernanceKernelData exampleNoOpStatefulAdversary)
      lengthThreeSurvivorNode_hasConsistencyViolationWitness
      lengthThreeSurvivorGraph_effectiveSurface
      lengthThreeSurvivorGraph_completeTail ∧
    ExtractorParityFixtureSatisfied autogenExtractorInput
      [autogenEmpiricalParityFixture autogenRustBytes autogenLeanBytes] := by
  have hwellFormed : autogenExtractorInput.WellFormed := by
    simp [ExtractorInput.WellFormed, autogenExtractorInput]
  have hparity :
      EmpiricalParityCertificate
        [autogenExtractorInput]
        [autogenEmpiricalParityFixture autogenRustBytes autogenLeanBytes] :=
    autogen_leaderboard_fixture_empirical_parity_certificate
      autogenRustBytes autogenLeanBytes hautogenBytes
  have hcanonical :
      autogenExtractorInput ∈ [autogenExtractorInput] := by
    simp
  exact
    extractedKernelData_satisfies_boundedSafetyStack
      (extract := exampleGovernanceSourceSensitiveKernelExtractor)
      exampleGovernanceSourceSensitiveKernelExtractor_contract
      autogenExtractorInput hwellFormed
      hparity hcanonical
      exampleGovernanceKernelData
      (exampleGovernanceSourceSensitiveExtracted_to_liveSemantic
        autogenExtractorInput)
      exampleGovernanceTrajectory
      exampleNoOpStatefulAdversary
      lengthThreeSurvivorNode_hasConsistencyViolationWitness
      lengthThreeSurvivorGraph_effectiveSurface
      lengthThreeSurvivorGraph_completeTail
      schedule
      (initialStatefulAdversaryConfig
        exampleGovernanceKernelData exampleNoOpStatefulAdversary)
      (exampleNoOpStatefulAdversary_preserves_stable_state_decisions schedule)

/-- The concrete governance-graph trajectory satisfies reachable-state safety
by the general theorem. This trajectory has only invariant-preserving steps,
so the conclusion is witnessed by the preserved semantic kernel invariant. -/
example :
    ReachableStateSafetyConclusion
      exampleGovernanceTrajectory :=
  reachable_state_safety
    exampleGovernanceKernelData
    exampleGovernanceKernelData
    exampleGovernanceTrajectory
    exampleGovernanceSemanticKernel

/-! ## Multi-step worked schedule-extraction examples

The `peerSurfaceWorkedExample_noUndeclaredDeployment_and_reachableSacrifice`
theorem above exercises a single-step `KernelGovernedTrajectory.sacrifice_step`
trajectory; it does not exercise the schedule-extraction contract over a
multi-step schedule. The two theorems here close the multi-step direction by
producing an inhabited `ScheduleKernelExtraction` over a non-trivial
`StatefulScheduleStep` list and replaying it as a `KernelGovernedTrajectory`.

The first theorem uses `ScheduleKernelExtraction.allInvariantRefl` to derive
the contract over a three-step schedule with no external sacrifice input. The
trajectory re-presentation theorem lifts an existing action-driven
`KernelGovernedTrajectory` through a length-matched schedule and exposes a
non-constant kernel-data axis. The peer-surface theorems use the protocol live
path to derive sacrifice certificates instead of taking them as hypotheses.
The final theorem keeps the manual heterogeneous constructor chain that
exposes the raw per-step shape. -/

/-- Minimal stateful adversary over the threshold-action datum. The worked
trajectory example below only needs an initial configuration and a one-step
kernel schedule; the adversary side is deliberately inert. -/
noncomputable def exampleThresholdNoOpStatefulAdversary :
    StatefulAdversaryLayer exampleThresholdKernelData where
  Memory := Unit
  initialMemory := ()
  Proposal := Unit
  propose := fun _ _ => ()
  applyProposal := fun _ S => S
  capability := fun _ => 0
  observedClaims := fun _ => []
  observedClaimant := fun _ => 0
  update := fun _ _ _ => ()
  stateRealization := fun _ => exampleThresholdKernelData.spectralGraph
  stateCoherent := rfl
  proposalRealization := fun _ G => G
  proposalRealizationCoherent := by
    intro _ _
    rfl
  capabilityPerturbationBound := by
    intro _ _
    simp [spectralDistance_self, perturbationBound]

/-- Re-presentation worked example with genuine kernel-data evolution. The
schedule has the concrete kernel action used by
`exampleThresholdActionDrivenTrajectory`; length matching lets
`fromKernelGovernedTrajectoryAndSchedule` replay that trajectory as a
`ScheduleKernelExtraction`, and the accompanying inequality proves the final
kernel datum is not the source datum. -/
theorem exampleThresholdActionDriven_scheduleExtraction_variesKernelData_worked_example :
    let schedule : List (StatefulScheduleStep exampleThresholdKernelData) :=
      [StatefulScheduleStep.kernel exampleThresholdAction.raiseThreshold]
    let cfg :=
      initialStatefulAdversaryConfig
        exampleThresholdKernelData exampleThresholdNoOpStatefulAdversary
    Nonempty
      (ScheduleKernelExtraction exampleThresholdKernelData
        exampleThresholdNoOpStatefulAdversary exampleThresholdKernelData
        schedule cfg
        (exampleThresholdTargetFromReplay
          (exampleThresholdActionSpace.applySeq
            [exampleThresholdAction.raiseThreshold]
            exampleGovernedSystem.state))) ∧
    exampleThresholdKernelData ≠
      exampleThresholdTargetFromReplay
        (exampleThresholdActionSpace.applySeq
          [exampleThresholdAction.raiseThreshold]
          exampleGovernedSystem.state) := by
  intro schedule cfg
  let traj := exampleThresholdActionDrivenTrajectory
  have h_length : schedule.length = traj.length := by
    rfl
  let ext :
      ScheduleKernelExtraction exampleThresholdKernelData
        exampleThresholdNoOpStatefulAdversary exampleThresholdKernelData
        schedule cfg
        (exampleThresholdTargetFromReplay
          (exampleThresholdActionSpace.applySeq
            [exampleThresholdAction.raiseThreshold]
            exampleGovernedSystem.state)) :=
    ScheduleKernelExtraction.fromKernelGovernedTrajectoryAndSchedule
      traj schedule cfg h_length
  exact ⟨⟨ext⟩, exampleThresholdActionDrivenStep_target_nonrefl⟩

/-- Multi-step automatic derivation over the worked governance datum. The
schedule contains one kernel action, one adversary turn, and a second kernel
action. The schedule-datum invariant is supplied by
`exampleGovernanceSemanticKernel`, so `allInvariantRefl` produces a
fully-invariant extraction without any external sacrifice input, and the
induced kernel-governed trajectory is constructively recovered through
`toKernelGovernedTrajectory`. -/
theorem exampleGovernance_multiStepScheduleExtraction_allInvariant_worked_example
    (a b : exampleGovernanceKernelData.actionSpace.Action) :
    Nonempty
      (KernelGovernedTrajectory exampleGovernedSystem
        exampleGovernanceKernelData exampleGovernanceKernelData) :=
  kernelGovernedTrajectory_from_allInvariantRefl
    exampleNoOpStatefulAdversary exampleGovernanceSemanticKernel
    [StatefulScheduleStep.kernel a, StatefulScheduleStep.adversary,
      StatefulScheduleStep.kernel b]
    (initialStatefulAdversaryConfig
      exampleGovernanceKernelData exampleNoOpStatefulAdversary)

/-- Multi-step sacrifice-only extraction over the canonical peer-relative
surface. The schedule has the concrete `[kernel a, adversary, kernel b]` shape,
but the extraction does not take a sacrifice certificate as input: each
certificate is derived from the live protocol path, the effective peer-relative
surface, and the complete tail. -/
theorem peerSurface_multiStepScheduleExtraction_forcedConsistencySacrifice_worked_example
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (hgraph : compiled.graph = peerSurfaceSystem.graph)
    (hlive : IsLiveCompiled compiled report monitoring)
    (adv : StatefulAdversaryLayer peerSurfaceKernelData)
    (a b : peerSurfaceKernelData.actionSpace.Action) :
    let schedule : List (StatefulScheduleStep peerSurfaceKernelData) :=
      [StatefulScheduleStep.kernel a, StatefulScheduleStep.adversary,
        StatefulScheduleStep.kernel b]
    let cfg :=
      initialStatefulAdversaryConfig peerSurfaceKernelData adv
    Nonempty
      (ScheduleKernelExtraction peerSurfaceKernelData adv
        peerSurfaceKernelData schedule cfg peerSurfaceKernelData) ∧
    Nonempty
      (KernelGovernedTrajectory peerSurfaceSystem
        peerSurfaceKernelData peerSurfaceKernelData) := by
  intro schedule cfg
  have heffective :
      EffectivePeerRelativeSurface compiled.graph [] [] := by
    rw [hgraph]
    exact peerGraph_effectivePeerRelativeSurface
  have hcomplete : CompletePeerRelativeTail [] :=
    peerGraph_completePeerRelativeTail
  let ext :
      ScheduleKernelExtraction peerSurfaceKernelData adv
        peerSurfaceKernelData schedule cfg peerSurfaceKernelData :=
    ScheduleKernelExtraction.fromForcedConsistencySacrifice
      peerSurfaceKernelData adv hlive heffective hcomplete hgraph schedule cfg
  exact ⟨⟨ext⟩, ⟨ext.toKernelGovernedTrajectory⟩⟩

/-- Multi-step invariant/sacrifice alternation over the same concrete
peer-surface schedule. The invariant witness supplies the reflexive invariant
steps, while the sacrifice step is still derived from the live protocol path
rather than accepted as a certificate hypothesis. -/
theorem peerSurface_multiStepScheduleExtraction_forcedAlternation_worked_example
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (hgraph : compiled.graph = peerSurfaceSystem.graph)
    (hlive : IsLiveCompiled compiled report monitoring)
    (hinv : KernelInvariant peerSurfaceKernelData)
    (adv : StatefulAdversaryLayer peerSurfaceKernelData)
    (a b : peerSurfaceKernelData.actionSpace.Action) :
    let schedule : List (StatefulScheduleStep peerSurfaceKernelData) :=
      [StatefulScheduleStep.kernel a, StatefulScheduleStep.adversary,
        StatefulScheduleStep.kernel b]
    let cfg :=
      initialStatefulAdversaryConfig peerSurfaceKernelData adv
    Nonempty
      (ScheduleKernelExtraction peerSurfaceKernelData adv
        peerSurfaceKernelData schedule cfg peerSurfaceKernelData) ∧
    Nonempty
      (KernelGovernedTrajectory peerSurfaceSystem
        peerSurfaceKernelData peerSurfaceKernelData) := by
  intro schedule cfg
  have heffective :
      EffectivePeerRelativeSurface compiled.graph [] [] := by
    rw [hgraph]
    exact peerGraph_effectivePeerRelativeSurface
  have hcomplete : CompletePeerRelativeTail [] :=
    peerGraph_completePeerRelativeTail
  let ext :
      ScheduleKernelExtraction peerSurfaceKernelData adv
        peerSurfaceKernelData schedule cfg peerSurfaceKernelData :=
    ScheduleKernelExtraction.fromForcedConsistencyAlternation
      peerSurfaceKernelData adv hinv hlive heffective hcomplete hgraph
      schedule cfg
  exact ⟨⟨ext⟩, ⟨ext.toKernelGovernedTrajectory⟩⟩

/-- Multi-step mixed-verdict extraction over the worked governance datum. The
schedule contains one kernel action, one adversary turn, and a second kernel
action; the per-step verdict chain is `invariant ∘ sacrifice ∘ invariant`
with the sacrifice certificate supplied as a hypothesis. The contract is
built directly by chaining `ScheduleKernelExtraction` constructors, exposing
the heterogeneous per-step verdict shape that the bijection
`schedule_extraction_iff_per_step_witness` characterizes. The induced
kernel-governed trajectory exposes a sacrifice step at index 1 of the
trajectory by `KernelGovernedTrajectory.HasSacrificeStepAt`. -/
theorem exampleGovernance_multiStepScheduleExtraction_mixed_worked_example
    (cert :
      MonitoredSacrificeCertificate
        exampleGovernanceKernelData exampleGovernanceKernelData)
    (a b : exampleGovernanceKernelData.actionSpace.Action) :
    let schedule : List (StatefulScheduleStep exampleGovernanceKernelData) :=
      [StatefulScheduleStep.kernel a, StatefulScheduleStep.adversary,
        StatefulScheduleStep.kernel b]
    let cfg_initial :=
      initialStatefulAdversaryConfig
        exampleGovernanceKernelData exampleNoOpStatefulAdversary
    Nonempty
      (ScheduleKernelExtraction exampleGovernanceKernelData
        exampleNoOpStatefulAdversary exampleGovernanceKernelData schedule cfg_initial
        exampleGovernanceKernelData) ∧
    Nonempty
      (KernelGovernedTrajectory exampleGovernedSystem
        exampleGovernanceKernelData exampleGovernanceKernelData) := by
  intro schedule cfg_initial
  let cfg_after_kernel_a :=
    applyStatefulStep exampleGovernanceKernelData exampleNoOpStatefulAdversary
      (StatefulScheduleStep.kernel a) cfg_initial
  let cfg_after_adversary :=
    applyStatefulStep exampleGovernanceKernelData exampleNoOpStatefulAdversary
      StatefulScheduleStep.adversary cfg_after_kernel_a
  let cfg_after_kernel_b :=
    applyStatefulStep exampleGovernanceKernelData exampleNoOpStatefulAdversary
      (StatefulScheduleStep.kernel b) cfg_after_adversary
  let ext :
      ScheduleKernelExtraction exampleGovernanceKernelData
        exampleNoOpStatefulAdversary exampleGovernanceKernelData schedule cfg_initial
        exampleGovernanceKernelData :=
    ScheduleKernelExtraction.invariant_step
      (KernelStep.refl exampleGovernanceKernelData)
      exampleGovernanceSemanticKernel
      (ScheduleKernelExtraction.sacrifice_step cert
        (ScheduleKernelExtraction.invariant_step
          (KernelStep.refl exampleGovernanceKernelData)
          exampleGovernanceSemanticKernel
          (ScheduleKernelExtraction.done exampleGovernanceKernelData cfg_after_kernel_b)))
  exact ⟨⟨ext⟩, ⟨ext.toKernelGovernedTrajectory⟩⟩

end Safety

end Legitimacy
