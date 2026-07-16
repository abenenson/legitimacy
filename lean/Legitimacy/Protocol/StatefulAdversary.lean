/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.ObservationalBridge

/-!
# Legitimacy.Protocol.StatefulAdversary

Feedback-coupled adversary substrate for the observational bridge.
-/

set_option autoImplicit false

namespace Legitimacy

/-! ### Stateful adversary substrate -/

/-- A stateful adversary carries private memory, chooses its next proposal from
that memory and the current supervisory state, observes the kernel decision on
the realized proposal, and updates its memory before the next adversary turn. -/
structure StatefulAdversaryLayer {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) where
  Memory : Type
  initialMemory : Memory
  Proposal : Type
  propose : Memory → GovernanceState → Proposal
  applyProposal : Proposal → GovernanceState → GovernanceState
  capability : Proposal → ℚ
  observedClaims : Proposal → List ClaimQ
  observedClaimant : Proposal → ClaimantId
  update : Memory → Proposal → GovernanceOutcome → Memory
  stateRealization : GovernanceState → GovGraph ℚ sys.graph.weightedSize
  stateCoherent : stateRealization sys.state = D.spectralGraph
  proposalRealization :
    Proposal → GovGraph ℚ sys.graph.weightedSize →
      GovGraph ℚ sys.graph.weightedSize
  proposalRealizationCoherent :
    ∀ (p : Proposal) (S : GovernanceState),
      stateRealization (applyProposal p S) =
        proposalRealization p (stateRealization S)
  capabilityPerturbationBound :
    ∀ (p : Proposal) (S : GovernanceState),
      spectralDistance (stateRealization S)
        (stateRealization (applyProposal p S)) ≤ perturbationBound (capability p)

/-- Runtime configuration for a stateful adversary interacting with the shared
supervisory state. -/
structure StatefulAdversaryConfig
    {n : Nat} {sys : GovernedSystem n} {D : LegitimacyKernelData sys}
    (adv : StatefulAdversaryLayer D) where
  memory : adv.Memory
  state : GovernanceState

/-- The response observed by a stateful adversary after one of its own
proposals has been realized. -/
def statefulAdversaryResponse
    {n : Nat} {sys : GovernedSystem n} {D : LegitimacyKernelData sys}
    (adv : StatefulAdversaryLayer D) (p : adv.Proposal)
    (S : GovernanceState) : GovernanceOutcome :=
  (adv.applyProposal p S).decide (adv.observedClaims p) (adv.observedClaimant p)

/-- A schedule specifies when the kernel acts and when the stateful adversary
gets a feedback-coupled proposal turn. The proposal itself is chosen at run
time from the adversary memory and the current state. -/
inductive StatefulScheduleStep
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) where
  | kernel : D.actionSpace.Action → StatefulScheduleStep D
  | adversary : StatefulScheduleStep D

/-- Initial stateful adversary configuration over the governed system's
adversary-free supervisory state. -/
def initialStatefulAdversaryConfig
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D) :
    StatefulAdversaryConfig adv where
  memory := adv.initialMemory
  state := sys.state

/-- Execute one scheduled kernel or adversary step. Adversary steps choose a
proposal from the current memory, observe the post-proposal kernel decision,
and carry the updated memory into the next step. -/
def applyStatefulStep
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D) :
    StatefulScheduleStep D → StatefulAdversaryConfig adv →
      StatefulAdversaryConfig adv
  | StatefulScheduleStep.kernel a, cfg =>
      { memory := cfg.memory, state := D.actionSpace.apply a cfg.state }
  | StatefulScheduleStep.adversary, cfg =>
      let p := adv.propose cfg.memory cfg.state
      let S' := adv.applyProposal p cfg.state
      let response := statefulAdversaryResponse adv p cfg.state
      { memory := adv.update cfg.memory p response, state := S' }

/-- Execute a full feedback-coupled stateful adversary schedule. -/
def applyStatefulTrajectory
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D) :
    List (StatefulScheduleStep D) → StatefulAdversaryConfig adv →
      StatefulAdversaryConfig adv
  | [], cfg => cfg
  | step :: rest, cfg =>
      applyStatefulTrajectory D adv rest (applyStatefulStep D adv step cfg)

/-- Proposals actually generated along a stateful run. This is intentionally a
realized trace, not an input list: later proposals may depend on all earlier
observed decisions through the adversary memory. -/
def statefulRealizedProposals
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D) :
    List (StatefulScheduleStep D) → StatefulAdversaryConfig adv →
      List adv.Proposal
  | [], _ => []
  | StatefulScheduleStep.kernel a :: rest, cfg =>
      statefulRealizedProposals D adv rest
        (applyStatefulStep D adv (StatefulScheduleStep.kernel a) cfg)
  | StatefulScheduleStep.adversary :: rest, cfg =>
      let p := adv.propose cfg.memory cfg.state
      p :: statefulRealizedProposals D adv rest
        (applyStatefulStep D adv StatefulScheduleStep.adversary cfg)

/-- Accumulated perturbation budget of the realized adaptive proposal trace. -/
def statefulTrajectoryPerturbationBound
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D)
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv) : ℚ :=
  ((statefulRealizedProposals D adv schedule cfg).map
    (fun p => perturbationBound (adv.capability p))).sum

/-- Every realized proposal generated by a stateful run stays below the same
capability ceiling. -/
def StatefulTrajectoryProposalCapabilityBounded
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D)
    (c : ℚ) (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv) : Prop :=
  ∀ p ∈ statefulRealizedProposals D adv schedule cfg, adv.capability p ≤ c

/-- Typeclass form of stateful kernel-action perturbation freedom. The field
is the concrete per-action/per-state zero-distance witness. -/
class IsKernelPerturbationFreeAdversary
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D) where
  kernel_action_zero_distance :
    ∀ (a : D.actionSpace.Action) (S : GovernanceState),
      spectralDistance (adv.stateRealization S)
        (adv.stateRealization (D.actionSpace.apply a S)) = 0

/-- Typeclass form of local state-decision stability. The field is the
concrete basin witness from realization distance to decision agreement. -/
class IsLocallyStableStatefulAdversary
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D)
    (S₀ : GovernanceState) (radius : ℚ) where
  stable_within_realization :
    ∀ S : GovernanceState,
      spectralDistance D.spectralGraph (adv.stateRealization S) < radius →
        StateClaimDecisionsAgree S₀ S

private lemma stateful_proposal_budget_le_length_mul
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D)
    (c : ℚ) :
    ∀ proposals : List adv.Proposal,
      (∀ p ∈ proposals, adv.capability p ≤ c) →
        ((proposals.map fun p => perturbationBound (adv.capability p)).sum ≤
          proposals.length * perturbationBound c)
  | [], _ => by simp
  | p :: proposals, hcap => by
      have hp : adv.capability p ≤ c := hcap p (by simp)
      have hrest : ∀ q ∈ proposals, adv.capability q ≤ c := by
        intro q hq
        exact hcap q (by simp [hq])
      have ih := stateful_proposal_budget_le_length_mul D adv c proposals hrest
      calc
        ((p :: proposals).map fun q => perturbationBound (adv.capability q)).sum
            = perturbationBound (adv.capability p) +
                (proposals.map fun q => perturbationBound (adv.capability q)).sum := by
              simp
        _ ≤ perturbationBound c + proposals.length * perturbationBound c := by
              exact add_le_add (perturbationBound_mono hp) ih
        _ = (p :: proposals).length * perturbationBound c := by
              simp [add_mul, add_comm]

/-- Capability-ceiling bound for the realized adaptive proposal trace. -/
lemma statefulTrajectoryPerturbationBound_le_of_capability_ceiling
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D)
    (c : ℚ) (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv)
    (hcap : StatefulTrajectoryProposalCapabilityBounded D adv c schedule cfg) :
    statefulTrajectoryPerturbationBound D adv schedule cfg ≤
      (statefulRealizedProposals D adv schedule cfg).length *
        perturbationBound c := by
  unfold statefulTrajectoryPerturbationBound
  exact stateful_proposal_budget_le_length_mul D adv c
    (statefulRealizedProposals D adv schedule cfg) hcap

private lemma distance_bound_stateful_trajectory_from
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D)
    [IsKernelPerturbationFreeAdversary D adv] :
    ∀ (schedule : List (StatefulScheduleStep D))
      (cfg : StatefulAdversaryConfig adv),
      spectralDistance (adv.stateRealization cfg.state)
        (adv.stateRealization
          (applyStatefulTrajectory D adv schedule cfg).state) ≤
          statefulTrajectoryPerturbationBound D adv schedule cfg := by
  intro schedule
  induction schedule with
  | nil =>
      intro cfg
      simpa [applyStatefulTrajectory, statefulTrajectoryPerturbationBound,
        statefulRealizedProposals]
        using (show spectralDistance (adv.stateRealization cfg.state)
          (adv.stateRealization cfg.state) ≤ 0 by simp [spectralDistance_self])
  | cons step rest ih =>
      intro cfg
      cases step with
      | kernel a =>
          let nextCfg : StatefulAdversaryConfig adv :=
            applyStatefulStep D adv (StatefulScheduleStep.kernel a) cfg
          have hRestDist := ih nextCfg
          have hStepZero :
              spectralDistance (adv.stateRealization cfg.state)
                (adv.stateRealization nextCfg.state) = 0 := by
            simpa [nextCfg, applyStatefulStep] using
              IsKernelPerturbationFreeAdversary.kernel_action_zero_distance
                (D := D) (adv := adv) a cfg.state
          have hTri :=
            spectralDistance_triangle
              (adv.stateRealization cfg.state)
              (adv.stateRealization nextCfg.state)
              (adv.stateRealization
                (applyStatefulTrajectory D adv rest nextCfg).state)
          have hStepLe :
              spectralDistance (adv.stateRealization cfg.state)
                (adv.stateRealization
                  (applyStatefulTrajectory D adv rest nextCfg).state) ≤
                statefulTrajectoryPerturbationBound D adv rest nextCfg := by
            rw [hStepZero, zero_add] at hTri
            exact le_trans hTri hRestDist
          simpa [applyStatefulTrajectory, statefulTrajectoryPerturbationBound,
            statefulRealizedProposals, applyStatefulStep, nextCfg] using hStepLe
      | adversary =>
          let p := adv.propose cfg.memory cfg.state
          let nextCfg : StatefulAdversaryConfig adv :=
            applyStatefulStep D adv StatefulScheduleStep.adversary cfg
          have hRestDist := ih nextCfg
          have hStepBound :
              spectralDistance (adv.stateRealization cfg.state)
                (adv.stateRealization nextCfg.state) ≤
                perturbationBound (adv.capability p) := by
            simpa [p, nextCfg, applyStatefulStep] using
              adv.capabilityPerturbationBound p cfg.state
          have hTri :=
            spectralDistance_triangle
              (adv.stateRealization cfg.state)
              (adv.stateRealization nextCfg.state)
              (adv.stateRealization
                (applyStatefulTrajectory D adv rest nextCfg).state)
          have hStepLe :
              spectralDistance (adv.stateRealization cfg.state)
                (adv.stateRealization
                  (applyStatefulTrajectory D adv rest nextCfg).state) ≤
                perturbationBound (adv.capability p) +
                  statefulTrajectoryPerturbationBound D adv rest nextCfg := by
            exact le_trans hTri (add_le_add hStepBound hRestDist)
          simpa [applyStatefulTrajectory, statefulTrajectoryPerturbationBound,
            statefulRealizedProposals, applyStatefulStep, p, nextCfg] using hStepLe

/-- Stateful adaptive adversaries preserve the initial claim-decision surface
whenever the realized adaptive perturbation budget remains below the datum's
graph-derived critical capability. The adversary can remember prior kernel
responses and choose later proposals from that memory; only the realized
capability budget is constrained. -/
theorem stateful_budgeted_subcritical_trajectory_preserves_stable_state_decisions
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : StatefulAdversaryLayer D)
    (hδ : 0 < D.toleranceParameter)
    (hcv : 0 < D.spectralGraph.cv D.spectralSignal)
    [IsKernelPerturbationFreeAdversary D adv]
    [IsLocallyStableStatefulAdversary D adv sys.state
      (kernelDataCriticalCapability D)] :
    ∀ schedule : List (StatefulScheduleStep D),
      statefulTrajectoryPerturbationBound D adv schedule
          (initialStatefulAdversaryConfig D adv) <
          kernelDataCriticalCapability D →
        0 < kernelDataCriticalCapability D ∧
        StateClaimDecisionsAgree sys.state
          (applyStatefulTrajectory D adv schedule
            (initialStatefulAdversaryConfig D adv)).state ∧
        spectralDistance D.spectralGraph
          (adv.stateRealization
            (applyStatefulTrajectory D adv schedule
              (initialStatefulAdversaryConfig D adv)).state) <
          kernelDataCriticalCapability D := by
  intro schedule hbudget
  have hthreshold_pos := kernelDataCriticalCapability_pos D hδ hcv
  have hdistBase :=
    distance_bound_stateful_trajectory_from D adv schedule
      (initialStatefulAdversaryConfig D adv)
  have hdist :
      spectralDistance D.spectralGraph
        (adv.stateRealization
          (applyStatefulTrajectory D adv schedule
            (initialStatefulAdversaryConfig D adv)).state) <
        kernelDataCriticalCapability D := by
    have hdist' :
        spectralDistance (adv.stateRealization sys.state)
          (adv.stateRealization
            (applyStatefulTrajectory D adv schedule
              (initialStatefulAdversaryConfig D adv)).state) <
          kernelDataCriticalCapability D :=
      lt_of_le_of_lt (by
        simpa [initialStatefulAdversaryConfig] using hdistBase) hbudget
    simpa [adv.stateCoherent] using hdist'
  exact ⟨hthreshold_pos,
    IsLocallyStableStatefulAdversary.stable_within_realization
      (D := D) (adv := adv) (S₀ := sys.state)
      (radius := kernelDataCriticalCapability D) _ hdist,
    hdist⟩

/-- Capability-ceiling form for stateful adaptive adversaries. The ceiling is
checked over the realized proposals generated from feedback, and the theorem
requires the realized number of adversary turns times the ceiling to remain
subcritical. -/
theorem stateful_capability_ceiling_subcritical_trajectory_preserves_stable_state_decisions
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : StatefulAdversaryLayer D)
    (hδ : 0 < D.toleranceParameter)
    (hcv : 0 < D.spectralGraph.cv D.spectralSignal)
    [IsKernelPerturbationFreeAdversary D adv]
    [IsLocallyStableStatefulAdversary D adv sys.state
      (kernelDataCriticalCapability D)] :
    ∀ (c : ℚ) (schedule : List (StatefulScheduleStep D)),
      0 ≤ c →
      StatefulTrajectoryProposalCapabilityBounded D adv c schedule
        (initialStatefulAdversaryConfig D adv) →
      (statefulRealizedProposals D adv schedule
        (initialStatefulAdversaryConfig D adv)).length * c <
          kernelDataCriticalCapability D →
        0 < kernelDataCriticalCapability D ∧
        StateClaimDecisionsAgree sys.state
          (applyStatefulTrajectory D adv schedule
            (initialStatefulAdversaryConfig D adv)).state ∧
        spectralDistance D.spectralGraph
          (adv.stateRealization
            (applyStatefulTrajectory D adv schedule
              (initialStatefulAdversaryConfig D adv)).state) <
          kernelDataCriticalCapability D := by
  intro c schedule hc_nonneg hcap hbudget
  have hceil :=
    statefulTrajectoryPerturbationBound_le_of_capability_ceiling D adv c
      schedule (initialStatefulAdversaryConfig D adv) hcap
  have hc : perturbationBound c = c := by
    simp [perturbationBound, max_eq_left hc_nonneg]
  have hbudget' :
      statefulTrajectoryPerturbationBound D adv schedule
          (initialStatefulAdversaryConfig D adv) <
        kernelDataCriticalCapability D := by
    exact lt_of_le_of_lt hceil (by simpa [hc] using hbudget)
  exact
    stateful_budgeted_subcritical_trajectory_preserves_stable_state_decisions
      D adv hδ hcv schedule hbudget'

end Legitimacy
