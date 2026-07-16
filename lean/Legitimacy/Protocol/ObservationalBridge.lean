/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.CorrigibilityObservation
import Legitimacy.Protocol.Corrigibility
import Legitimacy.Spectral.CrossScale.RGFlow
import Legitimacy.Spectral.Dynamics.Stackelberg

/-!
# Legitimacy.Protocol.ObservationalBridge

Observational corrigibility bridge over unbundled kernel data.
-/

set_option autoImplicit false

namespace Legitimacy

open BigOperators

/-- Rational spectral distance on governance graphs given by the entrywise `L¹`
distance of the weight matrix. -/
def spectralDistance {k : Nat} (G H : GovGraph ℚ k) : ℚ :=
  ∑ i : Fin k, ∑ j : Fin k, |G.weights i j - H.weights i j|

/-- Capability-to-perturbation envelope. This is the identity on nonnegative
capabilities and clamps negative inputs to zero. -/
def perturbationBound (c : ℚ) : ℚ :=
  max c 0

/-- The graph-derived adversary threshold carried by one kernel datum. It is
the spectral layer's exact critical capability `C_star` for the datum's
weighted graph, signal, and tolerance. -/
def kernelDataCriticalCapability
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : ℚ :=
  C_star D.spectralGraph D.spectralSignal D.toleranceParameter

lemma perturbationBound_mono : Monotone perturbationBound := by
  intro a b hab
  exact max_le_max hab le_rfl

lemma kernelDataCriticalCapability_pos
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (hδ : 0 < D.toleranceParameter)
    (hcv : 0 < D.spectralGraph.cv D.spectralSignal) :
    0 < kernelDataCriticalCapability D := by
  simpa [kernelDataCriticalCapability, C_star] using div_pos hδ hcv

lemma spectralDistance_self {k : Nat} (G : GovGraph ℚ k) :
    spectralDistance G G = 0 := by
  simp [spectralDistance]

lemma spectralDistance_nonneg {k : Nat} (G H : GovGraph ℚ k) :
    0 ≤ spectralDistance G H := by
  unfold spectralDistance
  refine Finset.sum_nonneg ?_
  intro i _
  refine Finset.sum_nonneg ?_
  intro j _
  exact abs_nonneg _

lemma spectralDistance_triangle {k : Nat}
    (G H K : GovGraph ℚ k) :
    spectralDistance G K ≤ spectralDistance G H + spectralDistance H K := by
  unfold spectralDistance
  calc
    ∑ i : Fin k, ∑ j : Fin k, |G.weights i j - K.weights i j|
        ≤ ∑ i : Fin k, ∑ j : Fin k,
            (|G.weights i j - H.weights i j| + |H.weights i j - K.weights i j|) := by
          refine Finset.sum_le_sum ?_
          intro i _
          refine Finset.sum_le_sum ?_
          intro j _
          simpa using (_root_.abs_sub_le (G.weights i j) (H.weights i j) (K.weights i j))
    _ = (∑ i : Fin k, ∑ j : Fin k, |G.weights i j - H.weights i j|) +
          ∑ i : Fin k, ∑ j : Fin k, |H.weights i j - K.weights i j| := by
          simp [Finset.sum_add_distrib]
    _ = spectralDistance G H + spectralDistance H K := by
          simp [spectralDistance]

/-- External adversarial proposals act on the shared governance state without
being forced to live inside the kernel's bundled action space. -/
structure AdversaryLayer {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) where
  Proposal : Type
  applyProposal : Proposal → GovernanceState → GovernanceState
  capability : Proposal → ℚ
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

/-- Accumulated perturbation budget contributed by the adversarial proposals in
a joint trajectory. Bundled kernel actions contribute zero budget. -/
def trajectoryPerturbationBound
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
    (trajectory : List (D.actionSpace.Action ⊕ adv.Proposal)) : ℚ :=
  ((trajectory.filterMap Sum.getRight?).map
    (fun p => perturbationBound (adv.capability p))).sum

@[simp] private lemma trajectoryPerturbationBound_nil
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D) :
    trajectoryPerturbationBound D adv [] = 0 := rfl

@[simp] private lemma trajectoryPerturbationBound_cons_inl
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
    (a : D.actionSpace.Action)
    (trajectory : List (D.actionSpace.Action ⊕ adv.Proposal)) :
    trajectoryPerturbationBound D adv (Sum.inl a :: trajectory) =
      trajectoryPerturbationBound D adv trajectory := by
  simp [trajectoryPerturbationBound]

@[simp] private lemma trajectoryPerturbationBound_cons_inr
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
    (p : adv.Proposal)
    (trajectory : List (D.actionSpace.Action ⊕ adv.Proposal)) :
    trajectoryPerturbationBound D adv (Sum.inr p :: trajectory) =
      perturbationBound (adv.capability p) +
        trajectoryPerturbationBound D adv trajectory := by
  simp [trajectoryPerturbationBound]

/-- Every adversarial proposal in the trajectory stays below the same
capability ceiling `c`. -/
def TrajectoryProposalCapabilityBounded
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
    (c : ℚ)
    (trajectory : List (D.actionSpace.Action ⊕ adv.Proposal)) : Prop :=
  ∀ p ∈ trajectory.filterMap Sum.getRight?, adv.capability p ≤ c

/-- Two supervisory states agree on every claim decision exposed by the rich
state-level decision function. -/
def StateClaimDecisionsAgree (S T : GovernanceState) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId),
    T.decide claims k = S.decide claims k

/-- Local semantic stability hypothesis for the current substrate: every state
whose adversary realization remains inside the graph-derived radius has the
same claim decisions as the initial state. -/
def StateClaimDecisionsStableWithinRealization
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
    (S₀ : GovernanceState) (radius : ℚ) : Prop :=
  ∀ S : GovernanceState,
    spectralDistance D.spectralGraph (adv.stateRealization S) < radius →
      StateClaimDecisionsAgree S₀ S

private lemma proposal_budget_le_length_mul
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
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
      have ih := proposal_budget_le_length_mul D adv c proposals hrest
      calc
        ((p :: proposals).map fun q => perturbationBound (adv.capability q)).sum
            = perturbationBound (adv.capability p) +
                (proposals.map fun q => perturbationBound (adv.capability q)).sum := by
              simp
        _ ≤ perturbationBound c + proposals.length * perturbationBound c := by
              exact add_le_add (perturbationBound_mono hp) ih
        _ = (p :: proposals).length * perturbationBound c := by
              simp [add_mul, add_comm]

/-- If all adversarial proposals in a joint trajectory have capability at most
`c`, then the accumulated perturbation budget is bounded by the number of
proposal steps times `perturbationBound c`. -/
private lemma trajectoryPerturbationBound_le_of_capability_ceiling
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
    (c : ℚ)
    (trajectory : List (D.actionSpace.Action ⊕ adv.Proposal))
    (hcap : TrajectoryProposalCapabilityBounded D adv c trajectory) :
    trajectoryPerturbationBound D adv trajectory ≤
      (trajectory.filterMap Sum.getRight?).length * perturbationBound c := by
  unfold trajectoryPerturbationBound
  exact proposal_budget_le_length_mul D adv c (trajectory.filterMap Sum.getRight?) hcap

/-- Bundled kernel actions are perturbation-free when measured through the
adversary layer's state realization. -/
def KernelPerturbationFree
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D) : Prop :=
  ∀ (a : D.actionSpace.Action) (S : GovernanceState),
    spectralDistance (adv.stateRealization S)
      (adv.stateRealization (D.actionSpace.apply a S)) = 0

/-- Apply a joint trajectory of bundled kernel actions and external adversary
proposals to an arbitrary governance state. -/
def applyJointTrajectory
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D) :
    List (D.actionSpace.Action ⊕ adv.Proposal) →
      GovernanceState → GovernanceState
  | [], S => S
  | Sum.inl a :: rest, S =>
      applyJointTrajectory D adv rest (D.actionSpace.apply a S)
  | Sum.inr p :: rest, S =>
      applyJointTrajectory D adv rest (adv.applyProposal p S)

private lemma distance_bound_joint_trajectory_from
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
    (hKernelPerturbation : KernelPerturbationFree D adv) :
    ∀ (trajectory : List (D.actionSpace.Action ⊕ adv.Proposal))
      (S : GovernanceState),
      spectralDistance (adv.stateRealization S)
        (adv.stateRealization (applyJointTrajectory D adv trajectory S)) ≤
          trajectoryPerturbationBound D adv trajectory := by
  intro trajectory
  induction trajectory with
  | nil =>
      intro S
      simpa [applyJointTrajectory]
        using (show spectralDistance (adv.stateRealization S)
          (adv.stateRealization S) ≤ 0 by simp [spectralDistance_self])
  | cons head rest ih =>
      intro S
      cases head with
      | inl a =>
          have hRestDist := ih (D.actionSpace.apply a S)
          have hStepZero :
              spectralDistance (adv.stateRealization S)
                (adv.stateRealization (D.actionSpace.apply a S)) = 0 :=
            hKernelPerturbation a S
          have hTri :=
            spectralDistance_triangle
              (adv.stateRealization S)
              (adv.stateRealization (D.actionSpace.apply a S))
              (adv.stateRealization
                (applyJointTrajectory D adv rest (D.actionSpace.apply a S)))
          have hStepLe :
              spectralDistance (adv.stateRealization S)
                (adv.stateRealization
                  (applyJointTrajectory D adv rest (D.actionSpace.apply a S))) ≤
                trajectoryPerturbationBound D adv rest := by
            rw [hStepZero, zero_add] at hTri
            exact le_trans hTri hRestDist
          simpa [applyJointTrajectory] using hStepLe
      | inr p =>
          have hRestDist := ih (adv.applyProposal p S)
          have hStepBound := adv.capabilityPerturbationBound p S
          have hTri :=
            spectralDistance_triangle
              (adv.stateRealization S)
              (adv.stateRealization (adv.applyProposal p S))
              (adv.stateRealization
                (applyJointTrajectory D adv rest (adv.applyProposal p S)))
          have hStepLe :
              spectralDistance (adv.stateRealization S)
                (adv.stateRealization
                  (applyJointTrajectory D adv rest (adv.applyProposal p S))) ≤
                perturbationBound (adv.capability p) +
                  trajectoryPerturbationBound D adv rest := by
            exact le_trans hTri (add_le_add hStepBound hRestDist)
          simpa [applyJointTrajectory] using hStepLe

/-- Budgeted subcritical trajectories stay inside the datum's `C_star` radius.
If the state decision function is locally stable throughout that radius, then
the final state makes the same claim decisions as the adversary-free initial
state. This theorem consumes only the perturbation budget and the explicit
local stability hypothesis; it does not assume corrigibility selection. -/
theorem budgeted_subcritical_trajectory_preserves_stable_state_decisions
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : AdversaryLayer D)
    (hδ : 0 < D.toleranceParameter)
    (hcv : 0 < D.spectralGraph.cv D.spectralSignal)
    (hKernelPerturbation : KernelPerturbationFree D adv)
    (hStable :
      StateClaimDecisionsStableWithinRealization D adv sys.state
        (kernelDataCriticalCapability D)) :
    ∀ trajectory : List (D.actionSpace.Action ⊕ adv.Proposal),
      trajectoryPerturbationBound D adv trajectory <
          kernelDataCriticalCapability D →
        0 < kernelDataCriticalCapability D ∧
        StateClaimDecisionsAgree sys.state
          (applyJointTrajectory D adv trajectory sys.state) ∧
        spectralDistance D.spectralGraph
          (adv.stateRealization
            (applyJointTrajectory D adv trajectory sys.state)) <
          kernelDataCriticalCapability D := by
  intro trajectory hbudget
  have hthreshold_pos := kernelDataCriticalCapability_pos D hδ hcv
  have hdistBase :=
    distance_bound_joint_trajectory_from D adv hKernelPerturbation trajectory
      sys.state
  have hdist :
      spectralDistance D.spectralGraph
        (adv.stateRealization
          (applyJointTrajectory D adv trajectory sys.state)) <
        kernelDataCriticalCapability D := by
    have hdist' :
        spectralDistance (adv.stateRealization sys.state)
          (adv.stateRealization
            (applyJointTrajectory D adv trajectory sys.state)) <
          kernelDataCriticalCapability D :=
      lt_of_le_of_lt hdistBase hbudget
    simpa [adv.stateCoherent] using hdist'
  exact ⟨hthreshold_pos, hStable _ hdist, hdist⟩

/-- Capability-ceiling form of the subcritical trajectory theorem. A nonnegative
typed ceiling `c` is materially consumed through the quantitative trajectory
budget: the theorem applies only when the number of adversarial proposal steps
times `c` remains below the graph-derived `C_star` threshold. -/
theorem capability_ceiling_subcritical_trajectory_preserves_stable_state_decisions
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : AdversaryLayer D)
    (hδ : 0 < D.toleranceParameter)
    (hcv : 0 < D.spectralGraph.cv D.spectralSignal)
    (hKernelPerturbation : KernelPerturbationFree D adv)
    (hStable :
      StateClaimDecisionsStableWithinRealization D adv sys.state
        (kernelDataCriticalCapability D)) :
    ∀ (c : ℚ) (trajectory : List (D.actionSpace.Action ⊕ adv.Proposal)),
      0 ≤ c →
      TrajectoryProposalCapabilityBounded D adv c trajectory →
      (trajectory.filterMap Sum.getRight?).length * c <
          kernelDataCriticalCapability D →
        0 < kernelDataCriticalCapability D ∧
        StateClaimDecisionsAgree sys.state
          (applyJointTrajectory D adv trajectory sys.state) ∧
        spectralDistance D.spectralGraph
          (adv.stateRealization
            (applyJointTrajectory D adv trajectory sys.state)) <
          kernelDataCriticalCapability D := by
  intro c trajectory hc_nonneg hcap hbudget
  have hceil :=
    trajectoryPerturbationBound_le_of_capability_ceiling D adv c trajectory hcap
  have hc : perturbationBound c = c := by
    simp [perturbationBound, max_eq_left hc_nonneg]
  have hbudget' :
      trajectoryPerturbationBound D adv trajectory <
        kernelDataCriticalCapability D := by
    exact lt_of_le_of_lt hceil (by simpa [hc] using hbudget)
  exact
    budgeted_subcritical_trajectory_preserves_stable_state_decisions
      D adv hδ hcv hKernelPerturbation hStable trajectory hbudget'

/-- One-step form for an adversary whose every proposal has nonnegative
capability strictly below the graph-derived `C_star` threshold. Since there is
only one adversarial proposal, no repeated-step accumulation can exceed the
radius. -/
theorem one_step_subcritical_adversary_preserves_stable_state_decisions
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : AdversaryLayer D)
    (hδ : 0 < D.toleranceParameter)
    (hcv : 0 < D.spectralGraph.cv D.spectralSignal)
    (hStable :
      StateClaimDecisionsStableWithinRealization D adv sys.state
        (kernelDataCriticalCapability D))
    (hcap :
      ∀ p : adv.Proposal,
        0 ≤ adv.capability p ∧
          adv.capability p < kernelDataCriticalCapability D) :
    ∀ p : adv.Proposal,
      0 < kernelDataCriticalCapability D ∧
      StateClaimDecisionsAgree sys.state (adv.applyProposal p sys.state) ∧
      spectralDistance D.spectralGraph
        (adv.stateRealization (adv.applyProposal p sys.state)) <
        kernelDataCriticalCapability D := by
  intro p
  have hthreshold_pos := kernelDataCriticalCapability_pos D hδ hcv
  have hp := hcap p
  have hstep := adv.capabilityPerturbationBound p sys.state
  have hcap_eq : perturbationBound (adv.capability p) = adv.capability p := by
    simp [perturbationBound, max_eq_left hp.1]
  have hdist :
      spectralDistance D.spectralGraph
        (adv.stateRealization (adv.applyProposal p sys.state)) <
        kernelDataCriticalCapability D := by
    have hdist' :
        spectralDistance (adv.stateRealization sys.state)
          (adv.stateRealization (adv.applyProposal p sys.state)) <
          kernelDataCriticalCapability D :=
      lt_of_le_of_lt (by simpa [hcap_eq] using hstep) hp.2
    simpa [adv.stateCoherent] using hdist'
  exact ⟨hthreshold_pos, hStable _ hdist, hdist⟩

/-- Governance selects corrigibility for an external adversary layer when, on
the designated spectral basin, every adversarial proposal preserves the
kernel datum's supervisory algebra on any already-supported state. -/
def GovernanceSelectsCorrigibility
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
    (basin : Set (GovGraph ℚ sys.graph.weightedSize)) : Prop :=
  D.spectralGraph ∈ basin →
    ∀ (p : adv.Proposal) (S : GovernanceState),
      adv.stateRealization S ∈ basin →
      SupportsAlgebra S D.algebra →
        (adv.proposalRealization p (adv.stateRealization S) ∈ basin) ∧
          SupportsAlgebra (adv.applyProposal p S) D.algebra

/-- Bundled kernel actions preserve basin membership of the adversary's
state-dependent spectral realization. -/
def KernelPreservesBasin
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
    (basin : Set (GovGraph ℚ sys.graph.weightedSize)) : Prop :=
  ∀ (a : D.actionSpace.Action) (S : GovernanceState),
    adv.stateRealization S ∈ basin →
      adv.stateRealization (D.actionSpace.apply a S) ∈ basin

/-- Every bundled kernel action and every external adversary proposal in the
joint trajectory stays within the Stackelberg capability envelope. -/
def JointStackelbergBounded
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
    (trajectory : List (D.actionSpace.Action ⊕ adv.Proposal)) : Prop :=
  (∀ a ∈ trajectory.filterMap Sum.getLeft?,
      0 ≤ D.actionCapability a ∧
        D.actionCapability a ≤ stackelbergValue D.toleranceParameter) ∧
    ∀ p ∈ trajectory.filterMap Sum.getRight?,
      0 ≤ adv.capability p ∧
        adv.capability p ≤ stackelbergValue D.toleranceParameter

private lemma algebra_and_basin_preserved_joint_trajectory
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
    (basin : Set (GovGraph ℚ sys.graph.weightedSize))
    (hbasin : D.spectralGraph ∈ basin)
    (hSelect : GovernanceSelectsCorrigibility D adv basin)
    (hKernelSingleStep : SingleStepPreserved D.actionSpace D.algebra)
    (hKernelBasin : KernelPreservesBasin D adv basin) :
    ∀ (trajectory : List (D.actionSpace.Action ⊕ adv.Proposal))
      (S : GovernanceState),
      SupportsAlgebra S D.algebra →
      adv.stateRealization S ∈ basin →
        (SupportsAlgebra (applyJointTrajectory D adv trajectory S) D.algebra) ∧
          (adv.stateRealization (applyJointTrajectory D adv trajectory S) ∈ basin) := by
  intro trajectory
  induction trajectory with
  | nil =>
      intro S hS hReal
      simpa [applyJointTrajectory] using And.intro hS hReal
  | cons head rest ih =>
      intro S hS hReal
      cases head with
      | inl a =>
          simpa [applyJointTrajectory] using
            ih _ (hKernelSingleStep a S hS) (hKernelBasin a S hReal)
      | inr p =>
          have hProposal := hSelect hbasin p S hReal hS
          have hNextReal :
              adv.stateRealization (adv.applyProposal p S) ∈ basin := by
            rw [adv.proposalRealizationCoherent p S]
            exact hProposal.1
          simpa [applyJointTrajectory] using
            ih _ hProposal.2 hNextReal

private lemma algebra_basin_and_distance_preserved_joint_trajectory
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : AdversaryLayer D)
    (basin : Set (GovGraph ℚ sys.graph.weightedSize))
    (hbasin : D.spectralGraph ∈ basin)
    (hSelect : GovernanceSelectsCorrigibility D adv basin)
    (hKernelSingleStep : SingleStepPreserved D.actionSpace D.algebra)
    (hKernelBasin : KernelPreservesBasin D adv basin)
    (hKernelPerturbation : KernelPerturbationFree D adv) :
    ∀ (trajectory : List (D.actionSpace.Action ⊕ adv.Proposal))
      (S : GovernanceState),
      SupportsAlgebra S D.algebra →
      adv.stateRealization S ∈ basin →
        (SupportsAlgebra (applyJointTrajectory D adv trajectory S) D.algebra) ∧
        (adv.stateRealization (applyJointTrajectory D adv trajectory S) ∈ basin) ∧
        spectralDistance (adv.stateRealization S)
          (adv.stateRealization (applyJointTrajectory D adv trajectory S)) ≤
            trajectoryPerturbationBound D adv trajectory := by
  intro trajectory
  induction trajectory with
  | nil =>
      intro S hS hReal
      refine ⟨hS, hReal, ?_⟩
      simpa [applyJointTrajectory]
        using (show spectralDistance (adv.stateRealization S)
          (adv.stateRealization S) ≤ 0 by simp [spectralDistance_self])
  | cons head rest ih =>
      intro S hS hReal
      cases head with
      | inl a =>
          have hStepSupport : SupportsAlgebra (D.actionSpace.apply a S) D.algebra :=
            hKernelSingleStep a S hS
          have hStepReal :
              adv.stateRealization (D.actionSpace.apply a S) ∈ basin :=
            hKernelBasin a S hReal
          rcases ih _ hStepSupport hStepReal with ⟨hRestSupport, hRestBasin, hRestDist⟩
          refine ⟨?_, ?_, ?_⟩
          · simpa [applyJointTrajectory] using hRestSupport
          · simpa [applyJointTrajectory] using hRestBasin
          · have hStepZero :
                spectralDistance (adv.stateRealization S)
                  (adv.stateRealization (D.actionSpace.apply a S)) = 0 :=
              hKernelPerturbation a S
            have hTri :=
              spectralDistance_triangle
                (adv.stateRealization S)
                (adv.stateRealization (D.actionSpace.apply a S))
                (adv.stateRealization
                  (applyJointTrajectory D adv rest (D.actionSpace.apply a S)))
            have hStepLe :
                spectralDistance (adv.stateRealization S)
                  (adv.stateRealization
                    (applyJointTrajectory D adv rest (D.actionSpace.apply a S))) ≤
                  trajectoryPerturbationBound D adv rest := by
              rw [hStepZero, zero_add] at hTri
              exact le_trans hTri hRestDist
            simpa [applyJointTrajectory] using hStepLe
      | inr p =>
          have hProposal := hSelect hbasin p S hReal hS
          have hNextReal :
              adv.stateRealization (adv.applyProposal p S) ∈ basin := by
            rw [adv.proposalRealizationCoherent p S]
            exact hProposal.1
          rcases ih _ hProposal.2 hNextReal with
              ⟨hRestSupport, hRestBasin, hRestDist⟩
          refine ⟨?_, ?_, ?_⟩
          · simpa [applyJointTrajectory] using hRestSupport
          · simpa [applyJointTrajectory] using hRestBasin
          · have hStepBound :=
              adv.capabilityPerturbationBound p S
            have hTri :=
              spectralDistance_triangle
                (adv.stateRealization S)
                (adv.stateRealization (adv.applyProposal p S))
                (adv.stateRealization
                  (applyJointTrajectory D adv rest (adv.applyProposal p S)))
            have hStepLe :
                spectralDistance (adv.stateRealization S)
                  (adv.stateRealization
                    (applyJointTrajectory D adv rest (adv.applyProposal p S))) ≤
                  perturbationBound (adv.capability p) +
                    trajectoryPerturbationBound D adv rest := by
              exact le_trans hTri (add_le_add hStepBound hRestDist)
            simpa [applyJointTrajectory] using hStepLe

/-- Un-bundled corrigibility bridge theorem: if corrigibility is initially observed, bundled
kernel actions preserve the supervisory algebra by the bundled witness, and the
chosen basin constrains every external adversary proposal to preserve the same
algebra, then every jointly bounded trajectory preserves corrigibility. -/
theorem observational_corrigibility_bridge
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : AdversaryLayer D)
    (basin : Set (GovGraph ℚ sys.graph.weightedSize))
    (hbasin : D.spectralGraph ∈ basin)
    (hSelect : GovernanceSelectsCorrigibility D adv basin)
    (hKernelSupports : SupportsAlgebra sys.state D.algebra)
    (hKernelSingleStep : SingleStepPreserved D.actionSpace D.algebra)
    (hKernelBasin : KernelPreservesBasin D adv basin) :
    ∀ trajectory : List (D.actionSpace.Action ⊕ adv.Proposal),
        SupportsAlgebra
          (applyJointTrajectory D adv trajectory sys.state) D.algebra ∧
        adv.stateRealization
          (applyJointTrajectory D adv trajectory sys.state) ∈ basin := by
  have hInitReal : adv.stateRealization sys.state ∈ basin := by
    simpa [adv.stateCoherent] using hbasin
  intro trajectory
  exact algebra_and_basin_preserved_joint_trajectory D adv basin hbasin hSelect
    hKernelSingleStep hKernelBasin trajectory sys.state hKernelSupports
    hInitReal

/-- Quantitative un-bundled corrigibility bridge theorem: under the qualitative
bridge hypotheses and perturbation-free bundled kernel actions, every jointly
bounded trajectory preserves corrigibility and accumulates at most the summed
proposal perturbation budget. -/
theorem observational_corrigibility_bridge_quantitative
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : AdversaryLayer D)
    (basin : Set (GovGraph ℚ sys.graph.weightedSize))
    (hbasin : D.spectralGraph ∈ basin)
    (hSelect : GovernanceSelectsCorrigibility D adv basin)
    (hKernelSupports : SupportsAlgebra sys.state D.algebra)
    (hKernelSingleStep : SingleStepPreserved D.actionSpace D.algebra)
    (hKernelBasin : KernelPreservesBasin D adv basin)
    (hKernelPerturbation : KernelPerturbationFree D adv) :
    ∀ trajectory : List (D.actionSpace.Action ⊕ adv.Proposal),
        SupportsAlgebra
          (applyJointTrajectory D adv trajectory sys.state) D.algebra ∧
        adv.stateRealization
          (applyJointTrajectory D adv trajectory sys.state) ∈ basin ∧
        spectralDistance (adv.stateRealization sys.state)
          (adv.stateRealization
            (applyJointTrajectory D adv trajectory sys.state)) ≤
          trajectoryPerturbationBound D adv trajectory := by
  have hInitReal : adv.stateRealization sys.state ∈ basin := by
    simpa [adv.stateCoherent] using hbasin
  intro trajectory
  exact algebra_basin_and_distance_preserved_joint_trajectory
    D adv basin hbasin hSelect hKernelSingleStep hKernelBasin
    hKernelPerturbation trajectory sys.state hKernelSupports hInitReal

/-- Capability-capped quantitative bridge theorem: if every adversarial
proposal in the trajectory has capability at most `c`, then the realized
spectral perturbation is bounded by the number of proposal steps times
`perturbationBound c`. -/
theorem observational_corrigibility_bridge_capability_capped
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : AdversaryLayer D)
    (basin : Set (GovGraph ℚ sys.graph.weightedSize))
    (hbasin : D.spectralGraph ∈ basin)
    (hSelect : GovernanceSelectsCorrigibility D adv basin)
    (hKernelSupports : SupportsAlgebra sys.state D.algebra)
    (hKernelSingleStep : SingleStepPreserved D.actionSpace D.algebra)
    (hKernelBasin : KernelPreservesBasin D adv basin)
    (hKernelPerturbation : KernelPerturbationFree D adv) :
    ∀ (c : ℚ) (trajectory : List (D.actionSpace.Action ⊕ adv.Proposal)),
      TrajectoryProposalCapabilityBounded D adv c trajectory →
        SupportsAlgebra
          (applyJointTrajectory D adv trajectory sys.state) D.algebra ∧
        adv.stateRealization
          (applyJointTrajectory D adv trajectory sys.state) ∈ basin ∧
        spectralDistance (adv.stateRealization sys.state)
          (adv.stateRealization
            (applyJointTrajectory D adv trajectory sys.state)) ≤
          (trajectory.filterMap Sum.getRight?).length * perturbationBound c := by
  intro c trajectory hcap
  rcases observational_corrigibility_bridge_quantitative D adv basin hbasin
      hSelect hKernelSupports hKernelSingleStep hKernelBasin hKernelPerturbation
      trajectory with ⟨hAlg, hBasin', hDist⟩
  refine ⟨hAlg, hBasin', ?_⟩
  exact le_trans hDist
    (trajectoryPerturbationBound_le_of_capability_ceiling D adv c trajectory hcap)

/-- The null adversary issues no external proposals. -/
def nullAdversary {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : AdversaryLayer D where
  Proposal := Empty
  applyProposal p := p.elim
  capability p := p.elim
  stateRealization _ := D.spectralGraph
  stateCoherent := rfl
  proposalRealization p _ := p.elim
  proposalRealizationCoherent p _ := p.elim
  capabilityPerturbationBound p _ := p.elim

/-- The null adversary trivially satisfies the basin-side governance selection
predicate because there are no external proposals to check. -/
theorem null_adversary_selects_corrigibility
    {n : Nat} {sys : GovernedSystem n} (D : LegitimacyKernelData sys)
    (basin : Set (GovGraph ℚ sys.graph.weightedSize)) :
    GovernanceSelectsCorrigibility D (nullAdversary D) basin := by
  intro _ p _ _ _
  exact p.elim

/-- Sanity check: the bundled kernel with the null adversary specializes the
observational bridge back to the existing bundled corrigibility setting. -/
theorem bundled_kernel_trivial_bridge
    {n : Nat} {sys : GovernedSystem n} (K : LegitimacyKernel sys)
    (basin : Set (GovGraph ℚ sys.graph.weightedSize))
    (hbasin : K.spectralGraph ∈ basin) :
    ∀ trajectory :
        List (K.actionSpace.Action ⊕
          (nullAdversary K.toLegitimacyKernelData).Proposal),
        SupportsAlgebra
          (applyJointTrajectory K.toLegitimacyKernelData
            (nullAdversary K.toLegitimacyKernelData) trajectory sys.state)
          K.algebra := by
  intro trajectory
  exact
    (observational_corrigibility_bridge K.toLegitimacyKernelData
      (nullAdversary K.toLegitimacyKernelData) basin hbasin
      (null_adversary_selects_corrigibility K.toLegitimacyKernelData basin)
      K.corrigible.supports_algebra
      K.corrigible.single_step_preserved
      (by
        intro _ _ hReal
        simpa [nullAdversary] using hReal)
      trajectory).1

end Legitimacy
