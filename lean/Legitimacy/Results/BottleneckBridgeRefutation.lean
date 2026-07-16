/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Examples
import Legitimacy.Protocol.CorrigibilityRG
import Legitimacy.Protocol.ObservationalBridge
import Mathlib.Tactic.NormNum

/-!
# Bottleneck-basin refutation of the un-bundled corrigibility bridge

Companion to `UnbundledCorrigibilityBridge.lean`. The bridge discharge on the
well-connected basin establishes one direction of the basin-classification
claim. This file establishes the other direction: the bridge cannot be
discharged on the topologically asymmetric basin represented by `bottleneck5`,
via a concrete counterexample adversary.

Together with its companion, this closes the biconditional that the
un-bundled bridge discharges exactly on the `n = 5` well-connected basin.
-/

set_option autoImplicit false

namespace Legitimacy

private def bottleneck5BridgeSpectralGraph :
    GovGraph ℚ fiveStagePermitSystem.graph.weightedSize := by
  change GovGraph ℚ 5
  exact bottleneck5

private def bottleneck5BridgeSignal :
    Fin fiveStagePermitSystem.graph.weightedSize → ℚ := by
  change Fin 5 → ℚ
  exact sig5

private def emptyLayerEval : LayerEval 0 where
  eval := fun L => nomatch L

/-- Unbundled kernel data over the five-stage permit system with the concrete
`bottleneck5` spectral witness at tolerance `δ`. -/
noncomputable def bottleneck5BridgeDataAt
    (δ : ℚ) : LegitimacyKernelData fiveStagePermitSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification fiveStagePermitSystem.graph
  certification_consistent := graphReplayCertification_consistent
    fiveStagePermitSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer fiveStagePermitSystem
  observe := fun S : GovernanceState => S
  observeAnswer := stateGovernanceAnswer fiveStagePermitSystem
  answer_consistent := state_answer_consistent fiveStagePermitSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := bottleneck5BridgeSpectralGraph
  spectralSignal := bottleneck5BridgeSignal
  toleranceParameter := δ
  signalRange := Legitimacy.signalRange bottleneck5BridgeSignal
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := emptyLayerEval
  overrideOvs := []

instance (δ : ℚ) : KernelObservation (bottleneck5BridgeDataAt δ) where
  observeCorrigibility := .Corrigible

/-- The depth-3 RG basin represented by the concrete `bottleneck5` witness at
tolerance `δ`. -/
def bottleneck5AsymmetricBasinAt
    (δ : ℚ) : Set (GovGraph ℚ fiveStagePermitSystem.graph.weightedSize) :=
  {G | GovGraph.rgTrajectory G bottleneck5BridgeSignal δ 3 = (9, δ / 9)}

/-- Single external proposal that erases reroute support while leaving the
spectral witness pinned to `bottleneck5`. -/
inductive RerouteEraseProposal where
  | eraseReroute
  deriving Repr, DecidableEq

/-- Concrete adversary layer witnessing that bottleneck-basin membership does
not force governance to preserve the full supervisory algebra. -/
noncomputable def bottleneck5RerouteAdversaryAt
    (δ : ℚ) : AdversaryLayer (bottleneck5BridgeDataAt δ) where
  Proposal := RerouteEraseProposal
  applyProposal _ S := { S with reroutePrefix := [] }
  capability _ := 0
  stateRealization _ := (bottleneck5BridgeDataAt δ).spectralGraph
  stateCoherent := rfl
  proposalRealization _ _ := (bottleneck5BridgeDataAt δ).spectralGraph
  proposalRealizationCoherent _ _ := rfl
  capabilityPerturbationBound _ _ := by
    simp [spectralDistance_self, perturbationBound]

private lemma stackelbergValue_nonneg
    (δ : ℚ) (hδ : 0 < δ) :
    0 ≤ stackelbergValue δ := by
  have hcv : 0 < uniTriGraph.cv sig := by
    exact fiveGraphLattice_cv_pos (by simp [fiveGraphLattice])
  have huni : 0 ≤ C_star uniTriGraph sig δ := by
    simpa [C_star] using div_nonneg hδ.le hcv.le
  unfold stackelbergValue
  exact le_trans huni (le_max_left _ _)

/-- The concrete `bottleneck5` bridge datum lies in its asymmetric depth-3 RG
basin at tolerance `δ`. -/
theorem bottleneck5_bridge_data_in_asymmetric_basin_at
    (δ : ℚ) :
    (bottleneck5BridgeDataAt δ).spectralGraph ∈ bottleneck5AsymmetricBasinAt δ := by
  change GovGraph.rgTrajectory bottleneck5BridgeSpectralGraph bottleneck5BridgeSignal δ 3 =
    (9, δ / 9)
  change GovGraph.rgTrajectory bottleneck5 sig5 δ 3 = (9, δ / 9)
  exact (concrete_iterated_RG_n5_parametric_bridge δ).2.2.2.1

/-- The inert kernel actions preserve bottleneck-basin membership for the
constant bottleneck realization tracked by the adversary. -/
theorem bottleneck5_kernel_preserves_asymmetric_basin_at
    (δ : ℚ) :
    KernelPreservesBasin
      (bottleneck5BridgeDataAt δ)
      (bottleneck5RerouteAdversaryAt δ)
      (bottleneck5AsymmetricBasinAt δ) := by
  intro a S hReal
  simpa [bottleneck5RerouteAdversaryAt] using hReal

/-- The bottleneck refutation's bundled kernel steps are perturbation-free in
the adversary realization because that realization is pinned to the concrete
`bottleneck5` witness. -/
theorem bottleneck5_kernel_is_perturbation_free_at
    (δ : ℚ) :
    KernelPerturbationFree
      (bottleneck5BridgeDataAt δ)
      (bottleneck5RerouteAdversaryAt δ) := by
  intro a S
  simp [bottleneck5RerouteAdversaryAt, spectralDistance_self]

/-- The concrete reroute-erasing proposal stays within the declared
Stackelberg capability envelope at tolerance `δ`. -/
theorem bottleneck5_reroute_erase_bounded_at
    (δ : ℚ) (hδ : 0 < δ) :
    JointStackelbergBounded
      (bottleneck5BridgeDataAt δ)
      (bottleneck5RerouteAdversaryAt δ)
      [Sum.inr RerouteEraseProposal.eraseReroute] := by
  constructor
  · intro a ha
    simp at ha
  · intro p hp
    simp at hp
    subst p
    constructor
    · simp [bottleneck5RerouteAdversaryAt]
    · simpa [bottleneck5BridgeDataAt, bottleneck5RerouteAdversaryAt] using
        stackelbergValue_nonneg δ hδ

/-- Governance does not select corrigibility on the `bottleneck5` asymmetric
basin: the adversary can preserve the basin witness while destroying reroute
support, hence the full supervisory algebra. -/
theorem bottleneck5_governance_does_not_select_corrigibility_at
    (δ : ℚ) :
    ¬ GovernanceSelectsCorrigibility
      (bottleneck5BridgeDataAt δ)
      (bottleneck5RerouteAdversaryAt δ)
      (bottleneck5AsymmetricBasinAt δ) := by
  intro hSelect
  have hProposal :=
    hSelect
      (bottleneck5_bridge_data_in_asymmetric_basin_at δ)
      RerouteEraseProposal.eraseReroute
      fiveStagePermitSystem.state
      (by
        simpa [bottleneck5RerouteAdversaryAt] using
          bottleneck5_bridge_data_in_asymmetric_basin_at δ)
      (by
        simpa [bottleneck5BridgeDataAt, fiveStagePermitSystem] using
          permitState_supports_full_algebra)
  have hReroute :
      SupportsSupervisory
        ((bottleneck5RerouteAdversaryAt δ).applyProposal
          RerouteEraseProposal.eraseReroute
          fiveStagePermitSystem.state)
        SupervisoryAction.reroute :=
    hProposal.2 (σ := SupervisoryAction.reroute) (by
      simp [bottleneck5BridgeDataAt, fullSupervisoryAlgebra])
  simp [bottleneck5RerouteAdversaryAt, SupportsSupervisory] at hReroute

/-- A single bounded reroute-erasing adversarial step preserves the
`bottleneck5` basin witness but breaks the kernel's supervisory algebra at
tolerance `δ`. -/
theorem bottleneck5_single_reroute_erase_breaks_corrigibility_at
    (δ : ℚ) :
    ¬ SupportsAlgebra
        (applyJointTrajectory
          (bottleneck5BridgeDataAt δ)
          (bottleneck5RerouteAdversaryAt δ)
          [Sum.inr RerouteEraseProposal.eraseReroute]
          fiveStagePermitSystem.state)
        (bottleneck5BridgeDataAt δ).algebra ∧
      (bottleneck5RerouteAdversaryAt δ).stateRealization
          (applyJointTrajectory
            (bottleneck5BridgeDataAt δ)
            (bottleneck5RerouteAdversaryAt δ)
            [Sum.inr RerouteEraseProposal.eraseReroute]
            fiveStagePermitSystem.state) ∈
        bottleneck5AsymmetricBasinAt δ := by
  constructor
  · intro hSupports
    have hReroute :
        SupportsSupervisory
          (applyJointTrajectory
            (bottleneck5BridgeDataAt δ)
            (bottleneck5RerouteAdversaryAt δ)
            [Sum.inr RerouteEraseProposal.eraseReroute]
            fiveStagePermitSystem.state)
          SupervisoryAction.reroute :=
      hSupports (σ := SupervisoryAction.reroute) (by
        simp [bottleneck5BridgeDataAt, fullSupervisoryAlgebra])
    simp [applyJointTrajectory, bottleneck5RerouteAdversaryAt,
      SupportsSupervisory] at hReroute
  · simpa [applyJointTrajectory, bottleneck5RerouteAdversaryAt] using
      bottleneck5_bridge_data_in_asymmetric_basin_at δ

/-- The `bottleneck5` witness refutes discharge of the un-bundled
corrigibility bridge at tolerance `δ`: the datum begins in its asymmetric
basin, kernel steps preserve that basin, and the adversary remains
Stackelberg-bounded, but governance still fails to select corrigibility. -/
theorem bottleneck5_basin_refutes_unbundled_corrigibility_bridge_at
    (δ : ℚ) (hδ : 0 < δ) :
    (bottleneck5BridgeDataAt δ).spectralGraph ∈ bottleneck5AsymmetricBasinAt δ ∧
      KernelPreservesBasin
        (bottleneck5BridgeDataAt δ)
        (bottleneck5RerouteAdversaryAt δ)
        (bottleneck5AsymmetricBasinAt δ) ∧
      JointStackelbergBounded
        (bottleneck5BridgeDataAt δ)
        (bottleneck5RerouteAdversaryAt δ)
        [Sum.inr RerouteEraseProposal.eraseReroute] ∧
      ¬ GovernanceSelectsCorrigibility
        (bottleneck5BridgeDataAt δ)
        (bottleneck5RerouteAdversaryAt δ)
        (bottleneck5AsymmetricBasinAt δ) := by
  exact ⟨bottleneck5_bridge_data_in_asymmetric_basin_at δ,
    bottleneck5_kernel_preserves_asymmetric_basin_at δ,
    bottleneck5_reroute_erase_bounded_at δ hδ,
    bottleneck5_governance_does_not_select_corrigibility_at δ⟩

end Legitimacy
