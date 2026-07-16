/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.ObservationalBridge
import Legitimacy.Protocol.CorrigibilityRG
import Legitimacy.Kernel.Examples
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Legitimacy.Results.UnbundledCorrigibilityBridge

The un-bundled corrigibility bridge from
`Legitimacy.Protocol.ObservationalBridge` requires
`GovernanceSelectsCorrigibility` and `KernelPreservesBasin` on a chosen basin.
This file discharges both hypotheses for each well-connected-basin
representative in the `n = 5` verification lattice (`uniK5`, `asymK5`,
`nearPath5`, `wheel5`), producing concrete bridge witnesses for every graph
that `concrete_iterated_RG_n5_parametric_bridge` places in the `(10, δ / 10)`
attractor.

The bottleneck-basin refutation lives separately. Together these witnesses
support the positive direction of the basin-classification and ASI-safety
classification correspondence on the `n = 5` lattice.
-/

set_option autoImplicit false

namespace Legitimacy

private def bridgeSpectralGraph
    (G : GovGraph ℚ 5) :
    GovGraph ℚ fiveStagePermitSystem.graph.weightedSize := by
  change GovGraph ℚ 5
  exact G

private def bridgeSignal :
    Fin fiveStagePermitSystem.graph.weightedSize → ℚ := by
  change Fin 5 → ℚ
  exact sig5

private def emptyLayerEval : LayerEval 0 where
  eval := fun L => nomatch L

/-- Unbundled kernel data over the five-stage permit system with a chosen
well-connected `n = 5` spectral witness at tolerance `δ`. -/
noncomputable def wellConnectedBridgeData
    (δ : ℚ) (G : GovGraph ℚ 5) : LegitimacyKernelData fiveStagePermitSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification fiveStagePermitSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent fiveStagePermitSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer fiveStagePermitSystem
  observe := fun S : GovernanceState => S
  observeAnswer := stateGovernanceAnswer fiveStagePermitSystem
  answer_consistent := state_answer_consistent fiveStagePermitSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := bridgeSpectralGraph G
  spectralSignal := bridgeSignal
  toleranceParameter := δ
  signalRange := Legitimacy.signalRange bridgeSignal
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := emptyLayerEval
  overrideOvs := []

instance wellConnectedKernelObservation (δ : ℚ) (G : GovGraph ℚ 5) :
    KernelObservation (wellConnectedBridgeData δ G) where
  observeCorrigibility := .Corrigible

/-- The concrete well-connected basin used by the `n = 5` bridge witnesses at
tolerance `δ`. -/
def wellConnectedBridgeBasinAt
    (δ : ℚ) : Set (GovGraph ℚ fiveStagePermitSystem.graph.weightedSize) :=
  WellConnectedBasin bridgeSignal δ

/-- The well-connected basin specialized to tolerance `1 / 10`. -/
def wellConnectedBridgeBasin :
    Set (GovGraph ℚ fiveStagePermitSystem.graph.weightedSize) :=
  wellConnectedBridgeBasinAt (1 / 10)

/-- Single external proposal that attempts to retune the `w₀₁` edge. In this
setting the governance layer absorbs the proposal, so the realized state and
spectral witness remain unchanged. -/
inductive Edge01RetuneProposal where
  | retune
  deriving Repr, DecidableEq

/-- Concrete adversary layer shared by every well-connected-basin witness. -/
noncomputable def wellConnectedBridgeAdversary
    (D : LegitimacyKernelData fiveStagePermitSystem) : AdversaryLayer D where
  Proposal := Edge01RetuneProposal
  applyProposal _ S := S
  capability _ := D.toleranceParameter / 50
  stateRealization _ := D.spectralGraph
  stateCoherent := rfl
  proposalRealization _ G := G
  proposalRealizationCoherent _ _ := rfl
  capabilityPerturbationBound _ _ := by
    simp [spectralDistance_self, perturbationBound]

/-- `uniK5` bridge datum, kept as a named abbreviation for the original
witness. -/
noncomputable abbrev uniK5BridgeData : LegitimacyKernelData fiveStagePermitSystem :=
  wellConnectedBridgeData (1 / 10) uniK5

/-- `uniK5` uses the shared inert retuning adversary. -/
noncomputable abbrev uniK5Edge01Adversary : AdversaryLayer uniK5BridgeData :=
  wellConnectedBridgeAdversary uniK5BridgeData

private lemma stackelbergValue_nonneg
    (δ : ℚ) (hδ : 0 < δ) :
    0 ≤ stackelbergValue δ := by
  have hcv : 0 < uniTriGraph.cv sig := by
    exact fiveGraphLattice_cv_pos (by simp [fiveGraphLattice])
  have huni : 0 ≤ C_star uniTriGraph sig δ := by
    simpa [C_star] using div_nonneg hδ.le hcv.le
  unfold stackelbergValue
  exact le_trans huni (le_max_left _ _)

private lemma tolerance_div_fifty_le_stackelbergValue
    (δ : ℚ) (hδ : 0 < δ) :
    δ / 50 ≤ stackelbergValue δ := by
  have hsmall : δ / 50 ≤ δ := by
    linarith
  rcases concrete_cv_values with ⟨huni, _, _, _, _⟩
  have huni_le : δ ≤ stackelbergValue δ := by
    calc
      δ = C_star uniTriGraph sig δ := by
        simp [C_star, huni]
      _ ≤ stackelbergValue δ := by
        simp [stackelbergValue]
  exact le_trans hsmall huni_le

private lemma uniK5_depth3_well_connected
    (δ : ℚ) :
    GovGraph.rgTrajectory uniK5 sig5 δ 3 = (10, δ / 10) :=
  (concrete_iterated_RG_n5_parametric_bridge δ).1

section WellConnectedBridge

variable (G : GovGraph ℚ 5) (δ : ℚ)

private lemma bridge_data_in_well_connected_basin
    (hDepth3 : GovGraph.rgTrajectory G sig5 δ 3 = (10, δ / 10)) :
    (wellConnectedBridgeData δ G).spectralGraph ∈ wellConnectedBridgeBasinAt δ := by
  simpa [wellConnectedBridgeBasinAt, WellConnectedBasin, wellConnectedBridgeData,
    bridgeSpectralGraph, bridgeSignal] using hDepth3

private theorem edge01_selects_corrigibility :
    GovernanceSelectsCorrigibility
      (wellConnectedBridgeData δ G)
      (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
      (wellConnectedBridgeBasinAt δ) := by
  intro _ p S hReal hSupports
  constructor
  · simpa [wellConnectedBridgeAdversary] using hReal
  · cases p
    simpa [wellConnectedBridgeAdversary] using hSupports

private theorem kernel_preserves_well_connected_basin :
    KernelPreservesBasin
      (wellConnectedBridgeData δ G)
      (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
      (wellConnectedBridgeBasinAt δ) := by
  intro a S hReal
  simpa [wellConnectedBridgeAdversary, idActionSpace] using hReal

private theorem kernel_is_perturbation_free :
    KernelPerturbationFree
      (wellConnectedBridgeData δ G)
      (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G)) := by
  intro a S
  simp [wellConnectedBridgeAdversary, spectralDistance_self]

private theorem edge01_retune_bounded
    (hδ : 0 < δ) :
    JointStackelbergBounded
      (wellConnectedBridgeData δ G)
      (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
      [Sum.inr Edge01RetuneProposal.retune] := by
  constructor
  · intro a ha
    simp at ha
  · intro p hp
    simp at hp
    subst p
    constructor
    · have hcap_nonneg : 0 ≤ δ / 50 := by
        linarith
      simpa [wellConnectedBridgeAdversary, wellConnectedBridgeData] using hcap_nonneg
    · simpa [wellConnectedBridgeAdversary, wellConnectedBridgeData] using
        tolerance_div_fifty_le_stackelbergValue δ hδ

/-- Concrete discharge of the observational bridge for any `n = 5` graph whose
depth-3 RG trajectory lands in the well-connected basin at tolerance `δ`. -/
theorem well_connected_observational_corrigibility_bridge_at
    (hDepth3 : GovGraph.rgTrajectory G sig5 δ 3 = (10, δ / 10))
    (trajectory :
      List ((wellConnectedBridgeData δ G).actionSpace.Action ⊕
        (wellConnectedBridgeAdversary
          (wellConnectedBridgeData δ G)).Proposal)) :
    SupportsAlgebra
      (applyJointTrajectory
        (wellConnectedBridgeData δ G)
        (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
        trajectory fiveStagePermitSystem.state)
      (wellConnectedBridgeData δ G).algebra ∧
    (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G)).stateRealization
      (applyJointTrajectory
        (wellConnectedBridgeData δ G)
        (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
        trajectory fiveStagePermitSystem.state) ∈
      wellConnectedBridgeBasinAt δ := by
  exact observational_corrigibility_bridge
    (wellConnectedBridgeData δ G)
    (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
    (wellConnectedBridgeBasinAt δ)
    (bridge_data_in_well_connected_basin G δ hDepth3)
    (edge01_selects_corrigibility G δ)
    (by
      simpa [wellConnectedBridgeData, fiveStagePermitSystem] using
        permitState_supports_full_algebra)
    (idActionSpace_single_step_preserved fullSupervisoryAlgebra)
    (kernel_preserves_well_connected_basin G δ)
    trajectory

/-- Quantitative discharge of the observational bridge for any `n = 5` graph
whose depth-3 RG trajectory lands in the well-connected basin at tolerance
`δ`. The realized spectral perturbation is bounded by the accumulated
capability budget of the adversarial proposals in the trajectory. -/
theorem well_connected_observational_corrigibility_bridge_quantitative_at
    (hDepth3 : GovGraph.rgTrajectory G sig5 δ 3 = (10, δ / 10))
    (trajectory :
      List ((wellConnectedBridgeData δ G).actionSpace.Action ⊕
        (wellConnectedBridgeAdversary
          (wellConnectedBridgeData δ G)).Proposal)) :
    SupportsAlgebra
      (applyJointTrajectory
        (wellConnectedBridgeData δ G)
        (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
        trajectory fiveStagePermitSystem.state)
      (wellConnectedBridgeData δ G).algebra ∧
    (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G)).stateRealization
      (applyJointTrajectory
        (wellConnectedBridgeData δ G)
        (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
        trajectory fiveStagePermitSystem.state) ∈
      wellConnectedBridgeBasinAt δ ∧
    spectralDistance
      ((wellConnectedBridgeAdversary
          (wellConnectedBridgeData δ G)).stateRealization
        fiveStagePermitSystem.state)
      ((wellConnectedBridgeAdversary
          (wellConnectedBridgeData δ G)).stateRealization
        (applyJointTrajectory
          (wellConnectedBridgeData δ G)
          (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
          trajectory fiveStagePermitSystem.state)) ≤
      trajectoryPerturbationBound
        (wellConnectedBridgeData δ G)
        (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
        trajectory := by
  exact observational_corrigibility_bridge_quantitative
    (wellConnectedBridgeData δ G)
    (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
    (wellConnectedBridgeBasinAt δ)
    (bridge_data_in_well_connected_basin G δ hDepth3)
    (edge01_selects_corrigibility G δ)
    (by
      simpa [wellConnectedBridgeData, fiveStagePermitSystem] using
        permitState_supports_full_algebra)
    (idActionSpace_single_step_preserved fullSupervisoryAlgebra)
    (kernel_preserves_well_connected_basin G δ)
    (kernel_is_perturbation_free G δ)
    trajectory

/-- The inert edge-retuning adversary stays within the Stackelberg envelope on
the shared one-step trajectory at tolerance `δ`. -/
theorem well_connected_single_retune_preserves_corrigibility_at
    (hDepth3 : GovGraph.rgTrajectory G sig5 δ 3 = (10, δ / 10)) :
    SupportsAlgebra
      (applyJointTrajectory
        (wellConnectedBridgeData δ G)
        (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
        [Sum.inr Edge01RetuneProposal.retune]
        fiveStagePermitSystem.state)
      (wellConnectedBridgeData δ G).algebra ∧
      (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G)).stateRealization
      (applyJointTrajectory
        (wellConnectedBridgeData δ G)
        (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
        [Sum.inr Edge01RetuneProposal.retune]
        fiveStagePermitSystem.state) ∈
      wellConnectedBridgeBasinAt δ := by
  exact well_connected_observational_corrigibility_bridge_at G δ hDepth3
    [Sum.inr Edge01RetuneProposal.retune]

/-- Quantitative one-step well-connected witness: the retuning proposal keeps
the state in the basin, preserves the supervisory algebra, and incurs no
realized spectral perturbation beyond its declared capability budget. -/
theorem well_connected_single_retune_preserves_corrigibility_quantitative_at
    (hDepth3 : GovGraph.rgTrajectory G sig5 δ 3 = (10, δ / 10)) :
    SupportsAlgebra
      (applyJointTrajectory
        (wellConnectedBridgeData δ G)
        (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
        [Sum.inr Edge01RetuneProposal.retune]
        fiveStagePermitSystem.state)
      (wellConnectedBridgeData δ G).algebra ∧
    (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G)).stateRealization
      (applyJointTrajectory
        (wellConnectedBridgeData δ G)
        (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
        [Sum.inr Edge01RetuneProposal.retune]
        fiveStagePermitSystem.state) ∈
      wellConnectedBridgeBasinAt δ ∧
    spectralDistance
      ((wellConnectedBridgeAdversary
          (wellConnectedBridgeData δ G)).stateRealization
        fiveStagePermitSystem.state)
      ((wellConnectedBridgeAdversary
          (wellConnectedBridgeData δ G)).stateRealization
        (applyJointTrajectory
          (wellConnectedBridgeData δ G)
          (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
          [Sum.inr Edge01RetuneProposal.retune]
          fiveStagePermitSystem.state)) ≤
      trajectoryPerturbationBound
        (wellConnectedBridgeData δ G)
        (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
        [Sum.inr Edge01RetuneProposal.retune] := by
  exact well_connected_observational_corrigibility_bridge_quantitative_at G δ
    hDepth3 [Sum.inr Edge01RetuneProposal.retune]

end WellConnectedBridge

/-- `uniK5` lies in the shared well-connected basin at depth `3`. -/
theorem uniK5_bridge_data_in_well_connected_basin :
    uniK5BridgeData.spectralGraph ∈ wellConnectedBridgeBasin := by
  exact bridge_data_in_well_connected_basin uniK5 (1 / 10)
    (uniK5_depth3_well_connected (1 / 10))

/-- The shared inert retuning adversary satisfies the corrigibility-side bridge
hypothesis on the `uniK5` witness. -/
theorem uniK5_edge01_selects_corrigibility :
    GovernanceSelectsCorrigibility
      uniK5BridgeData uniK5Edge01Adversary wellConnectedBridgeBasin := by
  simpa [uniK5BridgeData, wellConnectedBridgeBasin] using
    (edge01_selects_corrigibility uniK5 (1 / 10))

/-- Bundled kernel actions preserve well-connected basin membership on the
`uniK5` bridge datum. -/
theorem uniK5_kernel_preserves_well_connected_basin :
    KernelPreservesBasin
      uniK5BridgeData uniK5Edge01Adversary wellConnectedBridgeBasin := by
  simpa [uniK5BridgeData, wellConnectedBridgeBasin] using
    (kernel_preserves_well_connected_basin uniK5 (1 / 10))

/-- The shared inert retuning trajectory is Stackelberg-bounded on `uniK5`. -/
theorem uniK5_edge01_retune_bounded :
    JointStackelbergBounded
      uniK5BridgeData
      uniK5Edge01Adversary
      [Sum.inr Edge01RetuneProposal.retune] := by
  simpa [uniK5BridgeData] using
    (edge01_retune_bounded uniK5 (1 / 10) (by norm_num))

end Legitimacy
