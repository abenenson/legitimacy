/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Results.UnbundledCorrigibilityBridge
import Legitimacy.Results.BottleneckBridgeRefutation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The basin classification is the ASI-safety classification

The un-bundled corrigibility bridge from
`Legitimacy.Protocol.ObservationalBridge` has concrete discharges on every
well-connected-basin representative in the `n = 5` verification lattice
(`Legitimacy.Results.UnbundledCorrigibilityBridge`) and a concrete refutation
on the topologically asymmetric representative `bottleneck5`
(`Legitimacy.Results.BottleneckBridgeRefutation`).

This file composes those witnesses into the headline finite-lattice
biconditional: on the `n = 5` verification lattice, the concrete un-bundled
corrigibility bridge discharges exactly for the graphs in the well-connected
basin, uniformly for every positive tolerance parameter `δ`.
-/

set_option autoImplicit false

namespace Legitimacy

/-- The concrete `n = 5` verification lattice. -/
def n5Lattice : Set (GovGraph ℚ 5) :=
  {G | G = uniK5 ∨ G = asymK5 ∨ G = nearPath5 ∨ G = wheel5 ∨ G = bottleneck5}

private def wellConnectedBridgeStatementAt
    (G : GovGraph ℚ 5) (δ : ℚ) : Prop :=
  ∀ trajectory :
      List ((wellConnectedBridgeData δ G).actionSpace.Action ⊕
        (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G)).Proposal),
      SupportsAlgebra
        (applyJointTrajectory
          (wellConnectedBridgeData δ G)
          (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
          trajectory
          fiveStagePermitSystem.state)
        (wellConnectedBridgeData δ G).algebra ∧
      (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G)).stateRealization
          (applyJointTrajectory
            (wellConnectedBridgeData δ G)
            (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
            trajectory
            fiveStagePermitSystem.state) ∈
        wellConnectedBridgeBasinAt δ

private def bottleneckBridgeStatementAt (δ : ℚ) : Prop :=
  ∀ trajectory :
      List ((bottleneck5BridgeDataAt δ).actionSpace.Action ⊕
        (bottleneck5RerouteAdversaryAt δ).Proposal),
    JointStackelbergBounded
      (bottleneck5BridgeDataAt δ)
      (bottleneck5RerouteAdversaryAt δ)
      trajectory →
      SupportsAlgebra
        (applyJointTrajectory
          (bottleneck5BridgeDataAt δ)
          (bottleneck5RerouteAdversaryAt δ)
          trajectory
          fiveStagePermitSystem.state)
        (bottleneck5BridgeDataAt δ).algebra ∧
      (bottleneck5RerouteAdversaryAt δ).stateRealization
          (applyJointTrajectory
            (bottleneck5BridgeDataAt δ)
            (bottleneck5RerouteAdversaryAt δ)
            trajectory
            fiveStagePermitSystem.state) ∈
        bottleneck5AsymmetricBasinAt δ

private def wellConnectedQuantitativeBridgeStatementAt
    (G : GovGraph ℚ 5) (δ : ℚ) : Prop :=
  ∀ trajectory :
      List ((wellConnectedBridgeData δ G).actionSpace.Action ⊕
        (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G)).Proposal),
      SupportsAlgebra
        (applyJointTrajectory
          (wellConnectedBridgeData δ G)
          (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
          trajectory
          fiveStagePermitSystem.state)
        (wellConnectedBridgeData δ G).algebra ∧
      (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G)).stateRealization
          (applyJointTrajectory
            (wellConnectedBridgeData δ G)
            (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
            trajectory
            fiveStagePermitSystem.state) ∈
        wellConnectedBridgeBasinAt δ ∧
      spectralDistance
        ((wellConnectedBridgeAdversary (wellConnectedBridgeData δ G)).stateRealization
          fiveStagePermitSystem.state)
        ((wellConnectedBridgeAdversary (wellConnectedBridgeData δ G)).stateRealization
          (applyJointTrajectory
            (wellConnectedBridgeData δ G)
            (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
            trajectory
            fiveStagePermitSystem.state)) ≤
        trajectoryPerturbationBound
          (wellConnectedBridgeData δ G)
          (wellConnectedBridgeAdversary (wellConnectedBridgeData δ G))
          trajectory

private def bottleneckQuantitativeBridgeStatementAt (δ : ℚ) : Prop :=
  ∀ trajectory :
      List ((bottleneck5BridgeDataAt δ).actionSpace.Action ⊕
        (bottleneck5RerouteAdversaryAt δ).Proposal),
    JointStackelbergBounded
      (bottleneck5BridgeDataAt δ)
      (bottleneck5RerouteAdversaryAt δ)
      trajectory →
      SupportsAlgebra
        (applyJointTrajectory
          (bottleneck5BridgeDataAt δ)
          (bottleneck5RerouteAdversaryAt δ)
          trajectory
          fiveStagePermitSystem.state)
        (bottleneck5BridgeDataAt δ).algebra ∧
      (bottleneck5RerouteAdversaryAt δ).stateRealization
          (applyJointTrajectory
            (bottleneck5BridgeDataAt δ)
            (bottleneck5RerouteAdversaryAt δ)
            trajectory
            fiveStagePermitSystem.state) ∈
        bottleneck5AsymmetricBasinAt δ ∧
      spectralDistance
        ((bottleneck5RerouteAdversaryAt δ).stateRealization
          fiveStagePermitSystem.state)
        ((bottleneck5RerouteAdversaryAt δ).stateRealization
          (applyJointTrajectory
            (bottleneck5BridgeDataAt δ)
            (bottleneck5RerouteAdversaryAt δ)
            trajectory
            fiveStagePermitSystem.state)) ≤
        trajectoryPerturbationBound
          (bottleneck5BridgeDataAt δ)
          (bottleneck5RerouteAdversaryAt δ)
          trajectory

/-- `BridgeDischargesAt G δ` packages the concrete un-bundled bridge statement
for the `n = 5` representative named by `G` at tolerance `δ`. The four
well-connected representatives use the shared well-connected bridge witness,
while `bottleneck5` uses the concrete asymmetric-basin datum from the
refutation. -/
noncomputable def BridgeDischargesAt
    (G : GovGraph ℚ 5) (δ : ℚ) : Prop :=
  by
    classical
    exact
      if G = bottleneck5 then
        bottleneckBridgeStatementAt δ
      else
        wellConnectedBridgeStatementAt G δ

/-- Bridge-discharge predicate specialized to tolerance `1 / 10`. -/
noncomputable def BridgeDischarges (G : GovGraph ℚ 5) : Prop :=
  BridgeDischargesAt G (1 / 10)

/-- Quantitative companion to `BridgeDischargesAt`: the bridge preserves both
the supervisory algebra and a trajectory-indexed spectral perturbation budget. -/
noncomputable def QuantitativeBridgeDischargesAt
    (G : GovGraph ℚ 5) (δ : ℚ) : Prop :=
  by
    classical
    exact
      if G = bottleneck5 then
        bottleneckQuantitativeBridgeStatementAt δ
      else
        wellConnectedQuantitativeBridgeStatementAt G δ

/-- Quantitative bridge discharge specialized to tolerance `1 / 10`. -/
noncomputable def QuantitativeBridgeDischarges (G : GovGraph ℚ 5) : Prop :=
  QuantitativeBridgeDischargesAt G (1 / 10)

private lemma uniK5_depth3_well_connected
    (δ : ℚ) :
    GovGraph.rgTrajectory uniK5 sig5 δ 3 = (10, δ / 10) :=
  (concrete_iterated_RG_n5_parametric_bridge δ).1

private lemma asymK5_depth3_well_connected
    (δ : ℚ) :
    GovGraph.rgTrajectory asymK5 sig5 δ 3 = (10, δ / 10) :=
  (concrete_iterated_RG_n5_parametric_bridge δ).2.1

private lemma nearPath5_depth3_well_connected
    (δ : ℚ) :
    GovGraph.rgTrajectory nearPath5 sig5 δ 3 = (10, δ / 10) :=
  (concrete_iterated_RG_n5_parametric_bridge δ).2.2.1

private lemma bottleneck5_depth3_asymmetric
    (δ : ℚ) :
    GovGraph.rgTrajectory bottleneck5 sig5 δ 3 = (9, δ / 9) :=
  (concrete_iterated_RG_n5_parametric_bridge δ).2.2.2.1

private lemma wheel5_depth3_well_connected
    (δ : ℚ) :
    GovGraph.rgTrajectory wheel5 sig5 δ 3 = (10, δ / 10) :=
  (concrete_iterated_RG_n5_parametric_bridge δ).2.2.2.2

private lemma ne_bottleneck5_of_depth3
    (G : GovGraph ℚ 5)
    (δ : ℚ)
    (hDepth3 : GovGraph.rgTrajectory G sig5 δ 3 = (10, δ / 10)) :
    G ≠ bottleneck5 := by
  intro hEq
  rw [hEq] at hDepth3
  have h10 :
      (GovGraph.rgTrajectory bottleneck5 sig5 δ 3).1 = (10 : ℚ) := by
    simpa using congrArg Prod.fst hDepth3
  have h9 :
      (GovGraph.rgTrajectory bottleneck5 sig5 δ 3).1 = (9 : ℚ) := by
    simpa using congrArg Prod.fst (bottleneck5_depth3_asymmetric δ)
  linarith

private theorem wellConnectedBridgeStatement_of_depth3
    (G : GovGraph ℚ 5)
    (δ : ℚ)
    (hDepth3 : GovGraph.rgTrajectory G sig5 δ 3 = (10, δ / 10)) :
    wellConnectedBridgeStatementAt G δ := by
  intro trajectory
  exact well_connected_observational_corrigibility_bridge_at G δ hDepth3 trajectory

private theorem wellConnectedQuantitativeBridgeStatement_of_depth3
    (G : GovGraph ℚ 5)
    (δ : ℚ)
    (hDepth3 : GovGraph.rgTrajectory G sig5 δ 3 = (10, δ / 10)) :
    wellConnectedQuantitativeBridgeStatementAt G δ := by
  intro trajectory
  exact
    well_connected_observational_corrigibility_bridge_quantitative_at G δ
      hDepth3 trajectory

private theorem bottleneckBridgeStatement_false
    (δ : ℚ) (hδ : 0 < δ) :
    ¬ bottleneckBridgeStatementAt δ := by
  intro hDischarges
  have hWitness :=
    hDischarges
      [Sum.inr RerouteEraseProposal.eraseReroute]
      (bottleneck5_reroute_erase_bounded_at δ hδ)
  exact (bottleneck5_single_reroute_erase_breaks_corrigibility_at δ).1 hWitness.1

private theorem bottleneckQuantitativeBridgeStatement_false
    (δ : ℚ) (hδ : 0 < δ) :
    ¬ bottleneckQuantitativeBridgeStatementAt δ := by
  intro hDischarges
  have hWitness :=
    hDischarges
      [Sum.inr RerouteEraseProposal.eraseReroute]
      (bottleneck5_reroute_erase_bounded_at δ hδ)
  exact (bottleneck5_single_reroute_erase_breaks_corrigibility_at δ).1 hWitness.1

private theorem mem_wellConnectedBridgeBasinAt_of_depth3
    (G : GovGraph ℚ 5)
    (δ : ℚ)
    (hDepth3 : GovGraph.rgTrajectory G sig5 δ 3 = (10, δ / 10)) :
    G ∈ wellConnectedBridgeBasinAt δ := by
  simpa [wellConnectedBridgeBasinAt, WellConnectedBasin] using
    hDepth3

private theorem mem_wellConnectedBridgeBasin_of_depth3
    (G : GovGraph ℚ 5)
    (hDepth3 : GovGraph.rgTrajectory G sig5 (1 / 10) 3 = (10, (1 / 10) / 10)) :
    G ∈ wellConnectedBridgeBasin := by
  simpa [wellConnectedBridgeBasin, wellConnectedBridgeBasinAt, WellConnectedBasin] using
    hDepth3

private theorem bottleneck5_not_mem_wellConnectedBridgeBasinAt
    (δ : ℚ) :
    bottleneck5 ∉ wellConnectedBridgeBasinAt δ := by
  intro hBasin
  have hWellConnected :
      GovGraph.rgTrajectory bottleneck5 sig5 δ 3 = (10, δ / 10) := by
    simpa [wellConnectedBridgeBasinAt, WellConnectedBasin] using hBasin
  have hAsymmetric := bottleneck5_depth3_asymmetric δ
  have h10 :
      (GovGraph.rgTrajectory bottleneck5 sig5 δ 3).1 = (10 : ℚ) := by
    simpa using congrArg Prod.fst hWellConnected
  have h9 :
      (GovGraph.rgTrajectory bottleneck5 sig5 δ 3).1 = (9 : ℚ) := by
    simpa using congrArg Prod.fst hAsymmetric
  linarith

/-- On the `n = 5` verification lattice, well-connected basin membership is
independent of the tolerance parameter. -/
theorem well_connected_bridge_basin_scale_invariant_on_n5
    (G : GovGraph ℚ 5) (hLattice : G ∈ n5Lattice) (δ : ℚ) :
    G ∈ wellConnectedBridgeBasinAt δ ↔ G ∈ wellConnectedBridgeBasin := by
  rcases hLattice with rfl | rfl | rfl | rfl | rfl
  · constructor
    · intro _
      exact mem_wellConnectedBridgeBasin_of_depth3 uniK5
        (uniK5_depth3_well_connected (1 / 10))
    · intro _
      exact mem_wellConnectedBridgeBasinAt_of_depth3 uniK5 δ
        (uniK5_depth3_well_connected δ)
  · constructor
    · intro _
      exact mem_wellConnectedBridgeBasin_of_depth3 asymK5
        (asymK5_depth3_well_connected (1 / 10))
    · intro _
      exact mem_wellConnectedBridgeBasinAt_of_depth3 asymK5 δ
        (asymK5_depth3_well_connected δ)
  · constructor
    · intro _
      exact mem_wellConnectedBridgeBasin_of_depth3 nearPath5
        (nearPath5_depth3_well_connected (1 / 10))
    · intro _
      exact mem_wellConnectedBridgeBasinAt_of_depth3 nearPath5 δ
        (nearPath5_depth3_well_connected δ)
  · constructor
    · intro _
      exact mem_wellConnectedBridgeBasin_of_depth3 wheel5
        (wheel5_depth3_well_connected (1 / 10))
    · intro _
      exact mem_wellConnectedBridgeBasinAt_of_depth3 wheel5 δ
        (wheel5_depth3_well_connected δ)
  · constructor
    · exact fun h => False.elim (bottleneck5_not_mem_wellConnectedBridgeBasinAt δ h)
    · exact fun h =>
        False.elim (bottleneck5_not_mem_wellConnectedBridgeBasinAt (1 / 10) h)

/-- On the `n = 5` verification lattice, the concrete un-bundled
corrigibility bridge discharges exactly for the well-connected basin
representatives at every positive tolerance `δ`. -/
theorem n5_bridge_discharges_iff_well_connected_basin_parametric
    (G : GovGraph ℚ 5) (hLattice : G ∈ n5Lattice) (δ : ℚ) (hδ : 0 < δ) :
    BridgeDischargesAt G δ ↔ G ∈ wellConnectedBridgeBasinAt δ := by
  classical
  rcases hLattice with rfl | rfl | rfl | rfl | rfl
  · constructor
    · intro _
      exact mem_wellConnectedBridgeBasinAt_of_depth3 uniK5 δ
        (uniK5_depth3_well_connected δ)
    · intro _
      simpa [BridgeDischargesAt,
        ne_bottleneck5_of_depth3 uniK5 δ (uniK5_depth3_well_connected δ)] using
        wellConnectedBridgeStatement_of_depth3 uniK5 δ
          (uniK5_depth3_well_connected δ)
  · constructor
    · intro _
      exact mem_wellConnectedBridgeBasinAt_of_depth3 asymK5 δ
        (asymK5_depth3_well_connected δ)
    · intro _
      simpa [BridgeDischargesAt,
        ne_bottleneck5_of_depth3 asymK5 δ (asymK5_depth3_well_connected δ)] using
        wellConnectedBridgeStatement_of_depth3 asymK5 δ
          (asymK5_depth3_well_connected δ)
  · constructor
    · intro _
      exact mem_wellConnectedBridgeBasinAt_of_depth3 nearPath5 δ
        (nearPath5_depth3_well_connected δ)
    · intro _
      simpa [BridgeDischargesAt,
        ne_bottleneck5_of_depth3 nearPath5 δ (nearPath5_depth3_well_connected δ)] using
        wellConnectedBridgeStatement_of_depth3 nearPath5 δ
          (nearPath5_depth3_well_connected δ)
  · constructor
    · intro _
      exact mem_wellConnectedBridgeBasinAt_of_depth3 wheel5 δ
        (wheel5_depth3_well_connected δ)
    · intro _
      simpa [BridgeDischargesAt,
        ne_bottleneck5_of_depth3 wheel5 δ (wheel5_depth3_well_connected δ)] using
        wellConnectedBridgeStatement_of_depth3 wheel5 δ
          (wheel5_depth3_well_connected δ)
  · constructor
    · intro hDischarges
      have hBridge : bottleneckBridgeStatementAt δ := by
        simpa [BridgeDischargesAt] using hDischarges
      exact False.elim (bottleneckBridgeStatement_false δ hδ hBridge)
    · intro hBasin
      exact False.elim (bottleneck5_not_mem_wellConnectedBridgeBasinAt δ hBasin)

/-- On the `n = 5` verification lattice, the quantitative un-bundled
corrigibility bridge discharges exactly for the well-connected basin
representatives at every positive tolerance `δ`. The quantitative witness is
the trajectory-indexed perturbation budget from the observational bridge. -/
theorem n5_quantitative_bridge_discharges_iff_well_connected_basin_parametric
    (G : GovGraph ℚ 5) (hLattice : G ∈ n5Lattice) (δ : ℚ) (hδ : 0 < δ) :
    QuantitativeBridgeDischargesAt G δ ↔ G ∈ wellConnectedBridgeBasinAt δ := by
  classical
  rcases hLattice with rfl | rfl | rfl | rfl | rfl
  · constructor
    · intro _
      exact mem_wellConnectedBridgeBasinAt_of_depth3 uniK5 δ
        (uniK5_depth3_well_connected δ)
    · intro _
      simpa [QuantitativeBridgeDischargesAt,
        ne_bottleneck5_of_depth3 uniK5 δ (uniK5_depth3_well_connected δ)] using
        wellConnectedQuantitativeBridgeStatement_of_depth3 uniK5 δ
          (uniK5_depth3_well_connected δ)
  · constructor
    · intro _
      exact mem_wellConnectedBridgeBasinAt_of_depth3 asymK5 δ
        (asymK5_depth3_well_connected δ)
    · intro _
      simpa [QuantitativeBridgeDischargesAt,
        ne_bottleneck5_of_depth3 asymK5 δ (asymK5_depth3_well_connected δ)] using
        wellConnectedQuantitativeBridgeStatement_of_depth3 asymK5 δ
          (asymK5_depth3_well_connected δ)
  · constructor
    · intro _
      exact mem_wellConnectedBridgeBasinAt_of_depth3 nearPath5 δ
        (nearPath5_depth3_well_connected δ)
    · intro _
      simpa [QuantitativeBridgeDischargesAt,
        ne_bottleneck5_of_depth3 nearPath5 δ
          (nearPath5_depth3_well_connected δ)] using
        wellConnectedQuantitativeBridgeStatement_of_depth3 nearPath5 δ
          (nearPath5_depth3_well_connected δ)
  · constructor
    · intro _
      exact mem_wellConnectedBridgeBasinAt_of_depth3 wheel5 δ
        (wheel5_depth3_well_connected δ)
    · intro _
      simpa [QuantitativeBridgeDischargesAt,
        ne_bottleneck5_of_depth3 wheel5 δ (wheel5_depth3_well_connected δ)] using
        wellConnectedQuantitativeBridgeStatement_of_depth3 wheel5 δ
          (wheel5_depth3_well_connected δ)
  · constructor
    · intro hDischarges
      have hBridge : bottleneckQuantitativeBridgeStatementAt δ := by
        simpa [QuantitativeBridgeDischargesAt] using hDischarges
      exact False.elim (bottleneckQuantitativeBridgeStatement_false δ hδ hBridge)
    · intro hBasin
      exact False.elim (bottleneck5_not_mem_wellConnectedBridgeBasinAt δ hBasin)

/-- On the `n = 5` verification lattice, the `δ = 1 / 10`
bridge-discharge theorem is the specialization of the parametric
classification. -/
theorem n5_bridge_discharges_iff_well_connected_basin
    (G : GovGraph ℚ 5) (hLattice : G ∈ n5Lattice) :
    BridgeDischarges G ↔ G ∈ wellConnectedBridgeBasin := by
  simpa [BridgeDischarges, wellConnectedBridgeBasin] using
    n5_bridge_discharges_iff_well_connected_basin_parametric
      G hLattice (1 / 10) (by norm_num)

/-- Specialization of the quantitative bridge-classification theorem at
`δ = 1 / 10`. -/
theorem n5_quantitative_bridge_discharges_iff_well_connected_basin
    (G : GovGraph ℚ 5) (hLattice : G ∈ n5Lattice) :
    QuantitativeBridgeDischarges G ↔ G ∈ wellConnectedBridgeBasin := by
  simpa [QuantitativeBridgeDischarges, wellConnectedBridgeBasin] using
    n5_quantitative_bridge_discharges_iff_well_connected_basin_parametric
      G hLattice (1 / 10) (by norm_num)

end Legitimacy
