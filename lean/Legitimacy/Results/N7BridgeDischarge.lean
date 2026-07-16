/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.N7Bridge

/-!
# Legitimacy.Results.N7BridgeDischarge

Finite-lattice classification and bridge-discharge equivalence for the
experimental `n = 7` depth-3 robust basin.
-/

set_option autoImplicit false

namespace Legitimacy

/-- `BridgeDischargesAt7 G δ` packages the concrete unbundled bridge statement
for the `n = 7` representative named by `G` at tolerance `δ`. -/
noncomputable def BridgeDischargesAt7
    (G : GovGraph ℚ 7) (δ : ℚ) : Prop :=
  ∀ trajectory :
      List ((n7BridgeData δ G).actionSpace.Action ⊕
        (n7BridgeAdversary (n7BridgeData δ G)).Proposal),
      SupportsAlgebra
        (applyJointTrajectory
          (n7BridgeData δ G)
          (n7BridgeAdversary (n7BridgeData δ G))
          trajectory
          sevenStagePermitSystem.state)
        (n7BridgeData δ G).algebra ∧
      (n7BridgeAdversary (n7BridgeData δ G)).stateRealization
          (applyJointTrajectory
            (n7BridgeData δ G)
            (n7BridgeAdversary (n7BridgeData δ G))
            trajectory
            sevenStagePermitSystem.state) ∈
        Depth3RobustBasin7At δ

private theorem bridgeDischargesAt7_of_mem_depth3_robust_basin
    (G : GovGraph ℚ 7) (δ : ℚ)
    (hBasin : G ∈ Depth3RobustBasin7At δ) :
    BridgeDischargesAt7 G δ := by
  intro trajectory
  exact depth3_robust_observational_corrigibility_bridge_at G δ hBasin
    trajectory

private theorem mem_depth3_robust_basin_of_bridgeDischargesAt7
    (G : GovGraph ℚ 7) (δ : ℚ)
    (hDischarges : BridgeDischargesAt7 G δ) :
    G ∈ Depth3RobustBasin7At δ := by
  have hWitness := hDischarges []
  simpa [applyJointTrajectory, n7BridgeAdversary, n7BridgeData, bridgeSpectralGraph] using
    hWitness.2

/-- On the `n = 7` verification lattice, the honest depth-3 robust basin is
exactly the set of the five non-bottleneck witnesses. -/
theorem Depth3RobustBasin7At_n7_lattice_classification
    (G : GovGraph ℚ 7) (hLattice : G ∈ n7Lattice) (δ : ℚ) :
    G ∈ Depth3RobustBasin7At δ ↔
      G = uniK7 ∨ G = asymK7 ∨ G = nearPath7 ∨
        G = hubSpokeHierarchy7 ∨ G = nestedHierarchy7 := by
  rcases hLattice with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [uniK7_mem_Depth3RobustBasin7At]
  · simp [asymK7_mem_Depth3RobustBasin7At]
  · simp [nearPath7_mem_Depth3RobustBasin7At]
  · simp [hubSpokeHierarchy7_mem_Depth3RobustBasin7At]
  · simp [nestedHierarchy7_mem_Depth3RobustBasin7At]
  · constructor
    · intro hBasin
      exact False.elim (bottleneck7_bi_not_mem_Depth3RobustBasin7At δ hBasin)
    · intro hGood
      rcases hGood with hEq | hEq | hEq | hEq | hEq
      · simpa [hEq] using uniK7_mem_Depth3RobustBasin7At δ
      · simpa [hEq] using asymK7_mem_Depth3RobustBasin7At δ
      · simpa [hEq] using nearPath7_mem_Depth3RobustBasin7At δ
      · simpa [hEq] using hubSpokeHierarchy7_mem_Depth3RobustBasin7At δ
      · simpa [hEq] using nestedHierarchy7_mem_Depth3RobustBasin7At δ
  · constructor
    · intro hBasin
      exact False.elim (bottleneck7_tri_not_mem_Depth3RobustBasin7At δ hBasin)
    · intro hGood
      rcases hGood with hEq | hEq | hEq | hEq | hEq
      · simpa [hEq] using uniK7_mem_Depth3RobustBasin7At δ
      · simpa [hEq] using asymK7_mem_Depth3RobustBasin7At δ
      · simpa [hEq] using nearPath7_mem_Depth3RobustBasin7At δ
      · simpa [hEq] using hubSpokeHierarchy7_mem_Depth3RobustBasin7At δ
      · simpa [hEq] using nestedHierarchy7_mem_Depth3RobustBasin7At δ

/-- Basin membership is equivalent to bridge discharge for the `n = 7`
unbundled observational bridge. -/
theorem n7_bridge_discharges_iff_depth3_robust_basin
    (G : GovGraph ℚ 7) (δ : ℚ) :
    BridgeDischargesAt7 G δ ↔ G ∈ Depth3RobustBasin7At δ := by
  constructor
  · exact mem_depth3_robust_basin_of_bridgeDischargesAt7 G δ
  · exact bridgeDischargesAt7_of_mem_depth3_robust_basin G δ

end Legitimacy
