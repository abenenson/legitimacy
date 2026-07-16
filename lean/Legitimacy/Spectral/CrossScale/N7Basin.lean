/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.RGFlow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Legitimacy.Spectral.CrossScale.N7Basin

Concrete depth-3 robustness basin facts for the experimental `n = 7`
verification lattice.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Honest `n = 7` basin: depth-3 coarse robustness above the weakest
non-bottleneck witness on the current seven-graph lattice. -/
def Depth3RobustBasin7At (δ : ℚ) : Set (GovGraph ℚ 7) :=
  {G | (30 / 11 : ℚ) ≤ (GovGraph.rgTrajectory G sig7 δ 3).1}

/-- `Depth3RobustBasin7At` specialized to tolerance `1 / 10`. -/
def Depth3RobustBasin7 : Set (GovGraph ℚ 7) :=
  Depth3RobustBasin7At (1 / 10)

/-- The concrete `n = 7` verification lattice. -/
def n7Lattice : Set (GovGraph ℚ 7) :=
  {G | G = uniK7 ∨ G = asymK7 ∨ G = nearPath7 ∨ G = hubSpokeHierarchy7 ∨
      G = nestedHierarchy7 ∨ G = bottleneck7_bi ∨ G = bottleneck7_tri}

/-- The first coordinate of the RG trajectory is independent of the tolerance
parameter. Only the critical-capability coordinate rescales with `δ`. -/
private lemma rgTrajectory_fst_eq {n : ℕ}
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (δ₁ δ₂ : ℚ) (k : ℕ) :
    (GovGraph.rgTrajectory G s δ₁ k).1 =
      (GovGraph.rgTrajectory G s δ₂ k).1 := by
  unfold GovGraph.rgTrajectory
  cases h : GovGraph.rgStateAt G s k with
  | mk m pair =>
      cases pair
      rfl

private lemma depth3_fst_eq_of_concrete
    (G : GovGraph ℚ 7) (c : ℚ)
    (hConcrete : (GovGraph.rgTrajectory G sig7 (1 / 10) 3).1 = c)
    (δ : ℚ) :
    (GovGraph.rgTrajectory G sig7 δ 3).1 = c := by
  calc
    (GovGraph.rgTrajectory G sig7 δ 3).1
        = (GovGraph.rgTrajectory G sig7 (1 / 10) 3).1 :=
          rgTrajectory_fst_eq G sig7 δ (1 / 10) 3
    _ = c := by
      exact hConcrete

private lemma uniK7_depth3_cv_concrete :
    GovGraph.rgTrajectory uniK7 sig7 (1 / 10) 3 = (3, 1 / 30) := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  native_decide

private lemma asymK7_depth3_cv_concrete :
    GovGraph.rgTrajectory asymK7 sig7 (1 / 10) 3 = (3, 1 / 30) := by
  native_decide

private lemma nearPath7_depth3_cv_concrete :
    GovGraph.rgTrajectory nearPath7 sig7 (1 / 10) 3 = (30 / 11, 11 / 300) := by
  native_decide

private lemma hubSpokeHierarchy7_depth3_cv_concrete :
    GovGraph.rgTrajectory hubSpokeHierarchy7 sig7 (1 / 10) 3 = (10, 1 / 100) := by
  native_decide

private lemma nestedHierarchy7_depth3_cv_concrete :
    GovGraph.rgTrajectory nestedHierarchy7 sig7 (1 / 10) 3 = (77 / 24, 12 / 385) := by
  native_decide

private lemma bottleneck7_bi_depth3_cv_concrete :
    GovGraph.rgTrajectory bottleneck7_bi sig7 (1 / 10) 3 =
      (140000 / 70001, 70001 / 1400000) := by
  native_decide

private lemma bottleneck7_tri_depth3_cv_concrete :
    GovGraph.rgTrajectory bottleneck7_tri sig7 (1 / 10) 3 =
      (5 / 4, 2 / 25) := by
  native_decide

theorem uniK7_depth3_cv (δ : ℚ) :
    (GovGraph.rgTrajectory uniK7 sig7 δ 3).1 = 3 :=
  depth3_fst_eq_of_concrete uniK7 3
    (by simpa using congrArg Prod.fst uniK7_depth3_cv_concrete) δ

theorem asymK7_depth3_cv (δ : ℚ) :
    (GovGraph.rgTrajectory asymK7 sig7 δ 3).1 = 3 :=
  depth3_fst_eq_of_concrete asymK7 3
    (by simpa using congrArg Prod.fst asymK7_depth3_cv_concrete) δ

theorem nearPath7_depth3_cv (δ : ℚ) :
    (GovGraph.rgTrajectory nearPath7 sig7 δ 3).1 = 30 / 11 :=
  depth3_fst_eq_of_concrete nearPath7 (30 / 11)
    (by simpa using congrArg Prod.fst nearPath7_depth3_cv_concrete) δ

theorem hubSpokeHierarchy7_depth3_cv (δ : ℚ) :
    (GovGraph.rgTrajectory hubSpokeHierarchy7 sig7 δ 3).1 = 10 :=
  depth3_fst_eq_of_concrete hubSpokeHierarchy7 10
    (by simpa using congrArg Prod.fst hubSpokeHierarchy7_depth3_cv_concrete) δ

theorem nestedHierarchy7_depth3_cv (δ : ℚ) :
    (GovGraph.rgTrajectory nestedHierarchy7 sig7 δ 3).1 = 77 / 24 :=
  depth3_fst_eq_of_concrete nestedHierarchy7 (77 / 24)
    (by simpa using congrArg Prod.fst nestedHierarchy7_depth3_cv_concrete) δ

theorem bottleneck7_bi_depth3_cv (δ : ℚ) :
    (GovGraph.rgTrajectory bottleneck7_bi sig7 δ 3).1 = 140000 / 70001 :=
  depth3_fst_eq_of_concrete bottleneck7_bi (140000 / 70001)
    (by simpa using congrArg Prod.fst bottleneck7_bi_depth3_cv_concrete) δ

theorem bottleneck7_tri_depth3_cv (δ : ℚ) :
    (GovGraph.rgTrajectory bottleneck7_tri sig7 δ 3).1 = 5 / 4 :=
  depth3_fst_eq_of_concrete bottleneck7_tri (5 / 4)
    (by simpa using congrArg Prod.fst bottleneck7_tri_depth3_cv_concrete) δ

theorem uniK7_mem_Depth3RobustBasin7At (δ : ℚ) :
    uniK7 ∈ Depth3RobustBasin7At δ := by
  change (30 / 11 : ℚ) ≤ (GovGraph.rgTrajectory uniK7 sig7 δ 3).1
  rw [uniK7_depth3_cv δ]
  norm_num

theorem asymK7_mem_Depth3RobustBasin7At (δ : ℚ) :
    asymK7 ∈ Depth3RobustBasin7At δ := by
  change (30 / 11 : ℚ) ≤ (GovGraph.rgTrajectory asymK7 sig7 δ 3).1
  rw [asymK7_depth3_cv δ]
  norm_num

theorem nearPath7_mem_Depth3RobustBasin7At (δ : ℚ) :
    nearPath7 ∈ Depth3RobustBasin7At δ := by
  change (30 / 11 : ℚ) ≤ (GovGraph.rgTrajectory nearPath7 sig7 δ 3).1
  rw [nearPath7_depth3_cv δ]

theorem hubSpokeHierarchy7_mem_Depth3RobustBasin7At (δ : ℚ) :
    hubSpokeHierarchy7 ∈ Depth3RobustBasin7At δ := by
  change (30 / 11 : ℚ) ≤ (GovGraph.rgTrajectory hubSpokeHierarchy7 sig7 δ 3).1
  rw [hubSpokeHierarchy7_depth3_cv δ]
  norm_num

theorem nestedHierarchy7_mem_Depth3RobustBasin7At (δ : ℚ) :
    nestedHierarchy7 ∈ Depth3RobustBasin7At δ := by
  change (30 / 11 : ℚ) ≤ (GovGraph.rgTrajectory nestedHierarchy7 sig7 δ 3).1
  rw [nestedHierarchy7_depth3_cv δ]
  norm_num

theorem bottleneck7_bi_not_mem_Depth3RobustBasin7At (δ : ℚ) :
    bottleneck7_bi ∉ Depth3RobustBasin7At δ := by
  intro hBasin
  change (30 / 11 : ℚ) ≤ (GovGraph.rgTrajectory bottleneck7_bi sig7 δ 3).1 at hBasin
  rw [bottleneck7_bi_depth3_cv δ] at hBasin
  norm_num at hBasin

theorem bottleneck7_tri_not_mem_Depth3RobustBasin7At (δ : ℚ) :
    bottleneck7_tri ∉ Depth3RobustBasin7At δ := by
  intro hBasin
  change (30 / 11 : ℚ) ≤ (GovGraph.rgTrajectory bottleneck7_tri sig7 δ 3).1 at hBasin
  rw [bottleneck7_tri_depth3_cv δ] at hBasin
  norm_num at hBasin

end Legitimacy
