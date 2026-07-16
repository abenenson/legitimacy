/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Capacity.CriticalCapability

/-!
  Stackelberg comparisons on the canonical five-graph lattice.

  This module packages the finite lattice of concrete 3-node governance
  archetypes together with the exact Stackelberg value, attainment,
  lower-bound, dominance, and asymmetry-cost theorems used by the paper's
  comparative spectral analysis.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

/-- The canonical five-graph verification lattice used for Stackelberg
    governance comparisons at fixed signal `sig`. -/
def fiveGraphLattice : Set (GovGraph ℚ 3) :=
  {G | G = uniTriGraph ∨ G = asymTriGraph ∨ G = nearPathGraph ∨
      G = stronglyConnectedGraph ∨ G = bottleneckGraph}

/-- **Stackelberg value over the canonical peer-relative graph lattice.**
    Maximum critical-capability threshold achievable across the five
    structural archetypes under the standard signal. -/
def stackelbergValue (δ : ℚ) : ℚ :=
  max (C_star uniTriGraph sig δ)
    (max (C_star asymTriGraph sig δ)
      (max (C_star nearPathGraph sig δ)
        (max (C_star stronglyConnectedGraph sig δ)
             (C_star bottleneckGraph sig δ))))

private lemma max_three_eq_or {α : Type*} [LinearOrder α] (a b c : α) :
    max a (max b c) = a ∨ max a (max b c) = b ∨ max a (max b c) = c := by
  by_cases hrest : max b c ≤ a
  · left
    simp [max_eq_left hrest]
  · have htail : max b c = b ∨ max b c = c := by
      by_cases hcb : c ≤ b
      · left
        simp [max_eq_left hcb]
      · right
        simp [max_eq_right (le_of_not_ge hcb)]
    rcases htail with htail | htail
    · right
      left
      rw [max_eq_right (le_of_not_ge hrest), htail]
    · right
      right
      rw [max_eq_right (le_of_not_ge hrest), htail]

private lemma max_four_eq_or {α : Type*} [LinearOrder α] (a b c d : α) :
    max a (max b (max c d)) = a ∨
    max a (max b (max c d)) = b ∨
    max a (max b (max c d)) = c ∨
    max a (max b (max c d)) = d := by
  by_cases hrest : max b (max c d) ≤ a
  · left
    simp [max_eq_left hrest]
  · have htail := max_three_eq_or b c d
    rcases htail with htail | htail | htail
    · right
      left
      rw [max_eq_right (le_of_not_ge hrest), htail]
    · right
      right
      left
      rw [max_eq_right (le_of_not_ge hrest), htail]
    · right
      right
      right
      rw [max_eq_right (le_of_not_ge hrest), htail]

private lemma max_five_eq_or {α : Type*} [LinearOrder α] (a b c d e : α) :
    max a (max b (max c (max d e))) = a ∨
    max a (max b (max c (max d e))) = b ∨
    max a (max b (max c (max d e))) = c ∨
    max a (max b (max c (max d e))) = d ∨
    max a (max b (max c (max d e))) = e := by
  by_cases hrest : max b (max c (max d e)) ≤ a
  · left
    simp [max_eq_left hrest]
  · have htail := max_four_eq_or b c d e
    rcases htail with htail | htail | htail | htail
    · right
      left
      rw [max_eq_right (le_of_not_ge hrest), htail]
    · right
      right
      left
      rw [max_eq_right (le_of_not_ge hrest), htail]
    · right
      right
      right
      left
      rw [max_eq_right (le_of_not_ge hrest), htail]
    · right
      right
      right
      right
      rw [max_eq_right (le_of_not_ge hrest), htail]

/-- All five concrete graphs have CV at least one under the standard signal. -/
private lemma concrete_cv_ge_one :
    1 ≤ uniTriGraph.cv sig ∧
    1 ≤ asymTriGraph.cv sig ∧
    1 ≤ nearPathGraph.cv sig ∧
    1 ≤ stronglyConnectedGraph.cv sig ∧
    1 ≤ bottleneckGraph.cv sig := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  all_goals native_decide

/-- The Stackelberg value is attained by one of the five concrete graphs. -/
lemma stackelberg_attained (δ : ℚ) (hδ : 0 < δ) :
    stackelbergValue δ = C_star uniTriGraph sig δ ∨
    stackelbergValue δ = C_star asymTriGraph sig δ ∨
    stackelbergValue δ = C_star nearPathGraph sig δ ∨
    stackelbergValue δ = C_star stronglyConnectedGraph sig δ ∨
    stackelbergValue δ = C_star bottleneckGraph sig δ := by
  let _ := hδ
  simpa [stackelbergValue] using
    (max_five_eq_or
      (C_star uniTriGraph sig δ)
      (C_star asymTriGraph sig δ)
      (C_star nearPathGraph sig δ)
      (C_star stronglyConnectedGraph sig δ)
      (C_star bottleneckGraph sig δ))

/-- Exact Stackelberg values for the canonical five-graph lattice at tolerance
    `1/10`. -/
lemma stackelberg_concrete :
    stackelbergValue (1 / 10) = 1 / 10 ∧
    C_star uniTriGraph sig (1 / 10) = stackelbergValue (1 / 10) ∧
    C_star nearPathGraph sig (1 / 10) = stackelbergValue (1 / 10) ∧
    C_star stronglyConnectedGraph sig (1 / 10) = stackelbergValue (1 / 10) ∧
    C_star bottleneckGraph sig (1 / 10) = stackelbergValue (1 / 10) ∧
    C_star asymTriGraph sig (1 / 10) < stackelbergValue (1 / 10) := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  native_decide

/-- The Stackelberg value is always bounded above by the target tolerance. -/
lemma stackelberg_upper_bound (δ : ℚ) (hδ : 0 < δ) :
    stackelbergValue δ ≤ δ := by
  rcases concrete_cv_ge_one with ⟨huni, hasym, hnear, hstrong, hbot⟩
  unfold stackelbergValue
  apply max_le
  · unfold C_star
    exact div_le_self hδ.le huni
  · apply max_le
    · unfold C_star
      exact div_le_self hδ.le hasym
    · apply max_le
      · unfold C_star
        exact div_le_self hδ.le hnear
      · apply max_le
        · unfold C_star
          exact div_le_self hδ.le hstrong
        · unfold C_star
          exact div_le_self hδ.le hbot

/-- Every graph in the five-graph lattice has positive CV under `sig`. -/
lemma fiveGraphLattice_cv_pos {G : GovGraph ℚ 3} (hG : G ∈ fiveGraphLattice) :
    0 < G.cv sig := by
  rcases hG with rfl | rfl | rfl | rfl | rfl
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  all_goals native_decide

/-- Every graph in the lattice has critical capability bounded by the
    Stackelberg value. -/
lemma fiveGraphLattice_C_star_le_stackelbergValue (δ : ℚ)
    {G : GovGraph ℚ 3} (hG : G ∈ fiveGraphLattice) :
    C_star G sig δ ≤ stackelbergValue δ := by
  rcases hG with rfl | rfl | rfl | rfl | rfl
  · exact le_max_left _ _
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  · exact le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

/-- Any capability at least as large as the Stackelberg value suffices for the
    follower to realize a perturbation on every graph in the lattice. -/
lemma stackelberg_follower_strictly_dominates
    (C : ℚ) (δ : ℚ) (hδ : 0 < δ) (hC : stackelbergValue δ ≤ C) :
    ∀ G ∈ fiveGraphLattice, G.spViolation sig (δ / C) := by
  intro G hG
  have hcv : 0 < G.cv sig := fiveGraphLattice_cv_pos hG
  have hstar : C_star G sig δ ≤ C :=
    le_trans (fiveGraphLattice_C_star_le_stackelbergValue δ hG) hC
  exact (C_star_exists G sig δ hδ hcv).2 C hstar

/-- **Asymmetry cost.** Within the five-graph lattice, the asymmetric
    triangle has strictly lower critical capability than all four
    symmetric graphs at tolerance `1/10`. -/
lemma stackelberg_asymmetry_cost :
    C_star asymTriGraph sig (1 / 10) <
      min (C_star uniTriGraph sig (1 / 10))
        (min (C_star nearPathGraph sig (1 / 10))
          (min (C_star stronglyConnectedGraph sig (1 / 10))
               (C_star bottleneckGraph sig (1 / 10)))) := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  native_decide

end Legitimacy
