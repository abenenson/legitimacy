/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.RGFlow.Core

/-!
# Legitimacy.Spectral.CrossScale.RGFlow.N5

Concrete `n = 5` iterated-RG trajectory table and positive-δ spectral
signature package.
-/

set_option autoImplicit false

namespace Legitimacy

/-- **Experimental `n = 5` iterated-RG verification.** This computes the
deterministic maximum-weight-merge proxy trajectory for the five 5-node
archetypes for the five-graph lattice. The result is intended to discriminate the
finite-size coincidence reading from the flow-collapse reading on this single
extended lattice, not to assert a general fixed-point theorem. -/
theorem concrete_iterated_RG_n5 :
    GovGraph.rgTrajectory uniK5 sig5 (1 / 10) 0 = (3 / 4, 2 / 15) ∧
    GovGraph.rgTrajectory uniK5 sig5 (1 / 10) 1 = (3 / 4, 2 / 15) ∧
    GovGraph.rgTrajectory uniK5 sig5 (1 / 10) 2 = (3 / 2, 1 / 15) ∧
    GovGraph.rgTrajectory uniK5 sig5 (1 / 10) 3 = (10, 1 / 100) ∧
    GovGraph.rgTrajectory asymK5 sig5 (1 / 10) 0 = (6 / 5, 1 / 12) ∧
    GovGraph.rgTrajectory asymK5 sig5 (1 / 10) 1 = (3 / 4, 2 / 15) ∧
    GovGraph.rgTrajectory asymK5 sig5 (1 / 10) 2 = (3 / 2, 1 / 15) ∧
    GovGraph.rgTrajectory asymK5 sig5 (1 / 10) 3 = (10, 1 / 100) ∧
    GovGraph.rgTrajectory nearPath5 sig5 (1 / 10) 0 = (100 / 53, 53 / 1000) ∧
    GovGraph.rgTrajectory nearPath5 sig5 (1 / 10) 1 = (153 / 110, 11 / 153) ∧
    GovGraph.rgTrajectory nearPath5 sig5 (1 / 10) 2 = (100 / 53, 53 / 1000) ∧
    GovGraph.rgTrajectory nearPath5 sig5 (1 / 10) 3 = (10, 1 / 100) ∧
    GovGraph.rgTrajectory bottleneck5 sig5 (1 / 10) 0 = (20000 / 10001, 10001 / 200000) ∧
    GovGraph.rgTrajectory bottleneck5 sig5 (1 / 10) 1 = (3, 1 / 30) ∧
    GovGraph.rgTrajectory bottleneck5 sig5 (1 / 10) 2 = (3, 1 / 30) ∧
    GovGraph.rgTrajectory bottleneck5 sig5 (1 / 10) 3 = (9, 1 / 90) ∧
    GovGraph.rgTrajectory wheel5 sig5 (1 / 10) 0 = (5 / 2, 1 / 25) ∧
    GovGraph.rgTrajectory wheel5 sig5 (1 / 10) 1 = (11 / 12, 6 / 55) ∧
    GovGraph.rgTrajectory wheel5 sig5 (1 / 10) 2 = (11 / 6, 3 / 55) ∧
    GovGraph.rgTrajectory wheel5 sig5 (1 / 10) 3 = (10, 1 / 100) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  all_goals native_decide

/-- The canonical positive-`δ` ASI-safe depth-3 RG signature on the `n = 5`
lattice: well-connected archetypes land at CV `10`, so the critical-capability
coordinate is exactly `δ / 10`. -/
def ASISpectralSignature (δ : ℚ) (target : ℚ × ℚ) : Prop :=
  0 < δ ∧ target = (10, δ / 10)

/-- Transport a known depth-`k` CV value into the full `δ`-parametric RG
trajectory. The RG state itself is `δ`-independent; only the `C_star`
coordinate rescales with `δ`. -/
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

private lemma rgTrajectory_eq_of_cv {n : ℕ}
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (δ δ₀ c : ℚ) (k : ℕ)
    (hcv : (GovGraph.rgTrajectory G s δ₀ k).1 = c) :
    GovGraph.rgTrajectory G s δ k = (c, δ / c) := by
  have hfst : (GovGraph.rgTrajectory G s δ k).1 = c := by
    calc
      (GovGraph.rgTrajectory G s δ k).1
          = (GovGraph.rgTrajectory G s δ₀ k).1 :=
            rgTrajectory_fst_eq G s δ δ₀ k
      _ = c := hcv
  have hsnd : (GovGraph.rgTrajectory G s δ k).2 = δ / c := by
    unfold GovGraph.rgTrajectory
    cases hstate : GovGraph.rgStateAt G s k with
    | mk m pair =>
        cases pair with
        | mk Gk sk =>
            have hcv0 := hcv
            unfold GovGraph.rgTrajectory at hcv0
            have hcv' : Gk.cv sk = c := by
              rw [hstate] at hcv0
              simpa using hcv0
            simp [C_star, hcv']
  exact Prod.ext hfst hsnd

/-- Equality-form bridge for the `δ`-parametric ASI-safe signature.
Keeping the result as a raw trajectory table factors the parametric statement
through the already-computed `δ = 1/10` depth-3 witnesses, rather than asking
`native_decide` to solve a goal with a free rational parameter. -/
lemma concrete_iterated_RG_n5_parametric_bridge (δ : ℚ) :
    GovGraph.rgTrajectory uniK5 sig5 δ 3 = (10, δ / 10) ∧
    GovGraph.rgTrajectory asymK5 sig5 δ 3 = (10, δ / 10) ∧
    GovGraph.rgTrajectory nearPath5 sig5 δ 3 = (10, δ / 10) ∧
    GovGraph.rgTrajectory bottleneck5 sig5 δ 3 = (9, δ / 9) ∧
    GovGraph.rgTrajectory wheel5 sig5 δ 3 = (10, δ / 10) := by
  rcases concrete_iterated_RG_n5 with
    ⟨_, _, _, huni3, _, _, _, hasym3, _, _, _, hnear3,
      _, _, _, hbottleneck3, _, _, _, hwheel3⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact rgTrajectory_eq_of_cv uniK5 sig5 δ (1 / 10) 10 3 (by
      simpa using congrArg Prod.fst huni3)
  · exact rgTrajectory_eq_of_cv asymK5 sig5 δ (1 / 10) 10 3 (by
      simpa using congrArg Prod.fst hasym3)
  · exact rgTrajectory_eq_of_cv nearPath5 sig5 δ (1 / 10) 10 3 (by
      simpa using congrArg Prod.fst hnear3)
  · exact rgTrajectory_eq_of_cv bottleneck5 sig5 δ (1 / 10) 9 3 (by
      simpa using congrArg Prod.fst hbottleneck3)
  · exact rgTrajectory_eq_of_cv wheel5 sig5 δ (1 / 10) 10 3 (by
      simpa using congrArg Prod.fst hwheel3)

/-- The depth-3 `n = 5` lattice split is genuinely positive-`δ` parametric for the
deterministic RG proxy: the well-connected class has signature `(10, δ / 10)`,
while `bottleneck5` does not. -/
theorem concrete_iterated_RG_n5_parametric_signature
    (δ : ℚ) (hδ : 0 < δ) :
    ASISpectralSignature δ (GovGraph.rgTrajectory uniK5 sig5 δ 3) ∧
    ASISpectralSignature δ (GovGraph.rgTrajectory asymK5 sig5 δ 3) ∧
    ASISpectralSignature δ (GovGraph.rgTrajectory nearPath5 sig5 δ 3) ∧
    ¬ ASISpectralSignature δ (GovGraph.rgTrajectory bottleneck5 sig5 δ 3) ∧
    ASISpectralSignature δ (GovGraph.rgTrajectory wheel5 sig5 δ 3) := by
  rcases concrete_iterated_RG_n5_parametric_bridge δ with
    ⟨huni, hasym, hnear, hbottleneck, hwheel⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hδ, by simpa using huni⟩
  · exact ⟨hδ, by simpa using hasym⟩
  · exact ⟨hδ, by simpa using hnear⟩
  · have hnot : ¬ ASISpectralSignature δ (9, δ / 9) := by
      simp [ASISpectralSignature]
    simpa [hbottleneck] using hnot
  · exact ⟨hδ, by simpa using hwheel⟩

end Legitimacy
