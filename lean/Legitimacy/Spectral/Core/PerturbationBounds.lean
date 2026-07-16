/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Core.Basic

/-!
  Spectral perturbation and positive-semidefiniteness bounds.

  This module contains the analytic core of the spectral development: weighted
  average estimates, perturbation identities, pointwise perturbation bounds,
  and Laplacian PSD facts used by the concrete and capability layers.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {n : Nat}
-- =====================================================================
-- S 5. Weighted average bounds (algebraic layer)
-- =====================================================================

private theorem weighted_sum_le_upper {ι : Type*} (s : Finset ι)
    (w f : ι → F) (c : F)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, f i ≤ c) :
    ∑ i ∈ s, w i * f i ≤ c * ∑ i ∈ s, w i := by
  calc ∑ i ∈ s, w i * f i
      ≤ ∑ i ∈ s, w i * c := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hf i hi) (hw i hi)
    _ = c * ∑ i ∈ s, w i := by rw [Finset.mul_sum]; congr 1; ext; ring

private theorem weighted_sum_ge_lower {ι : Type*} (s : Finset ι)
    (w f : ι → F) (c : F)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, c ≤ f i) :
    c * ∑ i ∈ s, w i ≤ ∑ i ∈ s, w i * f i := by
  calc c * ∑ i ∈ s, w i
      = ∑ i ∈ s, w i * c := by rw [Finset.mul_sum]; congr 1; ext; ring
    _ ≤ ∑ i ∈ s, w i * f i := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hf i hi) (hw i hi)

/-- If every sample lies below `c`, then the weighted average also lies below
`c`. -/
lemma wavg_le {ι : Type*} (s : Finset ι)
    (w f : ι → F) (c : F)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, f i ≤ c)
    (hW : 0 < ∑ i ∈ s, w i) :
    (∑ i ∈ s, w i * f i) / (∑ i ∈ s, w i) ≤ c := by
  rw [div_le_iff₀ hW]
  exact weighted_sum_le_upper s w f c hw hf

/-- If every sample lies above `c`, then the weighted average also lies above
`c`. -/
lemma wavg_ge {ι : Type*} (s : Finset ι)
    (w f : ι → F) (c : F)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, c ≤ f i)
    (hW : 0 < ∑ i ∈ s, w i) :
    c ≤ (∑ i ∈ s, w i * f i) / (∑ i ∈ s, w i) := by
  rw [le_div_iff₀ hW]
  exact weighted_sum_ge_lower s w f c hw hf

-- =====================================================================
-- S 6. Perturbation identity (algebraic layer)
-- =====================================================================

/-- Weighted sum splits at k. -/
lemma GovGraph.wsum_split (G : GovGraph F n) (s : Fin n → F)
    (k i : Fin n) :
    ∑ j : Fin n, G.W i j * s j =
    G.W i k * s k + ∑ j : Fin n, (if j = k then 0 else G.W i j * s j) := by
  linarith [sum_ite_zero_eq k (fun j => G.W i j * s j)]

/-- Cook's (1977) leverage-residual factorization for the governance map.

    `gov_i(s) - gov_i^{(-k)}(s) = (w_ik / d_i) · (s_k - gov_i^{(-k)}(s))`

    where `w_ik / d_i = P_ik` is the hat-matrix leverage and `|s_k - gov_i^{(-k)}|`
    is the leave-one-out residual. See Cook (1977) "Detection of Influential
    Observation in Linear Regression," *Technometrics* 19(1): 15–18. -/
lemma GovGraph.leverage_residual_factorization (G : GovGraph F n) (s : Fin n → F)
    (k i : Fin n) (hD : G.deg i ≠ 0) (hD' : G.degRemoved k i ≠ 0) :
    G.gov s i - G.govRemoved s k i =
    G.W i k * (s k - G.govRemoved s k i) / G.deg i := by
  simp only [gov, govRemoved]
  rw [G.wsum_split s k i, G.deg_eq_weight_add_degRemoved k i]
  set a := G.W i k
  set b := G.degRemoved k i
  set num := ∑ j : Fin n, if j = k then 0 else G.W i j * s j
  have hab : a + b ≠ 0 := by rwa [← G.deg_eq_weight_add_degRemoved k i]
  field_simp
  ring

-- =====================================================================
-- S 7. Main algebraic bounds (over F)
-- =====================================================================

/-- govRemoved lies within R of s(k). -/
lemma GovGraph.govRemoved_in_signal_range (G : GovGraph F n) (s : Fin n → F)
    (R : F)
    (hsr : ∀ a b : Fin n, |s a - s b| ≤ R)
    (k i : Fin n) (hD' : 0 < G.degRemoved k i) :
    |s k - G.govRemoved s k i| ≤ R := by
  simp only [govRemoved]
  have hR : 0 ≤ R := by
    simpa using hsr k k
  have hlo : ∀ j : Fin n, s k - R ≤ s j := fun j => by
    have := hsr k j; rw [abs_le] at this; linarith [this.1]
  have hhi : ∀ j : Fin n, s j ≤ s k + R := fun j => by
    have := hsr k j; rw [abs_le] at this; linarith [this.2]
  set wk : Fin n → F := fun j => if j = k then 0 else G.W i j
  have hwk : ∀ j ∈ Finset.univ, 0 ≤ wk j := fun j _ => by
    simp only [wk]; split <;> [exact le_refl 0; exact G.nonneg i j]
  have hWk : 0 < ∑ j : Fin n, wk j := by
    have : ∑ j : Fin n, wk j = G.degRemoved k i := by
      apply Finset.sum_congr rfl; intro j _; simp [wk]
    linarith
  have hsum_eq :
      ∑ j : Fin n, wk j * s j =
      ∑ j : Fin n, (if j = k then 0 else G.W i j * s j) := by
    apply Finset.sum_congr rfl; intro j _
    simp only [wk]; split <;> simp [*]
  have hW_eq : ∑ j : Fin n, wk j = G.degRemoved k i := by
    apply Finset.sum_congr rfl; intro j _; simp [wk]
  have h_upper : (∑ j, (if j = k then 0 else G.W i j * s j)) /
      G.degRemoved k i ≤ s k + R := by
    rw [← hsum_eq, ← hW_eq]
    exact wavg_le Finset.univ wk s (s k + R) hwk (fun j _ => hhi j) hWk
  have h_lower : s k - R ≤ (∑ j, (if j = k then 0 else G.W i j * s j)) /
      G.degRemoved k i := by
    rw [← hsum_eq, ← hW_eq]
    exact wavg_ge Finset.univ wk s (s k - R) hwk (fun j _ => hlo j) hWk
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **Pointwise perturbation bound by signal range.**
    For the chosen removal/observer pair `(k, i)`, the perturbation in
    `gov` caused by removing `k` is at most `R`. -/
lemma GovGraph.perturbation_le_signalRange (G : GovGraph F n) (s : Fin n → F)
    (R : F) (hR : 0 ≤ R)
    (hsr : ∀ a b : Fin n, |s a - s b| ≤ R)
    (k i : Fin n)
    (hD : 0 < G.deg i) (hD' : 0 < G.degRemoved k i) :
    |G.gov s i - G.govRemoved s k i| ≤ R := by
  rw [G.leverage_residual_factorization s k i (ne_of_gt hD) (ne_of_gt hD')]
  rw [abs_div, abs_mul]
  apply div_le_of_le_mul₀ (abs_nonneg _) hR
  calc |G.W i k| * |s k - G.govRemoved s k i|
      ≤ |G.W i k| * R :=
        mul_le_mul_of_nonneg_left
          (G.govRemoved_in_signal_range s R hsr k i hD')
          (abs_nonneg _)
    _ ≤ G.deg i * R := by
        rw [abs_of_nonneg (G.nonneg i k)]
        exact mul_le_mul_of_nonneg_right (G.weight_le_deg i k) hR
    _ = R * |G.deg i| := by rw [abs_of_pos hD]; ring

/-- **Theorem 2: |perturb| * deg(i) ≤ R * w(i,k).** -/
lemma GovGraph.perturb_deg_le_signalRange_mul_weight_all (G : GovGraph F n)
    (s : Fin n → F) (R : F)
    (hsr : ∀ a b : Fin n, |s a - s b| ≤ R)
    (k i : Fin n)
    (hD : 0 < G.deg i) (hD' : 0 < G.degRemoved k i) :
    |G.gov s i - G.govRemoved s k i| * G.deg i ≤ R * G.W i k := by
  rw [G.leverage_residual_factorization s k i (ne_of_gt hD) (ne_of_gt hD')]
  rw [abs_div, abs_mul, abs_of_pos hD]
  rw [div_mul_cancel₀ _ (ne_of_gt hD)]
  calc |G.W i k| * |s k - G.govRemoved s k i|
      ≤ |G.W i k| * R :=
        mul_le_mul_of_nonneg_left
          (G.govRemoved_in_signal_range s R hsr k i hD')
          (abs_nonneg _)
    _ = R * G.W i k := by rw [abs_of_nonneg (G.nonneg i k)]; ring

/-- **Theorem 2: |perturb| * deg(i) ≤ R * w(i,k).** -/
lemma GovGraph.perturb_deg_le_signalRange_mul_weight (G : GovGraph F n)
    (s : Fin n → F) (R : F)
    (hsr : ∀ a b : Fin n, |s a - s b| ≤ R)
    (k i : Fin n)
    (hD : 0 < G.deg i) (hD' : 0 < G.degRemoved k i) :
    |G.gov s i - G.govRemoved s k i| * G.deg i ≤ R * G.W i k := by
  exact G.perturb_deg_le_signalRange_mul_weight_all s R hsr k i hD hD'

/-- **Theorem 3: |perturb| * deg(i) ≤ R * maxDeg(G).** -/
lemma GovGraph.perturb_deg_le_signalRange_mul_maxDeg_all (G : GovGraph F n)
    [NeZero n]
    (s : Fin n → F) (R : F) (hR : 0 ≤ R)
    (hsr : ∀ a b : Fin n, |s a - s b| ≤ R)
    (k i : Fin n)
    (hD : 0 < G.deg i) (hD' : 0 < G.degRemoved k i) :
    |G.gov s i - G.govRemoved s k i| * G.deg i ≤ R * G.maxDeg := by
  calc |G.gov s i - G.govRemoved s k i| * G.deg i
      ≤ R * G.W i k :=
        G.perturb_deg_le_signalRange_mul_weight_all s R hsr k i hD hD'
    _ ≤ R * G.maxDeg := by
        apply mul_le_mul_of_nonneg_left _ hR
        exact le_trans (G.weight_le_deg i k) (G.deg_le_maxDeg i)

/-- **Theorem 3: |perturb| * deg(i) ≤ R * maxDeg(G).** -/
lemma GovGraph.perturb_deg_le_signalRange_mul_maxDeg (G : GovGraph F n)
    [NeZero n]
    (s : Fin n → F) (R : F) (hR : 0 ≤ R)
    (hsr : ∀ a b : Fin n, |s a - s b| ≤ R)
    (k i : Fin n)
    (hD : 0 < G.deg i) (hD' : 0 < G.degRemoved k i) :
    |G.gov s i - G.govRemoved s k i| * G.deg i ≤ R * G.maxDeg := by
  exact G.perturb_deg_le_signalRange_mul_maxDeg_all s R hR hsr k i hD hD'

-- =====================================================================
-- S 8. Spectral gap via Mathlib eigenvalue theory (ℚ → ℝ)
-- =====================================================================


/-- **Pointwise spectral perturbation bound.**
    For the chosen removal/observer pair `(k, i)`, the perturbation is
    bounded by `R * maxDeg / spectralGap`. This assumes both
    `0 < G.spectralGap hn` and the extra comparison
    `G.spectralGap hn ≤ Rat.cast (G.deg i)`. -/
theorem GovGraph.perturbation_spectral_bound_pointwise (G : GovGraph ℚ n)
    [NeZero n]
    (hn : 2 ≤ n)
    (s : Fin n → ℚ) (R : ℚ) (hR : 0 ≤ R)
    (hsr : ∀ a b : Fin n, |s a - s b| ≤ R)
    (hsg : 0 < G.spectralGap hn)
    (k i : Fin n)
    (hD : 0 < G.deg i) (hD' : 0 < G.degRemoved k i)
    (hsg_le : G.spectralGap hn ≤ Rat.cast (G.deg i)) :
    (Rat.cast |G.gov s i - G.govRemoved s k i| : ℝ) ≤
      Rat.cast R * Rat.cast G.maxDeg / G.spectralGap hn := by
  have h3 := G.perturb_deg_le_signalRange_mul_maxDeg s R hR hsr k i hD hD'
  have h3R : (Rat.cast |G.gov s i - G.govRemoved s k i| : ℝ) * Rat.cast (G.deg i) ≤
      Rat.cast R * Rat.cast G.maxDeg := by exact_mod_cast h3
  have hdeg_pos : (0 : ℝ) < Rat.cast (G.deg i) := by exact_mod_cast hD
  have hRmD_nn : (0 : ℝ) ≤ Rat.cast R * Rat.cast G.maxDeg := by
    apply mul_nonneg
    · exact_mod_cast hR
    · exact_mod_cast le_trans (G.deg_nonneg i) (G.deg_le_maxDeg i)
  have step1 : (Rat.cast |G.gov s i - G.govRemoved s k i| : ℝ) ≤
      Rat.cast R * Rat.cast G.maxDeg / Rat.cast (G.deg i) :=
    (le_div_iff₀ hdeg_pos).mpr h3R
  have step2 : Rat.cast R * Rat.cast G.maxDeg / Rat.cast (G.deg i) ≤
      Rat.cast R * Rat.cast G.maxDeg / G.spectralGap hn :=
    div_le_div_of_nonneg_left hRmD_nn hsg hsg_le
  linarith

-- =====================================================================
-- S 9. Laplacian positive semidefiniteness
-- =====================================================================

-- S 9a. Algebraic PSD (over F)

/-- Term-level expansion of x_i * L_{ij} * x_j. -/
private lemma lap_term_eq (G : GovGraph F n) (x : Fin n → F) (i j : Fin n) :
    x i * G.laplacian i j * x j =
    (if i = j then G.deg i * x i ^ 2 else 0) - G.W i j * x i * x j := by
  simp only [GovGraph.laplacian, GovGraph.degMatrix, GovGraph.deg, sub_apply, diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp; ring
  · simp only [hij, ite_false]; ring

/-- Inner sum identity: row i of the quadratic form. -/
private lemma inner_sum_lap (G : GovGraph F n) (x : Fin n → F) (i : Fin n) :
    ∑ j : Fin n, x i * G.laplacian i j * x j =
    G.deg i * x i ^ 2 - ∑ j, G.W i j * x i * x j := by
  simp_rw [lap_term_eq G x i]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_ite_eq univ i]; simp

/-- **The Laplacian is positive semidefinite: x^T L x ≥ 0.**

    Proof via the identity x^T L x = (1/2) Σ_{i,j} w_{ij} (x_i - x_j)^2,
    using double-counting and W-symmetry. -/
theorem GovGraph.laplacian_psd (G : GovGraph F n) (x : Fin n → F) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * G.laplacian i j * x j := by
  simp_rw [inner_sum_lap G x]
  rw [Finset.sum_sub_distrib]
  rw [show ∑ i : Fin n, G.deg i * x i ^ 2 = ∑ i, ∑ j, G.W i j * x i ^ 2 from by
    congr 1; funext i; rw [GovGraph.deg, Finset.sum_mul]]
  have symm_sq : ∑ i : Fin n, ∑ j : Fin n, G.W i j * x j ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, G.W i j * x i ^ 2 := by
    rw [show ∑ i : Fin n, ∑ j : Fin n, G.W i j * x j ^ 2 =
        ∑ j : Fin n, ∑ i : Fin n, G.W i j * x j ^ 2 from Finset.sum_comm]
    congr 1; funext a; congr 1; funext b
    rw [G.symm.apply a b]
  suffices h :
      (∑ i, ∑ j, G.W i j * x i ^ 2) - (∑ i, ∑ j, G.W i j * x i * x j) =
      (1/2) * ∑ i : Fin n, ∑ j : Fin n, G.W i j * (x i - x j) ^ 2 by
    rw [h]
    apply mul_nonneg (by norm_num : (0:F) ≤ 1/2)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (G.nonneg i j) (sq_nonneg _)
  have expand : ∀ i j : Fin n, G.W i j * (x i - x j) ^ 2 =
      G.W i j * x i ^ 2 + G.W i j * x j ^ 2 - 2 * (G.W i j * (x i * x j)) := by
    intros; ring
  simp_rw [expand]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [symm_sq]
  rw [show ∑ i : Fin n, ∑ j : Fin n, 2 * (G.W i j * (x i * x j)) =
      2 * ∑ i : Fin n, ∑ j : Fin n, G.W i j * (x i * x j) from by
    rw [Finset.mul_sum]; congr 1; funext i; rw [Finset.mul_sum]]
  have key : ∀ i j : Fin n, G.W i j * (x i * x j) = G.W i j * x i * x j := by
    intros; ring
  simp_rw [key]
  linarith

-- S 9b. Mathlib PosSemidef and eigenvalue results (ℝ)

/-- Term-level expansion for the ℝ-Laplacian quadratic form. -/
private lemma lap_term_R (G : GovGraph ℚ n) (x : Fin n → ℝ) (i j : Fin n) :
    x i * (↑(G.laplacian i j) : ℝ) * x j =
    (if i = j then (↑(G.deg i) : ℝ) * x i ^ 2 else 0) - (↑(G.W i j) : ℝ) * x i * x j := by
  simp only [GovGraph.laplacian, GovGraph.degMatrix, GovGraph.deg, sub_apply, diagonal_apply]
  by_cases hij : i = j
  · subst hij; push_cast; simp; ring
  · simp only [hij, ite_false]; push_cast; ring

/-- Inner sum identity for the ℝ-Laplacian. -/
private lemma inner_sum_R (G : GovGraph ℚ n) (x : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin n, x i * (↑(G.laplacian i j) : ℝ) * x j =
    (↑(G.deg i) : ℝ) * x i ^ 2 - ∑ j, (↑(G.W i j) : ℝ) * x i * x j := by
  simp_rw [lap_term_R G x i]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_ite_eq univ i]; simp

/-- **The R-Laplacian is positive semidefinite (Mathlib PosSemidef).**
    Same quadratic form argument as laplacian_psd, over ℝ. -/
theorem GovGraph.laplacianR_posSemidef (G : GovGraph ℚ n) :
    G.laplacianR.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg G.laplacianR_isHermitian
  intro x
  simp only [star_trivial, dotProduct, mulVec, GovGraph.laplacianR, map_apply]
  have key : ∑ i, x i * ∑ j, (↑(G.laplacian i j) : ℝ) * x j =
      ∑ i, ∑ j, x i * (↑(G.laplacian i j) : ℝ) * x j := by
    congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
  rw [key]
  simp_rw [inner_sum_R G x]
  rw [Finset.sum_sub_distrib]
  rw [show ∑ i : Fin n, (↑(G.deg i) : ℝ) * x i ^ 2 =
      ∑ i, ∑ j, (↑(G.W i j) : ℝ) * x i ^ 2 from by
    congr 1; funext i; rw [show (↑(G.deg i) : ℝ) = ∑ j, (↑(G.W i j) : ℝ) from by
      push_cast [GovGraph.deg]; rfl]
    rw [Finset.sum_mul]]
  have symm_sq : ∑ i : Fin n, ∑ j : Fin n, (↑(G.W i j) : ℝ) * x j ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, (↑(G.W i j) : ℝ) * x i ^ 2 := by
    rw [show ∑ i : Fin n, ∑ j : Fin n, (↑(G.W i j) : ℝ) * x j ^ 2 =
        ∑ j : Fin n, ∑ i : Fin n, (↑(G.W i j) : ℝ) * x j ^ 2 from Finset.sum_comm]
    congr 1; funext a; congr 1; funext b
    rw [G.symm.apply a b]
  suffices h :
      (∑ i, ∑ j, (↑(G.W i j) : ℝ) * x i ^ 2) -
      (∑ i, ∑ j, (↑(G.W i j) : ℝ) * x i * x j) =
      (1/2) * ∑ i : Fin n, ∑ j : Fin n, (↑(G.W i j) : ℝ) * (x i - x j) ^ 2 by
    rw [h]
    apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (by exact_mod_cast G.nonneg i j) (sq_nonneg _)
  have expand : ∀ i j : Fin n, (↑(G.W i j) : ℝ) * (x i - x j) ^ 2 =
      (↑(G.W i j) : ℝ) * x i ^ 2 + (↑(G.W i j) : ℝ) * x j ^ 2 -
      2 * ((↑(G.W i j) : ℝ) * (x i * x j)) := by intros; ring
  simp_rw [expand]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [symm_sq]
  rw [show ∑ i : Fin n, ∑ j : Fin n, 2 * ((↑(G.W i j) : ℝ) * (x i * x j)) =
      2 * ∑ i : Fin n, ∑ j : Fin n, (↑(G.W i j) : ℝ) * (x i * x j) from by
    rw [Finset.mul_sum]; congr 1; funext i; rw [Finset.mul_sum]]
  have rewrite : ∀ i j : Fin n,
      (↑(G.W i j) : ℝ) * (x i * x j) = (↑(G.W i j) : ℝ) * x i * x j := by
    intros; ring
  simp_rw [rewrite]
  linarith

/-- **All eigenvalues of the Laplacian are non-negative.**
    Follows from PosSemidef via Mathlib's eigenvalue theory. -/
theorem GovGraph.eigenvalues_nonneg (G : GovGraph ℚ n) :
    ∀ i : Fin (Fintype.card (Fin n)),
      0 ≤ G.laplacianR_isHermitian.eigenvalues₀ i := by
  intro i
  have h := G.laplacianR_posSemidef.eigenvalues_nonneg
  simp only [Matrix.IsHermitian.eigenvalues] at h
  set e := Fintype.equivOfCardEq
    ((by simp : Fintype.card (Fin (Fintype.card (Fin n))) = Fintype.card (Fin n)))
  specialize h (e i)
  simp at h
  convert h using 1

end Legitimacy
