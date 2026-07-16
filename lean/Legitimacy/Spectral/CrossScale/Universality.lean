/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.N9Archetypes
import Legitimacy.Spectral.Core.SpectralWellConnected

/-!
# Natural weighted spectral classes

Class predicates for moving the spectral admissible-window statements beyond
the finite archetype table.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

namespace GovGraph

variable {n : Nat}

/-- A weighted governance graph is regular when every vertex has the same
weighted degree. This is the weighted analogue of Mathlib's unweighted
`SimpleGraph.IsRegularOfDegree`, phrased directly over `GovGraph` because the
spectral artifact works with rational edge weights. -/
def IsWeightedRegular (G : GovGraph ℚ n) : Prop :=
  ∃ d : ℚ, ∀ i : Fin n, G.deg i = d

/-- The missing lower-bound hypothesis for upgrading weighted regularity from
archetype membership to a universal pass theorem at the default separator.
This is deliberately a `Prop`, not an axiom. The audit found no
available Mathlib or first-party theorem strong enough to prove it, and it is
false for all weighted-regular graphs without additional scale/connectivity
assumptions. -/
def WeightedRegularDefaultProductLowerBound : Prop :=
  ∀ {n : Nat} [NeZero n] (G : GovGraph ℚ n) (hn : 2 ≤ n),
    G.IsWeightedRegular →
      ∀ s : Fin n → ℚ, 0 < G.cv s →
        (17 / 20 : ℝ) ≤ G.spectralGap hn * (G.cv s : ℝ)

/-- Historical conditional form of the stronger universality theorem. The
`WeightedRegularDefaultProductLowerBound` premise is intentionally explicit
and is false without additional scale/connectivity hypotheses; complete
carrier pass theorems must use their dedicated complete-family product floor
instead of routing through this conditional. -/
theorem IsWeightedRegular.admits_default_window_of_product_lower_bound
    (hbound : WeightedRegularDefaultProductLowerBound)
    [NeZero n] (G : GovGraph ℚ n) (hG : G.IsWeightedRegular)
    (s : Fin n → ℚ) (hs : 0 < G.cv s) (hn : 2 ≤ n) :
    ∃ θ_min θ_max : ℚ,
      θ_min ≤ (17 / 20 : ℚ) ∧ (17 / 20 : ℚ) ≤ θ_max ∧
        SpectralWellConnectedAt G s θ_min hn := by
  refine ⟨17 / 20, 17 / 20, le_rfl, le_rfl, ?_⟩
  exact (SpectralWellConnected_iff_at_default G s hn).mp
    ((SpectralWellConnected_iff_product_threshold G s hn).mpr
      (hbound G hn hG s hs))

end GovGraph

/-- Tiny weighted-regular uniform triangle. Scaling all off-diagonal weights
down preserves weighted regularity and the CV computation, but scales the
Laplacian spectral gap. -/
def tinyUniformTri : GovGraph ℚ 3 where
  weights := !![
    0, 1 / 10000, 1 / 10000;
    1 / 10000, 0, 1 / 10000;
    1 / 10000, 1 / 10000, 0
  ]
  weight_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by
    intro i
    fin_cases i <;> native_decide

/-- Every node in the tiny uniform triangle has weighted degree `1 / 5000`. -/
private lemma tinyUniformTri_deg (i : Fin 3) :
    tinyUniformTri.deg i = 1 / 5000 := by
  fin_cases i <;> native_decide

/-- The tiny uniform triangle is weighted-regular. -/
theorem tinyUniformTri_isWeightedRegular : GovGraph.IsWeightedRegular tinyUniformTri := by
  refine ⟨1 / 5000, ?_⟩
  intro i
  exact tinyUniformTri_deg i

private lemma tinyUniformTri_laplacianR_mulVec (x : Fin 3 → ℝ) (i : Fin 3) :
    (tinyUniformTri.laplacianR *ᵥ x) i =
      (3 / 10000) * x i - (1 / 10000) * ∑ j : Fin 3, x j := by
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, GovGraph.laplacianR, GovGraph.laplacian,
      GovGraph.degMatrix, GovGraph.deg, GovGraph.W, tinyUniformTri,
      Fin.sum_univ_succ] <;>
    ring_nf

private lemma tinyUniformTri_laplacianR_trace :
    tinyUniformTri.laplacianR.trace = 3 / 5000 := by
  simp [Matrix.trace, GovGraph.laplacianR, GovGraph.laplacian, GovGraph.degMatrix,
    GovGraph.deg, GovGraph.W, tinyUniformTri, Fin.sum_univ_succ]
  ring_nf

private lemma tinyUniformTri_eigenvalue_zero_or_gap (i : Fin 3) :
    let hA := tinyUniformTri.laplacianR_isHermitian
    hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 3 / 10000 := by
  classical
  intro hA
  let v : Fin 3 → ℝ := ⇑(hA.eigenvectorBasis i)
  let lam : ℝ := hA.eigenvalues i
  have hev_fun : tinyUniformTri.laplacianR *ᵥ v = lam • v := by
    simpa [v, lam] using hA.mulVec_eigenvectorBasis i
  by_cases hzero : lam = 0
  · left
    simpa [lam] using hzero
  · right
    have hsum0 : lam * (∑ k : Fin 3, v k) = 0 := by
      have hsum := congrArg (fun y : Fin 3 → ℝ => ∑ k : Fin 3, y k) hev_fun
      simp [Pi.smul_apply, tinyUniformTri_laplacianR_mulVec, Fin.sum_univ_succ] at hsum
      calc
        lam * (∑ k : Fin 3, v k) =
            lam * (v 0 + (v 1 + v 2)) := by
              simp [Fin.sum_univ_succ]
        _ = lam * v 0 + (lam * v 1 + lam * v 2) := by
              ring
        _ = 3 / 10000 * v 0 + (3 / 10000 * v 1 + 3 / 10000 * v 2) -
              3 * (10000⁻¹ * (v 0 + (v 1 + v 2))) := hsum.symm
        _ = 0 := by
              ring
    have hS : ∑ k : Fin 3, v k = 0 :=
      (mul_eq_zero.mp hsum0).resolve_left hzero
    have hv_ne : v ≠ 0 := by
      intro hv
      have hnorm := hA.eigenvectorBasis.norm_eq_one i
      have : hA.eigenvectorBasis i = 0 := by
        ext k
        exact congrFun hv k
      rw [this, norm_zero] at hnorm
      norm_num at hnorm
    have hex : ∃ k : Fin 3, v k ≠ 0 := by
      by_contra h
      apply hv_ne
      ext k
      by_contra hk
      exact h ⟨k, hk⟩
    rcases hex with ⟨k, hvk⟩
    have hrow := congrFun hev_fun k
    rw [tinyUniformTri_laplacianR_mulVec, hS] at hrow
    simp [Pi.smul_apply] at hrow
    rcases hrow with h | h
    · linarith
    · exact False.elim (hvk h)

private lemma tinyUniformTri_eigenvalue0_zero_or_gap
    (i : Fin (Fintype.card (Fin 3))) :
    let hA := tinyUniformTri.laplacianR_isHermitian
    hA.eigenvalues₀ i = 0 ∨ hA.eigenvalues₀ i = 3 / 10000 := by
  intro hA
  let e : Fin (Fintype.card (Fin 3)) ≃ Fin 3 :=
    Fintype.equivOfCardEq (by simp)
  have h := tinyUniformTri_eigenvalue_zero_or_gap (e i)
  simpa [Matrix.IsHermitian.eigenvalues, hA, e] using h

private lemma tinyUniformTri_sum_eigenvalues0 :
    ∑ i : Fin (Fintype.card (Fin 3)),
      tinyUniformTri.laplacianR_isHermitian.eigenvalues₀ i = 3 / 5000 := by
  let hA := tinyUniformTri.laplacianR_isHermitian
  have htrace := hA.trace_eq_sum_eigenvalues
  rw [tinyUniformTri_laplacianR_trace] at htrace
  let e : Fin (Fintype.card (Fin 3)) ≃ Fin 3 :=
    Fintype.equivOfCardEq (by simp)
  have hsum : (∑ i : Fin 3, hA.eigenvalues i) =
      ∑ i : Fin (Fintype.card (Fin 3)), hA.eigenvalues₀ i := by
    rw [← e.symm.sum_comp (fun i => hA.eigenvalues₀ i)]
    simp [Matrix.IsHermitian.eigenvalues, e]
  rw [← hsum]
  exact htrace.symm

/-- Exact spectral-gap discharge for the tiny uniform triangle. -/
theorem tinyUniformTri_spectralGap_eq :
    tinyUniformTri.spectralGap (by norm_num : 2 ≤ 3) = 3 / 10000 := by
  let hA := tinyUniformTri.laplacianR_isHermitian
  unfold GovGraph.spectralGap
  change hA.eigenvalues₀ (1 : Fin 3) = 3 / 10000
  have hvals : ∀ i : Fin 3, hA.eigenvalues₀ i = 0 ∨ hA.eigenvalues₀ i = 3 / 10000 := by
    intro i
    simpa using tinyUniformTri_eigenvalue0_zero_or_gap i
  have hsum : ∑ i : Fin 3, hA.eigenvalues₀ i = 3 / 5000 := by
    simpa using tinyUniformTri_sum_eigenvalues0
  have hnonneg : ∀ i : Fin 3, 0 ≤ hA.eigenvalues₀ i := by
    intro i
    exact GovGraph.eigenvalues_nonneg tinyUniformTri i
  rcases hvals (1 : Fin 3) with hgap0 | hgap
  · have hlast0 : hA.eigenvalues₀ (2 : Fin 3) = 0 := by
      have hlast_le_zero : hA.eigenvalues₀ (2 : Fin 3) ≤ 0 := by
        calc
          hA.eigenvalues₀ (2 : Fin 3) ≤ hA.eigenvalues₀ (1 : Fin 3) :=
            Matrix.IsHermitian.eigenvalues₀_antitone hA (by decide)
          _ = 0 := hgap0
      exact le_antisymm hlast_le_zero (hnonneg (2 : Fin 3))
    have h0_le_gap : hA.eigenvalues₀ (0 : Fin 3) ≤ 3 / 10000 := by
      rcases hvals (0 : Fin 3) with h0 | h0 <;> linarith
    have hsum_le : ∑ i : Fin 3, hA.eigenvalues₀ i ≤ 3 / 10000 := by
      simp [Fin.sum_univ_succ, hgap0, hlast0]
      exact h0_le_gap
    rw [hsum] at hsum_le
    norm_num at hsum_le
  · exact hgap

/-- Scaling the uniform triangle preserves the concrete CV value on `sig`. -/
theorem tinyUniformTri_cv_sig :
    tinyUniformTri.cv sig = 1 := by
  native_decide

/--
Weighted regularity alone does not imply the default product lower bound:
the tiny uniform triangle is weighted-regular and has positive CV, but its
spectral-CV product is strictly below `17 / 20`.

This complements
`GovGraph.IsWeightedRegular.admits_default_window_of_product_lower_bound`:
that theorem remains a useful conditional lift, and this witness shows its
`WeightedRegularDefaultProductLowerBound` hypothesis cannot be replaced by
weighted regularity alone.
-/
theorem weighted_regular_insufficient_for_default_product_lower_bound :
    ∃ (n : Nat) (_h : NeZero n) (G : GovGraph ℚ n) (hn : 2 ≤ n)
      (_hG : G.IsWeightedRegular) (s : Fin n → ℚ) (_hs : 0 < G.cv s),
        G.spectralGap hn * (G.cv s : ℝ) < (17 / 20 : ℝ) := by
  refine ⟨3, inferInstance, tinyUniformTri, by norm_num, tinyUniformTri_isWeightedRegular,
    sig, ?_, ?_⟩
  · rw [tinyUniformTri_cv_sig]
    norm_num
  · rw [tinyUniformTri_spectralGap_eq, tinyUniformTri_cv_sig]
    norm_num

/-- The five-node uniform complete archetype is weighted-regular. -/
theorem uniK5_isWeightedRegular : GovGraph.IsWeightedRegular uniK5 := by
  refine ⟨4, ?_⟩
  intro i
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  fin_cases i <;> native_decide

/-- The seven-node uniform complete archetype is weighted-regular. -/
theorem uniK7_isWeightedRegular : GovGraph.IsWeightedRegular uniK7 := by
  refine ⟨6, ?_⟩
  intro i
  fin_cases i <;> native_decide

/-- The nine-node uniform complete archetype is weighted-regular. -/
theorem uniK9_isWeightedRegular : GovGraph.IsWeightedRegular uniK9 := by
  refine ⟨8, ?_⟩
  intro i
  fin_cases i <;> native_decide

end Legitimacy
