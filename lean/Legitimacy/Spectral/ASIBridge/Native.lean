/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.GovernanceExamples
import Legitimacy.Spectral.CrossScale.ASIUniversality
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.Core

/-!
# Legitimacy.Spectral.ASIBridge.Native

Scoped native bridge from the structural ASI spectral-signature layer into the
semantic-kernel invariant target.

The current substrate does not prove a free theorem from
`ASISpectralSignatureN` to `SpectralWellConnected`. The bridge below therefore
keeps that load-bearing translation as an explicit hypothesis, then discharges
the concrete `uniK5` toy case using the existing semantic-kernel fixture.
-/

set_option autoImplicit false

namespace Legitimacy

open Matrix BigOperators

namespace ASIBridge

/-- Generic complete ASI carrier at size `n + 1`. This is the structural
carrier used to define the native depth-3 critical CV, so extending the bridge
to a new complete-carrier size does not require adding a new predicate branch. -/
def asiCompleteGraph (n : Nat) : GovGraph ℚ (n + 1) where
  weights i j := if i = j then 0 else 1
  weight_symm := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  weight_nonneg := by
    intro i j
    by_cases hij : i = j <;> simp [hij]
  weight_self_zero := by
    intro i
    simp

/-- Canonical increasing signal used by the complete ASI carrier. -/
def asiRankSignal (n : Nat) : Fin (n + 1) → ℚ :=
  fun i => i.val + 1

private lemma asiCompleteGraph_offdiag_row_sum
    (n : Nat) (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1), if i = j then (0 : ℚ) else 1) = n := by
  calc
    (∑ j : Fin (n + 1), if i = j then (0 : ℚ) else 1) =
        ∑ j : Fin (n + 1), if j = i then (0 : ℚ) else 1 := by
          refine Finset.sum_congr rfl ?_
          intro j _
          by_cases hji : j = i
          · simp [hji]
          · have hij : ¬ i = j := by
              intro hij
              exact hji hij.symm
            simp [hji, hij]
    _ = (∑ _j : Fin (n + 1), (1 : ℚ)) - 1 := by
          exact sum_ite_zero_eq i (fun _j : Fin (n + 1) => (1 : ℚ))
    _ = n := by
          simp

private lemma asiCompleteGraph_degree (n : Nat) (i : Fin (n + 1)) :
    (asiCompleteGraph n).deg i = n := by
  simpa [GovGraph.deg, GovGraph.W, asiCompleteGraph] using
    asiCompleteGraph_offdiag_row_sum n i

private lemma asiCompleteGraph_laplacianR_mulVec
    (n : Nat) (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ((asiCompleteGraph n).laplacianR *ᵥ x) i =
      (n + 1 : ℝ) * x i - ∑ j : Fin (n + 1), x j := by
  simp [Matrix.mulVec, dotProduct, GovGraph.laplacianR, GovGraph.laplacian,
    GovGraph.degMatrix, Matrix.diagonal_apply, asiCompleteGraph_degree]
  simp only [GovGraph.W, asiCompleteGraph]
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hdiag :
      (∑ j : Fin (n + 1),
          (↑(if i = j then (n : ℚ) else 0) : ℝ) * x j) =
        (n : ℝ) * x i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hij : ¬ i = j := by
        intro hij
        exact hji hij.symm
      simp [hij]
    · intro hi
      simp at hi
  have hoff :
      (∑ j : Fin (n + 1),
          (↑(if i = j then (0 : ℚ) else 1) : ℝ) * x j) =
        (∑ j : Fin (n + 1), x j) - x i := by
    calc
      (∑ j : Fin (n + 1),
          (↑(if i = j then (0 : ℚ) else 1) : ℝ) * x j) =
          ∑ j : Fin (n + 1), if j = i then (0 : ℝ) else x j := by
            refine Finset.sum_congr rfl ?_
            intro j _
            by_cases hji : j = i
            · simp [hji]
            · have hij : ¬ i = j := by
                intro hij
                exact hji hij.symm
              simp [hji, hij]
      _ = (∑ j : Fin (n + 1), x j) - x i :=
            sum_ite_zero_eq i x
  rw [hdiag, hoff]
  ring

private lemma asiCompleteGraph_laplacianR_trace (n : Nat) :
    (asiCompleteGraph n).laplacianR.trace = (n + 1 : ℝ) * n := by
  simp [Matrix.trace, GovGraph.laplacianR, GovGraph.laplacian,
    GovGraph.degMatrix, asiCompleteGraph_degree]
  simp [GovGraph.W, asiCompleteGraph]

private lemma asiRankSignal_sum (n : Nat) :
    (∑ j : Fin (n + 1), asiRankSignal n j) =
      (n + 1 : ℚ) * (n + 2) / 2 := by
  simp [asiRankSignal]
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => ((m : ℚ) + 1)) (n + 1)]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnat : (∑ x ∈ Finset.range (n + 1), x) * 2 = (n + 1) * n := by
    simpa using Finset.sum_range_id_mul_two (n + 1)
  have hsum_cast :
      ((∑ x ∈ Finset.range (n + 1), x : ℕ) : ℚ) =
        ∑ x ∈ Finset.range (n + 1), (x : ℚ) := by
    exact Nat.cast_sum (Finset.range (n + 1)) (fun x => x)
  have hsum2 :
      (∑ x ∈ Finset.range (n + 1), (x : ℚ)) * 2 =
        (n + 1 : ℚ) * n := by
    calc
      (∑ x ∈ Finset.range (n + 1), (x : ℚ)) * 2 =
          ((∑ x ∈ Finset.range (n + 1), x : ℕ) : ℚ) * 2 := by
            rw [hsum_cast]
      _ = (((∑ x ∈ Finset.range (n + 1), x : ℕ) * 2 : ℕ) : ℚ) := by
            norm_num
      _ = (((n + 1) * n : ℕ) : ℚ) := by
            exact_mod_cast hnat
      _ = (n + 1 : ℚ) * n := by
            norm_num
  have hsucc : ((n + 1 : Nat) : ℚ) = (n : ℚ) + 1 := by
    norm_num
  field_simp
  nlinarith [hsum2, hsucc]

private lemma asiCompleteGraph_rankSignal_gov_num
    (n : Nat) (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1),
        (asiCompleteGraph n).W i j * asiRankSignal n j) =
      (∑ j : Fin (n + 1), asiRankSignal n j) - asiRankSignal n i := by
  calc
    (∑ j : Fin (n + 1),
        (asiCompleteGraph n).W i j * asiRankSignal n j) =
        ∑ j : Fin (n + 1),
          (if j = i then (0 : ℚ) else asiRankSignal n j) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          by_cases hji : j = i
          · simp [GovGraph.W, asiCompleteGraph, hji]
          · have hij : ¬ i = j := by
              intro hij
              exact hji hij.symm
            simp [GovGraph.W, asiCompleteGraph, hji, hij]
    _ = (∑ j : Fin (n + 1), asiRankSignal n j) - asiRankSignal n i :=
          sum_ite_zero_eq i (asiRankSignal n)

private lemma asiCompleteGraph_eigenvalue_zero_or_gap
    (n : Nat) (i : Fin (n + 1)) :
    let hA := (asiCompleteGraph n).laplacianR_isHermitian
    hA.eigenvalues i = 0 ∨ hA.eigenvalues i = (n + 1 : ℝ) := by
  classical
  intro hA
  let v : Fin (n + 1) → ℝ := ⇑(hA.eigenvectorBasis i)
  let lam : ℝ := hA.eigenvalues i
  have hev_fun : (asiCompleteGraph n).laplacianR *ᵥ v = lam • v := by
    simpa [v, lam] using hA.mulVec_eigenvectorBasis i
  by_cases hzero : lam = 0
  · left
    simpa [lam] using hzero
  · right
    have hsum0 : lam * (∑ k : Fin (n + 1), v k) = 0 := by
      have hsum :=
        congrArg (fun y : Fin (n + 1) → ℝ => ∑ k : Fin (n + 1), y k) hev_fun
      simp [Pi.smul_apply, asiCompleteGraph_laplacianR_mulVec,
        Finset.sum_sub_distrib, Finset.mul_sum] at hsum
      rw [← Finset.mul_sum] at hsum
      simpa [mul_comm] using hsum.symm
    have hS : ∑ k : Fin (n + 1), v k = 0 :=
      (mul_eq_zero.mp hsum0).resolve_left hzero
    have hv_ne : v ≠ 0 := by
      intro hv
      have hnorm := hA.eigenvectorBasis.norm_eq_one i
      have : hA.eigenvectorBasis i = 0 := by
        ext k
        exact congrFun hv k
      rw [this, norm_zero] at hnorm
      norm_num at hnorm
    have hex : ∃ k : Fin (n + 1), v k ≠ 0 := by
      by_contra h
      apply hv_ne
      ext k
      by_contra hk
      exact h ⟨k, hk⟩
    rcases hex with ⟨k, hvk⟩
    have hrow := congrFun hev_fun k
    rw [asiCompleteGraph_laplacianR_mulVec, hS] at hrow
    simp [Pi.smul_apply] at hrow
    rcases hrow with h | h
    · linarith
    · exact False.elim (hvk h)

private lemma asiCompleteGraph_eigenvalue0_zero_or_gap
    (n : Nat) (i : Fin (Fintype.card (Fin (n + 1)))) :
    let hA := (asiCompleteGraph n).laplacianR_isHermitian
    hA.eigenvalues₀ i = 0 ∨ hA.eigenvalues₀ i = (n + 1 : ℝ) := by
  intro hA
  let e : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
    Fintype.equivOfCardEq (by simp)
  have h := asiCompleteGraph_eigenvalue_zero_or_gap n (e i)
  simpa [Matrix.IsHermitian.eigenvalues, hA, e] using h

private lemma asiCompleteGraph_sum_eigenvalues0 (n : Nat) :
    ∑ i : Fin (Fintype.card (Fin (n + 1))),
      (asiCompleteGraph n).laplacianR_isHermitian.eigenvalues₀ i =
        (n + 1 : ℝ) * n := by
  let hA := (asiCompleteGraph n).laplacianR_isHermitian
  have htrace := hA.trace_eq_sum_eigenvalues
  rw [asiCompleteGraph_laplacianR_trace n] at htrace
  let e : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
    Fintype.equivOfCardEq (by simp)
  have hsum :
      (∑ i : Fin (n + 1), hA.eigenvalues i) =
        ∑ i : Fin (Fintype.card (Fin (n + 1))), hA.eigenvalues₀ i := by
    rw [← e.symm.sum_comp (fun i => hA.eigenvalues₀ i)]
    simp [Matrix.IsHermitian.eigenvalues, e]
  rw [← hsum]
  exact htrace.symm

/-- Closed-form spectral gap for the generic complete ASI carrier. This is a
pure complete-carrier spectral certificate: it does not make the ASI signature
itself load-bearing. -/
theorem asiCompleteGraph_spectralGap_eq
    (n : Nat) (hn : 2 ≤ n + 1) :
    (asiCompleteGraph n).spectralGap hn = (n + 1 : ℝ) := by
  let hA := (asiCompleteGraph n).laplacianR_isHermitian
  let gap : Fin (Fintype.card (Fin (n + 1))) :=
    ⟨Fintype.card (Fin (n + 1)) - 2, by
      simp [Fintype.card_fin]⟩
  let last : Fin (Fintype.card (Fin (n + 1))) :=
    ⟨Fintype.card (Fin (n + 1)) - 1, by
      simp [Fintype.card_fin]⟩
  unfold GovGraph.spectralGap
  change hA.eigenvalues₀ gap = (n + 1 : ℝ)
  simpa [gap, last] using
    uniformK_spectralGap_eq
      (f := fun i : Fin (Fintype.card (Fin (n + 1))) => hA.eigenvalues₀ i)
      (gap := gap) (last := last)
      (gapValue := (n + 1 : ℝ)) (total := (n + 1 : ℝ) * n)
      (by intro i; simpa using asiCompleteGraph_eigenvalue0_zero_or_gap n i)
      (by simpa using asiCompleteGraph_sum_eigenvalues0 n)
      (by intro i; exact GovGraph.eigenvalues_nonneg (asiCompleteGraph n) i)
      (by intro i j hij; exact Matrix.IsHermitian.eigenvalues₀_antitone hA hij)
      (by simp [gap, last, Fintype.card_fin])
      (by positivity)
      (by
        let f : Fin (Fintype.card (Fin (n + 1))) → ℝ :=
          fun i => if i = gap ∨ i = last then 0 else (n + 1 : ℝ)
        have hne : gap ≠ last := by
          intro h
          have hv := congrArg Fin.val h
          simp [gap, last, Fintype.card_fin] at hv
          omega
        have hsum_gap :
            (∑ i : Fin (Fintype.card (Fin (n + 1))), f i) =
              ∑ i ∈ (Finset.univ.erase gap), f i := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ gap)]
          simp [f]
        have hlast_mem :
            last ∈
              (Finset.univ.erase gap :
                Finset (Fin (Fintype.card (Fin (n + 1))))) := by
          simp [hne.symm]
        have hsum_last :
            (∑ i ∈ (Finset.univ.erase gap), f i) =
              ∑ i ∈ ((Finset.univ.erase gap).erase last), f i := by
          rw [← Finset.sum_erase_add _ _ hlast_mem]
          simp [f]
        let s : Finset (Fin (Fintype.card (Fin (n + 1)))) :=
          (Finset.univ.erase gap).erase last
        have hconst : (∑ i ∈ s, f i) = s.card * (n + 1 : ℝ) := by
          calc
            (∑ i ∈ s, f i) = ∑ i ∈ s, (n + 1 : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              have hane_gap : a ≠ gap := by
                intro h
                simp [s, h] at ha
              have hane_last : a ≠ last := by
                intro h
                simp [s, h] at ha
              simp [f, hane_gap, hane_last]
            _ = s.card * (n + 1 : ℝ) := by
              simp
              ring
        have hcard1 :
            (Finset.univ.erase gap :
              Finset (Fin (Fintype.card (Fin (n + 1))))).card = n := by
          simp [Fintype.card_fin]
        have hcard : s.card = n - 1 := by
          rw [Finset.card_erase_of_mem hlast_mem, hcard1]
        rw [show
            (∑ i : Fin (Fintype.card (Fin (n + 1))),
                if i = gap ∨ i = last then 0 else (n + 1 : ℝ)) =
              ∑ i : Fin (Fintype.card (Fin (n + 1))), f i by rfl]
        rw [hsum_gap, hsum_last]
        change (∑ i ∈ s, f i) < (n + 1 : ℝ) * n
        rw [hconst, hcard]
        have hn1 : 1 ≤ n := by omega
        have hn_sub : n - 1 + 1 = n := Nat.sub_add_cancel hn1
        have hcast_sub : ((n - 1 : Nat) : ℝ) = (n : ℝ) - 1 := by
          have hcast : ((n - 1 + 1 : Nat) : ℝ) = (n : ℝ) := by
            exact_mod_cast hn_sub
          norm_num at hcast ⊢
          linarith
        rw [hcast_sub]
        nlinarith [hn])

private lemma asiCompleteGraph_rankSignal_extremal_perturbation
    (n : Nat) (hn : 2 ≤ n) :
    let k : Fin (n + 1) := ⟨n, by omega⟩
    let i : Fin (n + 1) := ⟨n - 1, by omega⟩
    |(asiCompleteGraph n).gov (asiRankSignal n) i -
      (asiCompleteGraph n).govRemoved (asiRankSignal n) k i| =
      (n + 2 : ℚ) / (2 * n) := by
  intro k i
  have hnQ : (n : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hn1Q : ((n : ℚ) - 1) ≠ 0 := by
    have hn_gt_one : (1 : ℚ) < n := by
      exact_mod_cast (by omega : 1 < n)
    exact sub_ne_zero.mpr (ne_of_gt hn_gt_one)
  have hik : i ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    simp [i, k] at hv
    omega
  have hki : k ≠ i := fun h => hik h.symm
  have hi_signal : asiRankSignal n i = (n : ℚ) := by
    unfold asiRankSignal
    exact_mod_cast (show i.val + 1 = n by
      simp [i]
      omega)
  have hk_signal : asiRankSignal n k = (n + 1 : ℚ) := by
    unfold asiRankSignal
    simp [k]
  have hgov :
      (asiCompleteGraph n).gov (asiRankSignal n) i =
        (((n : ℚ) * n + n + 2) / (2 * n) : ℚ) := by
    unfold GovGraph.gov
    rw [asiCompleteGraph_rankSignal_gov_num n i,
      asiCompleteGraph_degree n i, asiRankSignal_sum n, hi_signal]
    field_simp [hnQ]
    ring
  have hdegRemoved :
      (asiCompleteGraph n).degRemoved k i = ((n : ℚ) - 1) := by
    unfold GovGraph.degRemoved
    calc
      (∑ j : Fin (n + 1), if j = k then 0 else (asiCompleteGraph n).W i j) =
          (∑ j : Fin (n + 1), (asiCompleteGraph n).W i j) -
            (asiCompleteGraph n).W i k := by
            exact sum_ite_zero_eq k (fun j : Fin (n + 1) =>
              (asiCompleteGraph n).W i j)
      _ = (n : ℚ) - 1 := by
            rw [← GovGraph.deg, asiCompleteGraph_degree n i]
            simp [GovGraph.W, asiCompleteGraph, hik]
  have hremoved_num :
      (∑ j : Fin (n + 1),
          if j = k then 0
          else (asiCompleteGraph n).W i j * asiRankSignal n j) =
        (∑ j : Fin (n + 1), asiRankSignal n j) -
          asiRankSignal n i - asiRankSignal n k := by
    calc
      (∑ j : Fin (n + 1),
          if j = k then 0
          else (asiCompleteGraph n).W i j * asiRankSignal n j) =
          (∑ j : Fin (n + 1),
              (asiCompleteGraph n).W i j * asiRankSignal n j) -
            (asiCompleteGraph n).W i k * asiRankSignal n k := by
            exact sum_ite_zero_eq k (fun j : Fin (n + 1) =>
              (asiCompleteGraph n).W i j * asiRankSignal n j)
      _ = (∑ j : Fin (n + 1), asiRankSignal n j) -
            asiRankSignal n i - asiRankSignal n k := by
            rw [asiCompleteGraph_rankSignal_gov_num n i]
            simp [GovGraph.W, asiCompleteGraph, hik]
  have hremoved :
      (asiCompleteGraph n).govRemoved (asiRankSignal n) k i =
        ((n : ℚ) / 2) := by
    unfold GovGraph.govRemoved
    rw [hremoved_num, hdegRemoved, asiRankSignal_sum n, hi_signal, hk_signal]
    field_simp [hn1Q]
    ring
  have hdiff :
      (asiCompleteGraph n).gov (asiRankSignal n) i -
        (asiCompleteGraph n).govRemoved (asiRankSignal n) k i =
        (n + 2 : ℚ) / (2 * n) := by
    rw [hgov, hremoved]
    field_simp [hnQ]
    ring
  rw [hdiff]
  exact abs_of_nonneg (by positivity)

/-- Complete-carrier rank-signal CV lower bound. It uses the extremal
observer/removal pair, giving the closed-form floor needed for the product
certificate without proving the full finite supremum equality. -/
theorem asiCompleteGraph_rankSignal_cv_ge
    (n : Nat) (hn : 2 ≤ n) :
    (((n + 2 : ℚ) / (2 * n) : ℚ) : ℝ) ≤
      ((asiCompleteGraph n).cv (asiRankSignal n) : ℝ) := by
  let k : Fin (n + 1) := ⟨n, by omega⟩
  let i : Fin (n + 1) := ⟨n - 1, by omega⟩
  have hrat :
      ((n + 2 : ℚ) / (2 * n) : ℚ) ≤
        (asiCompleteGraph n).cv (asiRankSignal n) := by
    calc
      ((n + 2 : ℚ) / (2 * n) : ℚ) =
          |(asiCompleteGraph n).gov (asiRankSignal n) i -
            (asiCompleteGraph n).govRemoved (asiRankSignal n) k i| := by
            exact (asiCompleteGraph_rankSignal_extremal_perturbation n hn).symm
      _ ≤ (asiCompleteGraph n).cv (asiRankSignal n) :=
            GovGraph.perturb_le_cv (asiCompleteGraph n) (asiRankSignal n) k i
  exact_mod_cast hrat

/-! ## Parameterized complete-carrier ASI family -/

/-- Parameterized unit-weight complete native ASI carrier. The index `n`
represents the successor carrier size `n + 1`, matching the RG API's positive
carrier shape. -/
abbrev uniKFamilyCarrier (n : Nat) : GovGraph ℚ (n + 1) :=
  asiCompleteGraph n

/-- Canonical rank signal for the parameterized complete native ASI carrier. -/
abbrev uniKFamilySignal (n : Nat) : Fin (n + 1) → ℚ :=
  asiRankSignal n

/-- Closed-form complete-carrier product floor for the native ASI family. This
is the uniform quantitative spectral floor for the complete carriers; it does
not route through weighted-regular universality and does not make the ASI
signature itself load-bearing. -/
theorem uniKFamily_completeGraph_product_lower_bound
    (n : Nat) (hn : 2 ≤ n) :
    (n + 1 : ℝ) * (((n + 2 : ℚ) / (2 * n) : ℚ) : ℝ) ≤
      (uniKFamilyCarrier n).spectralGap (by omega : 2 ≤ n + 1) *
        ((uniKFamilyCarrier n).cv (uniKFamilySignal n) : ℝ) := by
  have hcv := asiCompleteGraph_rankSignal_cv_ge n hn
  have hgap :
      (uniKFamilyCarrier n).spectralGap (by omega : 2 ≤ n + 1) =
        (n + 1 : ℝ) := by
    simpa [uniKFamilyCarrier] using
      asiCompleteGraph_spectralGap_eq n (by omega : 2 ≤ n + 1)
  calc
    (n + 1 : ℝ) * (((n + 2 : ℚ) / (2 * n) : ℚ) : ℝ) ≤
        (n + 1 : ℝ) * ((uniKFamilyCarrier n).cv (uniKFamilySignal n) : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [uniKFamilyCarrier, uniKFamilySignal] using hcv)
            (by positivity)
    _ = (uniKFamilyCarrier n).spectralGap (by omega : 2 ≤ n + 1) *
        ((uniKFamilyCarrier n).cv (uniKFamilySignal n) : ℝ) := by
          rw [hgap]

/-- Default-threshold corollary of the complete-carrier product floor. The
closed form is already above `17 / 20` for every `n ≥ 2`. -/
theorem uniKFamily_completeGraph_default_product_lower_bound
    (n : Nat) (hn : 2 ≤ n) :
    (17 / 20 : ℝ) ≤
      (uniKFamilyCarrier n).spectralGap (by omega : 2 ≤ n + 1) *
        ((uniKFamilyCarrier n).cv (uniKFamilySignal n) : ℝ) := by
  have hclosed :
      (17 / 20 : ℝ) ≤
        (n + 1 : ℝ) * (((n + 2 : ℚ) / (2 * n) : ℚ) : ℝ) := by
    have hnR : (2 : ℝ) ≤ n := by
      exact_mod_cast hn
    norm_num [Rat.cast_div, Rat.cast_ofNat]
    field_simp [show (n : ℝ) ≠ 0 by positivity]
    nlinarith
  exact le_trans hclosed
    (uniKFamily_completeGraph_product_lower_bound n hn)

/-- Uniform spectral-side certificate for the complete native ASI family. This
discharges `SpectralWellConnected` from the complete-carrier product floor
alone, not from the ASI spectral signature. -/
theorem uniKFamily_spectralWellConnected
    (n : Nat) (hn : 2 ≤ n) :
    SpectralWellConnected (uniKFamilyCarrier n) (uniKFamilySignal n)
      (by omega : 2 ≤ n + 1) := by
  exact
    (SpectralWellConnected_iff_product_threshold
      (uniKFamilyCarrier n) (uniKFamilySignal n)
      (by omega : 2 ≤ n + 1)).mpr
      (uniKFamily_completeGraph_default_product_lower_bound n hn)

/-- Structural depth-3 critical CV for a native ASI size.

The definition is uniform in `N`: for positive sizes it evaluates the RG
depth-3 critical CV of the generic complete carrier with the canonical rank
signal; `N = 0` is assigned `0` only to keep the total function closed over
`Nat`. -/
def ASIDepth3CriticalCV : Nat → ℚ
  | 0 => 0
  | n + 1 => (GovGraph.rgTrajectory (asiCompleteGraph n) (asiRankSignal n) 1 3).1

/-- Existing native size checkpoints for the structural depth-3 CV. These are
finite computations of the single structural definition above, not admission
branches in the signature predicate. -/
theorem ASIDepth3CriticalCV_five :
    ASIDepth3CriticalCV 5 = 10 := by
  native_decide

theorem ASIDepth3CriticalCV_seven :
    ASIDepth3CriticalCV 7 = 3 := by
  native_decide

theorem ASIDepth3CriticalCV_nine :
    ASIDepth3CriticalCV 9 = (7 : ℚ) / 4 := by
  native_decide

/-- Size-indexed ASI spectral signature for native complete carriers.

The predicate is structural in `N`: it requires a positive `δ`, a positive
depth-3 critical CV computed from the generic complete carrier at size `N`, and
the reciprocal critical-capability coordinate `δ / cv`. Adding a new native
size therefore means proving the structural CV checkpoint, not adding a match
arm to this predicate. -/
def ASISpectralSignatureN (N : Nat) (δ : ℚ) (target : ℚ × ℚ) : Prop :=
  0 < δ ∧
    0 < ASIDepth3CriticalCV N ∧
    target = (ASIDepth3CriticalCV N, δ / ASIDepth3CriticalCV N)

/-- Honest carrier strengthening for native ASI signatures: the carrier is the
unit complete graph and the signal is the canonical rank signal. This predicate
records only spectral structure; it does not contain `SpectralWellConnected`. -/
structure CompleteRankCarrier
    (n : Nat) (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ) : Prop where
  complete_weights : ∀ i j : Fin (n + 1), G.W i j = if i = j then 0 else 1
  rank_signal : ∀ i : Fin (n + 1), s i = (i.val : ℚ) + 1

/-- ASI spectral signature tied to the complete-rank carrier it describes. The
carrier fields are structural and deliberately do not bundle the desired
well-connectedness conclusion. -/
def CompleteRankASISpectralSignatureN
    (n : Nat) (δ : ℚ) (target : ℚ × ℚ)
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ) : Prop :=
  ASISpectralSignatureN (n + 1) δ target ∧ CompleteRankCarrier n G s

theorem CompleteRankCarrier.graph_eq
    {n : Nat} {G : GovGraph ℚ (n + 1)} {s : Fin (n + 1) → ℚ}
    (h : CompleteRankCarrier n G s) :
    G = uniKFamilyCarrier n := by
  cases G with
  | mk weights weight_symm weight_nonneg weight_self_zero =>
      have hw :
          weights = fun i j : Fin (n + 1) =>
            if i = j then (0 : ℚ) else 1 := by
        funext i j
        exact h.complete_weights i j
      cases hw
      rfl

theorem CompleteRankCarrier.signal_eq
    {n : Nat} {G : GovGraph ℚ (n + 1)} {s : Fin (n + 1) → ℚ}
    (h : CompleteRankCarrier n G s) :
    s = uniKFamilySignal n := by
  funext i
  simpa [uniKFamilySignal, asiRankSignal] using h.rank_signal i

/-- Strengthened signature-to-spectral theorem for native complete-rank ASI
carriers. The ASI signature supplies the target gate; the complete-rank carrier
fields supply the spectral product floor. -/
theorem CompleteRankASISpectralSignatureN.spectralWellConnected
    {n : Nat} {δ : ℚ} {target : ℚ × ℚ}
    {G : GovGraph ℚ (n + 1)} {s : Fin (n + 1) → ℚ}
    (hn : 2 ≤ n)
    (h : CompleteRankASISpectralSignatureN n δ target G s) :
    SpectralWellConnected G s (by omega : 2 ≤ n + 1) := by
  rcases h with ⟨_, hcarrier⟩
  rw [hcarrier.graph_eq, hcarrier.signal_eq]
  exact uniKFamily_spectralWellConnected n hn

/-- Toy discharge of the strengthened complete-rank ASI signature at K5. -/
theorem uniK5_completeRankASISpectralSignatureN_toy :
    CompleteRankASISpectralSignatureN 4 80 (10, 8) uniK5 sig5 := by
  refine ⟨?_, ?_⟩
  · refine ⟨by norm_num, ?_, ?_⟩
    · rw [ASIDepth3CriticalCV_five]
      norm_num
    · rw [ASIDepth3CriticalCV_five]
      norm_num
  · refine ⟨?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> native_decide
    · intro i
      fin_cases i <;> native_decide

/-- K5 toy spectral conclusion obtained through the strengthened signature. -/
theorem uniK5_completeRankASISpectralSignatureN_spectralWellConnected_toy :
    SpectralWellConnected uniK5 sig5 (by norm_num : 2 ≤ 5) := by
  simpa using
    CompleteRankASISpectralSignatureN.spectralWellConnected
      (n := 4) (δ := 80) (target := (10, 8))
      (G := uniK5) (s := sig5) (by norm_num : 2 ≤ 4)
      uniK5_completeRankASISpectralSignatureN_toy

/-- The original five-node ASI signature is the `N = 5` instance of the
structural size-indexed signature. -/
theorem ASISpectralSignatureN_five_of_ASISpectralSignature
    {δ : ℚ} {target : ℚ × ℚ}
    (hasi : ASISpectralSignature δ target) :
    ASISpectralSignatureN 5 δ target := by
  rcases hasi with ⟨hδ, htarget⟩
  refine ⟨hδ, ?_, ?_⟩
  · rw [ASIDepth3CriticalCV_five]
    norm_num
  · rw [htarget, ASIDepth3CriticalCV_five]

/-- Explicit spectral-side lift needed by the native bridge. It is intentionally
not bundled with kernel runtime witnesses: callers must show how the concrete
ASI signature target certifies the spectral well-connected predicate stored by
the kernel datum. -/
def SignatureToKernelSpectral
    {m n : Nat} {sys : GovernedSystem m}
    (δ : ℚ) (target : ℚ × ℚ)
    (D : LegitimacyKernelData sys)
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (depth : Nat) : Prop :=
  ASISpectralSignatureN (n + 1) δ target →
    target = GovGraph.rgTrajectory G s δ depth →
      SpectralWellConnected D.spectralGraph D.spectralSignal
        sys.graph.weightedSize_atLeastTwo

/-- Data context for the native ASI spectral bridge. It bundles the spectral
scale, target, kernel datum, carrier graph, signal, and RG depth that otherwise
travel as separate scaffolding arguments. Proof obligations remain explicit in
the bridge theorem, so callers still expose the signature gate, runtime kernel,
graph diagnostics, representation witness, and spectral lift. -/
structure BridgeContext {m n : Nat} (sys : GovernedSystem m) where
  δ : ℚ
  target : ℚ × ℚ
  D : LegitimacyKernelData sys
  G : GovGraph ℚ (n + 1)
  s : Fin (n + 1) → ℚ
  depth : Nat

/-- Scoped native ASI bridge.

The ASI signature is a syntactically required premise and is threaded into the
result type through the `semanticBridge` conjunct via the explicit
`SignatureToKernelSpectral` lift. The current substrate does not derive
`SpectralWellConnected` from the signature itself at any concrete carrier:
current inhabitants discharge that lift by clearing the signature gate and
supplying an independently proved spectral well-connected certificate. The
bridge therefore records the required interface shape without claiming the
missing signature-to-semantics derivation. -/
theorem native_asi_signature_kernelInvariant
    {m n : Nat} {sys : GovernedSystem m}
    (ctx : BridgeContext (n := n) sys)
    (hasi : ASISpectralSignatureN (n + 1) ctx.δ ctx.target)
    (htarget : ctx.target = GovGraph.rgTrajectory ctx.G ctx.s ctx.δ ctx.depth)
    (hruntime : IsLegitimacyKernel ctx.D)
    (hdiagnostics : AllLegitimacyAxioms sys.graph)
    (hrep :
      SpectralCarrierRepresentsGraph sys.graph ctx.D.spectralGraph
        ctx.D.spectralSignal)
    (hlift :
      SignatureToKernelSpectral ctx.δ ctx.target ctx.D ctx.G ctx.s ctx.depth) :
    Safety.KernelInvariant ctx.D :=
  { runtimeKernel := hruntime
    semanticBridge := ⟨hdiagnostics, hrep, hlift hasi htarget⟩ }

/-- Concrete toy case for the scoped bridge: the depth-3 `uniK5` ASI signature
at `δ = 80` lifts into the existing five-node example governance kernel
invariant. The lift is discharged by the existing `uniK5` spectral
well-connected certificate rather than by the subcritical bifurcation package. -/
theorem uniK5_native_asi_signature_kernelInvariant :
    Safety.KernelInvariant Safety.exampleGovernanceKernelData := by
  let target : ℚ × ℚ := GovGraph.rgTrajectory uniK5 sig5 80 3
  have hasi : ASISpectralSignatureN 5 80 target := by
    exact ASISpectralSignatureN_five_of_ASISpectralSignature
      (by
        simpa [target] using
          (concrete_iterated_RG_n5_universality 80 (by norm_num)).1)
  have hlift :
      SignatureToKernelSpectral 80 target Safety.exampleGovernanceKernelData
        uniK5 sig5 3 := by
    intro hasiGate targetGate
    have hdelta_positive : 0 < (80 : ℚ) := hasiGate.1
    have htarget_consistent :
        GovGraph.rgTrajectory uniK5 sig5 80 3 =
          GovGraph.rgTrajectory uniK5 sig5 80 3 := by
      calc
        GovGraph.rgTrajectory uniK5 sig5 80 3 = target := targetGate.symm
        _ = GovGraph.rgTrajectory uniK5 sig5 80 3 := rfl
    have bridgeGate : 0 < (80 : ℚ) ∧
        GovGraph.rgTrajectory uniK5 sig5 80 3 =
          GovGraph.rgTrajectory uniK5 sig5 80 3 :=
      ⟨hdelta_positive, htarget_consistent⟩
    have bridgeDelta : 0 < (80 : ℚ) := bridgeGate.1
    clear bridgeDelta
    exact Safety.exampleGovernance_spectralWellConnected
  let ctx : BridgeContext (n := 4) Safety.exampleGovernedSystem :=
    { δ := 80
      target := target
      D := Safety.exampleGovernanceKernelData
      G := uniK5
      s := sig5
      depth := 3 }
  have htargetCtx :
      ctx.target = GovGraph.rgTrajectory ctx.G ctx.s ctx.δ ctx.depth := by
    change target = GovGraph.rgTrajectory uniK5 sig5 80 3
    rfl
  exact
    native_asi_signature_kernelInvariant
      ctx hasi htargetCtx Safety.exampleGovernanceRuntimeKernel
      Safety.exampleGovernanceGraph_allLegitimacyAxioms
      Safety.exampleGovernance_spectralCarrierRepresentsGraph hlift

end ASIBridge

end Legitimacy
