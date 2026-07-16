/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.Core

/-!
# Nine-Node Cross-Scale Spectral Certificates

Nine-node spectral-gap certificate discharges.
-/

set_option autoImplicit false

namespace Legitimacy

open Matrix BigOperators

private lemma uniK9_laplacianR_mulVec (x : Fin 9 → ℝ) (i : Fin 9) :
    (uniK9.laplacianR *ᵥ x) i = 9 * x i - ∑ j : Fin 9, x j := by
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, GovGraph.laplacianR, GovGraph.laplacian,
      GovGraph.degMatrix, GovGraph.deg, GovGraph.W, uniK9, Fin.sum_univ_succ] <;>
      ring_nf

private lemma uniK9_laplacianR_trace : uniK9.laplacianR.trace = 72 := by
  simp [Matrix.trace, GovGraph.laplacianR, GovGraph.laplacian, GovGraph.degMatrix,
    GovGraph.deg, GovGraph.W, uniK9, Fin.sum_univ_succ]
  ring_nf

private lemma uniK9_eigenvalue_zero_or_nine (i : Fin 9) :
    let hA := uniK9.laplacianR_isHermitian
    hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 9 := by
  classical
  intro hA
  let v : Fin 9 → ℝ := ⇑(hA.eigenvectorBasis i)
  let lam : ℝ := hA.eigenvalues i
  have hev_fun : uniK9.laplacianR *ᵥ v = lam • v := by
    simpa [v, lam] using hA.mulVec_eigenvectorBasis i
  by_cases hzero : lam = 0
  · left
    simpa [lam] using hzero
  · right
    have hsum0 : lam * (∑ k : Fin 9, v k) = 0 := by
      have hsum := congrArg (fun y : Fin 9 → ℝ => ∑ k : Fin 9, y k) hev_fun
      simp [Pi.smul_apply, uniK9_laplacianR_mulVec, Fin.sum_univ_succ] at hsum
      calc
        lam * (∑ k : Fin 9, v k) =
            lam * (v 0 + (v 1 + (v 2 + (v 3 + (v 4 +
              (v 5 + (v 6 + (v 7 + v 8)))))))) := by
              simp [Fin.sum_univ_succ]
        _ = lam * v 0 +
              (lam * v 1 +
                (lam * v 2 +
                  (lam * v 3 +
                    (lam * v 4 +
                      (lam * v 5 +
                        (lam * v 6 + (lam * v 7 + lam * v 8))))))) := by
              ring
        _ = 0 := hsum.symm
    have hS : ∑ k : Fin 9, v k = 0 :=
      (mul_eq_zero.mp hsum0).resolve_left hzero
    have hv_ne : v ≠ 0 := by
      intro hv
      have hnorm := hA.eigenvectorBasis.norm_eq_one i
      have : hA.eigenvectorBasis i = 0 := by
        ext k
        exact congrFun hv k
      rw [this, norm_zero] at hnorm
      norm_num at hnorm
    have hex : ∃ k : Fin 9, v k ≠ 0 := by
      by_contra h
      apply hv_ne
      ext k
      by_contra hk
      exact h ⟨k, hk⟩
    rcases hex with ⟨k, hvk⟩
    have hrow := congrFun hev_fun k
    rw [uniK9_laplacianR_mulVec, hS] at hrow
    simp [Pi.smul_apply] at hrow
    rcases hrow with h | h
    · linarith
    · exact False.elim (hvk h)

private lemma uniK9_eigenvalue0_zero_or_nine
    (i : Fin (Fintype.card (Fin 9))) :
    let hA := uniK9.laplacianR_isHermitian
    hA.eigenvalues₀ i = 0 ∨ hA.eigenvalues₀ i = 9 := by
  intro hA
  let e : Fin (Fintype.card (Fin 9)) ≃ Fin 9 :=
    Fintype.equivOfCardEq (by simp)
  have h := uniK9_eigenvalue_zero_or_nine (e i)
  simpa [Matrix.IsHermitian.eigenvalues, hA, e] using h

private lemma uniK9_sum_eigenvalues0 :
    ∑ i : Fin (Fintype.card (Fin 9)),
      uniK9.laplacianR_isHermitian.eigenvalues₀ i = 72 := by
  let hA := uniK9.laplacianR_isHermitian
  have htrace := hA.trace_eq_sum_eigenvalues
  rw [uniK9_laplacianR_trace] at htrace
  let e : Fin (Fintype.card (Fin 9)) ≃ Fin 9 :=
    Fintype.equivOfCardEq (by simp)
  have hsum : (∑ i : Fin 9, hA.eigenvalues i) =
      ∑ i : Fin (Fintype.card (Fin 9)), hA.eigenvalues₀ i := by
    rw [← e.symm.sum_comp (fun i => hA.eigenvalues₀ i)]
    simp [Matrix.IsHermitian.eigenvalues, e]
  rw [← hsum]
  exact htrace.symm

/-- Actual Mathlib spectral-gap discharge for the uniform complete nine-node
archetype. -/
theorem uniK9_spectralGap_eq_certificate :
    uniK9.spectralGap (by norm_num : 2 ≤ 9) =
      (uniK9SpectralGapCertificate : ℝ) := by
  let hA := uniK9.laplacianR_isHermitian
  unfold GovGraph.spectralGap
  change hA.eigenvalues₀ (7 : Fin 9) = 9
  simpa [uniK9SpectralGapCertificate] using
    uniformK_spectralGap_eq
      (f := fun i : Fin 9 => hA.eigenvalues₀ i)
      (gap := (7 : Fin 9)) (last := (8 : Fin 9))
      (gapValue := 9) (total := 72)
      (by intro i; simpa using uniK9_eigenvalue0_zero_or_nine i)
      (by simpa using uniK9_sum_eigenvalues0)
      (by intro i; exact GovGraph.eigenvalues_nonneg uniK9 i)
      (by intro i j hij; exact Matrix.IsHermitian.eigenvalues₀_antitone hA hij)
      (by decide)
      (by norm_num)
      (by simp [Fin.sum_univ_succ]; norm_num)

/-- Certificate-vs-actual-gap lower-bound discharge for `uniK9`. -/
theorem uniK9_certificate_discharge :
    (uniK9SpectralGapCertificate : ℝ) ≤
      uniK9.spectralGap (by norm_num : 2 ≤ 9) := by
  rw [uniK9_spectralGap_eq_certificate]

/-- Pending actual-gap discharge for the asymmetric nine-node complete graph. -/
def asymK9_certificate_discharge_pending : Prop :=
  (asymK9SpectralGapCertificate : ℝ) ≤
    asymK9.spectralGap (by norm_num : 2 ≤ 9)

/-- Pending actual-gap discharge for the nine-node near-path graph. -/
def nearPath9_certificate_discharge_pending : Prop :=
  (nearPath9SpectralGapCertificate : ℝ) ≤
    nearPath9.spectralGap (by norm_num : 2 ≤ 9)

/-- Pending actual-gap discharge for the nine-node hub-spoke hierarchy graph. -/
def hubSpokeHierarchy9_certificate_discharge_pending : Prop :=
  (hubSpokeHierarchy9SpectralGapCertificate : ℝ) ≤
    hubSpokeHierarchy9.spectralGap (by norm_num : 2 ≤ 9)

/-- Pending actual-gap discharge for the nine-node nested hierarchy graph. -/
def nestedHierarchy9_certificate_discharge_pending : Prop :=
  (nestedHierarchy9SpectralGapCertificate : ℝ) ≤
    nestedHierarchy9.spectralGap (by norm_num : 2 ≤ 9)

/-- Pending actual-gap discharge for the nine-node wheel graph. -/
def wheel9_certificate_discharge_pending : Prop :=
  (wheel9SpectralGapCertificate : ℝ) ≤
    wheel9.spectralGap (by norm_num : 2 ≤ 9)

private def bottleneck9BiSeparatorVectorQ : Fin 9 → ℚ :=
  ![1, 1, 1, 1, 0, -1, -1, -1, -1]

private def bottleneck9BiSeparatorVectorR : Fin 9 → ℝ :=
  fun i => (bottleneck9BiSeparatorVectorQ i : ℝ)

private def bottleneck9BiConstantVectorQ : Fin 9 → ℚ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1]

private def bottleneck9BiConstantVectorR : Fin 9 → ℝ :=
  fun i => (bottleneck9BiConstantVectorQ i : ℝ)

private lemma bottleneck9_bi_laplacian_mulVec_separatorQ :
    bottleneck9_bi.laplacian *ᵥ bottleneck9BiSeparatorVectorQ =
      (1 / 10000 : ℚ) • bottleneck9BiSeparatorVectorQ := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  native_decide

private lemma bottleneck9_bi_laplacian_mulVec_constantQ :
    bottleneck9_bi.laplacian *ᵥ bottleneck9BiConstantVectorQ =
      (0 : ℚ) • bottleneck9BiConstantVectorQ := by
  native_decide

private lemma bottleneck9_bi_laplacianR_mulVec_separator :
    bottleneck9_bi.laplacianR *ᵥ bottleneck9BiSeparatorVectorR =
      (1 / 10000 : ℝ) • bottleneck9BiSeparatorVectorR := by
  ext i
  have h := congrFun bottleneck9_bi_laplacian_mulVec_separatorQ i
  simp [Matrix.mulVec, dotProduct] at h
  have hq : (∑ x, bottleneck9_bi.laplacian i x * bottleneck9BiSeparatorVectorQ x) =
      (1 / 10000 : ℚ) * bottleneck9BiSeparatorVectorQ i := by
    simpa using h
  have hR : ((∑ x, bottleneck9_bi.laplacian i x *
        bottleneck9BiSeparatorVectorQ x : ℚ) : ℝ) =
      (((1 / 10000 : ℚ) * bottleneck9BiSeparatorVectorQ i : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa [GovGraph.laplacianR, Matrix.mulVec, dotProduct,
    bottleneck9BiSeparatorVectorR] using hR

private lemma bottleneck9_bi_laplacianR_mulVec_constant :
    bottleneck9_bi.laplacianR *ᵥ bottleneck9BiConstantVectorR =
      (0 : ℝ) • bottleneck9BiConstantVectorR := by
  ext i
  have h := congrFun bottleneck9_bi_laplacian_mulVec_constantQ i
  simp [Matrix.mulVec, dotProduct] at h
  have hq : (∑ x, bottleneck9_bi.laplacian i x * bottleneck9BiConstantVectorQ x) =
      (0 : ℚ) * bottleneck9BiConstantVectorQ i := by
    simpa using h
  have hR : ((∑ x, bottleneck9_bi.laplacian i x *
        bottleneck9BiConstantVectorQ x : ℚ) : ℝ) =
      (((0 : ℚ) * bottleneck9BiConstantVectorQ i : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa [GovGraph.laplacianR, Matrix.mulVec, dotProduct,
    bottleneck9BiConstantVectorR] using hR

private lemma bottleneck9BiSeparatorVectorR_ne_zero :
    bottleneck9BiSeparatorVectorR ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [bottleneck9BiSeparatorVectorR, bottleneck9BiSeparatorVectorQ] at this

private lemma bottleneck9BiConstantVectorR_ne_zero :
    bottleneck9BiConstantVectorR ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [bottleneck9BiConstantVectorR, bottleneck9BiConstantVectorQ] at this

private lemma bottleneck9_bi_eigenvalue_exists_of_mulVec
    (mu : ℝ) (v : Fin 9 → ℝ) (hv : v ≠ 0)
    (hmul : bottleneck9_bi.laplacianR *ᵥ v = mu • v) :
    ∃ i : Fin (Fintype.card (Fin 9)),
      bottleneck9_bi.laplacianR_isHermitian.eigenvalues₀ i = mu := by
  let hA := bottleneck9_bi.laplacianR_isHermitian
  have hev : Module.End.HasEigenvalue
      (Matrix.toLin' bottleneck9_bi.laplacianR : Module.End ℝ (Fin 9 → ℝ)) mu := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    rw [Module.End.hasEigenvector_iff]
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      simpa [Matrix.toLin'_apply] using hmul
    · exact hv
  have hspectrum : mu ∈ spectrum ℝ bottleneck9_bi.laplacianR := by
    rw [← Matrix.spectrum_toLin']
    exact Module.End.HasEigenvalue.mem_spectrum hev
  have hrange : mu ∈ Set.range hA.eigenvalues := by
    simpa [hA.spectrum_real_eq_range_eigenvalues] using hspectrum
  rcases hrange with ⟨i, hi⟩
  refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin 9)).symm i, ?_⟩
  simpa [Matrix.IsHermitian.eigenvalues, hA] using hi

private lemma bottleneck9_bi_zero_eigenvalue_exists :
    ∃ i : Fin (Fintype.card (Fin 9)),
      bottleneck9_bi.laplacianR_isHermitian.eigenvalues₀ i = 0 :=
  bottleneck9_bi_eigenvalue_exists_of_mulVec 0 bottleneck9BiConstantVectorR
    bottleneck9BiConstantVectorR_ne_zero bottleneck9_bi_laplacianR_mulVec_constant

private lemma bottleneck9_bi_separator_eigenvalue_exists :
    ∃ i : Fin (Fintype.card (Fin 9)),
      bottleneck9_bi.laplacianR_isHermitian.eigenvalues₀ i = (1 / 10000 : ℝ) :=
  bottleneck9_bi_eigenvalue_exists_of_mulVec (1 / 10000)
    bottleneck9BiSeparatorVectorR bottleneck9BiSeparatorVectorR_ne_zero
    bottleneck9_bi_laplacianR_mulVec_separator

/-- Actual spectral-gap upper-bound discharge for the nine-node biclique
bottleneck graph. -/
theorem bottleneck9_bi_spectralGap_le_certificate :
    bottleneck9_bi.spectralGap (by norm_num : 2 ≤ 9) ≤
      (bottleneck9BiSpectralGapCertificate : ℝ) := by
  let hA := bottleneck9_bi.laplacianR_isHermitian
  unfold GovGraph.spectralGap
  change hA.eigenvalues₀ (7 : Fin 9) ≤
    (bottleneck9BiSpectralGapCertificate : ℝ)
  calc
    hA.eigenvalues₀ (7 : Fin 9) ≤ (1 / 10000 : ℝ) :=
      bottleneck_spectralGap_le
        (f := fun i : Fin 9 => hA.eigenvalues₀ i)
        (gap := (7 : Fin 9)) (last := (8 : Fin 9))
        (cert := (1 / 10000 : ℝ))
        bottleneck9_bi_zero_eigenvalue_exists
        bottleneck9_bi_separator_eigenvalue_exists
        (by intro i; exact GovGraph.eigenvalues_nonneg bottleneck9_bi i)
        (by intro i j hij; exact Matrix.IsHermitian.eigenvalues₀_antitone hA hij)
        (by intro i; fin_cases i <;> decide)
        (by
          intro i hi
          fin_cases i <;> simp [Fin.le_iff_val_le_val]
          exact (hi rfl).elim)
        (by norm_num)
    _ = (bottleneck9BiSpectralGapCertificate : ℝ) := by
      norm_num [bottleneck9BiSpectralGapCertificate]

/-- Certificate-vs-actual-gap upper-bound discharge for `bottleneck9_bi`. -/
theorem bottleneck9_bi_certificate_discharge :
    bottleneck9_bi.spectralGap (by norm_num : 2 ≤ 9) ≤
      (bottleneck9BiSpectralGapCertificate : ℝ) :=
  bottleneck9_bi_spectralGap_le_certificate


end Legitimacy
