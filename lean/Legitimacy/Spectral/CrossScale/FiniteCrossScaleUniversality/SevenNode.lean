/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.Core

/-!
# Seven-Node Cross-Scale Spectral Certificates

Seven-node spectral-gap, consistency-vulnerability, and `S_delta` certificates.
-/

set_option autoImplicit false

namespace Legitimacy

open Matrix BigOperators

/-- Probe-side rational spectral-gap certificate for `uniK7`. -/
def sevenNodeCompleteSpectralGapCertificate : ℚ := 7

/-- Probe-side rational spectral-gap certificate for `asymK7`. -/
def sevenNodeAsymmetricSpectralGapCertificate : ℚ := 7

/-- Conservative rational lower-bound certificate for `nearPath7`. -/
def sevenNodeNearPathSpectralGapCertificate : ℚ := 8 / 25

/-- Probe-side upper certificate for the bi-clique bottleneck `bottleneck7_bi`. -/
def sevenNodeBicliqueBottleneckSpectralGapCertificate : ℚ := 1 / 10000

/-- Probe-side upper certificate for the tri-cluster bottleneck `bottleneck7_tri`. -/
def sevenNodeTriclusterBottleneckSpectralGapCertificate : ℚ := 1 / 10000

private lemma uniK7_laplacianR_mulVec (x : Fin 7 → ℝ) (i : Fin 7) :
    (uniK7.laplacianR *ᵥ x) i = 7 * x i - ∑ j : Fin 7, x j := by
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, GovGraph.laplacianR, GovGraph.laplacian,
      GovGraph.degMatrix, GovGraph.deg, GovGraph.W, uniK7, Fin.sum_univ_succ] <;>
      ring_nf

private lemma uniK7_laplacianR_trace : uniK7.laplacianR.trace = 42 := by
  simp [Matrix.trace, GovGraph.laplacianR, GovGraph.laplacian, GovGraph.degMatrix,
    GovGraph.deg, GovGraph.W, uniK7, Fin.sum_univ_succ]
  ring_nf

private lemma uniK7_eigenvalue_zero_or_seven (i : Fin 7) :
    let hA := uniK7.laplacianR_isHermitian
    hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 7 := by
  classical
  intro hA
  let v : Fin 7 → ℝ := ⇑(hA.eigenvectorBasis i)
  let lam : ℝ := hA.eigenvalues i
  have hev_fun : uniK7.laplacianR *ᵥ v = lam • v := by
    simpa [v, lam] using hA.mulVec_eigenvectorBasis i
  by_cases hzero : lam = 0
  · left
    simpa [lam] using hzero
  · right
    have hsum0 : lam * (∑ k : Fin 7, v k) = 0 := by
      have hsum := congrArg (fun y : Fin 7 → ℝ => ∑ k : Fin 7, y k) hev_fun
      simp [Pi.smul_apply, uniK7_laplacianR_mulVec, Fin.sum_univ_succ] at hsum
      calc
        lam * (∑ k : Fin 7, v k) =
            lam * (v 0 + (v 1 + (v 2 + (v 3 + (v 4 + (v 5 + v 6)))))) := by
              simp [Fin.sum_univ_succ]
        _ = lam * v 0 +
              (lam * v 1 +
                (lam * v 2 +
                  (lam * v 3 + (lam * v 4 + (lam * v 5 + lam * v 6))))) := by
              ring
        _ = 0 := hsum.symm
    have hS : ∑ k : Fin 7, v k = 0 :=
      (mul_eq_zero.mp hsum0).resolve_left hzero
    have hv_ne : v ≠ 0 := by
      intro hv
      have hnorm := hA.eigenvectorBasis.norm_eq_one i
      have : hA.eigenvectorBasis i = 0 := by
        ext k
        exact congrFun hv k
      rw [this, norm_zero] at hnorm
      norm_num at hnorm
    have hex : ∃ k : Fin 7, v k ≠ 0 := by
      by_contra h
      apply hv_ne
      ext k
      by_contra hk
      exact h ⟨k, hk⟩
    rcases hex with ⟨k, hvk⟩
    have hrow := congrFun hev_fun k
    rw [uniK7_laplacianR_mulVec, hS] at hrow
    simp [Pi.smul_apply] at hrow
    rcases hrow with h | h
    · linarith
    · exact False.elim (hvk h)

private lemma uniK7_eigenvalue0_zero_or_seven
    (i : Fin (Fintype.card (Fin 7))) :
    let hA := uniK7.laplacianR_isHermitian
    hA.eigenvalues₀ i = 0 ∨ hA.eigenvalues₀ i = 7 := by
  intro hA
  let e : Fin (Fintype.card (Fin 7)) ≃ Fin 7 :=
    Fintype.equivOfCardEq (by simp)
  have h := uniK7_eigenvalue_zero_or_seven (e i)
  simpa [Matrix.IsHermitian.eigenvalues, hA, e] using h

private lemma uniK7_sum_eigenvalues0 :
    ∑ i : Fin (Fintype.card (Fin 7)),
      uniK7.laplacianR_isHermitian.eigenvalues₀ i = 42 := by
  let hA := uniK7.laplacianR_isHermitian
  have htrace := hA.trace_eq_sum_eigenvalues
  rw [uniK7_laplacianR_trace] at htrace
  let e : Fin (Fintype.card (Fin 7)) ≃ Fin 7 :=
    Fintype.equivOfCardEq (by simp)
  have hsum : (∑ i : Fin 7, hA.eigenvalues i) =
      ∑ i : Fin (Fintype.card (Fin 7)), hA.eigenvalues₀ i := by
    rw [← e.symm.sum_comp (fun i => hA.eigenvalues₀ i)]
    simp [Matrix.IsHermitian.eigenvalues, e]
  rw [← hsum]
  exact htrace.symm

/-- Actual Mathlib spectral-gap discharge for the uniform complete seven-node
archetype. -/
theorem uniK7_spectralGap_eq_certificate :
    uniK7.spectralGap (by norm_num : 2 ≤ 7) =
      (sevenNodeCompleteSpectralGapCertificate : ℝ) := by
  let hA := uniK7.laplacianR_isHermitian
  unfold GovGraph.spectralGap
  change hA.eigenvalues₀ (5 : Fin 7) = 7
  simpa [sevenNodeCompleteSpectralGapCertificate] using
    uniformK_spectralGap_eq
      (f := fun i : Fin 7 => hA.eigenvalues₀ i)
      (gap := (5 : Fin 7)) (last := (6 : Fin 7))
      (gapValue := 7) (total := 42)
      (by intro i; simpa using uniK7_eigenvalue0_zero_or_seven i)
      (by simpa using uniK7_sum_eigenvalues0)
      (by intro i; exact GovGraph.eigenvalues_nonneg uniK7 i)
      (by intro i j hij; exact Matrix.IsHermitian.eigenvalues₀_antitone hA hij)
      (by decide)
      (by norm_num)
      (by simp [Fin.sum_univ_succ]; norm_num)

/-- Certificate-vs-actual-gap lower-bound discharge for `uniK7`. -/
theorem uniK7_certificate_discharge :
    (sevenNodeCompleteSpectralGapCertificate : ℝ) ≤
      uniK7.spectralGap (by norm_num : 2 ≤ 7) := by
  rw [uniK7_spectralGap_eq_certificate]

/-- Pending actual-gap discharge for the asymmetric seven-node complete graph. -/
def asymK7_certificate_discharge_pending : Prop :=
  (sevenNodeAsymmetricSpectralGapCertificate : ℝ) ≤
    asymK7.spectralGap (by norm_num : 2 ≤ 7)

/-- Pending actual-gap discharge for the seven-node near-path graph. -/
def nearPath7_certificate_discharge_pending : Prop :=
  (sevenNodeNearPathSpectralGapCertificate : ℝ) ≤
    nearPath7.spectralGap (by norm_num : 2 ≤ 7)

/-- Pending actual-gap discharge for the seven-node biclique bottleneck graph. -/
def bottleneck7_bi_certificate_discharge_pending : Prop :=
  bottleneck7_bi.spectralGap (by norm_num : 2 ≤ 7) ≤
    (sevenNodeBicliqueBottleneckSpectralGapCertificate : ℝ)

private def bottleneck7BiSeparatorVectorQ : Fin 7 → ℚ :=
  ![4, 4, 4, -3, -3, -3, -3]

private def bottleneck7BiSeparatorVectorR : Fin 7 → ℝ :=
  fun i => (bottleneck7BiSeparatorVectorQ i : ℝ)

private def bottleneck7BiConstantVectorQ : Fin 7 → ℚ := ![1, 1, 1, 1, 1, 1, 1]

private def bottleneck7BiConstantVectorR : Fin 7 → ℝ :=
  fun i => (bottleneck7BiConstantVectorQ i : ℝ)

private lemma bottleneck7_bi_laplacian_mulVec_separatorQ :
    bottleneck7_bi.laplacian *ᵥ bottleneck7BiSeparatorVectorQ =
      (1 / 10000 : ℚ) • bottleneck7BiSeparatorVectorQ := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  native_decide

private lemma bottleneck7_bi_laplacian_mulVec_constantQ :
    bottleneck7_bi.laplacian *ᵥ bottleneck7BiConstantVectorQ =
      (0 : ℚ) • bottleneck7BiConstantVectorQ := by
  native_decide

private lemma bottleneck7_bi_laplacianR_mulVec_separator :
    bottleneck7_bi.laplacianR *ᵥ bottleneck7BiSeparatorVectorR =
      (1 / 10000 : ℝ) • bottleneck7BiSeparatorVectorR := by
  ext i
  have h := congrFun bottleneck7_bi_laplacian_mulVec_separatorQ i
  simp [Matrix.mulVec, dotProduct] at h
  have hq : (∑ x, bottleneck7_bi.laplacian i x * bottleneck7BiSeparatorVectorQ x) =
      (1 / 10000 : ℚ) * bottleneck7BiSeparatorVectorQ i := by
    simpa using h
  have hR : ((∑ x, bottleneck7_bi.laplacian i x *
        bottleneck7BiSeparatorVectorQ x : ℚ) : ℝ) =
      (((1 / 10000 : ℚ) * bottleneck7BiSeparatorVectorQ i : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa [GovGraph.laplacianR, Matrix.mulVec, dotProduct,
    bottleneck7BiSeparatorVectorR] using hR

private lemma bottleneck7_bi_laplacianR_mulVec_constant :
    bottleneck7_bi.laplacianR *ᵥ bottleneck7BiConstantVectorR =
      (0 : ℝ) • bottleneck7BiConstantVectorR := by
  ext i
  have h := congrFun bottleneck7_bi_laplacian_mulVec_constantQ i
  simp [Matrix.mulVec, dotProduct] at h
  have hq : (∑ x, bottleneck7_bi.laplacian i x * bottleneck7BiConstantVectorQ x) =
      (0 : ℚ) * bottleneck7BiConstantVectorQ i := by
    simpa using h
  have hR : ((∑ x, bottleneck7_bi.laplacian i x *
        bottleneck7BiConstantVectorQ x : ℚ) : ℝ) =
      (((0 : ℚ) * bottleneck7BiConstantVectorQ i : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa [GovGraph.laplacianR, Matrix.mulVec, dotProduct,
    bottleneck7BiConstantVectorR] using hR

private lemma bottleneck7BiSeparatorVectorR_ne_zero :
    bottleneck7BiSeparatorVectorR ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [bottleneck7BiSeparatorVectorR, bottleneck7BiSeparatorVectorQ] at this

private lemma bottleneck7BiConstantVectorR_ne_zero :
    bottleneck7BiConstantVectorR ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [bottleneck7BiConstantVectorR, bottleneck7BiConstantVectorQ] at this

private lemma bottleneck7_bi_eigenvalue_exists_of_mulVec
    (mu : ℝ) (v : Fin 7 → ℝ) (hv : v ≠ 0)
    (hmul : bottleneck7_bi.laplacianR *ᵥ v = mu • v) :
    ∃ i : Fin (Fintype.card (Fin 7)),
      bottleneck7_bi.laplacianR_isHermitian.eigenvalues₀ i = mu := by
  let hA := bottleneck7_bi.laplacianR_isHermitian
  have hev : Module.End.HasEigenvalue
      (Matrix.toLin' bottleneck7_bi.laplacianR : Module.End ℝ (Fin 7 → ℝ)) mu := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    rw [Module.End.hasEigenvector_iff]
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      simpa [Matrix.toLin'_apply] using hmul
    · exact hv
  have hspectrum : mu ∈ spectrum ℝ bottleneck7_bi.laplacianR := by
    rw [← Matrix.spectrum_toLin']
    exact Module.End.HasEigenvalue.mem_spectrum hev
  have hrange : mu ∈ Set.range hA.eigenvalues := by
    simpa [hA.spectrum_real_eq_range_eigenvalues] using hspectrum
  rcases hrange with ⟨i, hi⟩
  refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin 7)).symm i, ?_⟩
  simpa [Matrix.IsHermitian.eigenvalues, hA] using hi

private lemma bottleneck7_bi_zero_eigenvalue_exists :
    ∃ i : Fin (Fintype.card (Fin 7)),
      bottleneck7_bi.laplacianR_isHermitian.eigenvalues₀ i = 0 :=
  bottleneck7_bi_eigenvalue_exists_of_mulVec 0 bottleneck7BiConstantVectorR
    bottleneck7BiConstantVectorR_ne_zero bottleneck7_bi_laplacianR_mulVec_constant

private lemma bottleneck7_bi_separator_eigenvalue_exists :
    ∃ i : Fin (Fintype.card (Fin 7)),
      bottleneck7_bi.laplacianR_isHermitian.eigenvalues₀ i = (1 / 10000 : ℝ) :=
  bottleneck7_bi_eigenvalue_exists_of_mulVec (1 / 10000) bottleneck7BiSeparatorVectorR
    bottleneck7BiSeparatorVectorR_ne_zero bottleneck7_bi_laplacianR_mulVec_separator

/-- Actual spectral-gap upper-bound discharge for the seven-node bi-cluster
bottleneck archetype. -/
theorem bottleneck7_bi_spectralGap_le_certificate :
    bottleneck7_bi.spectralGap (by norm_num : 2 ≤ 7) ≤
      (sevenNodeBicliqueBottleneckSpectralGapCertificate : ℝ) := by
  let hA := bottleneck7_bi.laplacianR_isHermitian
  unfold GovGraph.spectralGap
  change hA.eigenvalues₀ (5 : Fin 7) ≤
    (sevenNodeBicliqueBottleneckSpectralGapCertificate : ℝ)
  calc
    hA.eigenvalues₀ (5 : Fin 7) ≤ (1 / 10000 : ℝ) :=
      bottleneck_spectralGap_le
        (f := fun i : Fin 7 => hA.eigenvalues₀ i)
        (gap := (5 : Fin 7)) (last := (6 : Fin 7))
        (cert := (1 / 10000 : ℝ))
        bottleneck7_bi_zero_eigenvalue_exists
        bottleneck7_bi_separator_eigenvalue_exists
        (by intro i; exact GovGraph.eigenvalues_nonneg bottleneck7_bi i)
        (by intro i j hij; exact Matrix.IsHermitian.eigenvalues₀_antitone hA hij)
        (by intro i; fin_cases i <;> decide)
        (by
          intro i hi
          fin_cases i <;> simp [Fin.le_iff_val_le_val]
          exact (hi rfl).elim)
        (by norm_num)
    _ = (sevenNodeBicliqueBottleneckSpectralGapCertificate : ℝ) := by
      norm_num [sevenNodeBicliqueBottleneckSpectralGapCertificate]

/-- Certificate-vs-actual-gap upper-bound discharge for `bottleneck7_bi`. -/
theorem bottleneck7_bi_certificate_discharge :
    bottleneck7_bi.spectralGap (by norm_num : 2 ≤ 7) ≤
      (sevenNodeBicliqueBottleneckSpectralGapCertificate : ℝ) :=
  bottleneck7_bi_spectralGap_le_certificate

/-- Pending actual-gap discharge for the seven-node tricluster bottleneck graph. -/
def bottleneck7_tri_certificate_discharge_pending : Prop :=
  bottleneck7_tri.spectralGap (by norm_num : 2 ≤ 7) ≤
    (sevenNodeTriclusterBottleneckSpectralGapCertificate : ℝ)

private def bottleneck7TriSeparatorVectorQ : Fin 7 → ℚ :=
  ![2, 2, 2, -3, -3, 0, 0]

private def bottleneck7TriSeparatorVectorR : Fin 7 → ℝ :=
  fun i => (bottleneck7TriSeparatorVectorQ i : ℝ)

private def bottleneck7TriConstantVectorQ : Fin 7 → ℚ := ![1, 1, 1, 1, 1, 1, 1]

private def bottleneck7TriConstantVectorR : Fin 7 → ℝ :=
  fun i => (bottleneck7TriConstantVectorQ i : ℝ)

private lemma bottleneck7_tri_laplacian_mulVec_separatorQ :
    bottleneck7_tri.laplacian *ᵥ bottleneck7TriSeparatorVectorQ =
      (1 / 10000 : ℚ) • bottleneck7TriSeparatorVectorQ := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  native_decide

private lemma bottleneck7_tri_laplacian_mulVec_constantQ :
    bottleneck7_tri.laplacian *ᵥ bottleneck7TriConstantVectorQ =
      (0 : ℚ) • bottleneck7TriConstantVectorQ := by
  native_decide

private lemma bottleneck7_tri_laplacianR_mulVec_separator :
    bottleneck7_tri.laplacianR *ᵥ bottleneck7TriSeparatorVectorR =
      (1 / 10000 : ℝ) • bottleneck7TriSeparatorVectorR := by
  ext i
  have h := congrFun bottleneck7_tri_laplacian_mulVec_separatorQ i
  simp [Matrix.mulVec, dotProduct] at h
  have hq : (∑ x, bottleneck7_tri.laplacian i x * bottleneck7TriSeparatorVectorQ x) =
      (1 / 10000 : ℚ) * bottleneck7TriSeparatorVectorQ i := by
    simpa using h
  have hR : ((∑ x, bottleneck7_tri.laplacian i x *
        bottleneck7TriSeparatorVectorQ x : ℚ) : ℝ) =
      (((1 / 10000 : ℚ) * bottleneck7TriSeparatorVectorQ i : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa [GovGraph.laplacianR, Matrix.mulVec, dotProduct,
    bottleneck7TriSeparatorVectorR] using hR

private lemma bottleneck7_tri_laplacianR_mulVec_constant :
    bottleneck7_tri.laplacianR *ᵥ bottleneck7TriConstantVectorR =
      (0 : ℝ) • bottleneck7TriConstantVectorR := by
  ext i
  have h := congrFun bottleneck7_tri_laplacian_mulVec_constantQ i
  simp [Matrix.mulVec, dotProduct] at h
  have hq : (∑ x, bottleneck7_tri.laplacian i x * bottleneck7TriConstantVectorQ x) =
      (0 : ℚ) * bottleneck7TriConstantVectorQ i := by
    simpa using h
  have hR : ((∑ x, bottleneck7_tri.laplacian i x *
        bottleneck7TriConstantVectorQ x : ℚ) : ℝ) =
      (((0 : ℚ) * bottleneck7TriConstantVectorQ i : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa [GovGraph.laplacianR, Matrix.mulVec, dotProduct,
    bottleneck7TriConstantVectorR] using hR

private lemma bottleneck7TriSeparatorVectorR_ne_zero :
    bottleneck7TriSeparatorVectorR ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [bottleneck7TriSeparatorVectorR, bottleneck7TriSeparatorVectorQ] at this

private lemma bottleneck7TriConstantVectorR_ne_zero :
    bottleneck7TriConstantVectorR ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [bottleneck7TriConstantVectorR, bottleneck7TriConstantVectorQ] at this

private lemma bottleneck7_tri_eigenvalue_exists_of_mulVec
    (mu : ℝ) (v : Fin 7 → ℝ) (hv : v ≠ 0)
    (hmul : bottleneck7_tri.laplacianR *ᵥ v = mu • v) :
    ∃ i : Fin (Fintype.card (Fin 7)),
      bottleneck7_tri.laplacianR_isHermitian.eigenvalues₀ i = mu := by
  let hA := bottleneck7_tri.laplacianR_isHermitian
  have hev : Module.End.HasEigenvalue
      (Matrix.toLin' bottleneck7_tri.laplacianR : Module.End ℝ (Fin 7 → ℝ)) mu := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    rw [Module.End.hasEigenvector_iff]
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      simpa [Matrix.toLin'_apply] using hmul
    · exact hv
  have hspectrum : mu ∈ spectrum ℝ bottleneck7_tri.laplacianR := by
    rw [← Matrix.spectrum_toLin']
    exact Module.End.HasEigenvalue.mem_spectrum hev
  have hrange : mu ∈ Set.range hA.eigenvalues := by
    simpa [hA.spectrum_real_eq_range_eigenvalues] using hspectrum
  rcases hrange with ⟨i, hi⟩
  refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin 7)).symm i, ?_⟩
  simpa [Matrix.IsHermitian.eigenvalues, hA] using hi

private lemma bottleneck7_tri_zero_eigenvalue_exists :
    ∃ i : Fin (Fintype.card (Fin 7)),
      bottleneck7_tri.laplacianR_isHermitian.eigenvalues₀ i = 0 :=
  bottleneck7_tri_eigenvalue_exists_of_mulVec 0 bottleneck7TriConstantVectorR
    bottleneck7TriConstantVectorR_ne_zero bottleneck7_tri_laplacianR_mulVec_constant

private lemma bottleneck7_tri_separator_eigenvalue_exists :
    ∃ i : Fin (Fintype.card (Fin 7)),
      bottleneck7_tri.laplacianR_isHermitian.eigenvalues₀ i = (1 / 10000 : ℝ) :=
  bottleneck7_tri_eigenvalue_exists_of_mulVec (1 / 10000) bottleneck7TriSeparatorVectorR
    bottleneck7TriSeparatorVectorR_ne_zero bottleneck7_tri_laplacianR_mulVec_separator

/-- Actual spectral-gap upper-bound discharge for the seven-node tri-cluster
bottleneck archetype. -/
theorem bottleneck7_tri_spectralGap_le_certificate :
    bottleneck7_tri.spectralGap (by norm_num : 2 ≤ 7) ≤
      (sevenNodeTriclusterBottleneckSpectralGapCertificate : ℝ) := by
  let hA := bottleneck7_tri.laplacianR_isHermitian
  unfold GovGraph.spectralGap
  change hA.eigenvalues₀ (5 : Fin 7) ≤
    (sevenNodeTriclusterBottleneckSpectralGapCertificate : ℝ)
  calc
    hA.eigenvalues₀ (5 : Fin 7) ≤ (1 / 10000 : ℝ) :=
      bottleneck_spectralGap_le
        (f := fun i : Fin 7 => hA.eigenvalues₀ i)
        (gap := (5 : Fin 7)) (last := (6 : Fin 7))
        (cert := (1 / 10000 : ℝ))
        bottleneck7_tri_zero_eigenvalue_exists
        bottleneck7_tri_separator_eigenvalue_exists
        (by intro i; exact GovGraph.eigenvalues_nonneg bottleneck7_tri i)
        (by intro i j hij; exact Matrix.IsHermitian.eigenvalues₀_antitone hA hij)
        (by intro i; fin_cases i <;> decide)
        (by
          intro i hi
          fin_cases i <;> simp [Fin.le_iff_val_le_val]
          exact (hi rfl).elim)
        (by norm_num)
    _ = (sevenNodeTriclusterBottleneckSpectralGapCertificate : ℝ) := by
      norm_num [sevenNodeTriclusterBottleneckSpectralGapCertificate]

/-- Certificate-vs-actual-gap upper-bound discharge for `bottleneck7_tri`. -/
theorem bottleneck7_tri_certificate_discharge :
    bottleneck7_tri.spectralGap (by norm_num : 2 ≤ 7) ≤
      (sevenNodeTriclusterBottleneckSpectralGapCertificate : ℝ) :=
  bottleneck7_tri_spectralGap_le_certificate

/-- Exact consistency-vulnerability values for the seven-node canonical witnesses. -/
theorem sevenNode_cv_values :
    uniK7.cv sig7 = 2 / 3 ∧
    asymK7.cv sig7 = 8 / 7 ∧
    nearPath7.cv sig7 = 30 / 11 ∧
    bottleneck7_bi.cv sig7 = 612578750 / 612552501 ∧
    bottleneck7_tri.cv sig7 = 56000 / 14001 := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  repeat' constructor <;> native_decide

/-- Probe-side `S_delta = lambda_2 * CV` certificate for `uniK7`. -/
def sevenNodeCompleteSDeltaCertificate : ℚ :=
  sevenNodeCompleteSpectralGapCertificate * uniK7.cv sig7

/-- Probe-side `S_delta = lambda_2 * CV` certificate for `asymK7`. -/
def sevenNodeAsymmetricSDeltaCertificate : ℚ :=
  sevenNodeAsymmetricSpectralGapCertificate * asymK7.cv sig7

/-- Probe-side `S_delta = lambda_2 * CV` certificate for `nearPath7`. -/
def sevenNodeNearPathSDeltaCertificate : ℚ :=
  sevenNodeNearPathSpectralGapCertificate * nearPath7.cv sig7

/-- Probe-side `S_delta = lambda_2 * CV` certificate for `bottleneck7_bi`. -/
def sevenNodeBicliqueBottleneckSDeltaCertificate : ℚ :=
  sevenNodeBicliqueBottleneckSpectralGapCertificate * bottleneck7_bi.cv sig7

/-- Probe-side `S_delta = lambda_2 * CV` certificate for `bottleneck7_tri`. -/
def sevenNodeTriclusterBottleneckSDeltaCertificate : ℚ :=
  sevenNodeTriclusterBottleneckSpectralGapCertificate * bottleneck7_tri.cv sig7

/-- Exact rational `S_delta` certificate values for the seven-node witnesses. -/
theorem sevenNode_sdelta_certificate_values :
    sevenNodeCompleteSDeltaCertificate = 14 / 3 ∧
    sevenNodeAsymmetricSDeltaCertificate = 8 ∧
    sevenNodeNearPathSDeltaCertificate = 48 / 55 ∧
    sevenNodeBicliqueBottleneckSDeltaCertificate = 490063 / 4900420008 ∧
    sevenNodeTriclusterBottleneckSDeltaCertificate = 28 / 70005 := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  repeat' constructor <;> native_decide

end Legitimacy
