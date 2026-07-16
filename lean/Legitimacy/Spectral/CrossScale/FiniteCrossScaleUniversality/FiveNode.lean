/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.Core

/-!
# Five-Node Cross-Scale Spectral Certificates

Five-node spectral-gap, consistency-vulnerability, and `S_delta` certificates.
-/

set_option autoImplicit false

namespace Legitimacy

open Matrix BigOperators

/-- Probe-side rational spectral-gap certificate for `uniK5`. -/
def fiveNodeCompleteSpectralGapCertificate : ℚ := 5

/-- Probe-side rational spectral-gap certificate for `asymK5`. -/
def fiveNodeAsymmetricSpectralGapCertificate : ℚ := 5

/-- Conservative rational lower-bound certificate for `nearPath5`. -/
def fiveNodeNearPathSpectralGapCertificate : ℚ := 23 / 50

/-- Conservative rational lower-bound certificate for `wheel5`. -/
def fiveNodeWheelSpectralGapCertificate : ℚ := 1

/-- Probe-side upper certificate for the weak-center bottleneck `bottleneck5`. -/
def fiveNodeBottleneckSpectralGapCertificate : ℚ := 1 / 10000

private lemma uniK5_laplacianR_mulVec (x : Fin 5 → ℝ) (i : Fin 5) :
    (uniK5.laplacianR *ᵥ x) i = 5 * x i - ∑ j : Fin 5, x j := by
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, GovGraph.laplacianR, GovGraph.laplacian,
      GovGraph.degMatrix, GovGraph.deg, GovGraph.W, uniK5, Fin.sum_univ_succ] <;>
      ring_nf

private lemma uniK5_laplacianR_trace : uniK5.laplacianR.trace = 20 := by
  simp [Matrix.trace, GovGraph.laplacianR, GovGraph.laplacian, GovGraph.degMatrix,
    GovGraph.deg, GovGraph.W, uniK5, Fin.sum_univ_succ]
  ring_nf

private lemma uniK5_eigenvalue_zero_or_five (i : Fin 5) :
    let hA := uniK5.laplacianR_isHermitian
    hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 5 := by
  classical
  intro hA
  let v : Fin 5 → ℝ := ⇑(hA.eigenvectorBasis i)
  let lam : ℝ := hA.eigenvalues i
  have hev_fun : uniK5.laplacianR *ᵥ v = lam • v := by
    simpa [v, lam] using hA.mulVec_eigenvectorBasis i
  by_cases hzero : lam = 0
  · left
    simpa [lam] using hzero
  · right
    have hsum0 : lam * (∑ k : Fin 5, v k) = 0 := by
      have hsum := congrArg (fun y : Fin 5 → ℝ => ∑ k : Fin 5, y k) hev_fun
      simp [Pi.smul_apply, uniK5_laplacianR_mulVec, Fin.sum_univ_succ] at hsum
      calc
        lam * (∑ k : Fin 5, v k) =
            lam * (v 0 + (v 1 + (v 2 + (v 3 + v 4)))) := by
              simp [Fin.sum_univ_succ]
        _ = lam * v 0 + (lam * v 1 + (lam * v 2 + (lam * v 3 + lam * v 4))) := by
              ring
        _ = 0 := hsum.symm
    have hS : ∑ k : Fin 5, v k = 0 :=
      (mul_eq_zero.mp hsum0).resolve_left hzero
    have hv_ne : v ≠ 0 := by
      intro hv
      have hnorm := hA.eigenvectorBasis.norm_eq_one i
      have : hA.eigenvectorBasis i = 0 := by
        ext k
        exact congrFun hv k
      rw [this, norm_zero] at hnorm
      norm_num at hnorm
    have hex : ∃ k : Fin 5, v k ≠ 0 := by
      by_contra h
      apply hv_ne
      ext k
      by_contra hk
      exact h ⟨k, hk⟩
    rcases hex with ⟨k, hvk⟩
    have hrow := congrFun hev_fun k
    rw [uniK5_laplacianR_mulVec, hS] at hrow
    simp [Pi.smul_apply] at hrow
    rcases hrow with h | h
    · linarith
    · exact False.elim (hvk h)

private lemma uniK5_eigenvalue0_zero_or_five
    (i : Fin (Fintype.card (Fin 5))) :
    let hA := uniK5.laplacianR_isHermitian
    hA.eigenvalues₀ i = 0 ∨ hA.eigenvalues₀ i = 5 := by
  intro hA
  let e : Fin (Fintype.card (Fin 5)) ≃ Fin 5 :=
    Fintype.equivOfCardEq (by simp)
  have h := uniK5_eigenvalue_zero_or_five (e i)
  simpa [Matrix.IsHermitian.eigenvalues, hA, e] using h

private lemma uniK5_sum_eigenvalues0 :
    ∑ i : Fin (Fintype.card (Fin 5)),
      uniK5.laplacianR_isHermitian.eigenvalues₀ i = 20 := by
  let hA := uniK5.laplacianR_isHermitian
  have htrace := hA.trace_eq_sum_eigenvalues
  rw [uniK5_laplacianR_trace] at htrace
  let e : Fin (Fintype.card (Fin 5)) ≃ Fin 5 :=
    Fintype.equivOfCardEq (by simp)
  have hsum : (∑ i : Fin 5, hA.eigenvalues i) =
      ∑ i : Fin (Fintype.card (Fin 5)), hA.eigenvalues₀ i := by
    rw [← e.symm.sum_comp (fun i => hA.eigenvalues₀ i)]
    simp [Matrix.IsHermitian.eigenvalues, e]
  rw [← hsum]
  exact htrace.symm
/-- Actual Mathlib spectral-gap discharge for the uniform complete five-node
archetype. This proves that the probe-side certificate `5` is the true
second-smallest Laplacian eigenvalue of `uniK5`. -/
theorem uniK5_spectralGap_eq_certificate :
    uniK5.spectralGap (by norm_num : 2 ≤ 5) =
      (fiveNodeCompleteSpectralGapCertificate : ℝ) := by
  let hA := uniK5.laplacianR_isHermitian
  unfold GovGraph.spectralGap
  change hA.eigenvalues₀ (3 : Fin 5) = 5
  simpa [fiveNodeCompleteSpectralGapCertificate] using
    uniformK_spectralGap_eq
      (f := fun i : Fin 5 => hA.eigenvalues₀ i)
      (gap := (3 : Fin 5)) (last := (4 : Fin 5))
      (gapValue := 5) (total := 20)
      (by intro i; simpa using uniK5_eigenvalue0_zero_or_five i)
      (by simpa using uniK5_sum_eigenvalues0)
      (by intro i; exact GovGraph.eigenvalues_nonneg uniK5 i)
      (by intro i j hij; exact Matrix.IsHermitian.eigenvalues₀_antitone hA hij)
      (by decide)
      (by norm_num)
      (by simp [Fin.sum_univ_succ]; norm_num)

/-- Certificate-vs-actual-gap lower-bound discharge for `uniK5`. -/
theorem uniK5_certificate_discharge :
    (fiveNodeCompleteSpectralGapCertificate : ℝ) ≤
      uniK5.spectralGap (by norm_num : 2 ≤ 5) := by
  rw [uniK5_spectralGap_eq_certificate]

/-- Pending actual-gap discharge for the asymmetric five-node complete graph. -/
def asymK5_certificate_discharge_pending : Prop :=
  (fiveNodeAsymmetricSpectralGapCertificate : ℝ) ≤
    asymK5.spectralGap (by norm_num : 2 ≤ 5)

/-- Pending actual-gap discharge for the five-node near-path graph. -/
def nearPath5_certificate_discharge_pending : Prop :=
  (fiveNodeNearPathSpectralGapCertificate : ℝ) ≤
    nearPath5.spectralGap (by norm_num : 2 ≤ 5)

/-- Pending actual-gap discharge for the five-node wheel graph. -/
def wheel5_certificate_discharge_pending : Prop :=
  (fiveNodeWheelSpectralGapCertificate : ℝ) ≤
    wheel5.spectralGap (by norm_num : 2 ≤ 5)

private def bottleneck5SeparatorVectorQ : Fin 5 → ℚ := ![1, 1, 0, -1, -1]

private def bottleneck5SeparatorVectorR : Fin 5 → ℝ :=
  fun i => (bottleneck5SeparatorVectorQ i : ℝ)

private def bottleneck5ConstantVectorQ : Fin 5 → ℚ := ![1, 1, 1, 1, 1]

private def bottleneck5ConstantVectorR : Fin 5 → ℝ :=
  fun i => (bottleneck5ConstantVectorQ i : ℝ)

-- native_decide: finite rational Laplacian-vector identities and exact
-- certificate value checks for the concrete archetype family.

private lemma bottleneck5_laplacian_mulVec_separatorQ :
    bottleneck5.laplacian *ᵥ bottleneck5SeparatorVectorQ =
      (1 / 10000 : ℚ) • bottleneck5SeparatorVectorQ := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  native_decide

private lemma bottleneck5_laplacian_mulVec_constantQ :
    bottleneck5.laplacian *ᵥ bottleneck5ConstantVectorQ =
      (0 : ℚ) • bottleneck5ConstantVectorQ := by
  native_decide

private lemma bottleneck5_laplacianR_mulVec_separator :
    bottleneck5.laplacianR *ᵥ bottleneck5SeparatorVectorR =
      (1 / 10000 : ℝ) • bottleneck5SeparatorVectorR := by
  ext i
  have h := congrFun bottleneck5_laplacian_mulVec_separatorQ i
  simp [Matrix.mulVec, dotProduct] at h
  have hq : (∑ x, bottleneck5.laplacian i x * bottleneck5SeparatorVectorQ x) =
      (1 / 10000 : ℚ) * bottleneck5SeparatorVectorQ i := by
    simpa using h
  have hR : ((∑ x, bottleneck5.laplacian i x *
        bottleneck5SeparatorVectorQ x : ℚ) : ℝ) =
      (((1 / 10000 : ℚ) * bottleneck5SeparatorVectorQ i : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa [GovGraph.laplacianR, Matrix.mulVec, dotProduct,
    bottleneck5SeparatorVectorR] using hR

private lemma bottleneck5_laplacianR_mulVec_constant :
    bottleneck5.laplacianR *ᵥ bottleneck5ConstantVectorR =
      (0 : ℝ) • bottleneck5ConstantVectorR := by
  ext i
  have h := congrFun bottleneck5_laplacian_mulVec_constantQ i
  simp [Matrix.mulVec, dotProduct] at h
  have hq : (∑ x, bottleneck5.laplacian i x * bottleneck5ConstantVectorQ x) =
      (0 : ℚ) * bottleneck5ConstantVectorQ i := by
    simpa using h
  have hR : ((∑ x, bottleneck5.laplacian i x *
        bottleneck5ConstantVectorQ x : ℚ) : ℝ) =
      (((0 : ℚ) * bottleneck5ConstantVectorQ i : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa [GovGraph.laplacianR, Matrix.mulVec, dotProduct,
    bottleneck5ConstantVectorR] using hR

private lemma bottleneck5SeparatorVectorR_ne_zero :
    bottleneck5SeparatorVectorR ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [bottleneck5SeparatorVectorR, bottleneck5SeparatorVectorQ] at this

private lemma bottleneck5ConstantVectorR_ne_zero :
    bottleneck5ConstantVectorR ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [bottleneck5ConstantVectorR, bottleneck5ConstantVectorQ] at this

private lemma bottleneck5_eigenvalue_exists_of_mulVec
    (mu : ℝ) (v : Fin 5 → ℝ) (hv : v ≠ 0)
    (hmul : bottleneck5.laplacianR *ᵥ v = mu • v) :
    ∃ i : Fin (Fintype.card (Fin 5)),
      bottleneck5.laplacianR_isHermitian.eigenvalues₀ i = mu := by
  let hA := bottleneck5.laplacianR_isHermitian
  have hev : Module.End.HasEigenvalue
      (Matrix.toLin' bottleneck5.laplacianR : Module.End ℝ (Fin 5 → ℝ)) mu := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    rw [Module.End.hasEigenvector_iff]
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      simpa [Matrix.toLin'_apply] using hmul
    · exact hv
  have hspectrum : mu ∈ spectrum ℝ bottleneck5.laplacianR := by
    rw [← Matrix.spectrum_toLin']
    exact Module.End.HasEigenvalue.mem_spectrum hev
  have hrange : mu ∈ Set.range hA.eigenvalues := by
    simpa [hA.spectrum_real_eq_range_eigenvalues] using hspectrum
  rcases hrange with ⟨i, hi⟩
  refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin 5)).symm i, ?_⟩
  simpa [Matrix.IsHermitian.eigenvalues, hA] using hi

private lemma bottleneck5_zero_eigenvalue_exists :
    ∃ i : Fin (Fintype.card (Fin 5)),
      bottleneck5.laplacianR_isHermitian.eigenvalues₀ i = 0 :=
  bottleneck5_eigenvalue_exists_of_mulVec 0 bottleneck5ConstantVectorR
    bottleneck5ConstantVectorR_ne_zero bottleneck5_laplacianR_mulVec_constant

private lemma bottleneck5_separator_eigenvalue_exists :
    ∃ i : Fin (Fintype.card (Fin 5)),
      bottleneck5.laplacianR_isHermitian.eigenvalues₀ i = (1 / 10000 : ℝ) :=
  bottleneck5_eigenvalue_exists_of_mulVec (1 / 10000) bottleneck5SeparatorVectorR
    bottleneck5SeparatorVectorR_ne_zero bottleneck5_laplacianR_mulVec_separator

/-- Actual spectral-gap upper-bound discharge for the five-node bottleneck
archetype. The separating test mode is a true Laplacian eigenvector with
eigenvalue `1 / 10000`; since the constant mode gives eigenvalue `0` and
Laplacian eigenvalues are nonnegative, the second-smallest eigenvalue is at
most that separator eigenvalue. -/
theorem bottleneck5_spectralGap_le_certificate :
    bottleneck5.spectralGap (by norm_num : 2 ≤ 5) ≤
      (fiveNodeBottleneckSpectralGapCertificate : ℝ) := by
  let hA := bottleneck5.laplacianR_isHermitian
  unfold GovGraph.spectralGap
  change hA.eigenvalues₀ (3 : Fin 5) ≤
    (fiveNodeBottleneckSpectralGapCertificate : ℝ)
  calc
    hA.eigenvalues₀ (3 : Fin 5) ≤ (1 / 10000 : ℝ) :=
      bottleneck_spectralGap_le
        (f := fun i : Fin 5 => hA.eigenvalues₀ i)
        (gap := (3 : Fin 5)) (last := (4 : Fin 5))
        (cert := (1 / 10000 : ℝ))
        bottleneck5_zero_eigenvalue_exists
        bottleneck5_separator_eigenvalue_exists
        (by intro i; exact GovGraph.eigenvalues_nonneg bottleneck5 i)
        (by intro i j hij; exact Matrix.IsHermitian.eigenvalues₀_antitone hA hij)
        (by intro i; fin_cases i <;> decide)
        (by
          intro i hi
          fin_cases i <;> simp [Fin.le_iff_val_le_val]
          exact (hi rfl).elim)
        (by norm_num)
    _ = (fiveNodeBottleneckSpectralGapCertificate : ℝ) := by
      norm_num [fiveNodeBottleneckSpectralGapCertificate]

/-- Certificate-vs-actual-gap upper-bound discharge for `bottleneck5`. -/
theorem bottleneck5_certificate_discharge :
    bottleneck5.spectralGap (by norm_num : 2 ≤ 5) ≤
      (fiveNodeBottleneckSpectralGapCertificate : ℝ) :=
  bottleneck5_spectralGap_le_certificate

/-- Exact consistency-vulnerability values for the five-node witnesses. -/
theorem fiveNode_cv_values :
    uniK5.cv sig5 = 3 / 4 ∧
    asymK5.cv sig5 = 6 / 5 ∧
    nearPath5.cv sig5 = 100 / 53 ∧
    wheel5.cv sig5 = 5 / 2 ∧
    bottleneck5.cv sig5 = 20000 / 10001 := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  repeat' constructor <;> native_decide

/-- Probe-side `S_delta = lambda_2 * CV` certificate for `uniK5`. -/
def fiveNodeCompleteSDeltaCertificate : ℚ :=
  fiveNodeCompleteSpectralGapCertificate * uniK5.cv sig5

/-- Probe-side `S_delta = lambda_2 * CV` certificate for `asymK5`. -/
def fiveNodeAsymmetricSDeltaCertificate : ℚ :=
  fiveNodeAsymmetricSpectralGapCertificate * asymK5.cv sig5

/-- Probe-side `S_delta = lambda_2 * CV` certificate for `nearPath5`. -/
def fiveNodeNearPathSDeltaCertificate : ℚ :=
  fiveNodeNearPathSpectralGapCertificate * nearPath5.cv sig5

/-- Probe-side `S_delta = lambda_2 * CV` certificate for `wheel5`. -/
def fiveNodeWheelSDeltaCertificate : ℚ :=
  fiveNodeWheelSpectralGapCertificate * wheel5.cv sig5

/-- Probe-side `S_delta = lambda_2 * CV` certificate for `bottleneck5`. -/
def fiveNodeBottleneckSDeltaCertificate : ℚ :=
  fiveNodeBottleneckSpectralGapCertificate * bottleneck5.cv sig5

/-- Exact rational `S_delta` certificate values for the five-node witnesses. -/
theorem fiveNode_sdelta_certificate_values :
    fiveNodeCompleteSDeltaCertificate = 15 / 4 ∧
    fiveNodeAsymmetricSDeltaCertificate = 6 ∧
    fiveNodeNearPathSDeltaCertificate = 46 / 53 ∧
    fiveNodeWheelSDeltaCertificate = 5 / 2 ∧
    fiveNodeBottleneckSDeltaCertificate = 2 / 10001 := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  repeat' constructor <;> native_decide


end Legitimacy
