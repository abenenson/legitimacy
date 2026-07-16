/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.OpNormEigenvalue
import Legitimacy.Spectral.ASIEmbedding.ContinuousOperatorSignature

/-!
# Legitimacy.Spectral.ASIEmbedding.CompactSpectralBridge

Smoke-test bridge from Legitimacy's continuous-operator spectral signatures to
the standalone compact-spectral substrate.
-/

set_option autoImplicit false

namespace Legitimacy

namespace ASIEmbedding

/-- A `ContinuousOperatorSpectralSignature` has a nontrivial Hilbert carrier,
because it includes a nonzero stationary eigenvector. -/
private theorem continuousOperatorSpectralSignature_nontrivial
    (sig : ContinuousOperatorSpectralSignature) :
    Nontrivial sig.E :=
  nontrivial_of_ne sig.v_top 0 sig.v_top_ne

/-- Compact-spectral smoke test: the compact self-adjoint operator in a
Legitimacy continuous spectral signature has an eigenvalue whose modulus
attains the operator norm.

This is the direct bridge to
`CompactSelfAdjoint.exists_hasEigenvector_norm_eq_opNorm_of_isCompactOperator_of_isSelfAdjoint`.
-/
theorem ContinuousOperatorSpectralSignature.exists_opNorm_eigenvalue
    (sig : ContinuousOperatorSpectralSignature) :
    ∃ μ : ℝ, ∃ v : sig.E,
      Module.End.HasEigenvector (sig.T : sig.E →ₗ[ℝ] sig.E) μ v ∧
        ‖μ‖ = ‖sig.T‖ := by
  haveI : Nontrivial sig.E :=
    continuousOperatorSpectralSignature_nontrivial sig
  exact
    CompactSelfAdjoint.exists_hasEigenvector_norm_eq_opNorm_of_isCompactOperator_of_isSelfAdjoint
      (𝕜 := ℝ) (E := sig.E) sig.T sig.isSelfAdjoint sig.isCompact

/-- Gap-carrying version of the compact-spectral bridge.  Stage 3 can replace
the positive-gap conjunct with a concrete operator-norm formula; stage 2 only
certifies that the compact self-adjoint theorem is available on the signature. -/
theorem ContinuousOperatorSpectralSignature.gap_pos_and_exists_opNorm_eigenvalue
    (sig : ContinuousOperatorSpectralSignature) :
    0 < sig.gap ∧
      ∃ μ : ℝ, ∃ v : sig.E,
        Module.End.HasEigenvector (sig.T : sig.E →ₗ[ℝ] sig.E) μ v ∧
          ‖μ‖ = ‖sig.T‖ :=
  ⟨sig.gap_pos, sig.exists_opNorm_eigenvalue⟩

/-- The finite Bool counting-kernel gap surface agrees with the continuous
operator-norm `cvOp` for the corresponding rank-2 continuous operator
signature in the signed-eigenvalue regime. -/
theorem boolCountingKernel_measureTheoretic_to_continuousOperator_cv
    {g δ : ℚ} {target : ℚ × ℚ}
    (hmt :
      MeasureTheoreticSpectralSignature
        (MeasureTheory.Measure.count : MeasureTheory.Measure Bool)
        (countingDiagonalMassKernel g) g δ target)
    (hg1 : g < 1) :
    operatorSpectralGap (twoStateCountingKernel g) =
      cvOp (twoStateCountingKernelContinuousSignature g hmt.diagonal_parameter_pos) := by
  rw [twoStateCountingKernel_operatorSpectralGap_eq g hmt.diagonal_parameter_pos]
  rw [cvOp_twoStateCountingKernelContinuousSignature_eq g
    hmt.diagonal_parameter_pos hg1]

theorem twoStateCountingKernel_nontrivial_mem_spectrum
    (g : ℚ) (hg : 0 < g) :
    countingSpectralKernelNontrivialEigenvalue g ∈
      spectrum ℝ (twoStateCountingKernelCLM g) := by
  rw [ContinuousLinearMap.spectrum_eq]
  rcases twoStateCountingKernel_gap_witness g hg with
    ⟨v_gap, hv_gap_ne, _hv_gap_orth, hv_gap_eq⟩
  have hv_gap_eq' :
      twoStateCountingKernelCLM g v_gap =
        countingSpectralKernelNontrivialEigenvalue g • v_gap := by
    rw [← twoStateCountingKernel_one_sub_gap_eq_nontrivialEigenvalue g hg]
    exact hv_gap_eq
  exact
    (Module.End.hasEigenvalue_of_hasEigenvector
      (f := (twoStateCountingKernelCLM g :
        EuclideanSpace ℝ Bool →ₗ[ℝ] EuclideanSpace ℝ Bool))
      (x := v_gap)
      (by
        refine Module.End.hasEigenvector_iff.mpr ?_
        refine ⟨?_, hv_gap_ne⟩
        rw [Module.End.mem_eigenspace_iff]
        exact hv_gap_eq')).mem_spectrum

theorem twoStateCountingKernelCLM_spectrum_eq_pair
    (g : ℚ) (hg : 0 < g) :
    spectrum ℝ (twoStateCountingKernelCLM g) =
      ({1, countingSpectralKernelNontrivialEigenvalue g} : Set ℝ) := by
  ext l
  constructor
  · intro hl
    have hl_set :
        l ∈ countingSpectralKernelOperatorEigenvalueSet g :=
      mem_countingSpectralKernelOperatorEigenvalueSet_of_mem_spectrum hl
    simpa [countingSpectralKernel_operator_eigenvalues g hg] using hl_set
  · intro hl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl
    rcases hl with hl_one | hl_nontrivial
    · simpa [hl_one] using twoStateCountingKernel_top_mem_spectrum g hg
    · simpa [hl_nontrivial] using
        twoStateCountingKernel_nontrivial_mem_spectrum g hg

/-- The Bool counting kernel and rank-2 finite OU diagonal have the same real
spectrum under the nontrivial-eigenvalue substitution. -/
theorem twoStateCountingKernel_ouTruncated_spectrum_eq
    (g : ℚ) (hg : 0 < g) (_hg1 : g < 1) (t : ℝ) (ht : 0 < t)
    (hlambda : (1 - (g : ℝ)) / (1 + (g : ℝ)) = Real.exp (-t)) :
    spectrum ℝ (twoStateCountingKernelContinuousSignature g hg).T =
    spectrum ℝ (ouTruncatedSignature 2 (by norm_num) t ht).T := by
  change spectrum ℝ (twoStateCountingKernelCLM g) =
    spectrum ℝ (ouTruncatedCLM 2 t)
  rw [twoStateCountingKernelCLM_spectrum_eq_pair g hg,
    ouTruncatedCLM_spectrum_eq_range 2 t]
  ext l
  constructor
  · intro hl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl
    rcases hl with hl_one | hl_nontrivial
    · refine ⟨0, ?_⟩
      rw [hl_one]
      norm_num
    · refine ⟨1, ?_⟩
      rw [hl_nontrivial]
      simpa [countingSpectralKernelNontrivialEigenvalue] using hlambda.symm
  · intro hl
    rcases hl with ⟨k, rfl⟩
    fin_cases k
    · left
      norm_num
    · right
      simpa [countingSpectralKernelNontrivialEigenvalue] using hlambda.symm

end ASIEmbedding

end Legitimacy
