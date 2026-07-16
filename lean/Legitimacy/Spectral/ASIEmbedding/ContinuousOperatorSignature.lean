/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.OpNormEigenvalue
import Legitimacy.Spectral.ASIEmbedding.MeasureTheoretic

/-!
# Legitimacy.Spectral.ASIEmbedding.ContinuousOperatorSignature

Operator-level spectral substrate for ASI spectral embeddings.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace

open MeasureTheory

namespace Legitimacy

namespace ASIEmbedding

/-- Operator-level spectral signature.

The carrier is an abstract real Hilbert space, the operator is compact and
self-adjoint in Mathlib's adjoint-backed sense, and the top stationary witness
pins the eigenvalue `1`. -/
structure ContinuousOperatorSpectralSignature where
  E : Type*
  [normedAddCommGroup : NormedAddCommGroup E]
  [innerProduct : InnerProductSpace ℝ E]
  [completeSpace : CompleteSpace E]
  T : E →L[ℝ] E
  isCompact : IsCompactOperator T
  isSelfAdjoint : IsSelfAdjoint T
  v_top : E
  v_top_ne : v_top ≠ 0
  T_v_top : T v_top = v_top
  gap : ℝ
  gap_pos : 0 < gap

attribute [instance] ContinuousOperatorSpectralSignature.normedAddCommGroup
attribute [instance] ContinuousOperatorSpectralSignature.innerProduct
attribute [instance] ContinuousOperatorSpectralSignature.completeSpace

/-- Witness-style operator spectral gap predicate.

The existing two-state counting kernel certifies the right-edge spectral gap
`1 - λ₂ = 2g/(1+g)`.  For the ASI parameters already present in the repository,
`g` can be greater than `1`, so the nontrivial eigenvalue can be negative and
the stronger absolute bound `|λ| ≤ 1 - gap` would be false.  This predicate
therefore records the right-edge spectral statement: `1` is spectral, there is
a nonstationary witness at `1 - gap`, and every other spectral value is at most
`1 - gap`.

The explicit nonstationary witness rules out the constant-operator floor case,
where a positive gap would otherwise be vacuous.  The absolute bound is the
additional stage-3 strengthening needed for an operator-norm statement on the
orthogonal complement of the stationary line. -/
structure OperatorSpectralGapPredicate (sig : ContinuousOperatorSpectralSignature) : Prop where
  top_mem : (1 : ℝ) ∈ spectrum ℝ sig.T
  v_gap :
    ∃ v_gap : sig.E,
      v_gap ≠ 0 ∧
        inner ℝ v_gap sig.v_top = 0 ∧
          sig.T v_gap = (1 - sig.gap) • v_gap
  no_orthogonal_top :
    ∀ v : sig.E, v ≠ 0 → inner ℝ v sig.v_top = 0 → sig.T v ≠ v
  upper_bound :
    ∀ l : ℝ, l ∈ spectrum ℝ sig.T → l ≠ 1 → l ≤ 1 - sig.gap
  abs_bound :
    ∀ l : ℝ, l ∈ spectrum ℝ sig.T → l ≠ 1 → ‖l‖ ≤ 1 - sig.gap

/-! ### Operator-norm `cv` -/

/-- Orthogonal complement of the stationary line carried by `v_top`. -/
noncomputable abbrev stationaryOrthogonalSubmodule
    (sig : ContinuousOperatorSpectralSignature) : Submodule ℝ sig.E :=
  (ℝ ∙ sig.v_top)ᗮ

/-- The operator-norm spectral vulnerability: remove the stationary line and
measure the remaining action of `T`. -/
noncomputable def cvOp (sig : ContinuousOperatorSpectralSignature) : ℝ :=
  1 - ‖sig.T.comp (stationaryOrthogonalSubmodule sig).starProjection‖

theorem cvOp_nonneg (sig : ContinuousOperatorSpectralSignature)
    (hcontract :
      ‖sig.T.comp (stationaryOrthogonalSubmodule sig).starProjection‖ ≤ 1) :
    0 ≤ cvOp sig := by
  dsimp [cvOp]
  linarith

theorem cvOp_le_one (sig : ContinuousOperatorSpectralSignature) :
    cvOp sig ≤ 1 := by
  dsimp [cvOp]
  exact sub_le_self _ (norm_nonneg _)

private theorem stationaryOrthogonal_apply_mem
    (sig : ContinuousOperatorSpectralSignature) :
    ∀ v ∈ stationaryOrthogonalSubmodule sig, sig.T v ∈ stationaryOrthogonalSubmodule sig := by
  have hTsymm :
      (sig.T : sig.E →ₗ[ℝ] sig.E).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (A := sig.T)).1
      sig.isSelfAdjoint
  have hline_invt :
      (ℝ ∙ sig.v_top) ∈
        Module.End.invtSubmodule (sig.T : Module.End ℝ sig.E) := by
    intro v hv
    rw [Submodule.mem_span_singleton] at hv
    rcases hv with ⟨a, rfl⟩
    rw [Submodule.mem_comap, Submodule.mem_span_singleton]
    exact ⟨a, by simp [map_smul, sig.T_v_top]⟩
  have horth_invt :
      stationaryOrthogonalSubmodule sig ∈
        Module.End.invtSubmodule (sig.T : Module.End ℝ sig.E) := by
    simpa [stationaryOrthogonalSubmodule] using
      hTsymm.orthogonalComplement_mem_invtSubmodule hline_invt
  exact
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
      (f := (sig.T : sig.E →ₗ[ℝ] sig.E))
      (p := stationaryOrthogonalSubmodule sig)).1 horth_invt

private theorem stationaryOrthogonal_mem_iff_inner
    (sig : ContinuousOperatorSpectralSignature) (v : sig.E) :
    v ∈ stationaryOrthogonalSubmodule sig ↔ inner ℝ v sig.v_top = 0 := by
  rw [stationaryOrthogonalSubmodule]
  exact Submodule.mem_orthogonal_singleton_iff_inner_left

theorem cvOp_eq_gap_of_operatorSpectralGapPredicate
    (sig : ContinuousOperatorSpectralSignature)
    (h : OperatorSpectralGapPredicate sig) :
    cvOp sig = sig.gap := by
  classical
  let K : Submodule ℝ sig.E := stationaryOrthogonalSubmodule sig
  let A : sig.E →L[ℝ] sig.E := sig.T.comp K.starProjection
  have hK :
      ∀ v ∈ K, sig.T v ∈ K := by
    simpa [K] using stationaryOrthogonal_apply_mem sig
  rcases h with ⟨_, hv_gap_exists, hno_orthogonal_top, _, habs⟩
  rcases hv_gap_exists with ⟨v_gap, hv_gap_ne, hv_gap_orth, hv_gap_eq⟩
  have hv_gap_mem : v_gap ∈ K := by
    exact (stationaryOrthogonal_mem_iff_inner sig v_gap).2 hv_gap_orth
  have hA_self : IsSelfAdjoint A := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    have hPx_mem : K.starProjection x ∈ K :=
      Submodule.starProjection_apply_mem (U := K) x
    have hPy_mem : K.starProjection y ∈ K :=
      Submodule.starProjection_apply_mem (U := K) y
    have hTPx_mem : sig.T (K.starProjection x) ∈ K :=
      hK (K.starProjection x) hPx_mem
    have hTPy_mem : sig.T (K.starProjection y) ∈ K :=
      hK (K.starProjection y) hPy_mem
    have hy_decomp :
        y = K.starProjection y + (y - K.starProjection y) := by
      abel
    have hx_decomp :
        x = K.starProjection x + (x - K.starProjection x) := by
      abel
    have horth_y :
        inner ℝ (sig.T (K.starProjection x)) (y - K.starProjection y) = 0 := by
      exact Submodule.inner_right_of_mem_orthogonal hTPx_mem
        (Submodule.sub_starProjection_mem_orthogonal (K := K) y)
    have horth_x :
        inner ℝ (x - K.starProjection x) (sig.T (K.starProjection y)) = 0 := by
      exact Submodule.inner_left_of_mem_orthogonal hTPy_mem
        (Submodule.sub_starProjection_mem_orthogonal (K := K) x)
    have hsymm :
        inner ℝ (sig.T (K.starProjection x)) (K.starProjection y) =
          inner ℝ (K.starProjection x) (sig.T (K.starProjection y)) := by
      have hTsymm :
          (sig.T : sig.E →ₗ[ℝ] sig.E).IsSymmetric :=
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (A := sig.T)).1
          sig.isSelfAdjoint
      simpa using hTsymm (K.starProjection x) (K.starProjection y)
    have hsplit_y :
        inner ℝ (sig.T (K.starProjection x)) y =
          inner ℝ (sig.T (K.starProjection x)) (K.starProjection y) := by
      nth_rewrite 1 [hy_decomp]
      rw [inner_add_right, horth_y, add_zero]
    have hsplit_x :
        inner ℝ x (sig.T (K.starProjection y)) =
          inner ℝ (K.starProjection x) (sig.T (K.starProjection y)) := by
      nth_rewrite 1 [hx_decomp]
      rw [inner_add_left, horth_x, add_zero]
    calc
      inner ℝ (A x) y =
          inner ℝ (sig.T (K.starProjection x)) y := rfl
      _ = inner ℝ (sig.T (K.starProjection x)) (K.starProjection y) := hsplit_y
      _ = inner ℝ (K.starProjection x) (sig.T (K.starProjection y)) := hsymm
      _ = inner ℝ x (sig.T (K.starProjection y)) := hsplit_x.symm
      _ = inner ℝ x (A y) := rfl
  have hA_compact : IsCompactOperator (A : sig.E → sig.E) := by
    simpa [A, ContinuousLinearMap.comp_apply] using
      sig.isCompact.comp_clm K.starProjection
  haveI : Nontrivial sig.E :=
    nontrivial_of_ne sig.v_top 0 sig.v_top_ne
  obtain ⟨μ, y, hy_eig, hμ_norm⟩ :=
    CompactSelfAdjoint.exists_hasEigenvector_norm_eq_opNorm_of_isCompactOperator_of_isSelfAdjoint
      (𝕜 := ℝ) (E := sig.E) A hA_self hA_compact
  rcases (Module.End.hasEigenvector_iff.mp hy_eig) with ⟨hy_mem, hy_ne⟩
  have hAy_eq : A y = μ • y :=
    Module.End.mem_eigenspace_iff.mp hy_mem
  have hy_lift_of_ne_zero (hμ0 : μ ≠ 0) :
      Module.End.HasEigenvector (sig.T : sig.E →ₗ[ℝ] sig.E) μ y := by
    have hy_mem_K : y ∈ K := by
      have hAy_mem : A y ∈ K := by
        dsimp [A]
        exact hK (K.starProjection y) (Submodule.starProjection_apply_mem (U := K) y)
      have hsmul_mem : μ • y ∈ K := by simpa [hAy_eq] using hAy_mem
      exact (K.smul_mem_iff hμ0).1 hsmul_mem
    have hproj : K.starProjection y = y :=
      (Submodule.starProjection_eq_self_iff (K := K)).2 hy_mem_K
    refine Module.End.hasEigenvector_iff.mpr ?_
    refine ⟨?_, hy_ne⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa [A, ContinuousLinearMap.comp_apply, hproj] using hAy_eq
  have hμ_ne_one : μ ≠ 1 := by
    intro hμ
    have hμ0 : μ ≠ 0 := by norm_num [hμ]
    have hy_lift := hy_lift_of_ne_zero hμ0
    have hTy : sig.T y = y := by
      rcases (Module.End.hasEigenvector_iff.mp hy_lift) with ⟨hy_mem, _⟩
      have hy_eq :
          (sig.T : sig.E →ₗ[ℝ] sig.E) y = μ • y :=
        (Module.End.mem_eigenspace_iff.mp hy_mem)
      simpa [hμ] using hy_eq
    have hy_mem_K : y ∈ K := by
      have hAy_mem : A y ∈ K := by
        dsimp [A]
        exact hK (K.starProjection y) (Submodule.starProjection_apply_mem (U := K) y)
      have hsmul_mem : μ • y ∈ K := by simpa [hAy_eq] using hAy_mem
      exact (K.smul_mem_iff hμ0).1 hsmul_mem
    have hy_orth : inner ℝ y sig.v_top = 0 :=
      (stationaryOrthogonal_mem_iff_inner sig y).1 (by simpa [K] using hy_mem_K)
    exact hno_orthogonal_top y hy_ne hy_orth hTy
  have hgap_ne_one : (1 - sig.gap : ℝ) ≠ 1 := by
    linarith [sig.gap_pos]
  have hgap_spectrum : (1 - sig.gap : ℝ) ∈ spectrum ℝ sig.T := by
    have hgap_lift :
        Module.End.HasEigenvector (sig.T : sig.E →ₗ[ℝ] sig.E)
          (1 - sig.gap) v_gap := by
      refine Module.End.hasEigenvector_iff.mpr ?_
      refine ⟨?_, hv_gap_ne⟩
      rw [Module.End.mem_eigenspace_iff]
      exact hv_gap_eq
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      (f := (sig.T : sig.E →ₗ[ℝ] sig.E)) hgap_lift).mem_spectrum
  have hgap_abs_le : ‖(1 - sig.gap : ℝ)‖ ≤ 1 - sig.gap :=
    habs (1 - sig.gap) hgap_spectrum hgap_ne_one
  have hgap_nonneg : 0 ≤ 1 - sig.gap := by
    have hnorm_nonneg : 0 ≤ ‖(1 - sig.gap : ℝ)‖ := norm_nonneg _
    linarith
  have hgap_abs : ‖(1 - sig.gap : ℝ)‖ = 1 - sig.gap := by
    simpa [Real.norm_eq_abs] using abs_of_nonneg hgap_nonneg
  have hA_le : ‖A‖ ≤ 1 - sig.gap := by
    rw [← hμ_norm]
    by_cases hμ0 : μ = 0
    · rw [hμ0]
      simpa using hgap_nonneg
    · have hy_lift := hy_lift_of_ne_zero hμ0
      have hμ_spectrum : μ ∈ spectrum ℝ sig.T := by
        rw [ContinuousLinearMap.spectrum_eq]
        exact (Module.End.hasEigenvalue_of_hasEigenvector
          (f := (sig.T : sig.E →ₗ[ℝ] sig.E)) hy_lift).mem_spectrum
      exact habs μ hμ_spectrum hμ_ne_one
  have hgap_le_A : 1 - sig.gap ≤ ‖A‖ := by
    have hle := ContinuousLinearMap.le_opNorm A v_gap
    have hproj_gap : K.starProjection v_gap = v_gap :=
      (Submodule.starProjection_eq_self_iff (K := K)).2 hv_gap_mem
    have hSyg :
        ‖A v_gap‖ = ‖(1 - sig.gap : ℝ)‖ * ‖v_gap‖ := by
      simp [A, ContinuousLinearMap.comp_apply, hproj_gap, hv_gap_eq, norm_smul]
    have hyg_norm_pos : 0 < ‖v_gap‖ := norm_pos_iff.mpr hv_gap_ne
    have hmul :
        (1 - sig.gap) * ‖v_gap‖ ≤ ‖A‖ * ‖v_gap‖ := by
      simpa [hSyg, hgap_abs] using hle
    exact le_of_mul_le_mul_right hmul hyg_norm_pos
  have hA_eq : ‖A‖ = 1 - sig.gap := le_antisymm hA_le hgap_le_A
  dsimp [cvOp, stationaryOrthogonalSubmodule, K, A]
  rw [hA_eq]
  ring

theorem cvOp_nonneg_of_predicate
    (sig : ContinuousOperatorSpectralSignature)
    (h : OperatorSpectralGapPredicate sig) :
    0 ≤ cvOp sig := by
  rw [cvOp_eq_gap_of_operatorSpectralGapPredicate sig h]
  exact sig.gap_pos.le

/-! ### Rank-2 counting-kernel operator instance -/

/-- Matrix of the two-state counting kernel, indexed by `Bool`. -/
noncomputable def twoStateCountingKernelMatrix (g : ℚ) : Matrix Bool Bool ℝ :=
  fun x y => countingSpectralKernelRealDensity g x y

/-- Continuous linear operator induced by the two-state counting kernel on
Euclidean two-space. -/
noncomputable def twoStateCountingKernelCLM (g : ℚ) :
    EuclideanSpace ℝ Bool →L[ℝ] EuclideanSpace ℝ Bool :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Bool))
    (twoStateCountingKernelMatrix g)

@[simp]
theorem twoStateCountingKernelCLM_ofLp (g : ℚ)
    (v : EuclideanSpace ℝ Bool) :
    (twoStateCountingKernelCLM g v).ofLp =
      (twoStateCountingKernelMatrix g).mulVec v.ofLp := by
  exact Matrix.ofLp_toEuclideanCLM (twoStateCountingKernelMatrix g) v

theorem twoStateCountingKernelCLM_isSelfAdjoint (g : ℚ) :
    IsSelfAdjoint (twoStateCountingKernelCLM g) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change
    inner ℝ (twoStateCountingKernelCLM g x) y =
      inner ℝ x (twoStateCountingKernelCLM g y)
  rw [← (real_inner_comm (twoStateCountingKernelCLM g x) y)]
  unfold twoStateCountingKernelCLM
  rw [Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
  simp [twoStateCountingKernelMatrix, dotProduct, Matrix.mulVec,
    Fintype.univ_bool, countingSpectralKernelRealDensity, mul_add, add_mul,
    mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc]

theorem twoStateCountingKernelCLM_isCompact (g : ℚ) :
    IsCompactOperator (twoStateCountingKernelCLM g) :=
  isCompactOperator_of_locallyCompactSpace_dom (twoStateCountingKernelCLM g)

theorem twoStateCountingKernelCLM_v_top (g : ℚ) (hg : 0 < g) :
    twoStateCountingKernelCLM g (WithLp.toLp 2 (fun _ : Bool => (1 : ℝ))) =
      WithLp.toLp 2 (fun _ : Bool => (1 : ℝ)) := by
  rw [twoStateCountingKernelCLM, Matrix.toEuclideanCLM_toLp]
  congr 1
  funext x
  fin_cases x <;>
    simp [twoStateCountingKernelMatrix, Matrix.mulVec, dotProduct,
      Fintype.univ_bool, countingSpectralKernelRealDensity]
  all_goals
    have hden : (1 : ℝ) + (g : ℝ) ≠ 0 := by
      positivity
    field_simp [hden]
    try ring

theorem twoStateCountingKernel_gap_pos (g : ℚ) (hg : 0 < g) :
    0 < 2 * (g : ℝ) / (1 + (g : ℝ)) := by
  positivity

/-- Rank-2 continuous-operator spectral signature induced by the two-state
counting kernel. -/
noncomputable def twoStateCountingKernelContinuousSignature (g : ℚ) (hg : 0 < g) :
    ContinuousOperatorSpectralSignature where
  E := EuclideanSpace ℝ Bool
  T := twoStateCountingKernelCLM g
  isCompact := twoStateCountingKernelCLM_isCompact g
  isSelfAdjoint := twoStateCountingKernelCLM_isSelfAdjoint g
  v_top := WithLp.toLp 2 (fun _ : Bool => (1 : ℝ))
  v_top_ne := by
    intro h
    have hfalse := congrFun (congrArg WithLp.ofLp h) false
    norm_num at hfalse
  T_v_top := twoStateCountingKernelCLM_v_top g hg
  gap := 2 * (g : ℝ) / (1 + (g : ℝ))
  gap_pos := twoStateCountingKernel_gap_pos g hg

theorem twoStateCountingKernel_top_mem_spectrum (g : ℚ) (hg : 0 < g) :
    (1 : ℝ) ∈ spectrum ℝ (twoStateCountingKernelCLM g) := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact
    (show
        Module.End.HasEigenvalue
          (twoStateCountingKernelCLM g :
            EuclideanSpace ℝ Bool →ₗ[ℝ] EuclideanSpace ℝ Bool)
            (1 : ℝ) by
      refine Module.End.hasEigenvalue_of_hasEigenvector
        (x := WithLp.toLp 2 (fun _ : Bool => (1 : ℝ))) ?_
      rw [Module.End.hasEigenvector_iff]
      refine ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        ext x
        have htop :
            twoStateCountingKernelCLM g
                (WithLp.toLp 2 (fun _ : Bool => (1 : ℝ))) =
              WithLp.toLp 2 (fun _ : Bool => (1 : ℝ)) :=
          twoStateCountingKernelCLM_v_top g hg
        simpa using congrFun (congrArg WithLp.ofLp htop) x
      · intro h
        have hfalse := congrFun (congrArg WithLp.ofLp h) false
        norm_num at hfalse).mem_spectrum

theorem mem_countingSpectralKernelOperatorEigenvalueSet_of_mem_spectrum
    {g : ℚ} {l : ℝ}
    (hl : l ∈ spectrum ℝ (twoStateCountingKernelCLM g)) :
    l ∈ countingSpectralKernelOperatorEigenvalueSet g := by
  rw [ContinuousLinearMap.spectrum_eq] at hl
  have hl_eigen :
      Module.End.HasEigenvalue
        (twoStateCountingKernelCLM g :
          EuclideanSpace ℝ Bool →ₗ[ℝ] EuclideanSpace ℝ Bool) l :=
    Module.End.HasEigenvalue.of_mem_spectrum hl
  rcases Module.End.HasEigenvalue.exists_hasEigenvector hl_eigen with ⟨f, hf⟩
  refine ⟨f.ofLp, ?_, ?_⟩
  · intro hzero
    exact hf.2 ((WithLp.ofLp_eq_zero 2).mp hzero)
  intro x
  have happly := Module.End.HasEigenvector.apply_eq_smul hf
  have hoflp := congrFun (congrArg WithLp.ofLp happly) x
  simpa [twoStateCountingKernelCLM_ofLp, twoStateCountingKernelMatrix,
    countingSpectralKernelOperator, Matrix.mulVec, dotProduct,
    countingSpectralKernelRealDensity] using hoflp

theorem twoStateCountingKernel_one_sub_gap_eq_nontrivialEigenvalue
    (g : ℚ) (hg : 0 < g) :
    1 - 2 * (g : ℝ) / (1 + (g : ℝ)) =
      countingSpectralKernelNontrivialEigenvalue g := by
  have hden : (1 : ℝ) + (g : ℝ) ≠ 0 := by positivity
  simp [countingSpectralKernelNontrivialEigenvalue]
  field_simp [hden]
  ring

theorem twoStateCountingKernel_gap_witness (g : ℚ) (hg : 0 < g) :
    ∃ v_gap : EuclideanSpace ℝ Bool,
      v_gap ≠ 0 ∧
        inner ℝ v_gap (WithLp.toLp 2 (fun _ : Bool => (1 : ℝ))) = 0 ∧
          twoStateCountingKernelCLM g v_gap =
            (1 - 2 * (g : ℝ) / (1 + (g : ℝ))) • v_gap := by
  refine ⟨WithLp.toLp 2 (fun x : Bool => if x then (1 : ℝ) else (-1 : ℝ)), ?_, ?_, ?_⟩
  · intro h
    have htrue := congrFun (congrArg WithLp.ofLp h) true
    norm_num at htrue
  · change
      inner ℝ
        (WithLp.toLp 2 (fun x : Bool => if x then (1 : ℝ) else (-1 : ℝ)))
        (WithLp.toLp 2 (fun _ : Bool => (1 : ℝ))) = 0
    calc
      inner ℝ
          (WithLp.toLp 2 (fun x : Bool => if x then (1 : ℝ) else (-1 : ℝ)))
          (WithLp.toLp 2 (fun _ : Bool => (1 : ℝ))) =
          dotProduct (fun _ : Bool => (1 : ℝ))
            (star (fun x : Bool => if x then (1 : ℝ) else (-1 : ℝ))) :=
        EuclideanSpace.inner_toLp_toLp
          (fun x : Bool => if x then (1 : ℝ) else (-1 : ℝ))
          (fun _ : Bool => (1 : ℝ))
      _ = 0 := by
        simp [dotProduct, Fintype.univ_bool]
  · rw [twoStateCountingKernelCLM, Matrix.toEuclideanCLM_toLp]
    congr 1
    funext x
    have hden : (1 : ℝ) + (g : ℝ) ≠ 0 := by positivity
    fin_cases x <;>
      simp [twoStateCountingKernelMatrix, Matrix.mulVec, dotProduct,
        Fintype.univ_bool, countingSpectralKernelRealDensity]
    all_goals
      field_simp [hden]
      ring

theorem twoStateCountingKernel_operatorSpectralGapPredicate
    (g : ℚ) (hg : 0 < g) (hg1 : g < 1) :
    OperatorSpectralGapPredicate
      (twoStateCountingKernelContinuousSignature g hg) := by
  have hupper :
      ∀ l : ℝ, l ∈ spectrum ℝ (twoStateCountingKernelContinuousSignature g hg).T →
        l ≠ 1 → l ≤ 1 - (twoStateCountingKernelContinuousSignature g hg).gap := by
    intro l hl hl_ne_one
    have hl_set :
        l ∈ countingSpectralKernelOperatorEigenvalueSet g :=
      mem_countingSpectralKernelOperatorEigenvalueSet_of_mem_spectrum
        (by simpa [twoStateCountingKernelContinuousSignature] using hl)
    rw [countingSpectralKernel_operator_eigenvalues g hg] at hl_set
    rcases hl_set with hl_one | hl_nontrivial
    · exact False.elim (hl_ne_one hl_one)
    · rw [hl_nontrivial]
      rw [twoStateCountingKernelContinuousSignature]
      rw [twoStateCountingKernel_one_sub_gap_eq_nontrivialEigenvalue g hg]
  refine
    { top_mem := twoStateCountingKernel_top_mem_spectrum g hg
      v_gap := by
        simpa [twoStateCountingKernelContinuousSignature] using
          twoStateCountingKernel_gap_witness g hg
      no_orthogonal_top := ?_
      upper_bound := hupper
      abs_bound := ?_ }
  · intro v hv_ne hv_orth hv_top
    have hden : (1 : ℝ) + (g : ℝ) ≠ 0 := by positivity
    have hfalse := congrFun (congrArg WithLp.ofLp hv_top) false
    have htrue := congrFun (congrArg WithLp.ofLp hv_top) true
    have horth :
        v.ofLp false + v.ofLp true = 0 := by
      have hv_orth' :
          inner ℝ (WithLp.toLp 2 v.ofLp)
              (WithLp.toLp 2 (fun _ : Bool => (1 : ℝ))) = 0 := by
        simpa [WithLp.toLp_ofLp, twoStateCountingKernelContinuousSignature] using hv_orth
      calc
        v.ofLp false + v.ofLp true =
            dotProduct (fun _ : Bool => (1 : ℝ)) (star v.ofLp) := by
          simp [dotProduct, Fintype.univ_bool, add_comm]
        _ =
            inner ℝ (WithLp.toLp 2 v.ofLp)
              (WithLp.toLp 2 (fun _ : Bool => (1 : ℝ))) := by
          exact (EuclideanSpace.inner_toLp_toLp
            v.ofLp (fun _ : Bool => (1 : ℝ))).symm
        _ = 0 := hv_orth'
    have hfalse_eq :
        (g : ℝ) * v.ofLp true + v.ofLp false =
          v.ofLp false * (1 + (g : ℝ)) := by
      change ((twoStateCountingKernelCLM g) v).ofLp false = v.ofLp false at hfalse
      rw [twoStateCountingKernelCLM_ofLp] at hfalse
      simp [twoStateCountingKernelMatrix, Matrix.mulVec, dotProduct, Fintype.univ_bool,
        countingSpectralKernelRealDensity] at hfalse
      field_simp [hden] at hfalse
      linarith
    have htrue_eq :
        v.ofLp true + (g : ℝ) * v.ofLp false =
          v.ofLp true * (1 + (g : ℝ)) := by
      change ((twoStateCountingKernelCLM g) v).ofLp true = v.ofLp true at htrue
      rw [twoStateCountingKernelCLM_ofLp] at htrue
      simp [twoStateCountingKernelMatrix, Matrix.mulVec, dotProduct, Fintype.univ_bool,
        countingSpectralKernelRealDensity] at htrue
      field_simp [hden] at htrue
      linarith
    have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
    have hfalse_zero : v.ofLp false = 0 := by
      nlinarith
    have htrue_zero : v.ofLp true = 0 := by
      nlinarith
    apply hv_ne
    apply (WithLp.ofLp_eq_zero 2).mp
    funext x
    fin_cases x <;> simp [hfalse_zero, htrue_zero]
  · intro l hl hl_ne_one
    have hl_set :
        l ∈ countingSpectralKernelOperatorEigenvalueSet g :=
      mem_countingSpectralKernelOperatorEigenvalueSet_of_mem_spectrum
        (by simpa [twoStateCountingKernelContinuousSignature] using hl)
    rw [countingSpectralKernel_operator_eigenvalues g hg] at hl_set
    rcases hl_set with hl_one | hl_nontrivial
    · exact False.elim (hl_ne_one hl_one)
    · rw [hl_nontrivial]
      rw [twoStateCountingKernelContinuousSignature]
      rw [twoStateCountingKernel_one_sub_gap_eq_nontrivialEigenvalue g hg]
      have hnonneg :
          0 ≤ countingSpectralKernelNontrivialEigenvalue g := by
        have hnum : 0 ≤ (1 : ℝ) - (g : ℝ) := by exact_mod_cast sub_nonneg.mpr hg1.le
        have hdenpos : 0 < (1 : ℝ) + (g : ℝ) := by positivity
        exact div_nonneg hnum hdenpos.le
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]

theorem cvOp_twoStateCountingKernelContinuousSignature_eq
    (g : ℚ) (hg : 0 < g) (hg1 : g < 1) :
    cvOp (twoStateCountingKernelContinuousSignature g hg) =
      2 * (g : ℝ) / (1 + (g : ℝ)) := by
  simpa [twoStateCountingKernelContinuousSignature] using
    cvOp_eq_gap_of_operatorSpectralGapPredicate
      (twoStateCountingKernelContinuousSignature g hg)
      (twoStateCountingKernel_operatorSpectralGapPredicate g hg hg1)

/-! ### Rank-N truncated Ornstein-Uhlenbeck signature -/

/-- Matrix carrying the rank-`N` truncation of the Ornstein-Uhlenbeck/Mehler
eigenvalue ladder `exp (-n t)`. -/
noncomputable def ouTruncatedMatrix (N : ℕ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun k : Fin N => Real.exp (-(k : ℝ) * t))

/-- Continuous linear operator induced by the rank-`N` truncated
Ornstein-Uhlenbeck diagonal matrix. -/
noncomputable def ouTruncatedCLM (N : ℕ) (t : ℝ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N)) (ouTruncatedMatrix N t)

private def ouTopIndex (N : ℕ) (hN : 1 < N) : Fin N :=
  ⟨0, lt_of_lt_of_le Nat.one_pos hN.le⟩

private def ouGapIndex (N : ℕ) (hN : 1 < N) : Fin N :=
  ⟨1, hN⟩

theorem ouTruncatedCLM_isSelfAdjoint (N : ℕ) (t : ℝ) :
    IsSelfAdjoint (ouTruncatedCLM N t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold ouTruncatedCLM
  change
    star ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N))
      (ouTruncatedMatrix N t)) =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N))
        (ouTruncatedMatrix N t)
  calc
    star ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N))
        (ouTruncatedMatrix N t)) =
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N))
          (star (ouTruncatedMatrix N t)) :=
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N)).map_star'
        (ouTruncatedMatrix N t)).symm
    _ = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N))
        (ouTruncatedMatrix N t) := by
      congr 1
      ext i j
      by_cases hij : i = j
      · simp [ouTruncatedMatrix, Matrix.star_apply, Matrix.diagonal, hij]
      · simp [ouTruncatedMatrix, Matrix.star_apply, Matrix.diagonal, hij, Ne.symm hij]

theorem ouTruncatedCLM_isCompact (N : ℕ) (t : ℝ) :
    IsCompactOperator (ouTruncatedCLM N t) :=
  isCompactOperator_of_locallyCompactSpace_dom (ouTruncatedCLM N t)

theorem ouTruncatedCLM_top_single (N : ℕ) (hN : 1 < N) (t : ℝ) :
    ouTruncatedCLM N t
        (EuclideanSpace.single (ouTopIndex N hN) (1 : ℝ)) =
      EuclideanSpace.single (ouTopIndex N hN) (1 : ℝ) := by
  ext j
  by_cases hj : j = (⟨0, lt_of_lt_of_le Nat.one_pos hN.le⟩ : Fin N) <;>
    simp [ouTruncatedCLM, ouTruncatedMatrix, ouTopIndex, Matrix.mulVec, dotProduct,
      Matrix.diagonal, hj]

theorem ouTruncatedCLM_gap_single (N : ℕ) (hN : 1 < N) (t : ℝ) :
    ouTruncatedCLM N t
        (EuclideanSpace.single (ouGapIndex N hN) (1 : ℝ)) =
      Real.exp (-t) • EuclideanSpace.single (ouGapIndex N hN) (1 : ℝ) := by
  ext j
  by_cases hj : j = (⟨1, hN⟩ : Fin N) <;>
    simp [ouTruncatedCLM, ouTruncatedMatrix, ouGapIndex, Matrix.mulVec, dotProduct,
      Matrix.diagonal, hj]

theorem ouTruncated_gap_pos (t : ℝ) (ht : 0 < t) :
    0 < 1 - Real.exp (-t) := by
  have hexp_lt : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  linarith

/-- Rank-`N` truncated Ornstein-Uhlenbeck/Mehler continuous-operator spectral
signature.  The gap is computed from `t` as `1 - exp (-t)`. -/
noncomputable def ouTruncatedSignature
    (N : ℕ) (hN : 1 < N) (t : ℝ) (ht : 0 < t) :
    ContinuousOperatorSpectralSignature where
  E := EuclideanSpace ℝ (Fin N)
  T := ouTruncatedCLM N t
  isCompact := ouTruncatedCLM_isCompact N t
  isSelfAdjoint := ouTruncatedCLM_isSelfAdjoint N t
  v_top := EuclideanSpace.single (ouTopIndex N hN) (1 : ℝ)
  v_top_ne := by
    intro h
    have hcoord := congrFun (congrArg WithLp.ofLp h) (ouTopIndex N hN)
    simp [ouTopIndex] at hcoord
  T_v_top := ouTruncatedCLM_top_single N hN t
  gap := 1 - Real.exp (-t)
  gap_pos := ouTruncated_gap_pos t ht

theorem ouTruncatedCLM_spectrum_eq_range (N : ℕ) (t : ℝ) :
    spectrum ℝ (ouTruncatedCLM N t) =
      Set.range (fun k : Fin N => Real.exp (-(k : ℝ) * t)) := by
  have hspectrum_clm :
      spectrum ℝ (ouTruncatedCLM N t) =
        spectrum ℝ (ouTruncatedMatrix N t) := by
    exact
      AlgEquiv.spectrum_eq
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N))
        (ouTruncatedMatrix N t)
  have hmatrix :
      spectrum ℝ (ouTruncatedMatrix N t) =
        Set.range (fun k : Fin N => Real.exp (-(k : ℝ) * t)) := by
    simp [ouTruncatedMatrix]
  rw [hspectrum_clm, hmatrix]

theorem ouTruncated_top_mem_spectrum
    (N : ℕ) (hN : 1 < N) (t : ℝ) :
    (1 : ℝ) ∈ spectrum ℝ (ouTruncatedCLM N t) := by
  rw [ouTruncatedCLM_spectrum_eq_range]
  refine ⟨ouTopIndex N hN, ?_⟩
  simp [ouTopIndex]

private theorem ouTopIndex_ne_ouGapIndex (N : ℕ) (hN : 1 < N) :
    ouTopIndex N hN ≠ ouGapIndex N hN := by
  intro h
  have hval := congrArg Fin.val h
  norm_num [ouTopIndex, ouGapIndex] at hval

theorem ouTruncated_gap_witness (N : ℕ) (hN : 1 < N) (t : ℝ) :
    ∃ v_gap : EuclideanSpace ℝ (Fin N),
      v_gap ≠ 0 ∧
        inner ℝ v_gap (EuclideanSpace.single (ouTopIndex N hN) (1 : ℝ)) = 0 ∧
          ouTruncatedCLM N t v_gap =
            (1 - (1 - Real.exp (-t))) • v_gap := by
  refine
    ⟨EuclideanSpace.single (ouGapIndex N hN) (1 : ℝ), ?_, ?_, ?_⟩
  · intro h
    have hcoord := congrFun (congrArg WithLp.ofLp h) (ouGapIndex N hN)
    simp [ouGapIndex] at hcoord
  · have hne : ouTopIndex N hN ≠ ouGapIndex N hN :=
      ouTopIndex_ne_ouGapIndex N hN
    change
      inner ℝ
        (WithLp.toLp 2 (Pi.single (ouGapIndex N hN) (1 : ℝ) : Fin N → ℝ))
        (WithLp.toLp 2 (Pi.single (ouTopIndex N hN) (1 : ℝ) : Fin N → ℝ)) = 0
    calc
      inner ℝ
          (WithLp.toLp 2 (Pi.single (ouGapIndex N hN) (1 : ℝ) : Fin N → ℝ))
          (WithLp.toLp 2 (Pi.single (ouTopIndex N hN) (1 : ℝ) : Fin N → ℝ)) =
          dotProduct (Pi.single (ouTopIndex N hN) (1 : ℝ) : Fin N → ℝ)
            (star (Pi.single (ouGapIndex N hN) (1 : ℝ) : Fin N → ℝ)) :=
        EuclideanSpace.inner_toLp_toLp
          (Pi.single (ouGapIndex N hN) (1 : ℝ) : Fin N → ℝ)
          (Pi.single (ouTopIndex N hN) (1 : ℝ) : Fin N → ℝ)
      _ = 0 := by
        rw [dotProduct]
        apply Finset.sum_eq_zero
        intro x _
        by_cases hx0 : x = ouTopIndex N hN <;>
          by_cases hx1 : x = ouGapIndex N hN <;>
            simp [Pi.single_apply, hx0, hx1, hne, Ne.symm hne]
  · have hgap := ouTruncatedCLM_gap_single N hN t
    simpa using hgap

theorem ouTruncatedCLM_no_orthogonal_top
    (N : ℕ) (hN : 1 < N) (t : ℝ) (ht : 0 < t) :
    ∀ v : EuclideanSpace ℝ (Fin N), v ≠ 0 →
      inner ℝ v (EuclideanSpace.single (ouTopIndex N hN) (1 : ℝ)) = 0 →
        ouTruncatedCLM N t v ≠ v := by
  intro v hv_ne hv_orth hv_top
  apply hv_ne
  ext j
  by_cases hj0 : j = ouTopIndex N hN
  · have hcoord0 : v (ouTopIndex N hN) = 0 := by
      have hinner :
          inner ℝ v (EuclideanSpace.single (ouTopIndex N hN) (1 : ℝ)) =
            v (ouTopIndex N hN) := by
        simpa [EuclideanSpace.basisFun_apply, ouTopIndex] using
          EuclideanSpace.inner_basisFun_real (ι := Fin N) v (ouTopIndex N hN)
      simpa [hinner] using hv_orth
    simp [hj0, hcoord0]
  · have hcoord := congrFun (congrArg WithLp.ofLp hv_top) j
    change ((ouTruncatedCLM N t v).ofLp j) = v.ofLp j at hcoord
    rw [ouTruncatedCLM, ouTruncatedMatrix, Matrix.ofLp_toEuclideanCLM] at hcoord
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal] at hcoord
    have hjpos_nat : 0 < j.val := Nat.pos_of_ne_zero (by
      intro hjval
      apply hj0
      ext
      exact hjval)
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjpos_nat
    have hexp_ne : Real.exp (-(↑↑j * t)) ≠ 1 := by
      have hneg : -(↑↑j * t) < 0 := by nlinarith [mul_pos hjpos ht]
      exact ne_of_lt ((Real.exp_lt_one_iff).2 hneg)
    have hmul : (Real.exp (-(↑↑j * t)) - 1) * v.ofLp j = 0 := by
      nlinarith
    have hcoef : Real.exp (-(↑↑j * t)) - 1 ≠ 0 :=
      sub_ne_zero.mpr hexp_ne
    exact (mul_eq_zero.mp hmul).resolve_left hcoef

private theorem ouTruncated_spectral_value_le_exp_neg_t
    (N : ℕ) (hN : 1 < N) (t : ℝ) (ht : 0 < t)
    {l : ℝ}
    (hl : l ∈ spectrum ℝ (ouTruncatedCLM N t)) (hl_ne_one : l ≠ 1) :
    l ≤ Real.exp (-t) := by
  rw [ouTruncatedCLM_spectrum_eq_range] at hl
  rcases hl with ⟨k, rfl⟩
  by_cases hk0 : k.val = 0
  · exfalso
    apply hl_ne_one
    have hk_top : k = ouTopIndex N hN := by
      ext
      exact hk0
    simp [hk_top, ouTopIndex]
  · have hkpos_nat : 0 < k.val := Nat.pos_of_ne_zero hk0
    have hkge_nat : 1 ≤ k.val := Nat.succ_le_of_lt hkpos_nat
    have hkge : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkge_nat
    have harg : -(k : ℝ) * t ≤ -t := by
      have hmul : t ≤ (k : ℝ) * t :=
        by simpa [one_mul] using mul_le_mul_of_nonneg_right hkge ht.le
      nlinarith
    exact Real.exp_le_exp_of_le harg

theorem operatorSpectralGapPredicate_ouTruncatedSignature
    (N : ℕ) (hN : 1 < N) (t : ℝ) (ht : 0 < t) :
    OperatorSpectralGapPredicate (ouTruncatedSignature N hN t ht) := by
  refine
    { top_mem := by
        simpa [ouTruncatedSignature] using ouTruncated_top_mem_spectrum N hN t
      v_gap := by
        simpa [ouTruncatedSignature] using ouTruncated_gap_witness N hN t
      no_orthogonal_top := by
        simpa [ouTruncatedSignature] using
          ouTruncatedCLM_no_orthogonal_top N hN t ht
      upper_bound := ?_
      abs_bound := ?_ }
  · intro l hl hl_ne_one
    have hle := ouTruncated_spectral_value_le_exp_neg_t N hN t ht
      (by simpa [ouTruncatedSignature] using hl) hl_ne_one
    simpa [ouTruncatedSignature] using hle
  · intro l hl hl_ne_one
    have hl' : l ∈ spectrum ℝ (ouTruncatedCLM N t) := by
      simpa [ouTruncatedSignature] using hl
    rw [ouTruncatedCLM_spectrum_eq_range] at hl'
    rcases hl' with ⟨k, rfl⟩
    have hle :
        Real.exp (-(k : ℝ) * t) ≤ Real.exp (-t) := by
      exact ouTruncated_spectral_value_le_exp_neg_t N hN t ht
        (by
          rw [ouTruncatedCLM_spectrum_eq_range]
          exact ⟨k, rfl⟩)
        (by simpa using hl_ne_one)
    have hnonneg : 0 ≤ Real.exp (-(k : ℝ) * t) :=
      (Real.exp_pos _).le
    simpa [ouTruncatedSignature, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      using hle

theorem cvOp_ouTruncatedSignature_eq
    (N : ℕ) (hN : 1 < N) (t : ℝ) (ht : 0 < t) :
    cvOp (ouTruncatedSignature N hN t ht) = 1 - Real.exp (-t) := by
  simpa [ouTruncatedSignature] using
    cvOp_eq_gap_of_operatorSpectralGapPredicate
      (ouTruncatedSignature N hN t ht)
      (operatorSpectralGapPredicate_ouTruncatedSignature N hN t ht)

/-- The Bool counting kernel and the rank-2 OU truncation have matching
operator-norm `cvOp` whenever their parameters are related by the same
right-edge gap value.  The Bool parameter is rational in this formal surface,
so the real substitution `g = (1 - exp (-t)) / (1 + exp (-t))` is recorded
through the equality hypothesis. -/
theorem cvOp_twoStateCountingKernelContinuousSignature_eq_ouTruncatedSignature_of_gap_eq
    (g : ℚ) (hg : 0 < g) (hg1 : g < 1)
    (t : ℝ) (ht : 0 < t)
    (hgap : 2 * (g : ℝ) / (1 + (g : ℝ)) = 1 - Real.exp (-t)) :
    cvOp (twoStateCountingKernelContinuousSignature g hg) =
      cvOp (ouTruncatedSignature 2 (by norm_num) t ht) := by
  rw [cvOp_twoStateCountingKernelContinuousSignature_eq g hg hg1,
    cvOp_ouTruncatedSignature_eq 2 (by norm_num) t ht,
    hgap]

/-! ### Bool counting-kernel bridge and floor test -/

/-- The existing Bool counting measure-theoretic substrate embeds into the
continuous rank-2 operator substrate with the same right-edge gap witness. -/
theorem boolCountingKernel_measureTheoretic_to_continuousOperator
    {g δ : ℚ} {target : ℚ × ℚ}
    (hmt :
      MeasureTheoreticSpectralSignature
        (Measure.count : Measure Bool)
        (countingDiagonalMassKernel g) g δ target)
    (hg1 : g < 1) :
    ∃ sig : ContinuousOperatorSpectralSignature.{0},
      sig.gap = 2 * (g : ℝ) / (1 + (g : ℝ)) ∧
        OperatorSpectralGapPredicate sig := by
  refine
    ⟨twoStateCountingKernelContinuousSignature g hmt.diagonal_parameter_pos,
      rfl, ?_⟩
  exact
    twoStateCountingKernel_operatorSpectralGapPredicate
      g hmt.diagonal_parameter_pos hg1

/-- Identity operator on the Bool rank-2 Hilbert carrier, equipped with an
arbitrary positive claimed gap. -/
noncomputable def boolIdentityContinuousSignature (γ : ℝ) (hγ : 0 < γ) :
    ContinuousOperatorSpectralSignature where
  E := EuclideanSpace ℝ Bool
  T := 1
  isCompact :=
    isCompactOperator_of_locallyCompactSpace_dom
      (1 : EuclideanSpace ℝ Bool →L[ℝ] EuclideanSpace ℝ Bool)
  isSelfAdjoint := IsSelfAdjoint.one _
  v_top := WithLp.toLp 2 (fun _ : Bool => (1 : ℝ))
  v_top_ne := by
    intro h
    have hfalse := congrFun (congrArg WithLp.ofLp h) false
    norm_num at hfalse
  T_v_top := by
    simp
  gap := γ
  gap_pos := hγ

/-- Floor test: the constant identity operator cannot satisfy the positive-gap
operator predicate. -/
theorem boolIdentity_not_operatorSpectralGapPredicate
    (γ : ℝ) (hγ : 0 < γ) :
    ¬ OperatorSpectralGapPredicate
      (boolIdentityContinuousSignature γ hγ) := by
  intro hgap
  rcases hgap with ⟨_, hvgap, _, _, _⟩
  rcases hvgap with ⟨v, hv_ne, _hv_orth, hv_gap⟩
  have hv_eq : v = (1 - γ) • v := by
    simpa [boolIdentityContinuousSignature] using hv_gap
  apply hv_ne
  apply (WithLp.ofLp_eq_zero 2).mp
  funext x
  have hx := congrFun (congrArg WithLp.ofLp hv_eq) x
  change v.ofLp x = (1 - γ) * v.ofLp x at hx
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ
  have hmul : γ * v.ofLp x = 0 := by
    nlinarith
  exact (mul_eq_zero.mp hmul).resolve_left hγ_ne

theorem cvOp_boolIdentityContinuousSignature_eq_zero (γ : ℝ) (hγ : 0 < γ) :
    cvOp (boolIdentityContinuousSignature γ hγ) = 0 := by
  classical
  let sig := boolIdentityContinuousSignature γ hγ
  let K : Submodule ℝ sig.E := stationaryOrthogonalSubmodule sig
  have hK_ne : K ≠ ⊥ := by
    intro hbot
    let w : sig.E := WithLp.toLp 2 (fun x : Bool => if x then (1 : ℝ) else (-1 : ℝ))
    have hw_mem : w ∈ K := by
      exact (stationaryOrthogonal_mem_iff_inner sig w).2 (by
        change
          inner ℝ
            (WithLp.toLp 2 (fun x : Bool => if x then (1 : ℝ) else (-1 : ℝ)))
            (WithLp.toLp 2 (fun _ : Bool => (1 : ℝ))) = 0
        calc
          inner ℝ
              (WithLp.toLp 2 (fun x : Bool => if x then (1 : ℝ) else (-1 : ℝ)))
              (WithLp.toLp 2 (fun _ : Bool => (1 : ℝ))) =
              dotProduct (fun _ : Bool => (1 : ℝ))
                (star (fun x : Bool => if x then (1 : ℝ) else (-1 : ℝ))) :=
            EuclideanSpace.inner_toLp_toLp
              (fun x : Bool => if x then (1 : ℝ) else (-1 : ℝ))
              (fun _ : Bool => (1 : ℝ))
          _ = 0 := by
            simp [dotProduct, Fintype.univ_bool])
    have hw_zero : w = 0 := by
      simpa [hbot] using hw_mem
    have htrue := congrFun (congrArg WithLp.ofLp hw_zero) true
    have htrue_zero : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) =
            (WithLp.toLp 2 (fun x : Bool => if x then (1 : ℝ) else (-1 : ℝ))).ofLp true := by
          rfl
        _ = (0 : sig.E).ofLp true := htrue
        _ = 0 := rfl
    norm_num at htrue_zero
  have hcomp :
      sig.T.comp K.starProjection = K.starProjection := by
    ext x
    change (1 : sig.E →L[ℝ] sig.E) (K.starProjection x) = K.starProjection x
    simp
  have hnorm : ‖K.starProjection‖ = 1 :=
    Submodule.norm_starProjection K hK_ne
  dsimp [cvOp]
  rw [show (boolIdentityContinuousSignature γ hγ).T.comp
      (stationaryOrthogonalSubmodule (boolIdentityContinuousSignature γ hγ)).starProjection =
      K.starProjection by
        simpa [sig, K] using hcomp]
  rw [hnorm]
  ring

end ASIEmbedding

end Legitimacy
