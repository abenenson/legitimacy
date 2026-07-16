/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.ASIBridge.Native
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Legitimacy.Spectral.ASIEmbedding.MeasureTheoretic

Honest measure-theoretic embedding of the finite ASI spectral signature.

This module does not prove a continuous measure-space generalization.  It
embeds the already certified integer-indexed ASI scalar into a finite counting
measure substrate and records the exact kernel statistic that carries the
scalar: for each row, the measured diagonal kernel form is
`1 / (1 + diagonalParameter)`.  The density rows are strictly positive and mutually
absolutely continuous with counting measure, so the kernel is not the old
identity-density fallback.

A genuine continuous theorem would need a concrete reversible Markov kernel
such as the Mehler kernel, proof that its integral operator has the claimed
spectrum, and density/absolute-continuity estimates against the reference
measure.  This module only proves the operator-spectral calculation for the
specific two-state counting kernel below.
-/

set_option autoImplicit false

namespace Legitimacy

namespace ASIEmbedding

open MeasureTheory
open scoped ENNReal

/-- Measure-theoretic ASI spectral signature for a finite counting embedding.

`K x` is interpreted as a density with respect to the finite reference measure
`μ`.  The mutual absolute-continuity field rules out zero-density rows on the
counting substrate.  The named scalar pins a diagonal kernel statistic, not
operator spectral content. -/
structure MeasureTheoreticSpectralSignature
    {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℝ≥0∞) (diagonalParameter : ℚ)
    (δ : ℚ) (target : ℚ × ℚ) : Prop where
  measurable_kernel : Measurable (Function.uncurry K)
  self_adjoint : ∀ x y : Ω, K x y = K y x
  row_normalized : ∀ x : Ω, ∫⁻ y, K x y ∂μ = 1
  row_mutual_ac : ∀ x : Ω, μ.withDensity (K x) ≪ μ ∧ μ ≪ μ.withDensity (K x)
  diagonal_mass_witness :
    ∀ x : Ω,
      ∫⁻ y, K x y * (if y = x then (1 : ℝ≥0∞) else 0) ∂μ =
        ENNReal.ofReal ((1 : ℝ) / (1 + (diagonalParameter : ℝ)))
  delta_pos : 0 < δ
  diagonal_parameter_pos : 0 < diagonalParameter
  target_eq : target = (diagonalParameter, δ / diagonalParameter)

/-!
This file uses `Ω = Bool` (`N = 2` state space) for the counting embedding.
On two states, row normalization, symmetry, and the `diagonal_mass_witness`
pinning happen to determine the kernel up to permutation.  On `Fin N` for
`N ≥ 3`, the predicate admits a positive-dimensional family of off-diagonal
choices with the same `diagonalParameter`, all with different actual operator
spectra.  The Bool-only choice is therefore a SPECIFIC instance, not a general
embedding pattern.  Larger-state-space embeddings would require additional
fields constraining the off-diagonal structure, or proving operator-spectral
content directly.
-/

/-- Diagonal mass used by the finite counting embedding. -/
noncomputable def countingDiagonalMass (diagonalParameter : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 : ℝ) / (1 + (diagonalParameter : ℝ)))

/-- Off-diagonal mass used by the finite counting embedding. -/
noncomputable def countingOffDiagonalMass (diagonalParameter : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal ((diagonalParameter : ℝ) / (1 + (diagonalParameter : ℝ)))

/-- Two-state counting density kernel encoding the ASI scalar in its diagonal
kernel form. -/
noncomputable def countingDiagonalMassKernel (diagonalParameter : ℚ) (x y : Bool) : ℝ≥0∞ :=
  if x = y then countingDiagonalMass diagonalParameter
  else countingOffDiagonalMass diagonalParameter

/-!
The next definitions are the real-valued finite operator induced by the same
two-state density kernel.  On the counting space the integral operator is just
matrix multiplication by the row kernel.
-/

/-- Real matrix entries of the two-state counting density kernel. -/
noncomputable def countingSpectralKernelRealDensity
    (diagonalParameter : ℚ) (x y : Bool) : ℝ :=
  if x = y then (1 : ℝ) / (1 + (diagonalParameter : ℝ))
  else (diagonalParameter : ℝ) / (1 + (diagonalParameter : ℝ))

/-- Integral operator induced by the two-state counting density kernel on
real-valued functions on `Bool`. -/
noncomputable def countingSpectralKernelOperator
    (diagonalParameter : ℚ) (f : Bool → ℝ) (x : Bool) : ℝ :=
  ∑ y : Bool, countingSpectralKernelRealDensity diagonalParameter x y * f y

/-- The abstract two-state counting-kernel operator is the Bochner integral
operator induced by the same density kernel against counting measure. -/
theorem countingSpectralKernel_operator_is_integral
    {diagonalParameter : ℚ} (hparameter_pos : 0 < diagonalParameter)
    (f : Bool → ℝ) (x : Bool) :
    countingSpectralKernelOperator diagonalParameter f x =
      ∫ y,
        (countingDiagonalMassKernel diagonalParameter x y).toReal * f y
          ∂(Measure.count : Measure Bool) := by
  have hdiag :
      (ENNReal.ofReal ((1 + (diagonalParameter : ℝ))⁻¹)).toReal =
        (1 + (diagonalParameter : ℝ))⁻¹ := by
    exact ENNReal.toReal_ofReal (by positivity)
  have hoffdiag :
      (ENNReal.ofReal ((diagonalParameter : ℝ) / (1 + (diagonalParameter : ℝ)))).toReal =
        (diagonalParameter : ℝ) / (1 + (diagonalParameter : ℝ)) := by
    exact ENNReal.toReal_ofReal (by positivity)
  fin_cases x <;>
    simp [countingSpectralKernelOperator, countingSpectralKernelRealDensity,
      countingDiagonalMassKernel, countingDiagonalMass, countingOffDiagonalMass,
      hdiag, hoffdiag]

/-- Eigenvalues of the two-state counting-kernel operator, expressed directly
as nonzero real eigenfunctions on the finite counting space. -/
def countingSpectralKernelOperatorEigenvalueSet (diagonalParameter : ℚ) : Set ℝ :=
  {eigenvalue |
    ∃ f : (Bool → ℝ),
      f ≠ 0 ∧
        ∀ x : Bool,
          countingSpectralKernelOperator diagonalParameter f x = eigenvalue * f x}

/-- The nontrivial eigenvalue of the two-state counting-kernel operator. -/
noncomputable def countingSpectralKernelNontrivialEigenvalue (diagonalParameter : ℚ) : ℝ :=
  (1 - (diagonalParameter : ℝ)) / (1 + (diagonalParameter : ℝ))

/-- Spectral gap of the two-state counting-kernel operator, after the explicit
two-eigenvalue computation below. -/
noncomputable def countingSpectralKernelOperatorGap (diagonalParameter : ℚ) : ℝ :=
  1 - countingSpectralKernelNontrivialEigenvalue diagonalParameter

/-! ### Public two-state operator-gap surface -/

/-- Public audit-facing name for the real matrix entries of the two-state
counting density kernel.  In Bool order the matrix is
`[[1/(1+g), g/(1+g)], [g/(1+g), 1/(1+g)]]`. -/
noncomputable def twoStateCountingKernel (g : ℚ) : Bool → Bool → ℝ :=
  countingSpectralKernelRealDensity g

/-- Directly computed operator spectral gap for the two-state counting kernel
surface.  For a two-state stochastic matrix `[[1-p, p], [q, 1-q]]`, the
nontrivial eigenvalue is `1 - p - q`, hence the non-absolute spectral gap is
`p + q`.  The symmetric counting kernel below has `p = q = g/(1+g)`. -/
noncomputable def operatorSpectralGap (K : Bool → Bool → ℝ) : ℝ :=
  K false true + K true false

theorem countingSpectralKernel_operator_eigenvalues
    (diagonalParameter : ℚ) (hparameter_pos : 0 < diagonalParameter) :
    countingSpectralKernelOperatorEigenvalueSet diagonalParameter =
      ({1, countingSpectralKernelNontrivialEigenvalue diagonalParameter} : Set ℝ) := by
  ext eigenvalue
  constructor
  · intro heigenvalue
    rcases heigenvalue with ⟨f, hf, heigen⟩
    have hden : (1 : ℝ) + (diagonalParameter : ℝ) ≠ 0 := by positivity
    have hfalse :
        ((diagonalParameter : ℝ) / (1 + (diagonalParameter : ℝ))) * f true +
          ((1 : ℝ) / (1 + (diagonalParameter : ℝ))) * f false =
            eigenvalue * f false := by
      simpa [countingSpectralKernelOperator, countingSpectralKernelRealDensity]
        using heigen false
    have htrue :
        ((1 : ℝ) / (1 + (diagonalParameter : ℝ))) * f true +
          ((diagonalParameter : ℝ) / (1 + (diagonalParameter : ℝ))) * f false =
            eigenvalue * f true := by
      simpa [countingSpectralKernelOperator, countingSpectralKernelRealDensity]
        using heigen true
    have hfalse_den :
        (diagonalParameter : ℝ) * f true + f false =
          (eigenvalue * f false) * (1 + (diagonalParameter : ℝ)) := by
      have h := hfalse
      field_simp [hden] at h
      linarith
    have htrue_den :
        f true + (diagonalParameter : ℝ) * f false =
          (eigenvalue * f true) * (1 + (diagonalParameter : ℝ)) := by
      have h := htrue
      field_simp [hden] at h
      linarith
    by_cases hconst : f false = f true
    · left
      rw [← hconst] at hfalse_den
      have hf_false_ne : f false ≠ 0 := by
        intro hzero
        apply hf
        funext x
        fin_cases x <;> simp [hzero, ← hconst]
      have hprod_ne :
          f false * (1 + (diagonalParameter : ℝ)) ≠ 0 :=
        mul_ne_zero hf_false_ne hden
      have hmul :
          1 * (f false * (1 + (diagonalParameter : ℝ))) =
            eigenvalue * (f false * (1 + (diagonalParameter : ℝ))) := by
        nlinarith
      have hdiv :=
        congrArg
          (fun t : ℝ => t / (f false * (1 + (diagonalParameter : ℝ)))) hmul
      field_simp [hprod_ne] at hdiv
      linarith
    · right
      have hdiff :
          (1 - (diagonalParameter : ℝ)) * (f false - f true) =
            eigenvalue * (1 + (diagonalParameter : ℝ)) * (f false - f true) := by
        nlinarith
      have hdiff_ne : f false - f true ≠ 0 := sub_ne_zero.mpr hconst
      have hprod_ne :
          (1 + (diagonalParameter : ℝ)) * (f false - f true) ≠ 0 :=
        mul_ne_zero hden hdiff_ne
      have hdiv :=
        congrArg
          (fun t : ℝ =>
            t / ((1 + (diagonalParameter : ℝ)) * (f false - f true))) hdiff
      field_simp [hden, hdiff_ne, hprod_ne] at hdiv
      have heq :
          eigenvalue = countingSpectralKernelNontrivialEigenvalue diagonalParameter := by
        rw [eq_comm]
        simp [countingSpectralKernelNontrivialEigenvalue]
        field_simp [hden]
        linarith
      simp [heq]
  · intro heigenvalue
    rcases heigenvalue with rfl | hsecond
    · refine ⟨fun _ : Bool => (1 : ℝ), ?_, ?_⟩
      · intro hzero
        have hfalse := congrFun hzero false
        norm_num at hfalse
      · intro x
        fin_cases x <;>
          simp [countingSpectralKernelOperator, countingSpectralKernelRealDensity]
        all_goals
          have hden : (1 : ℝ) + (diagonalParameter : ℝ) ≠ 0 := by positivity
          field_simp [hden]
          try ring
    · rw [hsecond]
      refine ⟨fun x : Bool => if x then (1 : ℝ) else (-1 : ℝ), ?_, ?_⟩
      · intro hzero
        have htrue := congrFun hzero true
        norm_num at htrue
      · intro x
        fin_cases x <;>
          simp [countingSpectralKernelOperator, countingSpectralKernelRealDensity,
            countingSpectralKernelNontrivialEigenvalue]
        all_goals
          have hden : (1 : ℝ) + (diagonalParameter : ℝ) ≠ 0 := by positivity
          field_simp [hden]
          ring

theorem countingSpectralKernel_operator_gap
    (diagonalParameter : ℚ) (hparameter_pos : 0 < diagonalParameter) :
    countingSpectralKernelOperatorGap diagonalParameter =
      2 * (diagonalParameter : ℝ) / (1 + (diagonalParameter : ℝ)) := by
  have hden : (1 : ℝ) + (diagonalParameter : ℝ) ≠ 0 := by positivity
  simp [countingSpectralKernelOperatorGap, countingSpectralKernelNontrivialEigenvalue]
  field_simp [hden]
  ring

theorem twoStateCountingKernel_operatorSpectralGap_eq_countingSpectralKernelOperatorGap
    (g : ℚ) (hg : 0 < g) :
    operatorSpectralGap (twoStateCountingKernel g) =
      countingSpectralKernelOperatorGap g := by
  have hden : (1 : ℝ) + (g : ℝ) ≠ 0 := by positivity
  simp [operatorSpectralGap, twoStateCountingKernel, countingSpectralKernelRealDensity,
    countingSpectralKernelOperatorGap, countingSpectralKernelNontrivialEigenvalue]
  field_simp [hden]
  ring

/-- Closed form for the operator spectral gap of the two-state counting kernel.

The eigenvalue theorem above identifies the two eigenvalues as `1` and
`(1-g)/(1+g)`; the gap is therefore `1 - (1-g)/(1+g) = 2g/(1+g)`. -/
theorem twoStateCountingKernel_operatorSpectralGap_eq
    (g : ℚ) (hg : 0 < g) :
    operatorSpectralGap (twoStateCountingKernel g) =
      2 * (g : ℝ) / (1 + (g : ℝ)) := by
  calc
    operatorSpectralGap (twoStateCountingKernel g) =
        countingSpectralKernelOperatorGap g :=
      twoStateCountingKernel_operatorSpectralGap_eq_countingSpectralKernelOperatorGap g hg
    _ = 2 * (g : ℝ) / (1 + (g : ℝ)) :=
      countingSpectralKernel_operator_gap g hg

theorem countingDiagonalMassKernel_self_adjoint (diagonalParameter : ℚ) :
    ∀ x y : Bool,
      countingDiagonalMassKernel diagonalParameter x y =
        countingDiagonalMassKernel diagonalParameter y x := by
  intro x y
  fin_cases x <;> fin_cases y <;> simp [countingDiagonalMassKernel]

theorem countingDiagonalMassKernel_row_normalized
    {diagonalParameter : ℚ} (hparameter_pos : 0 < diagonalParameter) (x : Bool) :
    ∫⁻ y, countingDiagonalMassKernel diagonalParameter x y
        ∂(Measure.count : Measure Bool) = 1 := by
  fin_cases x <;>
    simp [countingDiagonalMassKernel, countingDiagonalMass, countingOffDiagonalMass,
      MeasureTheory.lintegral_count]
  all_goals
    rw [← ENNReal.ofReal_add]
    · rw [← ENNReal.ofReal_one]
      congr 1
      have hden : ((1 : ℝ) + (diagonalParameter : ℝ)) ≠ 0 := by positivity
      field_simp [hden]
      try ring
    · positivity
    · positivity

theorem countingDiagonalMassKernel_positive
    {diagonalParameter : ℚ} (hparameter_pos : 0 < diagonalParameter) :
    ∀ x y : Bool, 0 < countingDiagonalMassKernel diagonalParameter x y := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    simp [countingDiagonalMassKernel, countingDiagonalMass, countingOffDiagonalMass]
  all_goals positivity

theorem count_absolutelyContinuous_withDensity_of_positive
    {f : Bool → ℝ≥0∞} (hf : Measurable f) (hpos : ∀ y : Bool, 0 < f y) :
    (Measure.count : Measure Bool) ≪ (Measure.count : Measure Bool).withDensity f := by
  intro s hs
  rw [withDensity_apply_eq_zero hf] at hs
  have hsupport : {x | f x ≠ 0} ∩ s = s := by
    ext y
    simp [ne_of_gt (hpos y)]
  simpa [hsupport] using hs

theorem countingDiagonalMassKernel_row_mutual_ac
    {diagonalParameter : ℚ} (hparameter_pos : 0 < diagonalParameter) :
    ∀ x : Bool,
      (Measure.count : Measure Bool).withDensity (countingDiagonalMassKernel diagonalParameter x) ≪
          Measure.count ∧
        (Measure.count : Measure Bool) ≪
          (Measure.count : Measure Bool).withDensity
            (countingDiagonalMassKernel diagonalParameter x) := by
  intro x
  refine ⟨MeasureTheory.withDensity_absolutelyContinuous _ _, ?_⟩
  exact
    count_absolutelyContinuous_withDensity_of_positive
      (measurable_of_countable _) (countingDiagonalMassKernel_positive hparameter_pos x)

theorem countingDiagonalMassKernel_diagonal_mass_witness (diagonalParameter : ℚ) :
    ∀ x : Bool,
      ∫⁻ y,
          countingDiagonalMassKernel diagonalParameter x y *
            (if y = x then (1 : ℝ≥0∞) else 0) ∂(Measure.count : Measure Bool) =
        ENNReal.ofReal ((1 : ℝ) / (1 + (diagonalParameter : ℝ))) := by
  intro x
  fin_cases x <;>
    simp [countingDiagonalMassKernel, countingDiagonalMass, MeasureTheory.lintegral_count]

/-- Finite counting embedding of the size-indexed ASI signature.  The carrier
is a two-point counting space whose strictly positive symmetric density kernel
records the ASI scalar in its measured diagonal form. -/
theorem ASISpectralSignatureN.to_measureTheoretic_countingEmbedding
    {N : Nat} {δ : ℚ} {target : ℚ × ℚ}
    (hasi : ASIBridge.ASISpectralSignatureN N δ target) :
    MeasureTheoreticSpectralSignature
      (Measure.count : Measure Bool)
      (countingDiagonalMassKernel (ASIBridge.ASIDepth3CriticalCV N))
      (ASIBridge.ASIDepth3CriticalCV N) δ target := by
  rcases hasi with ⟨hδ, hgap_pos, htarget⟩
  refine
    { measurable_kernel := measurable_of_countable _
      self_adjoint := countingDiagonalMassKernel_self_adjoint _
      row_normalized := countingDiagonalMassKernel_row_normalized hgap_pos
      row_mutual_ac := countingDiagonalMassKernel_row_mutual_ac hgap_pos
      diagonal_mass_witness := countingDiagonalMassKernel_diagonal_mass_witness _
      delta_pos := hδ
      diagonal_parameter_pos := hgap_pos
      target_eq := htarget }

/-- Original five-node ASI signature embedded into the finite counting
measure-theoretic substrate. -/
theorem ASISpectralSignature.to_measureTheoretic_countingEmbedding
    {δ : ℚ} {target : ℚ × ℚ}
    (hasi : ASISpectralSignature δ target) :
    MeasureTheoreticSpectralSignature
      (Measure.count : Measure Bool)
      (countingDiagonalMassKernel (ASIBridge.ASIDepth3CriticalCV 5))
      (ASIBridge.ASIDepth3CriticalCV 5) δ target := by
  exact
    ASISpectralSignatureN.to_measureTheoretic_countingEmbedding
      (ASIBridge.ASISpectralSignatureN_five_of_ASISpectralSignature hasi)

/-- Universalized finite counting embedding supported by the native ASI
substrate.  This is a forward embedding only: it preserves the certified ASI
target scalar inside a finite measure kernel and does not claim a converse or
continuous generalization. -/
theorem ASISpectralSignature_embeds_in_measure_theoretic_counting
    (N : Nat) (δ : ℚ) (target : ℚ × ℚ)
    (hasi : ASIBridge.ASISpectralSignatureN N δ target) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : DecidableEq Ω)
      (μ : Measure Ω) (_ : IsFiniteMeasure μ)
      (K : Ω → Ω → ℝ≥0∞) (diagonalParameter : ℚ),
        MeasureTheoreticSpectralSignature μ K diagonalParameter δ target := by
  refine ⟨Bool, inferInstance, inferInstance, Measure.count, inferInstance,
    countingDiagonalMassKernel (ASIBridge.ASIDepth3CriticalCV N),
    ASIBridge.ASIDepth3CriticalCV N, ?_⟩
  exact ASISpectralSignatureN.to_measureTheoretic_countingEmbedding hasi

end ASIEmbedding

end Legitimacy
