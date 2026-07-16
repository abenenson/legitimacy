/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Channels.ThresholdGovernanceChannel
import ChannelCapacity.Finite
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Binary decision helpers

Shared finite-sum and entropy bounds for binary governance decisions.
-/

set_option autoImplicit false

namespace Legitimacy

open MeasureTheory ProbabilityTheory

namespace GovernanceChannel

def binaryDecisionEquivBool : BinaryDecision ≃ Bool where
  toFun
    | BinaryDecision.Permit => true
    | BinaryDecision.Deny => false
  invFun
    | true => BinaryDecision.Permit
    | false => BinaryDecision.Deny
  left_inv := by
    intro d
    cases d <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

lemma sum_binaryDecision (f : BinaryDecision → ℝ) :
    ∑ x, f x = f BinaryDecision.Permit + f BinaryDecision.Deny := by
  calc
    ∑ x, f x = ∑ b : Bool, f (binaryDecisionEquivBool.symm b) := by
      exact Fintype.sum_equiv binaryDecisionEquivBool f
        (fun b => f (binaryDecisionEquivBool.symm b)) (by
          intro x
          cases x <;> rfl)
    _ = f BinaryDecision.Permit + f BinaryDecision.Deny := by
      simp [binaryDecisionEquivBool]

lemma binaryDecision_entropy_le_log_two (p : ProbabilityMeasure BinaryDecision) :
    ChannelCapacity.ProbabilityMeasure.entropy p ≤ Real.log 2 := by
  let a : ℝ := (p.toMeasure {BinaryDecision.Permit}).toReal
  let b : ℝ := (p.toMeasure {BinaryDecision.Deny}).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hsum : a + b = 1 := by
    have h := ChannelCapacity.sum_toReal_singletonMass p
    simpa [sum_binaryDecision, a, b] using h
  have hconc := (Real.concaveOn_negMulLog.2 (by simpa using ha) (by simpa using hb)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1))
  have hmid : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b = 1 / 2 := by
    change (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = 1 / 2
    nlinarith
  have hle : (1 / 2 : ℝ) * Real.negMulLog a + (1 / 2 : ℝ) * Real.negMulLog b ≤
      Real.negMulLog (1 / 2 : ℝ) := by
    rw [hmid] at hconc
    simpa using hconc
  have hle2 : Real.negMulLog a + Real.negMulLog b ≤ 2 * Real.negMulLog (1 / 2 : ℝ) := by
    nlinarith
  have hlog : 2 * Real.negMulLog (1 / 2 : ℝ) = Real.log 2 := by
    rw [Real.negMulLog]
    rw [show Real.log (1 / 2 : ℝ) = - Real.log 2 by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      rw [Real.log_inv]]
    ring
  calc
    ChannelCapacity.ProbabilityMeasure.entropy p = Real.negMulLog a + Real.negMulLog b := by
      simp [ChannelCapacity.ProbabilityMeasure.entropy, sum_binaryDecision, a, b]
    _ ≤ 2 * Real.negMulLog (1 / 2 : ℝ) := hle2
    _ = Real.log 2 := hlog

end GovernanceChannel

end Legitimacy
