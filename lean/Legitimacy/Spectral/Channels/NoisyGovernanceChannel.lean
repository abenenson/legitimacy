/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Channels.BinaryDecisionHelpers
import ChannelCapacity.Finite
import ChannelCapacity.NonDegeneracy
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# NoisyGovernanceChannel

Binary noisy-threshold governance channels for the spectral layer.

## Main Result

- `GovernanceChannel.asNoisyThresholdChannel` is the binary symmetric-noise
  channel on `BinaryDecision`.
- `GovernanceChannel.asNoisyThresholdChannel_rowSeparating` shows its two rows
  are distinct whenever `0 < η < 1 / 2`.
- `GovernanceChannel.governance_channel_capacity_unique_achieving_prior_noisy`
  packages the upstream finite uniqueness theorem for this binary channel.
-/

set_option autoImplicit false

namespace Legitimacy

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GovernanceChannel

/-- Flip a binary decision. -/
@[simp] def flipDecision : BinaryDecision → BinaryDecision
  | BinaryDecision.Permit => BinaryDecision.Deny
  | BinaryDecision.Deny => BinaryDecision.Permit

@[simp] private lemma flipDecision_flipDecision (d : BinaryDecision) :
    flipDecision (flipDecision d) = d := by
  cases d <;> rfl

/-- The row PMF of the noisy-threshold binary channel: keep the threshold answer
with mass `1 - η` and flip it with mass `η`. -/
def keepMass (η : NNReal) : NNReal :=
  (1 : NNReal) - η

noncomputable def noisyThresholdRow
    (η : NNReal) (_hη : η ≤ (1 : NNReal)) (d : BinaryDecision) : PMF BinaryDecision :=
  (PMF.bernoulli (keepMass η) (by simp [keepMass])).map
    (fun b => if b then d else flipDecision d)

@[simp] private lemma noisyThresholdRow_apply_self
    (η : NNReal) (hη : η ≤ (1 : NNReal)) (d : BinaryDecision) :
    noisyThresholdRow η hη d d = (keepMass η : ENNReal) := by
  cases d <;> simp [noisyThresholdRow, keepMass, flipDecision]

@[simp] private lemma noisyThresholdRow_apply_flip
    (η : NNReal) (hη : η ≤ (1 : NNReal)) (d : BinaryDecision) :
    noisyThresholdRow η hη d (flipDecision d) = (η : ENNReal) := by
  cases d <;> simp [noisyThresholdRow, keepMass, flipDecision]
  all_goals
    exact_mod_cast (tsub_tsub_cancel_of_le hη)

lemma le_one_of_lt_half {η : NNReal} (hη : η < (1 / 2 : NNReal)) :
    η ≤ (1 : NNReal) := by
  exact le_trans hη.le (by norm_num)

/-- A binary governance channel with symmetric output noise `η`. The input is
the deterministic threshold answer, and the output flips that answer with
probability `η`. -/
noncomputable def asNoisyThresholdChannel (η : NNReal) (hη : η < (1 / 2 : NNReal)) :
    GovernanceChannel BinaryDecision BinaryDecision where
  kernel :=
    { toFun := fun d => (noisyThresholdRow η (le_one_of_lt_half hη) d).toMeasure
      measurable' := measurable_of_finite _ }
  isMarkov := by
    refine ⟨fun d => ?_⟩
    change IsProbabilityMeasure ((noisyThresholdRow η (le_one_of_lt_half hη) d).toMeasure)
    infer_instance

@[simp] private lemma asNoisyThresholdChannel_row
    (η : NNReal) (hη : η < (1 / 2 : NNReal)) (d : BinaryDecision) :
    (asNoisyThresholdChannel η hη).row d =
      noisyThresholdRow η (le_one_of_lt_half hη) d := by
  simp [GovernanceChannel.row, asNoisyThresholdChannel]

private lemma asNoisyThresholdChannel_rows_ne
    {η : NNReal} (hη : η < (1 / 2 : NNReal)) :
    (asNoisyThresholdChannel η hη).row BinaryDecision.Permit ≠
      (asNoisyThresholdChannel η hη).row BinaryDecision.Deny := by
  intro hrow
  have happly0 :=
    congrArg (fun p : PMF BinaryDecision => p BinaryDecision.Permit) hrow
  have hleft :
      (asNoisyThresholdChannel η hη).row BinaryDecision.Permit BinaryDecision.Permit =
        (keepMass η : ENNReal) := by
    rw [asNoisyThresholdChannel_row]
    exact noisyThresholdRow_apply_self η (le_one_of_lt_half hη) BinaryDecision.Permit
  have hright :
      (asNoisyThresholdChannel η hη).row BinaryDecision.Deny BinaryDecision.Permit =
        (η : ENNReal) := by
    simpa [asNoisyThresholdChannel_row, flipDecision] using
      noisyThresholdRow_apply_flip η (le_one_of_lt_half hη) BinaryDecision.Deny
  have happly : (keepMass η : ENNReal) = (η : ENNReal) := by
    calc
      (keepMass η : ENNReal) =
          (asNoisyThresholdChannel η hη).row BinaryDecision.Permit BinaryDecision.Permit :=
        hleft.symm
      _ =
          (asNoisyThresholdChannel η hη).row BinaryDecision.Deny BinaryDecision.Permit :=
        happly0
      _ = (η : ENNReal) := hright
  have hηR : (η : ℝ) < (1 : ℝ) / 2 := by
    exact_mod_cast hη
  have hmassR : (1 : ℝ) - (η : ℝ) = (η : ℝ) := by
    calc
      (1 : ℝ) - (η : ℝ) = ((1 : ENNReal) - (η : ENNReal)).toReal := by
        rw [ENNReal.toReal_sub_of_le (by exact_mod_cast le_one_of_lt_half hη) ENNReal.one_ne_top]
        simp
      _ = ((keepMass η : NNReal) : ENNReal).toReal := by
        simp [keepMass]
      _ = (η : ENNReal).toReal := congrArg ENNReal.toReal happly
      _ = (η : ℝ) := by simp
  nlinarith [hηR, hmassR]

theorem asNoisyThresholdChannel_rowSeparating
    {η : NNReal} (hη : (0 : NNReal) < η) (hη' : η < (1 / 2 : NNReal)) :
    RowSeparating (asNoisyThresholdChannel η hη') := by
  have hη_pos : (0 : NNReal) < η := hη
  intro x₁ x₂ hneq
  cases x₁ <;> cases x₂ <;> try contradiction
  · exact asNoisyThresholdChannel_rows_ne hη'
  · intro hrow
    exact asNoisyThresholdChannel_rows_ne hη' hrow.symm

theorem asNoisyThresholdChannel_kernel_rowSeparating
    {η : NNReal} (hη : (0 : NNReal) < η) (hη' : η < (1 / 2 : NNReal)) :
    ChannelCapacity.Kernel.RowSeparating (asNoisyThresholdChannel η hη').kernel := by
  intro x₁ x₂ hneq hkernel
  have hrow :
      (asNoisyThresholdChannel η hη').row x₁ =
        (asNoisyThresholdChannel η hη').row x₂ := by
    apply PMF.toMeasure_injective
    simpa [GovernanceChannel.row] using hkernel
  exact asNoisyThresholdChannel_rowSeparating hη hη' x₁ x₂ hneq hrow

theorem asNoisyThresholdChannel_rowMatrixFullRank
    {η : NNReal} (_hη : (0 : NNReal) < η) (hη' : η < (1 / 2 : NNReal)) :
    ChannelCapacity.Kernel.RowMatrixFullRank (asNoisyThresholdChannel η hη').kernel := by
  intro w v hEq
  have hPermit := congrFun hEq BinaryDecision.Permit
  have hDeny := congrFun hEq BinaryDecision.Deny
  have hηR : (η : ℝ) < (1 : ℝ) / 2 := by
    exact_mod_cast hη'
  have hKeep : ((1 : ENNReal) - (η : ENNReal)).toReal = (1 : ℝ) - η := by
    rw [ENNReal.toReal_sub_of_le (by exact_mod_cast le_one_of_lt_half hη') ENNReal.one_ne_top]
    simp
  have hPermit' := by
    simpa [sum_binaryDecision, asNoisyThresholdChannel, noisyThresholdRow, keepMass, flipDecision,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_comm,
      mul_left_comm, mul_assoc] using hPermit
  have hDeny' := by
    simpa [sum_binaryDecision, asNoisyThresholdChannel, noisyThresholdRow, keepMass, flipDecision,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_comm,
      mul_left_comm, mul_assoc] using hDeny
  funext d
  cases d
  · nlinarith [hPermit', hDeny', hηR, hKeep]
  · nlinarith [hPermit', hDeny', hηR, hKeep]

instance : Finite BinaryDecision := inferInstance

/-- The noisy-threshold governance channel admits a unique capacity-achieving
prior in the finite `channel-capacity` sense. -/
theorem governance_channel_capacity_unique_achieving_prior_noisy
    (η : NNReal) (hη : 0 < η) (hη' : η < 1 / 2) :
    ∃! p : ProbabilityMeasure BinaryDecision,
      ChannelCapacity.mutualInformation p (asNoisyThresholdChannel η hη').kernel =
        ChannelCapacity.channelCapacity (asNoisyThresholdChannel η hη').kernel := by
  exact ChannelCapacity.exists_unique_capacity_achieving_prior_of_finite
    (asNoisyThresholdChannel η hη').kernel
    (asNoisyThresholdChannel_rowMatrixFullRank hη hη')

end GovernanceChannel

end Legitimacy
