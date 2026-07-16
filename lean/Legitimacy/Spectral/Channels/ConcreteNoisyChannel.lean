/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Channels.NoisyGovernanceCapacity
import Legitimacy.Spectral.Channels.BinaryDecisionHelpers
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Concrete noisy governance channel capacity equality

This module gives a concrete finite noisy channel calibrated to a concrete graph
CV value. The construction used here is a binary erasure channel: with
probability `ρ` it reveals the binary decision, and with probability `1 - ρ` it
returns erasure. Its Shannon capacity in the imported `ChannelCapacity` sense is
computed directly as `ρ * log 2` by reducing mutual information to binary input
entropy and proving the uniform prior maximizes that entropy.
-/

set_option autoImplicit false

namespace Legitimacy

open MeasureTheory ProbabilityTheory

namespace GovernanceChannel

variable {n : Nat}

noncomputable def uniformBinaryDecisionPrior : ProbabilityMeasure BinaryDecision :=
  ⟨((PMF.bernoulli (1 / 2 : NNReal) (by norm_num)).map
      (fun b => if b then BinaryDecision.Permit else BinaryDecision.Deny)).toMeasure,
    by infer_instance⟩

lemma uniformBinaryDecisionPrior_apply_permit :
    (uniformBinaryDecisionPrior.toMeasure {BinaryDecision.Permit}).toReal = (1 / 2 : ℝ) := by
  simp [uniformBinaryDecisionPrior]

lemma uniformBinaryDecisionPrior_apply_deny :
    (uniformBinaryDecisionPrior.toMeasure {BinaryDecision.Deny}).toReal = (1 / 2 : ℝ) := by
  simp [uniformBinaryDecisionPrior]

lemma uniformBinaryDecisionPrior_entropy :
    ChannelCapacity.ProbabilityMeasure.entropy uniformBinaryDecisionPrior = Real.log 2 := by
  simp [ChannelCapacity.ProbabilityMeasure.entropy, sum_binaryDecision,
    uniformBinaryDecisionPrior_apply_permit, uniformBinaryDecisionPrior_apply_deny]
  rw [Real.negMulLog]
  rw [Real.log_inv]
  ring

instance optionBinaryDecisionMeasurableSpace : MeasurableSpace (Option BinaryDecision) := ⊤

instance optionBinaryDecisionMeasurableSingletonClass :
    MeasurableSingletonClass (Option BinaryDecision) :=
  ⟨fun _ => trivial⟩

/-- Row PMF for a binary erasure channel with reveal probability `ρ`. -/
noncomputable def erasureRow (ρ : NNReal) (hρ : ρ ≤ 1)
    (d : BinaryDecision) : PMF (Option BinaryDecision) :=
  (PMF.bernoulli ρ hρ).map (fun b => if b then some d else none)

/-- Binary erasure channel: revealed decision with probability `ρ`, erasure otherwise. -/
noncomputable def asErasureDecisionChannel (ρ : NNReal) (hρ : ρ ≤ 1) :
    GovernanceChannel BinaryDecision (Option BinaryDecision) where
  kernel :=
    { toFun := fun d => (erasureRow ρ hρ d).toMeasure
      measurable' := measurable_of_finite _ }
  isMarkov := by
    refine ⟨fun d => ?_⟩
    change IsProbabilityMeasure ((erasureRow ρ hρ d).toMeasure)
    infer_instance

@[simp] lemma erasureRow_apply_none (ρ : NNReal) (hρ : ρ ≤ 1) (d : BinaryDecision) :
    erasureRow ρ hρ d none = ((1 : NNReal) - ρ : NNReal) := by
  cases d <;> simp [erasureRow]

@[simp] lemma erasureRow_apply_some_self (ρ : NNReal) (hρ : ρ ≤ 1) (d : BinaryDecision) :
    erasureRow ρ hρ d (some d) = ρ := by
  cases d <;> simp [erasureRow]

@[simp] lemma erasureRow_apply_some_flip (ρ : NNReal) (hρ : ρ ≤ 1) (d : BinaryDecision) :
    erasureRow ρ hρ d (some (flipDecision d)) = 0 := by
  cases d <;> simp [erasureRow, flipDecision]

lemma erasure_kernel_toReal_none (ρ : NNReal) (hρ : ρ ≤ 1) (d : BinaryDecision) :
    (((asErasureDecisionChannel ρ hρ).kernel d {none}).toReal) = 1 - (ρ : ℝ) := by
  cases d <;> simp [asErasureDecisionChannel, erasureRow]
  all_goals
    rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hρ) ENNReal.one_ne_top]
    simp

lemma erasure_kernel_toReal_some_self (ρ : NNReal) (hρ : ρ ≤ 1) (d : BinaryDecision) :
    (((asErasureDecisionChannel ρ hρ).kernel d {some d}).toReal) = (ρ : ℝ) := by
  cases d <;> simp [asErasureDecisionChannel, erasureRow]

lemma erasure_kernel_toReal_some_flip (ρ : NNReal) (hρ : ρ ≤ 1) (d : BinaryDecision) :
    (((asErasureDecisionChannel ρ hρ).kernel d {some (flipDecision d)}).toReal) = 0 := by
  cases d <;> simp [asErasureDecisionChannel, erasureRow, flipDecision]

lemma erasure_rowEntropy (ρ : NNReal) (hρ : ρ ≤ 1) (d : BinaryDecision) :
    ChannelCapacity.Kernel.rowEntropy (asErasureDecisionChannel ρ hρ).kernel d =
      Real.negMulLog (1 - (ρ : ℝ)) + Real.negMulLog (ρ : ℝ) := by
  unfold ChannelCapacity.Kernel.rowEntropy ChannelCapacity.ProbabilityMeasure.entropy
  rw [Fintype.sum_option]
  rw [sum_binaryDecision]
  cases d
  · simp [ChannelCapacity.Kernel.rowProbabilityMeasure, asErasureDecisionChannel, erasureRow]
    rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hρ) ENNReal.one_ne_top]
    simp
  · simp [ChannelCapacity.Kernel.rowProbabilityMeasure, asErasureDecisionChannel, erasureRow]
    rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hρ) ENNReal.one_ne_top]
    simp

lemma erasure_conditionalEntropy (ρ : NNReal) (hρ : ρ ≤ 1)
    (p : ProbabilityMeasure BinaryDecision) :
    ChannelCapacity.conditionalEntropy p (asErasureDecisionChannel ρ hρ).kernel =
      Real.negMulLog (1 - (ρ : ℝ)) + Real.negMulLog (ρ : ℝ) := by
  unfold ChannelCapacity.conditionalEntropy
  simp_rw [erasure_rowEntropy]
  rw [← Finset.sum_mul]
  rw [ChannelCapacity.sum_toReal_singletonMass]
  ring

lemma erasure_outputPrior_toReal_none (ρ : NNReal) (hρ : ρ ≤ 1)
    (p : ProbabilityMeasure BinaryDecision) :
    (((ChannelCapacity.outputPrior (asErasureDecisionChannel ρ hρ).kernel p).toMeasure {none}).toReal) =
      1 - (ρ : ℝ) := by
  rw [ChannelCapacity.toReal_outputPrior_apply_singleton]
  rw [sum_binaryDecision]
  simp [erasure_kernel_toReal_none]
  have h := ChannelCapacity.sum_toReal_singletonMass p
  rw [sum_binaryDecision] at h
  linear_combination (1 - (ρ : ℝ)) * h

lemma erasure_outputPrior_toReal_some_permit (ρ : NNReal) (hρ : ρ ≤ 1)
    (p : ProbabilityMeasure BinaryDecision) :
    (((ChannelCapacity.outputPrior (asErasureDecisionChannel ρ hρ).kernel p).toMeasure
      {some BinaryDecision.Permit}).toReal) =
      (ρ : ℝ) * (p.toMeasure {BinaryDecision.Permit}).toReal := by
  rw [ChannelCapacity.toReal_outputPrior_apply_singleton]
  rw [sum_binaryDecision]
  have hcross : (((asErasureDecisionChannel ρ hρ).kernel BinaryDecision.Deny
      {some BinaryDecision.Permit}).toReal) = 0 := by
    simpa [flipDecision] using erasure_kernel_toReal_some_flip ρ hρ BinaryDecision.Deny
  rw [hcross]
  simp [erasure_kernel_toReal_some_self]
  ring

lemma erasure_outputPrior_toReal_some_deny (ρ : NNReal) (hρ : ρ ≤ 1)
    (p : ProbabilityMeasure BinaryDecision) :
    (((ChannelCapacity.outputPrior (asErasureDecisionChannel ρ hρ).kernel p).toMeasure
      {some BinaryDecision.Deny}).toReal) =
      (ρ : ℝ) * (p.toMeasure {BinaryDecision.Deny}).toReal := by
  rw [ChannelCapacity.toReal_outputPrior_apply_singleton]
  rw [sum_binaryDecision]
  have hcross : (((asErasureDecisionChannel ρ hρ).kernel BinaryDecision.Permit
      {some BinaryDecision.Deny}).toReal) = 0 := by
    simpa [flipDecision] using erasure_kernel_toReal_some_flip ρ hρ BinaryDecision.Permit
  rw [hcross]
  simp [erasure_kernel_toReal_some_self]
  ring

lemma erasure_output_entropy (ρ : NNReal) (hρ : ρ ≤ 1)
    (p : ProbabilityMeasure BinaryDecision) :
    ChannelCapacity.ProbabilityMeasure.entropy
        (ChannelCapacity.outputPrior (asErasureDecisionChannel ρ hρ).kernel p) =
      Real.negMulLog (1 - (ρ : ℝ)) + Real.negMulLog (ρ : ℝ) +
        (ρ : ℝ) * ChannelCapacity.ProbabilityMeasure.entropy p := by
  let a : ℝ := (p.toMeasure {BinaryDecision.Permit}).toReal
  let b : ℝ := (p.toMeasure {BinaryDecision.Deny}).toReal
  have hsum : a + b = 1 := by
    have h := ChannelCapacity.sum_toReal_singletonMass p
    simpa [sum_binaryDecision, a, b] using h
  unfold ChannelCapacity.ProbabilityMeasure.entropy
  rw [Fintype.sum_option]
  rw [sum_binaryDecision]
  rw [sum_binaryDecision]
  rw [erasure_outputPrior_toReal_none, erasure_outputPrior_toReal_some_permit,
    erasure_outputPrior_toReal_some_deny]
  change Real.negMulLog (1 - (ρ : ℝ)) +
      (Real.negMulLog ((ρ : ℝ) * a) + Real.negMulLog ((ρ : ℝ) * b)) =
    Real.negMulLog (1 - (ρ : ℝ)) + Real.negMulLog (ρ : ℝ) +
      (ρ : ℝ) * (Real.negMulLog a + Real.negMulLog b)
  rw [Real.negMulLog_mul, Real.negMulLog_mul]
  linear_combination (Real.negMulLog (ρ : ℝ)) * hsum

lemma erasure_mutualInformation_eq (ρ : NNReal) (hρ : ρ ≤ 1)
    (p : ProbabilityMeasure BinaryDecision) :
    ChannelCapacity.mutualInformation p (asErasureDecisionChannel ρ hρ).kernel =
      (ρ : ℝ) * ChannelCapacity.ProbabilityMeasure.entropy p := by
  rw [ChannelCapacity.mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy]
  rw [erasure_output_entropy, erasure_conditionalEntropy]
  ring

/-- The binary erasure channel has capacity `ρ * log 2` nats. -/
theorem erasure_channelCapacity_eq (ρ : NNReal) (hρ : ρ ≤ 1) :
    ChannelCapacity.channelCapacity (asErasureDecisionChannel ρ hρ).kernel =
      (ρ : ℝ) * Real.log 2 := by
  have hmax : IsMaxOn
      (fun q : ProbabilityMeasure BinaryDecision =>
        ChannelCapacity.mutualInformation q (asErasureDecisionChannel ρ hρ).kernel)
      Set.univ uniformBinaryDecisionPrior := by
    rw [isMaxOn_univ_iff]
    intro q
    rw [erasure_mutualInformation_eq, erasure_mutualInformation_eq,
      uniformBinaryDecisionPrior_entropy]
    exact mul_le_mul_of_nonneg_left (binaryDecision_entropy_le_log_two q) (by exact_mod_cast ρ.2)
  calc
    ChannelCapacity.channelCapacity (asErasureDecisionChannel ρ hρ).kernel =
        ChannelCapacity.mutualInformation uniformBinaryDecisionPrior
          (asErasureDecisionChannel ρ hρ).kernel :=
      ChannelCapacity.channelCapacity_eq_of_isMaxOn_univ _ hmax
    _ = (ρ : ℝ) * Real.log 2 := by
      rw [erasure_mutualInformation_eq, uniformBinaryDecisionPrior_entropy]

/-- Reveal probability giving erasure-channel capacity exactly `1 / 2` nat. -/
noncomputable def halfNatRevealProbability : NNReal :=
  ⟨(1 / 2 : ℝ) / Real.log 2,
    le_of_lt (div_pos (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2)))⟩

lemma halfNatRevealProbability_pos : 0 < halfNatRevealProbability := by
  exact div_pos (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2))

lemma halfNatRevealProbability_le_one : halfNatRevealProbability ≤ 1 := by
  change (1 / 2 : ℝ) / Real.log 2 ≤ 1
  have hlog : (1 / 2 : ℝ) < Real.log 2 := by
    exact lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9
  exact (div_le_one (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog.le

lemma halfNatRevealProbability_capacity_value :
    (halfNatRevealProbability : ℝ) * Real.log 2 = (1 / 2 : ℝ) := by
  dsimp [halfNatRevealProbability]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

/-- Reveal probability giving erasure-channel capacity exactly `2 / 3` nat. -/
noncomputable def twoThirdsNatRevealProbability : NNReal :=
  ⟨(2 / 3 : ℝ) / Real.log 2,
    le_of_lt (div_pos (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2)))⟩

lemma twoThirdsNatRevealProbability_pos : 0 < twoThirdsNatRevealProbability := by
  exact div_pos (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2))

lemma twoThirdsNatRevealProbability_le_one : twoThirdsNatRevealProbability ≤ 1 := by
  change (2 / 3 : ℝ) / Real.log 2 ≤ 1
  have hlog : (2 / 3 : ℝ) < Real.log 2 := by
    exact lt_trans (by norm_num : (2 / 3 : ℝ) < 0.6931471803) Real.log_two_gt_d9
  exact (div_le_one (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog.le

lemma twoThirdsNatRevealProbability_capacity_value :
    (twoThirdsNatRevealProbability : ℝ) * Real.log 2 = (2 / 3 : ℝ) := by
  dsimp [twoThirdsNatRevealProbability]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

/-- Reveal probability giving erasure-channel capacity exactly `3 / 8` nat. -/
noncomputable def threeEighthsNatRevealProbability : NNReal :=
  ⟨(3 / 8 : ℝ) / Real.log 2,
    le_of_lt (div_pos (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2)))⟩

lemma threeEighthsNatRevealProbability_pos : 0 < threeEighthsNatRevealProbability := by
  exact div_pos (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2))

lemma threeEighthsNatRevealProbability_le_one : threeEighthsNatRevealProbability ≤ 1 := by
  change (3 / 8 : ℝ) / Real.log 2 ≤ 1
  have hlog : (3 / 8 : ℝ) < Real.log 2 := by
    exact lt_trans (by norm_num : (3 / 8 : ℝ) < 0.6931471803) Real.log_two_gt_d9
  exact (div_le_one (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog.le

lemma threeEighthsNatRevealProbability_capacity_value :
    (threeEighthsNatRevealProbability : ℝ) * Real.log 2 = (3 / 8 : ℝ) := by
  dsimp [threeEighthsNatRevealProbability]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

/-- Exact CV value for the half-scale uniform triangle calibration signal. -/
lemma uniTriGraph_cv_halfSig : uniTriGraph.cv halfSig = 1 / 2 := by
  native_decide

lemma uniTriGraph_cv_halfSig_pos : 0 < uniTriGraph.cv halfSig := by
  rw [uniTriGraph_cv_halfSig]
  norm_num

lemma uniTriGraph_cv_halfSig_lt_one : uniTriGraph.cv halfSig < 1 := by
  rw [uniTriGraph_cv_halfSig]
  norm_num

/-- Exact CV value for the half-scale asymmetric-triangle calibration signal. -/
lemma asymTriGraph_cv_asymTriHalfSig : asymTriGraph.cv asymTriHalfSig = 2 / 3 := by
  native_decide

lemma asymTriGraph_cv_asymTriHalfSig_pos : 0 < asymTriGraph.cv asymTriHalfSig := by
  rw [asymTriGraph_cv_asymTriHalfSig]
  norm_num

lemma asymTriGraph_cv_asymTriHalfSig_lt_log_two :
    (asymTriGraph.cv asymTriHalfSig : ℝ) < Real.log 2 := by
  rw [asymTriGraph_cv_asymTriHalfSig]
  norm_num
  exact lt_trans (by norm_num : (2 / 3 : ℝ) < 0.6931471803) Real.log_two_gt_d9

/-- Exact CV value for the half-scale near-path calibration signal. -/
lemma nearPathGraph_cv_nearPathHalfSig : nearPathGraph.cv nearPathHalfSig = 1 / 2 := by
  native_decide

lemma nearPathGraph_cv_nearPathHalfSig_pos : 0 < nearPathGraph.cv nearPathHalfSig := by
  rw [nearPathGraph_cv_nearPathHalfSig]
  norm_num

lemma nearPathGraph_cv_nearPathHalfSig_lt_log_two :
    (nearPathGraph.cv nearPathHalfSig : ℝ) < Real.log 2 := by
  rw [nearPathGraph_cv_nearPathHalfSig]
  norm_num
  exact lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9

/-- Exact CV value for the half-scale bottleneck calibration signal. -/
lemma bottleneckGraph_cv_bottleneckHalfSig :
    bottleneckGraph.cv bottleneckHalfSig = 1 / 2 := by
  native_decide

lemma bottleneckGraph_cv_bottleneckHalfSig_pos :
    0 < bottleneckGraph.cv bottleneckHalfSig := by
  rw [bottleneckGraph_cv_bottleneckHalfSig]
  norm_num

lemma bottleneckGraph_cv_bottleneckHalfSig_lt_log_two :
    (bottleneckGraph.cv bottleneckHalfSig : ℝ) < Real.log 2 := by
  rw [bottleneckGraph_cv_bottleneckHalfSig]
  norm_num
  exact lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9

/-- Exact CV value for the half-scale `K₅` calibration signal. -/
lemma uniK5_cv_uniK5HalfSig : uniK5.cv uniK5HalfSig = 3 / 8 := by
  native_decide

lemma uniK5_cv_uniK5HalfSig_pos : 0 < uniK5.cv uniK5HalfSig := by
  rw [uniK5_cv_uniK5HalfSig]
  norm_num

lemma uniK5_cv_uniK5HalfSig_lt_log_two :
    (uniK5.cv uniK5HalfSig : ℝ) < Real.log 2 := by
  rw [uniK5_cv_uniK5HalfSig]
  norm_num
  exact lt_trans (by norm_num : (3 / 8 : ℝ) < 0.6931471803) Real.log_two_gt_d9

/-- A graph/signal calibration for the concrete binary erasure channel. -/
structure ConcreteNoisyCStarCalibration
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) where
  reveal : NNReal
  reveal_pos : 0 < reveal
  reveal_le_one : reveal ≤ 1
  capacity_eq_cv :
    (reveal : ℝ) * Real.log 2 = (G.cv s : ℝ)

/-- Any graph/signal pair with `cv` in the erasure-channel reachable range is inhabited. -/
theorem existsConcreteNoisyCStarCalibration_of_cv_pos_lt_log_two
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ)
    (hcv_pos : 0 < G.cv s) (hcv_lt : (G.cv s : ℝ) < Real.log 2) :
    ∃ _cal : ConcreteNoisyCStarCalibration G s, True := by
  have hlog_pos : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hcvR_pos : (0 : ℝ) < (G.cv s : ℝ) := by
    exact_mod_cast hcv_pos
  let reveal : NNReal := ⟨(G.cv s : ℝ) / Real.log 2, le_of_lt (div_pos hcvR_pos hlog_pos)⟩
  have reveal_pos : 0 < reveal := by
    change (0 : ℝ) < (G.cv s : ℝ) / Real.log 2
    exact div_pos hcvR_pos hlog_pos
  have reveal_le_one : reveal ≤ 1 := by
    change (G.cv s : ℝ) / Real.log 2 ≤ 1
    exact (div_le_one hlog_pos).mpr hcv_lt.le
  refine ⟨⟨reveal, reveal_pos, reveal_le_one, ?_⟩, trivial⟩
  dsimp [reveal]
  field_simp [ne_of_gt hlog_pos]

/-- The concrete calibrated noisy channel for a graph/signal pair. -/
noncomputable def ConcreteNoisyCStarCalibration.channel
    {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
    (cal : ConcreteNoisyCStarCalibration G s) :
    GovernanceChannel BinaryDecision (Option BinaryDecision) :=
  asErasureDecisionChannel cal.reveal cal.reveal_le_one

/-- The concrete erasure channel capacity equality derived from the channel theorem. -/
theorem concreteNoisyChannel_channelCapacity_eq_cv
    {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
    (cal : ConcreteNoisyCStarCalibration G s) :
    ChannelCapacity.channelCapacity cal.channel.kernel = (G.cv s : ℝ) := by
  calc
    ChannelCapacity.channelCapacity cal.channel.kernel =
        (cal.reveal : ℝ) * Real.log 2 := by
      exact erasure_channelCapacity_eq cal.reveal cal.reveal_le_one
    _ = (G.cv s : ℝ) := cal.capacity_eq_cv

/-- Concrete inhabitant closing the graph/channel calibration for `cv = 1 / 2`. -/
noncomputable def concreteHalfNoisyCStarCalibration :
    ConcreteNoisyCStarCalibration uniTriGraph halfSig where
  reveal := halfNatRevealProbability
  reveal_pos := halfNatRevealProbability_pos
  reveal_le_one := halfNatRevealProbability_le_one
  capacity_eq_cv := by
    rw [halfNatRevealProbability_capacity_value, uniTriGraph_cv_halfSig]
    norm_num

/-- The concrete inhabitant's equality field is the derived capacity computation. -/
theorem concreteHalfNoisyCStarCalibration_capacity_eq_true :
    ChannelCapacity.channelCapacity concreteHalfNoisyCStarCalibration.channel.kernel =
      (uniTriGraph.cv halfSig : ℝ) :=
  concreteNoisyChannel_channelCapacity_eq_cv concreteHalfNoisyCStarCalibration

/-- Concrete inhabitant closing the asymmetric-triangle graph/channel calibration. -/
noncomputable def concreteAsymTriHalfNoisyCStarCalibration :
    ConcreteNoisyCStarCalibration asymTriGraph asymTriHalfSig where
  reveal := twoThirdsNatRevealProbability
  reveal_pos := twoThirdsNatRevealProbability_pos
  reveal_le_one := twoThirdsNatRevealProbability_le_one
  capacity_eq_cv := by
    rw [twoThirdsNatRevealProbability_capacity_value, asymTriGraph_cv_asymTriHalfSig]
    norm_num

/-- The asymmetric-triangle inhabitant's equality field is the derived capacity computation. -/
theorem concreteAsymTriHalfNoisyCStarCalibration_capacity_eq_true :
    ChannelCapacity.channelCapacity concreteAsymTriHalfNoisyCStarCalibration.channel.kernel =
      (asymTriGraph.cv asymTriHalfSig : ℝ) :=
  concreteNoisyChannel_channelCapacity_eq_cv concreteAsymTriHalfNoisyCStarCalibration

/-- Concrete inhabitant closing the near-path graph/channel calibration. -/
noncomputable def concreteNearPathHalfNoisyCStarCalibration :
    ConcreteNoisyCStarCalibration nearPathGraph nearPathHalfSig where
  reveal := halfNatRevealProbability
  reveal_pos := halfNatRevealProbability_pos
  reveal_le_one := halfNatRevealProbability_le_one
  capacity_eq_cv := by
    rw [halfNatRevealProbability_capacity_value, nearPathGraph_cv_nearPathHalfSig]
    norm_num

/-- The near-path inhabitant's equality field is the derived capacity computation. -/
theorem concreteNearPathHalfNoisyCStarCalibration_capacity_eq_true :
    ChannelCapacity.channelCapacity concreteNearPathHalfNoisyCStarCalibration.channel.kernel =
      (nearPathGraph.cv nearPathHalfSig : ℝ) :=
  concreteNoisyChannel_channelCapacity_eq_cv concreteNearPathHalfNoisyCStarCalibration

/-- Concrete inhabitant closing the bottleneck graph/channel calibration. -/
noncomputable def concreteBottleneckHalfNoisyCStarCalibration :
    ConcreteNoisyCStarCalibration bottleneckGraph bottleneckHalfSig where
  reveal := halfNatRevealProbability
  reveal_pos := halfNatRevealProbability_pos
  reveal_le_one := halfNatRevealProbability_le_one
  capacity_eq_cv := by
    rw [halfNatRevealProbability_capacity_value, bottleneckGraph_cv_bottleneckHalfSig]
    norm_num

/-- The bottleneck inhabitant's equality field is the derived capacity computation. -/
theorem concreteBottleneckHalfNoisyCStarCalibration_capacity_eq_true :
    ChannelCapacity.channelCapacity concreteBottleneckHalfNoisyCStarCalibration.channel.kernel =
      (bottleneckGraph.cv bottleneckHalfSig : ℝ) :=
  concreteNoisyChannel_channelCapacity_eq_cv concreteBottleneckHalfNoisyCStarCalibration

/-- Concrete inhabitant closing the uniform `K₅` graph/channel calibration. -/
noncomputable def concreteUniK5HalfNoisyCStarCalibration :
    ConcreteNoisyCStarCalibration uniK5 uniK5HalfSig where
  reveal := threeEighthsNatRevealProbability
  reveal_pos := threeEighthsNatRevealProbability_pos
  reveal_le_one := threeEighthsNatRevealProbability_le_one
  capacity_eq_cv := by
    rw [threeEighthsNatRevealProbability_capacity_value, uniK5_cv_uniK5HalfSig]
    norm_num

/-- The uniform-`K₅` inhabitant's equality field is the derived capacity computation. -/
theorem concreteUniK5HalfNoisyCStarCalibration_capacity_eq_true :
    ChannelCapacity.channelCapacity concreteUniK5HalfNoisyCStarCalibration.channel.kernel =
      (uniK5.cv uniK5HalfSig : ℝ) :=
  concreteNoisyChannel_channelCapacity_eq_cv concreteUniK5HalfNoisyCStarCalibration

/-- Exact `C_star` threshold identity for a calibrated concrete noisy channel. -/
theorem concreteNoisyChannel_finite_capacity_implies_C_star_threshold
    {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
    (δ : ℚ) (cal : ConcreteNoisyCStarCalibration G s)
    (hcv : 0 < G.cv s) :
    0 < ChannelCapacity.channelCapacity cal.channel.kernel ∧
      (C_star G s δ : ℝ) =
        (δ : ℝ) / ChannelCapacity.channelCapacity cal.channel.kernel := by
  have hcap_eq_cv :
      ChannelCapacity.channelCapacity cal.channel.kernel = (G.cv s : ℝ) :=
    concreteNoisyChannel_channelCapacity_eq_cv cal
  have hcvR : (0 : ℝ) < (G.cv s : ℝ) := by
    exact_mod_cast hcv
  refine ⟨by simpa [hcap_eq_cv] using hcvR, ?_⟩
  have hcv_eq_cap :
      (G.cv s : ℝ) =
        ChannelCapacity.channelCapacity cal.channel.kernel := hcap_eq_cv.symm
  simp [C_star, hcv_eq_cap]

end GovernanceChannel

end Legitimacy
