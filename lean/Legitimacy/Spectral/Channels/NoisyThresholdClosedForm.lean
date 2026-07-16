/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Channels.ConcreteNoisyChannel
import Legitimacy.Spectral.Channels.BinaryDecisionHelpers
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Topology.Order.IntermediateValue

/-!
# Closed form capacity for the binary symmetric noisy-threshold channel

This module computes the finite Shannon capacity of
`asNoisyThresholdChannel`. The result is stated in nats, matching
`ChannelCapacity.channelCapacity`:

`C(BSC η) = log 2 - Real.binEntropy η`.
-/

set_option autoImplicit false

namespace Legitimacy

open MeasureTheory ProbabilityTheory

namespace GovernanceChannel

private lemma keepMass_toReal
    (η : NNReal) (hη : η ≤ (1 : NNReal)) :
    (keepMass η : ℝ) = 1 - (η : ℝ) := by
  rw [keepMass, NNReal.coe_sub hη]
  simp

private lemma ennreal_one_sub_eta_toReal
    (η : NNReal) (hη : η ≤ (1 : NNReal)) :
    ((1 : ENNReal) - (η : ENNReal)).toReal = 1 - (η : ℝ) := by
  rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hη) ENNReal.one_ne_top]
  simp

/-- Uniform prior on binary decisions, used by the BSC capacity proof. -/
noncomputable def uniformNoisyThresholdPrior : ProbabilityMeasure BinaryDecision :=
  ⟨((PMF.bernoulli (1 / 2 : NNReal) (by norm_num)).map
      (fun b => if b then BinaryDecision.Permit else BinaryDecision.Deny)).toMeasure,
    by infer_instance⟩

private lemma uniformNoisyThresholdPrior_apply_permit :
    (uniformNoisyThresholdPrior.toMeasure {BinaryDecision.Permit}).toReal = (1 / 2 : ℝ) := by
  simp [uniformNoisyThresholdPrior]

private lemma uniformNoisyThresholdPrior_apply_deny :
    (uniformNoisyThresholdPrior.toMeasure {BinaryDecision.Deny}).toReal = (1 / 2 : ℝ) := by
  simp [uniformNoisyThresholdPrior]

private lemma uniformNoisyThresholdPrior_entropy :
    ChannelCapacity.ProbabilityMeasure.entropy uniformNoisyThresholdPrior = Real.log 2 := by
  simp [ChannelCapacity.ProbabilityMeasure.entropy, sum_binaryDecision,
    uniformNoisyThresholdPrior_apply_permit, uniformNoisyThresholdPrior_apply_deny]
  rw [Real.negMulLog]
  rw [Real.log_inv]
  ring

private lemma noisyThreshold_kernel_toReal_self
    (η : NNReal) (hη : η < (1 / 2 : NNReal)) (d : BinaryDecision) :
    (((asNoisyThresholdChannel η hη).kernel d {d}).toReal) = 1 - (η : ℝ) := by
  have hkeep := ennreal_one_sub_eta_toReal η (le_one_of_lt_half hη)
  cases d <;> simpa [asNoisyThresholdChannel, noisyThresholdRow, keepMass] using hkeep

private lemma noisyThreshold_kernel_toReal_flip
    (η : NNReal) (hη : η < (1 / 2 : NNReal)) (d : BinaryDecision) :
    (((asNoisyThresholdChannel η hη).kernel d {flipDecision d}).toReal) = (η : ℝ) := by
  have hkeep := ennreal_one_sub_eta_toReal η (le_one_of_lt_half hη)
  have hflip : 1 - ((1 : ENNReal) - (η : ENNReal)).toReal = (η : ℝ) := by
    rw [hkeep]
    ring
  cases d <;> simpa [asNoisyThresholdChannel, noisyThresholdRow, keepMass, flipDecision] using hflip

private lemma noisyThreshold_rowEntropy
    (η : NNReal) (hη : η < (1 / 2 : NNReal)) (d : BinaryDecision) :
    ChannelCapacity.Kernel.rowEntropy (asNoisyThresholdChannel η hη).kernel d =
      Real.binEntropy (η : ℝ) := by
  have hkeep := ennreal_one_sub_eta_toReal η (le_one_of_lt_half hη)
  unfold ChannelCapacity.Kernel.rowEntropy ChannelCapacity.ProbabilityMeasure.entropy
  rw [sum_binaryDecision]
  cases d
  · simp [ChannelCapacity.Kernel.rowProbabilityMeasure, asNoisyThresholdChannel,
      noisyThresholdRow, keepMass, flipDecision, hkeep,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, add_comm]
  · simp [ChannelCapacity.Kernel.rowProbabilityMeasure, asNoisyThresholdChannel,
      noisyThresholdRow, keepMass, flipDecision, hkeep,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, add_comm]

private lemma noisyThreshold_conditionalEntropy
    (η : NNReal) (hη : η < (1 / 2 : NNReal))
    (p : ProbabilityMeasure BinaryDecision) :
    ChannelCapacity.conditionalEntropy p (asNoisyThresholdChannel η hη).kernel =
      Real.binEntropy (η : ℝ) := by
  unfold ChannelCapacity.conditionalEntropy
  simp_rw [noisyThreshold_rowEntropy]
  rw [← Finset.sum_mul]
  rw [ChannelCapacity.sum_toReal_singletonMass]
  ring

private lemma noisyThreshold_uniform_outputPrior_apply_permit
    (η : NNReal) (hη : η < (1 / 2 : NNReal)) :
    (((ChannelCapacity.outputPrior (asNoisyThresholdChannel η hη).kernel
        uniformNoisyThresholdPrior).toMeasure {BinaryDecision.Permit}).toReal) =
      (1 / 2 : ℝ) := by
  rw [ChannelCapacity.toReal_outputPrior_apply_singleton]
  rw [sum_binaryDecision]
  rw [uniformNoisyThresholdPrior_apply_permit, uniformNoisyThresholdPrior_apply_deny]
  have hself :=
    noisyThreshold_kernel_toReal_self η hη BinaryDecision.Permit
  have hflip :=
    noisyThreshold_kernel_toReal_flip η hη BinaryDecision.Deny
  simp [flipDecision] at hflip
  rw [hself, hflip]
  ring

private lemma noisyThreshold_uniform_outputPrior_apply_deny
    (η : NNReal) (hη : η < (1 / 2 : NNReal)) :
    (((ChannelCapacity.outputPrior (asNoisyThresholdChannel η hη).kernel
        uniformNoisyThresholdPrior).toMeasure {BinaryDecision.Deny}).toReal) =
      (1 / 2 : ℝ) := by
  rw [ChannelCapacity.toReal_outputPrior_apply_singleton]
  rw [sum_binaryDecision]
  rw [uniformNoisyThresholdPrior_apply_permit, uniformNoisyThresholdPrior_apply_deny]
  have hflip :=
    noisyThreshold_kernel_toReal_flip η hη BinaryDecision.Permit
  have hself :=
    noisyThreshold_kernel_toReal_self η hη BinaryDecision.Deny
  simp [flipDecision] at hflip
  rw [hflip, hself]
  ring

private lemma noisyThreshold_uniform_outputEntropy
    (η : NNReal) (hη : η < (1 / 2 : NNReal)) :
    ChannelCapacity.ProbabilityMeasure.entropy
        (ChannelCapacity.outputPrior (asNoisyThresholdChannel η hη).kernel
          uniformNoisyThresholdPrior) =
      Real.log 2 := by
  unfold ChannelCapacity.ProbabilityMeasure.entropy
  rw [sum_binaryDecision]
  rw [noisyThreshold_uniform_outputPrior_apply_permit,
    noisyThreshold_uniform_outputPrior_apply_deny]
  simp
  rw [Real.negMulLog]
  rw [Real.log_inv]
  ring

private lemma noisyThreshold_mutualInformation_eq_outputEntropy_sub_binEntropy
    (η : NNReal) (hη : η < (1 / 2 : NNReal))
    (p : ProbabilityMeasure BinaryDecision) :
    ChannelCapacity.mutualInformation p (asNoisyThresholdChannel η hη).kernel =
      ChannelCapacity.ProbabilityMeasure.entropy
          (ChannelCapacity.outputPrior (asNoisyThresholdChannel η hη).kernel p) -
        Real.binEntropy (η : ℝ) := by
  rw [ChannelCapacity.mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy]
  rw [noisyThreshold_conditionalEntropy]

private lemma noisyThreshold_uniform_mutualInformation
    (η : NNReal) (hη : η < (1 / 2 : NNReal)) :
    ChannelCapacity.mutualInformation uniformNoisyThresholdPrior
        (asNoisyThresholdChannel η hη).kernel =
      Real.log 2 - Real.binEntropy (η : ℝ) := by
  rw [noisyThreshold_mutualInformation_eq_outputEntropy_sub_binEntropy]
  rw [noisyThreshold_uniform_outputEntropy]

/-- The binary symmetric noisy-threshold channel has capacity
`log 2 - H₂(η)` nats. -/
theorem channelCapacity_asNoisyThresholdChannel_eq_log_two_sub_binEntropy
    (η : NNReal) (hη : η < (1 / 2 : NNReal)) :
    ChannelCapacity.channelCapacity (asNoisyThresholdChannel η hη).kernel =
      Real.log 2 - Real.binEntropy (η : ℝ) := by
  have hmax : IsMaxOn
      (fun q : ProbabilityMeasure BinaryDecision =>
        ChannelCapacity.mutualInformation q (asNoisyThresholdChannel η hη).kernel)
      Set.univ uniformNoisyThresholdPrior := by
    rw [isMaxOn_univ_iff]
    intro q
    rw [noisyThreshold_mutualInformation_eq_outputEntropy_sub_binEntropy,
      noisyThreshold_uniform_mutualInformation]
    exact sub_le_sub_right
      (binaryDecision_entropy_le_log_two
        (ChannelCapacity.outputPrior (asNoisyThresholdChannel η hη).kernel q))
      (Real.binEntropy (η : ℝ))
  calc
    ChannelCapacity.channelCapacity (asNoisyThresholdChannel η hη).kernel =
        ChannelCapacity.mutualInformation uniformNoisyThresholdPrior
          (asNoisyThresholdChannel η hη).kernel :=
      ChannelCapacity.channelCapacity_eq_of_isMaxOn_univ _ hmax
    _ = Real.log 2 - Real.binEntropy (η : ℝ) := by
      rw [noisyThreshold_uniform_mutualInformation]

/-- Bits-normalized form of the BSC capacity closed form. -/
theorem channelCapacity_asNoisyThresholdChannel_bits
    (η : NNReal) (hη : η < (1 / 2 : NNReal)) :
    ChannelCapacity.channelCapacity (asNoisyThresholdChannel η hη).kernel / Real.log 2 =
      1 - Real.binEntropy (η : ℝ) / Real.log 2 := by
  rw [channelCapacity_asNoisyThresholdChannel_eq_log_two_sub_binEntropy]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

/-! ### BSC graph calibration -/

variable {n : Nat}

/-- A graph/signal calibration for the binary symmetric noisy-threshold channel. -/
structure ConcreteBSCNoisyCStarCalibration
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) where
  noise : NNReal
  noise_lt_half : noise < 1 / 2
  capacity_eq_cv :
    Real.log 2 - Real.binEntropy (noise : ℝ) = (G.cv s : ℝ)

/-- The concrete BSC channel for a graph/signal pair. -/
noncomputable def ConcreteBSCNoisyCStarCalibration.channel
    {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
    (cal : ConcreteBSCNoisyCStarCalibration G s) :
    GovernanceChannel BinaryDecision BinaryDecision :=
  asNoisyThresholdChannel cal.noise cal.noise_lt_half

/-- The concrete BSC channel capacity equality derived from the closed-form theorem. -/
theorem concreteBSCNoisyChannel_channelCapacity_eq_cv
    {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
    (cal : ConcreteBSCNoisyCStarCalibration G s) :
    ChannelCapacity.channelCapacity cal.channel.kernel = (G.cv s : ℝ) := by
  calc
    ChannelCapacity.channelCapacity cal.channel.kernel =
        Real.log 2 - Real.binEntropy (cal.noise : ℝ) := by
      exact channelCapacity_asNoisyThresholdChannel_eq_log_two_sub_binEntropy
        cal.noise cal.noise_lt_half
    _ = (G.cv s : ℝ) := cal.capacity_eq_cv

/-- Any graph/signal pair with `cv` in the BSC reachable range is inhabited by
a binary symmetric noisy-threshold calibration. -/
theorem existsConcreteBSCNoisyCStarCalibration_of_cv_pos_lt_log_two
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ)
    (hcv_pos : 0 < G.cv s) (hcv_lt : (G.cv s : ℝ) < Real.log 2) :
    ∃ _cal : ConcreteBSCNoisyCStarCalibration G s, True := by
  let c : ℝ := (G.cv s : ℝ)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact_mod_cast hcv_pos
  have hcont : ContinuousOn (fun x : ℝ => Real.log 2 - Real.binEntropy x)
      (Set.Icc 0 (1 / 2)) := by
    fun_prop
  have hc_mem :
      c ∈ Set.Icc
        ((fun x : ℝ => Real.log 2 - Real.binEntropy x) (1 / 2))
        ((fun x : ℝ => Real.log 2 - Real.binEntropy x) 0) := by
    have hleft :
        ((fun x : ℝ => Real.log 2 - Real.binEntropy x) (1 / 2)) = 0 := by
      simp
    have hright :
        ((fun x : ℝ => Real.log 2 - Real.binEntropy x) 0) = Real.log 2 := by
      simp
    rw [hleft, hright]
    exact ⟨hc_pos.le, by dsimp [c]; exact hcv_lt.le⟩
  obtain ⟨η, hη_mem, hη_eq⟩ :=
    intermediate_value_Icc' (show (0 : ℝ) ≤ 1 / 2 by norm_num) hcont hc_mem
  have hη_lt : η < 1 / 2 := by
    refine lt_of_le_of_ne hη_mem.2 ?_
    intro hη_eq_half
    have hzero : c = 0 := by
      rw [← hη_eq]
      simp [hη_eq_half]
    exact ne_of_gt hc_pos hzero
  let noise : NNReal := ⟨η, hη_mem.1⟩
  have noise_lt_half : noise < (1 / 2 : NNReal) := by
    exact_mod_cast hη_lt
  refine ⟨⟨noise, noise_lt_half, ?_⟩, trivial⟩
  simpa [noise, c] using hη_eq

private lemma uniTriGraph_cv_halfSig_lt_log_two :
    (uniTriGraph.cv halfSig : ℝ) < Real.log 2 := by
  rw [uniTriGraph_cv_halfSig]
  norm_num
  exact lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9

/-- Concrete BSC inhabitant for the half-scale uniform triangle calibration. -/
noncomputable def concreteHalfBSCNoisyCStarCalibration :
    ConcreteBSCNoisyCStarCalibration uniTriGraph halfSig :=
  Classical.choose
    (existsConcreteBSCNoisyCStarCalibration_of_cv_pos_lt_log_two
      uniTriGraph halfSig uniTriGraph_cv_halfSig_pos uniTriGraph_cv_halfSig_lt_log_two)

/-- The concrete BSC inhabitant's equality field is the derived capacity computation. -/
theorem concreteHalfBSCNoisyCStarCalibration_capacity_eq_true :
    ChannelCapacity.channelCapacity concreteHalfBSCNoisyCStarCalibration.channel.kernel =
      (uniTriGraph.cv halfSig : ℝ) :=
  concreteBSCNoisyChannel_channelCapacity_eq_cv concreteHalfBSCNoisyCStarCalibration

end GovernanceChannel

end Legitimacy
