/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Channels.NoisyGovernanceChannel

/-!
# Noisy governance capacity

This module records finite capacity-attainment facts available for the binary
noisy-threshold governance channel. It deliberately does not claim the
still-open structural `C*` rate theorem: the result here is the exact
finite-channel statement supplied by the imported capacity library.
-/

set_option autoImplicit false

namespace Legitimacy

open MeasureTheory ProbabilityTheory

namespace GovernanceChannel

/-- A prior achieves the finite channel capacity of a governance channel in the
imported `ChannelCapacity` sense. -/
noncomputable def CapacityAchievingPrior
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (c : GovernanceChannel α β) (p : ProbabilityMeasure α) : Prop :=
  ChannelCapacity.mutualInformation p c.kernel =
    ChannelCapacity.channelCapacity c.kernel

/-- Low-noise binary threshold channels satisfy the full finite-channel
capacity certificate: row separation, full row-rank, and a unique
capacity-achieving prior. -/
theorem low_noise_noisyThreshold_capacity_certificate
    (η : NNReal) (hη : 0 < η) (hη' : η < 1 / 2) :
    (asNoisyThresholdChannel η hη').RowSeparating ∧
    ChannelCapacity.Kernel.RowSeparating
      (asNoisyThresholdChannel η hη').kernel ∧
    ChannelCapacity.Kernel.RowMatrixFullRank
      (asNoisyThresholdChannel η hη').kernel ∧
    ∃! p : ProbabilityMeasure BinaryDecision,
      CapacityAchievingPrior (asNoisyThresholdChannel η hη') p := by
  exact ⟨asNoisyThresholdChannel_rowSeparating hη hη',
    asNoisyThresholdChannel_kernel_rowSeparating hη hη',
    asNoisyThresholdChannel_rowMatrixFullRank hη hη',
    governance_channel_capacity_unique_achieving_prior_noisy η hη hη'⟩

/-- Capacity-attainer existence and uniqueness for the low-noise binary
governance channel: some prior achieves capacity, and any two
capacity-achieving priors are equal. -/
theorem noisyThreshold_capacity_attainer_exists_and_unique
    (η : NNReal) (hη : 0 < η) (hη' : η < 1 / 2) :
    (∃ p : ProbabilityMeasure BinaryDecision,
      CapacityAchievingPrior (asNoisyThresholdChannel η hη') p) ∧
    (∀ p q : ProbabilityMeasure BinaryDecision,
      CapacityAchievingPrior (asNoisyThresholdChannel η hη') p →
      CapacityAchievingPrior (asNoisyThresholdChannel η hη') q →
      p = q) := by
  obtain ⟨p₀, hp₀, hunique⟩ :=
    governance_channel_capacity_unique_achieving_prior_noisy η hη hη'
  constructor
  · exact ⟨p₀, hp₀⟩
  · intro p q hp hq
    exact (hunique p hp).trans (hunique q hq).symm

/-- Uniqueness form: below half-noise, capacity-achieving priors for the binary
noisy governance channel are unique. -/
theorem noisyThreshold_capacity_attainer_unique
    (η : NNReal) (hη : 0 < η) (hη' : η < 1 / 2)
    (p q : ProbabilityMeasure BinaryDecision)
    (hp : CapacityAchievingPrior (asNoisyThresholdChannel η hη') p)
    (hq : CapacityAchievingPrior (asNoisyThresholdChannel η hη') q) :
    p = q :=
  (noisyThreshold_capacity_attainer_exists_and_unique η hη hη').2 p q hp hq

end GovernanceChannel

end Legitimacy
