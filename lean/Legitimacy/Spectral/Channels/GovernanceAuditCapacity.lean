/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Channels.NoisyThresholdClosedForm
import Legitimacy.Results.GovernanceAdmissibilityAudit
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Governance audit capacity

This file keeps finite Shannon capacity load-bearing for audit-reporting
channels while refusing the circular Round 1 bridge from capacity achievement to
governance legitimacy.

The channel object and the real governance-admissibility verdict live on
different substrates:

* `CapacityAchievingPrior K.channel p` depends only on the stochastic kernel
  and prior.
* `governanceAdmissibilityVerdict subject = AuditVerdict.legitimate` depends
  only on the extracted audit graph and evaluator.

There is currently no formal map from channel reports into the audit graph's
claim corpus, nonvacuity witness, or check evidence.  The derived result in
this file is therefore the honest one: an independent verdict-based legitimacy
predicate is defined, and concrete witnesses show that capacity achievement and
that predicate are orthogonal in this substrate.  Reportability is proved from
kernel structure, with a non-atomic counterexample showing that it is not a
free consequence of capacity achievement.
-/

set_option autoImplicit false

namespace Legitimacy

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace GovernanceChannel

variable {n : Nat}

/-- Governance-side claim data audited by a finite channel.  The signal and
tolerance locate the audit in the spectral graph, but they do not define the
channel's Shannon capacity or the extracted-graph admissibility verdict. -/
structure AuditClaimSet (n : Nat) where
  signal : Fin n -> ℚ
  tolerance : ℚ

/-- A governance audit-reporting channel.  Its input prior is the audit
allocation object; capacity is computed from `channel.kernel` alone. -/
structure GovernanceAuditChannel
    (G : GovGraph ℚ n) [NeZero n] (claims : AuditClaimSet n)
    (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  channel : GovernanceChannel α β

namespace GovernanceAuditChannel

variable {G : GovGraph ℚ n} [NeZero n] {claims : AuditClaimSet n}
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The imported Shannon capacity of the audit kernel.  This is a projection
from the kernel, not from graph `cv` and not from an audit verdict. -/
noncomputable def capacity (K : GovernanceAuditChannel G claims α β)
    [IsMarkovKernel K.channel.kernel] : ℝ :=
  ChannelCapacity.channelCapacity K.channel.kernel

@[simp]
theorem capacity_eq_channelCapacity
    (K : GovernanceAuditChannel G claims α β)
    [IsMarkovKernel K.channel.kernel] :
    K.capacity = ChannelCapacity.channelCapacity K.channel.kernel :=
  rfl

end GovernanceAuditChannel

variable {G : GovGraph ℚ n} [NeZero n] {claims : AuditClaimSet n}
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Every positive-allocation audit input can produce an atomic report with
positive probability.  This is a property of the kernel/output observation
surface, not a property of Shannon capacity. -/
def AuditPriorReportable
    (K : GovernanceAuditChannel G claims α β) (p : ProbabilityMeasure α) : Prop :=
  ∀ x : α, 0 < (p.toMeasure {x}).toReal ->
    ∃ y : β, 0 < (K.channel.kernel x {y}).toReal

/-- Independent extracted-graph admissibility, using the real governance audit
verdict.  It contains no capacity-achievement field. -/
def AuditSubjectAdmissible (subject : AuditSubject) : Prop :=
  governanceAdmissibilityVerdict subject = AuditVerdict.legitimate

/-- Independent audit-allocation legitimacy: the real extracted-graph verdict
must be legitimate, and the chosen channel prior must be reportable.  Capacity
achievement is deliberately absent. -/
structure IndependentAuditAllocationLegitimate
    (subject : AuditSubject)
    (K : GovernanceAuditChannel G claims α β) (p : ProbabilityMeasure α) :
    Prop where
  admissible : AuditSubjectAdmissible subject
  reportable : AuditPriorReportable K p

theorem independent_audit_allocation_fails_of_not_admissible
    {subject : AuditSubject}
    (K : GovernanceAuditChannel G claims α β) (p : ProbabilityMeasure α)
    (hsubject :
      governanceAdmissibilityVerdict subject ≠ AuditVerdict.legitimate) :
    ¬ IndependentAuditAllocationLegitimate subject K p := by
  intro hlegit
  exact hsubject hlegit.admissible

/-! ## Reportability is a kernel fact, not a capacity field -/

/-- Finite atomic output alphabets make every Markov-kernel row reportable.
The proof uses only the row probability mass; it does not use capacity
achievement. -/
theorem auditPriorReportable_of_finite_output
    [Fintype β] [MeasurableSingletonClass β] [Nonempty β]
    (K : GovernanceAuditChannel G claims α β) (p : ProbabilityMeasure α) :
    AuditPriorReportable K p := by
  intro x _hx
  by_contra hnone
  push Not at hnone
  have hzero : ∀ y : β, ((K.channel.kernel x {y}).toReal) = 0 := by
    intro y
    exact le_antisymm (hnone y) ENNReal.toReal_nonneg
  have hsum :=
    ChannelCapacity.sum_toReal_singletonMass
      (ChannelCapacity.Kernel.rowProbabilityMeasure K.channel.kernel x)
  have hsum_zero : ∑ y : β, ((K.channel.kernel x {y}).toReal) = 0 := by
    simp [hzero]
  have : (1 : ℝ) = 0 := by
    simpa [ChannelCapacity.Kernel.rowProbabilityMeasure, hsum_zero] using hsum.symm
  norm_num at this

/-- Compatibility form for old call sites: when the output alphabet is finite,
capacity-achieving priors are reportable because every prior is reportable. -/
theorem reportable_of_capacity_for_finite_output
    [Fintype β] [MeasurableSingletonClass β] [Nonempty β]
    (K : GovernanceAuditChannel G claims α β) (p : ProbabilityMeasure α)
    (_hp : CapacityAchievingPrior K.channel p) :
    AuditPriorReportable K p :=
  auditPriorReportable_of_finite_output K p

/-- A non-atomic output row with positive input mass is not reportable: no
singleton report has positive probability. -/
theorem auditPriorReportable_fails_of_nonAtomic_positive_input
    (K : GovernanceAuditChannel G claims α β) (p : ProbabilityMeasure α)
    {x : α} (hx : 0 < (p.toMeasure {x}).toReal)
    [NoAtoms (K.channel.kernel x)] :
    ¬ AuditPriorReportable K p := by
  intro hreport
  obtain ⟨y, hy⟩ := hreport x hx
  have hzero : K.channel.kernel x {y} = 0 := measure_singleton y
  simp [hzero] at hy

/-! ## Structural orthogonality -/

/-- If a channel has a capacity-achieving prior, it can be paired with any
non-legitimate audit subject.  This proves that capacity achievement alone
cannot force the real governance-admissibility verdict in the present product
substrate. -/
theorem capacity_achieving_not_force_independent_legitimacy
    (subject : AuditSubject)
    (K : GovernanceAuditChannel G claims α β)
    (hexists : ∃ p : ProbabilityMeasure α, CapacityAchievingPrior K.channel p)
    (hsubject :
      governanceAdmissibilityVerdict subject ≠ AuditVerdict.legitimate) :
    ∃ p : ProbabilityMeasure α,
      CapacityAchievingPrior K.channel p ∧
        ¬ IndependentAuditAllocationLegitimate subject K p := by
  obtain ⟨p, hp⟩ := hexists
  exact ⟨p, hp, independent_audit_allocation_fails_of_not_admissible K p hsubject⟩

/-- Conversely, a real legitimate audit subject and reportable prior do not
force that prior to be capacity-achieving.  Capacity optimality is a separate
kernel optimization property. -/
theorem independent_legitimacy_not_force_capacity_achievement
    (subject : AuditSubject)
    (K : GovernanceAuditChannel G claims α β) (p : ProbabilityMeasure α)
    (hadmissible : AuditSubjectAdmissible subject)
    (hreportable : AuditPriorReportable K p)
    (hnotcap : ¬ CapacityAchievingPrior K.channel p) :
    IndependentAuditAllocationLegitimate subject K p ∧
      ¬ CapacityAchievingPrior K.channel p :=
  ⟨⟨hadmissible, hreportable⟩, hnotcap⟩

/-! ## Concrete capacity channel -/

/-- Concrete claim set for the uniform triangle audit witness. -/
def concreteQuarterAuditClaims : AuditClaimSet 3 where
  signal := sig
  tolerance := 1 / 10

/-- Noise value for the concrete BSC audit witness. -/
noncomputable def quarterAuditNoise : NNReal := 1 / 4

lemma quarterAuditNoise_pos : 0 < quarterAuditNoise := by
  norm_num [quarterAuditNoise]

lemma quarterAuditNoise_lt_half : quarterAuditNoise < 1 / 2 := by
  norm_num [quarterAuditNoise]

/-- Concrete governance audit channel: a BSC at noise `1/4`, not calibrated to
graph `cv` or to an extracted-graph verdict. -/
noncomputable def concreteQuarterNoisyAuditChannel :
    GovernanceAuditChannel uniTriGraph concreteQuarterAuditClaims
      BinaryDecision BinaryDecision where
  channel := asNoisyThresholdChannel quarterAuditNoise quarterAuditNoise_lt_half

lemma concreteQuarterNoisyAuditChannel_fullRank :
    ChannelCapacity.Kernel.RowMatrixFullRank
      concreteQuarterNoisyAuditChannel.channel.kernel := by
  exact asNoisyThresholdChannel_rowMatrixFullRank
    quarterAuditNoise_pos quarterAuditNoise_lt_half

theorem concreteQuarterNoisyAuditChannel_reportable
    (p : ProbabilityMeasure BinaryDecision) :
    AuditPriorReportable concreteQuarterNoisyAuditChannel p :=
  auditPriorReportable_of_finite_output concreteQuarterNoisyAuditChannel p

/-- Closed-form capacity computation for the concrete witness, from the channel
kernel alone. -/
theorem concreteQuarterNoisyAuditChannel_capacity_eq_log_two_sub_binEntropy :
    ChannelCapacity.channelCapacity
        concreteQuarterNoisyAuditChannel.channel.kernel =
      Real.log 2 - Real.binEntropy (quarterAuditNoise : ℝ) := by
  exact channelCapacity_asNoisyThresholdChannel_eq_log_two_sub_binEntropy
    quarterAuditNoise quarterAuditNoise_lt_half

/-- Independent capacity bound for the concrete witness.  This proof uses the
BSC closed-form theorem and analytic bounds on `log 2`; it does not mention an
extracted audit graph or graph `cv`. -/
theorem concreteQuarterNoisyAuditChannel_capacity_lt_one :
    ChannelCapacity.channelCapacity
        concreteQuarterNoisyAuditChannel.channel.kernel < 1 := by
  rw [concreteQuarterNoisyAuditChannel_capacity_eq_log_two_sub_binEntropy]
  have hbin_nonneg : 0 ≤ Real.binEntropy (quarterAuditNoise : ℝ) := by
    exact Real.binEntropy_nonneg (by norm_num [quarterAuditNoise])
      (by norm_num [quarterAuditNoise])
  have hlog_lt_one : Real.log 2 < (1 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  linarith

/-- The concrete BSC has a capacity-achieving prior by the finite strict
concavity theorem. -/
theorem concreteQuarterNoisyAuditChannel_exists_capacity_achieving_prior :
    ∃ p : ProbabilityMeasure BinaryDecision,
      CapacityAchievingPrior concreteQuarterNoisyAuditChannel.channel p := by
  obtain ⟨p, hp, _huniq⟩ :=
    ChannelCapacity.exists_unique_capacity_achieving_prior_of_finite
      concreteQuarterNoisyAuditChannel.channel.kernel
      concreteQuarterNoisyAuditChannel_fullRank
  exact ⟨p, hp⟩

/-! ## Discriminating witnesses -/

/-- Capacity achievement does not force the real audit verdict: the same
capacity channel can be paired with the cyclic skipped-check fixture, whose
verdict is undischarged rather than legitimate. -/
theorem concrete_capacity_achieving_prior_not_independent_legitimate_for_cyclic_skipped_graph :
    ∃ p : ProbabilityMeasure BinaryDecision,
      CapacityAchievingPrior concreteQuarterNoisyAuditChannel.channel p ∧
        ¬ IndependentAuditAllocationLegitimate cyclicSkippedAuditGraph
          concreteQuarterNoisyAuditChannel p := by
  exact capacity_achieving_not_force_independent_legitimacy
    cyclicSkippedAuditGraph
    concreteQuarterNoisyAuditChannel
    concreteQuarterNoisyAuditChannel_exists_capacity_achieving_prior
    cyclicSkippedAuditGraph_not_legitimate

noncomputable def permitPointAuditPrior : ProbabilityMeasure BinaryDecision :=
  ⟨Measure.dirac BinaryDecision.Permit, by infer_instance⟩

noncomputable def denyPointAuditPrior : ProbabilityMeasure BinaryDecision :=
  ⟨Measure.dirac BinaryDecision.Deny, by infer_instance⟩

lemma permitPointAuditPrior_ne_denyPointAuditPrior :
    permitPointAuditPrior ≠ denyPointAuditPrior := by
  intro h
  have hmass := congrArg (fun p : ProbabilityMeasure BinaryDecision =>
    (p.toMeasure {BinaryDecision.Permit}).toReal) h
  change ((Measure.dirac BinaryDecision.Permit) {BinaryDecision.Permit}).toReal =
    ((Measure.dirac BinaryDecision.Deny) {BinaryDecision.Permit}).toReal at hmass
  simp at hmass

lemma not_both_point_priors_capacity_achieving :
    ¬ (CapacityAchievingPrior concreteQuarterNoisyAuditChannel.channel
          permitPointAuditPrior ∧
        CapacityAchievingPrior concreteQuarterNoisyAuditChannel.channel
          denyPointAuditPrior) := by
  intro hboth
  obtain ⟨_p, _hp, huniq⟩ :=
    ChannelCapacity.exists_unique_capacity_achieving_prior_of_finite
      concreteQuarterNoisyAuditChannel.channel.kernel
      concreteQuarterNoisyAuditChannel_fullRank
  have heq : permitPointAuditPrior = denyPointAuditPrior :=
    (huniq permitPointAuditPrior hboth.1).trans
      (huniq denyPointAuditPrior hboth.2).symm
  exact permitPointAuditPrior_ne_denyPointAuditPrior heq

/-- The real compiler-audit subject is legitimate, but at least one point-mass
prior for the same BSC channel is not capacity-achieving.  Thus independent
legitimacy does not force capacity achievement. -/
theorem concrete_independent_legitimate_prior_not_capacity_achieving :
    ∃ p : ProbabilityMeasure BinaryDecision,
      IndependentAuditAllocationLegitimate compilerAuditGraph
          concreteQuarterNoisyAuditChannel p ∧
        ¬ CapacityAchievingPrior concreteQuarterNoisyAuditChannel.channel p := by
  by_cases hpermit :
      CapacityAchievingPrior concreteQuarterNoisyAuditChannel.channel
        permitPointAuditPrior
  · refine ⟨denyPointAuditPrior, ?_, ?_⟩
    · exact ⟨compiler_audit_is_self_legitimate,
        concreteQuarterNoisyAuditChannel_reportable denyPointAuditPrior⟩
    · intro hdeny
      exact not_both_point_priors_capacity_achieving ⟨hpermit, hdeny⟩
  · refine ⟨permitPointAuditPrior, ?_, hpermit⟩
    exact ⟨compiler_audit_is_self_legitimate,
      concreteQuarterNoisyAuditChannel_reportable permitPointAuditPrior⟩

/-- No universal theorem can send capacity achievement to independent
legitimacy in this substrate. -/
theorem no_universal_capacity_to_independent_legitimacy_bridge :
    ¬ (∀ subject : AuditSubject, ∀ p : ProbabilityMeasure BinaryDecision,
      CapacityAchievingPrior concreteQuarterNoisyAuditChannel.channel p ->
        IndependentAuditAllocationLegitimate subject
          concreteQuarterNoisyAuditChannel p) := by
  intro hbridge
  obtain ⟨p, hp, hnot⟩ :=
    concrete_capacity_achieving_prior_not_independent_legitimate_for_cyclic_skipped_graph
  exact hnot (hbridge cyclicSkippedAuditGraph p hp)

/-- No universal theorem can send independent legitimacy to capacity
achievement either. -/
theorem no_universal_independent_legitimacy_to_capacity_bridge :
    ¬ (∀ subject : AuditSubject, ∀ p : ProbabilityMeasure BinaryDecision,
      IndependentAuditAllocationLegitimate subject
          concreteQuarterNoisyAuditChannel p ->
        CapacityAchievingPrior concreteQuarterNoisyAuditChannel.channel p) := by
  intro hbridge
  obtain ⟨p, hlegit, hnotcap⟩ :=
    concrete_independent_legitimate_prior_not_capacity_achieving
  exact hnotcap (hbridge compilerAuditGraph p hlegit)

/-! ## Non-atomic reportability counterexample -/

lemma probabilityMeasure_unit_ext (p q : ProbabilityMeasure Unit) : p = q := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro s _hs
  by_cases hmem : () ∈ s
  · have hs_univ : s = Set.univ := by
      ext x
      cases x
      simp [hmem]
    simp [hs_univ]
  · have hs_empty : s = ∅ := by
      ext x
      cases x
      simp [hmem]
    simp [hs_empty]

/-- A capacity-achieving channel with non-atomic reports.  Since every row is
Lebesgue measure on the unit interval, no singleton report has positive mass. -/
noncomputable def nonAtomicUnitIntervalAuditChannel :
    GovernanceAuditChannel uniTriGraph concreteQuarterAuditClaims Unit I where
  channel :=
    { kernel := Kernel.const Unit (volume : Measure I)
      isMarkov := by infer_instance }

noncomputable def unitAuditPrior : ProbabilityMeasure Unit :=
  ⟨Measure.dirac (), by infer_instance⟩

lemma unitAuditPrior_singleton_pos :
    0 < (unitAuditPrior.toMeasure {()}).toReal := by
  change 0 < ((Measure.dirac ()) {()}).toReal
  rw [Measure.dirac_apply_of_mem]
  · norm_num
  · simp

theorem unitAuditPrior_capacityAchieving_nonAtomicUnitInterval :
    CapacityAchievingPrior nonAtomicUnitIntervalAuditChannel.channel unitAuditPrior := by
  unfold CapacityAchievingPrior ChannelCapacity.channelCapacity
  have hrange :
      Set.range (fun p : ProbabilityMeasure Unit =>
        ChannelCapacity.mutualInformation p
          nonAtomicUnitIntervalAuditChannel.channel.kernel) =
        {ChannelCapacity.mutualInformation unitAuditPrior
          nonAtomicUnitIntervalAuditChannel.channel.kernel} := by
    ext r
    constructor
    · rintro ⟨p, rfl⟩
      have hp : p = unitAuditPrior := probabilityMeasure_unit_ext p unitAuditPrior
      simp [hp]
    · intro hr
      refine ⟨unitAuditPrior, ?_⟩
      simpa using hr.symm
  rw [hrange, csSup_singleton]

theorem nonAtomicUnitIntervalAuditChannel_not_reportable :
    ¬ AuditPriorReportable nonAtomicUnitIntervalAuditChannel unitAuditPrior := by
  haveI : NoAtoms (nonAtomicUnitIntervalAuditChannel.channel.kernel ()) := by
    change NoAtoms (volume : Measure I)
    infer_instance
  exact auditPriorReportable_fails_of_nonAtomic_positive_input
    nonAtomicUnitIntervalAuditChannel unitAuditPrior unitAuditPrior_singleton_pos

/-- Counterexample to any unrestricted `reportable_of_capacity`: capacity
achievement does not imply atomic reportability for non-atomic output kernels. -/
theorem capacity_achieving_not_reportable_nonAtomicUnitInterval :
    CapacityAchievingPrior nonAtomicUnitIntervalAuditChannel.channel unitAuditPrior ∧
      ¬ AuditPriorReportable nonAtomicUnitIntervalAuditChannel unitAuditPrior :=
  ⟨unitAuditPrior_capacityAchieving_nonAtomicUnitInterval,
    nonAtomicUnitIntervalAuditChannel_not_reportable⟩

end GovernanceChannel

end Legitimacy
