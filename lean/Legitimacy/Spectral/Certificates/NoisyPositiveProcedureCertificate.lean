/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Certificates.PositiveProcedureCertificate
import Legitimacy.Spectral.Channels.NoisyThresholdClosedForm

/-!
# Noisy positive-procedure certificates

This module is the noisy/probabilistic companion to the exact finite-channel
positive procedure.  The exact extractor uses pointwise threshold decisions; the
noisy extractor keeps a profile-indexed verdict distribution and makes
solidarity the quantitative downward-persistence certificate for verdict drift.

The module deliberately stays in the spectral substrate.  Exact consistency
uses the profile-uniform semantic reflection in
`PositiveProcedureCertificate`; noisy all-profile diagnostics require their
own probabilistic analogue.
-/

set_option autoImplicit false

namespace Legitimacy

open MeasureTheory ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Finite α] [Finite β]
variable {n : Nat} [NeZero n]

/-- Binary verdict distribution over `Permit`/`Deny`, represented rationally so
the spectral layer can state quantitative drift bounds without importing a
measure-theoretic stochastic-process substrate. -/
structure VerdictDistribution where
  permit : ℚ
  deny : ℚ
  permit_nonneg : 0 ≤ permit
  deny_nonneg : 0 ≤ deny
  total_mass : permit + deny = 1

namespace VerdictDistribution

/-- Probability mass assigned to a binary decision. -/
def prob (v : VerdictDistribution) : BinaryDecision → ℚ
  | BinaryDecision.Permit => v.permit
  | BinaryDecision.Deny => v.deny

/-- Binary total variation distance.  For two-outcome distributions this is
the absolute difference of the `Permit` masses. -/
def totalVariation (p q : VerdictDistribution) : ℚ :=
  |p.permit - q.permit|

@[simp] private lemma totalVariation_self (p : VerdictDistribution) :
    totalVariation p p = 0 := by
  simp [totalVariation]

end VerdictDistribution

/-- Kernel-level data for the noisy positive procedure.

The finite channel remains the Shannon-capacity carrier.  The additional
`profileVerdict` field is the operational noisy surface: at each scale and
profile/input, the kernel exposes a probabilistic binary verdict. -/
structure NoisyKernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [Finite β] (n : Nat) [NeZero n] where
  G : GovGraph ℚ n
  s : Fin n → ℚ
  δ : ℚ
  channel : GovernanceChannel α β
  profileVerdict : ℚ → α → VerdictDistribution

/-- The spectral threshold read from a noisy kernel. -/
noncomputable def NoisyKernel.C_star (K : NoisyKernel α β n) : ℚ :=
  Legitimacy.C_star K.G K.s K.δ

/-- The noisy profile surface is constant-policy when all profile/input rows
give the same verdict distribution at every scale. -/
def NoisyKernel.ConstantPolicy (K : NoisyKernel α β n) : Prop :=
  ∀ c : ℚ, ∀ x y : α, K.profileVerdict c x = K.profileVerdict c y

/-- Profile sensitivity is the non-vacuity floor for noisy kernels: at some
scale, two profiles/inputs produce different verdict distributions. -/
def NoisyKernel.ProfileSensitive (K : NoisyKernel α β n) : Prop :=
  ∃ (c : ℚ) (x y : α), K.profileVerdict c x ≠ K.profileVerdict c y

/-- The probabilistic-verdict floor: some row has nonzero mass on both binary
verdicts.  This rules out merely wrapping an exact deterministic kernel in an
extra proposition. -/
def NoisyKernel.HasGenuineNoise (K : NoisyKernel α β n) : Prop :=
  ∃ (c : ℚ) (x : α),
    0 < (K.profileVerdict c x).permit ∧
      0 < (K.profileVerdict c x).deny

/-- A noisy finite-channel capacity certificate.

It is not the exact `CStarExactCapacityCertificate`: the finite capacity still
calibrates `C*`, but the certificate also requires genuine probabilistic verdict
mass and profile sensitivity. -/
structure NoisyCapacityCertificate (K : NoisyKernel α β n) where
  capacity_pos : 0 < ChannelCapacity.channelCapacity K.channel.kernel
  capacity_threshold :
    (K.C_star : ℝ) =
      (K.δ : ℝ) / ChannelCapacity.channelCapacity K.channel.kernel
  genuine_noise : K.HasGenuineNoise
  profile_sensitive : K.ProfileSensitive

/-- Quantitative downward persistence for noisy solidarity.

For every lower positive scale, the binary total-variation drift of each
profile-indexed verdict distribution is bounded linearly by the scale drop.
This is the content that the exact finite-channel substrate did not need. -/
structure QuantitativeDownwardPersistence
    (K : NoisyKernel α β n) (c : ℚ) where
  rate : ℚ
  rate_pos : 0 < rate
  drift_bound :
    ∀ C : ℚ, ∀ x : α, 0 < C → C ≤ c →
      VerdictDistribution.totalVariation
        (K.profileVerdict C x) (K.profileVerdict c x) ≤ rate * (c - C)

/-- Well-conditioned noisy kernels for the positive procedure.

The predicate supplies the spectral threshold ingredients, the noisy capacity
certificate, and the quantitative persistence law used by noisy solidarity. It
does not bridge into all-profile graph diagnostics. -/
structure NoisyWellConditionedForCapacity (K : NoisyKernel α β n) where
  tolerance_pos : 0 < K.δ
  cv_pos : 0 < K.G.cv K.s
  noisy_capacity : NoisyCapacityCertificate K
  downward_persistence :
    ∀ c : ℚ, 0 < c → c < K.C_star →
      QuantitativeDownwardPersistence K c

/-- Constant-policy noisy kernels fail the noisy well-conditioned floor. -/
theorem constantPolicy_not_noisyWellConditioned
    (K : NoisyKernel α β n) (hconst : K.ConstantPolicy) :
    NoisyWellConditionedForCapacity K → False := by
  intro hK
  rcases hK.noisy_capacity.profile_sensitive with ⟨c, x, y, hxy⟩
  exact hxy (hconst c x y)

/-- Consistency data available at one noisy scale.  It records the exact
spectral side at that scale only; it intentionally carries no lower-scale
probabilistic drift law. -/
structure NoisyConsistencyData (K : NoisyKernel α β n) (c : ℚ) : Prop where
  capacity_pos : 0 < c
  below_threshold : c < K.C_star
  verdict :
    K.G.capabilityResponse K.s K.δ c = BinaryDecision.Deny
  no_violation : ¬ K.G.spViolation K.s (K.δ / c)

/-- Boundary monotonicity data for a noisy kernel. -/
structure NoisyMonotonicityData (K : NoisyKernel α β n) (c : ℚ) : Prop where
  at_threshold : c = K.C_star
  verdict :
    K.G.capabilityResponse K.s K.δ c = BinaryDecision.Permit
  upper_scales_permit :
    ∀ C : ℚ, K.C_star ≤ C →
      K.G.capabilityResponse K.s K.δ C = BinaryDecision.Permit

/-- Noisy positive-procedure certificate.  The solidarity branch carries the
quantitative total-variation persistence law that is independent of the
single-scale consistency fields. -/
inductive NoisyPositiveProcedureCertificate
    (K : NoisyKernel α β n) (c : ℚ) where
  | consistency
      (data : NoisyConsistencyData K c)
      (capacity_threshold :
        (K.C_star : ℝ) =
          (K.δ : ℝ) / ChannelCapacity.channelCapacity K.channel.kernel)
  | solidarity
      (data : NoisyConsistencyData K c)
      (persistence : QuantitativeDownwardPersistence K c)
      (capacity_threshold :
        (K.C_star : ℝ) =
          (K.δ : ℝ) / ChannelCapacity.channelCapacity K.channel.kernel)
  | monotonicity
      (data : NoisyMonotonicityData K c)
      (capacity_threshold :
        (K.C_star : ℝ) =
          (K.δ : ℝ) / ChannelCapacity.channelCapacity K.channel.kernel)

namespace NoisyPositiveProcedureCertificate

/-- The diagnostic selected by a noisy positive-procedure certificate. -/
def kind {K : NoisyKernel α β n} {c : ℚ} :
    NoisyPositiveProcedureCertificate K c → PreservedDiagnostic
  | consistency .. => PreservedDiagnostic.consistency
  | solidarity .. => PreservedDiagnostic.solidarity
  | monotonicity .. => PreservedDiagnostic.monotonicity

end NoisyPositiveProcedureCertificate

/-- Extract a noisy positive-procedure certificate.  Strictly below `C*`, the
noisy extractor selects solidarity because the additional total-variation rate
is the operational persistence datum; at the boundary it selects monotonicity. -/
noncomputable def governance_certificate_noisy
    (K : NoisyKernel α β n) (hK : NoisyWellConditionedForCapacity K)
    (c : ℚ) (hcpos : 0 < c) (hc : c ≤ K.C_star) :
    NoisyPositiveProcedureCertificate K c := by
  classical
  have hthreshold := K.G.capabilityResponse_threshold K.s K.δ
    hK.tolerance_pos hK.cv_pos
  by_cases hlt : c < K.C_star
  · have hdeny :
        K.G.capabilityResponse K.s K.δ c = BinaryDecision.Deny := by
      exact hthreshold.1 c hcpos (by simpa [NoisyKernel.C_star] using hlt)
    have hno :
        ¬ K.G.spViolation K.s (K.δ / c) := by
      exact (C_star_exists K.G K.s K.δ hK.tolerance_pos hK.cv_pos).1
        c hcpos (by simpa [NoisyKernel.C_star] using hlt)
    exact NoisyPositiveProcedureCertificate.solidarity
      ⟨hcpos, hlt, hdeny, hno⟩
      (hK.downward_persistence c hcpos hlt)
      hK.noisy_capacity.capacity_threshold
  · have hle_boundary : K.C_star ≤ c := le_of_not_gt hlt
    have heq : c = K.C_star := le_antisymm hc hle_boundary
    have hpermit :
        K.G.capabilityResponse K.s K.δ c = BinaryDecision.Permit := by
      rw [heq]
      exact hthreshold.2 (K.C_star) (by simp [NoisyKernel.C_star])
    have hupper :
        ∀ C : ℚ, K.C_star ≤ C →
          K.G.capabilityResponse K.s K.δ C = BinaryDecision.Permit := by
      intro C hC
      exact hthreshold.2 C (by simpa [NoisyKernel.C_star] using hC)
    exact NoisyPositiveProcedureCertificate.monotonicity
      ⟨heq, hpermit, hupper⟩
      hK.noisy_capacity.capacity_threshold

/-- Noisy positive-procedure theorem. -/
theorem governance_certificate_constructible_noisy
    (K : NoisyKernel α β n)
    (hK : NoisyWellConditionedForCapacity K)
    (c : ℚ) (hcpos : 0 < c) (hc : c ≤ K.C_star) :
    ∃ cert : NoisyPositiveProcedureCertificate K c,
      cert.kind = PreservedDiagnostic.consistency ∨
        cert.kind = PreservedDiagnostic.solidarity ∨
          cert.kind = PreservedDiagnostic.monotonicity := by
  classical
  refine ⟨governance_certificate_noisy K hK c hcpos hc, ?_⟩
  unfold governance_certificate_noisy
  by_cases hlt : c < K.C_star
  · simp [hlt, NoisyPositiveProcedureCertificate.kind]
  · simp [hlt, NoisyPositiveProcedureCertificate.kind]

namespace NoisyPositiveProcedureExamples

/-- Rational binary verdict distribution constructor. -/
def rationalVerdictDistribution (p : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    VerdictDistribution where
  permit := p
  deny := 1 - p
  permit_nonneg := hp0
  deny_nonneg := by linarith
  total_mass := by ring

/-- Low-permit noisy row used below the jump scale. -/
def quarterPermitVerdict : VerdictDistribution :=
  rationalVerdictDistribution (1 / 4) (by norm_num) (by norm_num)

/-- A second low-permit row, making the worked counterexample profile-sensitive. -/
def thirdPermitVerdict : VerdictDistribution :=
  rationalVerdictDistribution (1 / 3) (by norm_num) (by norm_num)

/-- High-permit noisy row used at and above the jump scale. -/
def threeQuarterPermitVerdict : VerdictDistribution :=
  rationalVerdictDistribution (3 / 4) (by norm_num) (by norm_num)

/-- A second high-permit row, keeping profile sensitivity after the jump. -/
def twoThirdsPermitVerdict : VerdictDistribution :=
  rationalVerdictDistribution (2 / 3) (by norm_num) (by norm_num)

/-- A profile-sensitive noisy verdict surface with a discontinuity at `1 / 10`.
The discontinuity is used only to refute derivability of quantitative
persistence from consistency data alone. -/
def jumpProfileVerdict (C : ℚ) : BinaryDecision → VerdictDistribution
  | BinaryDecision.Permit =>
      if C < 1 / 10 then quarterPermitVerdict else threeQuarterPermitVerdict
  | BinaryDecision.Deny =>
      if C < 1 / 10 then thirdPermitVerdict else twoThirdsPermitVerdict

/-- Concrete noisy kernel used to separate consistency data from solidarity
data.  The channel is the existing concrete erasure calibration; the noisy
verdict surface is the profile-indexed probabilistic layer above. -/
noncomputable def jumpNoisyKernel :
    NoisyKernel BinaryDecision (Option BinaryDecision) 3 where
  G := uniTriGraph
  s := halfSig
  δ := 1 / 10
  channel := GovernanceChannel.concreteHalfNoisyCStarCalibration.channel
  profileVerdict := jumpProfileVerdict

private lemma jumpNoisyKernel_C_star :
    jumpNoisyKernel.C_star = 1 / 5 := by
  simp [jumpNoisyKernel, NoisyKernel.C_star, Legitimacy.C_star,
    GovernanceChannel.uniTriGraph_cv_halfSig]
  norm_num

theorem jumpNoisyKernel_profileSensitive :
    jumpNoisyKernel.ProfileSensitive := by
  refine ⟨0, BinaryDecision.Permit, BinaryDecision.Deny, ?_⟩
  intro h
  have hpermit := congrArg VerdictDistribution.permit h
  norm_num [jumpNoisyKernel, jumpProfileVerdict, quarterPermitVerdict,
    thirdPermitVerdict, rationalVerdictDistribution] at hpermit

theorem jumpNoisyKernel_hasGenuineNoise :
    jumpNoisyKernel.HasGenuineNoise := by
  refine ⟨0, BinaryDecision.Permit, ?_⟩
  norm_num [jumpNoisyKernel, jumpProfileVerdict, quarterPermitVerdict,
    rationalVerdictDistribution]

theorem jumpNoisyKernel_consistencyData_oneTenth :
    NoisyConsistencyData jumpNoisyKernel (1 / 10) := by
  have hlt : (1 / 10 : ℚ) < jumpNoisyKernel.C_star := by
    rw [jumpNoisyKernel_C_star]
    norm_num
  have hthreshold := uniTriGraph.capabilityResponse_threshold halfSig
    (1 / 10) (by norm_num) GovernanceChannel.uniTriGraph_cv_halfSig_pos
  refine ⟨by norm_num, hlt, ?_, ?_⟩
  · exact hthreshold.1 (1 / 10) (by norm_num) (by
      simpa [jumpNoisyKernel, NoisyKernel.C_star] using hlt)
  · exact (C_star_exists uniTriGraph halfSig (1 / 10)
      (by norm_num) GovernanceChannel.uniTriGraph_cv_halfSig_pos).1
        (1 / 10) (by norm_num) (by
          simpa [jumpNoisyKernel, NoisyKernel.C_star] using hlt)

theorem jumpNoisyKernel_noQuantitativePersistence_oneTenth :
    QuantitativeDownwardPersistence jumpNoisyKernel (1 / 10) → False := by
  intro hp
  let ε : ℚ := 1 / (20 * (hp.rate + 1))
  let C : ℚ := 1 / 10 - ε
  have hrate_nonneg : 0 ≤ hp.rate := le_of_lt hp.rate_pos
  have hden_pos : 0 < 20 * (hp.rate + 1) := by nlinarith
  have hden_gt_ten : (10 : ℚ) < 20 * (hp.rate + 1) := by nlinarith
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact one_div_pos.mpr hden_pos
  have hε_lt : ε < 1 / 10 := by
    dsimp [ε]
    rw [div_lt_iff₀ hden_pos]
    nlinarith
  have hCpos : 0 < C := by
    dsimp [C]
    linarith
  have hCle : C ≤ 1 / 10 := by
    dsimp [C]
    linarith
  have hClt : C < 1 / 10 := by
    dsimp [C]
    linarith
  have hbound := hp.drift_bound C BinaryDecision.Permit hCpos hCle
  have htv :
      VerdictDistribution.totalVariation
        (jumpNoisyKernel.profileVerdict C BinaryDecision.Permit)
        (jumpNoisyKernel.profileVerdict (1 / 10) BinaryDecision.Permit) =
        1 / 2 := by
    have hnot : ¬ (1 / 10 : ℚ) < 1 / 10 := by norm_num
    change
      VerdictDistribution.totalVariation
        (jumpProfileVerdict C BinaryDecision.Permit)
        (jumpProfileVerdict (1 / 10) BinaryDecision.Permit) = 1 / 2
    unfold jumpProfileVerdict
    rw [if_pos hClt, if_neg hnot]
    norm_num [VerdictDistribution.totalVariation, quarterPermitVerdict,
      threeQuarterPermitVerdict, rationalVerdictDistribution]
  have hsmall : hp.rate * (1 / 10 - C) < 1 / 2 := by
    have hdiff : 1 / 10 - C = ε := by
      dsimp [C]
      ring
    rw [hdiff]
    dsimp [ε]
    have hden_ne : 20 * (hp.rate + 1) ≠ 0 := ne_of_gt hden_pos
    field_simp [hden_ne]
    nlinarith [hp.rate_pos]
  rw [htv] at hbound
  exact (not_le_of_gt hsmall) hbound

/-- Single-scale noisy consistency data does not derive the solidarity
constructor's quantitative downward-persistence content. -/
theorem noisy_solidarity_not_derivable_from_consistency_data :
    (∀ (K : NoisyKernel BinaryDecision (Option BinaryDecision) 3) (c : ℚ),
      NoisyConsistencyData K c → QuantitativeDownwardPersistence K c) → False := by
  intro hderive
  exact jumpNoisyKernel_noQuantitativePersistence_oneTenth
    (hderive jumpNoisyKernel (1 / 10) jumpNoisyKernel_consistencyData_oneTenth)

/-! ### Worked BSC noisy kernel -/

/-- Scale mass used by the concrete BSC worked instance.  It is active on the
subcritical interval used by the certificate and zero outside that interval. -/
def boundedScaleMass (C : ℚ) : ℚ :=
  if 0 ≤ C ∧ C ≤ 1 / 5 then C else 0

private lemma boundedScaleMass_eq_of_mem {C : ℚ} (hC0 : 0 ≤ C) (hC1 : C ≤ 1 / 5) :
    boundedScaleMass C = C := by
  unfold boundedScaleMass
  rw [if_pos ⟨hC0, hC1⟩]

private lemma boundedScaleMass_nonneg (C : ℚ) : 0 ≤ boundedScaleMass C := by
  by_cases h : 0 ≤ C ∧ C ≤ 1 / 5
  · unfold boundedScaleMass
    rw [if_pos h]
    exact h.1
  · unfold boundedScaleMass
    rw [if_neg h]

private lemma boundedScaleMass_le_one_fifth (C : ℚ) : boundedScaleMass C ≤ 1 / 5 := by
  by_cases h : 0 ≤ C ∧ C ≤ 1 / 5
  · unfold boundedScaleMass
    rw [if_pos h]
    exact h.2
  · unfold boundedScaleMass
    rw [if_neg h]
    norm_num

def linearPermitMass (C : ℚ) : BinaryDecision → ℚ
  | BinaryDecision.Permit => 1 / 4 + boundedScaleMass C
  | BinaryDecision.Deny => 1 / 3 + boundedScaleMass C

private lemma linearPermitMass_nonneg (C : ℚ) (x : BinaryDecision) :
    0 ≤ linearPermitMass C x := by
  cases x <;> dsimp [linearPermitMass] <;>
    nlinarith [boundedScaleMass_nonneg C]

private lemma linearPermitMass_le_one (C : ℚ) (x : BinaryDecision) :
    linearPermitMass C x ≤ 1 := by
  cases x <;> dsimp [linearPermitMass] <;>
    nlinarith [boundedScaleMass_le_one_fifth C]

/-- Profile-sensitive noisy verdict surface with actual linear scale drift on
the subcritical interval. -/
def linearProfileVerdict (C : ℚ) (x : BinaryDecision) : VerdictDistribution :=
  rationalVerdictDistribution (linearPermitMass C x)
    (linearPermitMass_nonneg C x) (linearPermitMass_le_one C x)

/-- Concrete BSC noisy kernel for the half-scale uniform triangle. -/
noncomputable def concreteHalfBSCNoisyKernel :
    NoisyKernel BinaryDecision BinaryDecision 3 where
  G := uniTriGraph
  s := halfSig
  δ := 1 / 10
  channel := GovernanceChannel.concreteHalfBSCNoisyCStarCalibration.channel
  profileVerdict := linearProfileVerdict

private lemma concreteHalfBSCNoisyKernel_C_star :
    concreteHalfBSCNoisyKernel.C_star = 1 / 5 := by
  simp [concreteHalfBSCNoisyKernel, NoisyKernel.C_star, Legitimacy.C_star,
    GovernanceChannel.uniTriGraph_cv_halfSig]
  norm_num

theorem concreteHalfBSCNoisyKernel_profileSensitive :
    concreteHalfBSCNoisyKernel.ProfileSensitive := by
  refine ⟨0, BinaryDecision.Permit, BinaryDecision.Deny, ?_⟩
  intro h
  have hpermit := congrArg VerdictDistribution.permit h
  norm_num [concreteHalfBSCNoisyKernel, linearProfileVerdict,
    linearPermitMass, boundedScaleMass, rationalVerdictDistribution] at hpermit

theorem concreteHalfBSCNoisyKernel_hasGenuineNoise :
    concreteHalfBSCNoisyKernel.HasGenuineNoise := by
  refine ⟨0, BinaryDecision.Permit, ?_⟩
  norm_num [concreteHalfBSCNoisyKernel, linearProfileVerdict,
    linearPermitMass, boundedScaleMass, rationalVerdictDistribution]

theorem concreteHalfBSCNoisyKernel_capacityCertificate :
    NoisyCapacityCertificate concreteHalfBSCNoisyKernel := by
  have hcap_eq :=
    GovernanceChannel.concreteHalfBSCNoisyCStarCalibration_capacity_eq_true
  refine ⟨?_, ?_, concreteHalfBSCNoisyKernel_hasGenuineNoise,
    concreteHalfBSCNoisyKernel_profileSensitive⟩
  · simpa [concreteHalfBSCNoisyKernel, hcap_eq] using
      (show (0 : ℝ) < (uniTriGraph.cv halfSig : ℝ) by
        exact_mod_cast GovernanceChannel.uniTriGraph_cv_halfSig_pos)
  · simp [concreteHalfBSCNoisyKernel, NoisyKernel.C_star, Legitimacy.C_star,
      hcap_eq, GovernanceChannel.uniTriGraph_cv_halfSig]

def concreteHalfBSCNoisyKernel_downwardPersistence
    (c : ℚ) (hcpos : 0 < c) (hlt : c < concreteHalfBSCNoisyKernel.C_star) :
    QuantitativeDownwardPersistence concreteHalfBSCNoisyKernel c := by
  refine ⟨1, by norm_num, ?_⟩
  intro C x hCpos hCle
  have hCstar : concreteHalfBSCNoisyKernel.C_star = 1 / 5 :=
    concreteHalfBSCNoisyKernel_C_star
  have hc_le : c ≤ 1 / 5 := by
    rw [← hCstar]
    exact le_of_lt hlt
  have hC_le : C ≤ 1 / 5 := le_trans hCle hc_le
  have hCmass : boundedScaleMass C = C :=
    boundedScaleMass_eq_of_mem hCpos.le hC_le
  have hcmass : boundedScaleMass c = c :=
    boundedScaleMass_eq_of_mem hcpos.le hc_le
  have habs : |C - c| = c - C := by
    rw [abs_of_nonpos (sub_nonpos.mpr hCle)]
    ring
  cases x <;>
    simp [concreteHalfBSCNoisyKernel, linearProfileVerdict,
      linearPermitMass, rationalVerdictDistribution,
      VerdictDistribution.totalVariation, hCmass, hcmass, habs]

noncomputable def concreteHalfBSCNoisyKernel_wellConditioned :
    NoisyWellConditionedForCapacity concreteHalfBSCNoisyKernel := by
  refine ⟨?_, ?_, concreteHalfBSCNoisyKernel_capacityCertificate, ?_⟩
  · norm_num [concreteHalfBSCNoisyKernel]
  · simpa [concreteHalfBSCNoisyKernel] using
      GovernanceChannel.uniTriGraph_cv_halfSig_pos
  · intro c hcpos hlt
    exact concreteHalfBSCNoisyKernel_downwardPersistence c hcpos hlt

/-- Actual probabilistic verdict drift in the worked BSC kernel. -/
theorem concreteHalfBSCNoisyKernel_verdictDrift_oneTwentieth_to_oneTenth :
    VerdictDistribution.totalVariation
      (concreteHalfBSCNoisyKernel.profileVerdict (1 / 20) BinaryDecision.Permit)
      (concreteHalfBSCNoisyKernel.profileVerdict (1 / 10) BinaryDecision.Permit) =
        1 / 20 := by
  norm_num [concreteHalfBSCNoisyKernel, linearProfileVerdict,
    linearPermitMass, rationalVerdictDistribution,
    VerdictDistribution.totalVariation, boundedScaleMass]

/-- Worked noisy certificate at `c = 1 / 10`; the strict subcritical noisy
extractor selects solidarity. -/
noncomputable def concreteHalfBSCNoisyCertificateAtOneTenth :
    NoisyPositiveProcedureCertificate concreteHalfBSCNoisyKernel (1 / 10) :=
  governance_certificate_noisy
    concreteHalfBSCNoisyKernel
    concreteHalfBSCNoisyKernel_wellConditioned
    (1 / 10)
    (by norm_num)
    (by
      rw [concreteHalfBSCNoisyKernel_C_star]
      norm_num)

theorem concreteHalfBSCNoisyCertificateAtOneTenth_kind :
    concreteHalfBSCNoisyCertificateAtOneTenth.kind =
      PreservedDiagnostic.solidarity := by
  unfold concreteHalfBSCNoisyCertificateAtOneTenth governance_certificate_noisy
  have hlt : (1 / 10 : ℚ) < concreteHalfBSCNoisyKernel.C_star := by
    rw [concreteHalfBSCNoisyKernel_C_star]
    norm_num
  rw [dif_pos hlt]
  simp [NoisyPositiveProcedureCertificate.kind]

end NoisyPositiveProcedureExamples

end Legitimacy
