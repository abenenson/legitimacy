/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.FiveNode
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.SevenNode
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.NineNode

/-!
# Finite Cross-Scale Spectral Universality Package

# Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.Universality

Certified rational threshold windows for five-, seven-, and nine-node witnesses.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Parameterized probe separator on a rational `S_delta` certificate. -/
def ProbeSpectralWellConnectedAt (sDelta theta : ℚ) : Prop :=
  theta ≤ sDelta

instance instDecidableProbeSpectralWellConnectedAt (sDelta theta : ℚ) :
    Decidable (ProbeSpectralWellConnectedAt sDelta theta) := by
  unfold ProbeSpectralWellConnectedAt
  infer_instance

/-- The original probe predicate is the `17 / 20` instance of the
parameterized probe separator. -/
theorem ProbeSpectralWellConnected_iff_at_default (sDelta : ℚ) :
    ProbeSpectralWellConnected sDelta ↔
      ProbeSpectralWellConnectedAt sDelta (17 / 20) := by
  rfl

/-- Proposition packaging the certified non-bottleneck side of the finite
five/seven/nine-node cross-scale family. -/
def NonbottleneckArchetypesCertifiedSpectralWellConnected : Prop :=
    ProbeSpectralWellConnected fiveNodeCompleteSDeltaCertificate ∧
    ProbeSpectralWellConnected fiveNodeAsymmetricSDeltaCertificate ∧
    ProbeSpectralWellConnected fiveNodeNearPathSDeltaCertificate ∧
    ProbeSpectralWellConnected fiveNodeWheelSDeltaCertificate ∧
    ProbeSpectralWellConnected sevenNodeCompleteSDeltaCertificate ∧
    ProbeSpectralWellConnected sevenNodeAsymmetricSDeltaCertificate ∧
    ProbeSpectralWellConnected sevenNodeNearPathSDeltaCertificate ∧
    ProbeSpectralWellConnected uniK9SDeltaCertificate ∧
    ProbeSpectralWellConnected asymK9SDeltaCertificate ∧
    ProbeSpectralWellConnected nearPath9SDeltaCertificate ∧
    ProbeSpectralWellConnected wheel9SDeltaCertificate

/-- Every certified non-bottleneck archetype in the finite five/seven/nine-node
cross-scale family clears the `17 / 20` separator. -/
theorem all_nonbottleneck_archetypes_certifiedSpectralWellConnected :
    NonbottleneckArchetypesCertifiedSpectralWellConnected := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  repeat' constructor <;> native_decide

/-- Parameterized certified non-bottleneck side of the finite five/seven/nine
cross-scale family. -/
def NonbottleneckArchetypesCertifiedSpectralWellConnectedAt (theta : ℚ) : Prop :=
    ProbeSpectralWellConnectedAt fiveNodeCompleteSDeltaCertificate theta ∧
    ProbeSpectralWellConnectedAt fiveNodeAsymmetricSDeltaCertificate theta ∧
    ProbeSpectralWellConnectedAt fiveNodeNearPathSDeltaCertificate theta ∧
    ProbeSpectralWellConnectedAt fiveNodeWheelSDeltaCertificate theta ∧
    ProbeSpectralWellConnectedAt sevenNodeCompleteSDeltaCertificate theta ∧
    ProbeSpectralWellConnectedAt sevenNodeAsymmetricSDeltaCertificate theta ∧
    ProbeSpectralWellConnectedAt sevenNodeNearPathSDeltaCertificate theta ∧
    ProbeSpectralWellConnectedAt uniK9SDeltaCertificate theta ∧
    ProbeSpectralWellConnectedAt asymK9SDeltaCertificate theta ∧
    ProbeSpectralWellConnectedAt nearPath9SDeltaCertificate theta ∧
    ProbeSpectralWellConnectedAt wheel9SDeltaCertificate theta

/-- Every certified non-bottleneck archetype clears every threshold up to the
smallest certified non-bottleneck `S_delta` value, `46 / 53`. -/
theorem all_nonbottleneck_archetypes_certifiedSpectralWellConnectedAt_of_le
    {theta : ℚ} (htheta : theta ≤ 46 / 53) :
    NonbottleneckArchetypesCertifiedSpectralWellConnectedAt theta := by
  unfold NonbottleneckArchetypesCertifiedSpectralWellConnectedAt
  unfold ProbeSpectralWellConnectedAt
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  exact ⟨le_trans htheta (by native_decide),
    le_trans htheta (by native_decide),
    le_trans htheta (by native_decide),
    le_trans htheta (by native_decide),
    le_trans htheta (by native_decide),
    le_trans htheta (by native_decide),
    le_trans htheta (by native_decide),
    le_trans htheta (by native_decide),
    le_trans htheta (by native_decide),
    le_trans htheta (by native_decide),
    le_trans htheta (by native_decide)⟩

/-- Proposition packaging the certified bottleneck side of the finite
five/seven/nine-node cross-scale family. -/
def BottleneckArchetypesNotCertifiedSpectralWellConnected : Prop :=
    ¬ ProbeSpectralWellConnected fiveNodeBottleneckSDeltaCertificate ∧
    ¬ ProbeSpectralWellConnected sevenNodeBicliqueBottleneckSDeltaCertificate ∧
    ¬ ProbeSpectralWellConnected sevenNodeTriclusterBottleneckSDeltaCertificate ∧
    ¬ ProbeSpectralWellConnected bottleneck9BiSDeltaCertificate

/-- Every certified bottleneck archetype in the finite five/seven/nine-node
cross-scale family fails the `17 / 20` separator. -/
theorem all_bottleneck_archetypes_not_certifiedSpectralWellConnected :
    BottleneckArchetypesNotCertifiedSpectralWellConnected := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  repeat' constructor <;> native_decide

/-- Parameterized certified bottleneck side of the finite five/seven/nine
cross-scale family. -/
def BottleneckArchetypesNotCertifiedSpectralWellConnectedAt (theta : ℚ) : Prop :=
    ¬ ProbeSpectralWellConnectedAt fiveNodeBottleneckSDeltaCertificate theta ∧
    ¬ ProbeSpectralWellConnectedAt sevenNodeBicliqueBottleneckSDeltaCertificate theta ∧
    ¬ ProbeSpectralWellConnectedAt sevenNodeTriclusterBottleneckSDeltaCertificate theta ∧
    ¬ ProbeSpectralWellConnectedAt bottleneck9BiSDeltaCertificate theta

/-- Every certified bottleneck archetype fails every threshold at least as
large as the original `17 / 20` separator. -/
theorem all_bottleneck_archetypes_not_certifiedSpectralWellConnectedAt_of_ge
    {theta : ℚ} (htheta : 17 / 20 ≤ theta) :
    BottleneckArchetypesNotCertifiedSpectralWellConnectedAt theta := by
  unfold BottleneckArchetypesNotCertifiedSpectralWellConnectedAt
  unfold ProbeSpectralWellConnectedAt
  exact ⟨by
      intro hpass
      -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
      exact (not_le_of_gt (lt_of_lt_of_le (by native_decide) htheta)) hpass,
    by
      intro hpass
      exact (not_le_of_gt (lt_of_lt_of_le (by native_decide) htheta)) hpass,
    by
      intro hpass
      exact (not_le_of_gt (lt_of_lt_of_le (by native_decide) htheta)) hpass,
    by
      intro hpass
      exact (not_le_of_gt (lt_of_lt_of_le (by native_decide) htheta)) hpass⟩

/-- The finite five/seven/nine certified archetype family has a rational
threshold window around `17 / 20`: all certified non-bottleneck witnesses pass
throughout the window, and all certified bottleneck witnesses fail throughout
the window. -/
theorem nonbottleneck_archetype_family_admissible_window :
    ∃ theta_min theta_max : ℚ,
      theta_min ≤ (17 / 20 : ℚ) ∧ (17 / 20 : ℚ) ≤ theta_max ∧
        (∀ theta ∈ Set.Icc theta_min theta_max,
          NonbottleneckArchetypesCertifiedSpectralWellConnectedAt theta) ∧
        (∀ theta ∈ Set.Icc theta_min theta_max,
          BottleneckArchetypesNotCertifiedSpectralWellConnectedAt theta) := by
  refine ⟨17 / 20, 46 / 53, by norm_num, by norm_num, ?_, ?_⟩
  · intro theta htheta
    exact all_nonbottleneck_archetypes_certifiedSpectralWellConnectedAt_of_le
      htheta.2
  · intro theta htheta
    exact all_bottleneck_archetypes_not_certifiedSpectralWellConnectedAt_of_ge
      htheta.1

/-- The discharged `uniK5` spectral gap makes the lower side of the window an
actual spectral-CV statement, not merely a probe certificate statement. -/
theorem uniK5_actualSpectralWellConnectedAt_of_le
    {theta : ℚ} (htheta : theta ≤ 46 / 53) :
    SpectralWellConnectedAt uniK5 sig5 theta (by norm_num : 2 ≤ 5) := by
  unfold SpectralWellConnectedAt
  constructor
  · unfold SpectralConnected
    rw [uniK5_spectralGap_eq_certificate]
    norm_num [fiveNodeCompleteSpectralGapCertificate]
  · unfold PositiveGovernanceVulnerabilityAt
    rw [uniK5_spectralGap_eq_certificate]
    have hthetaR : (theta : ℝ) ≤ ((46 / 53 : ℚ) : ℝ) := by
      exact_mod_cast htheta
    calc
      (theta : ℝ) ≤ ((46 / 53 : ℚ) : ℝ) := hthetaR
      _ ≤ (fiveNodeCompleteSpectralGapCertificate : ℝ) * (uniK5.cv sig5 : ℝ) := by
        have hcv : uniK5.cv sig5 = 3 / 4 := fiveNode_cv_values.1
        norm_num [fiveNodeCompleteSpectralGapCertificate, hcv]

/-- The discharged `uniK7` spectral gap makes the lower side of the window an
actual spectral-CV statement, not merely a probe certificate statement. -/
theorem uniK7_actualSpectralWellConnectedAt_of_le
    {theta : ℚ} (htheta : theta ≤ 46 / 53) :
    SpectralWellConnectedAt uniK7 sig7 theta (by norm_num : 2 ≤ 7) := by
  unfold SpectralWellConnectedAt
  constructor
  · unfold SpectralConnected
    rw [uniK7_spectralGap_eq_certificate]
    norm_num [sevenNodeCompleteSpectralGapCertificate]
  · unfold PositiveGovernanceVulnerabilityAt
    rw [uniK7_spectralGap_eq_certificate]
    have hthetaR : (theta : ℝ) ≤ ((46 / 53 : ℚ) : ℝ) := by
      exact_mod_cast htheta
    calc
      (theta : ℝ) ≤ ((46 / 53 : ℚ) : ℝ) := hthetaR
      _ ≤ (sevenNodeCompleteSpectralGapCertificate : ℝ) * (uniK7.cv sig7 : ℝ) := by
        have hcv : uniK7.cv sig7 = 2 / 3 := sevenNode_cv_values.1
        norm_num [sevenNodeCompleteSpectralGapCertificate, hcv]

/-- The discharged `uniK9` spectral gap makes the lower side of the window an
actual spectral-CV statement, not merely a probe certificate statement. -/
theorem uniK9_actualSpectralWellConnectedAt_of_le
    {theta : ℚ} (htheta : theta ≤ 46 / 53) :
    SpectralWellConnectedAt uniK9 sig9 theta (by norm_num : 2 ≤ 9) := by
  unfold SpectralWellConnectedAt
  constructor
  · unfold SpectralConnected
    rw [uniK9_spectralGap_eq_certificate]
    norm_num [uniK9SpectralGapCertificate]
  · unfold PositiveGovernanceVulnerabilityAt
    rw [uniK9_spectralGap_eq_certificate]
    have hthetaR : (theta : ℝ) ≤ ((46 / 53 : ℚ) : ℝ) := by
      exact_mod_cast htheta
    calc
      (theta : ℝ) ≤ ((46 / 53 : ℚ) : ℝ) := hthetaR
      _ ≤ (uniK9SpectralGapCertificate : ℝ) * (uniK9.cv sig9 : ℝ) := by
        have hcv : uniK9.cv sig9 = 5 / 8 := n9_cv_values.1
        norm_num [uniK9SpectralGapCertificate, hcv]

/-- The discharged `bottleneck5` spectral-gap upper bound makes the upper side
of the window an actual spectral-CV exclusion, not merely a probe certificate
exclusion. -/
theorem bottleneck5_not_actualSpectralWellConnectedAt_of_ge
    {theta : ℚ} (htheta : 17 / 20 ≤ theta) :
    ¬ SpectralWellConnectedAt bottleneck5 sig5 theta (by norm_num : 2 ≤ 5) := by
  intro hwell
  unfold SpectralWellConnectedAt at hwell
  have hcv : bottleneck5.cv sig5 = 20000 / 10001 := fiveNode_cv_values.2.2.2.2
  have hcv_nonneg : 0 ≤ (bottleneck5.cv sig5 : ℝ) :=
    bottleneck5.spectralWellConnected_cv_cast_nonneg sig5
  have hprod_le :
      bottleneck5.spectralGap (by norm_num : 2 ≤ 5) * (bottleneck5.cv sig5 : ℝ) ≤
        (fiveNodeBottleneckSpectralGapCertificate : ℝ) * (bottleneck5.cv sig5 : ℝ) :=
    mul_le_mul_of_nonneg_right bottleneck5_spectralGap_le_certificate hcv_nonneg
  have hcert_lt :
      (fiveNodeBottleneckSpectralGapCertificate : ℝ) * (bottleneck5.cv sig5 : ℝ) <
        (17 / 20 : ℝ) := by
    norm_num [fiveNodeBottleneckSpectralGapCertificate, hcv]
  have hthetaR : (((17 / 20 : ℚ) : ℝ) ≤ (theta : ℝ)) := by
    exact_mod_cast htheta
  have hthreshold : ((17 / 20 : ℚ) : ℝ) = (17 / 20 : ℝ) := by
    norm_num
  exact not_lt_of_ge hwell.2
    (lt_of_le_of_lt hprod_le (lt_of_lt_of_le hcert_lt (by simpa [hthreshold] using hthetaR)))

/-- The discharged `bottleneck7_bi` spectral-gap upper bound makes the upper
side of the window an actual spectral-CV exclusion, not merely a probe
certificate exclusion. -/
theorem bottleneck7_bi_not_actualSpectralWellConnectedAt_of_ge
    {theta : ℚ} (htheta : 17 / 20 ≤ theta) :
    ¬ SpectralWellConnectedAt bottleneck7_bi sig7 theta (by norm_num : 2 ≤ 7) := by
  intro hwell
  unfold SpectralWellConnectedAt at hwell
  have hcv : bottleneck7_bi.cv sig7 = 612578750 / 612552501 :=
    sevenNode_cv_values.2.2.2.1
  have hcv_nonneg : 0 ≤ (bottleneck7_bi.cv sig7 : ℝ) :=
    bottleneck7_bi.spectralWellConnected_cv_cast_nonneg sig7
  have hprod_le :
      bottleneck7_bi.spectralGap (by norm_num : 2 ≤ 7) *
          (bottleneck7_bi.cv sig7 : ℝ) ≤
        (sevenNodeBicliqueBottleneckSpectralGapCertificate : ℝ) *
          (bottleneck7_bi.cv sig7 : ℝ) :=
    mul_le_mul_of_nonneg_right bottleneck7_bi_spectralGap_le_certificate hcv_nonneg
  have hcert_lt :
      (sevenNodeBicliqueBottleneckSpectralGapCertificate : ℝ) *
          (bottleneck7_bi.cv sig7 : ℝ) <
        (17 / 20 : ℝ) := by
    norm_num [sevenNodeBicliqueBottleneckSpectralGapCertificate, hcv]
  have hthetaR : (((17 / 20 : ℚ) : ℝ) ≤ (theta : ℝ)) := by
    exact_mod_cast htheta
  have hthreshold : ((17 / 20 : ℚ) : ℝ) = (17 / 20 : ℝ) := by
    norm_num
  exact not_lt_of_ge hwell.2
    (lt_of_le_of_lt hprod_le (lt_of_lt_of_le hcert_lt (by simpa [hthreshold] using hthetaR)))

/-- The discharged `bottleneck7_tri` spectral-gap upper bound makes the upper
side of the window an actual spectral-CV exclusion, not merely a probe
certificate exclusion. -/
theorem bottleneck7_tri_not_actualSpectralWellConnectedAt_of_ge
    {theta : ℚ} (htheta : 17 / 20 ≤ theta) :
    ¬ SpectralWellConnectedAt bottleneck7_tri sig7 theta (by norm_num : 2 ≤ 7) := by
  intro hwell
  unfold SpectralWellConnectedAt at hwell
  have hcv : bottleneck7_tri.cv sig7 = 56000 / 14001 :=
    sevenNode_cv_values.2.2.2.2
  have hcv_nonneg : 0 ≤ (bottleneck7_tri.cv sig7 : ℝ) :=
    bottleneck7_tri.spectralWellConnected_cv_cast_nonneg sig7
  have hprod_le :
      bottleneck7_tri.spectralGap (by norm_num : 2 ≤ 7) *
          (bottleneck7_tri.cv sig7 : ℝ) ≤
        (sevenNodeTriclusterBottleneckSpectralGapCertificate : ℝ) *
          (bottleneck7_tri.cv sig7 : ℝ) :=
    mul_le_mul_of_nonneg_right bottleneck7_tri_spectralGap_le_certificate hcv_nonneg
  have hcert_lt :
      (sevenNodeTriclusterBottleneckSpectralGapCertificate : ℝ) *
          (bottleneck7_tri.cv sig7 : ℝ) <
        (17 / 20 : ℝ) := by
    norm_num [sevenNodeTriclusterBottleneckSpectralGapCertificate, hcv]
  have hthetaR : (((17 / 20 : ℚ) : ℝ) ≤ (theta : ℝ)) := by
    exact_mod_cast htheta
  have hthreshold : ((17 / 20 : ℚ) : ℝ) = (17 / 20 : ℝ) := by
    norm_num
  exact not_lt_of_ge hwell.2
    (lt_of_le_of_lt hprod_le (lt_of_lt_of_le hcert_lt (by simpa [hthreshold] using hthetaR)))

/-- The discharged `bottleneck9_bi` spectral-gap upper bound makes the upper
side of the window an actual spectral-CV exclusion, not merely a probe
certificate exclusion. -/
theorem bottleneck9_bi_not_actualSpectralWellConnectedAt_of_ge
    {theta : ℚ} (htheta : 17 / 20 ≤ theta) :
    ¬ SpectralWellConnectedAt bottleneck9_bi sig9 theta (by norm_num : 2 ≤ 9) := by
  intro hwell
  unfold SpectralWellConnectedAt at hwell
  have hcv : bottleneck9_bi.cv sig9 = 166680000 / 200016667 :=
    n9_cv_values.2.2.2.2.2.2
  have hcv_nonneg : 0 ≤ (bottleneck9_bi.cv sig9 : ℝ) :=
    bottleneck9_bi.spectralWellConnected_cv_cast_nonneg sig9
  have hprod_le :
      bottleneck9_bi.spectralGap (by norm_num : 2 ≤ 9) *
          (bottleneck9_bi.cv sig9 : ℝ) ≤
        (bottleneck9BiSpectralGapCertificate : ℝ) *
          (bottleneck9_bi.cv sig9 : ℝ) :=
    mul_le_mul_of_nonneg_right bottleneck9_bi_spectralGap_le_certificate hcv_nonneg
  have hcert_lt :
      (bottleneck9BiSpectralGapCertificate : ℝ) * (bottleneck9_bi.cv sig9 : ℝ) <
        (17 / 20 : ℝ) := by
    norm_num [bottleneck9BiSpectralGapCertificate, hcv]
  have hthetaR : (((17 / 20 : ℚ) : ℝ) ≤ (theta : ℝ)) := by
    exact_mod_cast htheta
  have hthreshold : ((17 / 20 : ℚ) : ℝ) = (17 / 20 : ℝ) := by
    norm_num
  exact not_lt_of_ge hwell.2
    (lt_of_le_of_lt hprod_le (lt_of_lt_of_le hcert_lt (by simpa [hthreshold] using hthetaR)))

/-- Inside the certified admissible threshold window, the archetypes whose gap
certificates are discharged already range over actual `spectralGap` values:
`uniK5`, `uniK7`, and `uniK9` pass, while `bottleneck5`, `bottleneck7_bi`,
`bottleneck7_tri`, and `bottleneck9_bi` fail. -/
theorem discharged_archetypes_admissible_window_actual_gaps :
    ∃ theta_min theta_max : ℚ,
      theta_min ≤ (17 / 20 : ℚ) ∧ (17 / 20 : ℚ) ≤ theta_max ∧
        (∀ theta ∈ Set.Icc theta_min theta_max,
          SpectralWellConnectedAt uniK5 sig5 theta (by norm_num : 2 ≤ 5)) ∧
        (∀ theta ∈ Set.Icc theta_min theta_max,
          SpectralWellConnectedAt uniK7 sig7 theta (by norm_num : 2 ≤ 7)) ∧
        (∀ theta ∈ Set.Icc theta_min theta_max,
          SpectralWellConnectedAt uniK9 sig9 theta (by norm_num : 2 ≤ 9)) ∧
        (∀ theta ∈ Set.Icc theta_min theta_max,
          ¬ SpectralWellConnectedAt bottleneck5 sig5 theta (by norm_num : 2 ≤ 5)) ∧
        (∀ theta ∈ Set.Icc theta_min theta_max,
          ¬ SpectralWellConnectedAt bottleneck7_bi sig7 theta (by norm_num : 2 ≤ 7)) ∧
        (∀ theta ∈ Set.Icc theta_min theta_max,
          ¬ SpectralWellConnectedAt bottleneck7_tri sig7 theta (by norm_num : 2 ≤ 7)) ∧
        (∀ theta ∈ Set.Icc theta_min theta_max,
          ¬ SpectralWellConnectedAt bottleneck9_bi sig9 theta (by norm_num : 2 ≤ 9)) := by
  refine ⟨17 / 20, 46 / 53, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro theta htheta
    exact uniK5_actualSpectralWellConnectedAt_of_le htheta.2
  · intro theta htheta
    exact uniK7_actualSpectralWellConnectedAt_of_le htheta.2
  · intro theta htheta
    exact uniK9_actualSpectralWellConnectedAt_of_le htheta.2
  · intro theta htheta
    exact bottleneck5_not_actualSpectralWellConnectedAt_of_ge htheta.1
  · intro theta htheta
    exact bottleneck7_bi_not_actualSpectralWellConnectedAt_of_ge htheta.1
  · intro theta htheta
    exact bottleneck7_tri_not_actualSpectralWellConnectedAt_of_ge htheta.1
  · intro theta htheta
    exact bottleneck9_bi_not_actualSpectralWellConnectedAt_of_ge htheta.1

/-- Hierarchical nine-node witnesses are outside the certified well-connected
class for the same rational separator. -/
theorem nineNode_hierarchical_archetypes_not_certifiedSpectralWellConnected :
    ¬ ProbeSpectralWellConnected hubSpokeHierarchy9SDeltaCertificate ∧
    ¬ ProbeSpectralWellConnected nestedHierarchy9SDeltaCertificate := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  repeat' constructor <;> native_decide

/-- Finite cross-scale certified universality package: across the concrete
five-, seven-, and nine-node canonical family, every certified non-bottleneck
archetype clears the separator, while every certified bottleneck variant fails
it. -/
theorem finite_crossScale_certified_spectral_universality :
    NonbottleneckArchetypesCertifiedSpectralWellConnected ∧
    BottleneckArchetypesNotCertifiedSpectralWellConnected := by
  exact ⟨all_nonbottleneck_archetypes_certifiedSpectralWellConnected,
    all_bottleneck_archetypes_not_certifiedSpectralWellConnected⟩


end Legitimacy
