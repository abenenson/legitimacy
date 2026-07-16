/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Core.SpectralWellConnected

/-!
  Concrete 9-node archetypes for the cross-scale spectral probe.

  The graph constructors follow the calibrated odd-scale family from the probe
  scripts: complete, asymmetric complete, near-path with weak leakage, weak
  center bottleneck, hub-spoke hierarchy, nested hierarchy, and wheel.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

private def nearPath9Weight (i j : Fin 9) : ℚ :=
  if i = j then 0
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1
  else 1 / 50

private def bottleneck9BiWeight (i j : Fin 9) : ℚ :=
  if i = j then 0
  else if i.val < 4 ∧ j.val < 4 then 1
  else if 4 < i.val ∧ 4 < j.val then 1
  else if i.val = 4 ∨ j.val = 4 then 1 / 10000
  else 0

private def hubSpokeHierarchy9Weight (i j : Fin 9) : ℚ :=
  if i = j then 0
  else if (i.val = 0 ∧ 1 ≤ j.val ∧ j.val ≤ 5) ∨
      (j.val = 0 ∧ 1 ≤ i.val ∧ i.val ≤ 5) then 1
  else if (i.val = 1 ∧ 6 ≤ j.val) ∨ (j.val = 1 ∧ 6 ≤ i.val) then 1 / 10
  else 0

private def nestedHierarchy9Weight (i j : Fin 9) : ℚ :=
  if i = j then 0
  else if i.val < 3 ∧ j.val < 3 then 1
  else if 3 ≤ i.val ∧ i.val ≤ 5 ∧ 3 ≤ j.val ∧ j.val ≤ 5 then 1 / 2
  else if (i.val < 3 ∧ 3 ≤ j.val ∧ j.val ≤ 5) ∨
      (j.val < 3 ∧ 3 ≤ i.val ∧ i.val ≤ 5) then 1 / 5
  else if (3 ≤ i.val ∧ i.val ≤ 5 ∧ 6 ≤ j.val) ∨
      (3 ≤ j.val ∧ j.val ≤ 5 ∧ 6 ≤ i.val) then 1 / 20
  else 0

private def wheel9Weight (i j : Fin 9) : ℚ :=
  if i = j then 0
  else if i.val = 0 ∨ j.val = 0 then 1
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (i.val = 1 ∧ j.val = 8) ∨ (i.val = 8 ∧ j.val = 1) then 1 / 10
  else 0

/-- Experimental 9-node lattice witness: the uniform complete graph `K_9`. -/
def uniK9 : GovGraph ℚ 9 where
  weights i j := if i = j then 0 else 1
  weight_symm := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  weight_nonneg := by
    intro i j
    by_cases hij : i = j <;> simp [hij]
  weight_self_zero := by
    intro i
    simp

/-- Experimental 9-node lattice witness: `K_9` with one heavier edge
`w_01 = 2`. -/
def asymK9 : GovGraph ℚ 9 where
  weights i j :=
    if i = j then 0
    else if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) then 2
    else 1
  weight_symm := by
    intro i j
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by
    intro i
    fin_cases i <;> native_decide

/-- Experimental 9-node lattice witness: a path with weak long-range leakage
of weight `1/50`. -/
def nearPath9 : GovGraph ℚ 9 where
  weights := nearPath9Weight
  weight_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by
    intro i
    fin_cases i <;> native_decide

/-- Experimental 9-node lattice witness: two 4-cliques connected only through
a weak center node `4`. -/
def bottleneck9_bi : GovGraph ℚ 9 where
  weights := bottleneck9BiWeight
  weight_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by
    intro i
    fin_cases i <;> native_decide

/-- Experimental 9-node lattice witness: a hub-and-spoke hierarchy with hub
`0`, primary spokes `{1,2,3,4,5}`, and a secondary weak branch `{6,7,8}`
attached through spoke `1`. -/
def hubSpokeHierarchy9 : GovGraph ℚ 9 where
  weights := hubSpokeHierarchy9Weight
  weight_symm := by
    intro i j
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by
    intro i
    fin_cases i <;> native_decide

/-- Experimental 9-node lattice witness: a nested three-level hierarchy with
inner clique `{0,1,2}`, middle clique `{3,4,5}`, and outer leaves `{6,7,8}`. -/
def nestedHierarchy9 : GovGraph ℚ 9 where
  weights := nestedHierarchy9Weight
  weight_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by
    intro i
    fin_cases i <;> native_decide

/-- Experimental 9-node lattice witness: a wheel with hub `0`, unit spokes,
and rim edges of weight `1/10`. -/
def wheel9 : GovGraph ℚ 9 where
  weights := wheel9Weight
  weight_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by
    intro i
    fin_cases i <;> native_decide

/-- Standard 9-node concrete signal used for the cross-scale spectral probe. -/
def sig9 : Fin 9 → ℚ := ![1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The signal range of `sig9` is exactly 8. -/
lemma sig9_signalRange : signalRange sig9 = 8 := by
  native_decide

/-- Exact consistency-vulnerability values for the seven `n = 9` archetypes. -/
theorem n9_cv_values :
    uniK9.cv sig9 = 5 / 8 ∧
    asymK9.cv sig9 = 10 / 9 ∧
    nearPath9.cv sig9 = 200 / 57 ∧
    hubSpokeHierarchy9.cv sig9 = 70 / 13 ∧
    nestedHierarchy9.cv sig9 = 55 / 52 ∧
    wheel9.cv sig9 = 35 / 6 ∧
    bottleneck9_bi.cv sig9 = 166680000 / 200016667 := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  repeat' constructor <;> native_decide

/-- Probe-side rational spectral-gap certificate for `uniK9`. -/
def uniK9SpectralGapCertificate : ℚ := 9

/-- Probe-side rational spectral-gap certificate for `asymK9`. -/
def asymK9SpectralGapCertificate : ℚ := 9

/-- Conservative rational lower-bound certificate for `nearPath9`. -/
def nearPath9SpectralGapCertificate : ℚ := 2982 / 10000

/-- Exact rational spectral-gap certificate for `hubSpokeHierarchy9`. -/
def hubSpokeHierarchy9SpectralGapCertificate : ℚ := 1 / 10

/-- Exact rational spectral-gap certificate for `nestedHierarchy9`. -/
def nestedHierarchy9SpectralGapCertificate : ℚ := 3 / 20

/-- Conservative rational lower-bound certificate for `wheel9`. -/
def wheel9SpectralGapCertificate : ℚ := 1058 / 1000

/-- Exact rational spectral-gap certificate for `bottleneck9_bi`. -/
def bottleneck9BiSpectralGapCertificate : ℚ := 1 / 10000

/-- Probe-side `S_delta = lambda_2 * CV` certificates. -/
def uniK9SDeltaCertificate : ℚ := uniK9SpectralGapCertificate * uniK9.cv sig9

/-- Probe-side `S_delta = lambda_2 * CV` certificate. -/
def asymK9SDeltaCertificate : ℚ := asymK9SpectralGapCertificate * asymK9.cv sig9

/-- Probe-side `S_delta = lambda_2 * CV` certificate. -/
def nearPath9SDeltaCertificate : ℚ :=
  nearPath9SpectralGapCertificate * nearPath9.cv sig9

/-- Probe-side `S_delta = lambda_2 * CV` certificate. -/
def hubSpokeHierarchy9SDeltaCertificate : ℚ :=
  hubSpokeHierarchy9SpectralGapCertificate * hubSpokeHierarchy9.cv sig9

/-- Probe-side `S_delta = lambda_2 * CV` certificate. -/
def nestedHierarchy9SDeltaCertificate : ℚ :=
  nestedHierarchy9SpectralGapCertificate * nestedHierarchy9.cv sig9

/-- Probe-side `S_delta = lambda_2 * CV` certificate. -/
def wheel9SDeltaCertificate : ℚ := wheel9SpectralGapCertificate * wheel9.cv sig9

/-- Probe-side `S_delta = lambda_2 * CV` certificate. -/
def bottleneck9BiSDeltaCertificate : ℚ :=
  bottleneck9BiSpectralGapCertificate * bottleneck9_bi.cv sig9

/-- Computable version of the probe separator on a rational certificate. -/
def ProbeSpectralWellConnected (sDelta : ℚ) : Prop :=
  (17 / 20 : ℚ) ≤ sDelta

instance instDecidableProbeSpectralWellConnected (sDelta : ℚ) :
    Decidable (ProbeSpectralWellConnected sDelta) := by
  unfold ProbeSpectralWellConnected
  infer_instance

/-- Exact rational `S_delta` certificate values for the seven `n = 9`
archetypes. -/
theorem n9_sdelta_certificate_values :
    uniK9SDeltaCertificate = 45 / 8 ∧
    asymK9SDeltaCertificate = 10 ∧
    nearPath9SDeltaCertificate = 497 / 475 ∧
    hubSpokeHierarchy9SDeltaCertificate = 7 / 13 ∧
    nestedHierarchy9SDeltaCertificate = 33 / 208 ∧
    wheel9SDeltaCertificate = 3703 / 600 ∧
    bottleneck9BiSDeltaCertificate = 16668 / 200016667 := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  repeat' constructor <;> native_decide

/-- The certified `n = 9` probe split at threshold `17/20`: complete,
asymmetric complete, near-path, and wheel pass; weak bottleneck,
hub-spoke, and nested hierarchy fail. -/
theorem n9_probe_spectral_well_connected_decisions :
    ProbeSpectralWellConnected uniK9SDeltaCertificate ∧
    ProbeSpectralWellConnected asymK9SDeltaCertificate ∧
    ProbeSpectralWellConnected nearPath9SDeltaCertificate ∧
    ¬ ProbeSpectralWellConnected hubSpokeHierarchy9SDeltaCertificate ∧
    ¬ ProbeSpectralWellConnected nestedHierarchy9SDeltaCertificate ∧
    ProbeSpectralWellConnected wheel9SDeltaCertificate ∧
    ¬ ProbeSpectralWellConnected bottleneck9BiSDeltaCertificate := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  repeat' constructor <;> native_decide

/-- Conditional bridge from an exact or lower-bound spectral-gap certificate to
the noncomputable `SpectralWellConnected` predicate. -/
lemma SpectralWellConnected_of_gap_certificate
    (G : GovGraph ℚ 9) (lambda cv : ℚ)
    (hgap : (lambda : ℝ) ≤ G.spectralGap (by norm_num : 2 ≤ 9))
    (hcv : G.cv sig9 = cv)
    (hprod : (17 / 20 : ℚ) ≤ lambda * cv) :
    SpectralWellConnected G sig9 (by norm_num : 2 ≤ 9) := by
  have hcvR : (G.cv sig9 : ℝ) = cv := by
    exact_mod_cast hcv
  have hprodR' : (((17 / 20 : ℚ) : ℝ) ≤ ((lambda * cv : ℚ) : ℝ)) := by
    exact_mod_cast hprod
  have hthreshold : ((17 / 20 : ℚ) : ℝ) = (17 / 20 : ℝ) := by
    norm_num
  have hprodR : (17 / 20 : ℝ) ≤ (lambda : ℝ) * (cv : ℝ) := by
    simpa [hthreshold] using hprodR'
  have hcv_nonneg : 0 ≤ (cv : ℝ) := by
    rw [← hcvR]
    exact G.spectralWellConnected_cv_cast_nonneg sig9
  exact (SpectralWellConnected_iff_product_threshold G sig9
    (by norm_num : 2 ≤ 9)).mpr (le_trans hprodR (by
    change (lambda : ℝ) * (cv : ℝ) ≤
      G.spectralGap (by norm_num : 2 ≤ 9) * (G.cv sig9 : ℝ)
    rw [hcvR]
    exact mul_le_mul_of_nonneg_right hgap hcv_nonneg))

/-- Conditional exclusion from `SpectralWellConnected` using an upper spectral
gap certificate. -/
lemma not_SpectralWellConnected_of_gap_certificate
    (G : GovGraph ℚ 9) (lambda cv : ℚ)
    (hgap : G.spectralGap (by norm_num : 2 ≤ 9) ≤ (lambda : ℝ))
    (hcv : G.cv sig9 = cv)
    (hprod : lambda * cv < (17 / 20 : ℚ)) :
    ¬ SpectralWellConnected G sig9 (by norm_num : 2 ≤ 9) := by
  intro hwell
  have hcvR : (G.cv sig9 : ℝ) = cv := by
    exact_mod_cast hcv
  have hprodR' : (((lambda * cv : ℚ) : ℝ) < ((17 / 20 : ℚ) : ℝ)) := by
    exact_mod_cast hprod
  have hthreshold : ((17 / 20 : ℚ) : ℝ) = (17 / 20 : ℝ) := by
    norm_num
  have hprodR : (lambda : ℝ) * (cv : ℝ) < (17 / 20 : ℝ) := by
    simpa [hthreshold] using hprodR'
  have hnonneg : 0 ≤ (G.cv sig9 : ℝ) :=
    G.spectralWellConnected_cv_cast_nonneg sig9
  have hle : G.spectralGap (by norm_num : 2 ≤ 9) * (G.cv sig9 : ℝ) ≤
      (lambda : ℝ) * (cv : ℝ) := by
    rw [hcvR]
    exact mul_le_mul_of_nonneg_right hgap (by simpa [hcvR] using hnonneg)
  have hlt : G.spectralCvProduct sig9 (by norm_num : 2 ≤ 9) < (17 / 20 : ℝ) := by
    simpa [GovGraph.spectralCvProduct] using lt_of_le_of_lt hle hprodR
  exact not_lt_of_ge
    ((SpectralWellConnected_iff_product_threshold G sig9
      (by norm_num : 2 ≤ 9)).mp hwell)
    (by simpa [GovGraph.spectralCvProduct, defaultSeparatorAt_n5_n7_n9] using hlt)

end Legitimacy
