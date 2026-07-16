/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Capacity.CriticalCapability
import Mathlib.Tactic.NormNum

/-!
# Legitimacy.Spectral.Core.SpectralWellConnected

Composite spectral predicate used by the cross-scale basin probes.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset

/-- Spectral-CV product used by the cross-scale basin probe. This is the
formal counterpart of the empirical `S_delta(G, s)` score. -/
noncomputable def GovGraph.spectralCvProduct
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n) : ℝ :=
  G.spectralGap hn * Rat.cast (G.cv s)

/-- Pure spectral-gap lower bound, separated from any vulnerability claim. -/
noncomputable def SpectralGapLowerBound
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (theta : ℚ) (hn : 2 ≤ n) : Prop :=
  (theta : ℝ) ≤ G.spectralGap hn

/-- Connectivity-side spectral content: positive algebraic connectivity. The
signal argument is retained so this predicate can share the same call shape as
the composite semantic-kernel witness. -/
noncomputable def SpectralConnected
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (_s : Fin n → ℚ) (hn : 2 ≤ n) : Prop :=
  0 < G.spectralGap hn

/-- Parameterized positive-vulnerability product condition from the cross-scale
basin probe. This is the `S_delta(G, s)` threshold, not a pure connectivity
condition. -/
noncomputable def PositiveGovernanceVulnerabilityAt
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (theta : ℚ) (hn : 2 ≤ n) : Prop :=
  (G.spectralGap hn : ℝ) * (G.cv s : ℝ) ≥ (theta : ℝ)

/-- Parameterized composite spectral witness: a pure positive spectral gap and
the vulnerability-sensitive product threshold. -/
noncomputable def SpectralWellConnectedAt
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (theta : ℚ) (hn : 2 ≤ n) : Prop :=
  SpectralConnected G s hn ∧
    PositiveGovernanceVulnerabilityAt G s theta hn

/-- Named default separator for the five/seven/nine-node spectral probe family. -/
def defaultSeparatorAt_n5_n7_n9 : ℚ := 17 / 20

/-- Default positive-vulnerability product condition at the named
five/seven/nine-node separator. -/
noncomputable def PositiveGovernanceVulnerability
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n) : Prop :=
  PositiveGovernanceVulnerabilityAt G s defaultSeparatorAt_n5_n7_n9 hn

/-- Historical compatibility name for the semantic-kernel spectral witness. It
is now explicitly the conjunction of spectral connectivity and positive
governance vulnerability. -/
noncomputable def SpectralWellConnected
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n) : Prop :=
  SpectralConnected G s hn ∧ PositiveGovernanceVulnerability G s hn

/-- Consistency vulnerability is nonnegative: it is a finite supremum of
absolute perturbation magnitudes. This local name avoids depending on the
Stackelberg convergence layer. -/
lemma GovGraph.spectralWellConnected_cv_nonneg
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) :
    0 ≤ G.cv s := by
  classical
  let p : Fin n × Fin n :=
    (Finset.univ_nonempty : (Finset.univ (α := Fin n × Fin n)).Nonempty).choose
  have hp : p ∈ Finset.univ := by simp
  exact le_trans (abs_nonneg (G.gov s p.2 - G.govRemoved s p.1 p.2))
    (Finset.le_sup'
      (f := fun p : Fin n × Fin n =>
        |G.gov s p.2 - G.govRemoved s p.1 p.2|)
      hp)

/-- Real-cast form of `GovGraph.spectralWellConnected_cv_nonneg`. -/
lemma GovGraph.spectralWellConnected_cv_cast_nonneg
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) :
    0 ≤ (G.cv s : ℝ) := by
  exact_mod_cast G.spectralWellConnected_cv_nonneg s

/-- Unfolding lemma for the product score. -/
theorem SpectralWellConnected_iff_product_threshold
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n) :
    SpectralWellConnected G s hn ↔
      (17 : ℝ) / 20 ≤ G.spectralGap hn * Rat.cast (G.cv s) := by
  constructor
  · intro hG
    simpa [SpectralWellConnected, PositiveGovernanceVulnerability,
      PositiveGovernanceVulnerabilityAt, defaultSeparatorAt_n5_n7_n9,
      Rat.cast_div, Rat.cast_ofNat] using hG.2
  · intro hprod
    have hdefault : (0 : ℝ) < (defaultSeparatorAt_n5_n7_n9 : ℝ) := by
      norm_num [defaultSeparatorAt_n5_n7_n9]
    have hprod' :
        (defaultSeparatorAt_n5_n7_n9 : ℝ) ≤
          G.spectralGap hn * (G.cv s : ℝ) := by
      simpa [defaultSeparatorAt_n5_n7_n9, Rat.cast_div, Rat.cast_ofNat] using hprod
    have hprod_pos : 0 < G.spectralGap hn * (G.cv s : ℝ) :=
      lt_of_lt_of_le hdefault hprod'
    have hcv_nonneg : 0 ≤ (G.cv s : ℝ) :=
      G.spectralWellConnected_cv_cast_nonneg s
    have hgap_pos : 0 < G.spectralGap hn := by
      rcases (mul_pos_iff.mp hprod_pos) with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_lt_of_ge hcv_nonneg) hneg.2)
    exact ⟨hgap_pos, hprod'⟩

/-- The default predicate is definitionally the parameterized predicate at the
named default separator. -/
theorem SpectralWellConnected_iff_at_named_default
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n) :
    SpectralWellConnected G s hn ↔
      SpectralWellConnectedAt G s defaultSeparatorAt_n5_n7_n9 hn := by
  rfl

/-- The default predicate is exactly the parameterized predicate at threshold
`17 / 20`. -/
theorem SpectralWellConnected_iff_at_default
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n) :
    SpectralWellConnected G s hn ↔
      SpectralWellConnectedAt G s (17 / 20) hn := by
  simp [SpectralWellConnected, SpectralWellConnectedAt,
    PositiveGovernanceVulnerability, PositiveGovernanceVulnerabilityAt,
    defaultSeparatorAt_n5_n7_n9]

/-- The default positive-vulnerability product condition forces both factors in
the spectral-CV product to be strictly positive. -/
theorem PositiveGovernanceVulnerability_positive_factors
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n)
    (hG : PositiveGovernanceVulnerability G s hn) :
    0 < G.spectralGap hn ∧ 0 < (G.cv s : ℝ) := by
  have hprod : 0 < G.spectralGap hn * (G.cv s : ℝ) := by
    have hdefault : (0 : ℝ) < (defaultSeparatorAt_n5_n7_n9 : ℝ) := by
      norm_num [defaultSeparatorAt_n5_n7_n9]
    have hG' :
        (defaultSeparatorAt_n5_n7_n9 : ℝ) ≤
          G.spectralGap hn * (G.cv s : ℝ) := by
      simpa [PositiveGovernanceVulnerability,
        PositiveGovernanceVulnerabilityAt] using hG
    exact lt_of_lt_of_le hdefault hG'
  have hcv_nonneg : 0 ≤ (G.cv s : ℝ) :=
    G.spectralWellConnected_cv_cast_nonneg s
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact hpos
  · exact False.elim ((not_lt_of_ge hcv_nonneg) hneg.2)

/-- Membership in `SpectralWellConnected` forces both factors in the
spectral-CV product to be strictly positive. -/
theorem SpectralWellConnected_positive_factors
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n)
    (hG : SpectralWellConnected G s hn) :
    0 < G.spectralGap hn ∧ 0 < (G.cv s : ℝ) :=
  PositiveGovernanceVulnerability_positive_factors G s hn hG.2

/-- Rational CV positivity induced by the default positive-vulnerability
condition. -/
theorem PositiveGovernanceVulnerability_cv_pos
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n)
    (hG : PositiveGovernanceVulnerability G s hn) :
    0 < G.cv s := by
  have hcv : 0 < (G.cv s : ℝ) :=
    (PositiveGovernanceVulnerability_positive_factors G s hn hG).2
  exact_mod_cast hcv

/-- Rational CV positivity induced by `SpectralWellConnected`. -/
theorem SpectralWellConnected_cv_pos
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n)
    (hG : SpectralWellConnected G s hn) :
    0 < G.cv s := by
  exact PositiveGovernanceVulnerability_cv_pos G s hn hG.2

/-- `SpectralWellConnected` gives reciprocal lower bounds for both factors:
the spectral gap is large relative to CV, and CV is large relative to the
spectral gap. -/
theorem SpectralWellConnected_factor_lower_bounds
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n)
    (hG : SpectralWellConnected G s hn) :
    (17 : ℝ) / 20 / (G.cv s : ℝ) ≤ G.spectralGap hn ∧
      (17 : ℝ) / 20 / G.spectralGap hn ≤ (G.cv s : ℝ) := by
  have hpos := SpectralWellConnected_positive_factors G s hn hG
  constructor
  · exact (div_le_iff₀ hpos.2).mpr
      (by simpa [SpectralWellConnected, SpectralWellConnectedAt,
        PositiveGovernanceVulnerability, PositiveGovernanceVulnerabilityAt,
        defaultSeparatorAt_n5_n7_n9, GovGraph.spectralCvProduct,
        Rat.cast_div, Rat.cast_ofNat] using hG.2)
  · exact (div_le_iff₀ hpos.1).mpr (by
      simpa [SpectralWellConnected, SpectralWellConnectedAt,
        PositiveGovernanceVulnerability, PositiveGovernanceVulnerabilityAt,
        defaultSeparatorAt_n5_n7_n9, GovGraph.spectralCvProduct,
        Rat.cast_div, Rat.cast_ofNat, mul_comm] using hG.2)

/-- Exact relative classification: the threshold class is precisely the
positive product cone cut out by the reciprocal factor lower bounds. -/
theorem SpectralWellConnected_iff_factor_lower_bounds
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n) :
    SpectralWellConnected G s hn ↔
      0 < G.spectralGap hn ∧
        0 < (G.cv s : ℝ) ∧
          (17 : ℝ) / 20 / (G.cv s : ℝ) ≤ G.spectralGap hn ∧
            (17 : ℝ) / 20 / G.spectralGap hn ≤ (G.cv s : ℝ) := by
  constructor
  · intro hG
    exact ⟨(SpectralWellConnected_positive_factors G s hn hG).1,
      (SpectralWellConnected_positive_factors G s hn hG).2,
      (SpectralWellConnected_factor_lower_bounds G s hn hG).1,
      (SpectralWellConnected_factor_lower_bounds G s hn hG).2⟩
  · intro h
    refine ⟨h.1, ?_⟩
    simpa [SpectralWellConnected, SpectralWellConnectedAt,
      PositiveGovernanceVulnerability, PositiveGovernanceVulnerabilityAt,
      defaultSeparatorAt_n5_n7_n9, GovGraph.spectralCvProduct,
      Rat.cast_div, Rat.cast_ofNat] using
      (div_le_iff₀ h.2.1).mp h.2.2.1

/-- Critical-capability consequence of the product-cone classification:
inside `SpectralWellConnected`, the exact reciprocal threshold is bounded
above by an explicit linear function of the spectral gap. -/
theorem SpectralWellConnected_C_star_le_spectralGap
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (hn : 2 ≤ n)
    (δ : ℚ) (hδ : 0 ≤ δ)
    (hG : SpectralWellConnected G s hn) :
    (C_star G s δ : ℝ) ≤
      (20 : ℝ) / 17 * (δ : ℝ) * G.spectralGap hn := by
  have hpos := SpectralWellConnected_positive_factors G s hn hG
  have hcv_lb := (SpectralWellConnected_factor_lower_bounds G s hn hG).2
  have hδR : 0 ≤ (δ : ℝ) := by exact_mod_cast hδ
  have hbase :
      (δ : ℝ) / (G.cv s : ℝ) ≤
        (δ : ℝ) / (((17 : ℝ) / 20) / G.spectralGap hn) :=
    div_le_div_of_nonneg_left hδR
      (div_pos (by norm_num) hpos.1) hcv_lb
  have hgap_ne : G.spectralGap hn ≠ 0 := ne_of_gt hpos.1
  have hthreshold_ne : ((17 : ℝ) / 20) ≠ 0 := by norm_num
  calc
    (C_star G s δ : ℝ)
        = (δ : ℝ) / (G.cv s : ℝ) := by
            simp [C_star]
    _ ≤ (δ : ℝ) / (((17 : ℝ) / 20) / G.spectralGap hn) := hbase
    _ = (20 : ℝ) / 17 * (δ : ℝ) * G.spectralGap hn := by
            field_simp [hgap_ne, hthreshold_ne]

end Legitimacy
