/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Dynamics.StackelbergConvergence

/-!
# Adversarial capability scaling for the Stackelberg limit

This module lifts the static `C_star` Stackelberg limit through explicit
capability-scaling functions. The formal substrate has an important polarity:
`ZeroConsistencyVulnerability` graphs are stable at every positive capability. Hence
eventual loss of all stable equilibria along unbounded adversarial scaling is
equivalent to *non*-strategyproofness, while strategyproofness is equivalent to
failure of that eventual-loss property.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

variable {n : Nat}

/-- A monotone function `ℚ → ℚ` representing how the adversary's effective
capability scales with some external parameter such as compute, scale, or
time. Monotonicity records that increasing the external parameter cannot reduce
the adversary's reach. -/
structure AdversarialCapabilityScaling where
  scaling : ℚ → ℚ
  monotone : Monotone scaling

namespace AdversarialCapabilityScaling

/-- A scaling is cofinal when it eventually clears every rational capability
floor. Monotonicity alone is not enough: constant functions are monotone but do
not model unbounded adversarial capability. -/
def Cofinal (scaling : AdversarialCapabilityScaling) : Prop :=
  ∀ floor : ℚ, ∃ κ : ℚ, floor ≤ scaling.scaling κ

/-- Identity capability scaling. -/
def identity : AdversarialCapabilityScaling where
  scaling := id
  monotone := by
    intro κ₁ κ₂ hκ
    exact hκ

@[simp] private lemma identity_apply (κ : ℚ) :
    identity.scaling κ = κ :=
  rfl

/-- Constant capability scaling. This is monotone, but generally not cofinal. -/
def constant (capability : ℚ) : AdversarialCapabilityScaling where
  scaling := fun _ => capability
  monotone := by
    intro _ _ _
    exact le_rfl

@[simp] private lemma constant_apply (capability κ : ℚ) :
    (constant capability).scaling κ = capability :=
  rfl

/-- Affine scaling by a nonnegative slope. -/
def affine (slope intercept : ℚ) (hslope : 0 ≤ slope) :
    AdversarialCapabilityScaling where
  scaling := fun κ => slope * κ + intercept
  monotone := by
    intro κ₁ κ₂ hκ
    have hmul : slope * κ₁ ≤ slope * κ₂ := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hκ hslope
    linarith

/-- Composition of monotone capability scalings is monotone. -/
def comp (outer inner : AdversarialCapabilityScaling) :
    AdversarialCapabilityScaling where
  scaling := fun κ => outer.scaling (inner.scaling κ)
  monotone := by
    intro κ₁ κ₂ hκ
    exact outer.monotone (inner.monotone hκ)

private lemma identity_cofinal : identity.Cofinal := by
  intro floor
  exact ⟨floor, le_rfl⟩

private lemma affine_positive_slope_cofinal
    (slope intercept : ℚ) (hslope : 0 < slope) :
    (affine slope intercept hslope.le).Cofinal := by
  intro floor
  refine ⟨(floor - intercept) / slope, ?_⟩
  rw [affine]
  change floor ≤ slope * ((floor - intercept) / slope) + intercept
  rw [mul_div_cancel₀ _ (ne_of_gt hslope)]
  ring_nf
  exact le_rfl

end AdversarialCapabilityScaling

/-- Eventual adversarial collapse along every cofinal monotone scaling. -/
def AdversarialEventuallyNoStable
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) : Prop :=
  ∀ scaling : AdversarialCapabilityScaling,
    scaling.Cofinal →
      ∃ κ_threshold : ℚ, ∀ κ ≥ κ_threshold,
        ¬ SpectralStableEquilibrium G s δ (scaling.scaling κ)

/-- Non-zero-CV graphs eventually lose all stable equilibria along every
cofinal monotone adversarial capability scaling. -/
theorem adversarial_stackelberg_unbounded_of_positive_consistency_vulnerability
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hnot : ¬ ZeroConsistencyVulnerability G s)
    (scaling : AdversarialCapabilityScaling)
    (hcofinal : scaling.Cofinal) :
    ∃ κ_threshold : ℚ, ∀ κ ≥ κ_threshold,
      ¬ SpectralStableEquilibrium G s δ (scaling.scaling κ) := by
  obtain ⟨cap_threshold, _hcap_pos, hno⟩ :=
    eventually_no_stable_equilibrium_of_positive_consistency_vulnerability G s δ hδ hnot
  obtain ⟨κ_threshold, hfloor⟩ := hcofinal cap_threshold
  refine ⟨κ_threshold, ?_⟩
  intro κ hκ hstable
  have hscale : scaling.scaling κ_threshold ≤ scaling.scaling κ :=
    scaling.monotone hκ
  exact hno (le_trans hfloor hscale) hstable

/-- Deprecated compatibility alias for
`adversarial_stackelberg_unbounded_of_positive_consistency_vulnerability`. -/
theorem adversarial_stackelberg_unbounded_of_not_strategyproof
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hnot : ¬ SpectralStrategyproof G s)
    (scaling : AdversarialCapabilityScaling)
    (hcofinal : scaling.Cofinal) :
    ∃ κ_threshold : ℚ, ∀ κ ≥ κ_threshold,
      ¬ SpectralStableEquilibrium G s δ (scaling.scaling κ) :=
  adversarial_stackelberg_unbounded_of_positive_consistency_vulnerability
    G s δ hδ hnot scaling hcofinal

/-- If every cofinal monotone adversarial scaling eventually destroys stable
equilibria, then the graph is not zero-CV. The identity
scaling is the separating witness: zero-CV graphs are stable at every
positive identity capability. -/
theorem positive_consistency_vulnerability_of_adversarial_stackelberg_unbounded
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (h : AdversarialEventuallyNoStable G s δ) :
    ¬ ZeroConsistencyVulnerability G s := by
  intro hsp
  obtain ⟨κ_threshold, hno⟩ :=
    h AdversarialCapabilityScaling.identity
      AdversarialCapabilityScaling.identity_cofinal
  let κ : ℚ := max κ_threshold 1
  have hκ_ge : κ_threshold ≤ κ := le_max_left _ _
  have hκ_pos : 0 < κ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hstable :
      SpectralStableEquilibrium G s δ
        (AdversarialCapabilityScaling.identity.scaling κ) := by
    simpa using
      zeroConsistencyVulnerability_stable_all_capabilities G s δ κ hδ hκ_pos hsp
  exact hno κ hκ_ge hstable

/-- Deprecated compatibility alias for
`positive_consistency_vulnerability_of_adversarial_stackelberg_unbounded`. -/
theorem not_strategyproof_of_adversarial_stackelberg_unbounded
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (h : AdversarialEventuallyNoStable G s δ) :
    ¬ SpectralStrategyproof G s :=
  positive_consistency_vulnerability_of_adversarial_stackelberg_unbounded
    G s δ hδ h

/-- The honest polarity of adversarial scaling in the current spectral
Stackelberg substrate: eventual collapse along all cofinal monotone scaling is
equivalent to positive consistency vulnerability. -/
theorem adversarial_stackelberg_eventual_collapse_iff_positive_consistency_vulnerability
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ) :
    AdversarialEventuallyNoStable G s δ ↔
      ¬ ZeroConsistencyVulnerability G s := by
  constructor
  · exact positive_consistency_vulnerability_of_adversarial_stackelberg_unbounded G s δ hδ
  · intro hnot scaling hcofinal
    exact adversarial_stackelberg_unbounded_of_positive_consistency_vulnerability
      G s δ hδ hnot scaling hcofinal

/-- Deprecated compatibility alias for
`adversarial_stackelberg_eventual_collapse_iff_positive_consistency_vulnerability`. -/
theorem adversarial_stackelberg_eventual_collapse_iff_not_strategyproof
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ) :
    AdversarialEventuallyNoStable G s δ ↔
      ¬ SpectralStrategyproof G s :=
  adversarial_stackelberg_eventual_collapse_iff_positive_consistency_vulnerability
    G s δ hδ

/-- Equivalently, zero-CV graphs are exactly those that refute
eventual collapse under all cofinal monotone adversarial scaling. -/
theorem adversarial_stackelberg_unbounded_stability_iff_zero_consistency_vulnerability
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ) :
    ¬ AdversarialEventuallyNoStable G s δ ↔
      ZeroConsistencyVulnerability G s := by
  constructor
  · intro hnot_eventual
    by_contra hnot_sp
    exact hnot_eventual
      ((adversarial_stackelberg_eventual_collapse_iff_positive_consistency_vulnerability
        G s δ hδ).mpr hnot_sp)
  · intro hsp heventual
    exact
      ((adversarial_stackelberg_eventual_collapse_iff_positive_consistency_vulnerability
        G s δ hδ).mp heventual) hsp

/-- Deprecated compatibility alias for
`adversarial_stackelberg_unbounded_stability_iff_zero_consistency_vulnerability`. -/
theorem adversarial_stackelberg_unbounded_stability_iff_strategyproof
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ) :
    ¬ AdversarialEventuallyNoStable G s δ ↔
      SpectralStrategyproof G s :=
  adversarial_stackelberg_unbounded_stability_iff_zero_consistency_vulnerability
    G s δ hδ

/-! ## Worked fixtures -/

/-- Zero signal on the concrete triangle, used as a zero-CV fixture. -/
def zeroSig3 : Fin 3 → ℚ := fun _ => 0

lemma zeroConsistencyVulnerability_fixture_zeroSig3 :
    ZeroConsistencyVulnerability uniTriGraph zeroSig3 := by
  -- native_decide: finite rational spectral certificate check over a concrete graph/signal.
  change uniTriGraph.cv zeroSig3 = 0
  native_decide

/-- Deprecated compatibility alias for
`zeroConsistencyVulnerability_fixture_zeroSig3`. -/
lemma strategyproof_fixture_zeroSig3 :
    SpectralStrategyproof uniTriGraph zeroSig3 :=
  zeroConsistencyVulnerability_fixture_zeroSig3

/-- Strategyproof fixture: positive identity capability remains stable even at
a large adversarial scale. This is the concrete refutation of the opposite
polarity "strategyproof implies eventual non-equilibrium." -/
example :
    SpectralStableEquilibrium uniTriGraph zeroSig3 (1 / 10)
      (AdversarialCapabilityScaling.identity.scaling 100) := by
  -- native_decide: finite rational spectral certificate check over a concrete graph/signal.
  rw [spectralStableEquilibrium_iff]
  native_decide

lemma positiveConsistencyVulnerability_fixture_sig :
    ¬ ZeroConsistencyVulnerability uniTriGraph sig := by
  -- native_decide: finite rational spectral certificate check over a concrete graph/signal.
  change uniTriGraph.cv sig ≠ 0
  native_decide

/-- Deprecated compatibility alias for
`positiveConsistencyVulnerability_fixture_sig`. -/
lemma non_strategyproof_fixture_sig :
    ¬ SpectralStrategyproof uniTriGraph sig :=
  positiveConsistencyVulnerability_fixture_sig

/-- Non-zero-CV fixture: identity scaling eventually destroys stability. -/
example :
    ∃ κ_threshold : ℚ, ∀ κ ≥ κ_threshold,
      ¬ SpectralStableEquilibrium uniTriGraph sig (1 / 10)
        (AdversarialCapabilityScaling.identity.scaling κ) := by
  exact adversarial_stackelberg_unbounded_of_positive_consistency_vulnerability
    uniTriGraph sig (1 / 10) (by norm_num)
    positiveConsistencyVulnerability_fixture_sig
    AdversarialCapabilityScaling.identity
    AdversarialCapabilityScaling.identity_cofinal

/-- A monotone but bounded subcritical scaling. -/
def subcriticalConstantScaling : AdversarialCapabilityScaling :=
  AdversarialCapabilityScaling.constant (1 / 20)

/-- Monotonicity alone is insufficient: this positive-CV graph remains
stable forever under a bounded subcritical monotone scaling. -/
private lemma subcritical_constant_scaling_stable_all :
    ∀ κ : ℚ,
      SpectralStableEquilibrium uniTriGraph sig (1 / 10)
        (subcriticalConstantScaling.scaling κ) := by
  intro κ
  -- native_decide: finite rational spectral certificate check over a concrete graph/signal.
  change SpectralStableEquilibrium uniTriGraph sig (1 / 10) (1 / 20)
  rw [spectralStableEquilibrium_iff]
  native_decide

/-- A raw nonmonotone scaling with a subcritical nonnegative tail. -/
def nonmonotoneSubcriticalTail (κ : ℚ) : ℚ :=
  if κ < 0 then 1 / 5 else 1 / 20

private lemma nonmonotoneSubcriticalTail_not_monotone :
    ¬ Monotone nonmonotoneSubcriticalTail := by
  intro hmono
  have hle : (-1 : ℚ) ≤ 0 := by norm_num
  have := hmono hle
  norm_num [nonmonotoneSubcriticalTail] at this

/-- Dropping the structural scaling hypotheses admits a nonmonotone tail that
keeps the positive-CV fixture stable beyond every proposed threshold. -/
private lemma nonmonotone_subcritical_tail_refutes_eventual_collapse :
    ¬ ∃ κ_threshold : ℚ, ∀ κ ≥ κ_threshold,
      ¬ SpectralStableEquilibrium uniTriGraph sig (1 / 10)
        (nonmonotoneSubcriticalTail κ) := by
  rintro ⟨κ_threshold, hno⟩
  let κ : ℚ := max κ_threshold 0
  have hκ_ge : κ_threshold ≤ κ := le_max_left _ _
  have hκ_nonneg : 0 ≤ κ := le_max_right _ _
  have htail : nonmonotoneSubcriticalTail κ = 1 / 20 := by
    simp [nonmonotoneSubcriticalTail, not_lt.mpr hκ_nonneg]
  have hstable :
      SpectralStableEquilibrium uniTriGraph sig (1 / 10)
        (nonmonotoneSubcriticalTail κ) := by
    rw [htail]
    rw [spectralStableEquilibrium_iff]
    native_decide
  exact hno κ hκ_ge hstable

end Legitimacy
