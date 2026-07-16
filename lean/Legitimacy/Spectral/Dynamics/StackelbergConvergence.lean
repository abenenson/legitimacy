/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Dynamics.Stackelberg

/-!
  Stackelberg convergence at unbounded capability.

  The current spectral layer formalizes exploitability through `spViolation`
  and its exact threshold `C_star`, but does not encode a repeated
  governance-game equilibrium object. This module therefore states the
  strongest limit theorem available in the present API: under the spectral
  surrogate, a graph retains stable equilibria along arbitrarily large
  capability scales if and only if its consistency vulnerability vanishes.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

variable {n : Nat}

/-- Spectral stability at capability `κ`: the manipulator can target the scale
    `δ / κ`, but no perturbation of that size is realizable. This is the
    spectral surrogate for a Stackelberg-stable equilibrium at capability
    level `κ`. -/
def SpectralStableEquilibrium
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ κ : ℚ) : Prop :=
  0 < κ ∧ ¬ G.spViolation s (δ / κ)

/-- Zero consistency vulnerability: the graph has zero worst-case perturbation
    under the given signal. -/
def ZeroConsistencyVulnerability
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) : Prop :=
  G.cv s = 0

/-- Deprecated compatibility alias: the corrected name is
`ZeroConsistencyVulnerability`, since the statement is exactly `G.cv s = 0`. -/
def SpectralStrategyproof
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) : Prop :=
  ZeroConsistencyVulnerability G s

/-- Arbitrarily large stable equilibria: above every positive capability floor,
    some larger capability level still admits a stable spectral equilibrium. -/
def HasArbitrarilyLargeStableEquilibria
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) : Prop :=
  ∀ κ₀ : ℚ, 0 < κ₀ →
    ∃ κ : ℚ, κ₀ ≤ κ ∧ SpectralStableEquilibrium G s δ κ

/-- Graph-wide consistency vulnerability is nonnegative. -/
lemma GovGraph.cv_nonneg
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) :
    0 ≤ G.cv s := by
  classical
  let p : Fin n × Fin n := Finset.univ_nonempty.choose
  have hp : p ∈ (Finset.univ : Finset (Fin n × Fin n)) := by
    simp [p]
  exact le_trans (abs_nonneg _) <|
    by
      simpa [GovGraph.cv] using
        (Finset.le_sup'
          (s := Finset.univ)
          (f := fun q : Fin n × Fin n =>
            |G.gov s q.2 - G.govRemoved s q.1 q.2|)
          hp)

/-- Spectral stability means exactly that capability is positive and the
    current perturbation scale lies strictly above the graph-wide CV. -/
lemma spectralStableEquilibrium_iff
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ κ : ℚ) :
    SpectralStableEquilibrium G s δ κ ↔
      0 < κ ∧ G.cv s < δ / κ := by
  constructor
  · rintro ⟨hκ, hstable⟩
    refine ⟨hκ, ?_⟩
    exact lt_of_not_ge (by
      intro hle
      exact hstable ((G.spViolation_iff_le_cv s (δ / κ)).mpr hle))
  · rintro ⟨hκ, hcv⟩
    refine ⟨hκ, ?_⟩
    intro hviol
    exact not_le_of_gt hcv ((G.spViolation_iff_le_cv s (δ / κ)).mp hviol)

/-- If the graph is zero-CV, then every positive capability
    level remains spectrally stable. -/
lemma zeroConsistencyVulnerability_stable_all_capabilities
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ)
    (δ κ : ℚ) (hδ : 0 < δ) (hκ : 0 < κ)
    (hsp : ZeroConsistencyVulnerability G s) :
    SpectralStableEquilibrium G s δ κ := by
  refine ⟨hκ, ?_⟩
  intro hviol
  have hbound : δ / κ ≤ G.cv s :=
    (G.spViolation_iff_le_cv s (δ / κ)).mp hviol
  have hpos : 0 < δ / κ := div_pos hδ hκ
  rw [hsp] at hbound
  exact not_le_of_gt hpos hbound

/-- Deprecated compatibility alias for
`zeroConsistencyVulnerability_stable_all_capabilities`. -/
lemma spectralStrategyproof_stable_all_capabilities
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ)
    (δ κ : ℚ) (hδ : 0 < δ) (hκ : 0 < κ)
    (hsp : SpectralStrategyproof G s) :
    SpectralStableEquilibrium G s δ κ :=
  zeroConsistencyVulnerability_stable_all_capabilities
    G s δ κ hδ hκ hsp

/-- A stable equilibrium at sufficiently large capability forces the graph to
    be `ε`-close to zero consistency vulnerability. -/
theorem stackelberg_convergence_epsilon
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (hδ : 0 < δ) :
    ∀ ε > 0, ∃ κ₀ > 0, ∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
      SpectralStableEquilibrium G s δ κ → G.cv s < ε := by
  intro ε hε
  refine ⟨δ / ε, div_pos hδ hε, ?_⟩
  intro κ hκ hstable
  rcases (spectralStableEquilibrium_iff G s δ κ).mp hstable with ⟨hκpos, hcv_lt⟩
  have hmul : δ ≤ ε * κ := by
    simpa [mul_comm] using (div_le_iff₀ hε).mp hκ
  have hbound : δ / κ ≤ ε := by
    exact (div_le_iff₀ hκpos).mpr (by simpa [mul_comm] using hmul)
  exact lt_of_lt_of_le hcv_lt hbound

/-- Positive spectral vulnerability eventually destroys all spectral stable
    equilibria once capability crosses the exact threshold `C_star`. -/
theorem eventually_no_stable_equilibrium_of_positive_cv
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (hδ : 0 < δ) (hcv : 0 < G.cv s) :
    ∃ κ₀ > 0, ∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
      ¬ SpectralStableEquilibrium G s δ κ := by
  refine ⟨C_star G s δ, div_pos hδ hcv, ?_⟩
  intro κ hκ hstable
  exact hstable.2 ((C_star_exists G s δ hδ hcv).2 κ hκ)

/-- Any positive-CV graph eventually loses all spectral stable
    equilibria at high capability. -/
theorem eventually_no_stable_equilibrium_of_positive_consistency_vulnerability
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (hδ : 0 < δ) (hsp : ¬ ZeroConsistencyVulnerability G s) :
    ∃ κ₀ > 0, ∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
      ¬ SpectralStableEquilibrium G s δ κ := by
  have hcv_ne : G.cv s ≠ 0 := by
    simpa [ZeroConsistencyVulnerability] using hsp
  have hcv : 0 < G.cv s :=
    lt_of_le_of_ne (G.cv_nonneg s) (Ne.symm hcv_ne)
  exact eventually_no_stable_equilibrium_of_positive_cv G s δ hδ hcv

/-- Deprecated compatibility alias for
`eventually_no_stable_equilibrium_of_positive_consistency_vulnerability`. -/
theorem eventually_no_stable_equilibrium_of_not_strategyproof
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (hδ : 0 < δ) (hsp : ¬ SpectralStrategyproof G s) :
    ∃ κ₀ > 0, ∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
      ¬ SpectralStableEquilibrium G s δ κ :=
  eventually_no_stable_equilibrium_of_positive_consistency_vulnerability
    G s δ hδ hsp

/-- Zero-CV graphs retain stable equilibria along arbitrarily large
    capability scales. -/
theorem zeroConsistencyVulnerability_has_arbitrarily_large_stable_equilibria
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (hδ : 0 < δ) (hsp : ZeroConsistencyVulnerability G s) :
    HasArbitrarilyLargeStableEquilibria G s δ := by
  intro κ₀ hκ₀
  refine ⟨κ₀, le_rfl, ?_⟩
  exact zeroConsistencyVulnerability_stable_all_capabilities G s δ κ₀ hδ hκ₀ hsp

/-- Deprecated compatibility alias for
`zeroConsistencyVulnerability_has_arbitrarily_large_stable_equilibria`. -/
theorem spectralStrategyproof_has_arbitrarily_large_stable_equilibria
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (hδ : 0 < δ) (hsp : SpectralStrategyproof G s) :
    HasArbitrarilyLargeStableEquilibria G s δ :=
  zeroConsistencyVulnerability_has_arbitrarily_large_stable_equilibria
    G s δ hδ hsp

/-- **Stackelberg convergence theorem at the spectral capability limit.**
    In the currently formalized spectral surrogate, the mechanisms retaining
    stable equilibria along arbitrarily large capability scales are exactly the
    zero-CV ones. -/
theorem stackelberg_convergence_limit_iff_zero_consistency_vulnerability
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (hδ : 0 < δ) :
    HasArbitrarilyLargeStableEquilibria G s δ ↔
      ZeroConsistencyVulnerability G s := by
  constructor
  · intro hstable
    by_contra hsp
    obtain ⟨κ₀, hκ₀, hno⟩ :=
      eventually_no_stable_equilibrium_of_positive_consistency_vulnerability G s δ hδ hsp
    obtain ⟨κ, hκ, hstableκ⟩ := hstable κ₀ hκ₀
    exact hno hκ hstableκ
  · intro hsp
    exact zeroConsistencyVulnerability_has_arbitrarily_large_stable_equilibria G s δ hδ hsp

/-- Deprecated compatibility alias for
`stackelberg_convergence_limit_iff_zero_consistency_vulnerability`. -/
theorem stackelberg_convergence_limit_is_strategyproof
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (hδ : 0 < δ) :
    HasArbitrarilyLargeStableEquilibria G s δ ↔
      SpectralStrategyproof G s :=
  stackelberg_convergence_limit_iff_zero_consistency_vulnerability
    G s δ hδ

end Legitimacy
