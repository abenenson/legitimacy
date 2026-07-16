/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Dynamics.StackelbergConvergence

/-!
# Legitimacy.Spectral.Dynamics.Bifurcation

Purely spectral bifurcation packaging for the current API.

The present development supports one honest finite-capability bifurcation:
below the exact reciprocal threshold `C_star`, a graph with positive
consistency vulnerability admits a spectral stable equilibrium at capability
`κ`; at and above that threshold, the equilibrium disappears. Capacity is
packaged orthogonally as the structural side condition certifying `cv ≤ δ`.

This file deliberately does **not** tie the bifurcation directly to kernel
existentials. In the current API, `IsLegitimacyKernel` does not constrain the
spectral fields, and `DiagnosticAxiomIff` exposes accessors plus normalization
facts rather than diagnostic-to-axiom bridges. The conditional kernel-side
attachment point lives in a separate module to keep the spectral layer acyclic.
-/

set_option autoImplicit false

namespace Legitimacy

variable {n : Nat}

instance instDecidableCapacity
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) :
    Decidable (G.capacity s δ) := by
  unfold GovGraph.capacity
  infer_instance

instance instDecidableSpViolation
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) :
    Decidable (G.spViolation s δ) := by
  unfold GovGraph.spViolation
  infer_instance

instance instDecidableStable
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ κ : ℚ) :
    Decidable (SpectralStableEquilibrium G s δ κ) := by
  unfold SpectralStableEquilibrium
  infer_instance

/-- Finite-capability "below-boundary" regime: the graph passes the structural
capacity test at tolerance `δ`, has positive spectral vulnerability, and the
chosen capability `κ` lies strictly below the exact critical threshold `C_star`.
-/
structure BelowBifurcationBoundary
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ κ : ℚ) : Prop where
  capacity_admits : G.capacity s δ
  positive_cv : 0 < G.cv s
  positive_capability : 0 < κ
  subcritical : κ < C_star G s δ

/-- Pure spectral bifurcation theorem: the "below-boundary" package is exactly
capacity admissibility together with a positive-CV spectral stable equilibrium
at capability `κ`. -/
theorem bifurcation_iff_spectral
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ κ : ℚ)
    (hδ : 0 < δ) :
    BelowBifurcationBoundary G s δ κ ↔
      G.capacity s δ ∧ 0 < G.cv s ∧ SpectralStableEquilibrium G s δ κ := by
  constructor
  · intro hbelow
    refine ⟨hbelow.capacity_admits, hbelow.positive_cv, ?_⟩
    refine ⟨hbelow.positive_capability, ?_⟩
    exact (C_star_exists G s δ hδ hbelow.positive_cv).1 κ
      hbelow.positive_capability hbelow.subcritical
  · rintro ⟨hcap, hcv, hstable⟩
    refine ⟨hcap, hcv, hstable.1, ?_⟩
    by_contra hnot
    have hle : C_star G s δ ≤ κ := le_of_not_gt hnot
    have hviol := (C_star_exists G s δ hδ hcv).2 κ hle
    exact hstable.2 hviol

/-- Positive spectral vulnerability eventually ejects every capability level
from the below-boundary regime, because stable equilibria disappear once `κ`
crosses the exact threshold. -/
theorem eventually_not_below_bifurcation_boundary_of_positive_cv
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (hδ : 0 < δ) (hcv : 0 < G.cv s) :
    ∃ κ₀ > 0, ∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
      ¬ BelowBifurcationBoundary G s δ κ := by
  obtain ⟨κ₀, hκ₀, hno⟩ :=
    eventually_no_stable_equilibrium_of_positive_cv G s δ hδ hcv
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ hbelow
  have hstable :=
    (bifurcation_iff_spectral G s δ κ hδ).mp hbelow |>.2.2
  exact hno hκ hstable

/-- Re-export of the asymptotic spectral bifurcation already established in the
Stackelberg convergence file: arbitrarily large stable equilibria are exactly
the strategyproof case. -/
theorem stackelberg_limit_bifurcation
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (hδ : 0 < δ) :
    HasArbitrarilyLargeStableEquilibria G s δ ↔
      ZeroConsistencyVulnerability G s :=
  stackelberg_convergence_limit_iff_zero_consistency_vulnerability G s δ hδ

/-- Native-decision witness on the existing 5-node lattice at one concrete
parameter choice. At `(δ, κ) = (80, 1)`, the two fragile path/bottleneck
graphs lie above the boundary while `uniK5`, `asymK5`, and `wheel5` remain
below it. -/
theorem concrete_bifurcation_n5 :
    BelowBifurcationBoundary uniK5 sig5 80 1 ∧
    BelowBifurcationBoundary asymK5 sig5 80 1 ∧
    ¬ BelowBifurcationBoundary nearPath5 sig5 80 1 ∧
    BelowBifurcationBoundary wheel5 sig5 80 1 ∧
    ¬ BelowBifurcationBoundary bottleneck5 sig5 80 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hδ : 0 < (80 : ℚ) := by norm_num
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    exact (bifurcation_iff_spectral uniK5 sig5 80 1 hδ).mpr (by native_decide)
  · have hδ : 0 < (80 : ℚ) := by norm_num
    exact (bifurcation_iff_spectral asymK5 sig5 80 1 hδ).mpr (by native_decide)
  · have hδ : 0 < (80 : ℚ) := by norm_num
    intro hbelow
    exact (by native_decide :
      ¬ (nearPath5.capacity sig5 80 ∧ 0 < nearPath5.cv sig5 ∧
        SpectralStableEquilibrium nearPath5 sig5 80 1))
      ((bifurcation_iff_spectral nearPath5 sig5 80 1 hδ).mp hbelow)
  · have hδ : 0 < (80 : ℚ) := by norm_num
    exact (bifurcation_iff_spectral wheel5 sig5 80 1 hδ).mpr (by native_decide)
  · have hδ : 0 < (80 : ℚ) := by norm_num
    intro hbelow
    exact (by native_decide :
      ¬ (bottleneck5.capacity sig5 80 ∧ 0 < bottleneck5.cv sig5 ∧
        SpectralStableEquilibrium bottleneck5 sig5 80 1))
      ((bifurcation_iff_spectral bottleneck5 sig5 80 1 hδ).mp hbelow)

end Legitimacy
