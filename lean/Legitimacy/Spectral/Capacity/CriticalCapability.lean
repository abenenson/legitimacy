/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Capacity.Structural

/-!
  Critical-capability thresholds for spectral governance.

  This module packages the exploitability predicate `spViolation`, the exact
  reciprocal threshold `C_star`, its concrete five-graph values, and the
  phase-transition bounds linking `C_star` to the spectral-gap estimates.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {n : Nat}

/-- A quantitative strategyproofness violation occurs when some removal/observer
    pair induces a governance perturbation of magnitude at least `δ`. This is
    the spectral layer's concrete exploitability notion. -/
def GovGraph.spViolation
    (G : GovGraph F n) [NeZero n] (s : Fin n → F) (δ : F) : Prop :=
  ∃ p : Fin n × Fin n, δ ≤ |G.gov s p.2 - G.govRemoved s p.1 p.2|

/-- The exact perturbation threshold is the graph-wide consistency
    vulnerability. -/
def epsilon_star (G : GovGraph F n) [NeZero n] (s : Fin n → F) : F :=
  G.cv s

/-- Reciprocal critical capability threshold: capability `C` corresponds to the
    ability to target perturbations down to scale `δ / C`. -/
def C_star (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) : ℚ :=
  δ / G.cv s

/-- Strategyproofness violation at threshold `δ` is equivalent to `δ` lying
    below the graph-wide CV. -/
lemma GovGraph.spViolation_iff_le_cv
    (G : GovGraph F n) [NeZero n] (s : Fin n → F) (δ : F) :
    G.spViolation s δ ↔ δ ≤ G.cv s := by
  unfold GovGraph.spViolation GovGraph.cv
  simp [Finset.le_sup'_iff]

/-- The spectral-layer perturbation threshold exhibits a sharp reciprocal phase
    transition once the graph has a nonzero worst-case perturbation. Below
    `C_star`, perturbations of scale `δ / C` are unreachable; at or above
    `C_star`, some perturbation of that scale exists. -/
theorem C_star_exists
    (G : GovGraph ℚ n) [NeZero n]
    (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hcv : 0 < G.cv s) :
    (∀ C : ℚ, 0 < C → C < C_star G s δ → ¬ G.spViolation s (δ / C)) ∧
    (∀ C : ℚ, C_star G s δ ≤ C → G.spViolation s (δ / C)) := by
  constructor
  · intro C hC hlt
    have hmul : C * G.cv s < δ := by
      exact (lt_div_iff₀ hcv).mp (by simpa [C_star] using hlt)
    have hbound : G.cv s < δ / C := by
      exact (lt_div_iff₀ hC).mpr (by simpa [mul_comm] using hmul)
    intro hviol
    exact (not_le_of_gt hbound) ((G.spViolation_iff_le_cv s (δ / C)).mp hviol)
  · intro C hle
    have hCstar_pos : 0 < C_star G s δ := by
      simpa [C_star] using div_pos hδ hcv
    have hC : 0 < C := lt_of_lt_of_le hCstar_pos hle
    have hmul : δ ≤ C * G.cv s := by
      exact (div_le_iff₀ hcv).mp (by simpa [C_star] using hle)
    have hbound : δ / C ≤ G.cv s := by
      exact (div_le_iff₀ hC).mpr (by simpa [mul_comm] using hmul)
    exact (G.spViolation_iff_le_cv s (δ / C)).mpr hbound

/-- Sequential capability budgets compose additively below `C_star`.

    This is the algebraic differential-privacy reading of the critical
    capability threshold: with `cv(G, s)` serving as local sensitivity in the
    sense of Nissim--Raskhodnikova--Smith (2007), `k` sequential releases whose
    individual capability budgets are each strictly below `C_star / k` have
    total composed capability still strictly below `C_star`. -/
theorem C_star_sequential_capability_sum_lt
    (G : GovGraph ℚ n) [NeZero n]
    (s : Fin n → ℚ) (δ : ℚ)
    (k : Nat) [NeZero k] (capability : Fin k → ℚ)
    (hcap :
      ∀ i : Fin k, capability i < C_star G s δ / (k : ℚ)) :
    (∑ i : Fin k, capability i) < C_star G s δ := by
  have hsum :
      (∑ i : Fin k, capability i) <
        ∑ _i : Fin k, C_star G s δ / (k : ℚ) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact le_of_lt (hcap i)
    · exact ⟨0, by simp, hcap 0⟩
  have hk : ((k : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (NeZero.ne k)
  have hconst : (∑ _i : Fin k, C_star G s δ / (k : ℚ)) = C_star G s δ := by
    simp
    exact mul_div_cancel₀ (C_star G s δ) hk
  simpa [hconst] using hsum

/-- DP-composition form of the subcritical phase transition: once the
    sequentially composed capability budget is positive, the additive
    composition theorem above feeds directly into the existing `C_star`
    no-violation side. -/
theorem C_star_sequential_capability_preserves_subcritical_surface
    (G : GovGraph ℚ n) [NeZero n]
    (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hcv : 0 < G.cv s)
    (k : Nat) [NeZero k] (capability : Fin k → ℚ)
    (hcap :
      ∀ i : Fin k, capability i < C_star G s δ / (k : ℚ))
    (htotal :
      0 < ∑ i : Fin k, capability i) :
    ¬ G.spViolation s (δ / ∑ i : Fin k, capability i) := by
  exact (C_star_exists G s δ hδ hcv).1
    (∑ i : Fin k, capability i) htotal
    (C_star_sequential_capability_sum_lt G s δ k capability hcap)

/-- A maximizing removal/observer pair witnesses the spectral CV bound in cast
    form, avoiding any need to push `Rat.cast` through the supremum directly. -/
theorem GovGraph.cv_spectral_bound
    (G : GovGraph ℚ n) [NeZero n]
    (hn : 2 ≤ n)
    (s : Fin n → ℚ)
    (hmin : 0 < G.minRemovedDeg)
    (hsg : 0 < G.spectralGap hn)
    (hsg_le : ∀ i : Fin n, G.spectralGap hn ≤ Rat.cast (G.deg i)) :
    (Rat.cast (G.cv s) : ℝ) ≤
      Rat.cast (signalRange s) * Rat.cast G.maxDeg / G.spectralGap hn := by
  classical
  obtain ⟨p, _, hp⟩ :=
    Finset.exists_mem_eq_sup'
      (s := Finset.univ)
      (H := Finset.univ_nonempty)
      (f := fun p : Fin n × Fin n => |G.gov s p.2 - G.govRemoved s p.1 p.2|)
  rcases p with ⟨k, i⟩
  have hD : 0 < G.deg i := G.deg_pos_of_minRemovedDeg_pos hmin i
  have hD' : 0 < G.degRemoved k i := G.degRemoved_pos_of_minRemovedDeg_pos hmin k i
  have hpoint :=
    G.perturbation_spectral_bound_pointwise
      hn s (signalRange s) (signalRange_nonneg s) (le_signalRange s)
      hsg k i hD hD' (hsg_le i)
  have hpR : (Rat.cast (G.cv s) : ℝ) =
      Rat.cast |G.gov s i - G.govRemoved s k i| := by
    exact_mod_cast hp
  calc
    (Rat.cast (G.cv s) : ℝ)
        = Rat.cast |G.gov s i - G.govRemoved s k i| := hpR
    _ ≤ Rat.cast (signalRange s) * Rat.cast G.maxDeg / G.spectralGap hn := hpoint

/-- The exact critical capability is bounded below by an explicit spectral
    quantity: larger spectral gap certifies a larger safe capability window. -/
theorem C_star_spectral_bound
    (G : GovGraph ℚ n) [NeZero n]
    (hn : 2 ≤ n)
    (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hcv : 0 < G.cv s)
    (hmin : 0 < G.minRemovedDeg)
    (hsg : 0 < G.spectralGap hn)
    (hsg_le : ∀ i : Fin n, G.spectralGap hn ≤ Rat.cast (G.deg i)) :
    (Rat.cast δ : ℝ) /
        (Rat.cast (signalRange s) * Rat.cast G.maxDeg / G.spectralGap hn) ≤
      Rat.cast (C_star G s δ) := by
  have hcv_bound := G.cv_spectral_bound hn s hmin hsg hsg_le
  have hδ_nonneg : (0 : ℝ) ≤ Rat.cast δ := by exact_mod_cast hδ.le
  have hcvR_pos : (0 : ℝ) < Rat.cast (G.cv s) := by exact_mod_cast hcv
  have hstruct_pos :
      0 < Rat.cast (signalRange s) * Rat.cast G.maxDeg / G.spectralGap hn :=
    lt_of_lt_of_le hcvR_pos hcv_bound
  have hdiv :
      (Rat.cast δ : ℝ) /
          (Rat.cast (signalRange s) * Rat.cast G.maxDeg / G.spectralGap hn) ≤
        Rat.cast δ / Rat.cast (G.cv s) :=
    div_le_div_of_nonneg_left hδ_nonneg hcvR_pos hcv_bound
  simpa [C_star] using hdiv

/-- Paper-facing expander-style packaging of `C_star_spectral_bound`: the
    critical capability is bounded below by an explicit linear function of the
    governance graph spectral gap `λ₂ = spectralGap`. -/
theorem governance_graph_C_star_expander_bound
    (G : GovGraph ℚ n) [NeZero n]
    (hn : 2 ≤ n)
    (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hcv : 0 < G.cv s)
    (hmin : 0 < G.minRemovedDeg)
    (hsg : 0 < G.spectralGap hn)
    (hsg_le : ∀ i : Fin n, G.spectralGap hn ≤ Rat.cast (G.deg i)) :
    (δ : ℝ) * G.spectralGap hn / (((signalRange s : ℚ) : ℝ) * (G.maxDeg : ℝ)) ≤
      (C_star G s δ : ℝ) := by
  have hbase := C_star_spectral_bound G hn s δ hδ hcv hmin hsg hsg_le
  have hbase' :
      (δ : ℝ) / ((((signalRange s : ℚ) : ℝ) * (G.maxDeg : ℝ)) / G.spectralGap hn) ≤
        (C_star G s δ : ℝ) := by
    simpa using hbase
  have hcv_bound := G.cv_spectral_bound hn s hmin hsg hsg_le
  have hcvR_pos : (0 : ℝ) < (G.cv s : ℝ) := by exact_mod_cast hcv
  have hquot_pos :
      (0 : ℝ) < (((signalRange s : ℚ) : ℝ) * (G.maxDeg : ℝ)) / G.spectralGap hn :=
    lt_of_lt_of_le hcvR_pos hcv_bound
  have hnum_pos : (0 : ℝ) < ((signalRange s : ℚ) : ℝ) * (G.maxDeg : ℝ) := by
    exact (div_pos_iff_of_pos_right hsg).mp hquot_pos
  have hnum_ne : ((((signalRange s : ℚ) : ℝ) * (G.maxDeg : ℝ)) : ℝ) ≠ 0 := ne_of_gt hnum_pos
  have hsg_ne : G.spectralGap hn ≠ 0 := ne_of_gt hsg
  calc
    (δ : ℝ) * G.spectralGap hn / (((signalRange s : ℚ) : ℝ) * (G.maxDeg : ℝ))
      = (δ : ℝ) / ((((signalRange s : ℚ) : ℝ) * (G.maxDeg : ℝ)) / G.spectralGap hn) := by
            field_simp [hnum_ne, hsg_ne]
    _ ≤ (C_star G s δ : ℝ) := hbase'

/-- Exact five-graph critical capability values for `sig` at tolerance `1/10`.
    Under the present normalized weighted-average semantics, four of the five
    graphs tie exactly and the asymmetric triangle is the unique fragile case. -/
lemma concrete_C_star_values :
    C_star uniTriGraph sig (1 / 10) = 1 / 10 ∧
    C_star asymTriGraph sig (1 / 10) = 3 / 40 ∧
    C_star nearPathGraph sig (1 / 10) = 1 / 10 ∧
    C_star stronglyConnectedGraph sig (1 / 10) = 1 / 10 ∧
    C_star bottleneckGraph sig (1 / 10) = 1 / 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  all_goals native_decide

/-- Operational phase transition package: the exact threshold is `C_star`,
    and the spectral theorem supplies a graph-structural lower bound on it. -/
theorem phase_transition_at_C_star
    (G : GovGraph ℚ n) [NeZero n]
    (hn : 2 ≤ n)
    (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hcv : 0 < G.cv s)
    (hmin : 0 < G.minRemovedDeg)
    (hsg : 0 < G.spectralGap hn)
    (hsg_le : ∀ i : Fin n, G.spectralGap hn ≤ Rat.cast (G.deg i)) :
    (Rat.cast δ : ℝ) /
        (Rat.cast (signalRange s) * Rat.cast G.maxDeg / G.spectralGap hn) ≤
      Rat.cast (C_star G s δ) ∧
    (∀ C : ℚ, 0 < C → C < C_star G s δ → ¬ G.spViolation s (δ / C)) ∧
    (∀ C : ℚ, C_star G s δ ≤ C → G.spViolation s (δ / C)) := by
  refine ⟨C_star_spectral_bound G hn s δ hδ hcv hmin hsg hsg_le, ?_, ?_⟩
  · exact (C_star_exists G s δ hδ hcv).1
  · exact (C_star_exists G s δ hδ hcv).2

end Legitimacy
