/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Core.Localizability

/-!
  Capacity bounds for spectral governance.

  This module packages the structural capacity predicate together with the
  graph-wide CV bounds it implies, including the concrete five-graph capacity
  corollaries and the operational saturation contrapositive.

  ## Shannon correspondence

  The governance-graph quantity `capacity(G, s)` is the combinatorial analog of
  Shannon channel capacity. A companion repository,
  `abenenson/channel-capacity`, proves the corresponding measure-theoretic
  uniqueness theorem for capacity-achieving priors of Markov kernels under an
  injective-prior-pushforward non-degeneracy condition. The graph-theoretic
  bound here and the measure-theoretic uniqueness there describe the same
  phenomenon from different directions: structural asymmetry both bounds signal
  absorption and constrains the capacity-achieving prior.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {n : Nat}

/-- Capacity at tolerance `ε`: the signal-range budget induced by the graph's
    maximum degree is absorbable by the worst residual degree after a single
    removal. This is the structural condition used to certify `cv ≤ ε`. -/
def GovGraph.capacity (G : GovGraph F n) [NeZero n] (s : Fin n → F)
    (ε : F) : Prop :=
  signalRange s * G.maxDeg ≤ ε * G.minRemovedDeg

/-- Value-level structural capacity budget corresponding to the predicate
    `GovGraph.capacity`. This is the exact rational quantity mirrored by the
    Rust `capacity_bound` implementation. -/
def GovGraph.capacityBound (G : GovGraph F n) [NeZero n] (s : Fin n → F) : F :=
  signalRange s * G.maxDeg / G.minRemovedDeg

/-- Graph-wide CV bound obtained by lifting the pointwise perturbation estimate
    through the supremum over removal/observer pairs. -/
lemma GovGraph.cv_mul_minRemovedDeg_le_signalRange_mul_maxDeg
    (G : GovGraph F n) [NeZero n] (s : Fin n → F)
    (hmin : 0 < G.minRemovedDeg) :
    G.cv s * G.minRemovedDeg ≤ signalRange s * G.maxDeg := by
  have hcv :
      G.cv s ≤ signalRange s * G.maxDeg / G.minRemovedDeg := by
    apply Finset.sup'_le
    intro p _
    rcases p with ⟨k, i⟩
    have hD : 0 < G.deg i := G.deg_pos_of_minRemovedDeg_pos hmin i
    have hD' : 0 < G.degRemoved k i := G.degRemoved_pos_of_minRemovedDeg_pos hmin k i
    have hmin_le_deg : G.minRemovedDeg ≤ G.deg i := by
      have h := G.minRemovedDeg_le_degRemoved i i
      simpa [G.degRemoved_self i] using h
    have hpoint :=
      G.perturb_deg_le_signalRange_mul_maxDeg_all s (signalRange s)
        (signalRange_nonneg s) (le_signalRange s) k i hD hD'
    have hmul :
        |G.gov s i - G.govRemoved s k i| * G.minRemovedDeg ≤
          signalRange s * G.maxDeg := by
      calc |G.gov s i - G.govRemoved s k i| * G.minRemovedDeg
          ≤ |G.gov s i - G.govRemoved s k i| * G.deg i :=
            mul_le_mul_of_nonneg_left hmin_le_deg (abs_nonneg _)
        _ ≤ signalRange s * G.maxDeg := hpoint
    exact (le_div_iff₀ hmin).mpr hmul
  exact (le_div_iff₀ hmin).mp hcv

/-- CV is controlled by the signal range, the maximum degree, and the minimum
    residual degree after a single-node removal. -/
lemma GovGraph.cv_le_signalRange_mul_maxDeg_div_minRemovedDeg
    (G : GovGraph F n) [NeZero n] (s : Fin n → F)
    (hmin : 0 < G.minRemovedDeg) :
    G.cv s ≤ signalRange s * G.maxDeg / G.minRemovedDeg :=
  (le_div_iff₀ hmin).mpr (G.cv_mul_minRemovedDeg_le_signalRange_mul_maxDeg s hmin)

/-- Capacity theorem: the structural capacity condition implies the graph-wide
    CV tolerance bound. -/
lemma cv_capacity_bound
    (G : GovGraph F n) [NeZero n]
    (s : Fin n → F) (ε : F) (_hε : 0 < ε)
    (hmin : 0 < G.minRemovedDeg)
    (hcap : G.capacity s ε) :
    G.cv s ≤ ε := by
  have hstruct := G.cv_mul_minRemovedDeg_le_signalRange_mul_maxDeg s hmin
  have hbudget : G.cv s * G.minRemovedDeg ≤ ε * G.minRemovedDeg :=
    le_trans hstruct hcap
  exact le_of_mul_le_mul_right hbudget hmin

/-- Concrete CV bounds for the five weighted 3-node governance graphs, stated
    in capacity language. -/
lemma concrete_capacity_bounds :
    uniTriGraph.cv sig ≤ 1 ∧
    asymTriGraph.cv sig ≤ 4 / 3 ∧
    nearPathGraph.cv sig ≤ 1 ∧
      stronglyConnectedGraph.cv sig ≤ 1 ∧
      bottleneckGraph.cv sig ≤ 1 := by
  exact concrete_cv_spectral_bound

/-- Exact structural capacity values for the five weighted 3-node governance
    graphs under `sig`. -/
theorem concrete_capacity_exact_values :
    uniTriGraph.capacityBound sig = 4 ∧
    asymTriGraph.capacityBound sig = 6 ∧
    nearPathGraph.capacityBound sig = 200 ∧
    stronglyConnectedGraph.capacityBound sig = 4 ∧
    bottleneckGraph.capacityBound sig = 40000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  all_goals native_decide

/-- Operational contrapositive of the capacity theorem: once observed CV
    exceeds the tolerance, the structural capacity inequality cannot hold. -/
lemma capacity_saturation
    (G : GovGraph F n) [NeZero n]
    (s : Fin n → F) (ε : F) (hε : 0 < ε)
    (hmin : 0 < G.minRemovedDeg)
    (hcv : ε < G.cv s) :
    ¬ G.capacity s ε := by
  intro hcap
  have hbound := cv_capacity_bound G s ε hε hmin hcap
  linarith

end Legitimacy
