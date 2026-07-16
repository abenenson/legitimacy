/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Core.PerturbationBounds
import Legitimacy.Spectral.Core.ConcreteGraphs

/-!
  Consistency-vulnerability and localizability summaries.

  This module collects the graph-wide and per-node CV definitions, the induced
  localizability statistic, and the concrete five-graph localizability
  calculations used later by the capacity and critical-capability layers.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {n : Nat}

/-- Consistency vulnerability: max perturbation over all removals. -/
def GovGraph.cv (G : GovGraph F n) [NeZero n] (s : Fin n → F) : F :=
  Finset.sup' (Finset.univ (α := Fin n × Fin n))
    (Finset.univ_nonempty)
    (fun p => |G.gov s p.2 - G.govRemoved s p.1 p.2|)

/-- Cook's (1977) leverage factor for the governance map `gov = D^{-1} W`. -/
noncomputable def GovGraph.leverageFactor {n : Nat} [NeZero n]
    (G : GovGraph F n) (i k : Fin n) : F :=
  G.W i k / G.deg i

/-- Cook's (1977) leave-one-out residual for the governance map. -/
noncomputable def GovGraph.residual {n : Nat} [NeZero n]
    (G : GovGraph F n) (s : Fin n → F) (i k : Fin n) : F :=
  s k - G.govRemoved s k i

/-- Per-node consistency vulnerability: max perturbation induced by removing
    the specified node. -/
def GovGraph.cv_i (G : GovGraph F n) [NeZero n] (s : Fin n → F)
    (k : Fin n) : F :=
  Finset.sup' Finset.univ
    (Finset.univ_nonempty)
    (fun i => |G.gov s i - G.govRemoved s k i|)

/-- Localizability of inconsistency under signal `s`, computed as
    `1 - min_i CV_i / max_j |f(j)|` over rational governance evaluations. -/
def GovGraph.localizability
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) : ℚ :=
  1 - (Finset.inf' Finset.univ
      (Finset.univ_nonempty)
      (fun i => G.cv_i s i)) /
      (Finset.sup' Finset.univ
        (Finset.univ_nonempty)
        (fun j => |G.gov s j|))

/-- Cook's (1977) gross-error sensitivity identity for the governance map.

    `cv(G, s)` equals the sup over (observer, removed-node) pairs of
    `leverageFactor · |residual|` — i.e., `cv` is Hampel's (1974) influence
    function sup-norm of the governance map under single-node deletion.

    The shipped `probes/scripts/normalized_laplacian_probe.py` reconstruction
    tracks the classical identification with Cook 1977, Hampel 1974,
    Belsley-Kuh-Welsch 1980 (DFFITS), and Nissim-Raskhodnikova-Smith 2007
    (DP local sensitivity). -/
theorem GovGraph.cv_eq_grossErrorSensitivity
    (G : GovGraph F n) [NeZero n] (s : Fin n → F)
    (hD : ∀ i, G.deg i ≠ 0) (hD' : ∀ k i, G.degRemoved k i ≠ 0) :
    G.cv s = Finset.sup' (Finset.univ (α := Fin n × Fin n))
      Finset.univ_nonempty
      (fun p => |G.leverageFactor p.2 p.1 * G.residual s p.2 p.1|) := by
  unfold GovGraph.cv
  apply Finset.sup'_congr _ rfl
  intro p _
  rw [G.leverage_residual_factorization s p.1 p.2 (hD _) (hD' _ _)]
  unfold GovGraph.leverageFactor GovGraph.residual
  congr 1
  field_simp [hD p.2]

/-- Each per-removal perturbation is bounded by the graph-wide CV. -/
lemma GovGraph.perturb_le_cv
    (G : GovGraph F n) [NeZero n] (s : Fin n → F) (k i : Fin n) :
    |G.gov s i - G.govRemoved s k i| ≤ G.cv s := by
  exact Finset.le_sup' (f := fun p : Fin n × Fin n => |G.gov s p.2 - G.govRemoved s p.1 p.2|)
    (by simp : (k, i) ∈ Finset.univ)

/-- Removing any fixed node yields a per-node CV bounded by the graph-wide CV. -/
lemma GovGraph.cv_i_le_cv
    (G : GovGraph F n) [NeZero n] (s : Fin n → F) (k : Fin n) :
    G.cv_i s k ≤ G.cv s := by
  apply Finset.sup'_le
  intro i _
  exact G.perturb_le_cv s k i

/-- Exact CV values for the five concrete graphs under `sig`. -/
theorem concrete_cv_values :
    uniTriGraph.cv sig = 1 ∧
    asymTriGraph.cv sig = 4 / 3 ∧
    nearPathGraph.cv sig = 1 ∧
    stronglyConnectedGraph.cv sig = 1 ∧
    bottleneckGraph.cv sig = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  all_goals native_decide

/-- Each concrete graph has positive consistency vulnerability under `sig`. -/
lemma concrete_cv_pos :
    0 < uniTriGraph.cv sig ∧
    0 < asymTriGraph.cv sig ∧
    0 < nearPathGraph.cv sig ∧
    0 < stronglyConnectedGraph.cv sig ∧
    0 < bottleneckGraph.cv sig := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  all_goals native_decide

/-- Exact localizability values for the five concrete graphs under `sig`. -/
lemma concrete_localizability_values :
    uniTriGraph.localizability sig = 4 / 5 ∧
    asymTriGraph.localizability sig = 11 / 15 ∧
    nearPathGraph.localizability sig = 53 / 103 ∧
    stronglyConnectedGraph.localizability sig = 4 / 5 ∧
    bottleneckGraph.localizability sig = 10003 / 20003 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  all_goals native_decide

/-- Concrete CV upper bounds for the five weighted 3-node governance graphs. -/
theorem concrete_cv_spectral_bound :
    uniTriGraph.cv sig ≤ 1 ∧
    asymTriGraph.cv sig ≤ 4 / 3 ∧
    nearPathGraph.cv sig ≤ 1 ∧
    stronglyConnectedGraph.cv sig ≤ 1 ∧
    bottleneckGraph.cv sig ≤ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  all_goals native_decide

/-- **Five-graph verification of the CV × L ≥ 1/2 tradeoff.**
    Demonstrates the legitimacy uncertainty principle on five concrete
    weighted 3-node governance graphs. -/
theorem cv_localizability_tradeoff_concrete :
    (uniTriGraph.cv sig) * (uniTriGraph.localizability sig) ≥ 1 / 2 ∧
    (asymTriGraph.cv sig) * (asymTriGraph.localizability sig) ≥ 1 / 2 ∧
    (nearPathGraph.cv sig) * (nearPathGraph.localizability sig) ≥ 1 / 2 ∧
    (stronglyConnectedGraph.cv sig) * (stronglyConnectedGraph.localizability sig) ≥ 1 / 2 ∧
    (bottleneckGraph.cv sig) * (bottleneckGraph.localizability sig) ≥ 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  all_goals native_decide

end Legitimacy
