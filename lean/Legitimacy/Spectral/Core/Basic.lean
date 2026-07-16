/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Graph
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
  Basic spectral governance primitives.

  This module contains the shared definitions and low-level facts used by the
  spectral result files: the `GovGraph` aliases, degree and Laplacian
  constructions, consistency-vulnerability summaries, signal-range helpers,
  and the `ℚ`-to-`ℝ` spectral-gap interface.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

-- =====================================================================
-- S 1. Governance graph over a linearly-ordered field
-- =====================================================================

/-- Backward-compatible alias used by the spectral API.
    `GraphN` is the single canonical weighted graph type. -/
abbrev GovGraph (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (n : Nat) := GraphN F n

/-- Every `GovGraph` is the canonical `GraphN` weighted graph. -/
abbrev GovGraph.toWeightedGraph {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {n : ℕ}
    (G : GovGraph F n) : WeightedGraph F n :=
  GraphN.toWeightedGraph G

/-- Backward-compatible alias: `GovGraphQ n` is `GraphNQ n`. -/
abbrev GovGraphQ (n : ℕ) := GraphNQ n

-- =====================================================================
-- S 2. Degree, Laplacian, and governance function (algebraic layer)
-- =====================================================================

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {n : Nat}

/-- Matrix view of the canonical weighted graph. -/
abbrev GovGraph.W (G : GovGraph F n) : Matrix (Fin n) (Fin n) F :=
  G.weights

/-- Symmetry of the canonical weighted graph. -/
lemma GovGraph.symm (G : GovGraph F n) : G.W.IsSymm := by
  change G.Wᵀ = G.W
  ext i j
  simpa [GovGraph.W, Matrix.transpose_apply] using G.weight_symm j i

/-- Non-negativity of the canonical weighted graph. -/
lemma GovGraph.nonneg (G : GovGraph F n) (i j : Fin n) : 0 ≤ G.W i j :=
  G.weight_nonneg i j

/-- Diagonal entries of the canonical weighted graph vanish. -/
lemma GovGraph.no_self (G : GovGraph F n) (i : Fin n) : G.W i i = 0 :=
  G.weight_self_zero i

/-- Weighted degree of node i. -/
def GovGraph.deg (G : GovGraph F n) (i : Fin n) : F :=
  ∑ j : Fin n, G.W i j

/-- Maximum weighted degree across all nodes. -/
def GovGraph.maxDeg (G : GovGraph F n) [NeZero n] : F :=
  Finset.sup' Finset.univ (Finset.univ_nonempty) G.deg

/-- Degree matrix: diagonal with degrees. -/
def GovGraph.degMatrix (G : GovGraph F n) : Matrix (Fin n) (Fin n) F :=
  Matrix.diagonal G.deg

/-- Graph Laplacian: L = D - W. -/
def GovGraph.laplacian (G : GovGraph F n) : Matrix (Fin n) (Fin n) F :=
  G.degMatrix - G.W

/-- Governance decision at node i: weighted average of neighbors' signals. -/
def GovGraph.gov (G : GovGraph F n) (s : Fin n → F) (i : Fin n) : F :=
  (∑ j : Fin n, G.W i j * s j) / G.deg i

/-- Degree of node i after removing node k. -/
def GovGraph.degRemoved (G : GovGraph F n) (k i : Fin n) : F :=
  ∑ j : Fin n, if j = k then 0 else G.W i j

/-- Governance decision at node i after removing node k. -/
def GovGraph.govRemoved (G : GovGraph F n) (s : Fin n → F) (k i : Fin n) : F :=
  (∑ j : Fin n, if j = k then 0 else G.W i j * s j) / G.degRemoved k i

/-- Minimum residual degree across all single-node removals. -/
def GovGraph.minRemovedDeg (G : GovGraph F n) [NeZero n] : F :=
  Finset.inf' (Finset.univ (α := Fin n × Fin n))
    (Finset.univ_nonempty)
    (fun p => G.degRemoved p.1 p.2)

/-- Signal range: max |s(a) - s(b)| over all pairs. -/
def signalRange {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {n : Nat} [NeZero n] (s : Fin n → F) : F :=
  Finset.sup' (Finset.univ (α := Fin n × Fin n))
    (Finset.univ_nonempty)
    (fun p => |s p.1 - s p.2|)

-- =====================================================================
-- S 3. Laplacian properties (algebraic layer)
-- =====================================================================

/-- The Laplacian is symmetric. -/
lemma GovGraph.laplacian_symm (G : GovGraph F n) : G.laplacian.IsSymm := by
  ext i j
  simp only [laplacian, degMatrix, sub_apply, diagonal_apply, transpose_apply]
  by_cases hij : i = j
  · subst hij; ring
  · simp only [hij, ite_false, Ne.symm hij, ite_false]
    linarith [G.symm.apply i j]

/-- Laplacian row sums are zero. -/
lemma GovGraph.laplacian_row_sum (G : GovGraph F n) (i : Fin n) :
    ∑ j : Fin n, G.laplacian i j = 0 := by
  unfold laplacian degMatrix
  simp only [sub_apply, diagonal_apply]
  trans (∑ j : Fin n, (if i = j then G.deg i else 0)) - ∑ j : Fin n, G.W i j
  · rw [← Finset.sum_sub_distrib]
  · simp [Finset.sum_ite_eq, deg]

/-- Degree is non-negative. -/
lemma GovGraph.deg_nonneg (G : GovGraph F n) (i : Fin n) :
    0 ≤ G.deg i :=
  Finset.sum_nonneg (fun j _ => G.nonneg i j)

-- =====================================================================
-- S 4. Degree decomposition (algebraic layer)
-- =====================================================================

/-- Splitting a sum: the sum with k-th term zeroed equals the original minus the k-th term. -/
theorem sum_ite_zero_eq {α : Type*} [DecidableEq α] [Fintype α]
    (k : α) (f : α → F) :
    ∑ j : α, (if j = k then 0 else f j) = ∑ j : α, f j - f k := by
  have h1 : ∑ j : α, f j = f k + ∑ j ∈ Finset.univ.erase k, f j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
  have h2 : ∑ j : α, (if j = k then 0 else f j) =
      ∑ j ∈ Finset.univ.erase k, f j := by
    have key : ∀ j : α, (if j = k then (0 : F) else f j) =
        (if j ∈ Finset.univ.erase k then f j else 0) := by
      intro j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      split
      case isTrue h => subst h; simp
      case isFalse _ => simp
    simp_rw [key]
    rw [Finset.sum_ite_mem]
    simp [Finset.univ_inter]
  linarith

/-- deg(i) = w(i,k) + degRemoved(k,i). -/
lemma GovGraph.deg_eq_weight_add_degRemoved (G : GovGraph F n) (k i : Fin n) :
    G.deg i = G.W i k + G.degRemoved k i := by
  simp only [deg, degRemoved]
  linarith [sum_ite_zero_eq k (G.W i)]

/-- degRemoved is non-negative. -/
lemma GovGraph.degRemoved_nonneg (G : GovGraph F n) (k i : Fin n) :
    0 ≤ G.degRemoved k i := by
  apply Finset.sum_nonneg
  intro j _
  split
  · exact le_refl 0
  · exact G.nonneg i j

/-- w(i,k) ≤ deg(i). -/
lemma GovGraph.weight_le_deg (G : GovGraph F n) (i k : Fin n) :
    G.W i k ≤ G.deg i := by
  rw [G.deg_eq_weight_add_degRemoved k i]
  linarith [G.degRemoved_nonneg k i]

/-- deg(i) ≤ maxDeg. -/
lemma GovGraph.deg_le_maxDeg (G : GovGraph F n) [NeZero n] (i : Fin n) :
    G.deg i ≤ G.maxDeg :=
  Finset.le_sup' G.deg (Finset.mem_univ i)

/-- Removing `i` from the `i`-row changes nothing because self-loops are zero. -/
lemma GovGraph.degRemoved_self (G : GovGraph F n) (i : Fin n) :
    G.degRemoved i i = G.deg i := by
  unfold GovGraph.degRemoved GovGraph.deg
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases h : j = i
  · subst h
    simp [G.no_self]
  · simp [h]

/-- The minimum residual degree is bounded by every concrete residual degree. -/
lemma GovGraph.minRemovedDeg_le_degRemoved (G : GovGraph F n) [NeZero n]
    (k i : Fin n) :
    G.minRemovedDeg ≤ G.degRemoved k i := by
  simpa [GovGraph.minRemovedDeg] using
    (Finset.inf'_le
      (s := Finset.univ (α := Fin n × Fin n))
      (f := fun p : Fin n × Fin n => G.degRemoved p.1 p.2)
      (by simp : (k, i) ∈ Finset.univ))

/-- Positivity of the minimum residual degree implies positivity of every
    residual degree. -/
lemma GovGraph.degRemoved_pos_of_minRemovedDeg_pos (G : GovGraph F n)
    [NeZero n] (hmin : 0 < G.minRemovedDeg) (k i : Fin n) :
    0 < G.degRemoved k i :=
  lt_of_lt_of_le hmin (G.minRemovedDeg_le_degRemoved k i)

/-- Positivity of the minimum residual degree implies positivity of every
    original degree. -/
lemma GovGraph.deg_pos_of_minRemovedDeg_pos (G : GovGraph F n)
    [NeZero n] (hmin : 0 < G.minRemovedDeg) (i : Fin n) :
    0 < G.deg i := by
  have h := G.degRemoved_pos_of_minRemovedDeg_pos hmin i i
  simpa [G.degRemoved_self i] using h

/-- Every signal difference is bounded by the signal range. -/
theorem le_signalRange {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {n : Nat} [NeZero n] (s : Fin n → F)
    (a b : Fin n) :
    |s a - s b| ≤ signalRange s := by
  simpa [signalRange] using
    (Finset.le_sup'
      (s := Finset.univ (α := Fin n × Fin n))
      (f := fun p : Fin n × Fin n => |s p.1 - s p.2|)
      (by simp : (a, b) ∈ Finset.univ))

/-- The signal range is non-negative. -/
theorem signalRange_nonneg {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {n : Nat} [NeZero n] (s : Fin n → F) :
    0 ≤ signalRange s := by
  classical
  let i : Fin n := Finset.univ_nonempty.choose
  exact le_trans (abs_nonneg (s i - s i)) (le_signalRange s i i)

/-- The Laplacian cast to R for spectral analysis. -/
noncomputable def GovGraph.laplacianR (G : GovGraph ℚ n) : Matrix (Fin n) (Fin n) ℝ :=
  G.laplacian.map (Rat.cast : ℚ → ℝ)

/-- The R-Laplacian is Hermitian (= symmetric for real matrices). -/
lemma GovGraph.laplacianR_isHermitian (G : GovGraph ℚ n) :
    G.laplacianR.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp only [laplacianR, conjTranspose_apply, map_apply, star_trivial]
  exact congrArg Rat.cast (G.laplacian_symm.apply i j)

/-- The spectral gap (algebraic connectivity, Fiedler value): the
    second-smallest eigenvalue of the Laplacian.

    eigenvalues0 is antitone (descending). Index card-1 is the smallest
    (= 0 for connected graphs). Index card-2 is the spectral gap. -/
noncomputable def GovGraph.spectralGap (G : GovGraph ℚ n) (hn : 2 ≤ n) : ℝ :=
  G.laplacianR_isHermitian.eigenvalues₀
    ⟨Fintype.card (Fin n) - 2, by simp [Fintype.card_fin]; omega⟩

/-- **Spectral-gap positivity assumption wrapper.**
    This theorem does not prove positivity from connectivity. It simply
    re-exports the explicit hypothesis `0 < G.spectralGap hn` so downstream
    lemmas can name that assumption directly. -/
lemma GovGraph.spectral_gap_pos_assumption (G : GovGraph ℚ n)
    (hn : 2 ≤ n)
    (hfiedler : 0 < G.spectralGap hn) :
    0 < G.spectralGap hn :=
  hfiedler

end Legitimacy
