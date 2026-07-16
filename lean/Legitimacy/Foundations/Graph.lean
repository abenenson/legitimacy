/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Types
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Legitimacy.Foundations.Graph — Governance graph types on Mathlib

Port of the governance-graph and `GraphN` structures from the earlier
formalization to Mathlib-native types. Uses `Fin n → Fin n → F` for the weight matrix
(where `F` satisfies `[Field F] [LinearOrder F] [IsStrictOrderedRing F]`)
and `Finset.sum` / `Finset.univ` instead of hand-rolled `sumOver`.

## Design notes

- `WeightedGraph` is a type class capturing symmetric, non-negative weights
  with zero diagonal, parameterized over any linearly-ordered field `F`.
- `GraphN F n` carries this data as a structure and provides a `WeightedGraph`
  instance.
- `gov`, `govRemoved`, `deg`, `degRemoved` are defined via `Finset.univ.sum`
  and work over any linearly-ordered field.
- Binary governance pipeline (`GovernanceGraph`) remains over `ℚ` since
  `ClaimQ` uses `ℚ`.
- Alias `GraphNQ n := GraphN ℚ n` provided.

## References

* H. Peyton Young, *Equity: In Theory and Practice*, 1994.
-/

set_option autoImplicit false

open Finset

namespace Legitimacy

/-! ### Binary governance pipeline (port of Graph.lean) -/

/-- Binary decision outcome for a single claim. -/
inductive BinaryDecision where
  | Permit : BinaryDecision
  | Deny   : BinaryDecision
  deriving Repr, DecidableEq

instance : Nonempty BinaryDecision := ⟨BinaryDecision.Permit⟩

/-- A governance node maps a set of claims and a claimant to a binary decision. -/
def GovernanceNodeFn := List ClaimQ → ClaimantId → BinaryDecision

/-- A governance graph is a sequential pipeline of nodes. -/
def GovernanceGraph := List GovernanceNodeFn

/-- Filter claims to only those permitted by a node. -/
def filterPermitted (node : GovernanceNodeFn) (claims : List ClaimQ) : List ClaimQ :=
  claims.filter (fun c => node claims c.id == BinaryDecision.Permit)

/-- Evaluate a claimant through the full pipeline.
    Denied at any stage → short-circuit to Deny. -/
def graphDecide (graph : GovernanceGraph) (claims : List ClaimQ)
    (k : ClaimantId) : BinaryDecision :=
  match graph with
  | [] => BinaryDecision.Permit
  | node :: rest =>
    match node claims k with
    | BinaryDecision.Deny => BinaryDecision.Deny
    | BinaryDecision.Permit =>
      let forwarded := filterPermitted node claims
      graphDecide rest forwarded k

/-! ### WeightedGraph type class -/

/-- Type class for an n-node weighted graph with non-negative symmetric weights
    and zero self-loops, over a linearly-ordered field `F`. -/
class WeightedGraph (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (n : ℕ) where
  /-- Edge weight between nodes i and j. -/
  W : Fin n → Fin n → F
  /-- Weights are symmetric. -/
  symm : ∀ i j, W i j = W j i
  /-- All weights are non-negative. -/
  nonneg : ∀ i j, 0 ≤ W i j
  /-- No self-loops. -/
  self_zero : ∀ i, W i i = 0

/-! ### Weighted governance graph (Mathlib port of GraphN) -/

/-- An n-node weighted governance graph with non-negative symmetric weights
    and zero self-loops. Weight matrix is `Fin n → Fin n → F`. -/
structure GraphN (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (n : ℕ) where
  /-- Edge weight between nodes i and j. -/
  weights : Fin n → Fin n → F
  /-- Weights are symmetric. -/
  weight_symm : ∀ (i j : Fin n), weights i j = weights j i
  /-- All weights are non-negative. -/
  weight_nonneg : ∀ (i j : Fin n), 0 ≤ weights i j
  /-- No self-loops. -/
  weight_self_zero : ∀ (i : Fin n), weights i i = 0

/-- Forget a concrete `GraphN` into the corresponding `WeightedGraph`
type-class instance. -/
@[reducible]
def GraphN.toWeightedGraph {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {n : ℕ} (G : GraphN F n) : WeightedGraph F n where
  W := G.weights
  symm := G.weight_symm
  nonneg := G.weight_nonneg
  self_zero := G.weight_self_zero

/-- Alias: `GraphNQ n` is `GraphN ℚ n`. -/
abbrev GraphNQ (n : ℕ) := GraphN ℚ n

section Generic

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {n : ℕ}

/-- Degree of node i: sum of all edge weights from i. -/
def GraphN.deg (G : GraphN F n) (i : Fin n) : F :=
  ∑ j : Fin n, G.weights i j

/-- Weight function with edges to node k zeroed out. -/
def GraphN.wZero (G : GraphN F n) (k : Fin n) (i j : Fin n) : F :=
  if j = k then 0 else G.weights i j

/-- Degree of node i with node k removed. -/
def GraphN.degRemoved (G : GraphN F n) (k i : Fin n) : F :=
  ∑ j : Fin n, G.wZero k i j

/-- Governance decision at node i: weighted average of neighbors' signals. -/
noncomputable def GraphN.gov (G : GraphN F n) (s : Fin n → F) (i : Fin n) : F :=
  (∑ j : Fin n, G.weights i j * s j) / G.deg i

/-- Governance decision at node i with node k removed. -/
noncomputable def GraphN.govRemoved (G : GraphN F n) (s : Fin n → F)
    (k i : Fin n) : F :=
  (∑ j : Fin n, G.wZero k i j * s j) / G.degRemoved k i

/-! ### Basic structural lemmas -/

/-- Node degrees are nonnegative because every incident edge weight is
nonnegative. -/
lemma GraphN.deg_nonneg (G : GraphN F n) (i : Fin n) :
    0 ≤ G.deg i := by
  unfold deg
  exact Finset.sum_nonneg (fun j _ => G.weight_nonneg i j)

/-- Degrees in the graph with node `k` removed remain nonnegative. -/
lemma GraphN.degRemoved_nonneg (G : GraphN F n) (k i : Fin n) :
    0 ≤ G.degRemoved k i := by
  unfold degRemoved wZero
  exact Finset.sum_nonneg (fun j _ => by split_ifs <;> linarith [G.weight_nonneg i j])

end Generic

/-- Sum with zeroed k-term equals sum over erase k. -/
private lemma sum_ite_zero_eq_sum_erase' {F : Type*} [AddCommMonoid F]
    {n : ℕ} (f : Fin n → F) (k : Fin n) :
    (∑ j : Fin n, if j = k then (0 : F) else f j) = ∑ j ∈ univ.erase k, f j := by
  have h : ∑ j : Fin n, (if j = k then (0 : F) else f j) =
      (if k = k then (0 : F) else f k) + ∑ j ∈ univ.erase k, (if j = k then (0 : F) else f j) :=
    (Finset.add_sum_erase univ (fun j => if j = k then 0 else f j) (mem_univ k)).symm
  simp only [ite_true] at h
  rw [h, zero_add]
  exact Finset.sum_congr rfl (fun j hj => by
    rw [Finset.mem_erase] at hj; simp [hj.1])

section Generic2

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {n : ℕ}

/-- Degree decomposes as w(i,k) + degRemoved(k,i). -/
lemma GraphN.deg_split (G : GraphN F n) (k i : Fin n) :
    G.deg i = G.weights i k + G.degRemoved k i := by
  simp only [deg, degRemoved, wZero]
  rw [sum_ite_zero_eq_sum_erase' (G.weights i) k]
  exact (Finset.add_sum_erase univ (G.weights i) (mem_univ k)).symm

/-- wZero preserves non-negativity. -/
lemma GraphN.wZero_nonneg (G : GraphN F n) (k i j : Fin n) :
    0 ≤ G.wZero k i j := by
  unfold wZero; split_ifs <;> linarith [G.weight_nonneg i j]

end Generic2

end Legitimacy
