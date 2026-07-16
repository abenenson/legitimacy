/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Core.ConcreteGraphs
import Legitimacy.Spectral.Capacity.CriticalCapability
import Legitimacy.Diagnostics.Graph
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Legitimacy.Spectral.CrossScale.RGFlow.Core

Renormalization-group style coarse-graining on weighted governance graphs.

The operator merges two vertices into a single effective meta-vertex, summing
their outgoing weights and dropping the induced self-loop mass. The weighted
solidarity axiom is RG-invariant, while the exact critical-capability threshold
`C_star` can strictly decrease under coarse-graining.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Legitimacy

open Finset

namespace GovGraph

section Generic

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {n : ℕ}

/-- Deterministic lexicographic enumeration of admissible merge pairs. -/
private def pairCandidates (n : ℕ) : List (Fin n × Fin n) :=
  ((List.finRange n).map fun i =>
      (List.finRange n).filterMap fun j =>
        if i < j then
          some (i, j)
        else
          none).foldr List.append []

/-- Deterministic experimental proxy for the Cheeger hierarchy: merge the
maximum-weight pair, breaking ties by the lexicographic enumeration order from
`pairCandidates`. This keeps the computation `native_decide`-friendly for the
finite `n = 5` lattice experiment. -/
private def maxWeightPair (G : GovGraph ℚ (n + 2)) : Fin (n + 2) × Fin (n + 2) :=
  match pairCandidates (n + 2) with
  | [] => (0, 1)
  | p :: ps =>
      ps.foldl
        (fun best cand =>
          if G.W best.1 best.2 < G.W cand.1 cand.2 then cand else best)
        p

/-- Keep the lower-indexed vertex when merging `i` and `j`. -/
private def mergeKeep (i j : Fin (n + 1)) : Fin (n + 1) :=
  if _h : i < j then i else j

/-- Drop the higher-indexed vertex when merging `i` and `j`. -/
private def mergeDrop (i j : Fin (n + 1)) : Fin (n + 1) :=
  if _h : i < j then j else i

/-- Signal coarse-graining induced by merging two vertices: the merged
meta-vertex carries the sum of the two original signals. -/
def coarseSignal (s : Fin (n + 1) → F)
    (i j : Fin (n + 1)) (_hij : i ≠ j) : Fin n → F := fun a =>
  let keep := mergeKeep i j
  let drop := mergeDrop i j
  if _hkeep : drop.succAbove a = keep then
    s keep + s drop
  else
    s (drop.succAbove a)

/-- Core coarse-grained weight formula with fixed surviving and dropped
vertices. -/
private def coarseWeightWith (G : GovGraph F (n + 1))
    (keep drop : Fin (n + 1)) (a b : Fin n) : F :=
  if _ha : drop.succAbove a = keep then
    if _hb : drop.succAbove b = keep then
      0
    else
      G.W keep (drop.succAbove b) + G.W drop (drop.succAbove b)
  else if _hb : drop.succAbove b = keep then
    G.W (drop.succAbove a) keep + G.W (drop.succAbove a) drop
  else
    G.W (drop.succAbove a) (drop.succAbove b)

private theorem coarseWeightWith_symm (G : GovGraph F (n + 1))
    (keep drop : Fin (n + 1)) (a b : Fin n) :
    coarseWeightWith G keep drop a b = coarseWeightWith G keep drop b a := by
  unfold coarseWeightWith
  by_cases ha : drop.succAbove a = keep
  · by_cases hb : drop.succAbove b = keep
    · simp [ha, hb]
    · simp [ha, hb, G.weight_symm]
  · by_cases hb : drop.succAbove b = keep
    · simp [ha, hb, G.weight_symm]
    · simp [ha, hb, G.weight_symm]

private theorem coarseWeightWith_nonneg (G : GovGraph F (n + 1))
    (keep drop : Fin (n + 1)) (a b : Fin n) :
    0 ≤ coarseWeightWith G keep drop a b := by
  unfold coarseWeightWith
  by_cases ha : drop.succAbove a = keep
  · by_cases hb : drop.succAbove b = keep
    · simp [ha, hb]
    · simpa [ha, hb] using
        add_nonneg (G.weight_nonneg keep (drop.succAbove b))
          (G.weight_nonneg drop (drop.succAbove b))
  · by_cases hb : drop.succAbove b = keep
    · simpa [ha, hb] using
        add_nonneg (G.weight_nonneg (drop.succAbove a) keep)
          (G.weight_nonneg (drop.succAbove a) drop)
    · simpa [ha, hb] using G.weight_nonneg (drop.succAbove a) (drop.succAbove b)

private theorem coarseWeightWith_self_zero (G : GovGraph F (n + 1))
    (keep drop : Fin (n + 1)) (a : Fin n) :
    coarseWeightWith G keep drop a a = 0 := by
  unfold coarseWeightWith
  by_cases ha : drop.succAbove a = keep
  · simp [ha]
  · simp [ha, G.weight_self_zero]

/-- Sum of weights across two blocks. -/
private def blockWeight (G : GovGraph ℚ n)
    (left right : Finset (Fin n)) : ℚ :=
  Finset.sum left (fun i => Finset.sum right (fun j => G.W i j))

private theorem blockWeight_symm (G : GovGraph ℚ n)
    (left right : Finset (Fin n)) :
    blockWeight G left right = blockWeight G right left := by
  simp only [blockWeight]
  rw [Finset.sum_comm]
  simp_rw [G.weight_symm]

private theorem blockWeight_nonneg (G : GovGraph ℚ n)
    (left right : Finset (Fin n)) :
    0 ≤ blockWeight G left right := by
  simp only [blockWeight]
  refine Finset.sum_nonneg ?_
  intro i hi
  refine Finset.sum_nonneg ?_
  intro j hj
  exact G.weight_nonneg i j

/-- Lexicographic strict order on finite node sets, using ascending node IDs. A
set is smaller when it contains the first node where the two membership
profiles differ. -/
private def subsetLexLT (left right : Finset (Fin n)) : Bool :=
  ((List.finRange n).find? fun i => decide (i ∈ left) != decide (i ∈ right)).elim false
    fun i => decide (i ∈ left)

/-- Non-strict lexicographic order on finite node sets. -/
private def subsetLexLE (left right : Finset (Fin n)) : Bool :=
  if left = right then true else subsetLexLT left right

/-- Canonical lexicographic block order for partitions. -/
private def canonicalPartition (partition : List (Finset (Fin n))) :
    List (Finset (Fin n)) :=
  partition.mergeSort subsetLexLE

/-- Coarse-grained signal induced by an explicit partition. -/
def coarseSignalPartition (s : Fin n → ℚ)
    (partition : List (Finset (Fin n))) : Fin partition.length → ℚ := fun a =>
  Finset.sum (partition.get a) (fun i => s i)

/-- Core coarse-grained weight formula induced by an explicit partition. Internal
block mass is dropped, matching the two-vertex coarse-graining operator. -/
private def coarseWeightPartition (G : GovGraph ℚ n)
    (partition : List (Finset (Fin n)))
    (a b : Fin partition.length) : ℚ :=
  if _h : a = b then
    0
  else
    blockWeight G (partition.get a) (partition.get b)

private theorem coarseWeightPartition_symm (G : GovGraph ℚ n)
    (partition : List (Finset (Fin n))) (a b : Fin partition.length) :
    coarseWeightPartition G partition a b =
      coarseWeightPartition G partition b a := by
  unfold coarseWeightPartition
  by_cases h : a = b
  · subst h
    simp
  · have h' : b ≠ a := by
      intro hba
      exact h hba.symm
    simp [h, h', blockWeight_symm]

private theorem coarseWeightPartition_nonneg (G : GovGraph ℚ n)
    (partition : List (Finset (Fin n))) (a b : Fin partition.length) :
    0 ≤ coarseWeightPartition G partition a b := by
  unfold coarseWeightPartition
  by_cases h : a = b
  · simp [h]
  · simp [h, blockWeight_nonneg]

private theorem coarseWeightPartition_self_zero (G : GovGraph ℚ n)
    (partition : List (Finset (Fin n))) (a : Fin partition.length) :
    coarseWeightPartition G partition a a = 0 := by
  simp [coarseWeightPartition]

/-- Coarse-grain a graph along an explicit partition. -/
def coarseGrainPartition (G : GovGraph ℚ n)
    (partition : List (Finset (Fin n))) : GovGraph ℚ partition.length where
  weights := coarseWeightPartition G partition
  weight_symm := by
    intro a b
    exact coarseWeightPartition_symm G partition a b
  weight_nonneg := by
    intro a b
    exact coarseWeightPartition_nonneg G partition a b
  weight_self_zero := by
    intro a
    exact coarseWeightPartition_self_zero G partition a

/-- Merge two vertices into one effective vertex, summing their rows and
columns and dropping the induced self-loop mass. -/
def coarseGrain (G : GovGraph F (n + 1))
    (i j : Fin (n + 1)) (_hij : i ≠ j) :
    GovGraph F n where
  weights := coarseWeightWith G (mergeKeep i j) (mergeDrop i j)
  weight_symm := by
    intro a b
    exact coarseWeightWith_symm G (mergeKeep i j) (mergeDrop i j) a b
  weight_nonneg := by
    intro a b
    exact coarseWeightWith_nonneg G (mergeKeep i j) (mergeDrop i j) a b
  weight_self_zero := by
    intro a
    exact coarseWeightWith_self_zero G (mergeKeep i j) (mergeDrop i j) a

/-- Experimental RG state carrying a positive-size graph together with its
current coarse-grained signal. -/
abbrev RGState :=
  Σ m : ℕ, GovGraph ℚ (m + 1) × (Fin (m + 1) → ℚ)

/-- Safe division on `ℚ` for the exhaustive partition scorers. -/
private def safeDivQ (numerator denominator : ℚ) : ℚ :=
  if denominator = 0 then 0 else numerator / denominator

/-- Canonical singleton partition. -/
private def singletonPartition (n : ℕ) : List (Finset (Fin n)) :=
  canonicalPartition <| (List.finRange n).map fun i => ({i} : Finset (Fin n))

/-- Merge one side of a bipartition into a block and keep the complement as
singletons. -/
private def mergeSidePartition (side : Finset (Fin n)) : List (Finset (Fin n)) :=
  canonicalPartition <|
    side :: (List.finRange n).filterMap fun i =>
      if i ∈ side then none else some ({i} : Finset (Fin n))

/-- Exhaustive subset enumeration, built directly from `List.finRange` to stay
computable under `native_decide`. -/
private def allSubsets : List (Finset (Fin n)) :=
  (List.finRange n).foldl
    (fun subsets i => subsets ++ subsets.map (insert i))
    [∅]

/-- Exhaustive nontrivial subset search space for `n ≤ 5`. -/
private def nontrivialSubsets : List (Finset (Fin n)) :=
  allSubsets.filter fun side => 0 < side.card ∧ side.card < n

/-- The side that gets merged in the bipartition families: smaller cardinality,
breaking equal-size ties lexicographically on node IDs. -/
private def canonicalMergedSide (side : Finset (Fin n)) : Finset (Fin n) :=
  let other := Finset.univ \ side
  if side.card < other.card then
    side
  else if other.card < side.card then
    other
  else if subsetLexLT side other then
    side
  else
    other

/-- Total weighted degree mass of a side. -/
private def sideVolume (G : GovGraph ℚ n) (side : Finset (Fin n)) : ℚ :=
  Finset.sum side (fun i => G.deg i)

/-- Cross-cut mass of a bipartition side. -/
private def cutWeight (G : GovGraph ℚ n) (side : Finset (Fin n)) : ℚ :=
  blockWeight G side (Finset.univ \ side)

/-- Conductance score for a bipartition side. -/
private def conductanceScore (G : GovGraph ℚ n) (side : Finset (Fin n)) : ℚ :=
  let other := Finset.univ \ side
  safeDivQ (cutWeight G side) (min (sideVolume G side) (sideVolume G other))

/-- Total edge mass used in the modularity score. -/
private def totalEdgeMass (G : GovGraph ℚ n) : ℚ :=
  Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => G.W i j))

/-- Bipartition modularity score, following the literal formula in the brief. -/
private def modularityScore (G : GovGraph ℚ n) (side : Finset (Fin n)) : ℚ :=
  let other := Finset.univ \ side
  let mass := totalEdgeMass G
  let sameBlock : Fin n → Fin n → Bool := fun i j =>
    (i ∈ side ∧ j ∈ side) || (i ∈ other ∧ j ∈ other)
  let inner :=
    Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j =>
      if sameBlock i j then
        G.W i j - safeDivQ (G.deg i * G.deg j) (2 * mass)
      else
        0))
  safeDivQ inner (2 * mass)

/-- Prefer a lower conductance score, then break ties lexicographically on the
merged side. -/
private def cheegerBetter (G : GovGraph ℚ n)
    (cand best : Finset (Fin n)) : Bool :=
  let candScore := conductanceScore G cand
  let bestScore := conductanceScore G best
  let candSide := canonicalMergedSide cand
  let bestSide := canonicalMergedSide best
  if candScore < bestScore then
    true
  else if bestScore < candScore then
    false
  else
    subsetLexLT candSide bestSide

/-- Prefer a higher modularity score, then break ties lexicographically on the
merged side. -/
private def modularityBetter (G : GovGraph ℚ n)
    (cand best : Finset (Fin n)) : Bool :=
  let candScore := modularityScore G cand
  let bestScore := modularityScore G best
  let candSide := canonicalMergedSide cand
  let bestSide := canonicalMergedSide best
  if bestScore < candScore then
    true
  else if candScore < bestScore then
    false
  else
    subsetLexLT candSide bestSide

private def bestSubset? (better : Finset (Fin n) → Finset (Fin n) → Bool)
    (candidates : List (Finset (Fin n))) : Option (Finset (Fin n)) :=
  match candidates with
  | [] => none
  | first :: rest =>
      some <| rest.foldl (fun best cand => if better cand best then cand else best) first

/-- Minimum-conductance bipartition family. -/
def partitionFamilyCheeger (G : GovGraph ℚ n) : List (Finset (Fin n)) :=
  match bestSubset? (cheegerBetter G) nontrivialSubsets with
  | some side => mergeSidePartition (canonicalMergedSide side)
  | none => singletonPartition n

/-- Modularity-maximizing bipartition family. -/
def partitionFamilyModularity (G : GovGraph ℚ n) : List (Finset (Fin n)) :=
  match bestSubset? (modularityBetter G) nontrivialSubsets with
  | some side => mergeSidePartition (canonicalMergedSide side)
  | none => singletonPartition n

/-- Insert a new node into each existing block of a partition, plus the
singleton-block extension. This enumerates each set partition exactly once when
used over ascending node IDs. -/
private def insertIntoBlocks (x : Fin n) :
    List (Finset (Fin n)) → List (List (Finset (Fin n)))
  | [] => [[({x} : Finset (Fin n))]]
  | block :: blocks =>
      ((insert x block) :: blocks) ::
        (insertIntoBlocks x blocks).map fun partition => block :: partition

/-- Exhaustive set-partition enumeration for the `n ≤ 5` signal-preserving
family. -/
private def allSetPartitions : List (List (Finset (Fin n))) :=
  (List.finRange n).foldl
    (fun partitions x => partitions.foldr
      (fun partition acc => insertIntoBlocks x partition ++ acc)
      [])
    [[]]

/-- Mean signal value on a block. -/
private def blockMean (s : Fin n → ℚ) (block : Finset (Fin n)) : ℚ :=
  safeDivQ (Finset.sum block (fun i => s i)) block.card

/-- Variance of the signal values on a block. -/
private def blockVariance (s : Fin n → ℚ) (block : Finset (Fin n)) : ℚ :=
  let μ := blockMean s block
  safeDivQ (Finset.sum block (fun i => (s i - μ) ^ 2)) block.card

/-- Lexicographic strict order on canonical partitions. -/
private def partitionLexLT (left right : List (Finset (Fin n))) : Bool :=
  List.lex (canonicalPartition left) (canonicalPartition right) subsetLexLT

/-- Signal-preserving score: sum of within-block variances. -/
private def signalVarianceScore (s : Fin n → ℚ)
    (partition : List (Finset (Fin n))) : ℚ :=
  (canonicalPartition partition).foldl (fun acc block => acc + blockVariance s block) 0

/-- Prefer a lower signal-variance score, then break ties lexicographically on
the whole canonical partition. -/
private def signalPartitionBetter (s : Fin n → ℚ)
    (cand best : List (Finset (Fin n))) : Bool :=
  let candScore := signalVarianceScore s cand
  let bestScore := signalVarianceScore s best
  if candScore < bestScore then
    true
  else if bestScore < candScore then
    false
  else
    partitionLexLT cand best

private def bestPartition? (better : List (Finset (Fin n)) → List (Finset (Fin n)) → Bool)
    (candidates : List (List (Finset (Fin n)))) : Option (List (Finset (Fin n))) :=
  match candidates with
  | [] => none
  | first :: rest =>
      some <| rest.foldl (fun best cand => if better cand best then cand else best) first

/-- Signal-preserving partition family with `⌈n / 2⌉` blocks. -/
def partitionFamilySignalPreserving (_G : GovGraph ℚ n) (s : Fin n → ℚ) :
    List (Finset (Fin n)) :=
  let blockCount := (n + 1) / 2
  let candidates :=
    allSetPartitions.filter fun partition =>
      partition.length = blockCount
  match bestPartition? (signalPartitionBetter s) candidates with
  | some partition => canonicalPartition partition
  | none => singletonPartition n

/-- Partition-selector interface for the alternative RG families. -/
abbrev PartitionSelector :=
  ∀ {m : ℕ}, GovGraph ℚ (m + 1) → (Fin (m + 1) → ℚ) → List (Finset (Fin (m + 1)))

private def cheegerSelector : PartitionSelector := fun G _ => partitionFamilyCheeger G

private def modularitySelector : PartitionSelector := fun G _ => partitionFamilyModularity G

private def signalPreservingSelector : PartitionSelector := fun G s =>
  partitionFamilySignalPreserving G s

/-- One partition-family RG step. A one-vertex graph is terminal. -/
def rgStepWith (selector : PartitionSelector) : RGState → RGState
  | ⟨0, (G, s)⟩ => ⟨0, (G, s)⟩
  | ⟨m + 1, (G, s)⟩ =>
      let partition := selector G s
      match hlen : partition.length with
      | 0 => ⟨m + 1, (G, s)⟩
      | k + 1 =>
          let coarseG : GovGraph ℚ (k + 1) := by
            simpa [hlen] using G.coarseGrainPartition partition
          let coarseS : Fin (k + 1) → ℚ := by
            simpa [hlen] using GovGraph.coarseSignalPartition s partition
          ⟨k,
            (coarseG, coarseS)⟩

/-- Initial RG state for a partition-family flow. -/
def rgInitWith (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ) : RGState :=
  ⟨n, (G, s)⟩

/-- Iterated RG state under an explicit partition family. -/
def rgStateAtWith (selector : PartitionSelector)
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ) (k : ℕ) :
    RGState :=
  Nat.iterate (rgStepWith selector) k (rgInitWith G s)

/-- Trajectory helper for an explicit partition family. -/
def rgTrajectoryWith (selector : PartitionSelector)
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (δ : ℚ) (k : ℕ) : ℚ × ℚ :=
  match rgStateAtWith selector G s k with
  | ⟨_, (Gk, sk)⟩ => (Gk.cv sk, C_star Gk sk δ)

/-- Iterated RG trajectory under the minimum-conductance family. -/
def rgTrajectoryCheeger (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (δ : ℚ) (k : ℕ) : ℚ × ℚ :=
  rgTrajectoryWith cheegerSelector G s δ k

/-- Iterated RG trajectory under the modularity-maximizing family. -/
def rgTrajectoryModularity (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (δ : ℚ) (k : ℕ) : ℚ × ℚ :=
  rgTrajectoryWith modularitySelector G s δ k

/-- Iterated RG trajectory under the signal-preserving family. -/
def rgTrajectorySignalPreserving (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (δ : ℚ) (k : ℕ) : ℚ × ℚ :=
  rgTrajectoryWith signalPreservingSelector G s δ k

/-- One experimental RG step using the deterministic maximum-weight merge
proxy. A one-vertex graph is already terminal. -/
def rgStep : RGState → RGState
  | ⟨0, (G, s)⟩ => ⟨0, (G, s)⟩
  | ⟨m + 1, (G, s)⟩ =>
      let pair := maxWeightPair G
      if hij : pair.1 ≠ pair.2 then
        ⟨m,
          (G.coarseGrain pair.1 pair.2 hij,
           GovGraph.coarseSignal s pair.1 pair.2 hij)⟩
      else
        ⟨m + 1, (G, s)⟩

/-- Initial experimental RG state for a positive-size graph. -/
def rgInit (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ) : RGState :=
  ⟨n, (G, s)⟩

/-- Experimental iterated RG state after `k` deterministic maximum-weight
merge steps. -/
def rgStateAt (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ) (k : ℕ) :
    RGState :=
  Nat.iterate rgStep k (rgInit G s)

/-- Experimental RG trajectory value used for the `n = 5` adversarial test.
This is a finite-lattice proxy, not a
general Cheeger-flow theorem. -/
def rgTrajectory (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ)
    (δ : ℚ) (k : ℕ) : ℚ × ℚ :=
  match rgStateAt G s k with
  | ⟨_, (Gk, sk)⟩ => (Gk.cv sk, C_star Gk sk δ)

namespace List

private theorem flatten_eq_foldr_append {α : Type*} (L : List (List α)) :
    L.flatten = List.foldr List.append [] L := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [ih]

end List

private theorem pairCandidates_mem_lt {p : Fin n × Fin n}
    (hp : p ∈ pairCandidates n) : p.1 < p.2 := by
  unfold pairCandidates at hp
  rw [← List.flatten_eq_foldr_append] at hp
  rcases List.mem_flatten.mp hp with ⟨l, hl, hp'⟩
  rcases List.mem_map.mp hl with ⟨i, _, rfl⟩
  rcases List.mem_filterMap.mp hp' with ⟨j, _, hij⟩
  split_ifs at hij with hlt
  · cases hij
    exact hlt

private theorem zero_one_mem_pairCandidates (n : ℕ) :
    ((0 : Fin (n + 2)), (1 : Fin (n + 2))) ∈ pairCandidates (n + 2) := by
  unfold pairCandidates
  rw [← List.flatten_eq_foldr_append]
  apply List.mem_flatten.mpr
  refine ⟨List.filterMap
      (fun j : Fin (n + 2) =>
        if (0 : Fin (n + 2)) < j then some ((0 : Fin (n + 2)), j) else none)
      (List.finRange (n + 2)), ?_, ?_⟩
  · apply List.mem_map.mpr
    refine ⟨(0 : Fin (n + 2)), ?_, rfl⟩
    simp
  · apply List.mem_filterMap.mpr
    refine ⟨(1 : Fin (n + 2)), ?_, ?_⟩
    · simp
    · simp

private theorem foldl_pick_mem {α : Type*} (choose : α → α → α)
    (hchoose : ∀ a b, choose a b = a ∨ choose a b = b) :
    ∀ (best : α) (l : List α), List.foldl choose best l ∈ best :: l
  | best, [] => by simp
  | best, a :: l => by
      have ih := foldl_pick_mem choose hchoose (choose best a) l
      rcases hchoose best a with h | h
      · simp [List.foldl, h] at ih ⊢
        rcases ih with ih | ih
        · exact Or.inl ih
        · exact Or.inr <| Or.inr ih
      · simp [List.foldl, h] at ih ⊢
        rcases ih with ih | ih
        · exact Or.inr <| Or.inl ih
        · exact Or.inr <| Or.inr ih

private theorem maxWeightPair_mem (G : GovGraph ℚ (n + 2)) :
    maxWeightPair G ∈ pairCandidates (n + 2) := by
  unfold maxWeightPair
  have hnonempty : pairCandidates (n + 2) ≠ [] := by
    intro h
    have hmem := zero_one_mem_pairCandidates n
    simp [h] at hmem
  cases h : pairCandidates (n + 2) with
  | nil => exact (hnonempty h).elim
  | cons p ps =>
      simpa using foldl_pick_mem
        (fun best cand =>
          if G.W best.1 best.2 < G.W cand.1 cand.2 then cand else best)
        (by
          intro a b
          by_cases hlt : G.W a.1 a.2 < G.W b.1 b.2 <;> simp [hlt]) p ps

private theorem maxWeightPair_ne (G : GovGraph ℚ (n + 2)) :
    (maxWeightPair G).1 ≠ (maxWeightPair G).2 := by
  exact ne_of_lt <| pairCandidates_mem_lt <| maxWeightPair_mem G

private theorem rgStep_eq_coarseGrain (G : GovGraph ℚ (n + 2))
    (s : Fin (n + 2) → ℚ) :
    rgStep ⟨n + 1, (G, s)⟩ =
      ⟨n,
        (G.coarseGrain (maxWeightPair G).1 (maxWeightPair G).2 (maxWeightPair_ne G),
         GovGraph.coarseSignal s (maxWeightPair G).1 (maxWeightPair G).2 (maxWeightPair_ne G))⟩ := by
  unfold rgStep
  simp [maxWeightPair_ne]

private theorem rgStateAt_succ_eq (G : GovGraph ℚ (n + 2))
    (s : Fin (n + 2) → ℚ) (k : ℕ) :
    rgStateAt G s (k + 1) =
      rgStateAt
        (G.coarseGrain (maxWeightPair G).1 (maxWeightPair G).2 (maxWeightPair_ne G))
        (GovGraph.coarseSignal s (maxWeightPair G).1 (maxWeightPair G).2 (maxWeightPair_ne G))
        k := by
  simp [rgStateAt, rgInit, Function.iterate_succ_apply, rgStep_eq_coarseGrain]

/-- The canonical greedy RG flow reaches a terminal state after finitely many
steps. The current implementation is stronger than the paper's tentative
lexicographic-measure sketch: every nonterminal step merges a distinct pair, so
the node count strictly decreases until the one-vertex state is reached. -/
theorem rgStateAt_terminates_at_fixedPoint
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ) :
    ∃ k ≤ n, rgStateAt G s k = rgStateAt G s (k + 1) := by
  induction n with
  | zero =>
      refine ⟨0, Nat.le_refl 0, ?_⟩
      simp [rgStateAt, rgInit, rgStep]
  | succ n ih =>
      let G' :=
        G.coarseGrain (maxWeightPair G).1 (maxWeightPair G).2 (maxWeightPair_ne G)
      let s' :=
        GovGraph.coarseSignal s (maxWeightPair G).1 (maxWeightPair G).2 (maxWeightPair_ne G)
      obtain ⟨k, hk, hkfix⟩ := ih G' s'
      refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
      simpa [rgStateAt_succ_eq, G', s'] using hkfix

/-- The canonical greedy RG trajectory stabilizes after finitely many
coarse-graining steps. -/
theorem rgTrajectory_terminates_at_fixedPoint
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ) (δ : ℚ) :
    ∃ k ≤ n, rgTrajectory G s δ k = rgTrajectory G s δ (k + 1) := by
  obtain ⟨k, hk, hkfix⟩ := rgStateAt_terminates_at_fixedPoint G s
  refine ⟨k, hk, ?_⟩
  exact congrArg
    (fun state =>
      match state with
      | ⟨_, (Gk, sk)⟩ => (Gk.cv sk, C_star Gk sk δ))
    hkfix

/-- Task-surface alias for the canonical greedy RG fixed-point theorem. -/
theorem governanceGraph_RG_terminates_at_fixedPoint
    (G : GovGraph ℚ (n + 1)) (s : Fin (n + 1) → ℚ) (δ : ℚ) :
    ∃ k ≤ n, rgTrajectory G s δ k = rgTrajectory G s δ (k + 1) :=
  rgTrajectory_terminates_at_fixedPoint G s δ

end Generic

end GovGraph

section Concrete

variable {n : ℕ}

/-- Weighted solidarity holds unconditionally after coarse-graining in the
present weighted-average semantics. -/
theorem coarseGrain_unconditional_solidarity
    (G : GovGraph ℚ (n + 1)) (i j : Fin (n + 1)) (hij : i ≠ j) :
    WeightedGraphSolidarity (G.coarseGrain i j hij) := by
  exact graphSolidarity_holds _

/-- RG monotonicity at scale `δ`: coarse-graining does not shrink the exact
critical-capability threshold. -/
def RGFlowMonotonicityAt
    (G : GovGraph ℚ (n + 2)) (s : Fin (n + 2) → ℚ) (δ : ℚ)
    (i j : Fin (n + 2)) (hij : i ≠ j) : Prop :=
  C_star G s δ ≤
    C_star (G.coarseGrain i j hij) (GovGraph.coarseSignal s i j hij) δ

instance instDecidableRGFlowMonotonicityAt
    (G : GovGraph ℚ (n + 2)) (s : Fin (n + 2) → ℚ) (δ : ℚ)
    (i j : Fin (n + 2)) (hij : i ≠ j) :
    Decidable (RGFlowMonotonicityAt G s δ i j hij) := by
  unfold RGFlowMonotonicityAt
  infer_instance

/-- Strategyproofness-collapse class: after coarse-graining, the exact
critical-capability threshold strictly decreases, so a weaker manipulator now
suffices to reach the same perturbation scale. -/
def RGCriticalCapabilityCollapseClass
    (G : GovGraph ℚ (n + 2)) (s : Fin (n + 2) → ℚ) (δ : ℚ)
    (i j : Fin (n + 2)) (hij : i ≠ j) : Prop :=
  C_star (G.coarseGrain i j hij) (GovGraph.coarseSignal s i j hij) δ <
    C_star G s δ

/-- Deprecated compatibility alias: the corrected name is
`RGCriticalCapabilityCollapseClass`, since the predicate is a strict decrease
of `C_star` under coarse-graining. -/
def RGStrategyproofnessCollapseClass
    (G : GovGraph ℚ (n + 2)) (s : Fin (n + 2) → ℚ) (δ : ℚ)
    (i j : Fin (n + 2)) (hij : i ≠ j) : Prop :=
  RGCriticalCapabilityCollapseClass G s δ i j hij

instance instDecidableRGCriticalCapabilityCollapseClass
    (G : GovGraph ℚ (n + 2)) (s : Fin (n + 2) → ℚ) (δ : ℚ)
    (i j : Fin (n + 2)) (hij : i ≠ j) :
    Decidable (RGCriticalCapabilityCollapseClass G s δ i j hij) := by
  unfold RGCriticalCapabilityCollapseClass
  infer_instance

instance instDecidableRGStrategyproofnessCollapseClass
    (G : GovGraph ℚ (n + 2)) (s : Fin (n + 2) → ℚ) (δ : ℚ)
    (i j : Fin (n + 2)) (hij : i ≠ j) :
    Decidable (RGStrategyproofnessCollapseClass G s δ i j hij) := by
  unfold RGStrategyproofnessCollapseClass
  infer_instance

/-- Concrete counterexample: RG monotonicity of `C_star` can fail. -/
theorem coarseGrain_may_break_monotonicity :
    ∃ (G : GovGraph ℚ 3) (i j : Fin 3) (hij : i ≠ j),
      ¬ RGFlowMonotonicityAt G sig (1 / 10) i j hij := by
  refine ⟨uniTriGraph, 0, 1, by decide, ?_⟩
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  native_decide

/-- Exact RG-flow values for the five concrete governance graphs under the
standard merge `0 + 1`. -/
theorem concrete_RG_flow_5graphs :
    let i : Fin 3 := 0
    let j : Fin 3 := 1
    let hij : i ≠ j := by decide
    let s' := GovGraph.coarseSignal sig i j hij
    (uniTriGraph.coarseGrain i j hij).cv s' = 3 ∧
    C_star (uniTriGraph.coarseGrain i j hij) s' (1 / 10) = 1 / 30 ∧
    (asymTriGraph.coarseGrain i j hij).cv s' = 3 ∧
    C_star (asymTriGraph.coarseGrain i j hij) s' (1 / 10) = 1 / 30 ∧
    (nearPathGraph.coarseGrain i j hij).cv s' = 3 ∧
    C_star (nearPathGraph.coarseGrain i j hij) s' (1 / 10) = 1 / 30 ∧
    (stronglyConnectedGraph.coarseGrain i j hij).cv s' = 3 ∧
    C_star (stronglyConnectedGraph.coarseGrain i j hij) s' (1 / 10) = 1 / 30 ∧
    (bottleneckGraph.coarseGrain i j hij).cv s' = 3 ∧
    C_star (bottleneckGraph.coarseGrain i j hij) s' (1 / 10) = 1 / 30 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  all_goals native_decide

/-- **Universality conjecture (five-graph evidence).** For the five concrete
graphs already used throughout the paper, coarse-graining by merging `0 + 1`
always lowers `C_star`; empirically they all fall into the same
critical-capability-collapse class. -/
theorem universality_conjecture_evidence :
    let i : Fin 3 := 0
    let j : Fin 3 := 1
    let hij : i ≠ j := by decide
    RGCriticalCapabilityCollapseClass uniTriGraph sig (1 / 10) i j hij ∧
    RGCriticalCapabilityCollapseClass asymTriGraph sig (1 / 10) i j hij ∧
    RGCriticalCapabilityCollapseClass nearPathGraph sig (1 / 10) i j hij ∧
    RGCriticalCapabilityCollapseClass stronglyConnectedGraph sig (1 / 10) i j hij ∧
    RGCriticalCapabilityCollapseClass bottleneckGraph sig (1 / 10) i j hij := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  all_goals native_decide

end Concrete

end Legitimacy
