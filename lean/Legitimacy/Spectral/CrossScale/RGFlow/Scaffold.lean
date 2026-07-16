/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Unified
import Legitimacy.Spectral.CrossScale.RGFlow

/-!
# RG substrate scaffolds

Probe-only substrate contracts for the G1 RG-invariant kernel campaign.

This module deliberately contains no new axioms and no unfinished proofs. The
objects below are structures and `Prop`-valued contracts that make the two
candidate substrate paths explicit before any theorem campaign commits to one
of them.
-/

set_option autoImplicit false

namespace Legitimacy

open scoped BigOperators

/-! ## Path A: dependent coarse-grained governed systems -/

/-- A refinement from a coarse governed system into a base governed system.

The fields record the data a future implementation must preserve across the
coarse/base boundary. They are intentionally lightweight: this scaffold names
the proof obligations without choosing the eventual quotient/equitable-partition
implementation. -/
structure GovernedSystemRefinement {m n : Nat}
    (coarse : GovernedSystem m) (base : GovernedSystem n) where
  /-- Embedding of coarse causal nodes into base causal nodes. -/
  nodeMap : Fin m → Fin n
  /-- The coarse binary pipeline cannot expose more stages than the base. -/
  graphLength_le : coarse.graph.length ≤ base.graph.length
  /-- The coarse spectral carrier must refine the base spectral carrier. -/
  weightedSize_le : coarse.graph.weightedSize ≤ base.graph.weightedSize
  /-- Trace-level refinement obligation, to be discharged by the chosen model. -/
  trace_refines : Prop
  /-- Causal-DAG refinement obligation, to be discharged by the chosen model. -/
  dag_refines : Prop
  /-- Governed-boundary refinement obligation, to be discharged by the chosen model. -/
  governed_refines : Prop

scoped infix:50 " ⥹ " => GovernedSystemRefinement

/-- A governed system equipped with all size-indexed coarse systems below its
base causal dimension. -/
structure CoarseGrainedGovernedSystem (n : Nat) where
  /-- The original governed system. -/
  base : GovernedSystem n
  /-- A coarse governed system for every admissible causal dimension. -/
  coarse : (m : Nat) → m ≤ n → GovernedSystem m
  /-- Each coarse system refines the base system. -/
  refinement : (m : Nat) → (h : m ≤ n) → coarse m h ⥹ base

namespace CoarseGrainedGovernedSystem

variable {n : Nat} (C : CoarseGrainedGovernedSystem n)

/-- Identity coherence signature: the top coarse level is the base system. -/
def IdentityCoherence : Prop :=
  C.coarse n (Nat.le_refl n) = C.base

/-- Refinement composition signature: refining through an intermediate scale is
available whenever `k ≤ m ≤ n`. -/
def RefinementCompositionCoherence : Prop :=
  ∀ (k m : Nat) (hkm : k ≤ m) (hmn : m ≤ n),
    Nonempty (C.coarse k (Nat.le_trans hkm hmn) ⥹ C.coarse m hmn)

/-- Monotonicity signature for the binary-pipeline and spectral carrier sizes
under decreasing coarse dimensions. -/
def RefinementMonotonicity : Prop :=
  ∀ (k m : Nat) (hkm : k ≤ m) (hmn : m ≤ n),
    (C.coarse k (Nat.le_trans hkm hmn)).graph.length ≤
      (C.coarse m hmn).graph.length ∧
    (C.coarse k (Nat.le_trans hkm hmn)).graph.weightedSize ≤
      (C.coarse m hmn).graph.weightedSize

/-- Spectral coherence signature: every coarse kernel datum uses the spectral
carrier attached to the matching coarse governed system. -/
def SpectralCarrierCoherence : Prop :=
  ∀ (m : Nat) (h : m ≤ n),
    ∃ _carrierMap :
      Fin (C.coarse m h).graph.weightedSize → Fin C.base.graph.weightedSize,
      True

/-- Runtime-kernel lift signature for Path A. This is the theorem shape the G1
campaign would eventually need after constructing coarse kernel data. -/
def RuntimeKernelLiftContract : Prop :=
  ∀ Dbase : LegitimacyKernelData C.base,
    IsLegitimacyKernel Dbase →
      ∀ (m : Nat) (h : m ≤ n),
        ∃ Dcoarse : LegitimacyKernelData (C.coarse m h),
          IsLegitimacyKernel Dcoarse

/-- Semantic-kernel lift signature for Path A. This is the strengthened variant
that would preserve the explicit diagnostic/spectral bridge. -/
def SemanticKernelLiftContract : Prop :=
  ∀ Dbase : LegitimacyKernelData C.base,
    IsSemanticLegitimacyKernel Dbase →
      ∀ (m : Nat) (h : m ≤ n),
        ∃ Dcoarse : LegitimacyKernelData (C.coarse m h),
          IsSemanticLegitimacyKernel Dcoarse

/-- Combined Path A scaffold contract collecting the coherence obligations and
the two candidate kernel-lift targets. -/
def PathAContract : Prop :=
  C.IdentityCoherence ∧
    C.RefinementCompositionCoherence ∧
    C.RefinementMonotonicity ∧
    C.SpectralCarrierCoherence ∧
    C.RuntimeKernelLiftContract ∧
    C.SemanticKernelLiftContract

end CoarseGrainedGovernedSystem

/-! ## Path B: same-carrier RG operator -/

namespace GovGraph

variable {n : Nat}

/-- Deterministic lexicographic enumeration of admissible same-carrier merge
pairs. -/
private def sameCarrierPairCandidates (n : Nat) : List (Fin n × Fin n) :=
  ((List.finRange n).map fun i =>
      (List.finRange n).filterMap fun j =>
        if i < j then
          some (i, j)
        else
          none).foldr List.append []

/-- Select the maximum-weight merge pair, breaking ties by the enumeration
order. Graphs with fewer than two carrier slots have no admissible pair. -/
private def sameCarrierSelectedPair (G : GovGraph ℚ n) :
    Option (Fin n × Fin n) :=
  match sameCarrierPairCandidates n with
  | [] => none
  | p :: ps =>
      some <|
        ps.foldl
          (fun best cand =>
            if G.W best.1 best.2 < G.W cand.1 cand.2 then cand else best)
          p

/-- Lower-index representative for a selected same-carrier merge pair. -/
private def sameCarrierRepresentative (p : Fin n × Fin n) : Fin n :=
  if p.1 < p.2 then p.1 else p.2

/-- Higher-index slot retained in the carrier but isolated after aggregation. -/
private def sameCarrierIsolatedSlot (p : Fin n × Fin n) : Fin n :=
  if p.1 < p.2 then p.2 else p.1

/-- Carrier block represented by a live slot after a same-carrier merge. The
representative carries both original vertices; every other live slot carries
itself. -/
private def sameCarrierBlock (representative isolated i : Fin n) :
    Finset (Fin n) :=
  if i = representative then {representative, isolated} else {i}

/-- Total edge mass between two same-carrier blocks. -/
private def sameCarrierBlockWeight (G : GovGraph ℚ n)
    (left right : Finset (Fin n)) : ℚ :=
  Finset.sum left (fun i => Finset.sum right (fun j => G.W i j))

private theorem sameCarrierBlockWeight_symm (G : GovGraph ℚ n)
    (left right : Finset (Fin n)) :
    sameCarrierBlockWeight G left right =
      sameCarrierBlockWeight G right left := by
  simp only [sameCarrierBlockWeight]
  rw [Finset.sum_comm]
  simp_rw [G.weight_symm]

private theorem sameCarrierBlockWeight_nonneg (G : GovGraph ℚ n)
    (left right : Finset (Fin n)) :
    0 ≤ sameCarrierBlockWeight G left right := by
  simp only [sameCarrierBlockWeight]
  refine Finset.sum_nonneg ?_
  intro i _hi
  refine Finset.sum_nonneg ?_
  intro j _hj
  exact G.weight_nonneg i j

/-- Same-carrier aggregation weight: choose a maximum-weight pair, aggregate
the isolated slot into the lower representative by block summation, keep the
carrier dimension fixed, and zero all incident edges of the isolated slot. -/
private def sameCarrierWeight (G : GovGraph ℚ n) (i j : Fin n) : ℚ :=
  if i = j then
    0
  else
    match sameCarrierSelectedPair G with
    | none => G.W i j
    | some p =>
        let representative := sameCarrierRepresentative p
        let isolated := sameCarrierIsolatedSlot p
        if i = isolated then
          0
        else if j = isolated then
          0
        else
          sameCarrierBlockWeight G
            (sameCarrierBlock representative isolated i)
            (sameCarrierBlock representative isolated j)

private theorem sameCarrierWeight_symm (G : GovGraph ℚ n) (i j : Fin n) :
    sameCarrierWeight G i j = sameCarrierWeight G j i := by
  unfold sameCarrierWeight
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := Ne.symm hij
    cases hp : sameCarrierSelectedPair G with
    | none =>
        simp [hij, hji, G.weight_symm]
    | some p =>
        by_cases hi : i = sameCarrierIsolatedSlot p
        · simp [hi]
        · by_cases hj : j = sameCarrierIsolatedSlot p
          · simp [hi, hj]
          · simp [hij, hji, hi, hj, sameCarrierBlockWeight_symm]

private theorem sameCarrierWeight_nonneg (G : GovGraph ℚ n) (i j : Fin n) :
    0 ≤ sameCarrierWeight G i j := by
  unfold sameCarrierWeight
  by_cases hij : i = j
  · simp [hij]
  · cases hp : sameCarrierSelectedPair G with
    | none =>
        simpa [hij, hp] using G.weight_nonneg i j
    | some p =>
        by_cases hi : i = sameCarrierIsolatedSlot p
        · simp [hi]
        · by_cases hj : j = sameCarrierIsolatedSlot p
          · simp [hi, hj]
          · simpa [hij, hp, hi, hj] using
              sameCarrierBlockWeight_nonneg G
                (sameCarrierBlock (sameCarrierRepresentative p)
                  (sameCarrierIsolatedSlot p) i)
                (sameCarrierBlock (sameCarrierRepresentative p)
                  (sameCarrierIsolatedSlot p) j)

private theorem sameCarrierWeight_self_zero (G : GovGraph ℚ n) (i : Fin n) :
    sameCarrierWeight G i i = 0 := by
  simp [sameCarrierWeight]

/-- Same-carrier RG step. It does not remove a node; it aggregates the selected
maximum-weight pair into a representative while keeping the isolated slot in
the carrier with no incident edge mass. -/
def rgStepSameCarrier (G : GovGraph ℚ n) : GovGraph ℚ n where
  weights := sameCarrierWeight G
  weight_symm := by
    intro i j
    exact sameCarrierWeight_symm G i j
  weight_nonneg := by
    intro i j
    exact sameCarrierWeight_nonneg G i j
  weight_self_zero := by
    intro i
    exact sameCarrierWeight_self_zero G i

/-- Projection signature relating the same-carrier operator to an ordinary
dimension-dropping coarse-grain step. -/
def SameCarrierProjectsToCoarseGrain
    (G : GovGraph ℚ (n + 1)) (i j : Fin (n + 1)) (hij : i ≠ j) : Prop :=
  ∃ project : GovGraph ℚ (n + 1) → GovGraph ℚ n,
    project (rgStepSameCarrier G) = G.coarseGrain i j hij

/-- Exact CV-preservation signature for the optimistic same-carrier path. -/
def SameCarrierPreservesCv
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) : Prop :=
  (rgStepSameCarrier G).cv s = G.cv s

/-- Controlled CV-correction signature for the fallback same-carrier path. -/
def SameCarrierCvCorrection
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) : Prop :=
  ∃ correction : ℚ,
    (rgStepSameCarrier G).cv s = G.cv s + correction

/-- Spectral-gap correction signature for the same-carrier path. -/
def SameCarrierSpectralGapCorrection
    (G : GovGraph ℚ n) (hn : 2 ≤ n) : Prop :=
  ∃ correction : ℝ,
    (rgStepSameCarrier G).spectralGap hn = G.spectralGap hn + correction

/-- Named correction bound sufficient to preserve the semantic spectral layer:
the corrected spectral-gap/CV product for the same-carrier update remains above
the `SpectralWellConnected` threshold. -/
def SameCarrierSpectralProductCorrectionBound
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (hn : 2 ≤ n)
    (spectralGapCorrection : ℝ) (cvCorrection : ℚ) : Prop :=
  (rgStepSameCarrier G).spectralGap hn =
      G.spectralGap hn + spectralGapCorrection ∧
    (rgStepSameCarrier G).cv s = G.cv s + cvCorrection ∧
      (17 : ℝ) / 20 ≤
        (G.spectralGap hn + spectralGapCorrection) *
          Rat.cast (G.cv s + cvCorrection)

/-- Runtime-kernel invariance signature for a same-carrier RG update of the
spectral graph stored inside one fixed governed system. -/
def SameCarrierRuntimeKernelInvariant
    {m : Nat} {sys : GovernedSystem m} (D : LegitimacyKernelData sys) : Prop :=
  IsLegitimacyKernel D →
    ∃ D' : LegitimacyKernelData sys,
      D'.spectralGraph = rgStepSameCarrier D.spectralGraph ∧
        IsLegitimacyKernel D'

/-- Semantic-kernel invariance signature for the strengthened kernel target. -/
def SameCarrierSemanticKernelInvariant
    {m : Nat} {sys : GovernedSystem m} (D : LegitimacyKernelData sys) : Prop :=
  IsSemanticLegitimacyKernel D →
    ∃ D' : LegitimacyKernelData sys,
      D'.spectralGraph = rgStepSameCarrier D.spectralGraph ∧
        IsSemanticLegitimacyKernel D'

/-- Combined Path B scaffold contract collecting the projection/correction
obligations needed before attempting a same-carrier G1 theorem. -/
def SameCarrierRGContract
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (hn : 2 ≤ n) : Prop :=
  SameCarrierPreservesCv G s ∨
    (SameCarrierCvCorrection G s ∧ SameCarrierSpectralGapCorrection G hn)

end GovGraph

/-- Runtime kernel preservation under the same-carrier RG update. The update
changes only the spectral carrier stored in the datum; the five runtime kernel
axioms are operational witnesses over the fixed governed system. -/
theorem isLegitimacyKernel_rgStepSameCarrier_preservation
    {m : Nat} {sys : GovernedSystem m}
    (D : LegitimacyKernelData sys) (h : IsLegitimacyKernel D) :
    ∃ D' : LegitimacyKernelData sys,
      D'.spectralGraph = GovGraph.rgStepSameCarrier D.spectralGraph ∧
        IsLegitimacyKernel D' := by
  let D' : LegitimacyKernelData sys :=
    { D with spectralGraph := GovGraph.rgStepSameCarrier D.spectralGraph }
  refine ⟨D', rfl, ?_⟩
  exact
    { certifiable := h.certifiable
      observable := h.observable
      corrigible := by
        simpa [D'] using h.corrigible
      compositionalSafety := h.compositionalSafety
      nonVacuous := h.nonVacuous }

/-- Semantic kernel preservation under an explicit same-carrier spectral
correction bound. The runtime and diagnostic layers are unchanged; the named
bound supplies exactly the updated `SpectralWellConnected` witness. -/
theorem isSemanticLegitimacyKernel_rgStepSameCarrier_preservation_of_correction_bound
    {m : Nat} {sys : GovernedSystem m}
    (D : LegitimacyKernelData sys) (h : IsSemanticLegitimacyKernel D)
    {spectralGapCorrection : ℝ} {cvCorrection : ℚ}
    (hcorrection :
      GovGraph.SameCarrierSpectralProductCorrectionBound
        D.spectralGraph D.spectralSignal sys.graph.weightedSize_atLeastTwo
        spectralGapCorrection cvCorrection)
    (hrep :
      SpectralCarrierRepresentsGraph sys.graph
        (GovGraph.rgStepSameCarrier D.spectralGraph) D.spectralSignal) :
    ∃ D' : LegitimacyKernelData sys,
      D'.spectralGraph = GovGraph.rgStepSameCarrier D.spectralGraph ∧
        IsSemanticLegitimacyKernel D' := by
  let D' : LegitimacyKernelData sys :=
    { D with spectralGraph := GovGraph.rgStepSameCarrier D.spectralGraph }
  have hspectral :
      SpectralWellConnected (GovGraph.rgStepSameCarrier D.spectralGraph)
        D.spectralSignal sys.graph.weightedSize_atLeastTwo := by
    rcases hcorrection with ⟨hgap, hcv, hproduct⟩
    exact
      (SpectralWellConnected_iff_product_threshold
        (GovGraph.rgStepSameCarrier D.spectralGraph)
        D.spectralSignal sys.graph.weightedSize_atLeastTwo).mpr (by
        rw [hgap, hcv]
        norm_num at hproduct ⊢
        exact hproduct)
  refine ⟨D', rfl, ?_⟩
  exact
    { runtimeKernel :=
        { certifiable := h.runtimeKernel.certifiable
          observable := h.runtimeKernel.observable
          corrigible := by
            simpa [D'] using h.runtimeKernel.corrigible
          compositionalSafety := h.runtimeKernel.compositionalSafety
          nonVacuous := h.runtimeKernel.nonVacuous }
      semanticBridge :=
        ⟨h.semanticBridge.diagnostics,
          by simpa [D'] using hrep,
          by simpa [D'] using hspectral⟩ }

end Legitimacy
