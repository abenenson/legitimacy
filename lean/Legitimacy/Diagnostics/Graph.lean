/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Graph
import Legitimacy.Diagnostics.AllocationRule

/-!
# Legitimacy.Diagnostics.Graph — Graph-level diagnostics on Mathlib

Port of the earlier graph-axiom formalization to Mathlib-native types. Defines graph-level
diagnostics for both the binary governance pipeline and the weighted `GraphN`.

## Binary pipeline diagnostics (from GraphAxioms.lean)

- `NodeMonotonicity` — strengthening a claim does not flip Permit → Deny at a
  single node.
- `GraphMonotonicity` — strengthening a claim does not flip Permit → Deny
  through the full pipeline.

## Weighted graph diagnostics

- `WeightedGraphConsistency` — removing a disconnected node preserves governance.
- `WeightedGraphSolidarity` — homogeneity: scaling all signals scales
  governance by the same factor.
- `GraphMonotonicity_weighted` — increasing a node's signal does not decrease
  any governance output.
- `graphSolidarity_holds` and `graphConsistency_holds` discharge the weighted
  homogeneity and consistency obligations constructively.

## References

* Arrow-style impossibility theorems for the obstruction template.
* Thomson's reduced-problem consistency program for the consistency reading.
* Young's homogeneity axiom for apportionment as the scale-invariance analogue.
* Maskin/Sjostrom-style monotonicity and implementation-theory terminology.
-/

set_option autoImplicit false

open Finset

namespace Legitimacy

/-! ### Binary pipeline diagnostics -/

/-- Remove the first claim with the given ID from a list. -/
def removeClaimGraph (k : ClaimantId) : List ClaimQ → List ClaimQ
  | [] => []
  | c :: cs => if c.id = k then cs else c :: removeClaimGraph k cs

theorem ClaimProfile.lookup_removeClaimGraph_of_ne
    (claims : List ClaimQ) (k j : ClaimantId) (field : String)
    (hdist : ClaimsDistinct claims) (hkj : k ≠ j) :
    ClaimProfile.lookup (removeClaimGraph k claims) j field =
      ClaimProfile.lookup claims j field := by
  induction claims with
  | nil =>
      rfl
  | cons claim rest ih =>
      by_cases hclaimk : claim.id = k
      · have hclaimj : claim.id ≠ j := by
          intro hclaimj
          exact hkj (hclaimk.symm.trans hclaimj)
        have hbeq : (claim.id == j) = false := by
          simp [BEq.beq, hclaimj]
        have hkj_bool : (k == j) = false := by
          simp [BEq.beq, hkj]
        simp [removeClaimGraph, ClaimProfile.lookup, ClaimProfile.findSubject?,
          hclaimk, hkj_bool]
      · by_cases hclaimj : claim.id = j
        · subst j
          have hjk_bool : (claim.id == k) = false := by
            simp [BEq.beq, hclaimk]
          simp [removeClaimGraph, ClaimProfile.lookup, ClaimProfile.findSubject?,
            hclaimk]
        · have hbeq : (claim.id == j) = false := by
            simp [BEq.beq, hclaimj]
          have hdist_tail : ClaimsDistinct rest := ClaimsDistinct_tail hdist
          simp [removeClaimGraph, ClaimProfile.lookup, ClaimProfile.findSubject?,
            hclaimk, hbeq]
          exact ih hdist_tail

/-- **Node-level strategyproofness**: no claimant can improve their
decision by misreporting their strength. -/
def NodeStrategyproofness (node : GovernanceNodeFn) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId) (s_r : ℚ) (hs_r : 0 < s_r),
    InClaims k claims →
    ClaimsDistinct claims →
    node (strengthenClaim k s_r hs_r claims) k = BinaryDecision.Permit →
    node claims k = BinaryDecision.Permit

/-- **Graph-level strategyproofness**: no claimant can improve their final
decision by misreporting their strength at the graph input. This is the derived
graph diagnostic; see `solidarity_monotonicity_imply_strategyproof`. -/
def GraphStrategyproofness (graph : GovernanceGraph) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId) (s_r : ℚ) (hs_r : 0 < s_r),
    InClaims k claims →
    ClaimsDistinct claims →
    graphDecide graph (strengthenClaim k s_r hs_r claims) k = BinaryDecision.Permit →
    graphDecide graph claims k = BinaryDecision.Permit

/-- **Graph-level consistency**: removing a denied claimant does not change any
other claimant's decision. -/
def GraphConsistency (graph : GovernanceGraph) : Prop :=
  ∀ (claims : List ClaimQ) (k j : ClaimantId),
    InClaims k claims →
    InClaims j claims →
    k ≠ j →
    ClaimsDistinct claims →
    graphDecide graph claims k = BinaryDecision.Deny →
    graphDecide graph claims j = graphDecide graph (removeClaimGraph k claims) j

/-- **Graph-level solidarity**: the graph homogeneity / scale-invariance
diagnostic. Scaling all claim strengths by the same positive factor preserves
every decision. -/
def GraphSolidarity (graph : GovernanceGraph) : Prop :=
  ∀ (claims : List ClaimQ) (α : ℚ) (hα : 0 < α)
    (j : ClaimantId),
    InClaims j claims →
    let scaled := claims.map (fun c => c.scaleStrength α hα)
    graphDecide graph claims j = graphDecide graph scaled j

/-- **Node-level monotonicity** (binary version): strengthening a claimant's
claim does not flip that claimant's decision from Permit to Deny. -/
def NodeMonotonicity (node : GovernanceNodeFn) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId) (s' : ℚ) (hs' : 0 < s'),
    InClaims k claims →
    ClaimsDistinct claims →
    (∀ c ∈ claims, c.id = k → c.strength ≤ s') →
    node claims k = BinaryDecision.Permit →
    node (strengthenClaim k s' hs' claims) k = BinaryDecision.Permit

/-- **Graph-level monotonicity** (binary version): strengthening any claimant k's
claim at the graph input does not flip *any* claimant j's final decision
from Permit to Deny. -/
def GraphMonotonicity (graph : GovernanceGraph) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId) (s' : ℚ) (hs' : 0 < s')
    (j : ClaimantId),
    InClaims k claims →
    ClaimsDistinct claims →
    (∀ c ∈ claims, c.id = k → c.strength ≤ s') →
    graphDecide graph claims j = BinaryDecision.Permit →
    graphDecide graph (strengthenClaim k s' hs' claims) j = BinaryDecision.Permit

/-- Alias for the binary graph-level monotonicity diagnostic. -/
abbrev GraphMonotonicity_binary := GraphMonotonicity

/-! ### Weighted graph diagnostics -/

variable {n : ℕ}

/-- **Graph-level consistency**: when node k has zero weight to node i,
removing k does not change gov(i). -/
def WeightedGraphConsistency (G : GraphNQ n) : Prop :=
  ∀ (s : Fin n → ℚ) (k i : Fin n),
    i ≠ k →
    G.weights i k = 0 →
    G.deg i ≠ 0 →
    G.degRemoved k i ≠ 0 →
    G.gov s i = G.govRemoved s k i

/-- **Graph-level solidarity**: the weighted homogeneity diagnostic. Scaling
all signals by α scales governance by α (linearity of weighted average in
signals). -/
def WeightedGraphSolidarity (G : GraphNQ n) : Prop :=
  ∀ (s : Fin n → ℚ) (α : ℚ) (i : Fin n),
    0 < α →
    G.deg i ≠ 0 →
    G.gov (fun j => α * s j) i = α * G.gov s i

/-- **Graph-level monotonicity** (weighted): increasing node k's signal
weakly increases all governance outputs. -/
def GraphMonotonicity_weighted (G : GraphNQ n) : Prop :=
  ∀ (s s' : Fin n → ℚ) (k i : Fin n),
    s k ≤ s' k →
    (∀ j : Fin n, j ≠ k → s' j = s j) →
    G.deg i ≠ 0 →
    G.gov s i ≤ G.gov s' i

/-! ### Proofs of weighted graph diagnostics -/

/-- Governance scales linearly with signals. -/
lemma graphSolidarity_holds (G : GraphNQ n) : WeightedGraphSolidarity G := by
  intro s α i _hα hD
  simp only [GraphN.gov, GraphN.deg]
  have hnum : (∑ j : Fin n, G.weights i j * (α * s j)) =
      α * ∑ j : Fin n, G.weights i j * s j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hnum, mul_div_assoc]

/-- When w(i,k) = 0, removing k does not change governance at i. -/
lemma graphConsistency_holds (G : GraphNQ n) : WeightedGraphConsistency G := by
  intro s k i _hik hw0 _hD _hD'
  -- Show gov s i = govRemoved s k i by showing numerators and denominators match
  unfold GraphN.gov GraphN.govRemoved GraphN.deg GraphN.degRemoved
  -- Goal: (∑ j, w(i,j)*s(j)) / (∑ j, w(i,j)) = (∑ j, wZ(k,i,j)*s(j)) / (∑ j, wZ(k,i,j))
  -- When w(i,k) = 0, wZero(k,i,j) = w(i,j) for all j.
  suffices h : ∀ j : Fin n, G.wZero k i j = G.weights i j by
    simp_rw [h]
  intro j
  simp only [GraphN.wZero]
  split_ifs with hjk
  · subst hjk; exact hw0.symm
  · rfl

end Legitimacy
