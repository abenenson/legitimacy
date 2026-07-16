/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.DecisionSystem
import Legitimacy.Results.Impossibility

/-!
# Generic binary diagnostics for decision systems

This module lifts the graph-level binary diagnostics to the thin
`DecisionSystem` interface specialized to first-party claim profiles and binary
decisions. The definitions mention only `DecisionSystem.decide`; sequential
pipeline structure remains in `BinaryDecisionPipeline`.
-/

set_option autoImplicit false

namespace Legitimacy

/-! ### Binary diagnostics over the broad decision-system interface -/

/-- **Decision-system consistency**: removing a denied claimant does not change
any other claimant's decision. -/
def GraphConsistencyP {P : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    (system : P) : Prop :=
  ∀ (claims : List ClaimQ) (k j : ClaimantId),
    InClaims k claims →
    InClaims j claims →
    k ≠ j →
    ClaimsDistinct claims →
    DecisionSystem.decide system claims k = BinaryDecision.Deny →
    DecisionSystem.decide system claims j =
      DecisionSystem.decide system (removeClaimGraph k claims) j

/-- **Decision-system solidarity**: the decision-system homogeneity /
scale-invariance diagnostic. Scaling all claim strengths by the same positive
factor preserves every decision. -/
def GraphSolidarityP {P : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    (system : P) : Prop :=
  ∀ (claims : List ClaimQ) (α : ℚ) (hα : 0 < α)
    (j : ClaimantId),
    InClaims j claims →
    let scaled := claims.map (fun c => ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)
    DecisionSystem.decide system claims j =
      DecisionSystem.decide system scaled j

/-- **Decision-system monotonicity**: strengthening any claimant's claim does
not flip any claimant's final decision from Permit to Deny. -/
def GraphMonotonicityP {P : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    (system : P) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId) (s' : ℚ) (hs' : 0 < s')
    (j : ClaimantId),
    InClaims k claims →
    ClaimsDistinct claims →
    (∀ c ∈ claims, c.id = k → c.strength ≤ s') →
    DecisionSystem.decide system claims j = BinaryDecision.Permit →
    DecisionSystem.decide system (strengthenClaim k s' hs' claims) j =
      BinaryDecision.Permit

/-- **Decision-system strategyproofness**: no claimant can improve their final
decision by misreporting strength at the system input. -/
def GraphStrategyproofnessP {P : Type}
    [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    (system : P) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId) (s_r : ℚ) (hs_r : 0 < s_r),
    InClaims k claims →
    ClaimsDistinct claims →
    DecisionSystem.decide system (strengthenClaim k s_r hs_r claims) k =
      BinaryDecision.Permit →
    DecisionSystem.decide system claims k = BinaryDecision.Permit

/-- Decision-system consistency is invariant under extensional equivalence. -/
lemma GraphConsistencyP_congr
    {P Q : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    [DecisionSystem Q (List ClaimQ) ClaimantId BinaryDecision]
    {G : P} {H : Q} (heq : DecisionSystem.Equivalent G H) :
    GraphConsistencyP G ↔ GraphConsistencyP H := by
  constructor <;> intro hcons <;> intro claims k j hk hj hkj hdist hden
  · have hden' : DecisionSystem.decide G claims k = BinaryDecision.Deny := by
      exact (heq claims k).trans hden
    have h := hcons claims k j hk hj hkj hdist hden'
    exact (heq claims j).symm.trans <| h.trans (heq (removeClaimGraph k claims) j)
  · have hden' : DecisionSystem.decide H claims k = BinaryDecision.Deny := by
      exact (heq claims k).symm.trans hden
    have h := hcons claims k j hk hj hkj hdist hden'
    exact (heq claims j).trans <| h.trans (heq (removeClaimGraph k claims) j).symm

/-- Forward transfer form of `GraphConsistencyP_congr`. -/
lemma GraphConsistencyP.transfer
    {P Q : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    [DecisionSystem Q (List ClaimQ) ClaimantId BinaryDecision]
    {G : P} {H : Q} (heq : DecisionSystem.Equivalent G H) :
    GraphConsistencyP G → GraphConsistencyP H :=
  (GraphConsistencyP_congr heq).mp

/-- Decision-system homogeneity / scale-invariance is invariant under
extensional equivalence. -/
lemma GraphSolidarityP_congr
    {P Q : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    [DecisionSystem Q (List ClaimQ) ClaimantId BinaryDecision]
    {G : P} {H : Q} (heq : DecisionSystem.Equivalent G H) :
    GraphSolidarityP G ↔ GraphSolidarityP H := by
  constructor <;> intro hsol <;> intro claims α hα j hj
  · specialize hsol claims α hα j hj
    exact (heq claims j).symm.trans <| hsol.trans <|
      heq (claims.map (fun c => ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)) j
  · specialize hsol claims α hα j hj
    exact (heq claims j).trans <| hsol.trans <|
      (heq (claims.map (fun c => ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)) j).symm

/-- Forward transfer form of `GraphSolidarityP_congr`. -/
lemma GraphSolidarityP.transfer
    {P Q : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    [DecisionSystem Q (List ClaimQ) ClaimantId BinaryDecision]
    {G : P} {H : Q} (heq : DecisionSystem.Equivalent G H) :
    GraphSolidarityP G → GraphSolidarityP H :=
  (GraphSolidarityP_congr heq).mp

/-- Decision-system monotonicity is invariant under extensional equivalence. -/
lemma GraphMonotonicityP_congr
    {P Q : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    [DecisionSystem Q (List ClaimQ) ClaimantId BinaryDecision]
    {G : P} {H : Q} (heq : DecisionSystem.Equivalent G H) :
    GraphMonotonicityP G ↔ GraphMonotonicityP H := by
  constructor <;> intro hmon <;> intro claims k s' hs' j hk hdist hle hperm
  · have hperm' : DecisionSystem.decide G claims j = BinaryDecision.Permit := by
      exact (heq claims j).trans hperm
    have h := hmon claims k s' hs' j hk hdist hle hperm'
    exact (heq (strengthenClaim k s' hs' claims) j).symm.trans h
  · have hperm' : DecisionSystem.decide H claims j = BinaryDecision.Permit := by
      exact (heq claims j).symm.trans hperm
    have h := hmon claims k s' hs' j hk hdist hle hperm'
    exact (heq (strengthenClaim k s' hs' claims) j).trans h

/-- Forward transfer form of `GraphMonotonicityP_congr`. -/
lemma GraphMonotonicityP.transfer
    {P Q : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    [DecisionSystem Q (List ClaimQ) ClaimantId BinaryDecision]
    {G : P} {H : Q} (heq : DecisionSystem.Equivalent G H) :
    GraphMonotonicityP G → GraphMonotonicityP H :=
  (GraphMonotonicityP_congr heq).mp

/-- Decision-system strategyproofness is invariant under extensional
equivalence. -/
lemma GraphStrategyproofnessP_congr
    {P Q : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    [DecisionSystem Q (List ClaimQ) ClaimantId BinaryDecision]
    {G : P} {H : Q} (heq : DecisionSystem.Equivalent G H) :
    GraphStrategyproofnessP G ↔ GraphStrategyproofnessP H := by
  constructor <;> intro hsp <;> intro claims k s_r hs_r hk hdist hperm
  · have hperm' :
        DecisionSystem.decide G (strengthenClaim k s_r hs_r claims) k =
          BinaryDecision.Permit := by
      exact (heq (strengthenClaim k s_r hs_r claims) k).trans hperm
    have h := hsp claims k s_r hs_r hk hdist hperm'
    exact (heq claims k).symm.trans h
  · have hperm' :
        DecisionSystem.decide H (strengthenClaim k s_r hs_r claims) k =
          BinaryDecision.Permit := by
      exact (heq (strengthenClaim k s_r hs_r claims) k).symm.trans hperm
    have h := hsp claims k s_r hs_r hk hdist hperm'
    exact (heq claims k).trans h

/-- Forward transfer form of `GraphStrategyproofnessP_congr`. -/
lemma GraphStrategyproofnessP.transfer
    {P Q : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    [DecisionSystem Q (List ClaimQ) ClaimantId BinaryDecision]
    {G : P} {H : Q} (heq : DecisionSystem.Equivalent G H) :
    GraphStrategyproofnessP G → GraphStrategyproofnessP H :=
  (GraphStrategyproofnessP_congr heq).mp

/-! ### Bridges to the concrete governance graph diagnostics -/

/-- The generic consistency diagnostic specializes to the existing concrete
governance-graph consistency diagnostic. -/
lemma graphConsistency_eq_graphConsistencyP (G : GovernanceGraph) :
    GraphConsistency G ↔ GraphConsistencyP G := by
  rfl

/-- The generic homogeneity / scale-invariance diagnostic specializes to the
existing concrete governance-graph diagnostic. -/
lemma graphSolidarity_eq_graphSolidarityP (G : GovernanceGraph) :
    GraphSolidarity G ↔ GraphSolidarityP G := by
  rfl

/-- The generic monotonicity diagnostic specializes to the existing concrete
governance-graph monotonicity diagnostic. -/
lemma graphMonotonicity_eq_graphMonotonicityP (G : GovernanceGraph) :
    GraphMonotonicity G ↔ GraphMonotonicityP G := by
  rfl

/-- The generic strategyproofness diagnostic specializes to the existing
concrete governance-graph strategyproofness diagnostic. -/
lemma graphStrategyproofness_eq_graphStrategyproofnessP (G : GovernanceGraph) :
    GraphStrategyproofness G ↔ GraphStrategyproofnessP G := by
  rfl

end Legitimacy
