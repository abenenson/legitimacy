/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.PeerRelativeClass.Predicates

/-!
# Peer-Relative Witnesses

This module supplies the finite claim profiles and node witnesses used by the
peer-relative impossibility layer. It proves the canonical peer-relative node,
transparent-prefix facts, and first-effective witness obligations needed by
the obstruction theorem.

The scope is finite witness data and its local properties. It does not state
the final global impossibility result, which is assembled downstream from
these witnesses.
-/

set_option autoImplicit false

namespace Legitimacy

private def peerRelativeWitnessA : ClaimQ := ⟨0, 1/4, by norm_num, []⟩
private def peerRelativeWitnessA' : ClaimQ := ⟨0, 3/4, by norm_num, []⟩
private def peerRelativeWitnessB : ClaimQ := ⟨1, 1/2, by norm_num, []⟩
private def peerRelativeWitnessC : ClaimQ := ⟨2, 3/4, by norm_num, []⟩

private def peerRelativeWitnessClaims : List ClaimQ :=
  [peerRelativeWitnessA, peerRelativeWitnessB, peerRelativeWitnessC]

private def peerRelativeWitnessClaims' : List ClaimQ :=
  [peerRelativeWitnessA', peerRelativeWitnessB, peerRelativeWitnessC]

private def peerRelativeConsistencyWitnessA : ClaimQ := ⟨0, 1/4, by norm_num, []⟩
private def peerRelativeConsistencyWitnessB : ClaimQ := ⟨1, 1/2, by norm_num, []⟩
private def peerRelativeConsistencyWitnessC : ClaimQ := ⟨2, 3/4, by norm_num, []⟩
private def peerRelativeConsistencyWitnessD : ClaimQ := ⟨3, 1, by norm_num, []⟩

private def peerRelativeConsistencyWitnessClaims : List ClaimQ :=
  [peerRelativeConsistencyWitnessA, peerRelativeConsistencyWitnessB,
    peerRelativeConsistencyWitnessC, peerRelativeConsistencyWitnessD]

-- native_decide: finite canonical claim-profile membership, strength lookup,
-- and literal node-decision checks for the peer-relative witnesses.

/-- The canonical median-style peer-relative node is one instance of the
abstract peer-relative-node predicate: Bob's own strength is unchanged, while
raising Alice's surrounding claim flips Bob from Permit to Deny. -/
theorem peerRelativeNode_isPeerRelative :
    IsPeerRelativeNode peerRelativeNode := by
  refine ⟨peerRelativeWitnessClaims, peerRelativeWitnessClaims', 1, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  · native_decide
  · native_decide
  · native_decide
  · unfold ClaimsDistinct peerRelativeWitnessClaims peerRelativeWitnessA
      peerRelativeWitnessB peerRelativeWitnessC
    show ([0, 1, 2] : List Nat).Nodup
    decide
  · unfold ClaimsDistinct peerRelativeWitnessClaims' peerRelativeWitnessA'
      peerRelativeWitnessB peerRelativeWitnessC
    show ([0, 1, 2] : List Nat).Nodup
    decide
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  · native_decide
  · native_decide

/-- The canonical median-style peer-relative gate is a peer-relative aggregator:
raising Alice's claim flips Bob from Permit to Deny while Bob's own strength is
unchanged. -/
theorem peerRelativeNode_isPeerRelativeAggregator :
    IsPeerRelativeAggregator peerRelativeNode := by
  constructor
  · refine ⟨peerRelativeWitnessClaims, 0, 1, (3 / 4), by norm_num, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · decide
    -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
    · native_decide
    · native_decide
    · native_decide
    · unfold ClaimsDistinct peerRelativeWitnessClaims peerRelativeWitnessA
        peerRelativeWitnessB peerRelativeWitnessC
      show ([0, 1, 2] : List Nat).Nodup
      decide
    · unfold ClaimsDistinct peerRelativeWitnessClaims peerRelativeWitnessA
        peerRelativeWitnessB peerRelativeWitnessC strengthenClaim
      show ([0, 1, 2] : List Nat).Nodup
      decide
    · intro c hc hid
      cases hc with
      | head =>
          simp only [peerRelativeWitnessA] at hid ⊢
          norm_num
      | tail _ htail =>
          cases htail with
          | head =>
              simp only [peerRelativeWitnessB] at hid
              exact absurd hid (by decide)
          | tail _ htail2 =>
              cases htail2 with
              | head =>
                  simp only [peerRelativeWitnessC] at hid
                  exact absurd hid (by decide)
              | tail _ hnil =>
                  exact absurd hnil List.not_mem_nil
    -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
    · native_decide
    · native_decide
    · native_decide
  · refine ⟨peerRelativeConsistencyWitnessClaims, 0, 1, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · decide
    · native_decide
    · native_decide
    · unfold ClaimsDistinct peerRelativeConsistencyWitnessClaims
        peerRelativeConsistencyWitnessA peerRelativeConsistencyWitnessB
        peerRelativeConsistencyWitnessC peerRelativeConsistencyWitnessD
      show ([0, 1, 2, 3] : List Nat).Nodup
      decide
    · native_decide
    · native_decide
    · native_decide

/-- A non-peer-relative consistency-route node: claimant `0` is always denied,
claimant `1` is permitted only on three-claimant profiles, and all other
claimants are permitted. It exposes the removal/consistency witness without
depending on claim strengths. -/
def lengthThreeSurvivorNode : GovernanceNodeFn := fun claims k =>
  if k = 0 then
    BinaryDecision.Deny
  else if k = 1 then
    if claims.length = 3 then BinaryDecision.Permit else BinaryDecision.Deny
  else
    BinaryDecision.Permit

private def lengthThreeWitnessA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
private def lengthThreeWitnessB : ClaimQ := ⟨1, 1 / 2, by norm_num, []⟩
private def lengthThreeWitnessC : ClaimQ := ⟨2, 3 / 4, by norm_num, []⟩

private def lengthThreeWitnessClaims : List ClaimQ :=
  [lengthThreeWitnessA, lengthThreeWitnessB, lengthThreeWitnessC]

/-- The length-sensitive node has the broader concrete consistency-violation
route: removing denied claimant `0` flips surviving claimant `1` from Permit
to Deny. -/
@[reducible]
def lengthThreeSurvivorNode_hasConsistencyViolationWitness :
    BinaryDecisionPipeline.HasConsistencyViolationWitness
      (P := GovernanceGraph) lengthThreeSurvivorNode where
  claims := lengthThreeWitnessClaims
  denied := 0
  survivor := 1
  distinct_claimants := by decide
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  denied_in_claims := by native_decide
  survivor_in_claims := by native_decide
  claims_distinct := by
    unfold ClaimsDistinct lengthThreeWitnessClaims lengthThreeWitnessA
      lengthThreeWitnessB lengthThreeWitnessC
    show ([0, 1, 2] : List Nat).Nodup
    decide
  denied_decision := by native_decide
  survivor_permitted := by native_decide
  survivor_denied_after_removal := by native_decide

private lemma lengthThreeSurvivorNode_strengthen_eval
    (claims : List ClaimQ) (k j : ClaimantId) (s' : ℚ) (hs' : 0 < s') :
    lengthThreeSurvivorNode claims j =
      lengthThreeSurvivorNode (strengthenClaim k s' hs' claims) j := by
  simp [lengthThreeSurvivorNode, strengthenClaim_length]

/-- The length-sensitive consistency-route inhabitant is strictly broader than
the strengthened peer-relative aggregator predicate: strengthening a claim
preserves list length, and this node ignores claim strengths, so it cannot
exhibit the required monotonicity Permit-to-Deny flip. -/
theorem lengthThreeSurvivorNode_not_isPeerRelativeAggregator :
    ¬ BinaryDecisionPipeline.IsPeerRelativeAggregator
      (P := GovernanceGraph) lengthThreeSurvivorNode := by
  intro hagg
  rcases BinaryDecisionPipeline.IsPeerRelativeAggregator.monotonicityWitness
      hagg with
    ⟨claims, k, j, s', hs', _hkj, _hk, _hj, _hj', _hdist, _hdist',
      _hle, _hsame, hpermit, hdeny⟩
  have hsame :=
    lengthThreeSurvivorNode_strengthen_eval claims k j s' hs'
  change BinaryDecisionPipeline.evalNode (P := GovernanceGraph)
      lengthThreeSurvivorNode claims j =
    BinaryDecisionPipeline.evalNode (P := GovernanceGraph)
      lengthThreeSurvivorNode (strengthenClaim k s' hs' claims) j at hsame
  rw [hpermit, hdeny] at hsame
  exact BinaryDecision.noConfusion hsame

/-- A monotonicity-displacement node: claimant `1` is permitted until claimant
`0` is strengthened to the cutoff, then denied. All other claimants are always
permitted. -/
def thresholdDisplacementNode : GovernanceNodeFn := fun claims k =>
  if k = 1 then
    if ∃ c ∈ claims, c.id = 0 ∧ (3 / 4 : ℚ) ≤ c.strength then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit
  else
    BinaryDecision.Permit

private def thresholdDisplacementWitnessA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
private def thresholdDisplacementWitnessB : ClaimQ := ⟨1, 1 / 2, by norm_num, []⟩
private def thresholdDisplacementWitnessC : ClaimQ := ⟨2, 3 / 4, by norm_num, []⟩

private def thresholdDisplacementWitnessClaims : List ClaimQ :=
  [thresholdDisplacementWitnessA, thresholdDisplacementWitnessB,
    thresholdDisplacementWitnessC]

/-- The threshold-displacement node exposes the monotonicity route: raising
claimant `0` from `1 / 4` to `3 / 4` flips claimant `1` from Permit to Deny
without changing claimant `1`'s own strength. -/
@[reducible]
def thresholdDisplacementNode_hasMonotonicityViolationWitness :
    BinaryDecisionPipeline.HasMonotonicityViolationWitness
      (P := GovernanceGraph) thresholdDisplacementNode where
  claims := thresholdDisplacementWitnessClaims
  strengthened := 0
  affected := 1
  strengthened_strength := 3 / 4
  strengthened_strength_pos := by norm_num
  distinct_claimants := by decide
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  strengthened_in_claims := by native_decide
  affected_in_claims := by native_decide
  affected_in_strengthened := by native_decide
  claims_distinct := by
    unfold ClaimsDistinct thresholdDisplacementWitnessClaims
      thresholdDisplacementWitnessA thresholdDisplacementWitnessB
      thresholdDisplacementWitnessC
    show ([0, 1, 2] : List Nat).Nodup
    decide
  strengthened_claims_distinct := by
    unfold ClaimsDistinct thresholdDisplacementWitnessClaims
      thresholdDisplacementWitnessA thresholdDisplacementWitnessB
      thresholdDisplacementWitnessC strengthenClaim
    show ([0, 1, 2] : List Nat).Nodup
    decide
  strengthened_bound := by
    intro c hc hid
    cases hc with
    | head =>
        simp only [thresholdDisplacementWitnessA] at hid ⊢
        norm_num
    | tail _ htail =>
        cases htail with
        | head =>
            simp only [thresholdDisplacementWitnessB] at hid
            exact absurd hid (by decide)
        | tail _ htail2 =>
            cases htail2 with
            | head =>
                simp only [thresholdDisplacementWitnessC] at hid
                exact absurd hid (by decide)
            | tail _ hnil =>
                exact absurd hnil List.not_mem_nil
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  affected_strength_preserved := by native_decide
  affected_permitted := by native_decide
  affected_denied_after_strengthening := by native_decide

private lemma thresholdDisplacementNode_denied_only_affected
    {claims : List ClaimQ} {k : ClaimantId}
    (hdeny : thresholdDisplacementNode claims k = BinaryDecision.Deny) :
    k = 1 := by
  by_cases hk : k = 1
  · exact hk
  · simp [thresholdDisplacementNode, hk] at hdeny

private lemma thresholdDisplacementNode_eval_denied_only_affected
    {claims : List ClaimQ} {k : ClaimantId}
    (hdeny : BinaryDecisionPipeline.evalNode (P := GovernanceGraph)
      thresholdDisplacementNode claims k = BinaryDecision.Deny) :
    k = 1 := by
  exact thresholdDisplacementNode_denied_only_affected
    (by simpa [BinaryDecisionPipeline.evalNode] using hdeny)

/-- The monotonicity-displacement inhabitant is strictly broader than the
strengthened peer-relative aggregator predicate: it has a concrete
Permit-to-Deny strengthening witness, but any removal/consistency witness would
need a denied claimant and a distinct survivor both equal to claimant `1`. -/
theorem thresholdDisplacementNode_not_isPeerRelativeAggregator :
    ¬ BinaryDecisionPipeline.IsPeerRelativeAggregator
      (P := GovernanceGraph) thresholdDisplacementNode := by
  intro hagg
  rcases BinaryDecisionPipeline.IsPeerRelativeAggregator.consistencyViolationWitness
      hagg with
    ⟨claims, k, j, hkj, _hk, _hj, _hdistinct, hdeny, _hpermit,
      hremovedDeny⟩
  have hk : k = 1 :=
    thresholdDisplacementNode_eval_denied_only_affected hdeny
  have hj : j = 1 :=
    thresholdDisplacementNode_eval_denied_only_affected hremovedDeny
  have hsame : k = j := by
    rw [hk, hj]
  exact hkj hsame

end Legitimacy
