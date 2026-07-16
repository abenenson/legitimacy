/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.PeerRelativeClass.Countermodel
import Legitimacy.Impossibility.PeerRelativeClass.Obstructions

/-!
# Structural peer-relative scarcity

This module replaces the public peer-relative impossibility interface with a
structural class. The old `IsPeerRelativeAggregator` predicate remains as an
implementation lemma: structural scarcity and neutral rank response derive the
competitive-displacement and removal witnesses consumed by the older proof
route.
-/

set_option autoImplicit false

namespace Legitimacy

namespace DecisionPipeline

variable {P : Type} [DecisionPipeline P]

/-- A claimant has a strictly weaker peer in the same profile. -/
def HasStrictlyWeakerPeer (claims : List ClaimQ) (k : ClaimantId) : Prop :=
  ∃ j, j ≠ k ∧ InClaims j claims ∧
    lookupStrength j claims < lookupStrength k claims

/-- A claimant is at the bottom of a nontrivial relative-strength class. This
is a positive rank condition, not a diagnostic failure. -/
def WeakestWithStrongerPeer (claims : List ClaimQ) (k : ClaimantId) : Prop :=
  InClaims k claims ∧
    (∀ j, InClaims j claims → lookupStrength k claims ≤ lookupStrength j claims) ∧
    ∃ j, j ≠ k ∧ InClaims j claims ∧
      lookupStrength k claims < lookupStrength j claims

/-- Context sensitivity: some fixed-own-strength claimant is treated
differently under a different surrounding claim profile. This is the broad
semantic sensitivity condition; the obstruction below uses the stronger
structural rank laws rather than this existential fact. -/
def PeerRelativeByContext (node : NodeOf P) : Prop :=
  ∃ (claims claims' : List ClaimQ) (k : ClaimantId),
    claims ≠ claims' ∧
    InClaims k claims ∧ InClaims k claims' ∧
    ClaimsDistinct claims ∧ ClaimsDistinct claims' ∧
    lookupStrength k claims = lookupStrength k claims' ∧
    evalNode node claims k ≠ evalNode node claims' k

/-- Individual admissibility: every claimant in the profile is accepted when
considered alone. -/
def IndividuallyAdmissible (node : NodeOf P) (claims : List ClaimQ) : Prop :=
  ∀ c ∈ claims, evalNode node [c] c.id = BinaryDecision.Permit

/-- Constructor data for the rank-ordered obstruction used by the compatibility
route. This is deliberately named as an obstruction generator rather than as a
natural-class field: structural allocator instances produce it transparently,
and node decisions are derived from the behavioral laws below. -/
structure ObstructionGenerator (claims : List ClaimQ) where
  displaced : ClaimantId
  affected : ClaimantId
  strengthened_strength : ℚ
  strengthened_strength_pos : 0 < strengthened_strength
  distinct_claimants : displaced ≠ affected
  displaced_in_claims : InClaims displaced claims
  affected_in_claims : InClaims affected claims
  affected_in_strengthened :
    InClaims affected
      (strengthenClaim displaced strengthened_strength
        strengthened_strength_pos claims)
  affected_in_removed :
    InClaims affected (removeClaimGraph displaced claims)
  strengthened_claims_distinct :
    ClaimsDistinct
      (strengthenClaim displaced strengthened_strength
        strengthened_strength_pos claims)
  removed_claims_distinct :
    ClaimsDistinct (removeClaimGraph displaced claims)
  strengthened_bound :
    ∀ c ∈ claims, c.id = displaced → c.strength ≤ strengthened_strength
  affected_strength_preserved :
    lookupStrength affected claims =
      lookupStrength affected
        (strengthenClaim displaced strengthened_strength
          strengthened_strength_pos claims)
  affected_has_weaker : HasStrictlyWeakerPeer claims affected
  displaced_weakest : WeakestWithStrongerPeer claims displaced
  affected_weakest_after_strengthening :
    WeakestWithStrongerPeer
      (strengthenClaim displaced strengthened_strength
        strengthened_strength_pos claims)
      affected
  affected_weakest_after_removal :
    WeakestWithStrongerPeer (removeClaimGraph displaced claims) affected

/-- Backward-compatible spelling retained for older local references. New
statements should use `ObstructionGenerator` to make the witness-bearing role
explicit. -/
abbrev OverSubscriptionData := ObstructionGenerator

/-- An over-subscribed profile contains a rank-ordered scarcity configuration
whose transformations make the same survivor become the weakest remaining peer.
The predicate is Prop-shaped for theorem statements, while the witness-bearing
data is explicitly scoped as an `ObstructionGenerator`. -/
def OverSubscribed (claims : List ClaimQ) : Prop :=
  ∃ _h : ObstructionGenerator claims, True

/-- Finite estate coupling: every individually admissible overloaded profile
has some claimant selected out by the scarce estate. -/
def FiniteEstateCoupled (node : NodeOf P) : Prop :=
  ∀ claims, ClaimsDistinct claims → OverSubscribed claims →
    IndividuallyAdmissible node claims →
      ∃ k, InClaims k claims ∧ evalNode node claims k = BinaryDecision.Deny

/-- Equal-strength claimants in a symmetric profile receive equal decisions. -/
def ClaimantSymmetric (node : NodeOf P) : Prop :=
  ∀ claims k j, ClaimsDistinct claims →
    InClaims k claims → InClaims j claims →
      lookupStrength k claims = lookupStrength j claims →
        evalNode node claims k = evalNode node claims j

/-- Positive own-response: having a strictly weaker peer is sufficient for
acceptance in a scarce peer-relative comparison. -/
def OwnStrengthResponsive (node : NodeOf P) : Prop :=
  ∀ claims k, ClaimsDistinct claims → InClaims k claims →
    HasStrictlyWeakerPeer claims k →
      evalNode node claims k = BinaryDecision.Permit

/-- Tie-neutral scarce selection: when scarcity makes a claimant the weakest
member of a nontrivial relative-strength class, the rule excludes that claimant
by rank rather than by claimant identity. -/
def TieBreakNeutral (node : NodeOf P) : Prop :=
  ∀ claims k, ClaimsDistinct claims → InClaims k claims →
    WeakestWithStrongerPeer claims k →
      evalNode node claims k = BinaryDecision.Deny

/-- Structural class for nontrivial symmetric scarce peer-relative binary
allocation. The fields are behavioral laws and positive non-vacuity/scarcity
conditions; they do not preload monotonicity or consistency violations. -/
class StructuralScarcePeerRelativeAllocator
    (node : NodeOf P) : Prop where
  peer_sensitive : PeerRelativeByContext node
  finite_estate : FiniteEstateCoupled node
  nontrivial_acceptance :
    ∃ claims k, ClaimsDistinct claims ∧ InClaims k claims ∧
      evalNode node claims k = BinaryDecision.Permit
  scarcity_pressure :
    ∃ claims, ClaimsDistinct claims ∧
      OverSubscribed claims ∧ IndividuallyAdmissible node claims
  symmetry : ClaimantSymmetric node
  positive_own_response : OwnStrengthResponsive node
  no_arbitrary_tie_break : TieBreakNeutral node

/-- Transparency theorem for the witness-bearing constructor: every structural
scarce peer-relative allocator instance exposes the obstruction generator it
uses through scarcity pressure. -/
theorem structural_scarce_peer_relative_allocator_obstructionGenerator
    {node : NodeOf P}
    (hstruct : StructuralScarcePeerRelativeAllocator node) :
    ∃ claims, ClaimsDistinct claims ∧ IndividuallyAdmissible node claims ∧
      ∃ _h : ObstructionGenerator claims, True := by
  rcases hstruct.scarcity_pressure with
    ⟨claims, hdistinct, hscarce, hadmissible⟩
  rcases hscarce with ⟨hgenerator, _⟩
  exact ⟨claims, hdistinct, hadmissible, hgenerator, True.intro⟩

/-- Public theorem-class spelling used by the paper-facing obstruction. -/
abbrev NontrivialSymmetricScarcePeerRelativeBinaryAllocator
    (node : NodeOf P) : Prop :=
  StructuralScarcePeerRelativeAllocator node

/-- Scarce symmetric peer-relative allocation derives a competitive
displacement witness: strengthening one claimant can push a different claimant
from accepted to excluded. -/
theorem scarce_symmetric_peer_allocator_has_competitive_displacement
    {node : NodeOf P}
    (hstruct : StructuralScarcePeerRelativeAllocator node) :
    ∃ (claims : List ClaimQ) (k j : ClaimantId) (s' : ℚ) (hs' : 0 < s'),
      k ≠ j ∧
      InClaims k claims ∧
      InClaims j claims ∧
      InClaims j (strengthenClaim k s' hs' claims) ∧
      ClaimsDistinct claims ∧
      ClaimsDistinct (strengthenClaim k s' hs' claims) ∧
      (∀ c ∈ claims, c.id = k → c.strength ≤ s') ∧
      lookupStrength j claims =
        lookupStrength j (strengthenClaim k s' hs' claims) ∧
      evalNode node claims j = BinaryDecision.Permit ∧
      evalNode node (strengthenClaim k s' hs' claims) j =
        BinaryDecision.Deny := by
  rcases hstruct.scarcity_pressure with
    ⟨claims, hdistinct, hscarce, _hadmissible⟩
  rcases hscarce with ⟨hscarce, _⟩
  refine
    ⟨claims, hscarce.displaced, hscarce.affected,
      hscarce.strengthened_strength, hscarce.strengthened_strength_pos,
      hscarce.distinct_claimants, hscarce.displaced_in_claims,
      hscarce.affected_in_claims, hscarce.affected_in_strengthened,
      hdistinct, hscarce.strengthened_claims_distinct,
      hscarce.strengthened_bound, hscarce.affected_strength_preserved,
      ?_, ?_⟩
  · exact hstruct.positive_own_response claims hscarce.affected hdistinct
      hscarce.affected_in_claims hscarce.affected_has_weaker
  · exact hstruct.no_arbitrary_tie_break
      (strengthenClaim hscarce.displaced hscarce.strengthened_strength
        hscarce.strengthened_strength_pos claims)
      hscarce.affected hscarce.strengthened_claims_distinct
      hscarce.affected_in_strengthened
      hscarce.affected_weakest_after_strengthening

/-- Scarce symmetric peer-relative allocation derives a reduction witness:
removing a rank-excluded claimant can make a previously accepted survivor
become excluded. -/
theorem scarce_symmetric_peer_allocator_has_reduction_violation
    {node : NodeOf P}
    (hstruct : StructuralScarcePeerRelativeAllocator node) :
    ∃ (claims : List ClaimQ) (k j : ClaimantId),
      k ≠ j ∧
      InClaims k claims ∧ InClaims j claims ∧
      ClaimsDistinct claims ∧
      evalNode node claims k = BinaryDecision.Deny ∧
      evalNode node claims j = BinaryDecision.Permit ∧
      evalNode node (removeClaimGraph k claims) j = BinaryDecision.Deny := by
  rcases hstruct.scarcity_pressure with
    ⟨claims, hdistinct, hscarce, _hadmissible⟩
  rcases hscarce with ⟨hscarce, _⟩
  refine
    ⟨claims, hscarce.displaced, hscarce.affected,
      hscarce.distinct_claimants, hscarce.displaced_in_claims,
      hscarce.affected_in_claims, hdistinct, ?_, ?_, ?_⟩
  · exact hstruct.no_arbitrary_tie_break claims hscarce.displaced hdistinct
      hscarce.displaced_in_claims hscarce.displaced_weakest
  · exact hstruct.positive_own_response claims hscarce.affected hdistinct
      hscarce.affected_in_claims hscarce.affected_has_weaker
  · exact hstruct.no_arbitrary_tie_break
      (removeClaimGraph hscarce.displaced claims)
      hscarce.affected hscarce.removed_claims_distinct
      hscarce.affected_in_removed
      hscarce.affected_weakest_after_removal

/-- Compatibility lift: the old witness-bearing peer-relative aggregator
predicate is derivable from the structural scarce peer-relative class. -/
theorem structural_scarce_peer_relative_allocator_implies_aggregator
    {node : NodeOf P}
    (hstruct : StructuralScarcePeerRelativeAllocator node) :
    IsPeerRelativeAggregator node :=
  ⟨scarce_symmetric_peer_allocator_has_competitive_displacement hstruct,
    scarce_symmetric_peer_allocator_has_reduction_violation hstruct⟩

end DecisionPipeline

/-- Root-facing spelling for the structural scarce peer-relative allocator
class. The implementation lives under `DecisionPipeline` because it is
polymorphic over the pipeline node type. -/
abbrev StructuralScarcePeerRelativeAllocator
    {P : Type} [DecisionPipeline P]
    (node : DecisionPipeline.NodeOf P) : Prop :=
  DecisionPipeline.StructuralScarcePeerRelativeAllocator node

/-- Root-facing spelling for the public theorem class. -/
abbrev NontrivialSymmetricScarcePeerRelativeBinaryAllocator
    {P : Type} [DecisionPipeline P]
    (node : DecisionPipeline.NodeOf P) : Prop :=
  DecisionPipeline.NontrivialSymmetricScarcePeerRelativeBinaryAllocator node

/-- Public headline obstruction: any nontrivial symmetric peer-relative binary
allocator under finite scarcity generates the consistency/solidarity/
monotonicity obstruction on a complete first-effective surface. -/
theorem nontrivial_symmetric_scarce_peer_relative_binary_allocators_obstructed
    {P : Type} [DecisionPipeline P]
    (G pref tail : P) (node : DecisionPipeline.NodeOf P)
    (hstruct : NontrivialSymmetricScarcePeerRelativeBinaryAllocator node)
    (heffective : DecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : DecisionPipeline.CompleteTailForNode node tail) :
    ¬ (GraphConsistencyP G ∧ GraphSolidarityP G ∧ GraphMonotonicityP G) :=
  binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction
    G pref tail node
    (DecisionPipeline.structural_scarce_peer_relative_allocator_implies_aggregator
      hstruct)
    heffective hcomplete

private def contextOnlyA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
private def contextOnlyB : ClaimQ := ⟨1, 1 / 2, by norm_num, []⟩
private def contextOnlyC : ClaimQ := ⟨2, 3 / 4, by norm_num, []⟩

private def contextOnlyClaims3 : List ClaimQ :=
  [contextOnlyA, contextOnlyB, contextOnlyC]

private def contextOnlyClaims2 : List ClaimQ :=
  [contextOnlyA, contextOnlyB]

/-- Pure contextual peer-relativity is too weak: the length-sensitive survivor
node is context-sensitive but does not provide the competitive-displacement
component required by the old aggregator predicate. -/
theorem peer_relative_by_context_alone_insufficient :
    ∃ node : GovernanceNodeFn,
      DecisionPipeline.PeerRelativeByContext (P := GovernanceGraph) node ∧
        ¬ DecisionPipeline.IsPeerRelativeAggregator
          (P := GovernanceGraph) node := by
  refine ⟨lengthThreeSurvivorNode, ?_,
    lengthThreeSurvivorNode_not_isPeerRelativeAggregator⟩
  refine
    ⟨contextOnlyClaims3, contextOnlyClaims2, 1, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · unfold ClaimsDistinct contextOnlyClaims3 contextOnlyA contextOnlyB
      contextOnlyC
    show ([0, 1, 2] : List Nat).Nodup
    decide
  · unfold ClaimsDistinct contextOnlyClaims2 contextOnlyA contextOnlyB
    show ([0, 1] : List Nat).Nodup
    decide
  · native_decide
  · native_decide

/-- Asymmetric context-sensitive scarcity gate: claimant `1` is permitted only
on three-claimant profiles; everyone else is denied. -/
def asymmetricLengthThreeScarcityNode : GovernanceNodeFn := fun claims k =>
  if k = 1 ∧ claims.length = 3 then
    BinaryDecision.Permit
  else
    BinaryDecision.Deny

private theorem asymmetricLengthThreeScarcityNode_peerRelativeByContext :
    DecisionPipeline.PeerRelativeByContext
      (P := GovernanceGraph) asymmetricLengthThreeScarcityNode := by
  refine
    ⟨contextOnlyClaims3, contextOnlyClaims2, 1, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · unfold ClaimsDistinct contextOnlyClaims3 contextOnlyA contextOnlyB
      contextOnlyC
    show ([0, 1, 2] : List Nat).Nodup
    decide
  · unfold ClaimsDistinct contextOnlyClaims2 contextOnlyA contextOnlyB
    show ([0, 1] : List Nat).Nodup
    decide
  · native_decide
  · native_decide

private theorem asymmetricLengthThreeScarcityNode_finiteEstateCoupled :
    DecisionPipeline.FiniteEstateCoupled
      (P := GovernanceGraph) asymmetricLengthThreeScarcityNode := by
  intro claims _hdistinct hscarce _hadmissible
  rcases hscarce with ⟨hscarce, _⟩
  by_cases hdisplacedPermit :
      hscarce.displaced = 1 ∧ claims.length = 3
  · refine ⟨hscarce.affected, hscarce.affected_in_claims, ?_⟩
    have haffected_ne_one : hscarce.affected ≠ 1 := by
      intro haffected
      exact hscarce.distinct_claimants
        (by rw [hdisplacedPermit.1, haffected])
    change
      (if hscarce.affected = 1 ∧ claims.length = 3 then
        BinaryDecision.Permit
      else
        BinaryDecision.Deny) = BinaryDecision.Deny
    exact if_neg (by
      intro hpermit
      exact haffected_ne_one hpermit.1)
  · refine ⟨hscarce.displaced, hscarce.displaced_in_claims, ?_⟩
    change
      (if hscarce.displaced = 1 ∧ claims.length = 3 then
        BinaryDecision.Permit
      else
        BinaryDecision.Deny) = BinaryDecision.Deny
    exact if_neg hdisplacedPermit

private def asymmetricSymmetryA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
private def asymmetricSymmetryB : ClaimQ := ⟨1, 1 / 2, by norm_num, []⟩
private def asymmetricSymmetryC : ClaimQ := ⟨2, 1 / 2, by norm_num, []⟩

private def asymmetricSymmetryClaims : List ClaimQ :=
  [asymmetricSymmetryA, asymmetricSymmetryB, asymmetricSymmetryC]

private theorem asymmetricLengthThreeScarcityNode_not_symmetric :
    ¬ DecisionPipeline.ClaimantSymmetric
      (P := GovernanceGraph) asymmetricLengthThreeScarcityNode := by
  intro hsymm
  have hdistinct : ClaimsDistinct asymmetricSymmetryClaims := by
    unfold ClaimsDistinct asymmetricSymmetryClaims asymmetricSymmetryA
      asymmetricSymmetryB asymmetricSymmetryC
    show ([0, 1, 2] : List Nat).Nodup
    decide
  have hsame :
      lookupStrength 1 asymmetricSymmetryClaims =
        lookupStrength 2 asymmetricSymmetryClaims := by
    native_decide
  have heq :=
    hsymm asymmetricSymmetryClaims 1 2 hdistinct
      (by native_decide) (by native_decide) hsame
  have hpermit :
      DecisionPipeline.evalNode
          (P := GovernanceGraph) asymmetricLengthThreeScarcityNode
          asymmetricSymmetryClaims 1 =
        BinaryDecision.Permit := by
    native_decide
  have hdeny :
      DecisionPipeline.evalNode
          (P := GovernanceGraph) asymmetricLengthThreeScarcityNode
          asymmetricSymmetryClaims 2 =
        BinaryDecision.Deny := by
    native_decide
  rw [hpermit, hdeny] at heq
  exact BinaryDecision.noConfusion heq

/-- Peer-context plus finite-estate coupling still does not identify the
structural obstruction class without symmetry: an arbitrary claimant-id gate is
context-sensitive and always excludes someone under overloaded profiles, while
explicitly violating claimant symmetry. -/
theorem peer_relative_with_finite_estate_without_symmetry_insufficient :
    ∃ node : GovernanceNodeFn,
      DecisionPipeline.PeerRelativeByContext (P := GovernanceGraph) node ∧
        DecisionPipeline.FiniteEstateCoupled (P := GovernanceGraph) node ∧
          ¬ DecisionPipeline.ClaimantSymmetric
            (P := GovernanceGraph) node :=
  ⟨asymmetricLengthThreeScarcityNode,
    asymmetricLengthThreeScarcityNode_peerRelativeByContext,
    asymmetricLengthThreeScarcityNode_finiteEstateCoupled,
    asymmetricLengthThreeScarcityNode_not_symmetric⟩

/-- Upstream deny-all gates remain vacuous countermodels to any syntactic
"contains a peer-relative stage" theorem. -/
theorem upstream_deny_all_gate_vacuous_countermodel :
    ∃ G : GovernanceGraph, HasPeerRelativeStage G ∧ AllLegitimacyAxioms G :=
  hasPeerRelativeStage_does_not_force_impossibility

end Legitimacy
