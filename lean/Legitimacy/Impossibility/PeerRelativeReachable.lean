/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.StructuralPeerRelative

/-!
# Reachable peer-relative decisive stages

This module names the pipeline-class generalization around the existing
structural scarce peer-relative obstruction. The load-bearing stage no longer
has to be presented as the first syntactic stage of the whole pipeline: it may
sit behind a transparent prefix and in front of a non-denying suffix.
-/

set_option autoImplicit false

namespace Legitimacy

namespace DecisionPipeline

variable {P : Type} [DecisionPipeline P]

/-- A prefix is transparent when the pipeline instance's transparent-prefix
semantics erase it from external decisions. -/
class TransparentPrefix (pref : P) : Prop where
  transparent : DecisionPipeline.transparentPrefix (P := P) pref

/-- A suffix is non-denying for an exposed stage when it preserves every permit
emitted by that stage on the forwarded profile. -/
class NonDenyingSuffix (node : NodeOf P) (suffix : P) : Prop where
  preserves_permits : CompleteTailForNode node suffix

/-- Explicit composition of a prefix, exposed decisive node, and suffix. -/
def composedPipeline (pref : P) (node : NodeOf P) (suffix : P) : P :=
  DecisionPipeline.append pref (DecisionPipeline.cons node suffix)

/-- Reachability class for a structural peer-relative decisive stage in the
middle of a pipeline. The prefix may perform transparent governance work, the
node carries the scarce peer-relative obstruction, and the suffix may add
review/observability/logging provided it does not revoke node permits. -/
def ReachablePeerRelativeDecisiveStage
    (G pref : P) (node : NodeOf P) (suffix : P) : Prop :=
  TransparentPrefix pref ∧
    StructuralScarcePeerRelativeAllocator node ∧
      NonDenyingSuffix node suffix ∧
        G = composedPipeline pref node suffix

/-- Transparent-prefix wrappers expose the existing effective-surface
transparent-prefix fact. -/
lemma TransparentPrefix.effectiveSurface
    {pref suffix : P} {node : NodeOf P}
    (hprefix : TransparentPrefix pref) :
    EffectiveSurfaceForNode node
      (composedPipeline pref node suffix) pref suffix :=
  ⟨rfl, hprefix.transparent⟩

/-- Non-denying suffix wrappers expose the existing complete-tail fact. -/
lemma NonDenyingSuffix.completeTailForNode
    {suffix : P} {node : NodeOf P}
    (hsuffix : NonDenyingSuffix node suffix) :
    CompleteTailForNode node suffix :=
  hsuffix.preserves_permits

/-- A reachable stage supplies the effective first-stage surface consumed by
the existing complete-surface obstruction. -/
lemma ReachablePeerRelativeDecisiveStage.effectiveSurfaceForNode
    {G pref suffix : P} {node : NodeOf P}
    (hreach : ReachablePeerRelativeDecisiveStage G pref node suffix) :
    EffectiveSurfaceForNode node G pref suffix := by
  rcases hreach with ⟨hprefix, _hstruct, _hsuffix, hshape⟩
  rw [hshape]
  exact hprefix.effectiveSurface

/-- A reachable stage supplies the non-denying complete-tail fact consumed by
the existing complete-surface obstruction. -/
lemma ReachablePeerRelativeDecisiveStage.completeTailForNode
    {G pref suffix : P} {node : NodeOf P}
    (hreach : ReachablePeerRelativeDecisiveStage G pref node suffix) :
    CompleteTailForNode node suffix :=
  hreach.2.2.1.completeTailForNode

/-- A reachable stage exposes its structural scarce peer-relative node. -/
lemma ReachablePeerRelativeDecisiveStage.structural
    {G pref suffix : P} {node : NodeOf P}
    (hreach : ReachablePeerRelativeDecisiveStage G pref node suffix) :
    StructuralScarcePeerRelativeAllocator node :=
  hreach.2.1

end DecisionPipeline

/-- Root-facing spelling for the reachable-stage class. -/
abbrev ReachablePeerRelativeDecisiveStage
    {P : Type} [DecisionPipeline P]
    (G pref : P) (node : DecisionPipeline.NodeOf P) (suffix : P) : Prop :=
  DecisionPipeline.ReachablePeerRelativeDecisiveStage G pref node suffix

/-- Reachable-stage wrapper around the core scarce peer-relative obstruction:
under a transparent prefix and non-denying suffix, the reached structural
allocator inherits the same consistency/solidarity/monotonicity obstruction. -/
theorem reachable_peer_relative_decisive_stage_obstructs_diagnostics
    {P : Type} [DecisionPipeline P]
    (G pref : P) (node : DecisionPipeline.NodeOf P) (suffix : P)
    (hreach : ReachablePeerRelativeDecisiveStage G pref node suffix) :
    ¬ (GraphConsistencyP G ∧ GraphSolidarityP G ∧ GraphMonotonicityP G) :=
  nontrivial_symmetric_scarce_peer_relative_binary_allocators_obstructed
    G pref suffix node
    (DecisionPipeline.ReachablePeerRelativeDecisiveStage.structural hreach)
    (DecisionPipeline.ReachablePeerRelativeDecisiveStage.effectiveSurfaceForNode
      hreach)
    (DecisionPipeline.ReachablePeerRelativeDecisiveStage.completeTailForNode
      hreach)

/-- Strong reachable-stage corollary: the same reachable structural surface
forces both individual sacrifices supplied by the complete-surface obstruction,
not merely failure of the three-diagnostic conjunction. -/
theorem reachable_peer_relative_decisive_stage_forces_consistency_and_monotonicity_sacrifice
    {P : Type} [DecisionPipeline P]
    (G pref : P) (node : DecisionPipeline.NodeOf P) (suffix : P)
    (hreach : ReachablePeerRelativeDecisiveStage G pref node suffix) :
    ¬ GraphConsistencyP G ∧ ¬ GraphMonotonicityP G :=
  binaryDecisionPipeline_isPeerRelativeAggregator_complete_obstruction
    G pref suffix node
    (DecisionPipeline.structural_scarce_peer_relative_allocator_implies_aggregator
      (DecisionPipeline.ReachablePeerRelativeDecisiveStage.structural hreach))
    (DecisionPipeline.ReachablePeerRelativeDecisiveStage.effectiveSurfaceForNode
      hreach)
    (DecisionPipeline.ReachablePeerRelativeDecisiveStage.completeTailForNode
      hreach)

/-- Complete first-effective structural surfaces are the identity case of the
reachable-stage class: the old transparent-prefix and complete-tail hypotheses
become the new transparent-prefix and non-denying-suffix wrappers. -/
theorem complete_first_effective_implies_reachable_peer_relative_decisive
    {P : Type} [DecisionPipeline P]
    (G pref : P) (node : DecisionPipeline.NodeOf P) (suffix : P)
    (hstruct : StructuralScarcePeerRelativeAllocator node)
    (heffective : DecisionPipeline.EffectiveSurfaceForNode node G pref suffix)
    (hcomplete : DecisionPipeline.CompleteTailForNode node suffix) :
    ReachablePeerRelativeDecisiveStage G pref node suffix :=
  ⟨⟨heffective.2⟩, hstruct, ⟨hcomplete⟩, heffective.1⟩

/-- The retained complete first-effective theorem factors through the
reachable-stage theorem. This is the formal special-case route used by the
paper text: no old theorem is deleted, and the old hypotheses are repackaged
into the broader reachable-stage statement. -/
theorem complete_first_effective_obstructs_diagnostics_via_reachable
    {P : Type} [DecisionPipeline P]
    (G pref : P) (node : DecisionPipeline.NodeOf P) (suffix : P)
    (hstruct : StructuralScarcePeerRelativeAllocator node)
    (heffective : DecisionPipeline.EffectiveSurfaceForNode node G pref suffix)
    (hcomplete : DecisionPipeline.CompleteTailForNode node suffix) :
    ¬ (GraphConsistencyP G ∧ GraphSolidarityP G ∧ GraphMonotonicityP G) :=
  reachable_peer_relative_decisive_stage_obstructs_diagnostics G pref node
    suffix
    (complete_first_effective_implies_reachable_peer_relative_decisive
      G pref node suffix hstruct heffective hcomplete)

/-! ## Necessity countermodels -/

private def reachableDenyAllNode : GovernanceNodeFn :=
  fun _ _ => BinaryDecision.Deny

private def denyingPrefixPeerGraph : GovernanceGraph :=
  [reachableDenyAllNode, peerRelativeNode]

private def peerThenDenyingSuffixGraph : GovernanceGraph :=
  [peerRelativeNode, reachableDenyAllNode]

private lemma denyingPrefixPeerGraph_decide
    (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide denyingPrefixPeerGraph claims k = BinaryDecision.Deny := by
  simp [denyingPrefixPeerGraph, reachableDenyAllNode, graphDecide]

private lemma peerThenDenyingSuffixGraph_decide
    (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide peerThenDenyingSuffixGraph claims k = BinaryDecision.Deny := by
  cases hpeer : peerRelativeNode claims k <;>
    simp [peerThenDenyingSuffixGraph, reachableDenyAllNode, graphDecide, hpeer]

private theorem allDeny_consistent
    {G : GovernanceGraph}
    (hdeny : ∀ claims k, graphDecide G claims k = BinaryDecision.Deny) :
    GraphConsistency G := by
  intro claims k j _ _ _ _ _
  rw [hdeny claims j, hdeny (removeClaimGraph k claims) j]

private theorem allDeny_solidary
    {G : GovernanceGraph}
    (hdeny : ∀ claims k, graphDecide G claims k = BinaryDecision.Deny) :
    GraphSolidarity G := by
  intro claims α hα j _
  change graphDecide G claims j =
    graphDecide G
      (claims.map
        (fun c => ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩))
      j
  rw [hdeny claims j,
    hdeny
      (claims.map
        (fun c => ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩))
      j]

private theorem allDeny_monotone
    {G : GovernanceGraph}
    (hdeny : ∀ claims k, graphDecide G claims k = BinaryDecision.Deny) :
    GraphMonotonicity G := by
  intro claims _ _ _ j _ _ _ hpermit
  rw [hdeny claims j] at hpermit
  exact BinaryDecision.noConfusion hpermit

private theorem allDeny_strategyproof
    {G : GovernanceGraph}
    (hdeny : ∀ claims k, graphDecide G claims k = BinaryDecision.Deny) :
    GraphStrategyproofness G := by
  intro claims k s_r hs_r _ _ hpermit
  rw [hdeny (strengthenClaim k s_r hs_r claims) k] at hpermit
  exact BinaryDecision.noConfusion hpermit

private theorem allDeny_allLegitimacyAxioms
    {G : GovernanceGraph}
    (hdeny : ∀ claims k, graphDecide G claims k = BinaryDecision.Deny) :
    AllLegitimacyAxioms G :=
  ⟨allDeny_consistent hdeny, allDeny_solidary hdeny,
    allDeny_monotone hdeny, allDeny_strategyproof hdeny⟩

private theorem denyingPrefix_not_transparent :
    ¬ DecisionPipeline.TransparentPrefix
      (P := GovernanceGraph) [reachableDenyAllNode] := by
  intro hprefix
  have h :=
    hprefix.transparent reachableDenyAllNode (List.Mem.head [])
      ([] : List ClaimQ) 0
  have hbad : BinaryDecision.Deny = BinaryDecision.Permit := by
    change BinaryDecision.Deny = BinaryDecision.Permit at h
    exact h
  exact BinaryDecision.noConfusion hbad

/-- Dropping transparent-prefix reachability is unsound: a deny-all prefix can
mask a downstream peer-relative stage while the whole graph satisfies all graph
legitimacy axioms. -/
theorem without_transparentPrefix_denying_prefix_masks_obstruction :
    ∃ (G pref suffix : GovernanceGraph),
      G = DecisionPipeline.composedPipeline
        (P := GovernanceGraph) pref peerRelativeNode suffix ∧
        ¬ DecisionPipeline.TransparentPrefix (P := GovernanceGraph) pref ∧
          AllLegitimacyAxioms G :=
  ⟨denyingPrefixPeerGraph, [reachableDenyAllNode], [], rfl,
    denyingPrefix_not_transparent,
    allDeny_allLegitimacyAxioms denyingPrefixPeerGraph_decide⟩

private def nonDenyingSuffixWitnessClaim : ClaimQ :=
  ⟨0, 1, by norm_num, []⟩

private def nonDenyingSuffixWitnessClaims : List ClaimQ :=
  [nonDenyingSuffixWitnessClaim]

private theorem peerRelativeNode_permits_suffix_witness :
    peerRelativeNode nonDenyingSuffixWitnessClaims 0 =
      BinaryDecision.Permit := by
  native_decide

private theorem empty_governanceGraph_transparentPrefix :
    DecisionPipeline.TransparentPrefix (P := GovernanceGraph) [] :=
  ⟨by intro _ hmem; cases hmem⟩

private theorem denyingSuffix_not_nonDenying :
    ¬ DecisionPipeline.NonDenyingSuffix
      (P := GovernanceGraph) peerRelativeNode [reachableDenyAllNode] := by
  intro hsuffix
  have hpermit :=
    hsuffix.preserves_permits nonDenyingSuffixWitnessClaims 0
      peerRelativeNode_permits_suffix_witness
  have hpermitGraph :
      graphDecide [reachableDenyAllNode]
          (filterPermitted peerRelativeNode nonDenyingSuffixWitnessClaims) 0 =
        BinaryDecision.Permit := by
    change graphDecide [reachableDenyAllNode]
        (filterPermitted peerRelativeNode nonDenyingSuffixWitnessClaims) 0 =
      BinaryDecision.Permit at hpermit
    exact hpermit
  have hdeny :
      graphDecide [reachableDenyAllNode]
          (filterPermitted peerRelativeNode nonDenyingSuffixWitnessClaims) 0 =
        BinaryDecision.Deny := by
    simp [reachableDenyAllNode, graphDecide]
  rw [hpermitGraph] at hdeny
  exact BinaryDecision.noConfusion hdeny

/-- Dropping the non-denying-suffix condition is unsound: a permit-revoking
suffix can collapse the whole graph to deny-all behavior, cancelling the
peer-relative obstruction. -/
theorem without_nonDenyingSuffix_permit_revoking_suffix_masks_obstruction :
    ∃ (G pref suffix : GovernanceGraph),
      DecisionPipeline.TransparentPrefix (P := GovernanceGraph) pref ∧
        G = DecisionPipeline.composedPipeline
          (P := GovernanceGraph) pref peerRelativeNode suffix ∧
          ¬ DecisionPipeline.NonDenyingSuffix
            (P := GovernanceGraph) peerRelativeNode suffix ∧
            AllLegitimacyAxioms G :=
  ⟨peerThenDenyingSuffixGraph, [], [reachableDenyAllNode],
    empty_governanceGraph_transparentPrefix, rfl, denyingSuffix_not_nonDenying,
    allDeny_allLegitimacyAxioms peerThenDenyingSuffixGraph_decide⟩

/-- The transparent-prefix and non-denying-suffix qualifiers are individually
necessary: deleting either one admits a concrete all-deny countermodel. -/
theorem reachable_stage_qualifiers_individually_necessary :
    (∃ (G pref suffix : GovernanceGraph),
      G = DecisionPipeline.composedPipeline
        (P := GovernanceGraph) pref peerRelativeNode suffix ∧
        ¬ DecisionPipeline.TransparentPrefix (P := GovernanceGraph) pref ∧
          AllLegitimacyAxioms G) ∧
    (∃ (G pref suffix : GovernanceGraph),
      DecisionPipeline.TransparentPrefix (P := GovernanceGraph) pref ∧
        G = DecisionPipeline.composedPipeline
          (P := GovernanceGraph) pref peerRelativeNode suffix ∧
          ¬ DecisionPipeline.NonDenyingSuffix
            (P := GovernanceGraph) peerRelativeNode suffix ∧
            AllLegitimacyAxioms G) :=
  ⟨without_transparentPrefix_denying_prefix_masks_obstruction,
    without_nonDenyingSuffix_permit_revoking_suffix_masks_obstruction⟩

end Legitimacy
