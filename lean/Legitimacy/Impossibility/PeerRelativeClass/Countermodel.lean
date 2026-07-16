/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.PeerRelativeClass.Predicates

/-!
# Peer-Relative Countermodels

This module builds concrete governance graphs that separate peer-relative
surface shape from the graph-diagnostic properties. The witnesses show that
some combinations can satisfy consistency, solidarity, or monotonicity while
failing another diagnostic obligation.

The scope is countermodel construction for the peer-relative class. It does not
prove the complete obstruction theorem; that proof is layered through the
separate witness and obstruction modules.
-/

set_option autoImplicit false

namespace Legitimacy

private def denyAllNode : GovernanceNodeFn := fun _ _ => BinaryDecision.Deny

private def denyAllPeerGraph : GovernanceGraph := [denyAllNode, peerRelativeNode]

private lemma denyAllPeerGraph_decide
    (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide denyAllPeerGraph claims k = BinaryDecision.Deny := by
  simp [denyAllPeerGraph, denyAllNode, graphDecide]

private lemma denyAllPeerGraph_consistent :
    GraphConsistency denyAllPeerGraph := by
  intro claims k j _ _ _ _ _
  rw [denyAllPeerGraph_decide claims j,
    denyAllPeerGraph_decide (removeClaimGraph k claims) j]

private lemma denyAllPeerGraph_solidary :
    GraphSolidarity denyAllPeerGraph := by
  intro claims α hα j _
  change graphDecide denyAllPeerGraph claims j =
    graphDecide denyAllPeerGraph
      (claims.map (fun c => ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)) j
  rw [denyAllPeerGraph_decide claims j,
    denyAllPeerGraph_decide
      (claims.map (fun c => ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)) j]

private lemma denyAllPeerGraph_monotone :
    GraphMonotonicity denyAllPeerGraph := by
  intro claims _ _ _ j _ _ _ hpermit
  rw [denyAllPeerGraph_decide claims j] at hpermit
  exact BinaryDecision.noConfusion hpermit

private lemma denyAllPeerGraph_strategyproof :
    GraphStrategyproofness denyAllPeerGraph := by
  intro claims k s_r hs_r _ _ hpermit
  rw [denyAllPeerGraph_decide (strengthenClaim k s_r hs_r claims) k] at hpermit
  exact BinaryDecision.noConfusion hpermit

private lemma denyAllPeerGraph_has_peerRelativeStage :
    HasPeerRelativeStage denyAllPeerGraph := by
  exact List.Mem.tail _ (List.Mem.head _)

private lemma denyAllPeerGraph_allAxioms :
    AllLegitimacyAxioms denyAllPeerGraph :=
  ⟨denyAllPeerGraph_consistent, denyAllPeerGraph_solidary,
    denyAllPeerGraph_monotone, denyAllPeerGraph_strategyproof⟩

/-- The unqualified syntactic class is too broad: merely containing
`peerRelativeNode` does not force impossibility. A deny-all head stage makes the
peer-relative stage unreachable and satisfies all four graph-level axioms. -/
theorem hasPeerRelativeStage_does_not_force_impossibility :
    ∃ G : GovernanceGraph, HasPeerRelativeStage G ∧ AllLegitimacyAxioms G :=
  ⟨denyAllPeerGraph, denyAllPeerGraph_has_peerRelativeStage,
    denyAllPeerGraph_allAxioms⟩

end Legitimacy
