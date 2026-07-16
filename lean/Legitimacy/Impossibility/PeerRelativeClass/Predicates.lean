/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.AxiomIndependence
import Legitimacy.Diagnostics.DecisionSystem
import Legitimacy.Results.Impossibility
import Mathlib.Tactic.NormNum

/-!
# Quantified peer-relative class impossibility

The bare claim "any graph containing a peer-relative stage is impossible" is
false: an upstream deny-all gate can short-circuit the peer-relative stage while
satisfying the graph axioms vacuously. The honest quantified theorem therefore
uses an unbundled class predicate:

* `PeerRelativeHead G tail`: the pipeline begins with `peerRelativeNode`;
* `CompletePeerRelativeTail tail`: every claimant permitted by the peer-relative
  head remains permitted by the downstream tail on the forwarded profile.
* `EffectivePeerRelativeSurface G pref tail`: the pipeline may have an
  arbitrary transparent prefix before its first effective peer-relative surface.

Under these two non-vacuous hypotheses, the full pipeline is decision-equivalent
to the canonical singleton `peerGraph`, so the concrete peer-graph impossibility
lifts to the quantified class.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A graph has a peer-relative head when its first stage is exactly
`peerRelativeNode`, with the remaining stages exposed as `tail`. -/
def PeerRelativeHead (G : GovernanceGraph) (tail : GovernanceGraph) : Prop :=
  G = peerRelativeNode :: tail

/-- A governance node is peer-relative when a claimant's decision can depend on
the surrounding claim profile, not only on that claimant's own reported
strength. The distinctness hypotheses match the graph-diagnostic semantics. -/
def IsPeerRelativeNode (node : GovernanceNodeFn) : Prop :=
  ∃ (claims claims' : List ClaimQ) (k : ClaimantId),
    claims ≠ claims' ∧
    InClaims k claims ∧ InClaims k claims' ∧
    ClaimsDistinct claims ∧ ClaimsDistinct claims' ∧
    lookupStrength k claims = lookupStrength k claims' ∧
    node claims k ≠ node claims' k

/-- Strengthened peer-relative aggregator predicate. The original
`IsPeerRelativeNode` records context-dependence but is too weak to derive a
diagnostic obstruction: its two witness profiles need not be related by an
admissible one-claimant strength change or removal. This predicate records two
concrete witness components: strengthening one claimant can flip a different
claimant from Permit to Deny while preserving the affected claimant's own
reported strength, and removing a denied claimant can flip a surviving claimant
from Permit to Deny. -/
def IsPeerRelativeAggregator (node : GovernanceNodeFn) : Prop :=
  BinaryDecisionPipeline.IsPeerRelativeAggregator
    (P := GovernanceGraph) node

/-- Every peer-relative aggregator is peer-relative in the broader contextual
dependence sense. -/
lemma IsPeerRelativeAggregator.isPeerRelativeNode :
    ∀ node, IsPeerRelativeAggregator node → IsPeerRelativeNode node := by
  intro node hn
  rcases hn.1 with
    ⟨claims, k, j, s', hs', _hkj, _hk, hj, hj', hdist, hdist', _hle,
      hsame, hpermit, hdeny⟩
  refine ⟨claims, strengthenClaim k s' hs' claims, j, ?_, hj, hj',
    hdist, hdist', hsame, ?_⟩
  · intro heq
    have hpermit' : node claims j = BinaryDecision.Permit := by
      simpa [BinaryDecisionPipeline.evalNode] using hpermit
    have hdeny' :
        node (strengthenClaim k s' hs' claims) j = BinaryDecision.Deny := by
      simpa [BinaryDecisionPipeline.evalNode] using hdeny
    have hnodeeq :
        node claims j = node (strengthenClaim k s' hs' claims) j :=
      congrArg (fun xs => node xs j) heq
    rw [hpermit', hdeny'] at hnodeeq
    exact BinaryDecision.noConfusion hnodeeq
  · have hpermit' : node claims j = BinaryDecision.Permit := by
      simpa [BinaryDecisionPipeline.evalNode] using hpermit
    have hdeny' :
        node (strengthenClaim k s' hs' claims) j = BinaryDecision.Deny := by
      simpa [BinaryDecisionPipeline.evalNode] using hdeny
    rw [hpermit', hdeny']
    intro h
    exact BinaryDecision.noConfusion h

/-- A node is transparent when it permits every claimant on every profile. Such a
node may still exist as a logging, observation, or pass-through governance stage,
but it does not alter the binary decision surface or the forwarded claim set. -/
def TransparentNode (node : GovernanceNodeFn) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId),
    node claims k = BinaryDecision.Permit

/-- A transparent prefix is a finite sequence of stages that all permit all
claimants. This is the formally admissible "normalization" before the first
effective peer-relative decision surface. -/
def TransparentPrefix (pref : GovernanceGraph) : Prop :=
  ∀ node, List.Mem node pref → TransparentNode node

/-- The first effective peer-relative surface class: after erasing a transparent
prefix, the first decision-relevant stage is the peer-relative gate. This
strictly generalizes `PeerRelativeHead` while still excluding the deny-all
short-circuit countermodel. -/
def EffectivePeerRelativeSurface
    (G pref tail : GovernanceGraph) : Prop :=
  G = List.append pref (peerRelativeNode :: tail) ∧ TransparentPrefix pref

/-- A peer-relative tail is complete when it never revokes a claimant that the
peer-relative head permitted on the original profile. This is the paper-facing
strengthening that rules out vacuous short-circuit countermodels: downstream
stages may refine implementation, but not narrow the peer-relative gate. -/
def CompletePeerRelativeTail (tail : GovernanceGraph) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId),
    peerRelativeNode claims k = BinaryDecision.Permit →
    graphDecide tail (filterPermitted peerRelativeNode claims) k =
      BinaryDecision.Permit

/-- Named class predicate for complete pipelines whose first decision-relevant
surface is peer-relative after erasing a transparent prefix. -/
def CompleteFirstEffectivePeerRelativeSurfaceClass
    (G pref tail : GovernanceGraph) : Prop :=
  EffectivePeerRelativeSurface G pref tail ∧ CompletePeerRelativeTail tail

/-- Generalized first-effective surface for an arbitrary node. This is the
shape that an eventual abstract peer-relative-node obstruction must consume. -/
def EffectiveSurfaceForNode
    (node : GovernanceNodeFn) (G pref tail : GovernanceGraph) : Prop :=
  G = List.append pref (node :: tail) ∧ TransparentPrefix pref

/-- Generalized complete-tail predicate for an arbitrary first effective node:
downstream stages preserve every permit granted by that node on the forwarded
profile. -/
def CompleteTailForNode (node : GovernanceNodeFn) (tail : GovernanceGraph) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId),
    node claims k = BinaryDecision.Permit →
    graphDecide tail (filterPermitted node claims) k =
      BinaryDecision.Permit

/-- The exact per-node obstruction still needed to lift from the canonical
median peer-relative gate to all abstract peer-relative nodes. It is a
proposition, not an axiom: future work must prove it from `IsPeerRelativeNode`
or strengthen the predicate until it is true. -/
def CompleteFirstEffectiveNodeObstruction (node : GovernanceNodeFn) : Prop :=
  ∀ (G pref tail : GovernanceGraph),
    EffectiveSurfaceForNode node G pref tail →
    CompleteTailForNode node tail →
    ¬ (GraphConsistency G ∧ GraphSolidarity G ∧ GraphMonotonicity G)

/-- The broad syntactic predicate: `peerRelativeNode` appears somewhere in the
pipeline. This is intentionally weak, and the countermodel below shows it is
not enough for a universal impossibility theorem. -/
def HasPeerRelativeStage (G : GovernanceGraph) : Prop :=
  List.Mem peerRelativeNode G

end Legitimacy
