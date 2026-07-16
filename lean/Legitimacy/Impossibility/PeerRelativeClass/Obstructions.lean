/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.PeerRelativeClass.Witnesses

/-!
# Peer-Relative Obstructions

This module turns peer-relative node witnesses into graph-level obstruction
theorems. It records both the conditional abstract-node obstruction and the
concrete bridge from transparent prefixes and complete tails to failure of the
three graph diagnostics.

The scope is the peer-relative obstruction layer. It depends on supplied
witness obligations and does not assert that every arbitrary governance graph
contains such a surface.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Conditional abstract-node obstruction. This theorem is deliberately
conditional on the per-node obstruction property above; it records the target
shape without introducing an axiom or pretending that arbitrary peer-relativity
alone has been discharged. -/
theorem isPeerRelativeNode_complete_obstruction_conditional
    (node : GovernanceNodeFn)
    (_hn : IsPeerRelativeNode node)
    (hobstruction : CompleteFirstEffectiveNodeObstruction node)
    (G pref tail : GovernanceGraph)
    (h : EffectiveSurfaceForNode node G pref tail ∧
      CompleteTailForNode node tail) :
    ¬ (GraphConsistency G ∧ GraphSolidarity G ∧ GraphMonotonicity G) :=
  hobstruction G pref tail h.1 h.2

private lemma filterPermitted_transparent
    {node : GovernanceNodeFn}
    (hnode : TransparentNode node)
    (claims : List ClaimQ) :
    filterPermitted node claims = claims := by
  unfold filterPermitted
  apply List.filter_eq_self.mpr
  intro c _
  simp [hnode claims c.id]

private lemma graphDecide_transparentPrefix_append
    (pref rest : GovernanceGraph)
    (hpref : TransparentPrefix pref)
    (claims : List ClaimQ)
    (k : ClaimantId) :
    graphDecide (List.append pref rest) claims k = graphDecide rest claims k := by
  induction pref generalizing claims with
  | nil =>
      simp
  | cons node pref ih =>
      have hnode : TransparentNode node :=
        hpref node List.mem_cons_self
      have htail : TransparentPrefix pref := by
        intro n hn
        exact hpref n (List.mem_cons_of_mem node hn)
      calc
        graphDecide ((node :: pref).append rest) claims k =
            graphDecide (pref.append rest) (filterPermitted node claims) k := by
          simp [graphDecide, hnode claims k]
        _ = graphDecide (pref.append rest) claims k := by
          rw [filterPermitted_transparent hnode claims]
        _ = graphDecide rest claims k :=
          ih htail claims

private lemma effectivePeerRelativeSurface_equiv_head
    (G pref tail : GovernanceGraph)
    (heffective : EffectivePeerRelativeSurface G pref tail) :
    GovernanceGraphEquivalent G (peerRelativeNode :: tail) := by
  intro claims k
  rcases heffective with ⟨hshape, hpref⟩
  rw [hshape]
  exact graphDecide_transparentPrefix_append pref (peerRelativeNode :: tail)
    hpref claims k

private lemma effectiveSurfaceForNode_equiv_head
    (node : GovernanceNodeFn) (G pref tail : GovernanceGraph)
    (heffective : EffectiveSurfaceForNode node G pref tail) :
    GovernanceGraphEquivalent G (node :: tail) := by
  intro claims k
  rcases heffective with ⟨hshape, hpref⟩
  rw [hshape]
  exact graphDecide_transparentPrefix_append pref (node :: tail)
    hpref claims k

/-- Complete first-effective surfaces over peer-relative aggregators violate
graph monotonicity directly: the aggregator witness supplies a claimant whose
Permit decision is reversed by strengthening a different claimant, while the
complete tail preserves the original Permit. -/
theorem binaryDecisionPipeline_isPeerRelativeAggregator_complete_monotonicity_obstruction
    {P : Type} [DecisionPipeline P]
    (G pref tail : P) (node : DecisionPipeline.NodeOf P)
    (hagg : DecisionPipeline.IsPeerRelativeAggregator node)
    (heffective : DecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : DecisionPipeline.CompleteTailForNode node tail) :
    ¬ GraphMonotonicityP G := by
  intro hmon
  rcases DecisionPipeline.IsPeerRelativeAggregator.monotonicityWitness
      hagg with
    ⟨claims, k, j, s', hs', _hkj, hk, _hj, _hj', hdist, _hdist', hle,
      _hsame, hpermit, hdeny⟩
  have heq : DecisionSystem.Equivalent G
      (DecisionPipeline.canonicalPipelineFor node) :=
    DecisionPipeline.effectiveSurfaceForNode_completeTail_decision_equivalent_to_canonical
      G pref tail node heffective hcomplete
  have hmonCanonical :
      GraphMonotonicityP
        (DecisionPipeline.canonicalPipelineFor node) :=
    (GraphMonotonicityP_congr heq).mp hmon
  have hcanonicalPermit :
      DecisionSystem.decide
          (DecisionPipeline.canonicalPipelineFor node) claims j =
        BinaryDecision.Permit := by
    exact (DecisionPipeline.decide_canonicalPipelineFor node claims j).trans hpermit
  have hflip :=
    hmonCanonical claims k s' hs' j hk hdist hle hcanonicalPermit
  have hcanonicalDeny :
      DecisionSystem.decide
          (DecisionPipeline.canonicalPipelineFor node)
          (strengthenClaim k s' hs' claims) j =
        BinaryDecision.Deny := by
    exact (DecisionPipeline.decide_canonicalPipelineFor node
      (strengthenClaim k s' hs' claims) j).trans hdeny
  rw [hcanonicalDeny] at hflip
  exact BinaryDecision.noConfusion hflip

/-- Complete first-effective surfaces over peer-relative aggregators violate
graph consistency directly: the aggregator witness supplies a denied claimant
whose removal flips a surviving claimant from Permit to Deny in the canonical
singleton. -/
theorem binaryDecisionPipeline_hasConsistencyViolationWitness_complete_consistency_obstruction
    {P : Type} [DecisionPipeline P]
    (G pref tail : P) (node : DecisionPipeline.NodeOf P)
    (hwitness : DecisionPipeline.HasConsistencyViolationWitness node)
    (heffective : DecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : DecisionPipeline.CompleteTailForNode node tail) :
    ¬ GraphConsistencyP G := by
  intro hcons
  have heq : DecisionSystem.Equivalent G
      (DecisionPipeline.canonicalPipelineFor node) :=
    DecisionPipeline.effectiveSurfaceForNode_completeTail_decision_equivalent_to_canonical
      G pref tail node heffective hcomplete
  have hconsCanonical :
      GraphConsistencyP
        (DecisionPipeline.canonicalPipelineFor node) :=
    (GraphConsistencyP_congr heq).mp hcons
  have hcanonicalDeny :
      DecisionSystem.decide
          (DecisionPipeline.canonicalPipelineFor node)
          hwitness.claims hwitness.denied =
        BinaryDecision.Deny := by
    exact (DecisionPipeline.decide_canonicalPipelineFor node
      hwitness.claims hwitness.denied).trans hwitness.denied_decision
  have hcanonicalPermit :
      DecisionSystem.decide
          (DecisionPipeline.canonicalPipelineFor node)
          hwitness.claims hwitness.survivor =
        BinaryDecision.Permit := by
    exact (DecisionPipeline.decide_canonicalPipelineFor node
      hwitness.claims hwitness.survivor).trans hwitness.survivor_permitted
  have hcanonicalRemovedDeny :
      DecisionSystem.decide
          (DecisionPipeline.canonicalPipelineFor node)
          (removeClaimGraph hwitness.denied hwitness.claims)
          hwitness.survivor =
        BinaryDecision.Deny := by
    exact (DecisionPipeline.decide_canonicalPipelineFor node
      (removeClaimGraph hwitness.denied hwitness.claims)
      hwitness.survivor).trans hwitness.survivor_denied_after_removal
  have hconsistent :=
    hconsCanonical hwitness.claims hwitness.denied hwitness.survivor
      hwitness.denied_in_claims hwitness.survivor_in_claims
      hwitness.distinct_claimants hwitness.claims_distinct hcanonicalDeny
  rw [hcanonicalPermit, hcanonicalRemovedDeny] at hconsistent
  exact BinaryDecision.noConfusion hconsistent

/-- Complete first-effective surfaces over peer-relative aggregators violate
graph consistency by projecting their removal witness into the broader
consistency-route class. -/
theorem binaryDecisionPipeline_isPeerRelativeAggregator_complete_consistency_obstruction
    {P : Type} [DecisionPipeline P]
    (G pref tail : P) (node : DecisionPipeline.NodeOf P)
    (hagg : DecisionPipeline.IsPeerRelativeAggregator node)
    (heffective : DecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : DecisionPipeline.CompleteTailForNode node tail) :
    ¬ GraphConsistencyP G :=
  binaryDecisionPipeline_hasConsistencyViolationWitness_complete_consistency_obstruction
    G pref tail node
    (DecisionPipeline.HasConsistencyViolationWitness.ofPeerRelativeAggregator
      hagg)
    heffective hcomplete

/-- Complete first-effective surfaces over peer-relative aggregators violate
both diagnostics supplied by the strengthened predicate: consistency by the
removal witness, and monotonicity by the competitive-displacement witness. -/
theorem binaryDecisionPipeline_isPeerRelativeAggregator_complete_obstruction
    {P : Type} [DecisionPipeline P]
    (G pref tail : P) (node : DecisionPipeline.NodeOf P)
    (hagg : DecisionPipeline.IsPeerRelativeAggregator node)
    (heffective : DecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : DecisionPipeline.CompleteTailForNode node tail) :
    ¬ GraphConsistencyP G ∧ ¬ GraphMonotonicityP G :=
  ⟨binaryDecisionPipeline_isPeerRelativeAggregator_complete_consistency_obstruction
      G pref tail node hagg heffective hcomplete,
    binaryDecisionPipeline_isPeerRelativeAggregator_complete_monotonicity_obstruction
      G pref tail node hagg heffective hcomplete⟩

/-- Complete first-effective surfaces over peer-relative aggregators cannot
jointly satisfy the three decision-system diagnostics. The hypotheses remain
unbundled: aggregator witness, effective surface, and complete tail are
separate inputs. -/
theorem binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction
    {P : Type} [DecisionPipeline P]
    (G pref tail : P) (node : DecisionPipeline.NodeOf P)
    (hagg : DecisionPipeline.IsPeerRelativeAggregator node)
    (heffective : DecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : DecisionPipeline.CompleteTailForNode node tail) :
    ¬ (GraphConsistencyP G ∧ GraphSolidarityP G ∧ GraphMonotonicityP G) := by
  intro haxioms
  have hobstruction :=
    binaryDecisionPipeline_isPeerRelativeAggregator_complete_obstruction
      G pref tail node hagg heffective hcomplete
  exact hobstruction.1 haxioms.1

/-- Existential class form for complete first-effective surfaces over
peer-relative aggregators. The existential packages the witnesses, but the
pipeline theorem still consumes effective-surface and complete-tail hypotheses
as separate facts. -/
theorem binaryDecisionPipeline_existsClass_three_axiom_obstruction
    {P : Type} [DecisionPipeline P]
    (G : P) (node : DecisionPipeline.NodeOf P)
    (hagg : DecisionPipeline.IsPeerRelativeAggregator node)
    (h : ∃ pref tail,
      DecisionPipeline.EffectiveSurfaceForNode node G pref tail ∧
        DecisionPipeline.CompleteTailForNode node tail) :
    ¬ (GraphConsistencyP G ∧ GraphSolidarityP G ∧ GraphMonotonicityP G) :=
  Exists.elim h fun pref hpref =>
    Exists.elim hpref fun tail hsurface =>
      binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction
        G pref tail node hagg hsurface.1 hsurface.2

/-- Decision-pipeline-facing name for the complete first-effective obstruction. -/
theorem decisionPipeline_effectiveSurface_complete_three_axiom_obstruction
    {P : Type} [DecisionPipeline P]
    (G pref tail : P) (node : DecisionPipeline.NodeOf P)
    (hagg : DecisionPipeline.IsPeerRelativeAggregator node)
    (heffective : DecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : DecisionPipeline.CompleteTailForNode node tail) :
    ¬ (GraphConsistencyP G ∧ GraphSolidarityP G ∧ GraphMonotonicityP G) :=
  binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction
    G pref tail node hagg heffective hcomplete

/-- Existential decision-pipeline class form for complete first-effective
surfaces over peer-relative aggregators. -/
theorem decisionPipeline_existsClass_three_axiom_obstruction
    {P : Type} [DecisionPipeline P]
    (G : P) (node : DecisionPipeline.NodeOf P)
    (hagg : DecisionPipeline.IsPeerRelativeAggregator node)
    (h : ∃ pref tail,
      DecisionPipeline.EffectiveSurfaceForNode node G pref tail ∧
        DecisionPipeline.CompleteTailForNode node tail) :
    ¬ (GraphConsistencyP G ∧ GraphSolidarityP G ∧ GraphMonotonicityP G) :=
  binaryDecisionPipeline_existsClass_three_axiom_obstruction G node hagg h

theorem isPeerRelativeAggregator_complete_monotonicity_obstruction
    (node : GovernanceNodeFn) (hn : IsPeerRelativeAggregator node)
    (G pref tail : GovernanceGraph)
    (heffective : EffectiveSurfaceForNode node G pref tail)
    (hcomplete : CompleteTailForNode node tail) :
    ¬ GraphMonotonicity G := by
  intro hmon
  have hobstruction :
      ¬ GraphMonotonicityP G :=
    binaryDecisionPipeline_isPeerRelativeAggregator_complete_monotonicity_obstruction
      G pref tail node hn heffective hcomplete
  exact hobstruction ((graphMonotonicity_eq_graphMonotonicityP G).mp hmon)

/-- Complete first-effective surfaces over peer-relative aggregators cannot
jointly satisfy the three graph diagnostics. -/
theorem isPeerRelativeAggregator_complete_obstruction
    (node : GovernanceNodeFn) (hn : IsPeerRelativeAggregator node)
    {G pref tail : GovernanceGraph}
    (h : EffectiveSurfaceForNode node G pref tail ∧
      CompleteTailForNode node tail) :
    ¬ (GraphConsistency G ∧ GraphSolidarity G ∧ GraphMonotonicity G) := by
  intro haxioms
  have hobstruction :=
    binaryDecisionPipeline_isPeerRelativeAggregator_complete_obstruction
      G pref tail node hn h.1 h.2
  exact hobstruction.1 ((graphConsistency_eq_graphConsistencyP G).mp haxioms.1)

/-- The refined aggregator predicate discharges the previously named per-node
obstruction surface. -/
theorem IsPeerRelativeAggregator.completeFirstEffectiveNodeObstruction
    (node : GovernanceNodeFn) (hn : IsPeerRelativeAggregator node) :
    CompleteFirstEffectiveNodeObstruction node := by
  intro G pref tail heffective hcomplete
  exact isPeerRelativeAggregator_complete_obstruction node hn
    ⟨heffective, hcomplete⟩

/-- A complete peer-relative head-and-tail graph has exactly the same external
decision behavior as the canonical singleton peer graph. -/
theorem peerRelativeHead_complete_equiv_peerGraph
    (G tail : GovernanceGraph)
    (hhead : PeerRelativeHead G tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    GovernanceGraphEquivalent G peerGraph := by
  intro claims k
  rw [hhead]
  cases hpeer : peerRelativeNode claims k with
  | Permit =>
      have htail := hcomplete claims k hpeer
      simp [peerGraph, graphDecide, hpeer, htail]
  | Deny =>
      simp [peerGraph, graphDecide, hpeer]

/-- Quantified peer-relative class impossibility: every complete pipeline whose
head is the peer-relative gate violates the four graph-level legitimacy axioms.

The hypotheses are intentionally unbundled so the proof consumes both pieces:
`hhead` supplies the peer-relative head stage, and `hcomplete` prevents the tail
from changing the peer gate's external decision surface. -/
theorem peerRelativeHead_complete_impossibility
    (G tail : GovernanceGraph)
    (hhead : PeerRelativeHead G tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    ¬ AllLegitimacyAxioms G := by
  intro haxioms
  have heq : GovernanceGraphEquivalent G peerGraph :=
    peerRelativeHead_complete_equiv_peerGraph G tail hhead hcomplete
  exact peerGraph_impossibility ((allLegitimacyAxioms_congr heq).mp haxioms)

/-- Strong form: every complete pipeline headed by the peer-relative gate
violates monotonicity and strategyproofness individually. -/
theorem peerRelativeHead_complete_impossibility_strong
    (G tail : GovernanceGraph)
    (hhead : PeerRelativeHead G tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    ¬ GraphMonotonicity G ∧ ¬ GraphStrategyproofness G := by
  have heq : GovernanceGraphEquivalent G peerGraph :=
    peerRelativeHead_complete_equiv_peerGraph G tail hhead hcomplete
  constructor
  · intro hmon
    exact peerGraph_not_monotone ((graphMonotonicity_congr heq).mp hmon)
  · intro hsp
    exact peerGraph_not_strategyproof ((graphStrategyproofness_congr heq).mp hsp)

/-- First-effective peer-relative surface equivalence: transparent governance
prefixes normalize away, so a complete pipeline whose first effective surface is
peer-relative has the same external decision behavior as the canonical peer
graph. -/
theorem effectivePeerRelativeSurface_complete_equiv_peerGraph
    (G pref tail : GovernanceGraph)
    (heffective : EffectivePeerRelativeSurface G pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    GovernanceGraphEquivalent G peerGraph := by
  have heqHead : GovernanceGraphEquivalent G (peerRelativeNode :: tail) :=
    effectivePeerRelativeSurface_equiv_head G pref tail heffective
  have hhead : PeerRelativeHead (peerRelativeNode :: tail) tail := rfl
  have heqPeer : GovernanceGraphEquivalent (peerRelativeNode :: tail) peerGraph :=
    peerRelativeHead_complete_equiv_peerGraph (peerRelativeNode :: tail) tail
      hhead hcomplete
  intro claims k
  trans graphDecide (peerRelativeNode :: tail) claims k
  · exact heqHead claims k
  · exact heqPeer claims k

/-- Generalized first-effective-surface impossibility. The obstruction is not
limited to a syntactic peer-relative head: any transparent prefix before the
first effective peer-relative surface inherits the same impossibility, provided
the downstream tail preserves the peer surface. -/
theorem effectivePeerRelativeSurface_complete_impossibility
    (G pref tail : GovernanceGraph)
    (heffective : EffectivePeerRelativeSurface G pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    ¬ AllLegitimacyAxioms G := by
  intro haxioms
  have heq : GovernanceGraphEquivalent G peerGraph :=
    effectivePeerRelativeSurface_complete_equiv_peerGraph G pref tail
      heffective hcomplete
  exact peerGraph_impossibility ((allLegitimacyAxioms_congr heq).mp haxioms)

/-- Pipeline-level consistency-route obstruction for complete first-effective
surfaces. The canonical singleton's inconsistency is supplied as an unbundled
hypothesis, so concrete instances can discharge it with their own canonical
counterexample. -/
theorem binaryDecisionPipeline_effectiveSurface_complete_consistency_route_obstruction
    {P : Type} [BinaryDecisionPipeline P]
    (G pref tail : P) (peerNode : BinaryDecisionPipeline.NodeOf P)
    (heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode peerNode G pref tail)
    (hcomplete :
      BinaryDecisionPipeline.CompleteTailForNode peerNode tail)
    (hpeerNotConsistent :
      ¬ GraphConsistencyP
        (BinaryDecisionPipeline.canonicalPipelineFor peerNode)) :
    ¬ GraphConsistencyP G := by
  intro hcons
  have heq : DecisionSystem.Equivalent G
      (BinaryDecisionPipeline.canonicalPipelineFor peerNode) :=
    BinaryDecisionPipeline.effectiveSurfaceForNode_completeTail_decision_equivalent_to_canonical
        G pref tail peerNode heffective hcomplete
  exact hpeerNotConsistent ((GraphConsistencyP_congr heq).mp hcons)

/-- Concrete peer-relative effective surfaces specialize to the pipeline-level
effective-surface predicate for `GovernanceGraph`. -/
lemma effectiveSurface_specialize
    {G pref tail : GovernanceGraph}
    (heffective : EffectivePeerRelativeSurface G pref tail) :
    BinaryDecisionPipeline.EffectiveSurfaceForNode
      (P := GovernanceGraph) peerRelativeNode G pref tail := by
  exact heffective

/-- Concrete complete peer-relative tails specialize to the pipeline-level
complete-tail predicate for `GovernanceGraph`. -/
lemma completeTail_specialize
    {tail : GovernanceGraph}
    (hcomplete : CompletePeerRelativeTail tail) :
    BinaryDecisionPipeline.CompleteTailForNode
      (P := GovernanceGraph) peerRelativeNode tail := by
  exact hcomplete

/-- GovernanceGraph specialization of the pipeline-level consistency route. -/
theorem effectivePeerRelativeSurface_complete_consistency_route_obstruction_via_pipeline
    (G pref tail : GovernanceGraph)
    (heffective : EffectivePeerRelativeSurface G pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    ¬ GraphConsistency G := by
  have hpeerNotConsistent :
      ¬ GraphConsistencyP
        (BinaryDecisionPipeline.canonicalPipelineFor
          (P := GovernanceGraph) peerRelativeNode) := by
    intro hcons
    have hpeer : GraphConsistencyP peerGraph := by
      simpa [BinaryDecisionPipeline.canonicalPipelineFor, peerGraph] using hcons
    exact peerGraph_not_consistent
      ((graphConsistency_eq_graphConsistencyP peerGraph).mpr hpeer)
  have h :
      ¬ GraphConsistencyP G :=
    binaryDecisionPipeline_effectiveSurface_complete_consistency_route_obstruction
      G pref tail peerRelativeNode
      (effectiveSurface_specialize heffective)
      (completeTail_specialize hcomplete)
      hpeerNotConsistent
  intro hcons
  exact h ((graphConsistency_eq_graphConsistencyP G).mp hcons)

/-- Consistency-route obstruction for complete first-effective peer-relative
surfaces. This route does not use the solidarity/monotonicity-to-
strategyproofness bridge: decision equivalence to `peerGraph` transfers graph
consistency directly, contradicting the concrete consistency counterexample. -/
theorem effectivePeerRelativeSurface_complete_consistency_route_obstruction
    (G pref tail : GovernanceGraph)
    (heffective : EffectivePeerRelativeSurface G pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    ¬ GraphConsistency G :=
  effectivePeerRelativeSurface_complete_consistency_route_obstruction_via_pipeline
    G pref tail heffective hcomplete

/-- The retained concrete consistency-route theorem agrees with the
pipeline-derived specialization. -/
theorem effectivePeerRelativeSurface_complete_consistency_route_obstruction_eq_via_pipeline
    (G pref tail : GovernanceGraph)
    (heffective : EffectivePeerRelativeSurface G pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    effectivePeerRelativeSurface_complete_consistency_route_obstruction
      G pref tail heffective hcomplete =
    effectivePeerRelativeSurface_complete_consistency_route_obstruction_via_pipeline
      G pref tail heffective hcomplete :=
  Subsingleton.elim _ _

/-- Class-form consistency route for complete first-effective peer-relative
surfaces. -/
theorem effectivePeerRelativeSurface_class_consistency_route_obstruction
    (G pref tail : GovernanceGraph)
    (h : CompleteFirstEffectivePeerRelativeSurfaceClass G pref tail) :
    ¬ GraphConsistency G :=
  effectivePeerRelativeSurface_complete_consistency_route_obstruction G pref tail
    h.1 h.2

/-- Solidarity/monotonicity route for complete first-effective peer-relative
surfaces. This is the original bridge route: solidarity and monotonicity imply
graph strategyproofness, but the complete first-effective surface is
decision-equivalent to `peerGraph`, which is not graph-strategyproof. -/
theorem effectivePeerRelativeSurface_complete_solidarity_monotonicity_route_obstruction
    (G pref tail : GovernanceGraph)
    (heffective : EffectivePeerRelativeSurface G pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    ¬ (GraphSolidarity G ∧ GraphMonotonicity G) := by
  intro hsm
  have heq : GovernanceGraphEquivalent G peerGraph :=
    effectivePeerRelativeSurface_complete_equiv_peerGraph G pref tail
      heffective hcomplete
  have hsp : GraphStrategyproofness G :=
    solidarity_monotonicity_imply_strategyproof hsm.1 hsm.2
  exact peerGraph_not_strategyproof ((graphStrategyproofness_congr heq).mp hsp)

/-- Bundled route statement: complete first-effective peer-relative surfaces
fail graph consistency directly and also fail the solidarity/monotonicity pair
through the strategyproofness bridge. -/
theorem effectivePeerRelativeSurface_complete_route_obstructions
    (G pref tail : GovernanceGraph)
    (heffective : EffectivePeerRelativeSurface G pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    ¬ GraphConsistency G ∧ ¬ (GraphSolidarity G ∧ GraphMonotonicity G) :=
  ⟨effectivePeerRelativeSurface_complete_consistency_route_obstruction G pref tail
      heffective hcomplete,
    effectivePeerRelativeSurface_complete_solidarity_monotonicity_route_obstruction
      G pref tail heffective hcomplete⟩

/-- GovernanceGraph specialization of the strengthened pipeline-level
three-axiom obstruction. -/
theorem effectivePeerRelativeSurface_complete_three_axiom_obstruction_via_pipeline
    (G pref tail : GovernanceGraph)
    (heffective : EffectivePeerRelativeSurface G pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    ¬ (GraphConsistency G ∧ GraphSolidarity G ∧ GraphMonotonicity G) := by
  intro haxioms
  exact
    (binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction
      G pref tail peerRelativeNode peerRelativeNode_isPeerRelativeAggregator
      (effectiveSurface_specialize heffective)
      (completeTail_specialize hcomplete))
    ⟨(graphConsistency_eq_graphConsistencyP G).mp haxioms.1,
      (graphSolidarity_eq_graphSolidarityP G).mp haxioms.2.1,
      (graphMonotonicity_eq_graphMonotonicityP G).mp haxioms.2.2⟩

/-- Three-axiom obstruction for complete first-effective peer-relative
surfaces. The consistency conjunct is load-bearing via the direct consistency
route; solidarity and monotonicity also provide a parallel bridge route to
graph strategyproofness. -/
theorem effectivePeerRelativeSurface_complete_three_axiom_obstruction
    (G pref tail : GovernanceGraph)
    (heffective : EffectivePeerRelativeSurface G pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    ¬ (GraphConsistency G ∧ GraphSolidarity G ∧ GraphMonotonicity G) := by
  exact effectivePeerRelativeSurface_complete_three_axiom_obstruction_via_pipeline
    G pref tail heffective hcomplete

/-- Headline class-form impossibility for complete first-effective
peer-relative surfaces. -/
theorem effectivePeerRelativeSurface_class_impossibility
    (G pref tail : GovernanceGraph)
    (h : CompleteFirstEffectivePeerRelativeSurfaceClass G pref tail) :
    ¬ AllLegitimacyAxioms G :=
  effectivePeerRelativeSurface_complete_impossibility G pref tail h.1 h.2

/-- Headline class-form three-axiom obstruction for complete first-effective
peer-relative surfaces, inheriting both the direct consistency route and the
solidarity/monotonicity bridge route from the complete-surface theorem. -/
theorem effectivePeerRelativeSurface_class_three_axiom_obstruction
    (G pref tail : GovernanceGraph)
    (h : CompleteFirstEffectivePeerRelativeSurfaceClass G pref tail) :
    ¬ (GraphConsistency G ∧ GraphSolidarity G ∧ GraphMonotonicity G) :=
  effectivePeerRelativeSurface_complete_three_axiom_obstruction G pref tail
    h.1 h.2

/-- GovernanceGraph specialization of the pipeline-level existential class
obstruction. -/
theorem effectivePeerRelativeSurface_existsClass_three_axiom_obstruction_via_pipeline
    (G : GovernanceGraph)
    (h : ∃ pref tail,
      CompleteFirstEffectivePeerRelativeSurfaceClass G pref tail) :
    ¬ (GraphConsistency G ∧ GraphSolidarity G ∧ GraphMonotonicity G) := by
  have hpipeline :
      ∃ pref tail,
        BinaryDecisionPipeline.EffectiveSurfaceForNode
            (P := GovernanceGraph) peerRelativeNode G pref tail ∧
          BinaryDecisionPipeline.CompleteTailForNode
            (P := GovernanceGraph) peerRelativeNode tail := by
    exact Exists.elim h fun pref hpref =>
      Exists.elim hpref fun tail hclass =>
        ⟨pref, tail, effectiveSurface_specialize hclass.1,
          completeTail_specialize hclass.2⟩
  have hobstruction :
      ¬ (GraphConsistencyP G ∧ GraphSolidarityP G ∧ GraphMonotonicityP G) :=
    binaryDecisionPipeline_existsClass_three_axiom_obstruction
      G peerRelativeNode peerRelativeNode_isPeerRelativeAggregator hpipeline
  intro haxioms
  exact hobstruction
    ⟨(graphConsistency_eq_graphConsistencyP G).mp haxioms.1,
      (graphSolidarity_eq_graphSolidarityP G).mp haxioms.2.1,
      (graphMonotonicity_eq_graphMonotonicityP G).mp haxioms.2.2⟩

/-- Existential headline class form: any graph belonging to some complete
first-effective peer-relative surface class cannot satisfy consistency,
solidarity, and monotonicity jointly. -/
theorem effectivePeerRelativeSurface_existsClass_three_axiom_obstruction
    (G : GovernanceGraph)
    (h : ∃ pref tail,
      CompleteFirstEffectivePeerRelativeSurfaceClass G pref tail) :
    ¬ (GraphConsistency G ∧ GraphSolidarity G ∧ GraphMonotonicity G) :=
  effectivePeerRelativeSurface_existsClass_three_axiom_obstruction_via_pipeline
    G h

/-- Existential class consistency route: any graph belonging to some complete
first-effective peer-relative surface class fails graph consistency directly. -/
theorem effectivePeerRelativeSurface_existsClass_consistency_route_obstruction
    (G : GovernanceGraph)
    (h : ∃ pref tail,
      CompleteFirstEffectivePeerRelativeSurfaceClass G pref tail) :
    ¬ GraphConsistency G :=
  Exists.elim h fun pref hpref =>
    Exists.elim hpref fun tail hclass =>
      effectivePeerRelativeSurface_class_consistency_route_obstruction G pref tail
        hclass

/-- Strong generalized form: every complete first-effective peer-relative
surface violates monotonicity and strategyproofness individually. -/
theorem effectivePeerRelativeSurface_complete_impossibility_strong
    (G pref tail : GovernanceGraph)
    (heffective : EffectivePeerRelativeSurface G pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    ¬ GraphMonotonicity G ∧ ¬ GraphStrategyproofness G := by
  have heq : GovernanceGraphEquivalent G peerGraph :=
    effectivePeerRelativeSurface_complete_equiv_peerGraph G pref tail
      heffective hcomplete
  constructor
  · intro hmon
    exact peerGraph_not_monotone ((graphMonotonicity_congr heq).mp hmon)
  · intro hsp
    exact peerGraph_not_strategyproof ((graphStrategyproofness_congr heq).mp hsp)

end Legitimacy
