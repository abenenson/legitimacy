/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.Sacrifice

/-!
# Legitimacy.Safety.KernelSafety.BinaryDecisionPipeline

Binary-pipeline and stateful-adversary safety bridges.

This module owns no-undeclared-sacrifice theorems, bounded stateful
preservation, and the aggregator-witness predicates used by reachable-state
stack theorems and worked examples.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-! ## No undeclared sacrifice for binary decision pipelines -/

/-- A compiled artifact has reached the protocol `Live` state with the supplied
risk report and monitoring plan. This paper-facing alias keeps the headline
theorem stated in deployment terms rather than raw transition constructors. -/
def IsLiveCompiled
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan) : Prop :=
  TransitionSequence
    ProtocolState.Undeclared
    (ProtocolState.Live compiled report monitoring)

/-- Paper-facing predicate for the complete first-effective peer-relative
surface carried by a concrete governance graph. -/
def CompletePeerRelativeSurface (graph : GovernanceGraph) : Prop :=
  ∃ pref tail : GovernanceGraph,
    EffectivePeerRelativeSurface graph pref tail ∧
      CompletePeerRelativeTail tail

/-- The forced diagnostic sacrifices exposed by a complete peer-relative
surface are exactly consistency and monotonicity. -/
def ForcedPeerRelativeSacrificesDeclared
    (compiled : CompiledGovernance) : Prop :=
  GovernanceProperty.Consistency ∈ compiled.sacrifices ∧
    GovernanceProperty.Monotonicity ∈ compiled.sacrifices

/-- Live protocol soundness is biconditional at the property boundary: a live
compiled graph declares a property precisely when the graph fails that
property. -/
theorem liveCompiled_declaredSacrifice_iff_propertyFailure
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hlive : IsLiveCompiled compiled report monitoring)
    (property : GovernanceProperty) :
    property ∈ compiled.sacrifices ↔
      ¬ propertyHolds property compiled.graph := by
  obtain ⟨hnonSacrificed, hjustified, _hrisk⟩ :=
    protocol_live_soundness hlive
  constructor
  · intro hdeclared
    exact hjustified property hdeclared
  · intro hfailure
    by_contra hnotDeclared
    exact hfailure (hnonSacrificed property hnotDeclared)

/-- On a complete first-effective peer-relative surface, live deployment is
equivalent to live deployment with the forced consistency and monotonicity
sacrifices declared. The reverse direction is projection; the forward direction
is the load-bearing no-undeclared-sacrifice soundness claim. -/
theorem completePeerRelativeSurface_live_forces_sacrificesDeclared
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hsurface : CompletePeerRelativeSurface compiled.graph) :
    IsLiveCompiled compiled report monitoring ↔
      IsLiveCompiled compiled report monitoring ∧
        ForcedPeerRelativeSacrificesDeclared compiled := by
  constructor
  · intro hlive
    rcases hsurface with ⟨pref, tail, heffective, hcomplete⟩
    have hobstruction :
        ¬ GraphConsistencyP compiled.graph ∧
          ¬ GraphMonotonicityP compiled.graph :=
      binaryDecisionPipeline_isPeerRelativeAggregator_complete_obstruction
        (P := GovernanceGraph) compiled.graph pref tail peerRelativeNode
        peerRelativeNode_isPeerRelativeAggregator
        (effectiveSurface_specialize heffective)
        (completeTail_specialize hcomplete)
    have hconsFailure :
        ¬ propertyHolds GovernanceProperty.Consistency compiled.graph := by
      intro hcons
      exact hobstruction.1
        ((graphConsistency_eq_graphConsistencyP compiled.graph).mp hcons)
    have hmonFailure :
        ¬ propertyHolds GovernanceProperty.Monotonicity compiled.graph := by
      intro hmon
      exact hobstruction.2
        ((graphMonotonicity_eq_graphMonotonicityP compiled.graph).mp hmon)
    exact
      ⟨hlive,
        (liveCompiled_declaredSacrifice_iff_propertyFailure hlive
          GovernanceProperty.Consistency).2 hconsFailure,
        (liveCompiled_declaredSacrifice_iff_propertyFailure hlive
          GovernanceProperty.Monotonicity).2 hmonFailure⟩
  · intro hliveWithDeclarations
    exact hliveWithDeclarations.1

/-- Deprecated compatibility alias: the corrected name is
`completePeerRelativeSurface_live_forces_sacrificesDeclared`, because the
load-bearing direction is live deployment forcing declared sacrifices. -/
theorem completePeerRelativeSurface_live_iff_forcedSacrificesDeclared
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hsurface : CompletePeerRelativeSurface compiled.graph) :
    IsLiveCompiled compiled report monitoring ↔
      IsLiveCompiled compiled report monitoring ∧
        ForcedPeerRelativeSacrificesDeclared compiled :=
  completePeerRelativeSurface_live_forces_sacrificesDeclared hsurface

/-- Compatibility iff for the complete first-effective peer-relative activation
gate; use `noUndeclaredSacrificeImplication` for the operator-facing deployment
direction. -/
theorem noUndeclaredSacrifice
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hsurface : CompletePeerRelativeSurface compiled.graph) :
    IsLiveCompiled compiled report monitoring ↔
      IsLiveCompiled compiled report monitoring ∧
        ForcedPeerRelativeSacrificesDeclared compiled :=
  completePeerRelativeSurface_live_forces_sacrificesDeclared hsurface

/-- Operator-facing activation gate: a complete first-effective peer-relative
surface cannot enter `Live` without declaring the forced sacrifices. This is the
preferred deployment statement; the iff above is retained for compatibility. -/
theorem noUndeclaredSacrificeImplication
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hsurface : CompletePeerRelativeSurface compiled.graph) :
    IsLiveCompiled compiled report monitoring →
      ForcedPeerRelativeSacrificesDeclared compiled := by
  intro hlive
  exact ((noUndeclaredSacrifice hsurface).mp hlive).2

/-- A live compiled graph equivalent to a complete first-effective surface over
a peer-relative aggregator must declare the concrete consistency and
monotonicity sacrifices exposed by the aggregator witnesses. The class-level
hypotheses remain unbundled: aggregator, effective surface, complete tail, and
the live graph binding are separate inputs. -/
theorem binaryDecisionPipeline_noUndeclaredSacrifice
    {P : Type} [BinaryDecisionPipeline P]
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : KernelStep D D')
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (G pref tail : P) (node : BinaryDecisionPipeline.NodeOf P)
    (hagg : BinaryDecisionPipeline.IsPeerRelativeAggregator node)
    (heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : BinaryDecisionPipeline.CompleteTailForNode node tail)
    (heq : DecisionSystem.Equivalent G compiled.graph)
    (hgraph : compiled.graph = sys.graph)
    (hlive : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring)) :
    (∃ cert : MonitoredSacrificeCertificate D D',
      cert.sacrificed =
        SacrificedAxiom.governance GovernanceProperty.Consistency) ∧
    (∃ cert : MonitoredSacrificeCertificate D D',
      cert.sacrificed =
        SacrificedAxiom.governance GovernanceProperty.Monotonicity) := by
  rcases BinaryDecisionPipeline.IsPeerRelativeAggregator.consistencyViolationWitness
      hagg with
    ⟨consClaims, consDenied, _consSurvivor, _hneq, _hdeniedIn,
      _hsurvivorIn, _hdistinct, _hdeny, _hpermit, _hremovedDeny⟩
  rcases BinaryDecisionPipeline.IsPeerRelativeAggregator.monotonicityWitness
      hagg with
    ⟨monClaims, _monStrengthened, monAffected, _s', _hs', _hneq,
      _hstrengthenedIn, _haffectedIn, _haffectedStillIn, _hdistinct,
      _hstrengthenedDistinct, _hle, _hsame, _hpermit, _hdeny⟩
  obtain ⟨hnonSacrificed, _hjustified, _hrisk⟩ :=
    protocol_live_soundness hlive
  have hobstruction :
      ¬ GraphConsistencyP G ∧ ¬ GraphMonotonicityP G :=
    binaryDecisionPipeline_isPeerRelativeAggregator_complete_obstruction
      G pref tail node hagg heffective hcomplete
  have hconsDeclared :
      GovernanceProperty.Consistency ∈ compiled.sacrifices := by
    by_contra hnotDeclared
    have hcompiled :
        GraphConsistencyP compiled.graph :=
      (graphConsistency_eq_graphConsistencyP compiled.graph).mp
        (hnonSacrificed GovernanceProperty.Consistency hnotDeclared)
    have hG : GraphConsistencyP G :=
      (GraphConsistencyP_congr heq).mpr hcompiled
    exact hobstruction.1 hG
  have hmonDeclared :
      GovernanceProperty.Monotonicity ∈ compiled.sacrifices := by
    by_contra hnotDeclared
    have hcompiled :
        GraphMonotonicityP compiled.graph :=
      (graphMonotonicity_eq_graphMonotonicityP compiled.graph).mp
        (hnonSacrificed GovernanceProperty.Monotonicity hnotDeclared)
    have hG : GraphMonotonicityP G :=
      (GraphMonotonicityP_congr heq).mpr hcompiled
    exact hobstruction.2 hG
  constructor
  · refine ⟨MonitoredSacrificeCertificate.ofCompiledProperty step compiled
      monitoring GovernanceProperty.Consistency consClaims consDenied hgraph
      hconsDeclared ?_, ?_⟩
    · exact
        MonitoringBoundExceedance.oneObservedPropertyFailure compiled
          GovernanceProperty.Consistency
          (compiled.witness.sacrifices_justified GovernanceProperty.Consistency
            hconsDeclared)
    rfl
  · refine ⟨MonitoredSacrificeCertificate.ofCompiledProperty step compiled
      monitoring GovernanceProperty.Monotonicity monClaims monAffected hgraph
      hmonDeclared ?_, ?_⟩
    · exact
        MonitoringBoundExceedance.oneObservedPropertyFailure compiled
          GovernanceProperty.Monotonicity
          (compiled.witness.sacrifices_justified GovernanceProperty.Monotonicity
            hmonDeclared)
    rfl

/-- GovernanceGraph specialization of the generic no-undeclared-sacrifice
theorem. This is the concrete graph case, but it still consumes the
`BinaryDecisionPipeline` predicates rather than reproving the obstruction. -/
theorem governanceGraph_noUndeclaredSacrifice_via_pipeline
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : KernelStep D D')
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    {node : GovernanceNodeFn}
    {pref tail : GovernanceGraph}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (hagg :
      BinaryDecisionPipeline.IsPeerRelativeAggregator
        (P := GovernanceGraph) node)
    (heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode
        (P := GovernanceGraph) node compiled.graph pref tail)
    (hcomplete :
      BinaryDecisionPipeline.CompleteTailForNode
        (P := GovernanceGraph) node tail)
    (hgraph : compiled.graph = sys.graph) :
    (∃ cert : MonitoredSacrificeCertificate D D',
      cert.sacrificed =
        SacrificedAxiom.governance GovernanceProperty.Consistency) ∧
    (∃ cert : MonitoredSacrificeCertificate D D',
      cert.sacrificed =
        SacrificedAxiom.governance GovernanceProperty.Monotonicity) :=
  binaryDecisionPipeline_noUndeclaredSacrifice
    (P := GovernanceGraph)
    step compiled report monitoring compiled.graph pref tail node
    hagg heffective hcomplete
    (DecisionSystem.Equivalent.refl compiled.graph)
    hgraph hpath

/-- The median-rule peer-relative surface derives from the concrete
GovernanceGraph pipeline theorem, not from a graph-specific reproving of the
obstruction. -/
theorem effectivePeerRelativeSurface_live_forces_sacrifice_via_pipeline
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : KernelStep D D')
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    {pref tail : GovernanceGraph}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (heffective :
      EffectivePeerRelativeSurface compiled.graph pref tail)
    (hcomplete : CompletePeerRelativeTail tail)
    (hgraph : compiled.graph = sys.graph) :
    (∃ cert : MonitoredSacrificeCertificate D D',
      cert.sacrificed =
        SacrificedAxiom.governance GovernanceProperty.Consistency) ∧
    (∃ cert : MonitoredSacrificeCertificate D D',
      cert.sacrificed =
        SacrificedAxiom.governance GovernanceProperty.Monotonicity) :=
  governanceGraph_noUndeclaredSacrifice_via_pipeline
    step hpath peerRelativeNode_isPeerRelativeAggregator
    (effectiveSurface_specialize heffective)
    (completeTail_specialize hcomplete)
    hgraph

/-- The canonical tree instance carries the same peer-relative aggregator
witness because tree nodes evaluate ordinary governance node functions. -/
theorem peerRelativeNode_tree_isPeerRelativeAggregator :
    BinaryDecisionPipeline.IsPeerRelativeAggregator
      (P := BinaryDecisionTree) peerRelativeNode :=
  peerRelativeNode_isPeerRelativeAggregator

/-- Worked tree case: the generic no-undeclared-sacrifice theorem fires for the
canonical `BinaryDecisionTree` peer-relative singleton, assuming the live
compiled graph is decision-equivalent to that tree. -/
theorem treeNoUndeclaredSacrificeExample
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : KernelStep D D')
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (heq : DecisionSystem.Equivalent
      (BinaryDecisionPipeline.canonicalPipelineFor
        (P := BinaryDecisionTree) peerRelativeNode)
      compiled.graph)
    (hgraph : compiled.graph = sys.graph) :
    (∃ cert : MonitoredSacrificeCertificate D D',
      cert.sacrificed =
        SacrificedAxiom.governance GovernanceProperty.Consistency) ∧
    (∃ cert : MonitoredSacrificeCertificate D D',
      cert.sacrificed =
        SacrificedAxiom.governance GovernanceProperty.Monotonicity) := by
  refine binaryDecisionPipeline_noUndeclaredSacrifice
    (P := BinaryDecisionTree)
    step compiled report monitoring
    (BinaryDecisionPipeline.canonicalPipelineFor
      (P := BinaryDecisionTree) peerRelativeNode)
    (BinaryDecisionPipeline.empty : BinaryDecisionTree)
    (BinaryDecisionPipeline.empty : BinaryDecisionTree)
    peerRelativeNode
    peerRelativeNode_tree_isPeerRelativeAggregator
    ?_ ?_ heq hgraph hpath
  · constructor
    · rfl
    · trivial
  · intro claims k _hpermit
    exact BinaryDecisionPipeline.decide_empty
      (P := BinaryDecisionTree) claims k

/-- Concrete bounded-corrigibility conclusion for a realized stateful
trajectory. This is a definitional unwrap of the stateful theorem conclusion,
with the starting configuration left explicit. -/
def BoundedCorrigibilityPreservedAt
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : StatefulAdversaryLayer D)
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv) : Prop :=
  0 < kernelDataCriticalCapability D ∧
    StateClaimDecisionsAgree sys.state
      (applyStatefulTrajectory D adv schedule cfg).state ∧
    spectralDistance D.spectralGraph
      (adv.stateRealization
        (applyStatefulTrajectory D adv schedule cfg).state) <
      kernelDataCriticalCapability D

/-- A certificate's property-level witness data is supplied by one of the two
routes carried by `BinaryDecisionPipeline.IsPeerRelativeAggregator`: the
consistency-removal witness or the monotonicity competitive-displacement
witness. -/
def AggregatorAxiomWitnessedSacrifice
    {P : Type} [BinaryDecisionPipeline P]
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (cert : MonitoredSacrificeCertificate D D')
    {G pref tail : P} {node : BinaryDecisionPipeline.NodeOf P}
    (_hagg : BinaryDecisionPipeline.IsPeerRelativeAggregator node)
    (_heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (_hcomplete : BinaryDecisionPipeline.CompleteTailForNode node tail) :
    Prop :=
  (cert.sacrificed =
      SacrificedAxiom.governance GovernanceProperty.Consistency ∧
    cert.aggregator_witness =
      some AggregatorAxiomWitnessKind.consistencyViolation ∧
    ¬ GraphConsistencyP G ∧
    ∃ (claims : List ClaimQ) (denied survivor : ClaimantId),
      denied ≠ survivor ∧
      InClaims denied claims ∧
      InClaims survivor claims ∧
      ClaimsDistinct claims ∧
      BinaryDecisionPipeline.evalNode node claims denied =
        BinaryDecision.Deny ∧
      BinaryDecisionPipeline.evalNode node claims survivor =
        BinaryDecision.Permit ∧
      BinaryDecisionPipeline.evalNode node (removeClaimGraph denied claims)
          survivor =
        BinaryDecision.Deny ∧
      cert.claim_profile = claims ∧
      cert.claimant = denied) ∨
  (cert.sacrificed =
      SacrificedAxiom.governance GovernanceProperty.Monotonicity ∧
    cert.aggregator_witness =
      some AggregatorAxiomWitnessKind.monotonicityViolation ∧
    ¬ GraphMonotonicityP G ∧
    ∃ (claims : List ClaimQ) (strengthened affected : ClaimantId)
        (s' : ℚ) (hs' : 0 < s'),
      strengthened ≠ affected ∧
      InClaims strengthened claims ∧
      InClaims affected claims ∧
      InClaims affected (strengthenClaim strengthened s' hs' claims) ∧
      ClaimsDistinct claims ∧
      ClaimsDistinct (strengthenClaim strengthened s' hs' claims) ∧
      (∀ c ∈ claims, c.id = strengthened → c.strength ≤ s') ∧
      lookupStrength affected claims =
        lookupStrength affected
          (strengthenClaim strengthened s' hs' claims) ∧
      BinaryDecisionPipeline.evalNode node claims affected =
        BinaryDecision.Permit ∧
      BinaryDecisionPipeline.evalNode node
          (strengthenClaim strengthened s' hs' claims) affected =
        BinaryDecision.Deny ∧
      cert.claim_profile = claims ∧
      cert.claimant = affected)

/-- A certificate whose consistency-sacrifice data is supplied by the concrete
route fields of a broader binary-pipeline consistency witness. This is the
part of `AggregatorAxiomWitnessedSacrifice` consumed by the stateful
corrigibility-or-sacrifice bridge. -/
def ConsistencyAxiomWitnessedSacrifice
    {P : Type} [BinaryDecisionPipeline P]
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (cert : MonitoredSacrificeCertificate D D')
    {G pref tail : P} {node : BinaryDecisionPipeline.NodeOf P}
    (hwitness : BinaryDecisionPipeline.HasConsistencyViolationWitness node)
    (_heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (_hcomplete : BinaryDecisionPipeline.CompleteTailForNode node tail) :
    Prop :=
  cert.sacrificed =
      SacrificedAxiom.governance GovernanceProperty.Consistency ∧
    cert.aggregator_witness =
      some AggregatorAxiomWitnessKind.consistencyViolation ∧
    ¬ GraphConsistencyP G ∧
    BinaryDecisionPipeline.evalNode node hwitness.claims hwitness.denied =
      BinaryDecision.Deny ∧
    BinaryDecisionPipeline.evalNode node hwitness.claims hwitness.survivor =
      BinaryDecision.Permit ∧
    BinaryDecisionPipeline.evalNode node
        (removeClaimGraph hwitness.denied hwitness.claims) hwitness.survivor =
      BinaryDecision.Deny ∧
    cert.claim_profile = hwitness.claims ∧
    cert.claimant = hwitness.denied

/-- A stateful adversary run against a complete first-effective peer-relative
aggregator surface either stays below the critical-capability budget and
preserves bounded corrigibility, or its failed budget premise emits a monitored
sacrifice certificate whose witness data is the aggregator's concrete
consistency axiom witness. -/
theorem
    statefulAdversary_via_consistencyWitnessedAggregator_yields_boundedCorrigibility_or_sacrifice
    {P : Type} [BinaryDecisionPipeline P]
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : StatefulAdversaryLayer D)
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (G pref tail : P) (node : BinaryDecisionPipeline.NodeOf P)
    (hwitness : BinaryDecisionPipeline.HasConsistencyViolationWitness node)
    (heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : BinaryDecisionPipeline.CompleteTailForNode node tail)
    (heq : DecisionSystem.Equivalent G compiled.graph)
    (hgraph : compiled.graph = sys.graph)
    (hlive : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (hδ : 0 < D.toleranceParameter)
    (hcv : 0 < D.spectralGraph.cv D.spectralSignal)
    [IsKernelPerturbationFreeAdversary D adv]
    [IsLocallyStableStatefulAdversary D adv sys.state
      (kernelDataCriticalCapability D)]
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv)
    (hcfg : cfg = initialStatefulAdversaryConfig D adv) :
    BoundedCorrigibilityPreservedAt D adv schedule cfg ∨
    ∃ cert : MonitoredSacrificeCertificate D D,
      ConsistencyAxiomWitnessedSacrifice cert hwitness heffective hcomplete ∧
      ∃ hcritical :
        kernelDataCriticalCapability D ≤
          statefulTrajectoryPerturbationBound D adv schedule cfg,
        cert.stateful_violation =
          some
            ({ adv := adv
               schedule := schedule
               cfg := cfg
               critical_le_budget := hcritical } :
              StatefulCriticalCapabilityViolation D) := by
  subst cfg
  by_cases hbudget :
      statefulTrajectoryPerturbationBound D adv schedule
          (initialStatefulAdversaryConfig D adv) <
        kernelDataCriticalCapability D
  · exact Or.inl
      (stateful_budgeted_subcritical_trajectory_preserves_stable_state_decisions
        D adv hδ hcv schedule hbudget)
  · obtain ⟨hnonSacrificed, _hjustified, _hrisk⟩ :=
      protocol_live_soundness hlive
    have hobstruction :
        ¬ GraphConsistencyP G :=
      binaryDecisionPipeline_hasConsistencyViolationWitness_complete_consistency_obstruction
        G pref tail node hwitness heffective hcomplete
    have hconsDeclared :
        GovernanceProperty.Consistency ∈ compiled.sacrifices := by
      by_contra hnotDeclared
      have hcompiled :
          GraphConsistencyP compiled.graph :=
        (graphConsistency_eq_graphConsistencyP compiled.graph).mp
          (hnonSacrificed GovernanceProperty.Consistency hnotDeclared)
      have hG : GraphConsistencyP G :=
        (GraphConsistencyP_congr heq).mpr hcompiled
      exact hobstruction hG
    have hcritical :
        kernelDataCriticalCapability D ≤
          statefulTrajectoryPerturbationBound D adv schedule
            (initialStatefulAdversaryConfig D adv) :=
      le_of_not_gt hbudget
    let trigger : StatefulCriticalCapabilityViolation D :=
      { adv := adv
        schedule := schedule
        cfg := initialStatefulAdversaryConfig D adv
        critical_le_budget := hcritical }
    let cert : MonitoredSacrificeCertificate D D :=
      MonitoredSacrificeCertificate.ofCompiledPropertyWithAggregatorWitness
        (KernelStep.refl D) compiled monitoring GovernanceProperty.Consistency
        hwitness.claims hwitness.denied hgraph hconsDeclared
        (MonitoringBoundExceedance.oneObservedPropertyFailure compiled
          GovernanceProperty.Consistency
          (compiled.witness.sacrifices_justified GovernanceProperty.Consistency
            hconsDeclared))
        (some AggregatorAxiomWitnessKind.consistencyViolation)
        (some trigger)
    refine Or.inr ⟨cert, ?_, ?_⟩
    · exact ⟨rfl, rfl, hobstruction, hwitness.denied_decision,
        hwitness.survivor_permitted,
        hwitness.survivor_denied_after_removal, rfl, rfl⟩
    · exact ⟨hcritical, rfl⟩

/-- Exclusive operational wrapper for the stateful bounded-corrigibility
dichotomy. At or above the datum's graph-derived `C_star` budget, the live
peer-relative surface emits a monitored consistency-sacrifice certificate; if
the realized adaptive perturbation budget is strictly below that threshold,
bounded corrigibility is preserved. -/
theorem statefulAdversary_via_consistencyWitnessedAggregator_exclusive_dichotomy
    {P : Type} [BinaryDecisionPipeline P]
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : StatefulAdversaryLayer D)
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (G pref tail : P) (node : BinaryDecisionPipeline.NodeOf P)
    (hwitness : BinaryDecisionPipeline.HasConsistencyViolationWitness node)
    (heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : BinaryDecisionPipeline.CompleteTailForNode node tail)
    (heq : DecisionSystem.Equivalent G compiled.graph)
    (hgraph : compiled.graph = sys.graph)
    (hlive : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (hδ : 0 < D.toleranceParameter)
    (hcv : 0 < D.spectralGraph.cv D.spectralSignal)
    [IsKernelPerturbationFreeAdversary D adv]
    [IsLocallyStableStatefulAdversary D adv sys.state
      (kernelDataCriticalCapability D)]
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv)
    (hcfg : cfg = initialStatefulAdversaryConfig D adv) :
    (kernelDataCriticalCapability D ≤
        statefulTrajectoryPerturbationBound D adv schedule cfg →
      ∃ cert : MonitoredSacrificeCertificate D D,
        ConsistencyAxiomWitnessedSacrifice cert hwitness heffective
          hcomplete ∧
        ∃ hcritical :
          kernelDataCriticalCapability D ≤
            statefulTrajectoryPerturbationBound D adv schedule cfg,
          cert.stateful_violation =
            some
              ({ adv := adv
                 schedule := schedule
                 cfg := cfg
                 critical_le_budget := hcritical } :
                StatefulCriticalCapabilityViolation D)) ∧
    (statefulTrajectoryPerturbationBound D adv schedule cfg <
        kernelDataCriticalCapability D →
      BoundedCorrigibilityPreservedAt D adv schedule cfg) := by
  subst cfg
  constructor
  · intro hcritical
    obtain ⟨hnonSacrificed, _hjustified, _hrisk⟩ :=
      protocol_live_soundness hlive
    have hobstruction :
        ¬ GraphConsistencyP G :=
      binaryDecisionPipeline_hasConsistencyViolationWitness_complete_consistency_obstruction
        G pref tail node hwitness heffective hcomplete
    have hconsDeclared :
        GovernanceProperty.Consistency ∈ compiled.sacrifices := by
      by_contra hnotDeclared
      have hcompiled :
          GraphConsistencyP compiled.graph :=
        (graphConsistency_eq_graphConsistencyP compiled.graph).mp
          (hnonSacrificed GovernanceProperty.Consistency hnotDeclared)
      have hG : GraphConsistencyP G :=
        (GraphConsistencyP_congr heq).mpr hcompiled
      exact hobstruction hG
    let trigger : StatefulCriticalCapabilityViolation D :=
      { adv := adv
        schedule := schedule
        cfg := initialStatefulAdversaryConfig D adv
        critical_le_budget := hcritical }
    let cert : MonitoredSacrificeCertificate D D :=
      MonitoredSacrificeCertificate.ofCompiledPropertyWithAggregatorWitness
        (KernelStep.refl D) compiled monitoring GovernanceProperty.Consistency
        hwitness.claims hwitness.denied hgraph hconsDeclared
        (MonitoringBoundExceedance.oneObservedPropertyFailure compiled
          GovernanceProperty.Consistency
          (compiled.witness.sacrifices_justified GovernanceProperty.Consistency
            hconsDeclared))
        (some AggregatorAxiomWitnessKind.consistencyViolation)
        (some trigger)
    refine ⟨cert, ?_, ?_⟩
    · exact ⟨rfl, rfl, hobstruction, hwitness.denied_decision,
        hwitness.survivor_permitted,
        hwitness.survivor_denied_after_removal, rfl, rfl⟩
    · exact ⟨hcritical, rfl⟩
  · intro hsubcritical
    exact
      stateful_budgeted_subcritical_trajectory_preserves_stable_state_decisions
        D adv hδ hcv schedule hsubcritical

end Safety

end Legitimacy
