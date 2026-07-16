/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.PeerRelativeClass
import Legitimacy.Kernel.Data
import Legitimacy.Kernel.Examples

/-!
# Legitimacy.Kernel.DAGBinaryBridge

A narrow model-map contract from the richer governed-system/DAG substrate to
the binary pipeline substrate used by the peer-relative impossibility theorem.

This module does not claim that every operational DAG automatically reduces to
the binary theorem. It states the exact bridge condition needed to transfer the
theorem: the governed system's graph must be reflected by its DAG and
decision-equivalent to a binary pipeline whose first effective decision surface
is complete and peer-relative.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A governed system has a binary model map when its DAG reflects its carried
governance graph and that graph is externally decision-equivalent to a chosen
binary pipeline. This is the formal contract that separates DAG/source
interpretation from the binary theorem substrate. -/
structure DAGToBinaryModelMap {n : Nat}
    (sys : GovernedSystem n) (binary : GovernanceGraph) : Prop where
  reflects_graph : DagReflectsGraph sys.dag sys.graph
  decision_equiv : GovernanceGraphEquivalent sys.graph binary

/-- A governed system has a model map into an arbitrary decision
pipeline when its DAG reflects its carried governance graph and that graph is
externally decision-equivalent to the target pipeline. -/
structure DAGToPipelineModelMap {n : Nat} {P : Type}
    [DecisionPipeline P] (sys : GovernedSystem n) (pipeline : P) :
    Prop where
  reflects_graph : DagReflectsGraph sys.dag sys.graph
  decision_equiv : DecisionSystem.Equivalent sys.graph pipeline

/-- The DAG-to-pipeline bridge is functorial in the target pipeline up to
decision-system equivalence. -/
def DAGToPipelineModelMap.map {n : Nat} {P Q : Type}
    [DecisionPipeline P] [DecisionPipeline Q] {sys : GovernedSystem n}
    {pipeline : P} {target : Q}
    (hmap : DAGToPipelineModelMap sys pipeline)
    (heq : DecisionSystem.Equivalent pipeline target) :
    DAGToPipelineModelMap sys target where
  reflects_graph := hmap.reflects_graph
  decision_equiv := DecisionSystem.Equivalent.trans hmap.decision_equiv heq

/-- The binary bridge maps into any decision pipeline equivalent to its binary
representative. -/
def DAGToBinaryModelMap.toPipeline {n : Nat} {P : Type}
    [DecisionPipeline P] {sys : GovernedSystem n}
    {binary : GovernanceGraph} {pipeline : P}
    (hmap : DAGToBinaryModelMap sys binary)
    (heq : DecisionSystem.Equivalent binary pipeline) :
    DAGToPipelineModelMap sys pipeline where
  reflects_graph := hmap.reflects_graph
  decision_equiv := by
    intro claims k
    exact (hmap.decision_equiv claims k).trans (heq claims k)

/-- The original governance-graph bridge is the `GovernanceGraph`
specialization of the pipeline bridge. -/
theorem dagToBinaryModelMap_eq_pipeline
    {n : Nat} (sys : GovernedSystem n) (G : GovernanceGraph) :
    DAGToBinaryModelMap sys G ↔ DAGToPipelineModelMap sys G := by
  constructor
  · intro h
    exact
      { reflects_graph := h.reflects_graph
        decision_equiv := h.decision_equiv }
  · intro h
    exact
      { reflects_graph := h.reflects_graph
        decision_equiv := h.decision_equiv }

/-- A model-mapped DAG system falls under the peer-relative theorem exactly when
the binary representative has a complete first-effective peer-relative surface. -/
structure DAGPeerRelativeSurfaceMap {n : Nat}
    (sys : GovernedSystem n)
    (binary pref tail : GovernanceGraph) : Prop where
  model_map : DAGToBinaryModelMap sys binary
  effective_surface : EffectivePeerRelativeSurface binary pref tail
  complete_tail : CompletePeerRelativeTail tail

/-- Pipeline-level DAG bridge theorem: a governed system model-mapped into a
complete first-effective peer-relative aggregator pipeline inherits the generic
three-diagnostic obstruction through decision-system equivalence. -/
theorem dagPeerRelativeSurfaceMap_pipeline_impossibility
    {n : Nat} {P : Type} [DecisionPipeline P]
    (sys : GovernedSystem n) (pipeline : P)
    (node : DecisionPipeline.NodeOf P)
    (hagg : DecisionPipeline.IsPeerRelativeAggregator node)
    (heffective : ∃ pref tail,
      DecisionPipeline.EffectiveSurfaceForNode node pipeline pref tail ∧
        DecisionPipeline.CompleteTailForNode node tail)
    (hmodel : DAGToPipelineModelMap sys pipeline) :
    ¬ (GraphConsistencyP sys.graph ∧ GraphSolidarityP sys.graph ∧
      GraphMonotonicityP sys.graph) := by
  intro haxioms
  have hpipeline :
      GraphConsistencyP pipeline ∧ GraphSolidarityP pipeline ∧
        GraphMonotonicityP pipeline :=
    ⟨(GraphConsistencyP_congr hmodel.decision_equiv).mp haxioms.1,
      (GraphSolidarityP_congr hmodel.decision_equiv).mp haxioms.2.1,
      (GraphMonotonicityP_congr hmodel.decision_equiv).mp haxioms.2.2⟩
  exact decisionPipeline_existsClass_three_axiom_obstruction
    pipeline node hagg heffective hpipeline

/-- The binary representative of a mapped complete first-effective surface is
decision-equivalent to the canonical peer graph. -/
theorem dagPeerRelativeSurfaceMap_equiv_peerGraph
    {n : Nat} {sys : GovernedSystem n}
    {binary pref tail : GovernanceGraph}
    (hmap : DAGPeerRelativeSurfaceMap sys binary pref tail) :
    GovernanceGraphEquivalent sys.graph peerGraph := by
  intro claims k
  trans graphDecide binary claims k
  · exact hmap.model_map.decision_equiv claims k
  · exact effectivePeerRelativeSurface_complete_equiv_peerGraph
      binary pref tail hmap.effective_surface hmap.complete_tail claims k

/-- Concrete DAG-to-binary impossibility derived through the pipeline bridge
specialized to `GovernanceGraph`. -/
theorem dagPeerRelativeSurfaceMap_impossibility_via_pipeline
    {n : Nat} {sys : GovernedSystem n}
    {binary pref tail : GovernanceGraph}
    (hmap : DAGPeerRelativeSurfaceMap sys binary pref tail) :
    ¬ AllLegitimacyAxioms sys.graph := by
  intro haxioms
  have hmodel : DAGToPipelineModelMap sys binary :=
    (dagToBinaryModelMap_eq_pipeline sys binary).mp hmap.model_map
  have hsurface :
      ∃ pref tail,
        BinaryDecisionPipeline.EffectiveSurfaceForNode
            (P := GovernanceGraph) peerRelativeNode binary pref tail ∧
          BinaryDecisionPipeline.CompleteTailForNode
            (P := GovernanceGraph) peerRelativeNode tail :=
    ⟨pref, tail, effectiveSurface_specialize hmap.effective_surface,
      completeTail_specialize hmap.complete_tail⟩
  have hobstruction :
      ¬ (GraphConsistencyP sys.graph ∧ GraphSolidarityP sys.graph ∧
        GraphMonotonicityP sys.graph) :=
    dagPeerRelativeSurfaceMap_pipeline_impossibility
      sys binary peerRelativeNode peerRelativeNode_isPeerRelativeAggregator
      hsurface hmodel
  exact hobstruction
    ⟨(graphConsistency_eq_graphConsistencyP sys.graph).mp haxioms.1,
      (graphSolidarity_eq_graphSolidarityP sys.graph).mp haxioms.2.1,
      (graphMonotonicity_eq_graphMonotonicityP sys.graph).mp haxioms.2.2.1⟩

/-- DAG-to-binary bridge theorem: once an operational DAG system is mapped to a
complete first-effective peer-relative binary surface, the graph-diagnostic
impossibility transfers back to the governed system's own graph. -/
theorem dagPeerRelativeSurfaceMap_impossibility
    {n : Nat} {sys : GovernedSystem n}
    {binary pref tail : GovernanceGraph}
    (hmap : DAGPeerRelativeSurfaceMap sys binary pref tail) :
    ¬ AllLegitimacyAxioms sys.graph :=
  dagPeerRelativeSurfaceMap_impossibility_via_pipeline hmap

/-- Strong form of the bridge: the mapped governed system also inherits the
canonical monotonicity and strategyproofness failures. -/
theorem dagPeerRelativeSurfaceMap_impossibility_strong
    {n : Nat} {sys : GovernedSystem n}
    {binary pref tail : GovernanceGraph}
    (hmap : DAGPeerRelativeSurfaceMap sys binary pref tail) :
    ¬ GraphMonotonicity sys.graph ∧ ¬ GraphStrategyproofness sys.graph := by
  have heq : GovernanceGraphEquivalent sys.graph peerGraph :=
    dagPeerRelativeSurfaceMap_equiv_peerGraph hmap
  constructor
  · intro hmon
    exact peerGraph_not_monotone ((graphMonotonicity_congr heq).mp hmon)
  · intro hsp
    exact peerGraph_not_strategyproof ((graphStrategyproofness_congr heq).mp hsp)

/-! ## Bridge-field tightness witnesses -/

/-- Audit form of the binary transfer proof: DAG reflection is part of the
model-map semantics, but the binary decision-equivalence transfer itself uses
only decision equivalence, the effective peer-relative surface, and tail
completeness. -/
theorem dagPeerRelativeSurfaceMap_binary_transfer_without_reflects_graph
    {n : Nat} {sys : GovernedSystem n}
    {binary pref tail : GovernanceGraph}
    (hdecision : GovernanceGraphEquivalent sys.graph binary)
    (heffective : EffectivePeerRelativeSurface binary pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    GovernanceGraphEquivalent sys.graph peerGraph := by
  intro claims k
  trans graphDecide binary claims k
  · exact hdecision claims k
  · exact effectivePeerRelativeSurface_complete_equiv_peerGraph
      binary pref tail heffective hcomplete claims k

/-- The `reflects_graph` field of `DAGToBinaryModelMap` is definitionally
recoverable from the carried governed system. Every `GovernedSystem n` already
witnesses `DagReflectsGraph dag graph`, so the bridge field is structural
documentation rather than an independent obligation.

INTENTIONAL: the DAG bridge-field followup strengthens the redundancy claim by
proving derivability instead of deleting the documented field. -/
theorem dagBridge_reflects_graph_definitionally_redundant
    {n : Nat} (sys : GovernedSystem n) :
    DagReflectsGraph sys.dag sys.graph :=
  sys.dag_reflects_graph

/-! ## Worked DAG-to-binary model-map family -/

/-- A governed system whose operational DAG has a declared peer-relative
chokepoint and whose carried binary surface decomposes into deterministic
transparent refinement before the chokepoint and permit-preserving refinement
after it.

The current `CausalDAG` substrate records causal edges rather than per-node
decision functions, so the operational content of the chokepoint is expressed by
the governed system's carried graph decomposition. This is stronger than merely
supplying `DAGToBinaryModelMap.decision_equiv`: the decision equivalence is
derived below from the decomposition theorem for complete first-effective
peer-relative surfaces. -/
structure SinglePeerChokepointGovernedSystem (n : Nat) where
  /-- The governed system carrying the operational DAG and graph. -/
  base : GovernedSystem n
  /-- The DAG variable declared as the peer-relative chokepoint. -/
  chokepoint : Fin n
  /-- The chokepoint lies inside the governed causal boundary. -/
  chokepoint_governed : base.governed.governed chokepoint
  /-- Deterministic refinement before the peer-relative chokepoint. -/
  deterministic_prefix : GovernanceGraph
  /-- Deterministic or permit-preserving refinement after the chokepoint. -/
  deterministic_tail : GovernanceGraph
  /-- The carried graph has exactly one first-effective peer-relative surface at
  the declared chokepoint stage. -/
  graph_decomposes :
    base.graph = List.append deterministic_prefix (peerRelativeNode :: deterministic_tail)
  /-- Prefix stages are transparent deterministic refinements: they never alter a
  claimant's permit/deny status before the peer-relative chokepoint. -/
  prefix_transparent : TransparentPrefix deterministic_prefix
  /-- Downstream refinement preserves every permit emitted by the peer-relative
  chokepoint. -/
  tail_preserves_peer_permits : CompletePeerRelativeTail deterministic_tail

/-- A single-peer-chokepoint governed system has the first-effective
peer-relative surface required by the binary theorem. -/
theorem singlePeerChokepointGovernedSystem_effective_surface
    {n : Nat} (S : SinglePeerChokepointGovernedSystem n) :
    EffectivePeerRelativeSurface S.base.graph S.deterministic_prefix
      S.deterministic_tail :=
  ⟨S.graph_decomposes, S.prefix_transparent⟩

/-- For every single-peer-chokepoint governed system, the canonical binary
pipeline `[peerRelativeNode]` is a decision-equivalent representative. -/
theorem singlePeerChokepointGovernedSystem_admits_binary_modelMap
    {n : Nat} (S : SinglePeerChokepointGovernedSystem n) :
    DAGToBinaryModelMap S.base peerGraph where
  reflects_graph := S.base.dag_reflects_graph
  decision_equiv :=
    effectivePeerRelativeSurface_complete_equiv_peerGraph S.base.graph
      S.deterministic_prefix S.deterministic_tail
      (singlePeerChokepointGovernedSystem_effective_surface S)
      S.tail_preserves_peer_permits

/-- Every single-peer-chokepoint governed system also maps through the
parameterized pipeline bridge specialized to the canonical peer graph. -/
theorem singlePeerChokepointGovernedSystem_admits_pipeline_modelMap
    {n : Nat} (S : SinglePeerChokepointGovernedSystem n) :
    DAGToPipelineModelMap S.base peerGraph :=
  (dagToBinaryModelMap_eq_pipeline S.base peerGraph).mp
    (singlePeerChokepointGovernedSystem_admits_binary_modelMap S)

/-- The single-peer-chokepoint family is not merely mapped to a binary
representative; it maps to the complete first-effective peer-relative surface
used by the impossibility theorem. -/
theorem singlePeerChokepointGovernedSystem_peerSurfaceMap
    {n : Nat} (S : SinglePeerChokepointGovernedSystem n) :
    DAGPeerRelativeSurfaceMap S.base peerGraph [] [] where
  model_map := singlePeerChokepointGovernedSystem_admits_binary_modelMap S
  effective_surface := by
    constructor
    · simp [peerGraph]
    · intro node hmem
      cases hmem
  complete_tail := by
    intro claims k hpermit
    simp [graphDecide]

/-- Worked DAG bridge example: every single-peer-chokepoint governed system
falls under the binary peer-relative impossibility theorem by a proved
model-map, rather than by a user-supplied `decision_equiv` promise. -/
theorem singlePeerChokepointGovernedSystem_impossibility
    {n : Nat} (S : SinglePeerChokepointGovernedSystem n) :
    ¬ AllLegitimacyAxioms S.base.graph :=
  dagPeerRelativeSurfaceMap_impossibility
    (singlePeerChokepointGovernedSystem_peerSurfaceMap S)

/-- Causal chain for the canonical worked example:
input variable `0`, peer-relative chokepoint `1`, output variable `2`. -/
def canonicalSinglePeerChokepointEdge : Fin 3 → Fin 3 → Prop := fun i j =>
  (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 2)

instance canonicalSinglePeerChokepointEdge_dec :
    DecidableRel canonicalSinglePeerChokepointEdge := by
  intro i j
  unfold canonicalSinglePeerChokepointEdge
  infer_instance

/-- The concrete input -> peer chokepoint -> output operational DAG used by
the worked single-peer-chokepoint inhabitant. -/
def canonicalSinglePeerChokepointDAG : CausalDAG 3 where
  edge := canonicalSinglePeerChokepointEdge
  acyclic := by
    intro i j h
    rcases h with h | h
    · omega
    · omega
  edge_dec := canonicalSinglePeerChokepointEdge_dec

private lemma canonicalPeerGraph_permitClaim :
    graphDecide peerGraph [permitClaim] permitClaim.id =
      BinaryDecision.Permit := by
  -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
  native_decide

private lemma canonicalPeerGraphTrace_consistent :
    TraceConsistentWithGraph permitTrace peerGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, permitTrace]
  exact ⟨[permitClaim], by simp, canonicalPeerGraph_permitClaim⟩

private lemma canonicalSinglePeerChokepointDAG_reflects_peerGraph :
    DagReflectsGraph canonicalSinglePeerChokepointDAG peerGraph := by
  intro i j hedge
  refine ⟨0, by simp [peerGraph], ?_⟩
  exact canonicalSinglePeerChokepointDAG.acyclic i j hedge

/-- Concrete governed system carried by the canonical single-peer-chokepoint
example. The graph is the singleton peer-relative gate; the DAG records the
surrounding input and output variables. -/
def canonicalSinglePeerChokepointBase : GovernedSystem 3 where
  graph := peerGraph
  state := permitState
  trace := permitTrace
  dag := canonicalSinglePeerChokepointDAG
  governed := allGoverned 3
  trace_consistent := canonicalPeerGraphTrace_consistent
  dag_reflects_graph := canonicalSinglePeerChokepointDAG_reflects_peerGraph

/-- A concrete inhabitant of `SinglePeerChokepointGovernedSystem`: transparent
input, first-effective peer-relative chokepoint, and empty permit-preserving
output refinement. -/
def canonicalSinglePeerChokepointSystem :
    SinglePeerChokepointGovernedSystem 3 where
  base := canonicalSinglePeerChokepointBase
  chokepoint := ⟨1, by norm_num⟩
  chokepoint_governed := trivial
  deterministic_prefix := []
  deterministic_tail := []
  graph_decomposes := rfl
  prefix_transparent := by
    intro node hmem
    cases hmem
  tail_preserves_peer_permits := by
    intro claims k hpermit
    simp [graphDecide]

/-- Worked model-map discharge for the concrete single-peer-chokepoint
inhabitant. -/
theorem canonicalSinglePeerChokepointSystem_admits_binary_modelMap :
    DAGToBinaryModelMap canonicalSinglePeerChokepointSystem.base peerGraph :=
  singlePeerChokepointGovernedSystem_admits_binary_modelMap
    canonicalSinglePeerChokepointSystem

/-- Worked parameterized model-map discharge for the concrete
single-peer-chokepoint inhabitant. -/
theorem canonicalSinglePeerChokepointSystem_admits_pipeline_modelMap :
    DAGToPipelineModelMap (P := GovernanceGraph)
      canonicalSinglePeerChokepointSystem.base
      (peerRelativeNode :: [] : GovernanceGraph) :=
  singlePeerChokepointGovernedSystem_admits_pipeline_modelMap
    canonicalSinglePeerChokepointSystem

private def bridgeAllPermitGraph : GovernanceGraph :=
  [fun _ _ => BinaryDecision.Permit]

private lemma bridgeAllPermitGraph_allAxioms :
    AllLegitimacyAxioms bridgeAllPermitGraph := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    intro claims <;>
    simp [bridgeAllPermitGraph, graphDecide]

private lemma bridgeAllPermitTrace_consistent :
    TraceConsistentWithGraph permitTrace bridgeAllPermitGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, permitTrace]
  exact ⟨[permitClaim], by simp, by simp [bridgeAllPermitGraph, graphDecide]⟩

private def bridgeAllPermitSystem : GovernedSystem 1 where
  graph := bridgeAllPermitGraph
  state := permitState
  trace := permitTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := bridgeAllPermitTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 bridgeAllPermitGraph

private lemma bridgeAllPermitGraph_not_equiv_peerGraph :
    ¬ GovernanceGraphEquivalent bridgeAllPermitGraph peerGraph := by
  intro heq
  exact peerGraph_impossibility
    ((allLegitimacyAxioms_congr heq).mp bridgeAllPermitGraph_allAxioms)

private lemma bridgeEmptyTail_complete :
    CompletePeerRelativeTail [] := by
  intro claims k hpermit
  simp [graphDecide]

private lemma bridgePeerGraph_effective_surface :
    EffectivePeerRelativeSurface peerGraph [] [] := by
  constructor
  · rfl
  · intro node hmem
    cases hmem

/-- Dropping `decision_equiv` breaks the bridge: the governed system may have a
diagnostically admissible constant-permit graph while the chosen binary graph
has the complete peer-relative surface. -/
theorem dagBridge_decision_equiv_field_independent :
    ∃ (sys : GovernedSystem 1) (binary pref tail : GovernanceGraph),
      DagReflectsGraph sys.dag sys.graph ∧
      EffectivePeerRelativeSurface binary pref tail ∧
      CompletePeerRelativeTail tail ∧
      AllLegitimacyAxioms sys.graph ∧
      ¬ GovernanceGraphEquivalent sys.graph peerGraph := by
  refine ⟨bridgeAllPermitSystem, peerGraph, [], [], ?_, ?_, ?_, ?_, ?_⟩
  · exact bridgeAllPermitSystem.dag_reflects_graph
  · exact bridgePeerGraph_effective_surface
  · exact bridgeEmptyTail_complete
  · exact bridgeAllPermitGraph_allAxioms
  · exact bridgeAllPermitGraph_not_equiv_peerGraph

/-- Dropping `effective_surface` breaks the bridge: model-map equivalence and
tail completeness alone allow a constant-permit binary representative, which is
not equivalent to the peer graph. -/
theorem dagBridge_effective_surface_field_independent :
    ∃ (sys : GovernedSystem 1) (binary pref tail : GovernanceGraph),
      DAGToBinaryModelMap sys binary ∧
      TransparentPrefix pref ∧
      CompletePeerRelativeTail tail ∧
      AllLegitimacyAxioms sys.graph ∧
      ¬ GovernanceGraphEquivalent sys.graph peerGraph := by
  refine ⟨bridgeAllPermitSystem, bridgeAllPermitGraph, [], [], ?_, ?_, ?_, ?_, ?_⟩
  · exact
      { reflects_graph := bridgeAllPermitSystem.dag_reflects_graph
        decision_equiv := by
          intro claims k
          rfl }
  · intro node hmem
    cases hmem
  · exact bridgeEmptyTail_complete
  · exact bridgeAllPermitGraph_allAxioms
  · exact bridgeAllPermitGraph_not_equiv_peerGraph

private def bridgeDenyNode : GovernanceNodeFn :=
  fun _ _ => BinaryDecision.Deny

private def bridgePeerThenDenyGraph : GovernanceGraph :=
  [peerRelativeNode, bridgeDenyNode]

private lemma bridgePeerThenDenyGraph_denies
    (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide bridgePeerThenDenyGraph claims k = BinaryDecision.Deny := by
  cases hpeer : peerRelativeNode claims k <;>
    simp [bridgePeerThenDenyGraph, bridgeDenyNode, graphDecide, hpeer]

private lemma bridgePeerThenDenyGraph_allAxioms :
    AllLegitimacyAxioms bridgePeerThenDenyGraph := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro claims k j hk hj hkj hdist hdeny
    simp [bridgePeerThenDenyGraph_denies]
  · intro claims α hα j hj
    simp [bridgePeerThenDenyGraph_denies]
  · intro claims k s' hs' j hk hdist hle hperm
    rw [bridgePeerThenDenyGraph_denies claims j] at hperm
    exact BinaryDecision.noConfusion hperm
  · intro claims k s_r hs_r hk hdist hperm
    rw [bridgePeerThenDenyGraph_denies (strengthenClaim k s_r hs_r claims) k] at hperm
    exact BinaryDecision.noConfusion hperm

private def bridgeDenyTrace : GovernanceTrace :=
  fun _ => (permitClaim, some GovernanceOutcome.deny)

private lemma bridgeDenyTrace_consistent :
    TraceConsistentWithGraph bridgeDenyTrace bridgePeerThenDenyGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, bridgeDenyTrace]
  exact ⟨[permitClaim], by simp,
    bridgePeerThenDenyGraph_denies [permitClaim] permitClaim.id⟩

private def bridgePeerThenDenySystem : GovernedSystem 1 where
  graph := bridgePeerThenDenyGraph
  state := permitState
  trace := bridgeDenyTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := bridgeDenyTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 bridgePeerThenDenyGraph

private lemma bridgePeerThenDeny_effective_surface :
    EffectivePeerRelativeSurface bridgePeerThenDenyGraph [] [bridgeDenyNode] := by
  constructor
  · rfl
  · intro node hmem
    cases hmem

private lemma bridgePeerThenDeny_not_equiv_peerGraph :
    ¬ GovernanceGraphEquivalent bridgePeerThenDenyGraph peerGraph := by
  intro heq
  have hdeny :
      graphDecide bridgePeerThenDenyGraph [permitClaim] permitClaim.id =
        BinaryDecision.Deny :=
    bridgePeerThenDenyGraph_denies [permitClaim] permitClaim.id
  have hpeer :
      graphDecide peerGraph [permitClaim] permitClaim.id =
        BinaryDecision.Permit := by
    -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
    native_decide
  rw [heq [permitClaim] permitClaim.id] at hdeny
  rw [hpeer] at hdeny
  exact BinaryDecision.noConfusion hdeny

/-- Dropping `complete_tail` breaks the bridge: a peer-relative head followed
by a deny-all tail has the required effective surface and model map, but it is
not decision-equivalent to the canonical peer graph. -/
theorem dagBridge_complete_tail_field_independent :
    ∃ (sys : GovernedSystem 1) (binary pref tail : GovernanceGraph),
      DAGToBinaryModelMap sys binary ∧
      EffectivePeerRelativeSurface binary pref tail ∧
      AllLegitimacyAxioms sys.graph ∧
      ¬ GovernanceGraphEquivalent sys.graph peerGraph := by
  refine ⟨bridgePeerThenDenySystem, bridgePeerThenDenyGraph, [],
    [bridgeDenyNode], ?_, ?_, ?_, ?_⟩
  · exact
      { reflects_graph := bridgePeerThenDenySystem.dag_reflects_graph
        decision_equiv := by
          intro claims k
          rfl }
  · exact bridgePeerThenDeny_effective_surface
  · exact bridgePeerThenDenyGraph_allAxioms
  · exact bridgePeerThenDeny_not_equiv_peerGraph

end Legitimacy
