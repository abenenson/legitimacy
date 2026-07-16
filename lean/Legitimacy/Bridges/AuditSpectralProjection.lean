/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit
import Legitimacy.Spectral.Core.Localizability

/-!
# Legitimacy.Bridges.AuditSpectralProjection

Generic projection from extracted audit governance graphs to finite spectral
carriers, together with the audit-derived terminal-threshold signal used by the
case-study repair path.
-/

set_option autoImplicit false

namespace Legitimacy

/-!
## Audit graph to spectral carrier projection
-/

/-- Node id at a concrete list position in an extracted audit graph. -/
def AuditGovernanceGraph.nodeIdAt?
    (g : AuditGovernanceGraph) (i : ℕ) : Option AuditNodeId :=
  (g.nodes[i]?).map AuditGovernanceNode.id

/-- Directed edge predicate between concrete list positions. -/
def AuditGovernanceGraph.directedEdgeAt
    (g : AuditGovernanceGraph) (i j : ℕ) : Bool :=
  match g.nodeIdAt? i, g.nodeIdAt? j with
  | some fromId, some toId =>
      g.edges.any fun edge =>
        edge.fromNode == fromId && edge.toNode == toId
  | _, _ => false

/-- Symmetrized adjacency predicate between concrete list positions. -/
def AuditGovernanceGraph.spectralAdjacent
    (g : AuditGovernanceGraph) (i j : ℕ) : Bool :=
  g.directedEdgeAt i j || g.directedEdgeAt j i

/-- Symmetry of the audit-graph symmetrized adjacency predicate. -/
theorem AuditGovernanceGraph.spectralAdjacent_symm
    (g : AuditGovernanceGraph) (i j : ℕ) :
    g.spectralAdjacent i j = g.spectralAdjacent j i := by
  simp [AuditGovernanceGraph.spectralAdjacent, Bool.or_comm]

/-- Spectral carrier obtained by symmetrizing the extracted audit graph's edge
surface over the first `n` list positions. Missing list positions are isolated,
self-loops are suppressed, and every present extracted edge has unit weight. -/
def AuditGovernanceGraph.spectralProjection
    (g : AuditGovernanceGraph) (n : ℕ) : GovGraph ℚ n where
  weights := fun i j =>
    if i ≠ j ∧ g.spectralAdjacent i.val j.val then 1 else 0
  weight_symm := by
    intro i j
    by_cases hne : i ≠ j
    · have hne' : j ≠ i := Ne.symm hne
      simp [hne, hne', AuditGovernanceGraph.spectralAdjacent_symm g i.val j.val]
    · have hne' : ¬ j ≠ i := by
        simpa [ne_comm] using hne
      simp [hne, hne']
  weight_nonneg := by
    intro i j
    split <;> norm_num
  weight_self_zero := by
    intro i
    simp

/-!
## General adjudicated threshold repair signal
-/

/-- A threshold gate is a terminal threshold rejection when the threshold match
routes to a decision below `.permit` in the production audit rank lattice.
Non-threshold gates are outside this class predicate. -/
def thresholdGateMonotonicityRejection : AuditGate → Bool
  | .thresholdGate _ _ decision => decisionRank decision < decisionRank .permit
  | _ => false

/-- Node-level primitive predicate for a terminal threshold-rejection gate. -/
def nodeContainsThresholdMonotonicityRejection :
    AuditGovernanceNode → Bool
  | .binary _ _ gates _ _ =>
      gates.any thresholdGateMonotonicityRejection
  | _ => false

/-- Graph-level primitive predicate for the structural class C: extracted audit
graphs containing at least one threshold gate whose match routes to a terminal
decision below `.permit`. This is not the repair conclusion and does not assert
anything about the repaired graph. -/
def ContainsThresholdMonotonicityRejection
    (graph : AuditGovernanceGraph) : Bool :=
  graph.nodes.any nodeContainsThresholdMonotonicityRejection

/-- Extracted audit subjects in class C additionally fail the production
monotonicity check. This Prop-level predicate is used for harness
characterization; the general repair theorem is over arbitrary graphs and does
not use this as a bundled discharge. -/
def ThresholdGateMonotonicityRejectionSubject
    (subject : AuditSubject) : Prop :=
  ContainsThresholdMonotonicityRejection subject.graph = true ∧
    auditCheckStatus subject AuditCheck.monotonicity = .ok .failed

/-- A threshold gate is adjudicated when threshold matches are no longer
terminal deny/escalate decisions. Non-threshold gates are outside the
threshold-repair surface. -/
def thresholdGateAdjudicated : AuditGate → Bool
  | .thresholdGate _ _ decision => decision == .permit
  | _ => true

/-- Node-level threshold-adjudication predicate. -/
def nodeThresholdAdjudicated : AuditGovernanceNode → Bool
  | .binary _ _ gates _ _ => gates.all thresholdGateAdjudicated
  | _ => true

/-- Graph-level threshold-adjudication predicate for arbitrary extracted audit
graphs. -/
def graph_threshold_adjudicated (graph : AuditGovernanceGraph) : Bool :=
  graph.nodes.all nodeThresholdAdjudicated

/-- General repair: map every threshold gate to adjudicated permit evidence.
All other gate types are left unchanged. -/
def adjudicateThresholdGate : AuditGate → AuditGate
  | .thresholdGate field min _decision => .thresholdGate field min .permit
  | gate => gate

/-- Apply `adjudicateThresholdGate` to binary audit nodes. -/
def adjudicateThresholdNode : AuditGovernanceNode → AuditGovernanceNode
  | .binary id name gates default combination =>
      .binary id name (gates.map adjudicateThresholdGate) default combination
  | node => node

/-- General adjudicated repair over arbitrary extracted audit graphs. The repair
changes only node gates; graph edges are preserved. -/
def adjudicateThresholdGraph
    (graph : AuditGovernanceGraph) : AuditGovernanceGraph :=
  { nodes := graph.nodes.map adjudicateThresholdNode
    edges := graph.edges }

/-- The gate-level repair always satisfies the adjudicated-threshold predicate. -/
theorem adjudicateThresholdGate_threshold_adjudicated
    (gate : AuditGate) :
    thresholdGateAdjudicated (adjudicateThresholdGate gate) = true := by
  cases gate <;> simp [thresholdGateAdjudicated, adjudicateThresholdGate]

/-- The node-level repair always satisfies the adjudicated-threshold predicate. -/
theorem adjudicateThresholdNode_threshold_adjudicated
    (node : AuditGovernanceNode) :
    nodeThresholdAdjudicated (adjudicateThresholdNode node) = true := by
  cases node <;>
    simp [nodeThresholdAdjudicated, adjudicateThresholdNode,
      adjudicateThresholdGate_threshold_adjudicated]

/-- General repair theorem, graph side: adjudicating an arbitrary audit graph
forces every threshold gate in the repaired graph to carry `.permit`. -/
theorem graph_threshold_adjudicated_adjudicateThresholdGraph
    (graph : AuditGovernanceGraph) :
    graph_threshold_adjudicated
      (adjudicateThresholdGraph graph) = true := by
  cases graph
  simp [graph_threshold_adjudicated, adjudicateThresholdGraph,
    adjudicateThresholdNode_threshold_adjudicated]

/-- The general adjudication repair preserves the graph edge surface. -/
theorem adjudicateThresholdGraph_edges
    (graph : AuditGovernanceGraph) :
    (adjudicateThresholdGraph graph).edges = graph.edges := by
  rfl

/-- Decision-rank projection for terminal threshold gates. It is positive for
terminal decisions below `.permit` and zero for adjudicated permit evidence. -/
def thresholdDecisionSpectralComponent : AuditDecision → ℚ
  | .deny => 2
  | .escalate => 1
  | .permit => 0

/-- Gate-level audit-to-spectral projection. Only threshold gates contribute to
this repair surface; all other gate forms remain spectrally silent here. -/
def thresholdGateSpectralComponent : AuditGate → ℚ
  | .thresholdGate _ _ decision =>
      thresholdDecisionSpectralComponent decision
  | _ => 0

/-- Node-level audit-to-spectral projection: sum the terminal-threshold
components carried by the node's binary gates. -/
def nodeThresholdSpectralComponent : AuditGovernanceNode → ℚ
  | .binary _ _ gates _ _ =>
      (gates.map thresholdGateSpectralComponent).sum
  | _ => 0

/-- List-indexed audit-to-spectral projection used by
`auditGraphThresholdSignal`. -/
def auditNodesThresholdSignalAt :
    List AuditGovernanceNode → Nat → ℚ
  | [], _ => 0
  | node :: _, 0 => nodeThresholdSpectralComponent node
  | _ :: nodes, index + 1 =>
      auditNodesThresholdSignalAt nodes index

/-- Audit-graph-derived threshold signal. Coordinate `i` projects the `i`th
audit node, if present, to its terminal-threshold decision-rank component. -/
def auditGraphThresholdSignal
    (graph : AuditGovernanceGraph) {n : Nat} [NeZero n] : Fin n → ℚ :=
  fun i => auditNodesThresholdSignalAt graph.nodes i.val

/-- The primitive graph-side class predicate paired with the scoped spectral
fact used by the legacy concrete witnesses. The class-C conjunct records why
threshold adjudication is the relevant repair family, while the strict spectral
bound below is deliberately stated only over the load-bearing positivity fact:
an arbitrary supplied spectral topology does not make class-C membership alone
imply positive `cv`. -/
def ThresholdRepairSpectralWitness
    {n : Nat} [NeZero n]
    (spectralGraph : GovGraph ℚ n)
    (graph : AuditGovernanceGraph) : Prop :=
  ContainsThresholdMonotonicityRejection graph = true ∧
    0 < spectralGraph.cv (auditGraphThresholdSignal graph)

/-- Load-bearing strict spectral premise for threshold adjudication. -/
def ThresholdRepairStrictSpectralWitness
    {n : Nat} [NeZero n]
    (spectralGraph : GovGraph ℚ n)
    (graph : AuditGovernanceGraph) : Prop :=
  0 < spectralGraph.cv (auditGraphThresholdSignal graph)

/-- A legacy class-C spectral witness projects to the strict spectral premise. -/
theorem ThresholdRepairSpectralWitness.strict
    {n : Nat} [NeZero n]
    {spectralGraph : GovGraph ℚ n}
    {graph : AuditGovernanceGraph}
    (hwitness :
      ThresholdRepairSpectralWitness spectralGraph graph) :
    ThresholdRepairStrictSpectralWitness spectralGraph graph :=
  hwitness.2

/-- The gate-level repair removes terminal-threshold spectral mass. -/
theorem thresholdGateSpectralComponent_adjudicateThresholdGate
    (gate : AuditGate) :
    thresholdGateSpectralComponent (adjudicateThresholdGate gate) = 0 := by
  cases gate <;>
    simp [thresholdGateSpectralComponent, adjudicateThresholdGate,
      thresholdDecisionSpectralComponent]

/-- An adjudicated gate has no terminal-threshold spectral component. -/
theorem thresholdGateSpectralComponent_eq_zero_of_thresholdGateAdjudicated
    (gate : AuditGate)
    (hgate : thresholdGateAdjudicated gate = true) :
    thresholdGateSpectralComponent gate = 0 := by
  cases gate <;>
    simp [thresholdGateAdjudicated, thresholdGateSpectralComponent,
      thresholdDecisionSpectralComponent] at hgate ⊢
  cases hgate
  rfl

/-- A list of adjudicated gates has no terminal-threshold spectral component. -/
theorem thresholdGateSpectralComponent_sum_eq_zero_of_all_adjudicated
    (gates : List AuditGate)
    (hgates : gates.all thresholdGateAdjudicated = true) :
    (gates.map thresholdGateSpectralComponent).sum = 0 := by
  induction gates with
  | nil =>
      simp
  | cons gate rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hgates
      rcases hgates with ⟨hgate, hrest⟩
      simp [thresholdGateSpectralComponent_eq_zero_of_thresholdGateAdjudicated
        gate hgate, ih hrest]

/-- An adjudicated node has no terminal-threshold spectral component. -/
theorem nodeThresholdSpectralComponent_eq_zero_of_nodeThresholdAdjudicated
    (node : AuditGovernanceNode)
    (hnode : nodeThresholdAdjudicated node = true) :
    nodeThresholdSpectralComponent node = 0 := by
  cases node with
  | binary id name gates default combination =>
      exact
        thresholdGateSpectralComponent_sum_eq_zero_of_all_adjudicated
          gates
          (by simpa [nodeThresholdAdjudicated] using hnode)
  | proportional id name rule priorityClasses =>
      rfl
  | threshold id name threshold field =>
      rfl

/-- The node-level repair removes terminal-threshold spectral mass. -/
theorem nodeThresholdSpectralComponent_adjudicateThresholdNode
    (node : AuditGovernanceNode) :
    nodeThresholdSpectralComponent (adjudicateThresholdNode node) = 0 := by
  exact
    nodeThresholdSpectralComponent_eq_zero_of_nodeThresholdAdjudicated
      (adjudicateThresholdNode node)
      (adjudicateThresholdNode_threshold_adjudicated node)

/-- A list of adjudicated nodes has zero threshold signal at every index. -/
theorem auditNodesThresholdSignalAt_eq_zero_of_all_adjudicated
    (nodes : List AuditGovernanceNode)
    (hnodes : nodes.all nodeThresholdAdjudicated = true)
    (index : Nat) :
    auditNodesThresholdSignalAt nodes index = 0 := by
  induction nodes generalizing index with
  | nil =>
      cases index <;> simp [auditNodesThresholdSignalAt]
  | cons node rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hnodes
      rcases hnodes with ⟨hnode, hrest⟩
      cases index with
      | zero =>
          simp [auditNodesThresholdSignalAt,
            nodeThresholdSpectralComponent_eq_zero_of_nodeThresholdAdjudicated
              node hnode]
      | succ index =>
          simpa [auditNodesThresholdSignalAt] using ih hrest index

/-- Adjudicating the graph removes the audit-derived threshold signal. -/
theorem auditGraphThresholdSignal_adjudicateThresholdGraph_zero
    {n : Nat} [NeZero n]
    (graph : AuditGovernanceGraph)
    (i : Fin n) :
    auditGraphThresholdSignal
      (adjudicateThresholdGraph graph) i = 0 := by
  exact
    auditNodesThresholdSignalAt_eq_zero_of_all_adjudicated
      (adjudicateThresholdGraph graph).nodes
      (by
        simpa [graph_threshold_adjudicated] using
          graph_threshold_adjudicated_adjudicateThresholdGraph graph)
      i.val

/-- The repaired audit-derived threshold signal has zero spectral vulnerability
under any supplied spectral topology. -/
theorem adjudicateThresholdGraph_cv_zero
    {n : Nat} [NeZero n]
    (spectralGraph : GovGraph ℚ n)
    (graph : AuditGovernanceGraph) :
    spectralGraph.cv
      (auditGraphThresholdSignal
        (adjudicateThresholdGraph graph)) = 0 := by
  simp [GovGraph.cv, GovGraph.gov, GovGraph.govRemoved,
    auditGraphThresholdSignal_adjudicateThresholdGraph_zero graph]

/-- Any graph already satisfying `graph_threshold_adjudicated` has zero
audit-derived threshold signal under the scoped spectral topology. -/
theorem auditGraphThresholdSignal_cv_zero_of_graph_threshold_adjudicated
    {n : Nat} [NeZero n]
    (spectralGraph : GovGraph ℚ n)
    (graph : AuditGovernanceGraph)
    (hgraph : graph_threshold_adjudicated graph = true) :
    spectralGraph.cv (auditGraphThresholdSignal graph) = 0 := by
  have hzero :
      ∀ i : Fin n, auditGraphThresholdSignal graph i = 0 := by
    intro i
    exact
      auditNodesThresholdSignalAt_eq_zero_of_all_adjudicated
        graph.nodes
        (by simpa [graph_threshold_adjudicated] using hgraph)
        i.val
  simp [GovGraph.cv, GovGraph.gov, GovGraph.govRemoved, hzero]

end Legitimacy
