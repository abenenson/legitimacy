/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.CompositionalSafety
import Legitimacy.Bridges.ELKCorrespondence
import Legitimacy.Safety.KernelSafety

/-!
# Legitimacy.MultiAgentComposition.Core

Core substrate, compatibility witnesses, and anchored-representative realization
for cross-agent composition of semantic legitimacy kernels.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A kernel-governed agent together with the authority surface and declared
sacrifice index it exposes to a multi-agent composition audit. -/
structure KernelGovernedAgent where
  /-- Stable finite identifier used by cross-agent edges. -/
  id : Nat
  /-- Cardinality of the agent's causal substrate. -/
  n : Nat
  /-- The governed system on which this agent's kernel datum lives. -/
  sys : GovernedSystem n
  /-- The agent-local legitimacy kernel datum. -/
  kernel : LegitimacyKernelData sys
  /-- Reported authority surface exposed by this agent at composition time. -/
  authority : Safety.AuthorityGraph
  /-- Properties this agent has explicitly declared as sacrificed. -/
  sacrificeIndex : List GovernanceProperty
  /-- Rank used by escalation edges; lower ranks cannot silently dominate
  higher-rank reviewer surfaces. -/
  escalationRank : Nat

/-- Four concrete encodings by which two kernel-governed agents can share a
governance surface. -/
inductive CrossAgentEdgeKind where
  | delegation
  | toolAccess
  | sharedMemory
  | escalation
  deriving Repr, DecidableEq

/-- Boundary bridge status for one cross-agent edge. `detected` uses the ELK
discrepancy vocabulary that already corresponds to hidden-authority
certificates in `Bridges.ELKCorrespondence`; `undeclared` is the bad case. -/
inductive CrossAgentBridgeStatus where
  | clean
  | detected (disc : Safety.ELKDiscrepancy)
  | undeclared
  deriving Repr, DecidableEq

/-- One cross-agent composition edge. The fields are intentionally finite and
edge-local: they expose the exact surface on which the five compatibility
conditions are checked, rather than collapsing composition to per-agent kernel
soundness. -/
structure CrossAgentEdge where
  /-- Agent id at the acting side of the edge. -/
  sourceAgent : Nat
  /-- Agent id at the receiving or affected side of the edge. -/
  targetAgent : Nat
  /-- Composition encoding: delegation, shared tool, shared memory, or
  escalation. -/
  kind : CrossAgentEdgeKind
  /-- Authority level consumed by the source side. -/
  sourceAuthorityLevel : Nat
  /-- Authority ceiling accepted by the target side. -/
  targetAuthorityCeiling : Nat
  /-- Whether the edge writes into the target's kernel-relevant state. -/
  modifiesTargetKernel : Bool
  /-- Whether any such write was explicitly declared as interference. -/
  interferenceDeclared : Bool
  /-- Strengthening budget presented to an escalation reviewer. -/
  escalationStrengthening : Nat
  /-- Verdict floor before escalation. -/
  escalationVerdictFloor : Nat
  /-- Verdict ceiling after escalation. -/
  escalationVerdictCeiling : Nat
  /-- Sacrifices this edge attributes to the source agent. -/
  sourceSacrifices : List GovernanceProperty
  /-- Sacrifices this edge attributes to the target agent. -/
  targetSacrifices : List GovernanceProperty
  /-- Whether the two attributions contradict each other on this edge. -/
  contradictorySacrifice : Bool
  /-- ELK/hidden-authority bridge status at this agent boundary. -/
  bridgeStatus : CrossAgentBridgeStatus
  deriving Repr, DecidableEq

/-- A finite collection of kernel-governed agents whose governance surfaces
may interact via delegation, tool access, shared memory, or cross-agent
escalation. The `two_or_more_agents` field records that this is a genuine
multi-agent system, and `composition_edges` is load-bearing in every
compatibility theorem below. -/
structure MultiAgentSystem where
  agents : List KernelGovernedAgent
  two_or_more_agents : 2 ≤ agents.length
  composition_edges : List CrossAgentEdge

namespace MultiAgentSystem

/-- Agent identifiers exposed by the system. -/
def agentIds (sys : MultiAgentSystem) : List Nat :=
  sys.agents.map (fun agent => agent.id)

/-- Lookup the declared sacrifice index for an agent id. Missing ids expose an
empty index, so edge endpoint membership remains a separate compatibility
obligation rather than being hidden in lookup failure. -/
def sacrificeIndexFor (sys : MultiAgentSystem) (agentId : Nat) :
    List GovernanceProperty :=
  match sys.agents.find? (fun agent => agent.id == agentId) with
  | some agent => agent.sacrificeIndex
  | none => []

end MultiAgentSystem

/-- Endpoint-declaration check for one cross-agent edge. -/
def CrossAgentEdge.endpointsDeclared
    (sys : MultiAgentSystem) (edge : CrossAgentEdge) : Bool :=
  sys.agentIds.contains edge.sourceAgent &&
    sys.agentIds.contains edge.targetAgent

/-- Authority-lattice check for one cross-agent edge: the edge endpoints must
be declared agents, and the source-side authority consumed by the edge must fit
under the target-side authority ceiling. -/
def CrossAgentEdge.authorityLatticeCompatible
    (sys : MultiAgentSystem) (edge : CrossAgentEdge) : Bool :=
  edge.endpointsDeclared sys &&
    decide (edge.sourceAuthorityLevel ≤ edge.targetAuthorityCeiling)

/-- Structural endpoint witness for one cross-agent edge. Endpoint lookup is
kept as data so downstream compatibility proofs consume the agent list rather
than trusting edge-local numeric ids. -/
structure CrossAgentEndpointWitness
    (sys : MultiAgentSystem) (edge : CrossAgentEdge) where
  source : KernelGovernedAgent
  target : KernelGovernedAgent
  source_mem : source ∈ sys.agents
  target_mem : target ∈ sys.agents
  source_id : source.id = edge.sourceAgent
  target_id : target.id = edge.targetAgent

/-- Order-theoretic authority witness for one edge. The edge's numeric levels
are only projections into an explicit preorder carrier; the load-bearing fact
is that the source projection is below the target projection in that order. -/
structure CrossAgentAuthorityLatticeWitness
    (sys : MultiAgentSystem) (edge : CrossAgentEdge) where
  endpoints : CrossAgentEndpointWitness sys edge
  carrier : Type
  le : carrier → carrier → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  sourceAuthority : carrier
  targetAuthority : carrier
  projectLevel : carrier → Nat
  project_monotone :
    ∀ {x y}, le x y → projectLevel x ≤ projectLevel y
  sourceLevel_projects :
    projectLevel sourceAuthority = edge.sourceAuthorityLevel
  targetCeiling_projects :
    projectLevel targetAuthority = edge.targetAuthorityCeiling
  authority_monotone : le sourceAuthority targetAuthority

/-- Authority-lattice compatibility: every declared cross-agent edge respects
the receiving agent's authority order. This is not a bare edge Boolean:
callers must provide a preorder carrier and an order-preserving projection for
each cross-agent boundary. -/
structure AuthorityLatticeCompatible (sys : MultiAgentSystem) : Prop where
  nonempty_composition : sys.composition_edges ≠ []
  witnessed_edges :
    ∀ edge, edge ∈ sys.composition_edges →
      Nonempty (CrossAgentAuthorityLatticeWitness sys edge)

/-- Noninterference check for one edge: an edge either does not write into the
target's kernel-relevant state, or the write is explicitly declared. -/
def CrossAgentEdge.noninterferenceOrDeclared
    (edge : CrossAgentEdge) : Bool :=
  !edge.modifiesTargetKernel || edge.interferenceDeclared

/-- Kernel-level noninterference witness for one edge. The target kernel is
protected by an existing `KernelStep` preservation theorem; declared
interference is still allowed, but it must be named explicitly on the edge. -/
structure CrossAgentNoninterferenceWitness
    (sys : MultiAgentSystem) (edge : CrossAgentEdge) where
  endpoints : CrossAgentEndpointWitness sys edge
  source_invariant : Safety.KernelInvariant endpoints.source.kernel
  target_invariant : Safety.KernelInvariant endpoints.target.kernel
  target_preservation_step :
    Safety.KernelStep endpoints.target.kernel endpoints.target.kernel
  target_preserved :
    Safety.KernelInvariant endpoints.target.kernel
  target_preserved_by_step :
    target_preserved =
      Safety.kernelStep_preserves_invariant target_preservation_step
        target_invariant
  separated_or_declared :
    edge.modifiesTargetKernel = false ∨ edge.interferenceDeclared = true

/-- Noninterference (or declared interference): every composition edge is
either read-only with respect to another agent's kernel state, or carries an
explicit declaration that can be audited as a sacrifice surface. The read-only
case is backed by a kernel-preservation step on the target kernel. -/
structure NoninterferenceOrDeclared (sys : MultiAgentSystem) : Prop where
  nonempty_composition : sys.composition_edges ≠ []
  witnessed_edges :
    ∀ edge, edge ∈ sys.composition_edges →
      Nonempty (CrossAgentNoninterferenceWitness sys edge)

/-- Monotonicity check for one escalation edge. Non-escalation encodings are
irrelevant to escalation monotonicity; escalation edges must not turn a
strengthened source-side review into a lower target-side verdict ceiling. -/
def CrossAgentEdge.monotoneEscalationCompatible
    (edge : CrossAgentEdge) : Bool :=
  match edge.kind with
  | CrossAgentEdgeKind.escalation =>
      decide (edge.escalationVerdictFloor + edge.escalationStrengthening ≤
        edge.escalationVerdictCeiling)
  | _ => true

/-- Escalation monotonicity witness for one edge. Escalation edges consume the
receiving agent's existing `GraphMonotonicity` diagnostic and a concrete
source-strengthening/target-verdict inequality; non-escalation encodings are
handled by the same witness with a vacuous edge-shape implication. -/
structure CrossAgentEscalationMonotonicityWitness
    (sys : MultiAgentSystem) (edge : CrossAgentEdge) where
  endpoints : CrossAgentEndpointWitness sys edge
  target_graph_monotone : GraphMonotonicity endpoints.target.sys.graph
  escalation_shape :
    edge.kind = CrossAgentEdgeKind.escalation →
      edge.escalationVerdictFloor + edge.escalationStrengthening ≤
        edge.escalationVerdictCeiling

/-- Monotone escalation composition: every escalation chain represented by a
cross-agent edge preserves rule-level monotonicity. Strengthening a claim at
the source cannot weaken the receiving reviewer verdict, and the target graph
is required to satisfy the existing graph monotonicity diagnostic. -/
structure MonotoneEscalationComposition
    (sys : MultiAgentSystem) : Prop where
  nonempty_composition : sys.composition_edges ≠ []
  witnessed_edges :
    ∀ edge, edge ∈ sys.composition_edges →
      Nonempty (CrossAgentEscalationMonotonicityWitness sys edge)

/-- Computable list-inclusion check used for finite sacrifice indices. -/
def listSubsetByContains {α : Type} [BEq α]
    (xs ys : List α) : Bool :=
  xs.all (fun x => ys.contains x)

/-- Sacrifice-index check for one edge: edge-local attributions must be
subsets of the corresponding agents' declared indices, and the edge must not
mark those declarations as contradictory. -/
def CrossAgentEdge.sacrificeIndicesCompatible
    (sys : MultiAgentSystem) (edge : CrossAgentEdge) : Bool :=
  !edge.contradictorySacrifice &&
    listSubsetByContains edge.sourceSacrifices
      (sys.sacrificeIndexFor edge.sourceAgent) &&
    listSubsetByContains edge.targetSacrifices
      (sys.sacrificeIndexFor edge.targetAgent)

/-- Protocol-level sacrifice witness for one edge. Edge-attributed sacrifices
must be present in the corresponding endpoint's declared index, and each
agent's declared index must be interpretable by the existing protocol
predicates as either a non-sacrificed-hold boundary or a justified sacrificed
property. -/
structure CrossAgentSacrificeIndexWitness
    (sys : MultiAgentSystem) (edge : CrossAgentEdge) where
  endpoints : CrossAgentEndpointWitness sys edge
  no_contradiction : edge.contradictorySacrifice = false
  source_declared :
    ∀ property, property ∈ edge.sourceSacrifices →
      property ∈ endpoints.source.sacrificeIndex
  target_declared :
    ∀ property, property ∈ edge.targetSacrifices →
      property ∈ endpoints.target.sacrificeIndex
  source_protocol_boundary :
    NonSacrificedHold endpoints.source.sys.graph
        endpoints.source.sacrificeIndex ∨
      SacrificesJustified endpoints.source.sys.graph
        endpoints.source.sacrificeIndex
  target_protocol_boundary :
    NonSacrificedHold endpoints.target.sys.graph
        endpoints.target.sacrificeIndex ∨
      SacrificesJustified endpoints.target.sys.graph
        endpoints.target.sacrificeIndex

/-- Compatible sacrifice indices: cross-agent declarations are the per-edge
faces of the agents' own declared sacrifice indices, with no contradictory
attribution on an inter-agent boundary, interpreted through the existing
protocol sacrifice predicates. -/
structure CompatibleSacrificeIndices
    (sys : MultiAgentSystem) : Prop where
  nonempty_composition : sys.composition_edges ≠ []
  witnessed_edges :
    ∀ edge, edge ∈ sys.composition_edges →
      Nonempty (CrossAgentSacrificeIndexWitness sys edge)

/-- Bridge-preservation check for one edge. Clean edges and detected
ELK-discrepancy edges are admissible; an undeclared boundary means the
composition introduced hidden authority outside the bridge vocabulary. -/
def CrossAgentEdge.bridgePreserving
    (edge : CrossAgentEdge) : Bool :=
  match edge.bridgeStatus with
  | CrossAgentBridgeStatus.clean => true
  | CrossAgentBridgeStatus.detected _ => true
  | CrossAgentBridgeStatus.undeclared => false

/-- Structural bridge witness for one boundary status. Detected ELK
discrepancies are accepted only when they are matched to an existing
`HiddenAuthorityCertificate`; the discrepancy payload is not discarded. -/
def CrossAgentBridgeStatusSupported
    (status : CrossAgentBridgeStatus) : Prop :=
  match status with
  | CrossAgentBridgeStatus.clean => True
  | CrossAgentBridgeStatus.detected disc =>
      ∃ (artifact : Safety.RuleLayerKernelArtifact)
        (observation : Safety.GovernanceKernelizationObservation artifact)
        (cert : Safety.HiddenAuthorityCertificate observation),
        Safety.ELKDiscrepancyMatchesCert disc cert
  | CrossAgentBridgeStatus.undeclared => False

/-- Bridge-preservation witness for one cross-agent edge. -/
structure CrossAgentBridgeWitness
    (sys : MultiAgentSystem) (edge : CrossAgentEdge) where
  endpoints : CrossAgentEndpointWitness sys edge
  bridge_supported : CrossAgentBridgeStatusSupported edge.bridgeStatus

/-- Bridge preservation: ELK-style hidden-authority discrepancies at
cross-agent boundaries are either absent or detected in the existing bridge
vocabulary by an actual hidden-authority certificate, so no edge adds an
undeclared authority pathway. -/
structure CrossAgentBridgePreservation
    (sys : MultiAgentSystem) : Prop where
  nonempty_composition : sys.composition_edges ≠ []
  witnessed_edges :
    ∀ edge, edge ∈ sys.composition_edges →
      Nonempty (CrossAgentBridgeWitness sys edge)

/-- A bundled representative kernel anchored in one declared agent of the
multi-agent system. This is not a new composed kernel object; the underlying
`LegitimacyKernel` remains dependent on the anchor agent's governed system, so
the bundle records that system index explicitly. -/
structure AnchoredRepresentativeKernel where
  /-- Agent id anchoring this representative in the finite system. -/
  anchorAgent : Nat
  n : Nat
  sys : GovernedSystem n
  kernel : LegitimacyKernel sys

/-- The five compatibility conditions as one theorem-side abbreviation. -/
def AllMultiAgentCompatibilityConditions
    (sys : MultiAgentSystem) : Prop :=
  AuthorityLatticeCompatible sys ∧
    NoninterferenceOrDeclared sys ∧
    MonotoneEscalationComposition sys ∧
    CompatibleSacrificeIndices sys ∧
    CrossAgentBridgePreservation sys

/-- One cross-agent edge realized against the existing substrate: authority is
order-theoretic, noninterference uses kernel-step preservation, escalation uses
graph monotonicity, sacrifice declarations use protocol sacrifice predicates,
and boundary bridges consume hidden-authority/ELK certificate vocabulary.

The realization payload is intentionally scoped to the five compatibility
witnesses listed above. It records edge-local substrate compatibility rather
than a derivation of those witnesses from a lower-level composed operational
semantics.
-/
structure CrossAgentEdgeSubstrateRealization
    (sys : MultiAgentSystem) (edge : CrossAgentEdge) where
  authority : CrossAgentAuthorityLatticeWitness sys edge
  noninterference : CrossAgentNoninterferenceWitness sys edge
  monotone_escalation : CrossAgentEscalationMonotonicityWitness sys edge
  sacrifice_indices : CrossAgentSacrificeIndexWitness sys edge
  bridge_preservation : CrossAgentBridgeWitness sys edge

/-- Semantic kernel soundness gives the graph-level compositional-safety
projection from `Legitimacy.Kernel.CompositionalSafety`: denied decisions stay
denied under appended governance stages. -/
lemma compositionalSafety_of_semantic_kernel
    {n : Nat} {sys : GovernedSystem n}
    {D : LegitimacyKernelData sys}
    (_hsemantic : IsSemanticLegitimacyKernel D) :
    CompositionalSafety sys.graph := by
  intro H claims k hdeny
  exact graphDecide_append_of_deny sys.graph H claims k hdeny

/-- Causal-boundary translation from a semantic kernel to the existing
boundary-relative compositional-safety axiom. -/
lemma causalSoundness_of_semantic_kernel
    {n : Nat} {sys : GovernedSystem n}
    {D : LegitimacyKernelData sys}
    (hsemantic : IsSemanticLegitimacyKernel D) :
    CausalSoundness sys.dag sys.governed :=
  by
    simpa [LegitimacyKernelData.KernelCausalSoundness] using
      hsemantic.runtimeKernel.compositionalSafety

/-- Realization relation for an anchored representative kernel over a
multi-agent system. The representative must be selected from the agent list,
every cross-agent edge must realize the substrate obligations, and each
agent's semantic kernel is translated back to the existing graph-level and
causal compositional-safety substrate.

The edge realization field currently quantifies the compatibility-substrate
witness bundle above. A stronger behavioral theorem would instead quantify
lower-level denial-preservation and causal boundary behavior, then derive the
five compatibility predicates as consequences rather than projections. -/
structure AnchoredRepresentativeRealizesMultiAgentSystem
    (representativeKernel : AnchoredRepresentativeKernel)
    (sys : MultiAgentSystem) : Prop where
  anchor_declared :
    ∃ agent ∈ sys.agents, agent.id = representativeKernel.anchorAgent
  composition_nonempty : sys.composition_edges ≠ []
  edge_realization :
    ∀ edge, edge ∈ sys.composition_edges →
      Nonempty (CrossAgentEdgeSubstrateRealization sys edge)
  agent_graph_compositional :
    ∀ agent, agent ∈ sys.agents → CompositionalSafety agent.sys.graph
  agent_causal_sound :
    ∀ agent, agent ∈ sys.agents →
      CausalSoundness agent.sys.dag agent.sys.governed

/-- Substrate realization derives authority-lattice compatibility. -/
lemma AnchoredRepresentativeRealizesMultiAgentSystem.authority_compatible
    {representativeKernel : AnchoredRepresentativeKernel}
    {sys : MultiAgentSystem}
    (hrealizes : AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel sys)
    (hnonempty : sys.composition_edges ≠ []) :
    AuthorityLatticeCompatible sys where
  nonempty_composition := hnonempty
  witnessed_edges := fun edge hedge =>
    let ⟨hsubstrate⟩ := hrealizes.edge_realization edge hedge
    ⟨hsubstrate.authority⟩

/-- Substrate realization derives noninterference compatibility. -/
lemma AnchoredRepresentativeRealizesMultiAgentSystem.noninterference_compatible
    {representativeKernel : AnchoredRepresentativeKernel}
    {sys : MultiAgentSystem}
    (hrealizes : AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel sys)
    (hnonempty : sys.composition_edges ≠ []) :
    NoninterferenceOrDeclared sys where
  nonempty_composition := hnonempty
  witnessed_edges := fun edge hedge =>
    let ⟨hsubstrate⟩ := hrealizes.edge_realization edge hedge
    ⟨hsubstrate.noninterference⟩

/-- Substrate realization derives monotone escalation compatibility. -/
lemma AnchoredRepresentativeRealizesMultiAgentSystem.monotone_compatible
    {representativeKernel : AnchoredRepresentativeKernel}
    {sys : MultiAgentSystem}
    (hrealizes : AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel sys)
    (hnonempty : sys.composition_edges ≠ []) :
    MonotoneEscalationComposition sys where
  nonempty_composition := hnonempty
  witnessed_edges := fun edge hedge =>
    let ⟨hsubstrate⟩ := hrealizes.edge_realization edge hedge
    ⟨hsubstrate.monotone_escalation⟩

/-- Substrate realization derives sacrifice-index compatibility. -/
lemma AnchoredRepresentativeRealizesMultiAgentSystem.sacrifice_compatible
    {representativeKernel : AnchoredRepresentativeKernel}
    {sys : MultiAgentSystem}
    (hrealizes : AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel sys)
    (hnonempty : sys.composition_edges ≠ []) :
    CompatibleSacrificeIndices sys where
  nonempty_composition := hnonempty
  witnessed_edges := fun edge hedge =>
    let ⟨hsubstrate⟩ := hrealizes.edge_realization edge hedge
    ⟨hsubstrate.sacrifice_indices⟩

/-- Substrate realization derives cross-agent bridge preservation. -/
lemma AnchoredRepresentativeRealizesMultiAgentSystem.bridge_compatible
    {representativeKernel : AnchoredRepresentativeKernel}
    {sys : MultiAgentSystem}
    (hrealizes : AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel sys)
    (hnonempty : sys.composition_edges ≠ []) :
    CrossAgentBridgePreservation sys where
  nonempty_composition := hnonempty
  witnessed_edges := fun edge hedge =>
    let ⟨hsubstrate⟩ := hrealizes.edge_realization edge hedge
    ⟨hsubstrate.bridge_preservation⟩

lemma AnchoredRepresentativeRealizesMultiAgentSystem.compatibility
    {representativeKernel : AnchoredRepresentativeKernel}
    {sys : MultiAgentSystem}
    (hrealizes : AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel sys)
    (hnonempty : sys.composition_edges ≠ []) :
    AllMultiAgentCompatibilityConditions sys :=
  ⟨hrealizes.authority_compatible hnonempty,
    hrealizes.noninterference_compatible hnonempty,
    hrealizes.monotone_compatible hnonempty,
    hrealizes.sacrifice_compatible hnonempty,
    hrealizes.bridge_compatible hnonempty⟩

/-- A multi-agent system realizes an anchored representative semantic
legitimacy kernel iff all five compatibility conditions hold. This theorem is
deliberately about a dependent bundle over one declared agent kernel, matching
the existing `LegitimacyKernel` substrate rather than pretending that this file
constructs a parameter-free composed kernel type. -/
theorem anchored_representative_kernel_realized_iff_all_compatible
    (sys : MultiAgentSystem) :
    (∀ agent ∈ sys.agents, IsSemanticLegitimacyKernel agent.kernel) →
      ((∃ representativeKernel : AnchoredRepresentativeKernel,
          IsSemanticLegitimacyKernel
            representativeKernel.kernel.toLegitimacyKernelData ∧
            AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel sys) ↔
        AllMultiAgentCompatibilityConditions sys) := by
  intro hsemantic_agents
  constructor
  · rintro ⟨representativeKernel, _hsemantic, hrealizes⟩
    exact hrealizes.compatibility hrealizes.composition_nonempty
  · intro hcompat
    have hagents_nonempty : sys.agents ≠ [] := by
      intro hnil
      have hbad : (2 : Nat) ≤ 0 := by
        simpa [hnil] using sys.two_or_more_agents
      omega
    obtain ⟨agent, hagent_mem⟩ :=
      List.exists_mem_of_ne_nil sys.agents hagents_nonempty
    have hsemantic_agent :
        IsSemanticLegitimacyKernel agent.kernel :=
      hsemantic_agents agent hagent_mem
    let bundledKernel : LegitimacyKernel agent.sys :=
      { toLegitimacyKernelData := agent.kernel
        isKernel := hsemantic_agent.runtimeKernel }
    refine
      ⟨AnchoredRepresentativeKernel.mk agent.id agent.n agent.sys bundledKernel,
        hsemantic_agent,
        ?_⟩
    exact
      { anchor_declared := ⟨agent, hagent_mem, rfl⟩
        composition_nonempty := hcompat.1.nonempty_composition
        edge_realization := fun edge hedge =>
          let ⟨hauthority⟩ := hcompat.1.witnessed_edges edge hedge
          let ⟨hnoninterference⟩ := hcompat.2.1.witnessed_edges edge hedge
          let ⟨hmonotone⟩ := hcompat.2.2.1.witnessed_edges edge hedge
          let ⟨hsacrifice⟩ := hcompat.2.2.2.1.witnessed_edges edge hedge
          let ⟨hbridge⟩ := hcompat.2.2.2.2.witnessed_edges edge hedge
          ⟨{ authority := hauthority
             noninterference := hnoninterference
             monotone_escalation := hmonotone
             sacrifice_indices := hsacrifice
             bridge_preservation := hbridge }⟩
        agent_graph_compositional := fun checkedAgent hchecked =>
          compositionalSafety_of_semantic_kernel
            (hsemantic_agents checkedAgent hchecked)
        agent_causal_sound := fun checkedAgent hchecked =>
          causalSoundness_of_semantic_kernel
            (hsemantic_agents checkedAgent hchecked) }

end Legitimacy
