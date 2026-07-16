/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.MultiAgentEdgeLocalComposition

/-!
# Legitimacy.MultiAgentJointCapabilityComposition.Core

Joint-capability instance multi-agent compositional safety.

This module extends the edge-local T1 substrate with the missing Spera 2026
hypergraph channel. A composed run can now violate a forbidden-property set in
exactly three structural ways:

1. an agent-local kernel trajectory violates a forbidden property;
2. a declared cross-agent edge realizes a forbidden boundary failure;
3. a marked joint-capability instance across multiple agents reaches a
   forbidden conjunctive dependency that no participating agent reaches alone.

The headline theorem below proves safety for systems that already mark their
joint-capability instances in this finite substrate. T1.2 makes the third
channel behavioral rather than cosmetic: a joint capability carries one action
from each participant's own kernel action alphabet, and reachability is linked
to `GovernanceForbiddenProperty.jointTrajectoryPredicate`.

The earlier edge-local theorem remains available in
`MultiAgentEdgeLocalComposition`; it is the two-channel theorem obtained by
ignoring the joint-capability disjunct.

The original Unit-action Spera fixture is kept as a legacy tautology
regression. The paper-facing content-link fixture below is the Bool-action
fixture, where participant actions are genuinely distinguishable.
-/

set_option autoImplicit false

namespace Legitimacy

open Safety

/-! ## Joint-capability substrate -/

/-- A declared edge directly realizes a joint capability only when the edge's
source and target are the exact two participating agents and the edge carries
single-action tool access whose payload cannot distinguish any participant
action. This is intentionally stricter than
`EdgeTracksJointCapability`: realization means "the joint capability is a
single ordinary declared edge", while tracking means "a declared edge names
and governs the conjunction." The exact-cardinality check prevents a two-endpoint
edge from collapsing a 3+ participant hyperedge; the action-collapse check
prevents a level-1 tool edge from erasing nontrivial kernel-typed action
pairs. -/
def EdgeRealizesJointCapability
    (edge : CrossAgentEdge)
    (participating_agents : List KernelGovernedAgent)
    (agent_action :
      ∀ agent, agent ∈ participating_agents →
        agent.kernel.actionSpace.Action) : Prop :=
  participating_agents.length = 2 ∧
    ∃ source ∈ participating_agents,
    ∃ target ∈ participating_agents,
      source.id = edge.sourceAgent ∧
        target.id = edge.targetAgent ∧
        edge.kind = CrossAgentEdgeKind.toolAccess ∧
        edge.sourceAuthorityLevel = 1 ∧
        ∀ agent (hmem : agent ∈ participating_agents)
          (other : agent.kernel.actionSpace.Action),
          agent_action agent hmem = other

/-- A joint capability is a finite multi-agent action conjunction that crosses
agents without collapsing to a single declared cross-agent edge. Participants
are a set by stable agent id: the list order is only presentation, and repeated
mentions of the same agent id do not increase the capability arity. The action
payload is kernel-typed: every participating agent contributes one action from
that agent's own `kernel.actionSpace.Action`. There is no disconnected
substrate token. -/
structure JointCapability (sys : MultiAgentSystem) where
  /-- Participating agents in the conjunctive capability. -/
  participating_agents : List KernelGovernedAgent
  /-- Participating agent ids are distinct; duplicate listings do not create
  extra joint-capability arity. -/
  participating_agent_ids_nodup :
    (participating_agents.map (fun agent => agent.id)).Nodup
  /-- Every participant is a declared agent of the system. -/
  participation_proof :
    ∀ agent, agent ∈ participating_agents → agent ∈ sys.agents
  /-- One kernel-typed action per participating agent. -/
  agent_action :
    ∀ agent, agent ∈ participating_agents →
      agent.kernel.actionSpace.Action
  /-- Joint capabilities are genuinely multi-agent. -/
  cardinality_two_or_more : 2 ≤ participating_agents.length
  /-- The joint capability is not itself a single declared cross-agent edge. -/
  not_single_declared_edge :
    ∀ edge, edge ∈ sys.composition_edges →
      ¬ EdgeRealizesJointCapability edge participating_agents agent_action

/-- The action contributed by a participating agent. This small wrapper keeps
the dependent action payload explicit in statements and drop tests. -/
def JointParticipantAction
    {sys : MultiAgentSystem}
    (jc : JointCapability sys)
    (agent : KernelGovernedAgent)
    (hmem : agent ∈ jc.participating_agents) :
    agent.kernel.actionSpace.Action :=
  jc.agent_action agent hmem

/-- A declared edge tracks a joint capability when it names the participating
source and target and carries enough finite budget to identify the whole
conjunction. Tracking is weaker than direct realization: a tool-access edge
can govern a hidden hyperedge without the hyperedge being identical to that
edge.

The `toolAccess` requirement is an encoding choice for the current finite
instance substrate: among `CrossAgentEdgeKind` values, tool access is the one
whose natural payload is an externally shared capability surface rather than
delegation, memory mutation, or reviewer escalation. The equality
`sourceAuthorityLevel = jc.participating_agents.length` is likewise a compact
cardinality witness that the edge budget names the whole participant
conjunction.
These fields are load-bearing for the fixture-level tracking predicate but
are not a claim that future behavioral substrates must encode tracking with
exactly this pair of fields. -/
def EdgeTracksJointCapability
    {sys : MultiAgentSystem}
    (edge : CrossAgentEdge)
    (jc : JointCapability sys) : Prop :=
  ∃ source ∈ jc.participating_agents,
    ∃ target ∈ jc.participating_agents,
      source.id = edge.sourceAgent ∧
        target.id = edge.targetAgent ∧
        edge.kind = CrossAgentEdgeKind.toolAccess ∧
        edge.sourceAuthorityLevel = jc.participating_agents.length

/-- A joint capability reaches a forbidden property exactly when a forbidden
property's joint predicate fires on the kernel-typed action bundle and no
single participant's solo trajectory fires the local predicate. This is the
T1.2 content link: the hidden hyperedge is behavioral content over typed
kernel actions, not a detached structural token. -/
def JointCapabilityReaches
    {sys : MultiAgentSystem}
    (jc : JointCapability sys)
    (per_agent_traj :
      ∀ agent, agent ∈ jc.participating_agents → AgentKernelTrajectory agent)
    (forbidden : List GovernanceForbiddenProperty) : Prop :=
  ∃ property ∈ forbidden,
    property.jointTrajectoryPredicate sys jc.participating_agents
      jc.participation_proof per_agent_traj jc.agent_action ∧
    ∀ agent (hmem : agent ∈ jc.participating_agents),
      ¬ property.trajectoryPredicate agent (per_agent_traj agent hmem)

/-- A composed trajectory exhibits a joint-capability violation when it
instantiates a joint capability whose conjunctive action reaches a listed
forbidden property. -/
def JointCapabilityViolatesForbidden
    {sys : MultiAgentSystem}
    (traj : ComposedTrajectory sys)
    (forbidden : List GovernanceForbiddenProperty) : Prop :=
  ∃ jc : JointCapability sys,
    JointCapabilityReaches jc
      (fun agent hmem => traj.perAgent agent (jc.participation_proof agent hmem))
      forbidden

/-- Agent-local channel of the three-channel composed violation predicate. -/
def PerAgentTrajectoryViolatesForbidden
    {sys : MultiAgentSystem}
    (traj : ComposedTrajectory sys)
    (forbidden : List GovernanceForbiddenProperty) : Prop :=
  ∃ agent : KernelGovernedAgent,
    ∃ hmem : agent ∈ sys.agents,
      TrajectoryViolatesForbidden (traj.perAgent agent hmem) forbidden

/-- Declared-edge boundary channel of the three-channel composed violation
predicate. -/
def EdgeBoundaryViolatesForbidden
    {sys : MultiAgentSystem}
  (_traj : ComposedTrajectory sys)
  (forbidden : List GovernanceForbiddenProperty) : Prop :=
  ∃ edge : CrossAgentEdge,
    ∃ _hedge : edge ∈ sys.composition_edges,
      EdgeViolatesForbidden sys edge forbidden

/-- Full Spera-frontier composed violation predicate: local, declared-edge,
or hidden joint-capability hyperedge. -/
def ComposedTrajectoryViolatesForbidden
    {sys : MultiAgentSystem}
    (traj : ComposedTrajectory sys)
    (forbidden : List GovernanceForbiddenProperty) : Prop :=
  PerAgentTrajectoryViolatesForbidden traj forbidden ∨
    EdgeBoundaryViolatesForbidden traj forbidden ∨
      JointCapabilityViolatesForbidden traj forbidden

/-- Joint-capability compatibility: every cross-agent conjunction is tracked
by a declared edge that names the conjunction. Hidden hyperedges that bypass
declared-edge governance are incompatible.

This is not definitional pass-through to the headline theorem: it does not
mention forbidden lists or composed trajectories, and the Spera fixtures below
prove that it can fail even when the five older edge-local predicates hold. -/
def JointCapabilityCompatibility (sys : MultiAgentSystem) : Prop :=
  ∀ jc : JointCapability sys,
    (∃ edge, ∃ _hedge : edge ∈ sys.composition_edges,
      EdgeTracksJointCapability edge jc)

/-! ## Content-linked preservation theorem -/

/-- Joint-capability compatibility plus the content-link discharge hypothesis
rules out the joint-capability failure channel. The proof is deliberately not
a field projection from the headline theorem: it opens the existential hidden
hyperedge, builds the per-agent trajectory bundle used by
`JointCapabilityReaches`, and applies the behavioral content-link hypothesis. -/
theorem joint_capability_forbidden_excluded
    {sys : MultiAgentSystem}
    (forbidden : List GovernanceForbiddenProperty)
    (h_joint : JointCapabilityCompatibility sys)
    (h_joint_per_agent :
      ∀ jc : JointCapability sys,
        (∃ edge, ∃ _hedge : edge ∈ sys.composition_edges,
          EdgeTracksJointCapability edge jc) →
        ∀ per_agent_traj :
          ∀ agent, agent ∈ jc.participating_agents →
            AgentKernelTrajectory agent,
          ¬ JointCapabilityReaches jc per_agent_traj forbidden)
    (traj : ComposedTrajectory sys) :
    ¬ JointCapabilityViolatesForbidden traj forbidden := by
  intro hviolates
  rcases hviolates with
    ⟨jc, property, hproperty_mem, hjoint_fires, hsolo_quiet⟩
  let per_agent_traj :
      ∀ agent, agent ∈ jc.participating_agents →
        AgentKernelTrajectory agent :=
    fun agent hmem =>
      traj.perAgent agent (jc.participation_proof agent hmem)
  rcases h_joint jc with ⟨edge, hedge, htracks⟩
  have htracked :
      ∃ edge, ∃ _hedge : edge ∈ sys.composition_edges,
        EdgeTracksJointCapability edge jc :=
    ⟨edge, hedge, htracks⟩
  have hreach : JointCapabilityReaches jc per_agent_traj forbidden :=
    ⟨property, hproperty_mem, hjoint_fires, hsolo_quiet⟩
  exact h_joint_per_agent jc htracked per_agent_traj hreach

/-- Content-linked joint-capability composition safety: under semantic endpoint
kernels, all five edge-local compatibility predicates, joint-capability
compatibility, per-agent forbidden-property preservation, and the behavioral
joint content-link discharge, multi-agent kernel composition preserves
forbidden-property exclusion across the three Spera channels.

The proof case-splits over agent-local, declared-edge, and hidden
joint-capability violations. The joint branch discharges through
`JointCapabilityReaches`, whose definition requires the joint predicate to
fire on kernel-typed actions while every solo predicate stays false. -/
theorem multi_agent_kernel_joint_capability_composition_safe
    (sys : MultiAgentSystem)
    (forbidden : List GovernanceForbiddenProperty)
    (h_kernel :
      ∀ agent ∈ sys.agents, IsSemanticLegitimacyKernel agent.kernel)
    (h_compat_5 : AllMultiAgentCompatibilityConditions sys)
    (h_joint : JointCapabilityCompatibility sys)
    (h_per_agent :
      ∀ agent (_hmem : agent ∈ sys.agents),
        ∀ traj : AgentKernelTrajectory agent,
          ¬ TrajectoryViolatesForbidden traj forbidden)
    (h_joint_per_agent :
      ∀ jc : JointCapability sys,
        (∃ edge, ∃ _hedge : edge ∈ sys.composition_edges,
          EdgeTracksJointCapability edge jc) →
        ∀ per_agent_traj :
          ∀ agent, agent ∈ jc.participating_agents →
            AgentKernelTrajectory agent,
          ¬ JointCapabilityReaches jc per_agent_traj forbidden) :
    ∀ traj : ComposedTrajectory sys,
      ¬ ComposedTrajectoryViolatesForbidden traj forbidden := by
  intro traj hviolates
  rcases hviolates with hlocal | hboundary_or_joint
  · rcases hlocal with ⟨agent, hmem, hagentViolation⟩
    exact h_per_agent agent hmem (traj.perAgent agent hmem) hagentViolation
  · rcases hboundary_or_joint with hboundary | hjoint
    · rcases hboundary with ⟨edge, hedge, hedgeViolation⟩
      exact
        multi_agent_cross_edge_forbidden_excluded forbidden h_kernel
          h_compat_5 hedge hedgeViolation
    · exact
        joint_capability_forbidden_excluded forbidden h_joint
          h_joint_per_agent traj hjoint

/-- Historical T1.1 theorem name retained with the strengthened T1.2 signature.
The content-link discharge is now a load-bearing hypothesis, so this name is no
longer an old-arity wrapper. -/
theorem multi_agent_kernel_joint_capability_instance_safe
    (sys : MultiAgentSystem)
    (forbidden : List GovernanceForbiddenProperty)
    (h_kernel :
      ∀ agent ∈ sys.agents, IsSemanticLegitimacyKernel agent.kernel)
    (h_compat_5 : AllMultiAgentCompatibilityConditions sys)
    (h_joint : JointCapabilityCompatibility sys)
    (h_per_agent :
      ∀ agent (_hmem : agent ∈ sys.agents),
        ∀ traj : AgentKernelTrajectory agent,
          ¬ TrajectoryViolatesForbidden traj forbidden)
    (h_joint_per_agent :
      ∀ jc : JointCapability sys,
        (∃ edge, ∃ _hedge : edge ∈ sys.composition_edges,
          EdgeTracksJointCapability edge jc) →
        ∀ per_agent_traj :
          ∀ agent, agent ∈ jc.participating_agents →
            AgentKernelTrajectory agent,
          ¬ JointCapabilityReaches jc per_agent_traj forbidden) :
    ∀ traj : ComposedTrajectory sys,
      ¬ ComposedTrajectoryViolatesForbidden traj forbidden :=
  multi_agent_kernel_joint_capability_composition_safe sys forbidden h_kernel
    h_compat_5 h_joint h_per_agent h_joint_per_agent

#print axioms multi_agent_kernel_joint_capability_composition_safe


end Legitimacy
