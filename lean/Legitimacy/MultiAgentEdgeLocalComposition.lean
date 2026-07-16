/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.MultiAgentComposition

/-!
# Legitimacy.MultiAgentEdgeLocalComposition

Edge-local multi-agent compositional safety.

Spera 2026, arXiv:2603.15973 with companion arXiv:2603.15978, proves that
individually safe agents can compose into a forbidden conjunctive dependency.
This module records the edge-local theorem supported by the existing
multi-agent kernel substrate. It does not model joint-capability hyperedges:
`Legitimacy.MultiAgentJointCapabilityComposition` adds a hidden
joint-capability violation channel, sixth compatibility predicate, and T1.2
content link from kernel-typed joint actions to forbidden-property
reachability.
This module remains the two-channel decomposition for agent-local and
declared-edge boundary failures; the content-linked hypergraph theorem lives
in the joint-capability module.
-/

set_option autoImplicit false

namespace Legitimacy

open Safety

/-! ## Forbidden-property trajectories and composed runs -/

/-- Agent-local kernel trajectory from an agent's declared kernel datum to a
later kernel datum over the same governed system. -/
structure AgentKernelTrajectory (agent : KernelGovernedAgent) where
  /-- Final kernel datum reached by the agent-local trajectory. -/
  finalKernel : LegitimacyKernelData agent.sys
  /-- Kernel-governed trajectory from the agent's declared starting datum. -/
  trajectory :
    KernelGovernedTrajectory agent.sys agent.kernel finalKernel

/-- Forbidden-property object for multi-agent composition.

The local predicate ranges over an agent-dependent kernel trajectory. The
edge fields identify which cross-agent compatibility witness is load-bearing
for excluding the corresponding emergent boundary failure. -/
structure GovernanceForbiddenProperty where
  /-- Agent-local forbidden trajectory predicate. -/
  trajectoryPredicate :
    ∀ agent : KernelGovernedAgent, AgentKernelTrajectory agent → Prop
  /-- Joint-capability-aware forbidden predicate. The action payload is typed
  by each participant's own kernel action alphabet, so a joint property can
  observe a conjunctive behavior that no single trajectory exposes. The
  definition is kept in this cyclic-safe argument form; `JointCapability`
  specializes it in `MultiAgentJointCapabilityComposition`. -/
  jointTrajectoryPredicate :
    (sys : MultiAgentSystem) →
      (participants : List KernelGovernedAgent) →
      (participation :
        ∀ agent, agent ∈ participants → agent ∈ sys.agents) →
      (perAgent :
        ∀ agent, agent ∈ participants → AgentKernelTrajectory agent) →
      (agentAction :
        ∀ agent, agent ∈ participants → agent.kernel.actionSpace.Action) →
      Prop
  /-- Cross-agent compatibility kind whose absence realizes this forbidden
  property at a boundary. -/
  edgeFailureKind : CrossAgentCompatibilityFailureKind
  /-- Structural applicability predicate for an edge. This is intentionally a
  `Prop` over the edge object, not a string or label comparison. -/
  edgeApplies : CrossAgentEdge → Prop

/-- A kernel trajectory violates one of the forbidden properties. -/
def TrajectoryViolatesForbidden
    {agent : KernelGovernedAgent}
    (traj : AgentKernelTrajectory agent)
    (forbidden : List GovernanceForbiddenProperty) : Prop :=
  ∃ property ∈ forbidden, property.trajectoryPredicate agent traj

/-- Minimal consistency required of a composed edge trajectory: the boundary
names declared endpoints in the multi-agent system. The five richer
compatibility witnesses remain external hypotheses, so composed safety cannot
be discharged by this trajectory record alone. -/
structure ComposedEdgeConsistent
    (sys : MultiAgentSystem) (edge : CrossAgentEdge) where
  /-- Declared endpoint lookup for the boundary. -/
  endpoints : Nonempty (CrossAgentEndpointWitness sys edge)

/-- A global trajectory across all declared agents, with each cross-agent
boundary tied to declared endpoints. -/
structure ComposedTrajectory (sys : MultiAgentSystem) where
  /-- Agent-local trajectory for each declared agent. -/
  perAgent :
    ∀ agent : KernelGovernedAgent, agent ∈ sys.agents →
      AgentKernelTrajectory agent
  /-- Endpoint consistency for each composed boundary. -/
  edgeConsistent :
    ∀ edge : CrossAgentEdge, edge ∈ sys.composition_edges →
      ComposedEdgeConsistent sys edge

/-- An edge realizes a forbidden boundary failure when a listed property
applies to the edge and either semantic endpoint soundness is missing or the
compatibility witness corresponding to the property's failure kind is missing.

This disjunctive encoding is a modeling choice: "the edge violates" means
either the endpoint-soundness witness exposes a forbidden boundary trajectory,
or the declared edge fails one of the framework's own compatibility
obligations. Compatibility failure is therefore a violation by this edge-local
framework's lights. The definition is not a pass-through wrapper: the
soundness branch is `KernelDerivedEndpointSoundness`, a quantified causal
soundness claim over endpoint witnesses, while the compatibility branch is the
separate missing-witness predicate indexed by
`CrossAgentCompatibilityFailureKind`. -/
def EdgeViolatesForbidden
    (sys : MultiAgentSystem)
    (edge : CrossAgentEdge)
    (forbidden : List GovernanceForbiddenProperty) : Prop :=
  ∃ property ∈ forbidden,
    property.edgeApplies edge ∧
      (¬ KernelDerivedEndpointSoundness sys edge ∨
        CrossAgentFailureAtKind sys property.edgeFailureKind edge)

/-- A composed trajectory violates the forbidden-property set when either an
agent-local trajectory violates a listed property or a composed boundary
realizes a listed edge failure. -/
def EdgeLocalComposedTrajectoryViolatesForbidden
    {sys : MultiAgentSystem}
    (traj : ComposedTrajectory sys)
    (forbidden : List GovernanceForbiddenProperty) : Prop :=
  (∃ (agent : KernelGovernedAgent),
    ∃ (hmem : agent ∈ sys.agents),
    TrajectoryViolatesForbidden (traj.perAgent agent hmem) forbidden) ∨
  (∃ (edge : CrossAgentEdge),
    ∃ (_hedge : edge ∈ sys.composition_edges),
    EdgeViolatesForbidden sys edge forbidden)

/-! ## Structural preservation chain -/

/-- Semantic kernels preserve endpoint causal soundness for every declared
endpoint of a cross-agent edge. -/
private lemma kernelDerivedEndpointSoundness_of_semantic_agents
    {sys : MultiAgentSystem}
    (h_kernel :
      ∀ agent ∈ sys.agents, IsSemanticLegitimacyKernel agent.kernel)
    (edge : CrossAgentEdge) :
    KernelDerivedEndpointSoundness sys edge := by
  intro endpoints
  exact
    ⟨causalSoundness_of_semantic_kernel
        (h_kernel endpoints.source endpoints.source_mem),
      causalSoundness_of_semantic_kernel
        (h_kernel endpoints.target endpoints.target_mem)⟩

/-- All five compatibility predicates collectively rule out the edge-local
missing-witness clause for any failure kind. -/
private lemma crossAgentFailureAtKind_absurd_of_compat
    {sys : MultiAgentSystem}
    (h_compat : AllMultiAgentCompatibilityConditions sys)
    {edge : CrossAgentEdge}
    (hedge : edge ∈ sys.composition_edges)
    {kind : CrossAgentCompatibilityFailureKind} :
    ¬ CrossAgentFailureAtKind sys kind edge := by
  cases kind
  · exact fun hmissing => hmissing (h_compat.1.witnessed_edges edge hedge)
  · exact fun hmissing => hmissing (h_compat.2.1.witnessed_edges edge hedge)
  · exact fun hmissing =>
      hmissing (h_compat.2.2.1.witnessed_edges edge hedge)
  · exact fun hmissing =>
      hmissing (h_compat.2.2.2.1.witnessed_edges edge hedge)
  · exact fun hmissing =>
      hmissing (h_compat.2.2.2.2.witnessed_edges edge hedge)

/-- Kernel soundness plus all five compatibility predicates exclude every
listed forbidden boundary violation on every composed edge. -/
theorem multi_agent_cross_edge_forbidden_excluded
    {sys : MultiAgentSystem}
    (forbidden : List GovernanceForbiddenProperty)
    (h_kernel :
      ∀ agent ∈ sys.agents, IsSemanticLegitimacyKernel agent.kernel)
    (h_compat : AllMultiAgentCompatibilityConditions sys)
    {edge : CrossAgentEdge}
    (hedge : edge ∈ sys.composition_edges) :
    ¬ EdgeViolatesForbidden sys edge forbidden := by
  intro hviolates
  rcases hviolates with
    ⟨property, _hproperty_mem, _hproperty_applies, hboundary⟩
  rcases hboundary with hmissingSoundness | hmissingCompat
  · exact hmissingSoundness
      (kernelDerivedEndpointSoundness_of_semantic_agents h_kernel edge)
  · exact
      crossAgentFailureAtKind_absurd_of_compat h_compat hedge
        hmissingCompat

/-- Under semantic endpoint kernels and the five edge-local compatibility
predicates, multi-agent kernel composition preserves forbidden-property
exclusion for forbidden properties whose violations decompose into per-agent
local trajectory violations and per-declared-cross-agent-edge boundary
failures. This is a structural compositional-safety theorem at the
declared-edge boundary; it does not address joint-capability hyperedge
dependencies in the sense of Spera 2026 §6, which would require a
joint-capability-graph extension to the substrate.

The proof is not a pass-through wrapper: the local branch consumes
`h_per_agent`; the boundary branch consumes semantic endpoint soundness and
then case-splits through all five compatibility predicates to exclude declared
edge-local boundary failures. The `h_kernel` hypothesis is load-bearing even
though noninterference witnesses carry one semantic endpoint pair: those
witnesses do not give the uniform `KernelDerivedEndpointSoundness` claim over
every possible endpoint witness unless the substrate later adds endpoint-id
uniqueness. -/
theorem multi_agent_kernel_edge_local_composition_safe
    (sys : MultiAgentSystem)
    (forbidden : List GovernanceForbiddenProperty)
    (h_kernel :
      ∀ agent ∈ sys.agents, IsSemanticLegitimacyKernel agent.kernel)
    (h_compat : AllMultiAgentCompatibilityConditions sys)
    (h_per_agent :
      ∀ agent (_hmem : agent ∈ sys.agents),
        ∀ traj : AgentKernelTrajectory agent,
          ¬ TrajectoryViolatesForbidden traj forbidden) :
    ∀ traj : ComposedTrajectory sys,
      ¬ EdgeLocalComposedTrajectoryViolatesForbidden traj forbidden := by
  intro traj hviolates
  rcases hviolates with hlocal | hedgeViolation
  · rcases hlocal with ⟨agent, hmem, hagentViolation⟩
    exact h_per_agent agent hmem (traj.perAgent agent hmem) hagentViolation
  · rcases hedgeViolation with ⟨edge, hedge, hedgeViolation⟩
    exact
      multi_agent_cross_edge_forbidden_excluded forbidden h_kernel h_compat
        hedge hedgeViolation

/-! ## Tightness fixtures -/

/-!
The five witnesses below are edge-local tightness witnesses for this theorem:
they prove that each compatibility predicate is individually load-bearing for
declared-edge forbidden-property exclusion. The Spera-style hypergraph
witnesses live in `Legitimacy.MultiAgentJointCapabilityComposition`; this file
intentionally keeps the two-channel predicate
`EdgeLocalComposedTrajectoryViolatesForbidden` separate from the full
three-channel `ComposedTrajectoryViolatesForbidden`.
-/

/-- Backward-compatible alias for downstream consumers of the original T1
name. Despite the historical name, this is the edge-local theorem above, not a
full positive complement for Spera-style joint-capability hyperedges. -/
theorem multi_agent_kernel_composition_safe
    (sys : MultiAgentSystem)
    (forbidden : List GovernanceForbiddenProperty)
    (h_kernel :
      ∀ agent ∈ sys.agents, IsSemanticLegitimacyKernel agent.kernel)
    (h_compat : AllMultiAgentCompatibilityConditions sys)
    (h_per_agent :
      ∀ agent (_hmem : agent ∈ sys.agents),
        ∀ traj : AgentKernelTrajectory agent,
          ¬ TrajectoryViolatesForbidden traj forbidden) :
    ∀ traj : ComposedTrajectory sys,
      ¬ EdgeLocalComposedTrajectoryViolatesForbidden traj forbidden :=
  multi_agent_kernel_edge_local_composition_safe sys forbidden h_kernel
    h_compat h_per_agent

/-- Boundary-only forbidden property: no agent-local trajectory is forbidden,
but a missing cross-agent witness for the selected kind is forbidden. -/
def boundaryFailureForbidden
    (kind : CrossAgentCompatibilityFailureKind) :
    GovernanceForbiddenProperty where
  trajectoryPredicate := fun _agent _traj => False
  jointTrajectoryPredicate := fun _sys _participants _participation
      _perAgent _agentAction => False
  edgeFailureKind := kind
  edgeApplies := fun _edge => True

/-- A reflexive per-agent trajectory for worked fixtures. -/
noncomputable def workedAgentReflTrajectory
    (agent : KernelGovernedAgent) :
    AgentKernelTrajectory agent where
  finalKernel := agent.kernel
  trajectory := KernelGovernedTrajectory.refl agent.kernel

/-- Composed trajectory over any worked singleton-edge system. -/
noncomputable def workedComposedTrajectory
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1) :
    ComposedTrajectory (workedSystemWithEdge edge) where
  perAgent := fun agent _hmem => workedAgentReflTrajectory agent
  edgeConsistent := by
    intro checkedEdge hmem
    simp [workedSystemWithEdge] at hmem
    subst checkedEdge
    exact
      { endpoints :=
          ⟨workedEndpointWitness edge hsource htarget⟩ }

private lemma boundaryFailureForbidden_per_agent_preserved
    (sys : MultiAgentSystem)
    (kind : CrossAgentCompatibilityFailureKind) :
    ∀ agent (_hmem : agent ∈ sys.agents),
      ∀ traj : AgentKernelTrajectory agent,
        ¬ TrajectoryViolatesForbidden traj
          [boundaryFailureForbidden kind] := by
  intro agent _hmem traj hviolates
  rcases hviolates with ⟨property, hmemForbidden, hproperty⟩
  simp at hmemForbidden
  subst property
  simp [boundaryFailureForbidden] at hproperty

private lemma authority_failure_missing_witness :
    CrossAgentFailureAtKind authorityFailureSystem
      CrossAgentCompatibilityFailureKind.authorityLattice
      authorityFailureEdge := by
  intro hwitness
  obtain ⟨witness⟩ := hwitness
  have hsource := witness.sourceLevel_projects
  have htarget := witness.targetCeiling_projects
  have horder := witness.project_monotone witness.authority_monotone
  simp [authorityFailureEdge, compatibleDelegationEdge] at hsource htarget
  rw [hsource, htarget] at horder
  omega

private lemma authority_failure_not_compatible :
    ¬ AuthorityLatticeCompatible authorityFailureSystem := by
  intro hcompat
  exact authority_failure_missing_witness
    (hcompat.witnessed_edges authorityFailureEdge (by
      simp [authorityFailureSystem, workedSystemWithEdge]))

private lemma noninterference_failure_missing_witness :
    CrossAgentFailureAtKind noninterferenceFailureSystem
      CrossAgentCompatibilityFailureKind.noninterference
      noninterferenceFailureEdge := by
  intro hwitness
  obtain ⟨witness⟩ := hwitness
  rcases witness.separated_or_declared with hsep | hdecl
  · simp [noninterferenceFailureEdge, compatibleDelegationEdge] at hsep
  · simp [noninterferenceFailureEdge, compatibleDelegationEdge] at hdecl

private lemma noninterference_failure_not_compatible :
    ¬ NoninterferenceOrDeclared noninterferenceFailureSystem := by
  intro hcompat
  exact noninterference_failure_missing_witness
    (hcompat.witnessed_edges noninterferenceFailureEdge (by
      simp [noninterferenceFailureSystem, workedSystemWithEdge]))

private lemma monotone_failure_missing_witness :
    CrossAgentFailureAtKind monotoneFailureSystem
      CrossAgentCompatibilityFailureKind.monotoneEscalation
      incompatibleEscalationEdge := by
  intro hwitness
  obtain ⟨witness⟩ := hwitness
  have hbad := witness.escalation_shape rfl
  norm_num [monotoneFailureSystem, incompatibleTwoAgentSystem,
    incompatibleEscalationEdge, compatibleDelegationEdge] at hbad

private lemma monotone_failure_not_compatible :
    ¬ MonotoneEscalationComposition monotoneFailureSystem := by
  intro hcompat
  exact monotone_failure_missing_witness
    (hcompat.witnessed_edges incompatibleEscalationEdge (by
      simp [monotoneFailureSystem, incompatibleTwoAgentSystem,
        workedSystemWithEdge]))

private lemma sacrifice_failure_missing_witness :
    CrossAgentFailureAtKind sacrificeFailureSystem
      CrossAgentCompatibilityFailureKind.sacrificeIndex
      sacrificeFailureEdge := by
  intro hwitness
  obtain ⟨witness⟩ := hwitness
  have hdecl :=
    witness.target_declared GovernanceProperty.Monotonicity (by
      simp [sacrificeFailureEdge, compatibleDelegationEdge])
  have htarget_agent : witness.endpoints.target = workedAgentB := by
    have hmem := witness.endpoints.target_mem
    simp [sacrificeFailureSystem, workedSystemWithEdge, workedAgents] at hmem
    rcases hmem with htargetA | htargetB
    · have hid := witness.endpoints.target_id
      simp [htargetA, workedAgentA, sacrificeFailureEdge,
        compatibleDelegationEdge] at hid
    · exact htargetB
  rw [htarget_agent] at hdecl
  simp [workedAgentB] at hdecl

private lemma sacrifice_failure_not_compatible :
    ¬ CompatibleSacrificeIndices sacrificeFailureSystem := by
  intro hcompat
  exact sacrifice_failure_missing_witness
    (hcompat.witnessed_edges sacrificeFailureEdge (by
      simp [sacrificeFailureSystem, workedSystemWithEdge]))

private lemma bridge_failure_missing_witness :
    CrossAgentFailureAtKind bridgeFailureSystem
      CrossAgentCompatibilityFailureKind.bridgePreservation
      bridgeFailureEdge := by
  intro hwitness
  obtain ⟨witness⟩ := hwitness
  simpa [bridgeFailureEdge, compatibleDelegationEdge,
    CrossAgentBridgeStatusSupported] using witness.bridge_supported

private lemma bridge_failure_not_compatible :
    ¬ CrossAgentBridgePreservation bridgeFailureSystem := by
  intro hcompat
  exact bridge_failure_missing_witness
    (hcompat.witnessed_edges bridgeFailureEdge (by
      simp [bridgeFailureSystem, workedSystemWithEdge]))

/-- Tightness witness: dropping authority-lattice compatibility admits a
boundary-only forbidden violation despite per-agent preservation. -/
lemma authority_lattice_tightness_witness :
    ∃ (sys : MultiAgentSystem) (forbidden : List GovernanceForbiddenProperty),
      (∀ agent (_hmem : agent ∈ sys.agents),
        ∀ traj : AgentKernelTrajectory agent,
          ¬ TrajectoryViolatesForbidden traj forbidden) ∧
      ¬ AuthorityLatticeCompatible sys ∧
      ∃ traj : ComposedTrajectory sys,
        EdgeLocalComposedTrajectoryViolatesForbidden traj forbidden := by
  refine
    ⟨authorityFailureSystem,
      [boundaryFailureForbidden
        CrossAgentCompatibilityFailureKind.authorityLattice],
      ?_, authority_failure_not_compatible, ?_⟩
  · exact
      boundaryFailureForbidden_per_agent_preserved authorityFailureSystem
        CrossAgentCompatibilityFailureKind.authorityLattice
  · refine ⟨workedComposedTrajectory authorityFailureEdge rfl rfl, ?_⟩
    change
      (∃ (agent : KernelGovernedAgent),
        ∃ (hmem : agent ∈ authorityFailureSystem.agents),
          TrajectoryViolatesForbidden
            ((workedComposedTrajectory authorityFailureEdge rfl rfl).perAgent
              agent hmem)
            [boundaryFailureForbidden
              CrossAgentCompatibilityFailureKind.authorityLattice]) ∨
        (∃ (edge : CrossAgentEdge),
          ∃ (hedge : edge ∈ authorityFailureSystem.composition_edges),
            EdgeViolatesForbidden authorityFailureSystem edge
              [boundaryFailureForbidden
                CrossAgentCompatibilityFailureKind.authorityLattice])
    right
    refine ⟨authorityFailureEdge, ?_, ?_⟩
    · simp [authorityFailureSystem, workedSystemWithEdge]
    · refine
        ⟨boundaryFailureForbidden
          CrossAgentCompatibilityFailureKind.authorityLattice, ?_, ?_, ?_⟩
      · simp
      · simp [boundaryFailureForbidden]
      · exact Or.inr authority_failure_missing_witness

/-- Tightness witness: dropping noninterference compatibility admits a
boundary-only forbidden violation despite per-agent preservation. -/
lemma noninterference_tightness_witness :
    ∃ (sys : MultiAgentSystem) (forbidden : List GovernanceForbiddenProperty),
      (∀ agent (_hmem : agent ∈ sys.agents),
        ∀ traj : AgentKernelTrajectory agent,
          ¬ TrajectoryViolatesForbidden traj forbidden) ∧
      ¬ NoninterferenceOrDeclared sys ∧
      ∃ traj : ComposedTrajectory sys,
        EdgeLocalComposedTrajectoryViolatesForbidden traj forbidden := by
  refine
    ⟨noninterferenceFailureSystem,
      [boundaryFailureForbidden
        CrossAgentCompatibilityFailureKind.noninterference],
      ?_, noninterference_failure_not_compatible, ?_⟩
  · exact
      boundaryFailureForbidden_per_agent_preserved noninterferenceFailureSystem
        CrossAgentCompatibilityFailureKind.noninterference
  · refine ⟨workedComposedTrajectory noninterferenceFailureEdge rfl rfl, ?_⟩
    change
      (∃ (agent : KernelGovernedAgent),
        ∃ (hmem : agent ∈ noninterferenceFailureSystem.agents),
          TrajectoryViolatesForbidden
            ((workedComposedTrajectory noninterferenceFailureEdge rfl rfl).perAgent
              agent hmem)
            [boundaryFailureForbidden
              CrossAgentCompatibilityFailureKind.noninterference]) ∨
        (∃ (edge : CrossAgentEdge),
          ∃ (hedge : edge ∈ noninterferenceFailureSystem.composition_edges),
            EdgeViolatesForbidden noninterferenceFailureSystem edge
              [boundaryFailureForbidden
                CrossAgentCompatibilityFailureKind.noninterference])
    right
    refine ⟨noninterferenceFailureEdge, ?_, ?_⟩
    · simp [noninterferenceFailureSystem, workedSystemWithEdge]
    · refine
        ⟨boundaryFailureForbidden
          CrossAgentCompatibilityFailureKind.noninterference, ?_, ?_, ?_⟩
      · simp
      · simp [boundaryFailureForbidden]
      · exact Or.inr noninterference_failure_missing_witness

/-- Tightness witness: dropping monotone-escalation compatibility admits a
boundary-only forbidden violation despite per-agent preservation. -/
lemma monotone_escalation_tightness_witness :
    ∃ (sys : MultiAgentSystem) (forbidden : List GovernanceForbiddenProperty),
      (∀ agent (_hmem : agent ∈ sys.agents),
        ∀ traj : AgentKernelTrajectory agent,
          ¬ TrajectoryViolatesForbidden traj forbidden) ∧
      ¬ MonotoneEscalationComposition sys ∧
      ∃ traj : ComposedTrajectory sys,
        EdgeLocalComposedTrajectoryViolatesForbidden traj forbidden := by
  refine
    ⟨monotoneFailureSystem,
      [boundaryFailureForbidden
        CrossAgentCompatibilityFailureKind.monotoneEscalation],
      ?_, monotone_failure_not_compatible, ?_⟩
  · exact
      boundaryFailureForbidden_per_agent_preserved monotoneFailureSystem
        CrossAgentCompatibilityFailureKind.monotoneEscalation
  · refine ⟨workedComposedTrajectory incompatibleEscalationEdge rfl rfl, ?_⟩
    change
      (∃ (agent : KernelGovernedAgent),
        ∃ (hmem : agent ∈ monotoneFailureSystem.agents),
          TrajectoryViolatesForbidden
            ((workedComposedTrajectory incompatibleEscalationEdge rfl rfl).perAgent
              agent hmem)
            [boundaryFailureForbidden
              CrossAgentCompatibilityFailureKind.monotoneEscalation]) ∨
        (∃ (edge : CrossAgentEdge),
          ∃ (hedge : edge ∈ monotoneFailureSystem.composition_edges),
            EdgeViolatesForbidden monotoneFailureSystem edge
              [boundaryFailureForbidden
                CrossAgentCompatibilityFailureKind.monotoneEscalation])
    right
    refine ⟨incompatibleEscalationEdge, ?_, ?_⟩
    · simp [monotoneFailureSystem, incompatibleTwoAgentSystem,
        workedSystemWithEdge]
    · refine
        ⟨boundaryFailureForbidden
          CrossAgentCompatibilityFailureKind.monotoneEscalation, ?_, ?_, ?_⟩
      · simp
      · simp [boundaryFailureForbidden]
      · exact Or.inr monotone_failure_missing_witness

/-- Tightness witness: dropping sacrifice-index compatibility admits a
boundary-only forbidden violation despite per-agent preservation. -/
lemma sacrifice_index_tightness_witness :
    ∃ (sys : MultiAgentSystem) (forbidden : List GovernanceForbiddenProperty),
      (∀ agent (_hmem : agent ∈ sys.agents),
        ∀ traj : AgentKernelTrajectory agent,
          ¬ TrajectoryViolatesForbidden traj forbidden) ∧
      ¬ CompatibleSacrificeIndices sys ∧
      ∃ traj : ComposedTrajectory sys,
        EdgeLocalComposedTrajectoryViolatesForbidden traj forbidden := by
  refine
    ⟨sacrificeFailureSystem,
      [boundaryFailureForbidden
        CrossAgentCompatibilityFailureKind.sacrificeIndex],
      ?_, sacrifice_failure_not_compatible, ?_⟩
  · exact
      boundaryFailureForbidden_per_agent_preserved sacrificeFailureSystem
        CrossAgentCompatibilityFailureKind.sacrificeIndex
  · refine ⟨workedComposedTrajectory sacrificeFailureEdge rfl rfl, ?_⟩
    change
      (∃ (agent : KernelGovernedAgent),
        ∃ (hmem : agent ∈ sacrificeFailureSystem.agents),
          TrajectoryViolatesForbidden
            ((workedComposedTrajectory sacrificeFailureEdge rfl rfl).perAgent
              agent hmem)
            [boundaryFailureForbidden
              CrossAgentCompatibilityFailureKind.sacrificeIndex]) ∨
        (∃ (edge : CrossAgentEdge),
          ∃ (hedge : edge ∈ sacrificeFailureSystem.composition_edges),
            EdgeViolatesForbidden sacrificeFailureSystem edge
              [boundaryFailureForbidden
                CrossAgentCompatibilityFailureKind.sacrificeIndex])
    right
    refine ⟨sacrificeFailureEdge, ?_, ?_⟩
    · simp [sacrificeFailureSystem, workedSystemWithEdge]
    · refine
        ⟨boundaryFailureForbidden
          CrossAgentCompatibilityFailureKind.sacrificeIndex, ?_, ?_, ?_⟩
      · simp
      · simp [boundaryFailureForbidden]
      · exact Or.inr sacrifice_failure_missing_witness

/-- Tightness witness: dropping bridge-preservation compatibility admits a
boundary-only forbidden violation despite per-agent preservation. -/
lemma bridge_preservation_tightness_witness :
    ∃ (sys : MultiAgentSystem) (forbidden : List GovernanceForbiddenProperty),
      (∀ agent (_hmem : agent ∈ sys.agents),
        ∀ traj : AgentKernelTrajectory agent,
          ¬ TrajectoryViolatesForbidden traj forbidden) ∧
      ¬ CrossAgentBridgePreservation sys ∧
      ∃ traj : ComposedTrajectory sys,
        EdgeLocalComposedTrajectoryViolatesForbidden traj forbidden := by
  refine
    ⟨bridgeFailureSystem,
      [boundaryFailureForbidden
        CrossAgentCompatibilityFailureKind.bridgePreservation],
      ?_, bridge_failure_not_compatible, ?_⟩
  · exact
      boundaryFailureForbidden_per_agent_preserved bridgeFailureSystem
        CrossAgentCompatibilityFailureKind.bridgePreservation
  · refine ⟨workedComposedTrajectory bridgeFailureEdge rfl rfl, ?_⟩
    change
      (∃ (agent : KernelGovernedAgent),
        ∃ (hmem : agent ∈ bridgeFailureSystem.agents),
          TrajectoryViolatesForbidden
            ((workedComposedTrajectory bridgeFailureEdge rfl rfl).perAgent
              agent hmem)
            [boundaryFailureForbidden
              CrossAgentCompatibilityFailureKind.bridgePreservation]) ∨
        (∃ (edge : CrossAgentEdge),
          ∃ (hedge : edge ∈ bridgeFailureSystem.composition_edges),
            EdgeViolatesForbidden bridgeFailureSystem edge
              [boundaryFailureForbidden
                CrossAgentCompatibilityFailureKind.bridgePreservation])
    right
    refine ⟨bridgeFailureEdge, ?_, ?_⟩
    · simp [bridgeFailureSystem, workedSystemWithEdge]
    · refine
        ⟨boundaryFailureForbidden
          CrossAgentCompatibilityFailureKind.bridgePreservation, ?_, ?_, ?_⟩
      · simp
      · simp [boundaryFailureForbidden]
      · exact Or.inr bridge_failure_missing_witness

/-! ## Drop-test sanity checks -/

private lemma empty_forbidden_composed_safe
    (sys : MultiAgentSystem)
    (traj : ComposedTrajectory sys) :
    ¬ EdgeLocalComposedTrajectoryViolatesForbidden traj [] := by
  intro hviolates
  rcases hviolates with hlocal | hedge
  · rcases hlocal with ⟨agent, hmem, hagent⟩
    rcases hagent with ⟨property, hproperty_mem, _hproperty⟩
    simp at hproperty_mem
  · rcases hedge with ⟨edge, hedge_mem, hedgeViolates⟩
    rcases hedgeViolates with
      ⟨property, hproperty_mem, _hproperty_applies, _hboundary⟩
    simp at hproperty_mem

private lemma empty_system_has_no_composed_edge_violation
    (agents : List KernelGovernedAgent)
    (htwo : 2 ≤ agents.length)
    (_traj : ComposedTrajectory
      { agents := agents
        two_or_more_agents := htwo
        composition_edges := [] })
    (forbidden : List GovernanceForbiddenProperty) :
    ¬ ∃ (edge : CrossAgentEdge),
      ∃ (_hedge : edge ∈
      ({ agents := agents
         two_or_more_agents := htwo
         composition_edges := [] } : MultiAgentSystem).composition_edges),
        EdgeViolatesForbidden
          ({ agents := agents
             two_or_more_agents := htwo
             composition_edges := [] } : MultiAgentSystem)
          edge forbidden := by
  intro hedge
  rcases hedge with ⟨edge, hedge_mem, _hviolates⟩
  simp at hedge_mem

end Legitimacy
