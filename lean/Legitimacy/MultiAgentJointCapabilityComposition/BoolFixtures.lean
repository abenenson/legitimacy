/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/


import Legitimacy.MultiAgentJointCapabilityComposition.Core

/-!
# Legitimacy.MultiAgentJointCapabilityComposition.BoolFixtures

Nontrivial Bool-action Spera fixtures for joint-capability composition.
-/

set_option autoImplicit false

namespace Legitimacy

open Safety

/-! ## Nontrivial-action Spera fixtures -/

/-- Bool-action semantic agent A for the non-vacuous content-link fixture. -/
noncomputable def speraBoolAgentA : KernelGovernedAgent where
  id := 0
  n := 1
  sys := Safety.exampleGovernedSystem
  kernel := Safety.boolGovernanceKernelData
  authority := workedAuthorityGraph
  sacrificeIndex := [GovernanceProperty.Consistency]
  escalationRank := 0

/-- Bool-action semantic agent B for the non-vacuous content-link fixture. -/
noncomputable def speraBoolAgentB : KernelGovernedAgent where
  id := 1
  n := 1
  sys := Safety.exampleGovernedSystem
  kernel := Safety.boolGovernanceKernelData
  authority := workedAuthorityGraph
  sacrificeIndex := [GovernanceProperty.Consistency]
  escalationRank := 1

/-- Bool-action semantic agent C for the higher-arity Spera fixture. -/
noncomputable def speraBoolAgentC : KernelGovernedAgent where
  id := 2
  n := 1
  sys := Safety.exampleGovernedSystem
  kernel := Safety.boolGovernanceKernelData
  authority := workedAuthorityGraph
  sacrificeIndex := [GovernanceProperty.Consistency]
  escalationRank := 2

noncomputable def speraBoolAgents : List KernelGovernedAgent :=
  [speraBoolAgentA, speraBoolAgentB]

noncomputable def speraBoolThreeAgents : List KernelGovernedAgent :=
  [speraBoolAgentA, speraBoolAgentB, speraBoolAgentC]

lemma speraBoolAgents_semantic :
    ∀ agent ∈ speraBoolAgents,
      IsSemanticLegitimacyKernel agent.kernel := by
  intro agent hmem
  simp [speraBoolAgents, speraBoolAgentA, speraBoolAgentB] at hmem
  rcases hmem with hagent | hagent
  · subst agent
    exact Safety.boolGovernanceSemanticKernel
  · subst agent
    exact Safety.boolGovernanceSemanticKernel

lemma speraBoolThreeAgents_semantic :
    ∀ agent ∈ speraBoolThreeAgents,
      IsSemanticLegitimacyKernel agent.kernel := by
  intro agent hmem
  simp [speraBoolThreeAgents, speraBoolAgentA, speraBoolAgentB,
    speraBoolAgentC] at hmem
  rcases hmem with hagent | hagent | hagent
  · subst agent
    exact Safety.boolGovernanceSemanticKernel
  · subst agent
    exact Safety.boolGovernanceSemanticKernel
  · subst agent
    exact Safety.boolGovernanceSemanticKernel

noncomputable def speraBoolSystemWithEdge
    (edge : CrossAgentEdge) : MultiAgentSystem where
  agents := speraBoolAgents
  two_or_more_agents := by simp [speraBoolAgents]
  composition_edges := [edge]

noncomputable def speraBoolThreeSystemWithEdge
    (edge : CrossAgentEdge) : MultiAgentSystem where
  agents := speraBoolThreeAgents
  two_or_more_agents := by simp [speraBoolThreeAgents]
  composition_edges := [edge]

noncomputable def speraBoolEndpointWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1) :
    CrossAgentEndpointWitness (speraBoolSystemWithEdge edge) edge where
  source := speraBoolAgentA
  target := speraBoolAgentB
  source_mem := by simp [speraBoolSystemWithEdge, speraBoolAgents]
  target_mem := by simp [speraBoolSystemWithEdge, speraBoolAgents]
  source_id := by simp [speraBoolAgentA, hsource]
  target_id := by simp [speraBoolAgentB, htarget]

noncomputable def speraBoolThreeEndpointWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1) :
    CrossAgentEndpointWitness (speraBoolThreeSystemWithEdge edge) edge where
  source := speraBoolAgentA
  target := speraBoolAgentB
  source_mem := by simp [speraBoolThreeSystemWithEdge, speraBoolThreeAgents]
  target_mem := by simp [speraBoolThreeSystemWithEdge, speraBoolThreeAgents]
  source_id := by simp [speraBoolAgentA, hsource]
  target_id := by simp [speraBoolAgentB, htarget]

noncomputable def speraBoolAuthorityWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hlevel : edge.sourceAuthorityLevel ≤ edge.targetAuthorityCeiling) :
    CrossAgentAuthorityLatticeWitness (speraBoolSystemWithEdge edge) edge where
  endpoints := speraBoolEndpointWitness edge hsource htarget
  carrier := Nat
  le := (· ≤ ·)
  le_refl := by intro _; rfl
  le_trans := by intro _ _ _; exact Nat.le_trans
  sourceAuthority := edge.sourceAuthorityLevel
  targetAuthority := edge.targetAuthorityCeiling
  projectLevel := id
  project_monotone := by intro _ _ h; exact h
  sourceLevel_projects := rfl
  targetCeiling_projects := rfl
  authority_monotone := hlevel

noncomputable def speraBoolThreeAuthorityWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hlevel : edge.sourceAuthorityLevel ≤ edge.targetAuthorityCeiling) :
    CrossAgentAuthorityLatticeWitness
      (speraBoolThreeSystemWithEdge edge) edge where
  endpoints := speraBoolThreeEndpointWitness edge hsource htarget
  carrier := Nat
  le := (· ≤ ·)
  le_refl := by intro _; rfl
  le_trans := by intro _ _ _; exact Nat.le_trans
  sourceAuthority := edge.sourceAuthorityLevel
  targetAuthority := edge.targetAuthorityCeiling
  projectLevel := id
  project_monotone := by intro _ _ h; exact h
  sourceLevel_projects := rfl
  targetCeiling_projects := rfl
  authority_monotone := hlevel

noncomputable def speraBoolNoninterferenceWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hsep : edge.modifiesTargetKernel = false ∨
      edge.interferenceDeclared = true) :
    CrossAgentNoninterferenceWitness (speraBoolSystemWithEdge edge) edge where
  endpoints := speraBoolEndpointWitness edge hsource htarget
  source_invariant := by
    simpa [speraBoolEndpointWitness, speraBoolAgentA, Safety.KernelInvariant]
      using Safety.boolGovernanceSemanticKernel
  target_invariant := by
    simpa [speraBoolEndpointWitness, speraBoolAgentB, Safety.KernelInvariant]
      using Safety.boolGovernanceSemanticKernel
  target_preservation_step := by
    exact Safety.KernelStep.refl speraBoolAgentB.kernel
  target_preserved := by
    exact
      Safety.kernelStep_preserves_invariant
        (Safety.KernelStep.refl speraBoolAgentB.kernel)
        Safety.boolGovernanceSemanticKernel
  target_preserved_by_step := by
    rfl
  separated_or_declared := hsep

noncomputable def speraBoolThreeNoninterferenceWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hsep : edge.modifiesTargetKernel = false ∨
      edge.interferenceDeclared = true) :
    CrossAgentNoninterferenceWitness
      (speraBoolThreeSystemWithEdge edge) edge where
  endpoints := speraBoolThreeEndpointWitness edge hsource htarget
  source_invariant := by
    simpa [speraBoolThreeEndpointWitness, speraBoolAgentA,
      Safety.KernelInvariant] using Safety.boolGovernanceSemanticKernel
  target_invariant := by
    simpa [speraBoolThreeEndpointWitness, speraBoolAgentB,
      Safety.KernelInvariant] using Safety.boolGovernanceSemanticKernel
  target_preservation_step := by
    exact Safety.KernelStep.refl speraBoolAgentB.kernel
  target_preserved := by
    exact
      Safety.kernelStep_preserves_invariant
        (Safety.KernelStep.refl speraBoolAgentB.kernel)
        Safety.boolGovernanceSemanticKernel
  target_preserved_by_step := by
    rfl
  separated_or_declared := hsep

noncomputable def speraBoolEscalationWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hshape :
      edge.kind = CrossAgentEdgeKind.escalation →
        edge.escalationVerdictFloor + edge.escalationStrengthening ≤
          edge.escalationVerdictCeiling) :
    CrossAgentEscalationMonotonicityWitness
      (speraBoolSystemWithEdge edge) edge where
  endpoints := speraBoolEndpointWitness edge hsource htarget
  target_graph_monotone :=
    Safety.exampleGovernanceGraph_allLegitimacyAxioms.2.2.1
  escalation_shape := hshape

noncomputable def speraBoolThreeEscalationWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hshape :
      edge.kind = CrossAgentEdgeKind.escalation →
        edge.escalationVerdictFloor + edge.escalationStrengthening ≤
          edge.escalationVerdictCeiling) :
    CrossAgentEscalationMonotonicityWitness
      (speraBoolThreeSystemWithEdge edge) edge where
  endpoints := speraBoolThreeEndpointWitness edge hsource htarget
  target_graph_monotone :=
    Safety.exampleGovernanceGraph_allLegitimacyAxioms.2.2.1
  escalation_shape := hshape

noncomputable def speraBoolSacrificeWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hcontradiction : edge.contradictorySacrifice = false)
    (hsourceDecl :
      ∀ property, property ∈ edge.sourceSacrifices →
        property ∈ speraBoolAgentA.sacrificeIndex)
    (htargetDecl :
      ∀ property, property ∈ edge.targetSacrifices →
        property ∈ speraBoolAgentB.sacrificeIndex) :
    CrossAgentSacrificeIndexWitness (speraBoolSystemWithEdge edge) edge where
  endpoints := speraBoolEndpointWitness edge hsource htarget
  no_contradiction := hcontradiction
  source_declared := by intro property hproperty; exact hsourceDecl property hproperty
  target_declared := by intro property hproperty; exact htargetDecl property hproperty
  source_protocol_boundary := by
    left
    simpa [speraBoolEndpointWitness, speraBoolAgentA] using
      workedNonSacrificedHold
  target_protocol_boundary := by
    left
    simpa [speraBoolEndpointWitness, speraBoolAgentB] using
      workedNonSacrificedHold

noncomputable def speraBoolThreeSacrificeWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hcontradiction : edge.contradictorySacrifice = false)
    (hsourceDecl :
      ∀ property, property ∈ edge.sourceSacrifices →
        property ∈ speraBoolAgentA.sacrificeIndex)
    (htargetDecl :
      ∀ property, property ∈ edge.targetSacrifices →
        property ∈ speraBoolAgentB.sacrificeIndex) :
    CrossAgentSacrificeIndexWitness
      (speraBoolThreeSystemWithEdge edge) edge where
  endpoints := speraBoolThreeEndpointWitness edge hsource htarget
  no_contradiction := hcontradiction
  source_declared := by intro property hproperty; exact hsourceDecl property hproperty
  target_declared := by intro property hproperty; exact htargetDecl property hproperty
  source_protocol_boundary := by
    left
    simpa [speraBoolThreeEndpointWitness, speraBoolAgentA] using
      workedNonSacrificedHold
  target_protocol_boundary := by
    left
    simpa [speraBoolThreeEndpointWitness, speraBoolAgentB] using
      workedNonSacrificedHold

noncomputable def speraBoolBridgeWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hsupported : CrossAgentBridgeStatusSupported edge.bridgeStatus) :
    CrossAgentBridgeWitness (speraBoolSystemWithEdge edge) edge where
  endpoints := speraBoolEndpointWitness edge hsource htarget
  bridge_supported := hsupported

noncomputable def speraBoolThreeBridgeWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hsupported : CrossAgentBridgeStatusSupported edge.bridgeStatus) :
    CrossAgentBridgeWitness (speraBoolThreeSystemWithEdge edge) edge where
  endpoints := speraBoolThreeEndpointWitness edge hsource htarget
  bridge_supported := hsupported

noncomputable def speraBoolAllConditions
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hlevel : edge.sourceAuthorityLevel ≤ edge.targetAuthorityCeiling)
    (hsep : edge.modifiesTargetKernel = false ∨
      edge.interferenceDeclared = true)
    (hshape :
      edge.kind = CrossAgentEdgeKind.escalation →
        edge.escalationVerdictFloor + edge.escalationStrengthening ≤
          edge.escalationVerdictCeiling)
    (hcontradiction : edge.contradictorySacrifice = false)
    (hsourceDecl :
      ∀ property, property ∈ edge.sourceSacrifices →
        property ∈ speraBoolAgentA.sacrificeIndex)
    (htargetDecl :
      ∀ property, property ∈ edge.targetSacrifices →
        property ∈ speraBoolAgentB.sacrificeIndex)
    (hsupported : CrossAgentBridgeStatusSupported edge.bridgeStatus) :
    AllMultiAgentCompatibilityConditions (speraBoolSystemWithEdge edge) :=
  ⟨{ nonempty_composition := by simp [speraBoolSystemWithEdge],
      witnessed_edges := by
        intro checkedEdge hmem
        simp [speraBoolSystemWithEdge] at hmem
        subst checkedEdge
        exact ⟨speraBoolAuthorityWitness edge hsource htarget hlevel⟩ },
    { nonempty_composition := by simp [speraBoolSystemWithEdge],
      witnessed_edges := by
        intro checkedEdge hmem
        simp [speraBoolSystemWithEdge] at hmem
        subst checkedEdge
        exact ⟨speraBoolNoninterferenceWitness edge hsource htarget hsep⟩ },
    { nonempty_composition := by simp [speraBoolSystemWithEdge],
      witnessed_edges := by
        intro checkedEdge hmem
        simp [speraBoolSystemWithEdge] at hmem
        subst checkedEdge
        exact ⟨speraBoolEscalationWitness edge hsource htarget hshape⟩ },
    { nonempty_composition := by simp [speraBoolSystemWithEdge],
      witnessed_edges := by
        intro checkedEdge hmem
        simp [speraBoolSystemWithEdge] at hmem
        subst checkedEdge
        exact
          ⟨speraBoolSacrificeWitness edge hsource htarget hcontradiction
            hsourceDecl htargetDecl⟩ },
    { nonempty_composition := by simp [speraBoolSystemWithEdge],
      witnessed_edges := by
        intro checkedEdge hmem
        simp [speraBoolSystemWithEdge] at hmem
        subst checkedEdge
        exact ⟨speraBoolBridgeWitness edge hsource htarget hsupported⟩ }⟩

noncomputable def speraBoolThreeAllConditions
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hlevel : edge.sourceAuthorityLevel ≤ edge.targetAuthorityCeiling)
    (hsep : edge.modifiesTargetKernel = false ∨
      edge.interferenceDeclared = true)
    (hshape :
      edge.kind = CrossAgentEdgeKind.escalation →
        edge.escalationVerdictFloor + edge.escalationStrengthening ≤
          edge.escalationVerdictCeiling)
    (hcontradiction : edge.contradictorySacrifice = false)
    (hsourceDecl :
      ∀ property, property ∈ edge.sourceSacrifices →
        property ∈ speraBoolAgentA.sacrificeIndex)
    (htargetDecl :
      ∀ property, property ∈ edge.targetSacrifices →
        property ∈ speraBoolAgentB.sacrificeIndex)
    (hsupported : CrossAgentBridgeStatusSupported edge.bridgeStatus) :
    AllMultiAgentCompatibilityConditions
      (speraBoolThreeSystemWithEdge edge) :=
  ⟨{ nonempty_composition := by simp [speraBoolThreeSystemWithEdge],
      witnessed_edges := by
        intro checkedEdge hmem
        simp [speraBoolThreeSystemWithEdge] at hmem
        subst checkedEdge
        exact ⟨speraBoolThreeAuthorityWitness edge hsource htarget hlevel⟩ },
    { nonempty_composition := by simp [speraBoolThreeSystemWithEdge],
      witnessed_edges := by
        intro checkedEdge hmem
        simp [speraBoolThreeSystemWithEdge] at hmem
        subst checkedEdge
        exact
          ⟨speraBoolThreeNoninterferenceWitness edge hsource htarget hsep⟩ },
    { nonempty_composition := by simp [speraBoolThreeSystemWithEdge],
      witnessed_edges := by
        intro checkedEdge hmem
        simp [speraBoolThreeSystemWithEdge] at hmem
        subst checkedEdge
        exact ⟨speraBoolThreeEscalationWitness edge hsource htarget hshape⟩ },
    { nonempty_composition := by simp [speraBoolThreeSystemWithEdge],
      witnessed_edges := by
        intro checkedEdge hmem
        simp [speraBoolThreeSystemWithEdge] at hmem
        subst checkedEdge
        exact
          ⟨speraBoolThreeSacrificeWitness edge hsource htarget hcontradiction
            hsourceDecl htargetDecl⟩ },
    { nonempty_composition := by simp [speraBoolThreeSystemWithEdge],
      witnessed_edges := by
        intro checkedEdge hmem
        simp [speraBoolThreeSystemWithEdge] at hmem
        subst checkedEdge
        exact
          ⟨speraBoolThreeBridgeWitness edge hsource htarget hsupported⟩ }⟩

/-- Bool-action tracking edge for the non-vacuous content-link fixture. It is
not a single-action ordinary edge, but it names the two-agent conjunction with
a level-2 tool-access budget. -/
def speraBoolTrackedToolEdge : CrossAgentEdge :=
  { compatibleDelegationEdge with
    kind := CrossAgentEdgeKind.toolAccess
    sourceAuthorityLevel := 2
    targetAuthorityCeiling := 2 }

/-- Bool-action Spera fixture: the old five edge-local predicates hold, and the
declared tool-access edge tracks every distinct two-agent joint capability. -/
noncomputable def speraBoolFixture : MultiAgentSystem :=
  speraBoolSystemWithEdge speraBoolTrackedToolEdge

lemma speraBoolFixture_semantic :
    ∀ agent ∈ speraBoolFixture.agents,
      IsSemanticLegitimacyKernel agent.kernel := by
  simpa [speraBoolFixture, speraBoolSystemWithEdge] using
    speraBoolAgents_semantic

lemma speraBoolFixture_old_five_compatible :
    AllMultiAgentCompatibilityConditions speraBoolFixture := by
  exact
    speraBoolAllConditions speraBoolTrackedToolEdge rfl rfl (by decide)
      (Or.inl rfl) (by intro h; cases h) rfl
      (by
        intro property h
        simpa [speraBoolTrackedToolEdge, compatibleDelegationEdge,
          speraBoolAgentA] using h)
      (by
        intro property h
        simpa [speraBoolTrackedToolEdge, compatibleDelegationEdge,
          speraBoolAgentB] using h)
      trivial

/-- Non-vacuous Bool forbidden property: the solo predicate is a real agent-id
test, and the joint predicate requires A's `true` action with B's `false`
action. -/
def boolJointForbidden : GovernanceForbiddenProperty where
  trajectoryPredicate := fun agent _traj => agent.id = 99
  jointTrajectoryPredicate := fun _sys participants _participation
      _perAgent agentAction =>
    (∃ hA : speraBoolAgentA ∈ participants,
      ∃ hB : speraBoolAgentB ∈ participants,
        agentAction speraBoolAgentA hA = true ∧
          agentAction speraBoolAgentB hB = false)
  edgeFailureKind := CrossAgentCompatibilityFailureKind.authorityLattice
  edgeApplies := fun _edge => False

def boolJointForbiddenList : List GovernanceForbiddenProperty :=
  [boolJointForbidden]

noncomputable def speraBoolJointAction
    (agent : KernelGovernedAgent)
    (hmem : agent ∈ [speraBoolAgentA, speraBoolAgentB]) :
    agent.kernel.actionSpace.Action :=
  by
    have haction_bool : agent.kernel.actionSpace.Action = Bool := by
      rcases (List.mem_cons.mp hmem) with rfl | htail
      · rfl
      · rcases (List.mem_cons.mp htail) with rfl | hnil
        · rfl
        · cases hnil
    exact haction_bool.symm ▸ decide (agent.id = 0)

noncomputable def speraBoolJointCapability :
    JointCapability speraBoolFixture where
  participating_agents := [speraBoolAgentA, speraBoolAgentB]
  participating_agent_ids_nodup := by
    simp [speraBoolAgentA, speraBoolAgentB]
  participation_proof := by
    intro agent hmem
    simp [speraBoolFixture, speraBoolSystemWithEdge,
      speraBoolAgents] at hmem ⊢
    exact hmem
  agent_action := speraBoolJointAction
  cardinality_two_or_more := by simp
  not_single_declared_edge := by
    intro edge hedge hrealizes
    simp [speraBoolFixture, speraBoolSystemWithEdge] at hedge
    subst edge
    simp [EdgeRealizesJointCapability, speraBoolTrackedToolEdge,
      compatibleDelegationEdge, speraBoolAgentA, speraBoolAgentB] at hrealizes

noncomputable def speraBoolTrajectory :
    ComposedTrajectory speraBoolFixture where
  perAgent := fun agent _hmem => workedAgentReflTrajectory agent
  edgeConsistent := by
    intro edge hmem
    simp [speraBoolFixture, speraBoolSystemWithEdge] at hmem
    subst edge
    exact
      { endpoints :=
          ⟨speraBoolEndpointWitness speraBoolTrackedToolEdge rfl rfl⟩ }

lemma speraBoolJointCapability_actions_distinguishable :
    speraBoolJointCapability.agent_action speraBoolAgentA (by simp [speraBoolJointCapability]) ≠
      speraBoolJointCapability.agent_action speraBoolAgentB (by simp [speraBoolJointCapability]) := by
  simp [speraBoolJointCapability, speraBoolJointAction, speraBoolAgentA,
    speraBoolAgentB]

lemma speraBoolJointCapability_reaches :
    JointCapabilityReaches speraBoolJointCapability
      (fun agent hmem =>
        speraBoolTrajectory.perAgent agent
          (speraBoolJointCapability.participation_proof agent hmem))
      boolJointForbiddenList := by
  refine ⟨boolJointForbidden, by simp [boolJointForbiddenList], ?_, ?_⟩
  · simp [boolJointForbidden, speraBoolJointCapability, speraBoolJointAction,
      speraBoolAgentA, speraBoolAgentB]
  · intro agent hmem
    simp [boolJointForbidden]
    simp [speraBoolJointCapability, speraBoolAgentA, speraBoolAgentB] at hmem
    rcases hmem with hagent | hagent
    · subst agent
      simp
    · subst agent
      simp

lemma speraBoolFixture_joint_violation :
    JointCapabilityViolatesForbidden speraBoolTrajectory
      boolJointForbiddenList := by
  exact ⟨speraBoolJointCapability, speraBoolJointCapability_reaches⟩

lemma speraBoolFixture_no_per_agent_violation :
    ¬ PerAgentTrajectoryViolatesForbidden speraBoolTrajectory
      boolJointForbiddenList := by
  intro hviolates
  rcases hviolates with ⟨agent, hmem, htraj⟩
  rcases htraj with ⟨property, hproperty_mem, hproperty⟩
  simp [boolJointForbiddenList] at hproperty_mem
  subst property
  simp [speraBoolFixture, speraBoolSystemWithEdge, speraBoolAgents,
    speraBoolAgentA, speraBoolAgentB] at hmem
  rcases hmem with hagent | hagent
  · subst agent
    simp [boolJointForbidden, speraBoolAgentA] at hproperty
  · subst agent
    simp [boolJointForbidden, speraBoolAgentB] at hproperty

lemma speraBoolFixture_no_edge_boundary_violation :
    ¬ EdgeBoundaryViolatesForbidden speraBoolTrajectory
      boolJointForbiddenList := by
  intro hviolates
  rcases hviolates with ⟨edge, hedge, hedgeViolation⟩
  rcases hedgeViolation with
    ⟨property, hproperty_mem, hproperty_applies, _hboundary⟩
  simp [boolJointForbiddenList] at hproperty_mem
  subst property
  simp [boolJointForbidden] at hproperty_applies

private lemma speraBoolFixture_agent_eq_of_id_zero
    {agent : KernelGovernedAgent}
    (hmem : agent ∈ speraBoolFixture.agents)
    (hid : agent.id = 0) :
    agent = speraBoolAgentA := by
  simp [speraBoolFixture, speraBoolSystemWithEdge, speraBoolAgents,
    speraBoolAgentA, speraBoolAgentB] at hmem
  rcases hmem with hagent | hagent
  · exact hagent
  · subst agent
    simp at hid

private lemma speraBoolFixture_agent_eq_of_id_one
    {agent : KernelGovernedAgent}
    (hmem : agent ∈ speraBoolFixture.agents)
    (hid : agent.id = 1) :
    agent = speraBoolAgentB := by
  simp [speraBoolFixture, speraBoolSystemWithEdge, speraBoolAgents,
    speraBoolAgentA, speraBoolAgentB] at hmem
  rcases hmem with hagent | hagent
  · subst agent
    simp at hid
  · exact hagent

private lemma speraBoolFixture_participant_facts
    (jc : JointCapability speraBoolFixture) :
    speraBoolAgentA ∈ jc.participating_agents ∧
      speraBoolAgentB ∈ jc.participating_agents ∧
      jc.participating_agents.length = 2 := by
  let ids := jc.participating_agents.map (fun agent => agent.id)
  have hsubset : ids ⊆ [0, 1] := by
    intro id hid
    rcases List.mem_map.mp hid with ⟨agent, hagent, rfl⟩
    have hsys := jc.participation_proof agent hagent
    simp [speraBoolFixture, speraBoolSystemWithEdge, speraBoolAgents,
      speraBoolAgentA, speraBoolAgentB] at hsys
    rcases hsys with hagentA | hagentB
    · subst agent
      simp
    · subst agent
      simp
  have hsubperm : ids.Subperm [0, 1] :=
    jc.participating_agent_ids_nodup.subperm hsubset
  have hlength_ge : [0, 1].length ≤ ids.length := by
    simpa [ids] using jc.cardinality_two_or_more
  have hperm : ids.Perm [0, 1] :=
    hsubperm.perm_of_length_le hlength_ge
  have hlength : jc.participating_agents.length = 2 := by
    simpa [ids] using hperm.length_eq
  have hid0 : 0 ∈ ids := by
    exact (hperm.mem_iff).2 (by simp)
  have hid1 : 1 ∈ ids := by
    exact (hperm.mem_iff).2 (by simp)
  rcases List.mem_map.mp hid0 with ⟨agent0, hagent0, hid_agent0⟩
  rcases List.mem_map.mp hid1 with ⟨agent1, hagent1, hid_agent1⟩
  have hagent0_eq :
      agent0 = speraBoolAgentA :=
    speraBoolFixture_agent_eq_of_id_zero
      (jc.participation_proof agent0 hagent0) hid_agent0
  have hagent1_eq :
      agent1 = speraBoolAgentB :=
    speraBoolFixture_agent_eq_of_id_one
      (jc.participation_proof agent1 hagent1) hid_agent1
  exact
    ⟨by simpa [hagent0_eq] using hagent0,
      by simpa [hagent1_eq] using hagent1,
      hlength⟩

lemma speraBoolFixture_joint_compatible :
    JointCapabilityCompatibility speraBoolFixture := by
  intro jc
  rcases speraBoolFixture_participant_facts jc with
    ⟨hagentA, hagentB, hlength⟩
  refine ⟨speraBoolTrackedToolEdge, ?_, ?_⟩
  · simp [speraBoolFixture, speraBoolSystemWithEdge]
  · refine ⟨speraBoolAgentA, hagentA, speraBoolAgentB, hagentB, ?_⟩
    simp [speraBoolTrackedToolEdge, compatibleDelegationEdge,
      speraBoolAgentA, speraBoolAgentB, hlength]

theorem exampleJointCapabilityCompatible :
    JointCapabilityCompatibility speraBoolFixture :=
  speraBoolFixture_joint_compatible

lemma speraBoolFixture_not_joint_compatible_refuted :
    ¬ ¬ JointCapabilityCompatibility speraBoolFixture := by
  intro hnot
  exact hnot exampleJointCapabilityCompatible

lemma spera_bool_fixture_joint_capability_inhabited :
    (∀ agent ∈ speraBoolFixture.agents,
        IsSemanticLegitimacyKernel agent.kernel) ∧
    AllMultiAgentCompatibilityConditions speraBoolFixture ∧
    JointCapabilityCompatibility speraBoolFixture ∧
    ∃ traj : ComposedTrajectory speraBoolFixture,
      JointCapabilityViolatesForbidden traj boolJointForbiddenList ∧
      ¬ PerAgentTrajectoryViolatesForbidden traj boolJointForbiddenList ∧
      ¬ EdgeBoundaryViolatesForbidden traj boolJointForbiddenList ∧
      speraBoolJointCapability.agent_action speraBoolAgentA
          (by simp [speraBoolJointCapability]) ≠
        speraBoolJointCapability.agent_action speraBoolAgentB
          (by simp [speraBoolJointCapability]) := by
  exact
    ⟨speraBoolFixture_semantic,
      speraBoolFixture_old_five_compatible,
      speraBoolFixture_joint_compatible,
      ⟨speraBoolTrajectory, speraBoolFixture_joint_violation,
        speraBoolFixture_no_per_agent_violation,
        speraBoolFixture_no_edge_boundary_violation,
        speraBoolJointCapability_actions_distinguishable⟩⟩

lemma speraBoolJointCapability_is_tracked :
    ∃ edge, ∃ _hedge : edge ∈ speraBoolFixture.composition_edges,
      EdgeTracksJointCapability edge speraBoolJointCapability := by
  refine ⟨speraBoolTrackedToolEdge, ?_, ?_⟩
  · simp [speraBoolFixture, speraBoolSystemWithEdge]
  · simp [EdgeTracksJointCapability, speraBoolJointCapability,
      speraBoolTrackedToolEdge, compatibleDelegationEdge, speraBoolAgentA,
      speraBoolAgentB]

theorem example_joint_capability_compatible_exists :
    ∃ sys : MultiAgentSystem,
      (∀ agent ∈ sys.agents, IsSemanticLegitimacyKernel agent.kernel) ∧
      AllMultiAgentCompatibilityConditions sys ∧
      JointCapabilityCompatibility sys ∧
      (∃ agentA ∈ sys.agents,
        ∃ agentB ∈ sys.agents, agentA.id ≠ agentB.id) ∧
      ∃ jc : JointCapability sys,
        ∃ edge, ∃ _hedge : edge ∈ sys.composition_edges,
          EdgeTracksJointCapability edge jc ∧
          ∃ hA : speraBoolAgentA ∈ jc.participating_agents,
          ∃ hB : speraBoolAgentB ∈ jc.participating_agents,
            jc.agent_action speraBoolAgentA hA ≠
              jc.agent_action speraBoolAgentB hB := by
  refine
    ⟨speraBoolFixture, speraBoolFixture_semantic,
      speraBoolFixture_old_five_compatible,
      speraBoolFixture_joint_compatible, ?_, ?_⟩
  · refine ⟨speraBoolAgentA, ?_, speraBoolAgentB, ?_, ?_⟩
    · simp [speraBoolFixture, speraBoolSystemWithEdge, speraBoolAgents]
    · simp [speraBoolFixture, speraBoolSystemWithEdge, speraBoolAgents]
    · simp [speraBoolAgentA, speraBoolAgentB]
  · refine
      ⟨speraBoolJointCapability, speraBoolTrackedToolEdge, ?_, ?_, ?_⟩
    · simp [speraBoolFixture, speraBoolSystemWithEdge]
    · simpa using
        (show EdgeTracksJointCapability speraBoolTrackedToolEdge
          speraBoolJointCapability by
          simp [EdgeTracksJointCapability, speraBoolJointCapability,
            speraBoolTrackedToolEdge, compatibleDelegationEdge,
            speraBoolAgentA, speraBoolAgentB])
    · refine ⟨by simp [speraBoolJointCapability], by
        simp [speraBoolJointCapability], ?_⟩
      exact speraBoolJointCapability_actions_distinguishable

/-- Nonempty tracked-safe forbidden property used to instantiate T1.2 on the
Bool tracked fixture. It is not syntactically false: it asks for an undeclared
agent id in either the local or joint participant channel. -/
def boolTrackedSafeForbidden : GovernanceForbiddenProperty where
  trajectoryPredicate := fun agent _traj => agent.id = 99
  jointTrajectoryPredicate := fun _sys participants _participation
      _perAgent _agentAction =>
    ∃ agent ∈ participants, agent.id = 99
  edgeFailureKind := CrossAgentCompatibilityFailureKind.authorityLattice
  edgeApplies := fun _edge => False

def boolTrackedSafeForbiddenList : List GovernanceForbiddenProperty :=
  [boolTrackedSafeForbidden]

private lemma speraBoolFixture_no_agent_id_99
    {agent : KernelGovernedAgent}
    (hmem : agent ∈ speraBoolFixture.agents) :
    agent.id ≠ 99 := by
  simp [speraBoolFixture, speraBoolSystemWithEdge, speraBoolAgents,
    speraBoolAgentA, speraBoolAgentB] at hmem
  rcases hmem with hagent | hagent
  · subst agent
    simp
  · subst agent
    simp

lemma speraBoolFixture_tracked_safe_per_agent :
    ∀ agent (_hmem : agent ∈ speraBoolFixture.agents),
      ∀ traj : AgentKernelTrajectory agent,
        ¬ TrajectoryViolatesForbidden traj
          boolTrackedSafeForbiddenList := by
  intro agent hmem _traj hviolates
  rcases hviolates with ⟨property, hproperty_mem, hproperty⟩
  simp [boolTrackedSafeForbiddenList] at hproperty_mem
  subst property
  exact speraBoolFixture_no_agent_id_99 hmem hproperty

lemma speraBoolFixture_tracked_safe_joint_discharge :
    ∀ jc : JointCapability speraBoolFixture,
      (∃ edge, ∃ _hedge : edge ∈ speraBoolFixture.composition_edges,
        EdgeTracksJointCapability edge jc) →
      ∀ per_agent_traj :
        ∀ agent, agent ∈ jc.participating_agents →
          AgentKernelTrajectory agent,
        ¬ JointCapabilityReaches jc per_agent_traj
          boolTrackedSafeForbiddenList := by
  intro jc _htracked _per_agent_traj hreach
  rcases hreach with
    ⟨property, hproperty_mem, hjoint_fires, _hsolo_quiet⟩
  simp [boolTrackedSafeForbiddenList] at hproperty_mem
  subst property
  rcases hjoint_fires with ⟨agent, hagent, hid⟩
  exact
    speraBoolFixture_no_agent_id_99
      (jc.participation_proof agent hagent) hid

theorem exampleJointCapabilityT12_nonvacuous :
    ∀ traj : ComposedTrajectory speraBoolFixture,
      ¬ ComposedTrajectoryViolatesForbidden traj
        boolTrackedSafeForbiddenList :=
  multi_agent_kernel_joint_capability_composition_safe
    speraBoolFixture boolTrackedSafeForbiddenList
    speraBoolFixture_semantic
    speraBoolFixture_old_five_compatible
    exampleJointCapabilityCompatible
    speraBoolFixture_tracked_safe_per_agent
    speraBoolFixture_tracked_safe_joint_discharge

/-- Three-agent Bool-action fixture: the hidden hyperedge has arity three, while
the only declared compatible edge still names the A/B ordinary delegation. -/
noncomputable def speraBoolThreeFixture : MultiAgentSystem :=
  speraBoolThreeSystemWithEdge compatibleDelegationEdge

lemma speraBoolThreeFixture_semantic :
    ∀ agent ∈ speraBoolThreeFixture.agents,
      IsSemanticLegitimacyKernel agent.kernel := by
  simpa [speraBoolThreeFixture, speraBoolThreeSystemWithEdge] using
    speraBoolThreeAgents_semantic

lemma speraBoolThreeFixture_old_five_compatible :
    AllMultiAgentCompatibilityConditions speraBoolThreeFixture := by
  exact
    speraBoolThreeAllConditions compatibleDelegationEdge rfl rfl (by decide)
      (Or.inl rfl) (by intro h; cases h) rfl
      (by intro property h; simpa [compatibleDelegationEdge, speraBoolAgentA] using h)
      (by intro property h; simpa [compatibleDelegationEdge, speraBoolAgentB] using h)
      trivial

def boolThreeJointForbidden : GovernanceForbiddenProperty where
  trajectoryPredicate := fun agent _traj => agent.id = 99
  jointTrajectoryPredicate := fun _sys participants _participation
      _perAgent agentAction =>
    (∃ hA : speraBoolAgentA ∈ participants,
      ∃ hB : speraBoolAgentB ∈ participants,
      ∃ hC : speraBoolAgentC ∈ participants,
        agentAction speraBoolAgentA hA = true ∧
          agentAction speraBoolAgentB hB = false ∧
          agentAction speraBoolAgentC hC = true)
  edgeFailureKind := CrossAgentCompatibilityFailureKind.authorityLattice
  edgeApplies := fun _edge => False

def boolThreeJointForbiddenList : List GovernanceForbiddenProperty :=
  [boolThreeJointForbidden]

noncomputable def speraBoolThreeJointAction
    (agent : KernelGovernedAgent)
    (hmem : agent ∈ [speraBoolAgentA, speraBoolAgentB, speraBoolAgentC]) :
    agent.kernel.actionSpace.Action :=
  by
    have haction_bool : agent.kernel.actionSpace.Action = Bool := by
      rcases (List.mem_cons.mp hmem) with rfl | htail
      · rfl
      · rcases (List.mem_cons.mp htail) with rfl | htail
        · rfl
        · rcases (List.mem_cons.mp htail) with rfl | hnil
          · rfl
          · cases hnil
    exact haction_bool.symm ▸ decide (agent.id ≠ 1)

noncomputable def speraBoolThreeJointCapability :
    JointCapability speraBoolThreeFixture where
  participating_agents := [speraBoolAgentA, speraBoolAgentB, speraBoolAgentC]
  participating_agent_ids_nodup := by
    simp [speraBoolAgentA, speraBoolAgentB, speraBoolAgentC]
  participation_proof := by
    intro agent hmem
    simp [speraBoolThreeFixture, speraBoolThreeSystemWithEdge,
      speraBoolThreeAgents] at hmem ⊢
    exact hmem
  agent_action := speraBoolThreeJointAction
  cardinality_two_or_more := by simp
  not_single_declared_edge := by
    intro edge hedge hrealizes
    simp [speraBoolThreeFixture, speraBoolThreeSystemWithEdge] at hedge
    subst edge
    simp [EdgeRealizesJointCapability, compatibleDelegationEdge,
      speraBoolAgentA, speraBoolAgentB, speraBoolAgentC] at hrealizes

noncomputable def speraBoolThreeTrajectory :
    ComposedTrajectory speraBoolThreeFixture where
  perAgent := fun agent _hmem => workedAgentReflTrajectory agent
  edgeConsistent := by
    intro edge hmem
    simp [speraBoolThreeFixture, speraBoolThreeSystemWithEdge] at hmem
    subst edge
    exact
      { endpoints :=
          ⟨speraBoolThreeEndpointWitness compatibleDelegationEdge rfl rfl⟩ }

lemma speraBoolThreeJointCapability_actions_distinguishable :
    speraBoolThreeJointCapability.agent_action speraBoolAgentA
        (by simp [speraBoolThreeJointCapability]) ≠
      speraBoolThreeJointCapability.agent_action speraBoolAgentB
        (by simp [speraBoolThreeJointCapability]) := by
  simp [speraBoolThreeJointCapability, speraBoolThreeJointAction,
    speraBoolAgentA, speraBoolAgentB, speraBoolAgentC]

lemma speraBoolThreeJointCapability_reaches :
    JointCapabilityReaches speraBoolThreeJointCapability
      (fun agent hmem =>
        speraBoolThreeTrajectory.perAgent agent
          (speraBoolThreeJointCapability.participation_proof agent hmem))
      boolThreeJointForbiddenList := by
  refine ⟨boolThreeJointForbidden, by simp [boolThreeJointForbiddenList], ?_, ?_⟩
  · simp [boolThreeJointForbidden, speraBoolThreeJointCapability,
      speraBoolThreeJointAction, speraBoolAgentA, speraBoolAgentB,
      speraBoolAgentC]
  · intro agent hmem
    simp [boolThreeJointForbidden]
    simp [speraBoolThreeJointCapability, speraBoolAgentA, speraBoolAgentB,
      speraBoolAgentC] at hmem
    rcases hmem with hagent | hagent | hagent
    · subst agent
      simp
    · subst agent
      simp
    · subst agent
      simp

lemma speraBoolThreeFixture_not_joint_compatible :
    ¬ JointCapabilityCompatibility speraBoolThreeFixture := by
  intro hcompat
  rcases hcompat speraBoolThreeJointCapability with ⟨edge, hedge, htrack⟩
  simp [speraBoolThreeFixture, speraBoolThreeSystemWithEdge] at hedge
  subst edge
  simp [EdgeTracksJointCapability, speraBoolThreeJointCapability,
    compatibleDelegationEdge, speraBoolAgentA, speraBoolAgentB,
    speraBoolAgentC] at htrack

lemma spera_bool_three_agent_joint_capability_tightness :
    (∀ agent ∈ speraBoolThreeFixture.agents,
        IsSemanticLegitimacyKernel agent.kernel) ∧
    AllMultiAgentCompatibilityConditions speraBoolThreeFixture ∧
    ¬ JointCapabilityCompatibility speraBoolThreeFixture ∧
    JointCapabilityReaches speraBoolThreeJointCapability
      (fun agent hmem =>
        speraBoolThreeTrajectory.perAgent agent
          (speraBoolThreeJointCapability.participation_proof agent hmem))
      boolThreeJointForbiddenList ∧
    speraBoolThreeJointCapability.participating_agents.length = 3 ∧
    speraBoolThreeJointCapability.agent_action speraBoolAgentA
        (by simp [speraBoolThreeJointCapability]) ≠
      speraBoolThreeJointCapability.agent_action speraBoolAgentB
        (by simp [speraBoolThreeJointCapability]) := by
  exact
    ⟨speraBoolThreeFixture_semantic,
      speraBoolThreeFixture_old_five_compatible,
      speraBoolThreeFixture_not_joint_compatible,
      speraBoolThreeJointCapability_reaches,
      by simp [speraBoolThreeJointCapability],
      speraBoolThreeJointCapability_actions_distinguishable⟩


end Legitimacy
