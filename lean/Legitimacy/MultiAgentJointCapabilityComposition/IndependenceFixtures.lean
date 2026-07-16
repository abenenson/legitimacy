/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.MultiAgentJointCapabilityComposition.Core
import Legitimacy.MultiAgentJointCapabilityComposition.CanonicalFixtures
import Legitimacy.MultiAgentJointCapabilityComposition.BoolFixtures

/-!
# Legitimacy.MultiAgentJointCapabilityComposition.IndependenceFixtures

Independence and hypothesis drop-test fixtures for joint-capability composition.
-/

set_option autoImplicit false

namespace Legitimacy

open Safety

/-! ## `h_kernel` independence fixture -/

/-- A declared dormant agent whose kernel data fails the causal-soundness
projection of semantic legitimacy. The compatible edge below does not use this
agent as an endpoint, exposing that old-five edge-local compatibility does not
derive the headline theorem's global `h_kernel` hypothesis. -/
noncomputable def nonSemanticDormantAgent : KernelGovernedAgent where
  id := 99
  n := 3
  sys := unsafeCompositionSystem
  kernel := replayStateKernelData unsafeCompositionSystem
  authority := workedAuthorityGraph
  sacrificeIndex := [GovernanceProperty.Consistency]
  escalationRank := 99

lemma nonSemanticDormantAgent_not_semantic :
    ¬ IsSemanticLegitimacyKernel nonSemanticDormantAgent.kernel := by
  intro hsemantic
  exact unsafeComposition_not_causally_sound
    (by
      simpa [LegitimacyKernelData.KernelCausalSoundness] using
        hsemantic.runtimeKernel.compositionalSafety)

noncomputable def hKernelDebtAgents : List KernelGovernedAgent :=
  [speraBoolAgentA, speraBoolAgentB, nonSemanticDormantAgent]

noncomputable def hKernelDebtSystemWithEdge
    (edge : CrossAgentEdge) : MultiAgentSystem where
  agents := hKernelDebtAgents
  two_or_more_agents := by simp [hKernelDebtAgents]
  composition_edges := [edge]

noncomputable def hKernelDebtFixture : MultiAgentSystem :=
  hKernelDebtSystemWithEdge compatibleDelegationEdge

noncomputable def hKernelDebtEndpointWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1) :
    CrossAgentEndpointWitness (hKernelDebtSystemWithEdge edge) edge where
  source := speraBoolAgentA
  target := speraBoolAgentB
  source_mem := by simp [hKernelDebtSystemWithEdge, hKernelDebtAgents]
  target_mem := by simp [hKernelDebtSystemWithEdge, hKernelDebtAgents]
  source_id := by simp [speraBoolAgentA, hsource]
  target_id := by simp [speraBoolAgentB, htarget]

lemma hKernelDebtFixture_old_five_compatible :
    AllMultiAgentCompatibilityConditions hKernelDebtFixture := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine
      { nonempty_composition := by simp [hKernelDebtFixture,
          hKernelDebtSystemWithEdge],
        witnessed_edges := ?_ }
    intro checkedEdge hmem
    simp [hKernelDebtFixture, hKernelDebtSystemWithEdge] at hmem
    subst checkedEdge
    exact
      ⟨{ endpoints := hKernelDebtEndpointWitness compatibleDelegationEdge rfl rfl
         carrier := Nat
         le := (· ≤ ·)
         le_refl := by intro _; rfl
         le_trans := by intro _ _ _; exact Nat.le_trans
         sourceAuthority := compatibleDelegationEdge.sourceAuthorityLevel
         targetAuthority := compatibleDelegationEdge.targetAuthorityCeiling
         projectLevel := id
         project_monotone := by intro _ _ h; exact h
         sourceLevel_projects := rfl
         targetCeiling_projects := rfl
         authority_monotone := by decide }⟩
  · refine
      { nonempty_composition := by simp [hKernelDebtFixture,
          hKernelDebtSystemWithEdge],
        witnessed_edges := ?_ }
    intro checkedEdge hmem
    simp [hKernelDebtFixture, hKernelDebtSystemWithEdge] at hmem
    subst checkedEdge
    exact
      ⟨{ endpoints := hKernelDebtEndpointWitness compatibleDelegationEdge rfl rfl
         source_invariant := by
          simpa [hKernelDebtEndpointWitness, speraBoolAgentA,
            Safety.KernelInvariant] using Safety.boolGovernanceSemanticKernel
         target_invariant := by
          simpa [hKernelDebtEndpointWitness, speraBoolAgentB,
            Safety.KernelInvariant] using Safety.boolGovernanceSemanticKernel
         target_preservation_step := by
          exact Safety.KernelStep.refl speraBoolAgentB.kernel
         target_preserved := by
          exact
            Safety.kernelStep_preserves_invariant
              (Safety.KernelStep.refl speraBoolAgentB.kernel)
              Safety.boolGovernanceSemanticKernel
         target_preserved_by_step := by rfl
         separated_or_declared := Or.inl rfl }⟩
  · refine
      { nonempty_composition := by simp [hKernelDebtFixture,
          hKernelDebtSystemWithEdge],
        witnessed_edges := ?_ }
    intro checkedEdge hmem
    simp [hKernelDebtFixture, hKernelDebtSystemWithEdge] at hmem
    subst checkedEdge
    exact
      ⟨{ endpoints := hKernelDebtEndpointWitness compatibleDelegationEdge rfl rfl
         target_graph_monotone :=
          Safety.exampleGovernanceGraph_allLegitimacyAxioms.2.2.1
         escalation_shape := by intro h; cases h }⟩
  · refine
      { nonempty_composition := by simp [hKernelDebtFixture,
          hKernelDebtSystemWithEdge],
        witnessed_edges := ?_ }
    intro checkedEdge hmem
    simp [hKernelDebtFixture, hKernelDebtSystemWithEdge] at hmem
    subst checkedEdge
    exact
      ⟨{ endpoints := hKernelDebtEndpointWitness compatibleDelegationEdge rfl rfl
         no_contradiction := rfl
         source_declared := by
          intro property hproperty
          simp [compatibleDelegationEdge] at hproperty
          subst property
          simp [hKernelDebtEndpointWitness, speraBoolAgentA]
         target_declared := by
          intro property hproperty
          simp [compatibleDelegationEdge] at hproperty
          subst property
          simp [hKernelDebtEndpointWitness, speraBoolAgentB]
         source_protocol_boundary := by
          left
          simpa [hKernelDebtEndpointWitness, speraBoolAgentA] using
            workedNonSacrificedHold
         target_protocol_boundary := by
          left
          simpa [hKernelDebtEndpointWitness, speraBoolAgentB] using
            workedNonSacrificedHold }⟩
  · refine
      { nonempty_composition := by simp [hKernelDebtFixture,
          hKernelDebtSystemWithEdge],
        witnessed_edges := ?_ }
    intro checkedEdge hmem
    simp [hKernelDebtFixture, hKernelDebtSystemWithEdge] at hmem
    subst checkedEdge
    exact
      ⟨{ endpoints := hKernelDebtEndpointWitness compatibleDelegationEdge rfl rfl
         bridge_supported := trivial }⟩

noncomputable def hKernelDebtJointCapability :
    JointCapability hKernelDebtFixture where
  participating_agents := [speraBoolAgentA, speraBoolAgentB]
  participating_agent_ids_nodup := by
    simp [speraBoolAgentA, speraBoolAgentB]
  participation_proof := by
    intro agent hmem
    simp [hKernelDebtFixture, hKernelDebtSystemWithEdge, hKernelDebtAgents,
      speraBoolAgentA, speraBoolAgentB] at hmem ⊢
    rcases hmem with hagent | hagent
    · exact Or.inl hagent
    · exact Or.inr (Or.inl hagent)
  agent_action := speraBoolJointAction
  cardinality_two_or_more := by simp
  not_single_declared_edge := by
    intro edge hedge hrealizes
    simp [hKernelDebtFixture, hKernelDebtSystemWithEdge] at hedge
    subst edge
    simp [EdgeRealizesJointCapability, compatibleDelegationEdge,
      speraBoolAgentA, speraBoolAgentB] at hrealizes

lemma hKernelDebtFixture_lacks_global_h_kernel :
    ¬ (∀ agent ∈ hKernelDebtFixture.agents,
        IsSemanticLegitimacyKernel agent.kernel) := by
  intro hkernel
  exact nonSemanticDormantAgent_not_semantic
    (hkernel nonSemanticDormantAgent (by
      simp [hKernelDebtFixture, hKernelDebtSystemWithEdge, hKernelDebtAgents]))

lemma h_kernel_not_derivable_from_old_five_with_bool_actions :
    AllMultiAgentCompatibilityConditions hKernelDebtFixture ∧
    ¬ (∀ agent ∈ hKernelDebtFixture.agents,
        IsSemanticLegitimacyKernel agent.kernel) ∧
    hKernelDebtJointCapability.agent_action speraBoolAgentA
        (by simp [hKernelDebtJointCapability]) ≠
      hKernelDebtJointCapability.agent_action speraBoolAgentB
        (by simp [hKernelDebtJointCapability]) := by
  exact
    ⟨hKernelDebtFixture_old_five_compatible,
      hKernelDebtFixture_lacks_global_h_kernel,
      by
        simp [hKernelDebtJointCapability, speraBoolJointAction,
          speraBoolAgentA, speraBoolAgentB]⟩

lemma drop_h_kernel_not_derivable_from_old_five :
    AllMultiAgentCompatibilityConditions hKernelDebtFixture ∧
    ¬ (∀ agent ∈ hKernelDebtFixture.agents,
        IsSemanticLegitimacyKernel agent.kernel) :=
  ⟨hKernelDebtFixture_old_five_compatible,
    hKernelDebtFixture_lacks_global_h_kernel⟩

lemma boolJointForbidden_solo_predicate_nonvacuous :
    TrajectoryViolatesForbidden
      (workedAgentReflTrajectory nonSemanticDormantAgent)
      boolJointForbiddenList := by
  exact
    ⟨boolJointForbidden, by simp [boolJointForbiddenList],
      by simp [boolJointForbidden, nonSemanticDormantAgent]⟩

lemma boolThreeJointForbidden_solo_predicate_nonvacuous :
    TrajectoryViolatesForbidden
      (workedAgentReflTrajectory nonSemanticDormantAgent)
      boolThreeJointForbiddenList := by
  exact
    ⟨boolThreeJointForbidden, by simp [boolThreeJointForbiddenList],
      by simp [boolThreeJointForbidden, nonSemanticDormantAgent]⟩

/-- Alternate structurally distinct edge: the same two agents share memory
rather than using the canonical delegation edge. It still satisfies the old
five edge-local predicates, but it cannot track a joint capability because
`EdgeTracksJointCapability` requires a `toolAccess` edge. -/
def speraSharedMemoryUntrackedEdge : CrossAgentEdge :=
  { compatibleDelegationEdge with kind := CrossAgentEdgeKind.sharedMemory }

noncomputable def speraSharedMemoryFixture : MultiAgentSystem :=
  workedSystemWithEdge speraSharedMemoryUntrackedEdge

lemma speraSharedMemoryFixture_old_five_compatible :
    AllMultiAgentCompatibilityConditions speraSharedMemoryFixture := by
  exact
    ⟨workedAuthorityCompatible speraSharedMemoryUntrackedEdge rfl rfl
        (by decide),
      workedNoninterferenceCompatible speraSharedMemoryUntrackedEdge rfl rfl
        (Or.inl rfl),
      workedMonotoneCompatible speraSharedMemoryUntrackedEdge rfl rfl
        (by intro h; cases h),
      workedSacrificeCompatible speraSharedMemoryUntrackedEdge rfl rfl rfl
        (by intro property h; simpa [speraSharedMemoryUntrackedEdge,
          compatibleDelegationEdge, workedAgentA] using h)
        (by intro property h; simpa [speraSharedMemoryUntrackedEdge,
          compatibleDelegationEdge, workedAgentB] using h),
      workedBridgeCompatible speraSharedMemoryUntrackedEdge rfl rfl trivial⟩

/-- Alternate untracked hyperedge over a structurally different
old-five-compatible system. The failure is not just a different action vector:
the declared edge has `kind = sharedMemory`, while tracking requires
`toolAccess`. -/
noncomputable def speraAlternateJointCapability :
    JointCapability speraSharedMemoryFixture where
  participating_agents := [workedAgentA, workedAgentB]
  participating_agent_ids_nodup := by
    simp [workedAgentA, workedAgentB]
  participation_proof := by
    intro agent hmem
    simp [speraSharedMemoryFixture,
      workedSystemWithEdge, workedAgents] at hmem ⊢
    exact hmem
  agent_action := workedJointAction
  cardinality_two_or_more := by simp
  not_single_declared_edge := by
    intro edge hedge hrealizes
    simp [speraSharedMemoryFixture, workedSystemWithEdge] at hedge
    subst edge
    simp [EdgeRealizesJointCapability, speraSharedMemoryUntrackedEdge,
      compatibleDelegationEdge, workedAgentA, workedAgentB] at hrealizes

lemma speraAlternateFixture_not_joint_compatible :
    ¬ JointCapabilityCompatibility speraSharedMemoryFixture := by
  intro hcompat
  rcases hcompat speraAlternateJointCapability with ⟨edge, hedge, htrack⟩
  simp [speraSharedMemoryFixture, workedSystemWithEdge] at hedge
  subst edge
  simp [EdgeTracksJointCapability, speraAlternateJointCapability,
    speraSharedMemoryUntrackedEdge, compatibleDelegationEdge, workedAgentA,
    workedAgentB] at htrack

/-- A declared tool-access edge that tracks, but does not directly realize, the
two-agent joint capability. The source authority level names both participant
actions, so `EdgeTracksJointCapability` holds; direct realization remains
false because the edge is not a single-action edge. -/
def speraTrackedToolEdge : CrossAgentEdge :=
  { compatibleDelegationEdge with
    kind := CrossAgentEdgeKind.toolAccess
    sourceAuthorityLevel := 2
    targetAuthorityCeiling := 2 }

noncomputable def speraTrackedToolFixture : MultiAgentSystem :=
  workedSystemWithEdge speraTrackedToolEdge

lemma speraTrackedToolFixture_old_five_compatible :
    AllMultiAgentCompatibilityConditions speraTrackedToolFixture := by
  exact
    ⟨workedAuthorityCompatible speraTrackedToolEdge rfl rfl
        (by decide),
      workedNoninterferenceCompatible speraTrackedToolEdge rfl rfl
        (Or.inl rfl),
      workedMonotoneCompatible speraTrackedToolEdge rfl rfl
        (by intro h; cases h),
      workedSacrificeCompatible speraTrackedToolEdge rfl rfl rfl
        (by intro property h; simpa [speraTrackedToolEdge,
          compatibleDelegationEdge, workedAgentA] using h)
        (by intro property h; simpa [speraTrackedToolEdge,
          compatibleDelegationEdge, workedAgentB] using h),
      workedBridgeCompatible speraTrackedToolEdge rfl rfl trivial⟩

noncomputable def speraTrackedJointCapability :
    JointCapability speraTrackedToolFixture where
  participating_agents := [workedAgentA, workedAgentB]
  participating_agent_ids_nodup := by
    simp [workedAgentA, workedAgentB]
  participation_proof := by
    intro agent hmem
    simp [speraTrackedToolFixture,
      workedSystemWithEdge, workedAgents] at hmem ⊢
    exact hmem
  agent_action := workedJointAction
  cardinality_two_or_more := by simp
  not_single_declared_edge := by
    intro edge hedge hrealizes
    simp [speraTrackedToolFixture, workedSystemWithEdge] at hedge
    subst edge
    simp [EdgeRealizesJointCapability, speraTrackedToolEdge,
      compatibleDelegationEdge, workedAgentA, workedAgentB] at hrealizes

lemma speraTrackedJointCapability_is_tracked :
    ∃ edge, ∃ _hedge : edge ∈ speraTrackedToolFixture.composition_edges,
      EdgeTracksJointCapability edge speraTrackedJointCapability := by
  refine ⟨speraTrackedToolEdge, by simp [speraTrackedToolFixture,
    workedSystemWithEdge], ?_⟩
  simp [EdgeTracksJointCapability, speraTrackedJointCapability,
    speraTrackedToolEdge, compatibleDelegationEdge, workedAgentA,
    workedAgentB]

/-- Drop-test witness for `h_joint`: without the sixth predicate, the
canonical Spera fixture satisfies the old five predicates and per-agent
preservation while still exhibiting a joint-capability violation. -/
lemma drop_h_joint_admits_spera_violation :
    AllMultiAgentCompatibilityConditions speraCanonicalFixture ∧
    (∀ agent (_hmem : agent ∈ speraCanonicalFixture.agents),
      ∀ traj : AgentKernelTrajectory agent,
        ¬ TrajectoryViolatesForbidden traj jointForbiddenList) ∧
    ∃ traj : ComposedTrajectory speraCanonicalFixture,
      ComposedTrajectoryViolatesForbidden traj jointForbiddenList := by
  refine
    ⟨speraCanonicalFixture_old_five_compatible, ?_,
      ⟨speraCanonicalTrajectory, Or.inr (Or.inr
        speraCanonicalFixture_joint_violation)⟩⟩
  intro agent hmem traj hviolates
  rcases hviolates with ⟨property, hproperty_mem, hproperty⟩
  simp [jointForbiddenList] at hproperty_mem
  subst property
  simp [jointCapabilityForbidden] at hproperty

/-- Local-only forbidden property used by the `h_per_agent` drop-test. -/
def workedAgentALocalForbidden : GovernanceForbiddenProperty where
  trajectoryPredicate := fun agent _traj => agent.id = 0
  jointTrajectoryPredicate := fun _sys _participants _participation
      _perAgent _agentAction => False
  edgeFailureKind := CrossAgentCompatibilityFailureKind.authorityLattice
  edgeApplies := fun _edge => False

/-- Drop-test witness for `h_per_agent`: local forbidden properties still
require the per-agent preservation hypothesis, independently of the new joint
predicate. -/
lemma drop_h_per_agent_admits_local_violation :
    PerAgentTrajectoryViolatesForbidden speraCanonicalTrajectory
      [workedAgentALocalForbidden] := by
  refine ⟨workedAgentA, ?_, ?_⟩
  · simp [speraCanonicalFixture, compatibleTwoAgentSystem,
      workedSystemWithEdge, workedAgents]
  · exact
      ⟨workedAgentALocalForbidden, by simp,
        by simp [workedAgentALocalForbidden, workedAgentA]⟩

/-- Drop-test witness for `h_compat_5`: the old edge-local boundary witnesses
remain load-bearing inside the three-channel theorem. -/
lemma drop_h_compat_5_admits_edge_violation :
    ∃ sys forbidden,
      (∀ agent (_hmem : agent ∈ sys.agents),
        ∀ traj : AgentKernelTrajectory agent,
          ¬ TrajectoryViolatesForbidden traj forbidden) ∧
      ¬ AuthorityLatticeCompatible sys ∧
      ∃ traj : ComposedTrajectory sys,
        ComposedTrajectoryViolatesForbidden traj forbidden := by
  rcases authority_lattice_tightness_witness with
    ⟨sys, forbidden, hper, hnot, traj, hviolates⟩
  rcases hviolates with hlocal | hedge
  · exact ⟨sys, forbidden, hper, hnot, traj, Or.inl hlocal⟩
  · exact ⟨sys, forbidden, hper, hnot, traj, Or.inr (Or.inl hedge)⟩


end Legitimacy
