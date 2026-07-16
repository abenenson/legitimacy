/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.MultiAgentJointCapabilityComposition.Core

/-!
# Legitimacy.MultiAgentJointCapabilityComposition.CanonicalFixtures

Unit-action Spera tightness fixtures for joint-capability composition.
-/

set_option autoImplicit false

namespace Legitimacy

open Safety

/-! ## Spera-style tightness fixtures -/

/-- Boundary-inert forbidden property used by the joint-capability fixtures:
no single agent and no declared edge violates it by itself. Only the joint
capability channel can realize it. -/
def jointCapabilityForbidden : GovernanceForbiddenProperty where
  trajectoryPredicate := fun _agent _traj => False
  jointTrajectoryPredicate := fun _sys participants _participation
      _perAgent agentAction =>
    (∃ hA : workedAgentA ∈ participants,
      ∃ hB : workedAgentB ∈ participants,
        agentAction workedAgentA hA = () ∧
          agentAction workedAgentB hB = ())
  edgeFailureKind := CrossAgentCompatibilityFailureKind.authorityLattice
  edgeApplies := fun _edge => False

/-- Forbidden list for the canonical Spera fixture. -/
def jointForbiddenList : List GovernanceForbiddenProperty :=
  [jointCapabilityForbidden]

noncomputable def workedJointAction
    (agent : KernelGovernedAgent)
    (hmem : agent ∈ [workedAgentA, workedAgentB]) :
    agent.kernel.actionSpace.Action :=
  by
    have haction_unit : agent.kernel.actionSpace.Action = Unit := by
      rcases (List.mem_cons.mp hmem) with rfl | htail
      · rfl
      · rcases (List.mem_cons.mp htail) with rfl | hnil
        · rfl
        · cases hnil
    exact haction_unit.symm ▸ ()

/-- Spera 2026 canonical fixture system: two individually semantic agents and
one ordinary compatible delegation edge. The edge does not track the hidden
conjunctive action. -/
noncomputable def speraCanonicalFixture : MultiAgentSystem :=
  compatibleTwoAgentSystem

/-- The canonical hidden hyperedge `{c_A1, c_B1} -> forbidden`: both agents
contribute kernel-typed actions, and no declared edge tracks the conjunction. -/
noncomputable def speraCanonicalJointCapability :
    JointCapability speraCanonicalFixture where
  participating_agents := [workedAgentA, workedAgentB]
  participating_agent_ids_nodup := by
    simp [workedAgentA, workedAgentB]
  participation_proof := by
    intro agent hmem
    simp [speraCanonicalFixture, compatibleTwoAgentSystem,
      workedSystemWithEdge, workedAgents] at hmem ⊢
    exact hmem
  agent_action := workedJointAction
  cardinality_two_or_more := by simp
  not_single_declared_edge := by
    intro edge hedge hrealizes
    simp [speraCanonicalFixture, compatibleTwoAgentSystem,
      workedSystemWithEdge] at hedge
    subst edge
    simp [EdgeRealizesJointCapability, compatibleDelegationEdge, workedAgentA,
      workedAgentB] at hrealizes

/-- Worked composed trajectory for the canonical Spera fixture. -/
noncomputable def speraCanonicalTrajectory :
    ComposedTrajectory speraCanonicalFixture :=
  workedComposedTrajectory compatibleDelegationEdge rfl rfl

lemma speraCanonicalFixture_semantic :
    ∀ agent ∈ speraCanonicalFixture.agents,
      IsSemanticLegitimacyKernel agent.kernel := by
  simpa [speraCanonicalFixture] using compatibleTwoAgentSystem_semantic

lemma speraCanonicalFixture_old_five_compatible :
    AllMultiAgentCompatibilityConditions speraCanonicalFixture := by
  simpa [speraCanonicalFixture] using compatible_two_agent_all_conditions

lemma speraCanonicalFixture_not_joint_compatible :
    ¬ JointCapabilityCompatibility speraCanonicalFixture := by
  intro hcompat
  rcases hcompat speraCanonicalJointCapability with ⟨edge, hedge, htrack⟩
  simp [speraCanonicalFixture, compatibleTwoAgentSystem,
    workedSystemWithEdge] at hedge
  subst edge
  simp [EdgeTracksJointCapability, speraCanonicalJointCapability,
    compatibleDelegationEdge, workedAgentA, workedAgentB] at htrack

lemma speraCanonicalJointCapability_reaches :
    JointCapabilityReaches speraCanonicalJointCapability
      (fun agent hmem =>
        speraCanonicalTrajectory.perAgent agent
          (speraCanonicalJointCapability.participation_proof agent hmem))
      jointForbiddenList := by
  refine ⟨jointCapabilityForbidden, by simp [jointForbiddenList], ?_, ?_⟩
  · simp [jointCapabilityForbidden, speraCanonicalJointCapability, workedAgentA,
      workedAgentB]
    constructor
    · cases (workedJointAction workedAgentA (by simp))
      rfl
    · cases (workedJointAction workedAgentB (by simp))
      rfl
  · intro agent hmem
    simp [jointCapabilityForbidden]

lemma speraCanonicalFixture_joint_violation :
    JointCapabilityViolatesForbidden speraCanonicalTrajectory
      jointForbiddenList := by
  exact
    ⟨speraCanonicalJointCapability, speraCanonicalJointCapability_reaches⟩

lemma speraCanonicalFixture_no_per_agent_violation :
    ¬ PerAgentTrajectoryViolatesForbidden speraCanonicalTrajectory
      jointForbiddenList := by
  intro hviolates
  rcases hviolates with ⟨agent, hmem, htraj⟩
  rcases htraj with ⟨property, hproperty_mem, hproperty⟩
  simp [jointForbiddenList] at hproperty_mem
  subst property
  simp [jointCapabilityForbidden] at hproperty

lemma speraCanonicalFixture_no_edge_boundary_violation :
    ¬ EdgeBoundaryViolatesForbidden speraCanonicalTrajectory
      jointForbiddenList := by
  intro hviolates
  rcases hviolates with ⟨edge, hedge, hedgeViolation⟩
  rcases hedgeViolation with
    ⟨property, hproperty_mem, hproperty_applies, _hboundary⟩
  simp [jointForbiddenList] at hproperty_mem
  subst property
  simp [jointCapabilityForbidden] at hproperty_applies

/-- Mandatory tightness witness: the old five compatibility predicates and
per-agent safety hold, but the sixth predicate fails and the composed
trajectory violates the forbidden set only through the joint-capability
channel. -/
lemma spera_canonical_fixture_joint_capability_tightness :
    (∀ agent ∈ speraCanonicalFixture.agents,
        IsSemanticLegitimacyKernel agent.kernel) ∧
    AllMultiAgentCompatibilityConditions speraCanonicalFixture ∧
    ¬ JointCapabilityCompatibility speraCanonicalFixture ∧
    ∃ traj : ComposedTrajectory speraCanonicalFixture,
      JointCapabilityViolatesForbidden traj jointForbiddenList ∧
      ¬ PerAgentTrajectoryViolatesForbidden traj jointForbiddenList ∧
      ¬ EdgeBoundaryViolatesForbidden traj jointForbiddenList := by
  exact
    ⟨speraCanonicalFixture_semantic,
      speraCanonicalFixture_old_five_compatible,
      speraCanonicalFixture_not_joint_compatible,
      ⟨speraCanonicalTrajectory, speraCanonicalFixture_joint_violation,
        speraCanonicalFixture_no_per_agent_violation,
        speraCanonicalFixture_no_edge_boundary_violation⟩⟩



end Legitimacy
