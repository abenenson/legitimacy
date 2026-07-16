/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.MultiAgentComposition.Certificates

/-!
# Legitimacy.MultiAgentComposition.Fixtures

Worked two-agent fixtures and per-condition independence witnesses for
cross-agent composition.
-/

set_option autoImplicit false

namespace Legitimacy


/-! ## Worked two-agent fixtures -/

/-- Small reported authority surface for the worked multi-agent fixtures. -/
def workedAuthorityGraph : Safety.AuthorityGraph where
  nodes := ["agent-a", "agent-b"]
  edges := [{ fromNode := "agent-a", toNode := "agent-b" }]
  overrides := []

/-- First worked semantic-kernel agent. -/
noncomputable def workedAgentA : KernelGovernedAgent where
  id := 0
  n := 1
  sys := Safety.exampleGovernedSystem
  kernel := Safety.exampleGovernanceKernelData
  authority := workedAuthorityGraph
  sacrificeIndex := [GovernanceProperty.Consistency]
  escalationRank := 0

/-- Second worked semantic-kernel agent. -/
noncomputable def workedAgentB : KernelGovernedAgent where
  id := 1
  n := 1
  sys := Safety.exampleGovernedSystem
  kernel := Safety.exampleGovernanceKernelData
  authority := workedAuthorityGraph
  sacrificeIndex := [GovernanceProperty.Consistency]
  escalationRank := 1

noncomputable def workedAgents : List KernelGovernedAgent :=
  [workedAgentA, workedAgentB]

lemma workedAgents_semantic :
    ∀ agent ∈ workedAgents,
      IsSemanticLegitimacyKernel agent.kernel := by
  intro agent hmem
  simp [workedAgents, workedAgentA, workedAgentB] at hmem
  rcases hmem with hagent | hagent
  · subst hagent
    exact Safety.exampleGovernanceSemanticKernel
  · subst hagent
    exact Safety.exampleGovernanceSemanticKernel

/-- Build a two-agent worked system from one edge. -/
noncomputable def workedSystemWithEdge
    (edge : CrossAgentEdge) : MultiAgentSystem where
  agents := workedAgents
  two_or_more_agents := by simp [workedAgents]
  composition_edges := [edge]

/-- Endpoint lookup for all worked edges. -/
noncomputable def workedEndpointWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1) :
    CrossAgentEndpointWitness (workedSystemWithEdge edge) edge where
  source := workedAgentA
  target := workedAgentB
  source_mem := by simp [workedSystemWithEdge, workedAgents]
  target_mem := by simp [workedSystemWithEdge, workedAgents]
  source_id := by simp [workedAgentA, hsource]
  target_id := by simp [workedAgentB, htarget]

/-- The worked graph satisfies the protocol non-vacuity property used by
`propertyHolds`. -/
lemma workedGraph_protocolNonVacuous :
    ProtocolNonVacuous Safety.exampleGovernanceGraph := by
  let witness := Safety.exampleGovernanceNonVacuousWitness
  refine
    ⟨permitTrace, witness.governedClaims, witness.permitEligibleClaims,
      Safety.exampleGovernanceTrace_consistent, witness.wellFormed,
      witness.governed_nonempty, witness.boundedDisposition,
      witness.eligible_nonempty, witness.eligible_subset,
      witness.permitEligible, witness.notRefusal,
      witness.notPermanentEscalation, witness.notDeadlock⟩

/-- Every non-sacrificed property in the worked agent's one-item sacrifice
index holds on the worked graph. -/
lemma workedNonSacrificedHold :
    NonSacrificedHold Safety.exampleGovernanceGraph
      [GovernanceProperty.Consistency] := by
  intro property hnot
  rcases Safety.exampleGovernanceGraph_allLegitimacyAxioms with
    ⟨_, hsolidarity, hmonotone, hstrategyproof⟩
  cases property <;> simp [propertyHolds] at hnot ⊢
  · exact hsolidarity
  · exact hmonotone
  · exact hstrategyproof
  · exact workedGraph_protocolNonVacuous

/-- Authority witness constructor for worked edges. -/
noncomputable def workedAuthorityWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hlevel : edge.sourceAuthorityLevel ≤ edge.targetAuthorityCeiling) :
    CrossAgentAuthorityLatticeWitness (workedSystemWithEdge edge) edge where
  endpoints := workedEndpointWitness edge hsource htarget
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

/-- Noninterference witness constructor for worked edges. -/
noncomputable def workedNoninterferenceWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hsep : edge.modifiesTargetKernel = false ∨
      edge.interferenceDeclared = true) :
    CrossAgentNoninterferenceWitness (workedSystemWithEdge edge) edge where
  endpoints := workedEndpointWitness edge hsource htarget
  source_invariant := by
    simpa [workedEndpointWitness, workedAgentA, Safety.KernelInvariant] using
      Safety.exampleGovernanceSemanticKernel
  target_invariant := by
    simpa [workedEndpointWitness, workedAgentB, Safety.KernelInvariant] using
      Safety.exampleGovernanceSemanticKernel
  target_preservation_step := by
    exact Safety.KernelStep.refl workedAgentB.kernel
  target_preserved := by
    exact
      Safety.kernelStep_preserves_invariant
        (Safety.KernelStep.refl workedAgentB.kernel)
        Safety.exampleGovernanceSemanticKernel
  target_preserved_by_step := by
    rfl
  separated_or_declared := hsep

/-- Escalation monotonicity witness constructor for worked edges. -/
noncomputable def workedEscalationWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hshape :
      edge.kind = CrossAgentEdgeKind.escalation →
        edge.escalationVerdictFloor + edge.escalationStrengthening ≤
          edge.escalationVerdictCeiling) :
    CrossAgentEscalationMonotonicityWitness
      (workedSystemWithEdge edge) edge where
  endpoints := workedEndpointWitness edge hsource htarget
  target_graph_monotone :=
    Safety.exampleGovernanceGraph_allLegitimacyAxioms.2.2.1
  escalation_shape := hshape

/-- Sacrifice-index witness constructor for worked edges. -/
noncomputable def workedSacrificeWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hcontradiction : edge.contradictorySacrifice = false)
    (hsourceDecl :
      ∀ property, property ∈ edge.sourceSacrifices →
        property ∈ workedAgentA.sacrificeIndex)
    (htargetDecl :
      ∀ property, property ∈ edge.targetSacrifices →
        property ∈ workedAgentB.sacrificeIndex) :
    CrossAgentSacrificeIndexWitness (workedSystemWithEdge edge) edge where
  endpoints := workedEndpointWitness edge hsource htarget
  no_contradiction := hcontradiction
  source_declared := by
    intro property hproperty
    exact hsourceDecl property hproperty
  target_declared := by
    intro property hproperty
    exact htargetDecl property hproperty
  source_protocol_boundary := by
    left
    simpa [workedEndpointWitness, workedAgentA] using workedNonSacrificedHold
  target_protocol_boundary := by
    left
    simpa [workedEndpointWitness, workedAgentB] using workedNonSacrificedHold

/-- Bridge witness constructor for worked edges. -/
noncomputable def workedBridgeWitness
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hsupported : CrossAgentBridgeStatusSupported edge.bridgeStatus) :
    CrossAgentBridgeWitness (workedSystemWithEdge edge) edge where
  endpoints := workedEndpointWitness edge hsource htarget
  bridge_supported := hsupported

/-- Shared good edge used by the compatible worked composition. -/
def compatibleDelegationEdge : CrossAgentEdge where
  sourceAgent := 0
  targetAgent := 1
  kind := CrossAgentEdgeKind.delegation
  sourceAuthorityLevel := 1
  targetAuthorityCeiling := 1
  modifiesTargetKernel := false
  interferenceDeclared := false
  escalationStrengthening := 0
  escalationVerdictFloor := 0
  escalationVerdictCeiling := 0
  sourceSacrifices := [GovernanceProperty.Consistency]
  targetSacrifices := [GovernanceProperty.Consistency]
  contradictorySacrifice := false
  bridgeStatus := CrossAgentBridgeStatus.clean

/-- Lift one worked edge authority witness to system compatibility. -/
noncomputable def workedAuthorityCompatible
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hlevel : edge.sourceAuthorityLevel ≤ edge.targetAuthorityCeiling) :
    AuthorityLatticeCompatible (workedSystemWithEdge edge) where
  nonempty_composition := by simp [workedSystemWithEdge]
  witnessed_edges := by
    intro checkedEdge hmem
    simp [workedSystemWithEdge] at hmem
    subst checkedEdge
    exact ⟨workedAuthorityWitness edge hsource htarget hlevel⟩

/-- Lift one worked edge noninterference witness to system compatibility. -/
noncomputable def workedNoninterferenceCompatible
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hsep : edge.modifiesTargetKernel = false ∨
      edge.interferenceDeclared = true) :
    NoninterferenceOrDeclared (workedSystemWithEdge edge) where
  nonempty_composition := by simp [workedSystemWithEdge]
  witnessed_edges := by
    intro checkedEdge hmem
    simp [workedSystemWithEdge] at hmem
    subst checkedEdge
    exact ⟨workedNoninterferenceWitness edge hsource htarget hsep⟩

/-- Lift one worked edge escalation witness to system compatibility. -/
noncomputable def workedMonotoneCompatible
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hshape :
      edge.kind = CrossAgentEdgeKind.escalation →
        edge.escalationVerdictFloor + edge.escalationStrengthening ≤
          edge.escalationVerdictCeiling) :
    MonotoneEscalationComposition (workedSystemWithEdge edge) where
  nonempty_composition := by simp [workedSystemWithEdge]
  witnessed_edges := by
    intro checkedEdge hmem
    simp [workedSystemWithEdge] at hmem
    subst checkedEdge
    exact ⟨workedEscalationWitness edge hsource htarget hshape⟩

/-- Lift one worked edge sacrifice witness to system compatibility. -/
noncomputable def workedSacrificeCompatible
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hcontradiction : edge.contradictorySacrifice = false)
    (hsourceDecl :
      ∀ property, property ∈ edge.sourceSacrifices →
        property ∈ workedAgentA.sacrificeIndex)
    (htargetDecl :
      ∀ property, property ∈ edge.targetSacrifices →
        property ∈ workedAgentB.sacrificeIndex) :
    CompatibleSacrificeIndices (workedSystemWithEdge edge) where
  nonempty_composition := by simp [workedSystemWithEdge]
  witnessed_edges := by
    intro checkedEdge hmem
    simp [workedSystemWithEdge] at hmem
    subst checkedEdge
    exact
      ⟨workedSacrificeWitness edge hsource htarget hcontradiction
        hsourceDecl htargetDecl⟩

/-- Lift one worked edge bridge witness to system compatibility. -/
noncomputable def workedBridgeCompatible
    (edge : CrossAgentEdge)
    (hsource : edge.sourceAgent = 0)
    (htarget : edge.targetAgent = 1)
    (hsupported : CrossAgentBridgeStatusSupported edge.bridgeStatus) :
    CrossAgentBridgePreservation (workedSystemWithEdge edge) where
  nonempty_composition := by simp [workedSystemWithEdge]
  witnessed_edges := by
    intro checkedEdge hmem
    simp [workedSystemWithEdge] at hmem
    subst checkedEdge
    exact ⟨workedBridgeWitness edge hsource htarget hsupported⟩

/-- Compatible two-agent composition: delegation is within authority,
read-only, sacrifice-compatible, and bridge-clean. -/
noncomputable def compatibleTwoAgentSystem : MultiAgentSystem :=
  workedSystemWithEdge compatibleDelegationEdge

lemma compatibleTwoAgentSystem_semantic :
    ∀ agent ∈ compatibleTwoAgentSystem.agents,
      IsSemanticLegitimacyKernel agent.kernel := by
  simpa [compatibleTwoAgentSystem, workedSystemWithEdge] using
    workedAgents_semantic

/-- Executable check that all five conditions hold on the compatible fixture. -/
lemma compatible_two_agent_all_conditions :
    AllMultiAgentCompatibilityConditions compatibleTwoAgentSystem := by
  exact
    ⟨workedAuthorityCompatible compatibleDelegationEdge rfl rfl (by decide),
      workedNoninterferenceCompatible compatibleDelegationEdge rfl rfl
        (Or.inl rfl),
      workedMonotoneCompatible compatibleDelegationEdge rfl rfl
        (by intro h; cases h),
      workedSacrificeCompatible compatibleDelegationEdge rfl rfl rfl
        (by intro property h; simpa [compatibleDelegationEdge, workedAgentA] using h)
        (by intro property h; simpa [compatibleDelegationEdge, workedAgentB] using h),
      workedBridgeCompatible compatibleDelegationEdge rfl rfl trivial⟩

/-- Executable mirror of the compatible worked fixture's five edge checks.
This is separated from `MultiAgentSystem` because the full system carries
dependent noncomputable semantic kernels, while the compatibility surface is a
finite computable edge audit. -/
def compatibleTwoAgentExecutableCheck : Bool :=
  let agentIds := [0, 1]
  let sourceIndex := [GovernanceProperty.Consistency]
  let targetIndex := [GovernanceProperty.Consistency]
  let edge := compatibleDelegationEdge
  (agentIds.contains edge.sourceAgent &&
      agentIds.contains edge.targetAgent &&
      decide (edge.sourceAuthorityLevel ≤ edge.targetAuthorityCeiling)) &&
    edge.noninterferenceOrDeclared &&
    edge.monotoneEscalationCompatible &&
    (!edge.contradictorySacrifice &&
      listSubsetByContains edge.sourceSacrifices sourceIndex &&
      listSubsetByContains edge.targetSacrifices targetIndex) &&
    edge.bridgePreserving

lemma compatible_two_agent_native_decide_check :
    compatibleTwoAgentExecutableCheck = true := by
  native_decide

/-- The compatible worked fixture realizes an anchored representative semantic
kernel. -/
lemma compatible_two_agent_anchored_representative_kernel_exists :
    ∃ representativeKernel : AnchoredRepresentativeKernel,
      IsSemanticLegitimacyKernel
        representativeKernel.kernel.toLegitimacyKernelData ∧
        AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel compatibleTwoAgentSystem := by
  exact
    ((anchored_representative_kernel_realized_iff_all_compatible
      compatibleTwoAgentSystem) compatibleTwoAgentSystem_semantic).2
      compatible_two_agent_all_conditions

/-- Incompatible escalation: strengthening at the source lowers the receiving
review surface below the required monotone ceiling. -/
def incompatibleEscalationEdge : CrossAgentEdge :=
  { compatibleDelegationEdge with
    kind := CrossAgentEdgeKind.escalation
    escalationStrengthening := 1
    escalationVerdictFloor := 1
    escalationVerdictCeiling := 1 }

noncomputable def incompatibleTwoAgentSystem : MultiAgentSystem :=
  workedSystemWithEdge incompatibleEscalationEdge

lemma incompatibleTwoAgentSystem_semantic :
    ∀ agent ∈ incompatibleTwoAgentSystem.agents,
      IsSemanticLegitimacyKernel agent.kernel := by
  simpa [incompatibleTwoAgentSystem, workedSystemWithEdge] using
    workedAgents_semantic

/-- Executable check that the incompatible fixture triggers the negative
theorem. -/
lemma incompatible_two_agent_failure_fires :
    (∃ cert : CrossAgentSacrificeCertificate incompatibleTwoAgentSystem,
        IsValidCrossAgentCertificate cert ∧
          CrossAgentCertificateFailureClause cert) := by
  obtain ⟨cert, hvalid, hfailure, _hkernelAware⟩ :=
    multi_agent_failure_emits_valid_certificate
      incompatibleTwoAgentSystem
      incompatibleTwoAgentSystem_semantic
      (by
        intro hall
        obtain ⟨witness⟩ :=
          hall.2.2.1.witnessed_edges incompatibleEscalationEdge (by
            simp [incompatibleTwoAgentSystem, workedSystemWithEdge])
        have hbad := witness.escalation_shape rfl
        norm_num [incompatibleEscalationEdge, compatibleDelegationEdge] at hbad)
  exact ⟨cert, hvalid, hfailure⟩

/-- Executable mirror that the incompatible worked fixture triggers the
monotone-escalation side of the failure theorem. -/
def incompatibleTwoAgentExecutableFailureCheck : Bool :=
  !incompatibleEscalationEdge.monotoneEscalationCompatible

lemma incompatible_two_agent_native_decide_failure_check :
    incompatibleTwoAgentExecutableFailureCheck = true := by
  native_decide

/-! ## Per-condition independence witnesses -/

def authorityFailureEdge : CrossAgentEdge :=
  { compatibleDelegationEdge with
    sourceAuthorityLevel := 2
    targetAuthorityCeiling := 1 }

def noninterferenceFailureEdge : CrossAgentEdge :=
  { compatibleDelegationEdge with
    kind := CrossAgentEdgeKind.sharedMemory
    modifiesTargetKernel := true
    interferenceDeclared := false }

def sacrificeFailureEdge : CrossAgentEdge :=
  { compatibleDelegationEdge with
    targetSacrifices := [GovernanceProperty.Monotonicity] }

def bridgeFailureEdge : CrossAgentEdge :=
  { compatibleDelegationEdge with
    kind := CrossAgentEdgeKind.toolAccess
    bridgeStatus := CrossAgentBridgeStatus.undeclared }

noncomputable def authorityFailureSystem : MultiAgentSystem :=
  workedSystemWithEdge authorityFailureEdge

noncomputable def noninterferenceFailureSystem : MultiAgentSystem :=
  workedSystemWithEdge noninterferenceFailureEdge

noncomputable def monotoneFailureSystem : MultiAgentSystem :=
  incompatibleTwoAgentSystem

noncomputable def sacrificeFailureSystem : MultiAgentSystem :=
  workedSystemWithEdge sacrificeFailureEdge

noncomputable def bridgeFailureSystem : MultiAgentSystem :=
  workedSystemWithEdge bridgeFailureEdge

lemma authority_failure_satisfies_other_four :
    NoninterferenceOrDeclared authorityFailureSystem ∧
      MonotoneEscalationComposition authorityFailureSystem ∧
      CompatibleSacrificeIndices authorityFailureSystem ∧
      CrossAgentBridgePreservation authorityFailureSystem := by
  exact
    ⟨workedNoninterferenceCompatible authorityFailureEdge rfl rfl
        (Or.inl rfl),
      workedMonotoneCompatible authorityFailureEdge rfl rfl
        (by intro h; cases h),
      workedSacrificeCompatible authorityFailureEdge rfl rfl rfl
        (by intro property h; simpa [authorityFailureEdge,
          compatibleDelegationEdge, workedAgentA] using h)
        (by intro property h; simpa [authorityFailureEdge,
          compatibleDelegationEdge, workedAgentB] using h),
      workedBridgeCompatible authorityFailureEdge rfl rfl trivial⟩

lemma noninterference_failure_satisfies_other_four :
    AuthorityLatticeCompatible noninterferenceFailureSystem ∧
      MonotoneEscalationComposition noninterferenceFailureSystem ∧
      CompatibleSacrificeIndices noninterferenceFailureSystem ∧
      CrossAgentBridgePreservation noninterferenceFailureSystem := by
  exact
    ⟨workedAuthorityCompatible noninterferenceFailureEdge rfl rfl
        (by decide),
      workedMonotoneCompatible noninterferenceFailureEdge rfl rfl
        (by intro h; cases h),
      workedSacrificeCompatible noninterferenceFailureEdge rfl rfl rfl
        (by intro property h; simpa [noninterferenceFailureEdge,
          compatibleDelegationEdge, workedAgentA] using h)
        (by intro property h; simpa [noninterferenceFailureEdge,
          compatibleDelegationEdge, workedAgentB] using h),
      workedBridgeCompatible noninterferenceFailureEdge rfl rfl trivial⟩

lemma monotone_failure_satisfies_other_four :
    AuthorityLatticeCompatible monotoneFailureSystem ∧
      NoninterferenceOrDeclared monotoneFailureSystem ∧
      CompatibleSacrificeIndices monotoneFailureSystem ∧
      CrossAgentBridgePreservation monotoneFailureSystem := by
  exact
    ⟨workedAuthorityCompatible incompatibleEscalationEdge rfl rfl
        (by decide),
      workedNoninterferenceCompatible incompatibleEscalationEdge rfl rfl
        (Or.inl rfl),
      workedSacrificeCompatible incompatibleEscalationEdge rfl rfl rfl
        (by intro property h; simpa [incompatibleEscalationEdge,
          compatibleDelegationEdge, workedAgentA] using h)
        (by intro property h; simpa [incompatibleEscalationEdge,
          compatibleDelegationEdge, workedAgentB] using h),
      workedBridgeCompatible incompatibleEscalationEdge rfl rfl trivial⟩

lemma sacrifice_failure_satisfies_other_four :
    AuthorityLatticeCompatible sacrificeFailureSystem ∧
      NoninterferenceOrDeclared sacrificeFailureSystem ∧
      MonotoneEscalationComposition sacrificeFailureSystem ∧
      CrossAgentBridgePreservation sacrificeFailureSystem := by
  exact
    ⟨workedAuthorityCompatible sacrificeFailureEdge rfl rfl
        (by decide),
      workedNoninterferenceCompatible sacrificeFailureEdge rfl rfl
        (Or.inl rfl),
      workedMonotoneCompatible sacrificeFailureEdge rfl rfl
        (by intro h; cases h),
      workedBridgeCompatible sacrificeFailureEdge rfl rfl trivial⟩

lemma bridge_failure_satisfies_other_four :
    AuthorityLatticeCompatible bridgeFailureSystem ∧
      NoninterferenceOrDeclared bridgeFailureSystem ∧
      MonotoneEscalationComposition bridgeFailureSystem ∧
      CompatibleSacrificeIndices bridgeFailureSystem := by
  exact
    ⟨workedAuthorityCompatible bridgeFailureEdge rfl rfl
        (by decide),
      workedNoninterferenceCompatible bridgeFailureEdge rfl rfl
        (Or.inl rfl),
      workedMonotoneCompatible bridgeFailureEdge rfl rfl
        (by intro h; cases h),
      workedSacrificeCompatible bridgeFailureEdge rfl rfl rfl
        (by intro property h; simpa [bridgeFailureEdge,
          compatibleDelegationEdge, workedAgentA] using h)
        (by intro property h; simpa [bridgeFailureEdge,
          compatibleDelegationEdge, workedAgentB] using h)⟩

private theorem workedSystem_semantic
    (edge : CrossAgentEdge) :
    ∀ agent ∈ (workedSystemWithEdge edge).agents,
      IsSemanticLegitimacyKernel agent.kernel := by
  simpa [workedSystemWithEdge] using workedAgents_semantic

lemma authority_failure_blocks_anchored_representative_kernel :
    ¬ ∃ representativeKernel : AnchoredRepresentativeKernel,
      IsSemanticLegitimacyKernel
        representativeKernel.kernel.toLegitimacyKernelData ∧
        AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel authorityFailureSystem := by
  intro hrepresentative
  have hall :=
    ((anchored_representative_kernel_realized_iff_all_compatible
      authorityFailureSystem)
      (workedSystem_semantic authorityFailureEdge)).1 hrepresentative
  have hnot : ¬ AuthorityLatticeCompatible authorityFailureSystem := by
    intro hcompat
    obtain ⟨witness⟩ :=
      hcompat.witnessed_edges authorityFailureEdge (by
        simp [authorityFailureSystem, workedSystemWithEdge])
    have hsource := witness.sourceLevel_projects
    have htarget := witness.targetCeiling_projects
    have horder := witness.project_monotone witness.authority_monotone
    simp [authorityFailureEdge, compatibleDelegationEdge] at hsource htarget
    rw [hsource, htarget] at horder
    omega
  exact hnot hall.1

lemma noninterference_failure_blocks_anchored_representative_kernel :
    ¬ ∃ representativeKernel : AnchoredRepresentativeKernel,
      IsSemanticLegitimacyKernel
        representativeKernel.kernel.toLegitimacyKernelData ∧
        AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel noninterferenceFailureSystem := by
  intro hrepresentative
  have hall :=
    ((anchored_representative_kernel_realized_iff_all_compatible
      noninterferenceFailureSystem)
      (workedSystem_semantic noninterferenceFailureEdge)).1 hrepresentative
  have hnot : ¬ NoninterferenceOrDeclared noninterferenceFailureSystem := by
    intro hcompat
    obtain ⟨witness⟩ :=
      hcompat.witnessed_edges noninterferenceFailureEdge (by
        simp [noninterferenceFailureSystem, workedSystemWithEdge])
    rcases witness.separated_or_declared with hsep | hdecl
    · simp [noninterferenceFailureEdge, compatibleDelegationEdge] at hsep
    · simp [noninterferenceFailureEdge, compatibleDelegationEdge] at hdecl
  exact hnot hall.2.1

lemma monotone_failure_blocks_anchored_representative_kernel :
    ¬ ∃ representativeKernel : AnchoredRepresentativeKernel,
      IsSemanticLegitimacyKernel
        representativeKernel.kernel.toLegitimacyKernelData ∧
        AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel monotoneFailureSystem := by
  intro hrepresentative
  have hall :=
    ((anchored_representative_kernel_realized_iff_all_compatible
      monotoneFailureSystem)
      incompatibleTwoAgentSystem_semantic).1 hrepresentative
  have hnot : ¬ MonotoneEscalationComposition monotoneFailureSystem := by
    intro hcompat
    obtain ⟨witness⟩ :=
      hcompat.witnessed_edges incompatibleEscalationEdge (by
        simp [monotoneFailureSystem, incompatibleTwoAgentSystem,
          workedSystemWithEdge])
    have hbad := witness.escalation_shape rfl
    norm_num [incompatibleEscalationEdge, compatibleDelegationEdge] at hbad
  exact hnot hall.2.2.1

lemma sacrifice_failure_blocks_anchored_representative_kernel :
    ¬ ∃ representativeKernel : AnchoredRepresentativeKernel,
      IsSemanticLegitimacyKernel
        representativeKernel.kernel.toLegitimacyKernelData ∧
        AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel sacrificeFailureSystem := by
  intro hrepresentative
  have hall :=
    ((anchored_representative_kernel_realized_iff_all_compatible
      sacrificeFailureSystem)
      (workedSystem_semantic sacrificeFailureEdge)).1 hrepresentative
  have hnot : ¬ CompatibleSacrificeIndices sacrificeFailureSystem := by
    intro hcompat
    obtain ⟨witness⟩ :=
      hcompat.witnessed_edges sacrificeFailureEdge (by
        simp [sacrificeFailureSystem, workedSystemWithEdge])
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
  exact hnot hall.2.2.2.1

lemma bridge_failure_blocks_anchored_representative_kernel :
    ¬ ∃ representativeKernel : AnchoredRepresentativeKernel,
      IsSemanticLegitimacyKernel
        representativeKernel.kernel.toLegitimacyKernelData ∧
        AnchoredRepresentativeRealizesMultiAgentSystem representativeKernel bridgeFailureSystem := by
  intro hrepresentative
  have hall :=
    ((anchored_representative_kernel_realized_iff_all_compatible
      bridgeFailureSystem)
      (workedSystem_semantic bridgeFailureEdge)).1 hrepresentative
  have hnot : ¬ CrossAgentBridgePreservation bridgeFailureSystem := by
    intro hcompat
    obtain ⟨witness⟩ :=
      hcompat.witnessed_edges bridgeFailureEdge (by
        simp [bridgeFailureSystem, workedSystemWithEdge])
    simpa [bridgeFailureEdge, compatibleDelegationEdge,
      CrossAgentBridgeStatusSupported] using witness.bridge_supported
  exact hnot hall.2.2.2.2

end Legitimacy
