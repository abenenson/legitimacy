/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.ASIBridge.FamilyAlignment

/-!
# Legitimacy.Spectral.ASIBridge.DenialBearing

Denial-bearing runtime toy for the complete-rank native ASI bridge.
-/

set_option autoImplicit false

namespace Legitimacy

namespace ASIBridge

/-! ## Denial-bearing K5 complete-rank toy -/

/-- Claim-presence gate: permits claimants represented in the submitted profile
and denies absent claimants. This gives a real denial branch while preserving the
complete-rank ASI carrier on the canonical K5 profile. -/
def claimPresenceNode : GovernanceNodeFn :=
  fun claims claimant =>
    if InClaims claimant claims then BinaryDecision.Permit else BinaryDecision.Deny

/-- Five-stage denial-bearing governance graph aligned to the K5 complete-rank
spectral carrier. It is not the inert all-permit substrate: absent claimants are
denied by the first stage. -/
def claimPresenceK5GovernanceGraph : GovernanceGraph :=
  [ claimPresenceNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  , Safety.examplePermitNode
  ]

lemma claimPresenceK5GovernanceGraph_decides
    (claims : List ClaimQ) (claimant : ClaimantId) :
    graphDecide claimPresenceK5GovernanceGraph claims claimant =
      if InClaims claimant claims then BinaryDecision.Permit else BinaryDecision.Deny := by
  by_cases h : InClaims claimant claims <;>
    simp [claimPresenceK5GovernanceGraph, claimPresenceNode,
      Safety.examplePermitNode, graphDecide, h]

/-- Concrete denial branch for the K5 claim-presence graph. -/
lemma claimPresenceK5GovernanceGraph_denies_empty :
    graphDecide claimPresenceK5GovernanceGraph [] 0 = BinaryDecision.Deny := by
  simp [claimPresenceK5GovernanceGraph_decides, InClaims]

private lemma claimPresenceK5_inClaims_scaled_of_inClaims
    {claims : List ClaimQ} {j : ClaimantId} {α : ℚ} (hα : 0 < α) :
    InClaims j claims →
      InClaims j (claims.map fun c => c.scaleStrength α hα) := by
  intro hj
  rcases hj with ⟨c, hmem, hid⟩
  exact ⟨c.scaleStrength α hα, List.mem_map_of_mem hmem, by simpa using hid⟩

private lemma claimPresenceK5_inClaims_strengthenClaim_of_inClaims
    {claims : List ClaimQ} {j k : ClaimantId} {s' : ℚ} {hs' : 0 < s'} :
    InClaims j claims → InClaims j (strengthenClaim k s' hs' claims) := by
  intro hj
  induction claims generalizing j with
  | nil =>
      rcases hj with ⟨_, hmem, _⟩
      simp at hmem
  | cons c cs ih =>
      by_cases hck : c.id = k
      · simp [strengthenClaim, hck]
        rcases hj with ⟨c', hc'mem, hc'id⟩
        cases hc'mem with
        | head =>
            exact ⟨⟨k, s', hs', c.metadata⟩, by simp, hck.symm.trans hc'id⟩
        | tail _ htail =>
            exact ⟨c', List.Mem.tail _ htail, hc'id⟩
      · simp [strengthenClaim, hck]
        rcases hj with ⟨c', hc'mem, hc'id⟩
        cases hc'mem with
        | head =>
            exact ⟨c, by simp, hc'id⟩
        | tail _ htail =>
            rcases ih ⟨c', htail, hc'id⟩ with ⟨c'', hm, hid⟩
            exact ⟨c'', List.Mem.tail _ hm, hid⟩

lemma claimPresenceK5GovernanceGraph_allLegitimacyAxioms :
    AllLegitimacyAxioms claimPresenceK5GovernanceGraph := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro claims k j hk hj hkj hdist hdeny
    simp [claimPresenceK5GovernanceGraph_decides, hk] at hdeny
  · intro claims α hα j hj
    have hj_scaled : InClaims j (claims.map fun c => c.scaleStrength α hα) :=
      claimPresenceK5_inClaims_scaled_of_inClaims hα hj
    simp [claimPresenceK5GovernanceGraph_decides, hj, hj_scaled]
  · intro claims k s' hs' j hk hdist hle hperm
    by_cases hj : InClaims j claims
    · have hj' : InClaims j (strengthenClaim k s' hs' claims) :=
        claimPresenceK5_inClaims_strengthenClaim_of_inClaims hj
      simp [claimPresenceK5GovernanceGraph_decides, hj']
    · simp [claimPresenceK5GovernanceGraph_decides, hj] at hperm
  · intro claims k s_r hs_r hk hdist hperm
    simp [claimPresenceK5GovernanceGraph_decides, hk]

lemma claimPresenceK5GovernanceTrace_consistent :
    TraceConsistentWithGraph permitTrace claimPresenceK5GovernanceGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, permitTrace]
  exact ⟨[permitClaim], by simp, by
    rw [claimPresenceK5GovernanceGraph_decides]
    simp [permitClaim, InClaims]⟩

def claimPresenceK5GovernedSystem : GovernedSystem 1 where
  graph := claimPresenceK5GovernanceGraph
  state := permitState
  trace := permitTrace
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := claimPresenceK5GovernanceTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 claimPresenceK5GovernanceGraph

private def claimPresenceK5LayerEval : LayerEval 0 where
  eval := fun L => nomatch L

def claimPresenceK5GovernanceNonVacuousWitness :
    NonVacuousWitness claimPresenceK5GovernanceGraph permitTrace where
  wellFormed := by
    simp [claimPresenceK5GovernanceGraph, WellFormed]
  governedClaims := [permitClaim]
  governed_nonempty := by
    simp
  boundedDisposition := permitTrace_bounded
  permitEligibleClaims := [permitClaim]
  eligible_nonempty := by
    simp
  eligible_subset := by
    intro c hc
    simpa using hc
  permitEligible := permitTrace_permitEligible
  notRefusal := permitTrace_notRefusal
  notPermanentEscalation := permitTrace_notPermanentEscalation
  notDeadlock := permitTrace_notDeadlock

lemma claimPresenceK5Governance_nonvacuous :
    NonVacuous claimPresenceK5GovernanceGraph permitTrace :=
  ⟨claimPresenceK5GovernanceNonVacuousWitness⟩

noncomputable def claimPresenceK5KernelData :
    LegitimacyKernelData claimPresenceK5GovernedSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification claimPresenceK5GovernedSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent claimPresenceK5GovernedSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer claimPresenceK5GovernedSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer claimPresenceK5GovernedSystem
  answer_consistent := state_answer_consistent claimPresenceK5GovernedSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := uniK5
  spectralSignal := sig5
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange sig5
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := claimPresenceK5LayerEval
  overrideOvs := []

@[reducible]
noncomputable def claimPresenceK5RuntimeKernel :
    IsLegitimacyKernel claimPresenceK5KernelData where
  certifiable :=
    graphReplayCertification_certifiable claimPresenceK5GovernedSystem.graph
  observable := state_id_observable claimPresenceK5GovernedSystem
  corrigible :=
    kernelCorrigible_zero _ permit_corrigible (by intro a; rfl)
  compositionalSafety :=
    LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
      (noEdge_causal_soundness 1 (allGoverned 1))
  nonVacuous :=
    LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
      claimPresenceK5Governance_nonvacuous

lemma claimPresenceK5GovernanceGraph_canonical_permits
    (i : Fin claimPresenceK5GovernanceGraph.weightedSize) :
    graphDecide claimPresenceK5GovernanceGraph
        claimPresenceK5GovernanceGraph.profileClaims i.val =
      BinaryDecision.Permit := by
  rw [claimPresenceK5GovernanceGraph_decides]
  simp [GovernanceGraph.profileClaims]
  refine ⟨⟨i.val, i.val + 1, by exact_mod_cast Nat.succ_pos i.val, []⟩, ?_, rfl⟩
  simp [claimPresenceK5GovernanceGraph, GovernanceGraph.weightedSize]

theorem claimPresenceK5KernelData_spectralCarrierRepresentsGraph :
    SpectralCarrierRepresentsGraph claimPresenceK5GovernedSystem.graph
      claimPresenceK5KernelData.spectralGraph
      claimPresenceK5KernelData.spectralSignal where
  claimantProjects := by
    intro i
    refine ⟨⟨i.val, i.val + 1, by exact_mod_cast Nat.succ_pos i.val, []⟩, ?_, rfl⟩
    simp [GovernanceGraph.profileClaims]
  graphSize := by
    simp [claimPresenceK5GovernedSystem, claimPresenceK5GovernanceGraph,
      GovernanceGraph.weightedSize]
  canonicalProfileRecovery := by
    intro representative _hsize hclass i
    have hspectral :
        ∀ i : Fin claimPresenceK5GovernedSystem.graph.weightedSize,
          spectralCarrierDecision uniK5 sig5 i = BinaryDecision.Permit := by
      native_decide
    calc
      spectralCarrierDecision uniK5 sig5 i = BinaryDecision.Permit :=
        hspectral i
      _ = graphDecide claimPresenceK5GovernedSystem.graph
          claimPresenceK5GovernedSystem.graph.profileClaims i.val :=
        (claimPresenceK5GovernanceGraph_canonical_permits i).symm
      _ = graphDecide representative representative.profileClaims i.val :=
        (hclass.2 i).symm
  peerSurfacePositiveCV := by
    intro pref tail _hsurface
    change 0 < uniK5.cv sig5
    rw [fiveNode_cv_values.1]
    norm_num

theorem claimPresenceK5_completeRankASISpectralSignatureN :
    CompleteRankASISpectralSignatureN 4 80
      (GovGraph.rgTrajectory uniK5 sig5 80 3) uniK5 sig5 := by
  refine ⟨?_, uniK5_completeRankASISpectralSignatureN_toy.2⟩
  exact ASISpectralSignatureN_five_of_ASISpectralSignature
    (by
      simpa using
        (concrete_iterated_RG_n5_universality 80 (by norm_num)).1)

/-- Native ASI bridge over a denial-bearing runtime graph. The runtime graph has
a real denial branch, while the strengthened complete-rank signature supplies
the kernel spectral witness for its aligned K5 carrier. -/
theorem claimPresenceK5_completeRank_native_asi_signature_kernelInvariant :
    Safety.KernelInvariant claimPresenceK5KernelData := by
  let target : ℚ × ℚ := GovGraph.rgTrajectory uniK5 sig5 80 3
  have hcomplete :
      CompleteRankASISpectralSignatureN 4 80 target uniK5 sig5 := by
    simpa [target] using claimPresenceK5_completeRankASISpectralSignatureN
  have hlift :
      SignatureToKernelSpectral 80 target claimPresenceK5KernelData
        uniK5 sig5 3 := by
    intro hasiGate _htargetGate
    have hcompleteGate :
        CompleteRankASISpectralSignatureN 4 80 target uniK5 sig5 :=
      ⟨hasiGate, hcomplete.2⟩
    change SpectralWellConnected uniK5 sig5 (by norm_num : 2 ≤ 5)
    exact
      CompleteRankASISpectralSignatureN.spectralWellConnected
        (n := 4) (δ := 80) (target := target)
        (G := uniK5) (s := sig5) (by norm_num : 2 ≤ 4)
        hcompleteGate
  let ctx : BridgeContext (n := 4) claimPresenceK5GovernedSystem :=
    { δ := 80
      target := target
      D := claimPresenceK5KernelData
      G := uniK5
      s := sig5
      depth := 3 }
  have htargetCtx :
      ctx.target = GovGraph.rgTrajectory ctx.G ctx.s ctx.δ ctx.depth := by
    change target = GovGraph.rgTrajectory uniK5 sig5 80 3
    rfl
  exact
    native_asi_signature_kernelInvariant
      ctx hcomplete.1 htargetCtx claimPresenceK5RuntimeKernel
      claimPresenceK5GovernanceGraph_allLegitimacyAxioms
      claimPresenceK5KernelData_spectralCarrierRepresentsGraph hlift

end ASIBridge

end Legitimacy
