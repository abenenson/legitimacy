/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.PeerRelativeClass.Predicates
import Legitimacy.Kernel.Examples

/-!
# Non-peer-relative escape trichotomy

Avoiding every reachable peer-relative stage does not recover substantive
legitimacy for free. A governing pipeline must instead collapse allocation,
lose concurrent-claim feasibility, or leave the runtime legitimacy kernel.
-/

set_option autoImplicit false

namespace Legitimacy

structure Pipeline where
  n : Nat
  sys : GovernedSystem n
  kernel : LegitimacyKernelData sys
  stages : GovernanceGraph
  admitted : List ClaimQ → Prop
  allocation : List ClaimQ → ClaimantId → Option BinaryDecision

abbrev IsPeerRelativeStage : GovernanceNodeFn → Prop :=
  IsPeerRelativeNode

def ReachableInPipeline (pipeline : Pipeline) (stage : GovernanceNodeFn) : Prop :=
  List.Mem stage pipeline.stages

def ConcurrentClaims (claims : List ClaimQ) : Prop :=
  ClaimsDistinct claims ∧ 2 ≤ claims.length

def HandlesProfile (pipeline : Pipeline) (claims : List ClaimQ) : Prop :=
  pipeline.admitted claims ∧
    ∀ c ∈ claims, ∃ d, pipeline.allocation claims c.id = some d

def SubstantiveAllocation (pipeline : Pipeline) : Prop :=
  ∃ (claims : List ClaimQ) (c : ClaimQ),
    pipeline.admitted claims ∧ c ∈ claims ∧
      pipeline.allocation claims c.id = some BinaryDecision.Permit

def SubstantiveAllocationCollapse (pipeline : Pipeline) : Prop :=
  ¬ SubstantiveAllocation pipeline

def PipelineFeasible (pipeline : Pipeline) : Prop :=
  ∃ claims : List ClaimQ,
    ConcurrentClaims claims ∧ HandlesProfile pipeline claims

def PipelineInfeasible (pipeline : Pipeline) : Prop :=
  ¬ PipelineFeasible pipeline

def IsLegitimacyKernelEscape (pipeline : Pipeline) : Prop :=
  (¬ ∃ stage, IsPeerRelativeStage stage ∧
    ReachableInPipeline pipeline stage) ∧
  SubstantiveAllocation pipeline ∧
  PipelineFeasible pipeline ∧
  IsLegitimacyKernel pipeline.kernel

/-- The runtime graph exposed by the pipeline is the graph published by the
governed system it claims to instantiate. -/
def PublishedPipelineSpecification (pipeline : Pipeline) : Prop :=
  pipeline.stages = pipeline.sys.graph

/-- The activation gate has fired on a concurrent profile and produced at least
one permit decision, rather than remaining a paper-only or deny-only artifact. -/
def ActivationGateFires (pipeline : Pipeline) : Prop :=
  ∃ (claims : List ClaimQ) (c : ClaimQ),
    ConcurrentClaims claims ∧
    HandlesProfile pipeline claims ∧
    c ∈ claims ∧
    pipeline.allocation claims c.id = some BinaryDecision.Permit

/-- Operational coverage required of a governing runtime: once the pipeline is
substantive, feasible, and inside the kernel, some reachable stage must expose
the peer-relative decision surface. -/
def PeerRelativeCoverageObligation (pipeline : Pipeline) : Prop :=
  SubstantiveAllocation pipeline →
  PipelineFeasible pipeline →
  IsLegitimacyKernel pipeline.kernel →
  ∃ stage, IsPeerRelativeStage stage ∧
    ReachableInPipeline pipeline stage

/-- Operational governance is an activation-and-coverage contract, not the
negation of the escape predicate: the runtime has a published specification, its
activation gate fires on a substantive concurrent profile, kernel obligations
hold, and its coverage obligation exposes a peer-relative stage for every
substantive feasible kernel run. -/
def Pipeline.governs (pipeline : Pipeline) : Prop :=
  PublishedPipelineSpecification pipeline ∧
  ActivationGateFires pipeline ∧
  IsLegitimacyKernel pipeline.kernel ∧
  PeerRelativeCoverageObligation pipeline

theorem ActivationGateFires.substantive
    {pipeline : Pipeline} (hactivation : ActivationGateFires pipeline) :
    SubstantiveAllocation pipeline := by
  rcases hactivation with
    ⟨claims, c, _hconcurrent, hhandled, hmem, hpermit⟩
  exact ⟨claims, c, hhandled.1, hmem, hpermit⟩

theorem ActivationGateFires.feasible
    {pipeline : Pipeline} (hactivation : ActivationGateFires pipeline) :
    PipelineFeasible pipeline := by
  rcases hactivation with
    ⟨claims, _c, hconcurrent, hhandled, _hmem, _hpermit⟩
  exact ⟨claims, hconcurrent, hhandled⟩

theorem Pipeline.governs_not_escape
    {pipeline : Pipeline} (hgov : pipeline.governs) :
    ¬ IsLegitimacyKernelEscape pipeline := by
  rintro ⟨hnonPR, hsubstantive, hfeasible, hkernel⟩
  exact hnonPR (hgov.2.2.2 hsubstantive hfeasible hkernel)

/-- A governing pipeline with no reachable peer-relative stage must collapse
allocation, lose feasibility, or leave the runtime legitimacy kernel. -/
theorem non_peer_relative_collapse_or_infeasible_or_exits_kernel
    (pipeline : Pipeline) (hgov : pipeline.governs)
    (hnonPR : ¬ ∃ stage, IsPeerRelativeStage stage ∧
      ReachableInPipeline pipeline stage) :
    SubstantiveAllocationCollapse pipeline ∨
    PipelineInfeasible pipeline ∨
    ¬ IsLegitimacyKernel pipeline.kernel := by
  classical
  by_cases hcollapse : SubstantiveAllocationCollapse pipeline
  · exact Or.inl hcollapse
  · by_cases hinfeasible : PipelineInfeasible pipeline
    · exact Or.inr (Or.inl hinfeasible)
    · refine Or.inr (Or.inr ?_)
      intro hkernel
      exact hnonPR
        (hgov.2.2.2 (not_not.mp hcollapse) (not_not.mp hinfeasible)
          hkernel)

def escapeClaimA : ClaimQ := ⟨0, 1, by norm_num, []⟩
def escapeClaimB : ClaimQ := ⟨1, 1, by norm_num, []⟩

def escapeConcurrentClaims : List ClaimQ :=
  [escapeClaimA, escapeClaimB]

lemma escapeConcurrentClaims_concurrent :
    ConcurrentClaims escapeConcurrentClaims := by
  unfold ConcurrentClaims ClaimsDistinct escapeConcurrentClaims escapeClaimA
    escapeClaimB
  simp

def alwaysDenyStage : GovernanceNodeFn := fun _ _ => BinaryDecision.Deny
def alwaysPermitStage : GovernanceNodeFn := fun _ _ => BinaryDecision.Permit

lemma alwaysDenyStage_not_peerRelative :
    ¬ IsPeerRelativeStage alwaysDenyStage := by
  intro h
  rcases h with
    ⟨_claims, _claims', _k, _hne, _hin, _hin', _hdist, _hdist',
      _hsame, hdiff⟩
  simp [alwaysDenyStage] at hdiff

lemma alwaysPermitStage_not_peerRelative :
    ¬ IsPeerRelativeStage alwaysPermitStage := by
  intro h
  rcases h with
    ⟨_claims, _claims', _k, _hne, _hin, _hin', _hdist, _hdist',
      _hsame, hdiff⟩
  simp [alwaysPermitStage] at hdiff

private lemma no_peer_relative_singleton
    {stage : GovernanceNodeFn} (hstage : ¬ IsPeerRelativeStage stage) :
    ¬ ∃ reached, IsPeerRelativeStage reached ∧ List.Mem reached [stage] := by
  rintro ⟨_reached, hpr, hmem⟩
  cases hmem with
  | head =>
      exact hstage hpr
  | tail _ htail =>
      cases htail

/-! ## Witness 1: collapse -/

noncomputable def collapseWitnessPipeline : Pipeline where
  n := 1
  sys := permitSystem
  kernel := permitKernel.toLegitimacyKernelData
  stages := [alwaysDenyStage]
  admitted := fun _ => True
  allocation := fun _ _ => some BinaryDecision.Deny

theorem collapseWitnessPipeline_non_peer_relative :
    ¬ ∃ stage, IsPeerRelativeStage stage ∧
      ReachableInPipeline collapseWitnessPipeline stage := by
  simpa [ReachableInPipeline, collapseWitnessPipeline]
    using no_peer_relative_singleton alwaysDenyStage_not_peerRelative

theorem collapseWitnessPipeline_reachable_non_peer_relative :
    ∃ stage, ReachableInPipeline collapseWitnessPipeline stage ∧
      ¬ IsPeerRelativeStage stage := by
  exact ⟨alwaysDenyStage, List.Mem.head _,
    alwaysDenyStage_not_peerRelative⟩

theorem collapseWitnessPipeline_collapse :
    SubstantiveAllocationCollapse collapseWitnessPipeline := by
  rintro ⟨_claims, _c, _hadmit, _hmem, hpermit⟩
  simp [collapseWitnessPipeline] at hpermit

theorem collapseWitnessPipeline_not_governs :
    ¬ collapseWitnessPipeline.governs := by
  intro hgov
  exact collapseWitnessPipeline_collapse
    (ActivationGateFires.substantive hgov.2.1)

/-! ## Witness 2: infeasibility -/

def singletonOnlyAllocation
    (claims : List ClaimQ) (_k : ClaimantId) : Option BinaryDecision :=
  if claims.length ≤ 1 then some BinaryDecision.Permit else none

noncomputable def singletonOnlyPipeline : Pipeline where
  n := 1
  sys := permitSystem
  kernel := permitKernel.toLegitimacyKernelData
  stages := [alwaysPermitStage]
  admitted := fun _ => True
  allocation := singletonOnlyAllocation

theorem singletonOnlyPipeline_non_peer_relative :
    ¬ ∃ stage, IsPeerRelativeStage stage ∧
      ReachableInPipeline singletonOnlyPipeline stage := by
  simpa [ReachableInPipeline, singletonOnlyPipeline]
    using no_peer_relative_singleton alwaysPermitStage_not_peerRelative

theorem singletonOnlyPipeline_reachable_non_peer_relative :
    ∃ stage, ReachableInPipeline singletonOnlyPipeline stage ∧
      ¬ IsPeerRelativeStage stage := by
  exact ⟨alwaysPermitStage, List.Mem.head _,
    alwaysPermitStage_not_peerRelative⟩

theorem singletonOnlyAllocation_undefined_on_concurrent
    {claims : List ClaimQ} (hclaims : ConcurrentClaims claims)
    (k : ClaimantId) :
    singletonOnlyAllocation claims k = none := by
  have hlen : 2 ≤ claims.length := hclaims.2
  have hnot : ¬ claims.length ≤ 1 := by
    omega
  simp [singletonOnlyAllocation, hnot]

theorem singletonOnlyPipeline_infeasible :
    PipelineInfeasible singletonOnlyPipeline := by
  rintro ⟨claims, hconcurrent, _hadmit, hhandled⟩
  cases claims with
  | nil =>
      simp [ConcurrentClaims] at hconcurrent
  | cons c cs =>
      have hmem : c ∈ c :: cs := by simp
      rcases hhandled c hmem with ⟨d, hd⟩
      have hundef :=
        singletonOnlyAllocation_undefined_on_concurrent hconcurrent c.id
      change singletonOnlyAllocation (c :: cs) c.id = some d at hd
      rw [hundef] at hd
      cases hd

theorem singletonOnlyPipeline_not_governs :
    ¬ singletonOnlyPipeline.governs := by
  intro hgov
  exact singletonOnlyPipeline_infeasible
    (ActivationGateFires.feasible hgov.2.1)

theorem admit_only_singleton_rule_fails_feasibility_at_multi_claim_profiles :
    PipelineInfeasible singletonOnlyPipeline :=
  singletonOnlyPipeline_infeasible

/-! ## Witness 3: kernel exit -/

noncomputable def hiddenAuthorityExitPipeline : Pipeline where
  n := 1
  sys := permitSystem
  kernel := kernelDataWithoutObservable
  stages := [alwaysPermitStage]
  admitted := fun _ => True
  allocation := fun _ _ => some BinaryDecision.Permit

theorem hiddenAuthorityExitPipeline_non_peer_relative :
    ¬ ∃ stage, IsPeerRelativeStage stage ∧
      ReachableInPipeline hiddenAuthorityExitPipeline stage := by
  simpa [ReachableInPipeline, hiddenAuthorityExitPipeline]
    using no_peer_relative_singleton alwaysPermitStage_not_peerRelative

theorem hiddenAuthorityExitPipeline_reachable_non_peer_relative :
    ∃ stage, ReachableInPipeline hiddenAuthorityExitPipeline stage ∧
      ¬ IsPeerRelativeStage stage := by
  exact ⟨alwaysPermitStage, List.Mem.head _,
    alwaysPermitStage_not_peerRelative⟩

theorem hiddenAuthorityExitPipeline_substantive :
    SubstantiveAllocation hiddenAuthorityExitPipeline := by
  refine ⟨escapeConcurrentClaims, escapeClaimA, trivial, ?_, ?_⟩
  · simp [escapeConcurrentClaims]
  · simp [hiddenAuthorityExitPipeline]

theorem hiddenAuthorityExitPipeline_feasible :
    PipelineFeasible hiddenAuthorityExitPipeline := by
  refine ⟨escapeConcurrentClaims, escapeConcurrentClaims_concurrent, ?_, ?_⟩
  · trivial
  · intro _c _hmem
    exact ⟨BinaryDecision.Permit, by simp [hiddenAuthorityExitPipeline]⟩

theorem hiddenAuthorityExitPipeline_exits_kernel :
    ¬ IsLegitimacyKernel hiddenAuthorityExitPipeline.kernel := by
  intro hkernel
  exact permit_constantFalse_not_observable hkernel.observable

theorem hiddenAuthorityExitPipeline_not_governs :
    ¬ hiddenAuthorityExitPipeline.governs := by
  intro hgov
  exact hiddenAuthorityExitPipeline_exits_kernel hgov.2.2.1

/-! ## Permanent-escalation non-vacuity countermodel -/

/-- An honest always-permit trace meets the non-vacuity liveness contract. -/
lemma honest_permit_all_trace_satisfies_nonvacuous :
    NonVacuous permitGraph permitTrace :=
  permit_nonvacuous

def alwaysPermitGraph : GovernanceGraph := [alwaysPermitStage]

def escalatingPermitGraphTrace : GovernanceTrace :=
  fun _ => (permitClaim, some GovernanceOutcome.escalate)

lemma escalatingPermitGraphTrace_consistent :
    TraceConsistentWithGraph escalatingPermitGraphTrace alwaysPermitGraph := by
  intro _t
  simp [TraceEventConsistentWithGraph, escalatingPermitGraphTrace,
    alwaysPermitGraph]

def permanentlyEscalatingPermitSystem : GovernedSystem 1 where
  graph := alwaysPermitGraph
  state := permitState
  trace := escalatingPermitGraphTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := escalatingPermitGraphTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 alwaysPermitGraph

noncomputable def permanentlyEscalatingPermitKernelData :
    LegitimacyKernelData permanentlyEscalatingPermitSystem :=
  replayStateKernelData permanentlyEscalatingPermitSystem

noncomputable def permanentlyEscalatingPermitPipeline : Pipeline where
  n := 1
  sys := permanentlyEscalatingPermitSystem
  kernel := permanentlyEscalatingPermitKernelData
  stages := [alwaysPermitStage]
  admitted := fun _ => True
  allocation := fun _ _ => some BinaryDecision.Permit

lemma escalatingPermitGraphTrace_permanentEscalation :
    PermanentEscalation escalatingPermitGraphTrace := by
  intro _t
  rfl

theorem permanentlyEscalatingPermitPipeline_nonvacuity_failure :
    ¬ NonVacuous permanentlyEscalatingPermitSystem.graph
      permanentlyEscalatingPermitSystem.trace := by
  exact permanentEscalation_not_nonvacuous
    escalatingPermitGraphTrace_permanentEscalation

theorem permanently_escalating_permit_graph_fails_nonvacuity :
    ¬ IsLegitimacyKernel permanentlyEscalatingPermitPipeline.kernel := by
  intro hkernel
  exact permanentlyEscalatingPermitPipeline_nonvacuity_failure
    hkernel.nonVacuous.1

/-! ## Global negative result -/

theorem no_non_peer_relative_pipeline_substantive_feasible_and_kernel
    (pipeline : Pipeline) (hgov : pipeline.governs)
    (hnonPR : ¬ ∃ stage, IsPeerRelativeStage stage ∧
      ReachableInPipeline pipeline stage) :
    ¬ (SubstantiveAllocation pipeline ∧
      PipelineFeasible pipeline ∧
      IsLegitimacyKernel pipeline.kernel) := by
  intro htriple
  exact Pipeline.governs_not_escape hgov
    ⟨hnonPR, htriple.1, htriple.2.1, htriple.2.2⟩

theorem collapseWitnessPipeline_no_escape_but_not_governs :
    ¬ IsLegitimacyKernelEscape collapseWitnessPipeline ∧
    ¬ collapseWitnessPipeline.governs := by
  constructor
  · intro hescape
    exact collapseWitnessPipeline_collapse hescape.2.1
  · exact collapseWitnessPipeline_not_governs

theorem non_governing_collapse_witness_has_escape_branch :
    ¬ collapseWitnessPipeline.governs ∧
    (SubstantiveAllocationCollapse collapseWitnessPipeline ∨
      PipelineInfeasible collapseWitnessPipeline ∨
      ¬ IsLegitimacyKernel collapseWitnessPipeline.kernel) := by
  exact ⟨collapseWitnessPipeline_not_governs,
    Or.inl collapseWitnessPipeline_collapse⟩

theorem no_non_peer_relative_escape_countermodel :
    ¬ ∃ pipeline : Pipeline,
      pipeline.governs ∧
      (¬ ∃ stage, IsPeerRelativeStage stage ∧
        ReachableInPipeline pipeline stage) ∧
      SubstantiveAllocation pipeline ∧
      PipelineFeasible pipeline ∧
      IsLegitimacyKernel pipeline.kernel := by
  rintro ⟨pipeline, hgov, hnonPR, hsub, hfeas, hkernel⟩
  exact no_non_peer_relative_pipeline_substantive_feasible_and_kernel
    pipeline hgov hnonPR ⟨hsub, hfeas, hkernel⟩

end Legitimacy
