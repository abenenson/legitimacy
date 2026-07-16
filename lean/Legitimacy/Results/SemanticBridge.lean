/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Examples
import Legitimacy.Results.Impossibility
import Legitimacy.Results.NonPeerRelative

/-!
# Legitimacy.Results.SemanticBridge

Semantic bridge theorem for the strengthened kernel target.

The original five kernel axioms are runtime obligations. They do not, by
themselves, assert the graph-diagnostic axioms or the spectral
well-connected predicate. `IsSemanticLegitimacyKernel` strengthens that target
with an explicit semantic bridge contract, and the theorem below gives the
exact iff decomposition into runtime, diagnostic, and spectral layers.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Unfolded semantic-bridge characterization of the strengthened kernel
target: it is precisely the five runtime kernel axioms, with kernel action
boundedness folded into corrigibility, together with the graph-diagnostic
axioms, the carrier-grounding witness, and the spectral well-connected witness
carried by the kernel datum. -/
theorem semanticKernel_iff_runtime_diagnostic_spectral_layers_unfolded
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) :
    IsSemanticLegitimacyKernel D ↔
      Certifiable D.certification ∧
      GovernanceObservable D.answer D.observeAnswer D.observe ∧
      KernelCorrigible D ∧
      CausalSoundness sys.dag sys.governed ∧
      NonVacuous sys.graph sys.trace ∧
      AllLegitimacyAxioms sys.graph ∧
      SpectralCarrierRepresentsGraph sys.graph D.spectralGraph
        D.spectralSignal ∧
      SpectralWellConnected D.spectralGraph D.spectralSignal
        sys.graph.weightedSize_atLeastTwo := by
  rw [isSemanticLegitimacyKernel_iff_runtime_and_bridge, KernelSemanticBridge]
  constructor
  · rintro ⟨hruntime, hdiag, hrep, hspec⟩
    exact ⟨hruntime.certifiable,
      hruntime.observable,
      hruntime.corrigible,
      by
        simpa [LegitimacyKernelData.KernelCausalSoundness] using
          hruntime.compositionalSafety,
      hruntime.nonVacuous.1,
      hdiag,
      hrep,
      hspec⟩
  · rintro ⟨hcert, hobs, hcorr, hsafe, hnv, hdiag, hrep, hspec⟩
    exact ⟨({ certifiable := hcert
              observable := hobs
              corrigible := hcorr
              compositionalSafety :=
                LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
                  hsafe
              nonVacuous :=
                LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
                  hnv } : IsLegitimacyKernel D),
      hdiag,
      hrep,
      hspec⟩

/-- Structural-unfold compatibility name for runtime/diagnostic/spectral analysis. -/
theorem semanticKernel_iff_runtime_diagnostic_spectral_layers
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) :
    IsSemanticLegitimacyKernel D ↔
      Certifiable D.certification ∧
      GovernanceObservable D.answer D.observeAnswer D.observe ∧
      KernelCorrigible D ∧
      CausalSoundness sys.dag sys.governed ∧
      NonVacuous sys.graph sys.trace ∧
      AllLegitimacyAxioms sys.graph ∧
      SpectralCarrierRepresentsGraph sys.graph D.spectralGraph
        D.spectralSignal ∧
      SpectralWellConnected D.spectralGraph D.spectralSignal
        sys.graph.weightedSize_atLeastTwo :=
  semanticKernel_iff_runtime_diagnostic_spectral_layers_unfolded D

/-- Forward semantic bridge: a semantically anchored kernel exposes the
runtime kernel witness, the graph-diagnostic layer, the carrier-grounding
relation, and the spectral layer as ordinary Lean consequences. -/
theorem semanticKernel_implies_runtime_diagnostics_and_spectral
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (h : IsSemanticLegitimacyKernel D) :
    IsLegitimacyKernel D ∧
      AllLegitimacyAxioms sys.graph ∧
      SpectralCarrierRepresentsGraph sys.graph D.spectralGraph
        D.spectralSignal ∧
      SpectralWellConnected D.spectralGraph D.spectralSignal
        sys.graph.weightedSize_atLeastTwo :=
  ⟨h.runtimeKernel, h.semanticBridge.diagnostics,
    h.semanticBridge.carrierRepresentsGraph,
    h.semanticBridge.spectralWellConnected⟩

/-! ## Runtime-only obstruction -/

private def peerRuntimeClaim : ClaimQ := ⟨0, 1, by norm_num, []⟩

private def peerRuntimeTrace : GovernanceTrace :=
  fun _ => (peerRuntimeClaim, some GovernanceOutcome.permit)

private lemma peerGraph_permits_runtime_claim :
    graphDecide peerGraph [peerRuntimeClaim] peerRuntimeClaim.id =
      BinaryDecision.Permit := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

private lemma peerRuntimeTrace_consistent :
    TraceConsistentWithGraph peerRuntimeTrace peerGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, peerRuntimeTrace]
  exact ⟨[peerRuntimeClaim], by simp, peerGraph_permits_runtime_claim⟩

private def peerRuntimeSystem : GovernedSystem 1 where
  graph := peerGraph
  state := permitState
  trace := peerRuntimeTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := peerRuntimeTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 peerGraph

private def peerRuntimeSignal :
    Fin peerRuntimeSystem.graph.weightedSize → ℚ := fun i => i.val + 1

private def peerEmptyLayerEval : LayerEval 0 where
  eval := fun L => nomatch L

private noncomputable def peerRuntimeKernelData :
    LegitimacyKernelData peerRuntimeSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification peerRuntimeSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent peerRuntimeSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer peerRuntimeSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer peerRuntimeSystem
  answer_consistent := state_answer_consistent peerRuntimeSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := peerRuntimeSystem.graph.toWeighted
  spectralSignal := peerRuntimeSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange peerRuntimeSignal
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := peerEmptyLayerEval
  overrideOvs := []

private def peerRuntimeNonVacuousWitness :
    NonVacuousWitness peerGraph peerRuntimeTrace where
  wellFormed := by
    simp [peerGraph, WellFormed]
  governedClaims := [peerRuntimeClaim]
  governed_nonempty := by
    simp
  boundedDisposition := by
    refine ⟨0, ?_⟩
    intro c hc
    simp at hc
    subst c
    exact ⟨0, le_rfl, Or.inl rfl⟩
  permitEligibleClaims := [peerRuntimeClaim]
  eligible_nonempty := by
    simp
  eligible_subset := by
    intro c hc
    simpa using hc
  permitEligible := by
    intro c hc
    simp at hc
    subst c
    exact ⟨0, rfl⟩
  notRefusal := by
    intro hrefusal
    have h0 := hrefusal 0
    simp [peerRuntimeTrace] at h0
  notPermanentEscalation := by
    intro hesc
    have h0 := hesc 0
    simp [peerRuntimeTrace] at h0
  notDeadlock := by
    intro hdead
    have h0 := hdead 0
    simp [peerRuntimeTrace] at h0

private lemma peerRuntime_nonvacuous :
    NonVacuous peerGraph peerRuntimeTrace :=
  ⟨peerRuntimeNonVacuousWitness⟩

private noncomputable def peerRuntimeKernel :
    LegitimacyKernel peerRuntimeSystem where
  toLegitimacyKernelData := peerRuntimeKernelData
  isKernel :=
    { certifiable := graphReplayCertification_certifiable peerRuntimeSystem.graph
      observable := state_id_observable peerRuntimeSystem
      corrigible :=
        kernelCorrigible_zero _ permit_corrigible (by intro a; rfl)
      compositionalSafety :=
        LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
          (noEdge_causal_soundness 1 (allGoverned 1))
      nonVacuous :=
        LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
          peerRuntime_nonvacuous }

/-- Structural obstruction for the unstrengthened target: the five runtime
kernel axioms alone do not imply the graph-diagnostic layer. The peer-relative
kernel satisfies the runtime class, while its graph violates the
graph-diagnostic bundle. -/
theorem runtime_kernel_does_not_imply_graph_diagnostics :
    IsLegitimacyKernel peerRuntimeKernel.toLegitimacyKernelData ∧
      ¬ AllLegitimacyAxioms peerRuntimeSystem.graph := by
  constructor
  · exact peerRuntimeKernel.isKernel
  · change ¬ AllLegitimacyAxioms peerGraph
    exact peerGraph_impossibility

/-! ## Diagnostic-but-not-spectral obstruction -/

private def diagnosticRuntimeGraph : GovernanceGraph :=
  claimantConstGraph (fun _ => BinaryDecision.Permit)

private lemma diagnosticRuntimeGraph_permits_claim :
    graphDecide diagnosticRuntimeGraph [permitClaim] permitClaim.id =
      BinaryDecision.Permit := by
  simp [diagnosticRuntimeGraph, claimantConstGraph, graphDecide]

private lemma diagnosticRuntimeTrace_consistent :
    TraceConsistentWithGraph permitTrace diagnosticRuntimeGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, permitTrace]
  exact ⟨[permitClaim], by simp, diagnosticRuntimeGraph_permits_claim⟩

private def diagnosticRuntimeSystem : GovernedSystem 1 where
  graph := diagnosticRuntimeGraph
  state := permitState
  trace := permitTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := diagnosticRuntimeTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 diagnosticRuntimeGraph

private def diagnosticRuntimeZeroSignal :
    Fin diagnosticRuntimeSystem.graph.weightedSize → ℚ := fun _ => 0

private def diagnosticEmptyLayerEval : LayerEval 0 where
  eval := fun L => nomatch L

private noncomputable def diagnosticRuntimeKernelData :
    LegitimacyKernelData diagnosticRuntimeSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification diagnosticRuntimeSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent diagnosticRuntimeSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer diagnosticRuntimeSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer diagnosticRuntimeSystem
  answer_consistent := state_answer_consistent diagnosticRuntimeSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := diagnosticRuntimeSystem.graph.toWeighted
  spectralSignal := diagnosticRuntimeZeroSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange diagnosticRuntimeZeroSignal
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := diagnosticEmptyLayerEval
  overrideOvs := []

private def diagnosticRuntimeNonVacuousWitness :
    NonVacuousWitness diagnosticRuntimeGraph permitTrace where
  wellFormed := by
    simp [diagnosticRuntimeGraph, claimantConstGraph, WellFormed]
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

private lemma diagnosticRuntime_nonvacuous :
    NonVacuous diagnosticRuntimeGraph permitTrace :=
  ⟨diagnosticRuntimeNonVacuousWitness⟩

private noncomputable def diagnosticRuntimeKernel :
    LegitimacyKernel diagnosticRuntimeSystem where
  toLegitimacyKernelData := diagnosticRuntimeKernelData
  isKernel :=
    { certifiable := graphReplayCertification_certifiable diagnosticRuntimeSystem.graph
      observable := state_id_observable diagnosticRuntimeSystem
      corrigible :=
        kernelCorrigible_zero _ permit_corrigible (by intro a; rfl)
      compositionalSafety :=
        LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
          (noEdge_causal_soundness 1 (allGoverned 1))
      nonVacuous :=
        LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
          diagnosticRuntime_nonvacuous }

private lemma diagnosticRuntimeZeroSignal_cv :
    diagnosticRuntimeSystem.graph.toWeighted.cv diagnosticRuntimeZeroSignal = 0 := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

/-- Strengthening the runtime kernel by the four graph-diagnostic axioms still
does not imply spectral well-connectedness. The witness is a constant-permit
diagnostic graph with a valid runtime kernel, paired with a zero spectral
signal; the zero signal gives zero CV, while `SpectralWellConnected` forces
positive CV. -/
theorem runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected :
    ∃ (n : Nat) (sys : GovernedSystem n) (D : LegitimacyKernelData sys),
      IsLegitimacyKernel D ∧
      AllLegitimacyAxioms sys.graph ∧
      ¬ SpectralWellConnected D.spectralGraph D.spectralSignal
        sys.graph.weightedSize_atLeastTwo := by
  refine ⟨1, diagnosticRuntimeSystem,
    diagnosticRuntimeKernel.toLegitimacyKernelData, ?_, ?_, ?_⟩
  · exact diagnosticRuntimeKernel.isKernel
  · change AllLegitimacyAxioms diagnosticRuntimeGraph
    exact claimantConstGraph_allLegitimacyAxioms _
  · intro hspec
    have hcv_pos :
        0 < diagnosticRuntimeSystem.graph.toWeighted.cv diagnosticRuntimeZeroSignal :=
      SpectralWellConnected_cv_pos
        diagnosticRuntimeKernelData.spectralGraph
        diagnosticRuntimeKernelData.spectralSignal
        diagnosticRuntimeSystem.graph.weightedSize_atLeastTwo
        hspec
    rw [diagnosticRuntimeZeroSignal_cv] at hcv_pos
    exact (lt_irrefl (0 : ℚ)) hcv_pos

/-- The five runtime kernel axioms alone do not imply spectral well-connectedness.
A fortiori consequence of `runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected`:
the same constant-permit, zero-signal witness drops the diagnostic conjunct and
still refutes the spectral predicate. -/
theorem runtime_kernel_does_not_imply_spectral_well_connected :
    ∃ (n : Nat) (sys : GovernedSystem n) (D : LegitimacyKernelData sys),
      IsLegitimacyKernel D ∧
      ¬ SpectralWellConnected D.spectralGraph D.spectralSignal
        sys.graph.weightedSize_atLeastTwo := by
  obtain ⟨n, sys, D, hkernel, _, hspec⟩ :=
    runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected
  exact ⟨n, sys, D, hkernel, hspec⟩

end Legitimacy
