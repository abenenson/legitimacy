/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Bridges.ELK.CoreVocabulary

/-!
# Extractor trace semantics for core-vocabulary ELK observations

This module records the operational trace data needed to classify a core
extractor output branch without carrying a failed-output certificate field.
-/

set_option autoImplicit false

namespace Legitimacy

namespace GovGraph

open Safety

/-- Primitive stage-level extractor trace data.

The selected branch is not justified directly by a failed capability bit.
Instead, the clean branch is selected only when every primitive clean-stage
guard accepts, including the capability validation stage. -/
structure ExtractorTraceFrame where
  sourceEvidenceChecked : Bool
  authorityEquivalentChecked : Bool
  semanticKernelAccepted : Bool
  capabilityValidated : Bool
  selectedBranch : KernelizationExtractorBranch

namespace ExtractorTraceFrame

/-- Operational clean-branch precondition assembled from primitive trace
stages. Any rejected stage routes the run away from the clean branch. -/
def cleanPreconditionsSatisfied (trace : ExtractorTraceFrame) : Bool :=
  trace.sourceEvidenceChecked &&
    trace.authorityEquivalentChecked &&
      trace.semanticKernelAccepted &&
        trace.capabilityValidated

end ExtractorTraceFrame

/-- Core extractor trace semantics for one capacity-aware native observation.

The trace gives the primitive stage booleans for each protocol message, relates
the capability-validation stage to the recorded core capability bit, relates
the trace-selected branch to the recorded core branch, and states the extractor
branch-selection rule from primitive clean-stage preconditions. -/
structure CoreExtractorTraceSemantics
    {n : Nat} {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ} {δ : ℚ}
    {protocol : AlignmentProtocol G s δ}
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    {contract : KernelizationExtractorContract observation}
    (native :
      CoreCapacityAwareExtractorObservation G s δ protocol observation
        contract) where
  traceAt : ∀ block, protocol.Message block → ExtractorTraceFrame
  capabilityValidated_eq :
    ∀ block (message : protocol.Message block),
      (traceAt block message).capabilityValidated =
        observation.capabilityUsed block (native.messageAt block message)
  extractorOutput_eq_selected :
    ∀ block (message : protocol.Message block),
      observation.extractorOutput block (native.messageAt block message) =
        (traceAt block message).selectedBranch
  selectedBranch_eq_cleanPreconditions :
    ∀ block (message : protocol.Message block),
      (traceAt block message).selectedBranch =
      if (traceAt block message).cleanPreconditionsSatisfied then
        KernelizationExtractorBranch.clean
      else
        KernelizationExtractorBranch.certificate

namespace CoreExtractorTraceSemantics

variable {n : Nat} {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
  {δ : ℚ} {protocol : AlignmentProtocol G s δ}
  {artifact : RuleLayerKernelArtifact}
  {observation : GovernanceKernelizationObservation artifact}
  {contract : KernelizationExtractorContract observation}
  {native :
    CoreCapacityAwareExtractorObservation G s δ protocol observation
      contract}

/-- Failed capability branch classification discharged from primitive trace
semantics.

A failed recorded capability use makes the capability-validation trace stage
false. Since capability validation is one of the primitive clean-stage guards,
the clean precondition is false, and the trace branch-selection rule records
the certificate branch. -/
theorem failedCapabilityOutputBranchClassified
    (trace : CoreExtractorTraceSemantics native) :
    FailedCapabilityOutputBranchClassified native := by
  intro block message hfailed
  let frame := trace.traceAt block message
  have hcapability :
      frame.capabilityValidated = false := by
    exact (trace.capabilityValidated_eq block message).trans hfailed
  have hpreconditions :
      frame.cleanPreconditionsSatisfied = false := by
    cases hsource : frame.sourceEvidenceChecked <;>
      cases hauthority : frame.authorityEquivalentChecked <;>
        cases hsemantic : frame.semanticKernelAccepted <;>
          simp [ExtractorTraceFrame.cleanPreconditionsSatisfied, frame,
            hsource, hauthority, hsemantic, hcapability]
  calc
    observation.extractorOutput block (native.messageAt block message) =
        frame.selectedBranch := by
      exact trace.extractorOutput_eq_selected block message
    _ = KernelizationExtractorBranch.certificate := by
      simpa [frame, hpreconditions] using
        trace.selectedBranch_eq_cleanPreconditions block message

end CoreExtractorTraceSemantics

/-- Capacity threshold forcing through core extractor trace semantics.

This is the trace-semantics discharge of the previous residual classifier:
callers provide primitive trace stages and branch-selection semantics, and the
failed-output branch classifier is derived internally. -/
theorem core_capacity_threshold_forces_certificate_from_trace
    {n : Nat} (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (hδ : 0 < δ) (hcv : 0 < G.cv s)
    (protocol : AlignmentProtocol G s δ)
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (contract : KernelizationExtractorContract observation)
    (hcap : C_star G s δ ≤ protocol.target_capability)
    (htarget_floor : ∀ block m i,
      protocol.target_capability ≤
        (protocol.code block).encoder (protocol.encode block m) i)
    (rate : ℚ) (hrate : 0 < rate)
    (hprotocol_rate : ∀ block, 1 ≤ block →
      rate ≤ (Nat.log2 (Fintype.card (protocol.Message block)) : ℚ) / block)
    (native :
      CoreCapacityAwareExtractorObservation G s δ protocol observation
        contract)
    (trace : CoreExtractorTraceSemantics native) :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate observation,
          contract.extract input = Sum.inr cert ∧
            MinimalHiddenAuthority cert :=
  core_capacity_threshold_forces_certificate G s δ hδ hcv protocol
    contract hcap htarget_floor rate hrate hprotocol_rate native
    trace.failedCapabilityOutputBranchClassified

end GovGraph

end Legitimacy
