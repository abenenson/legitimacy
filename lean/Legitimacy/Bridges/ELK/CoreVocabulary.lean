/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Capacity.CapacityConverse
import Legitimacy.Bridges.ELKCorrespondence
import Mathlib.Data.Finset.Card

/-!
# Core-vocabulary ELK capacity observations

Generic helpers for capacity-aware ELK observations whose extractor-run
vocabulary lives directly on `GovernanceKernelizationObservation`.
-/

set_option autoImplicit false

namespace Legitimacy

namespace GovGraph

open Safety

/-- Erase a witness-bearing extractor result to the branch vocabulary carried
by core `GovernanceKernelizationObservation`s. -/
def KernelizationExtractorBranch.ofExtractorResult
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (result :
      Sum (KernelizationCleanWitness observation)
        (HiddenAuthorityCertificate observation)) :
    KernelizationExtractorBranch :=
  match result with
  | Sum.inl _ => KernelizationExtractorBranch.clean
  | Sum.inr _ => KernelizationExtractorBranch.certificate

/-- Core-typed capacity-aware extraction observation. The capacity-aware
message/input/capability/output vocabulary lives on the
`GovernanceKernelizationObservation`; this record only relates the protocol
message type to the core observation's message family and states the extractor
semantics of the recorded branch output.

Unlike `CapacityAwareExtractorObservation`, this structure has no
`failed_output_certificate` field. The branch-to-certificate handoff below is
derived from the extractor result equality, and the remaining local residual is
only the branch classifier saying that failed capability uses record the
certificate branch. -/
structure CoreCapacityAwareExtractorObservation
    {n : Nat} (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (protocol : AlignmentProtocol G s δ)
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact)
    (contract : KernelizationExtractorContract observation) where
  messageAt :
    ∀ block, protocol.Message block → observation.MessageAt block
  capabilityUsed_eq_deploy :
    ∀ block (message : protocol.Message block),
      observation.capabilityUsed block (messageAt block message) =
        protocol.deploy_zero_error_at_capability block message
  extractorOutput_eq :
    ∀ block (message : protocol.Message block),
      observation.extractorOutput block (messageAt block message) =
        KernelizationExtractorBranch.ofExtractorResult
          (contract.extract
            (observation.inputAt block (messageAt block message)))

/-- Named residual for the core-typed path: the extractor semantics can turn a
recorded certificate branch into a concrete certificate, but the present core
vocabulary still needs the observation to classify failed capability uses as
recording the certificate branch. -/
def FailedCapabilityOutputBranchClassified
    {n : Nat} {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ} {δ : ℚ}
    {protocol : AlignmentProtocol G s δ}
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    {contract : KernelizationExtractorContract observation}
    (native :
      CoreCapacityAwareExtractorObservation G s δ protocol observation
        contract) : Prop :=
  ∀ block (message : protocol.Message block),
    observation.capabilityUsed block (native.messageAt block message) =
        false →
      observation.extractorOutput block (native.messageAt block message) =
        KernelizationExtractorBranch.certificate

namespace CoreCapacityAwareExtractorObservation

variable {n : Nat} {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
  {δ : ℚ} {protocol : AlignmentProtocol G s δ}
  {artifact : RuleLayerKernelArtifact}
  {observation : GovernanceKernelizationObservation artifact}
  {contract : KernelizationExtractorContract observation}

/-- If the core observation records the certificate branch and the branch is
semantically tied to the extractor result, a concrete hidden-authority
certificate is recovered by case analysis on the extractor output. -/
theorem certificate_of_recorded_certificate_branch
    (native :
      CoreCapacityAwareExtractorObservation G s δ protocol observation
        contract)
    {block : Nat} {message : protocol.Message block}
    (hbranch :
      observation.extractorOutput block
          (native.messageAt block message) =
        KernelizationExtractorBranch.certificate) :
    ∃ cert : HiddenAuthorityCertificate observation,
      contract.extract
          (observation.inputAt block
            (native.messageAt block message)) =
        Sum.inr cert := by
  let coreMessage := native.messageAt block message
  cases hresult :
      contract.extract (observation.inputAt block coreMessage) with
  | inl witness =>
      have hclean :
          observation.extractorOutput block coreMessage =
            KernelizationExtractorBranch.clean := by
        simpa [KernelizationExtractorBranch.ofExtractorResult, coreMessage,
          hresult] using native.extractorOutput_eq block message
      rw [hclean] at hbranch
      cases hbranch
  | inr cert =>
      exact ⟨cert, rfl⟩

/-- Core-vocabulary failed capability handoff. This narrows the old
`failed_output_certificate` field to
`FailedCapabilityOutputBranchClassified`; once a failed use is classified as
the recorded certificate branch, the concrete certificate and its minimality
are derived from extractor semantics and `certSound`. -/
theorem failed_capability_use_extracts_certificate_from_core
    (native :
      CoreCapacityAwareExtractorObservation G s δ protocol observation
        contract)
    (hclassified : FailedCapabilityOutputBranchClassified native)
    {block : Nat} {message : protocol.Message block}
    (hfailed :
      protocol.deploy_zero_error_at_capability block message = false) :
    ∃ input : ExtractorInput,
      ∃ cert : HiddenAuthorityCertificate observation,
        contract.extract input = Sum.inr cert ∧
          MinimalHiddenAuthority cert := by
  let coreMessage := native.messageAt block message
  have hcapability :
      observation.capabilityUsed block coreMessage = false := by
    rw [native.capabilityUsed_eq_deploy block message]
    exact hfailed
  have hbranch :
      observation.extractorOutput block coreMessage =
        KernelizationExtractorBranch.certificate :=
    hclassified block message hcapability
  rcases native.certificate_of_recorded_certificate_branch hbranch with
    ⟨cert, hextract⟩
  exact ⟨observation.inputAt block coreMessage, cert, hextract,
    contract.certSound (observation.inputAt block coreMessage) cert
      hextract⟩

end CoreCapacityAwareExtractorObservation

/-- Capacity threshold forcing through the core observation vocabulary. The
only residual is the named failed-branch classifier; the certificate itself is
derived from the recorded extractor semantics. -/
theorem core_capacity_threshold_forces_certificate
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
    (hclassified : FailedCapabilityOutputBranchClassified native) :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate observation,
          contract.extract input = Sum.inr cert ∧
            MinimalHiddenAuthority cert := by
  obtain ⟨block_length, hfailed⟩ :=
    governance_capacity_alignment_threshold G s δ hδ hcv protocol hcap
      htarget_floor rate hrate hprotocol_rate
  refine ⟨block_length, ?_⟩
  intro block hblock
  obtain ⟨message, hmessage⟩ := hfailed block hblock
  exact native.failed_capability_use_extracts_certificate_from_core
    hclassified hmessage

end GovGraph

end Legitimacy
