/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/
import Legitimacy.Spectral.Capacity.CapacityConverse
import Legitimacy.Bridges.ELKCorrespondence
import Legitimacy.Bridges.ELK.CoreVocabulary
import Legitimacy.Bridges.ELK.TraceSemantics
import Mathlib.Data.Finset.Card
/-!
# Capacity-aware ELK bridge

This module connects the zero-error capacity converse for the deterministic
capability-response channel to the ARC ELK hidden-authority certificate
vocabulary. The ELK report is cited in the narrow sense used by this bridge:
Christiano, Cotra, and Xu's 2021 ARC technical report "Eliciting Latent
Knowledge" frames latent knowledge extraction as eliciting truthful facts from
a reporter even when direct observation is misleading; the Lean theorem below
uses only the already-formalized five hidden-authority certificate classes.

The capacity side is intentionally the substrate that exists in this
repository: `CapabilityResponseBlockCode`, zero-error decoding, and the
binary-output log-rate converse. It is not a new stochastic Shannon channel
layer, and it does not identify `C_star` with a numeric certificate-emission
rate.
-/
set_option autoImplicit false
namespace Legitimacy
namespace Safety
/-! ## Five hidden-authority certificate kinds -/
namespace HiddenAuthorityCertificateKind
/-- The complete five-kind hidden-authority certificate vocabulary. -/
def all : Finset HiddenAuthorityCertificateKind :=
  { unmodeledEdge, bypassPath, hiddenOverride, sourceEvidenceGap,
    semanticBridgeFailure }
/-- Proves `card_all` for the capacity-aware ELK extraction substrate; it is scoped to the finite certificate fixture. -/
theorem card_all : all.card = 5 := by
  native_decide

end HiddenAuthorityCertificateKind

/-- Erase a witness-bearing hidden-authority certificate to its finite kind. The erasure is only for emission counting; the witness-bearing correspondence in `ELKCorrespondence` remains the source of truth for substrate derivations. -/
def HiddenAuthorityCertificate.kind
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation) :
    HiddenAuthorityCertificateKind :=
  match cert with
  | HiddenAuthorityCertificate.unmodeledEdge _ => .unmodeledEdge
  | HiddenAuthorityCertificate.bypassPath _ => .bypassPath
  | HiddenAuthorityCertificate.hiddenOverride _ => .hiddenOverride
  | HiddenAuthorityCertificate.sourceEvidenceGap _ => .sourceEvidenceGap
  | HiddenAuthorityCertificate.semanticBridgeFailure _ =>
      .semanticBridgeFailure

end Safety

namespace GovGraph

open Safety

/-! ## Extraction windows and finite emission streams -/

/-- A finite extraction window measured in deterministic channel uses. The positivity field keeps the rate expressions aligned with the existing capacity-converse theorem, whose block threshold starts at one. -/
structure ExtractionWindow where
  block : Nat
  positive : 1 ≤ block

/-- A stream records which of the five hidden-authority certificate classes were emitted in the window. The witness payloads remain observation-dependent, so the rate theorem counts distinct certificate classes rather than pretending all concrete certificates live in one global finite type. -/
abbrev CertificateEmissionStream :=
  Finset HiddenAuthorityCertificateKind

/-- A named provider for the axiomatic interface boundary between the finite ELK certificate vocabulary and a concrete channel message alphabet. This layer does not expose transition labels rich enough to derive the injection from a graph; callers must provide the encoding and its injectivity explicitly. -/
structure CertificateEncodingProvider
    {n : Nat} (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (window : ExtractionWindow)
    (code : CapabilityResponseBlockCode G s δ window.block) where
  encodeKind : HiddenAuthorityCertificateKind → code.Message
  encodeKind_injective : Function.Injective encodeKind

/-- A certificate extractor respects the available channel when its emitted certificate classes have a named injective encoding provider inside the message alphabet of a zero-error `CapabilityResponseBlockCode` for the same window. This is the load-bearing compliance boundary: without the provider and zero-error decoding, finite ELK labels alone do not imply a capacity bound. -/
structure ExtractorRespectsChannel
    {n : Nat} (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (window : ExtractionWindow)
    (emission : CertificateEmissionStream)
    (code : CapabilityResponseBlockCode G s δ window.block) where
  encoding : CertificateEncodingProvider G s δ window code
  zero_error : code.ZeroError

namespace ExtractorRespectsChannel

variable {n : Nat} {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
  {δ : ℚ} {window : ExtractionWindow}
  {emission : CertificateEmissionStream}
  {code : CapabilityResponseBlockCode G s δ window.block}

/-- Proves `emission_card_le_message_card` for the capacity-aware ELK extraction substrate; it is scoped to the finite certificate fixture. -/
theorem emission_card_le_message_card
    (hrespect :
      ExtractorRespectsChannel G s δ window emission code) :
    emission.card ≤ Fintype.card code.Message := by
  have hknown_kinds :
      emission.card ≤ Fintype.card HiddenAuthorityCertificateKind := by
    simpa using Finset.card_le_univ emission
  have hnamed_encoding :
      Fintype.card HiddenAuthorityCertificateKind ≤ Fintype.card code.Message :=
    Fintype.card_le_of_injective hrespect.encoding.encodeKind
      hrespect.encoding.encodeKind_injective
  exact le_trans hknown_kinds hnamed_encoding

/-- Proves `emission_log_le_message_log` for the capacity-aware ELK extraction substrate; it is scoped to the finite certificate fixture. -/
theorem emission_log_le_message_log
    (hrespect :
      ExtractorRespectsChannel G s δ window emission code) :
    Nat.log2 emission.card ≤ Nat.log2 (Fintype.card code.Message) := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right hrespect.emission_card_le_message_card

end ExtractorRespectsChannel

/-! ## Capacity-aware ELK forcing theorem -/

/-- An extraction stream is *strictly below* a target log-rate when the target rate is not at-or-below `log2(emission.card) / block`. Read this as a per-use rate predicate: the rate is measured in base-2 logarithm of distinct emitted certificate classes per deterministic channel use, and the predicate fires when the candidate rate is strictly above that quantity. Naming caveat: the prior name was `ExtractionRespectsCapacityBound`, which suggested a shape `card ≤ ⌊C* · t⌋`. The body below keys on `binaryDecisionPerUseRate` (per-use log-rate) rather than on `C_star` numerically; the structural `C_star` link lives in `governance_capacity_threshold_C_star_binding` rather than here. -/
def ExtractionStrictlyBelowLog2Rate
    (window : ExtractionWindow)
    (emission : CertificateEmissionStream)
    (rate : ℚ) : Prop :=
  ¬ rate ≤ (Nat.log2 emission.card : ℚ) / (window.block : ℚ)

/-- Capacity-aware ELK forcing theorem. If a hidden-authority certificate extractor is actually represented by a zero-error capability-response block code, then the existing binary-output converse forces the emitted ELK certificate-class log-rate below every rate strictly above one binary decision per channel use. This is deliberately an extraction-channel theorem, not a claim that `C_star` is itself a Shannon capacity for arbitrary ELK reporters. The only numeric capacity threshold used here is `binaryDecisionPerUseRate`, and the bridge to ELK is the injective, zero-error `ExtractorRespectsChannel` witness. -/
theorem hidden_authority_certificate_rate_bounded
    {n : Nat} (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (rate : ℚ) (hrate : binaryDecisionPerUseRate < rate) :
    ∃ block_threshold : Nat, ∀ window : ExtractionWindow,
      block_threshold ≤ window.block →
        ∀ (code : CapabilityResponseBlockCode G s δ window.block)
          (emission : CertificateEmissionStream),
          ExtractorRespectsChannel G s δ window emission code →
            ExtractionStrictlyBelowLog2Rate window emission rate := by
  obtain ⟨block_threshold, hconverse⟩ :=
    binary_output_log_rate_converse G s δ rate hrate
  refine ⟨block_threshold, ?_⟩
  intro window hthreshold code emission hrespect hrate_emission
  have hlog_le_q :
      (Nat.log2 emission.card : ℚ) ≤
        Nat.log2 (Fintype.card code.Message) := by
    exact_mod_cast hrespect.emission_log_le_message_log
  have hblock_nonneg : (0 : ℚ) ≤ window.block := by
    exact_mod_cast Nat.zero_le window.block
  have hrate_code :
      rate ≤
        (Nat.log2 (Fintype.card code.Message) : ℚ) /
          (window.block : ℚ) := by
    exact le_trans hrate_emission
      (div_le_div_of_nonneg_right hlog_le_q hblock_nonneg)
  exact (hconverse window.block hthreshold code hrate_code) hrespect.zero_error

/-! ## Capacity-forced extractor certificates -/

/-- Capacity-aware extraction observations decorate one kernelization observation with the capability-use and extractor-run data needed by the capacity converse. The record is intentionally observation-shaped rather than a separate failure-to-certificate bridge. A block/message pair carries its own bounded extractor input, the capability-use bit observed for that pair, and the recorded extractor output. The residual hypothesis is the narrow branch classifier `failed_output_certificate`: if the recorded capability-use bit is false, the recorded extractor output is on the certificate branch. The certificate itself is then derived by projecting the recorded output, and minimality still comes from `KernelizationExtractorContract.certSound`. -/
structure CapacityAwareExtractorObservation
    {n : Nat} (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (protocol : AlignmentProtocol G s δ)
    {artifact : RuleLayerKernelArtifact}
    (observation : GovernanceKernelizationObservation artifact)
    (contract : KernelizationExtractorContract observation) where
  inputAt :
    ∀ block, protocol.Message block → ExtractorInput
  failed_output_certificate :
    ∀ block (message : protocol.Message block),
      protocol.deploy_zero_error_at_capability block message = false →
        ∃ cert : HiddenAuthorityCertificate observation,
          contract.extract (inputAt block message) = Sum.inr cert

namespace CapacityAwareExtractorObservation

variable {n : Nat} {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
  {δ : ℚ} {protocol : AlignmentProtocol G s δ}
  {artifact : RuleLayerKernelArtifact}
  {observation : GovernanceKernelizationObservation artifact}
  {contract : KernelizationExtractorContract observation}

/-- Projection replacing the former stored capability-use field. A capacity-aware observation's capability bit is the protocol deployment result at the same block and message. -/
def capabilityUsed
    (_native :
      CapacityAwareExtractorObservation G s δ protocol observation contract)
    (block : Nat) (message : protocol.Message block) : Bool :=
  protocol.deploy_zero_error_at_capability block message

/-- Projection replacing the former stored extractor-output field. The output is the contract result at the observation's input for the same block and message. -/
def extractorOutput
    (native :
      CapacityAwareExtractorObservation G s δ protocol observation contract)
    (block : Nat) (message : protocol.Message block) :
    Sum (KernelizationCleanWitness observation)
      (HiddenAuthorityCertificate observation) :=
  contract.extract (native.inputAt block message)

/-- The capability-use value is a projection from the protocol, not an independent observation field. -/
theorem CapacityAwareExtractorObservation_capabilityUsed_field_eq_projection
    (native :
      CapacityAwareExtractorObservation G s δ protocol observation contract)
    (block : Nat) (message : protocol.Message block) :
    native.capabilityUsed block message =
      protocol.deploy_zero_error_at_capability block message :=
  rfl

/-- The extractor-output value is a projection from the contract and input, not an independent observation field. -/
theorem CapacityAwareExtractorObservation_extractorOutput_field_eq_projection
    (native :
      CapacityAwareExtractorObservation G s δ protocol observation contract)
    (block : Nat) (message : protocol.Message block) :
    native.extractorOutput block message =
      contract.extract (native.inputAt block message) :=
  rfl

/-- Derived failure handoff. Once a capacity-aware observation records a failed capability use and its extractor output, the certificate-branch extractor fact is projected from the observation rather than supplied as a separate bridge conditional. -/
theorem failed_capability_use_extracts_certificate
    (native :
      CapacityAwareExtractorObservation G s δ protocol observation contract)
    {block : Nat} {message : protocol.Message block}
    (hfailed :
      protocol.deploy_zero_error_at_capability block message = false) :
    ∃ input : ExtractorInput,
      ∃ cert : HiddenAuthorityCertificate observation,
        contract.extract input = Sum.inr cert ∧
          MinimalHiddenAuthority cert := by
  rcases native.failed_output_certificate block message hfailed with
    ⟨cert, hextract⟩
  let input := native.inputAt block message
  exact ⟨input, cert, hextract, contract.certSound input cert hextract⟩

end CapacityAwareExtractorObservation

/-- Capacity threshold forcing from native capacity-aware extraction observations. Honest restate: this removes the explicit `CapacityFailureExtractorBridge` conditional. The remaining local gap is narrower: a capacity-aware observation must classify failed recorded capability uses as certificate-branch extractor outputs. It no longer preselects a certificate per protocol failure or assumes an external message-to-input bridge; those are native observation fields, and the certificate handoff is derived by projecting the recorded extractor output. -/
theorem capacity_threshold_forces_certificate
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
      CapacityAwareExtractorObservation G s δ protocol observation contract) :
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
  exact native.failed_capability_use_extracts_certificate hmessage

/-! ### Concrete forcing fixture -/

/-- Native capacity-aware observation for the padded bottleneck protocol. The recorded extractor output is the bypass-path certificate branch, so failed capability uses project to a genuine multi-hop authority route. -/
def bottleneckPaddedBypassExtractionObservation :
    CapacityAwareExtractorObservation bottleneckGraph sig (1 / 10)
      bottleneckPaddedAlignmentProtocol bypassPathObservation
      bypassPathExtractorContract where
  inputAt := fun _ _ => autogenExtractorInput
  failed_output_certificate := by
    intro _block _message _hfailed
    exact ⟨bypassPathCertificate, rfl⟩

/-- Worked capacity-forcing instance. On the concrete bottleneck graph, the padded target-saturating protocol is above the exact `C_star = 1/10` threshold. The capacity converse produces a failed deployment beyond the block threshold, and the native extraction observation routes that failure to the bypass-path certificate emitted by the kernelization extractor. -/
theorem bottleneck_padded_capacity_forces_certificate :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate bypassPathObservation,
          bypassPathExtractorContract.extract input = Sum.inr cert ∧
            MinimalHiddenAuthority cert := by
  have hcap :
      C_star bottleneckGraph sig (1 / 10) ≤
        bottleneckPaddedAlignmentProtocol.target_capability := by
    change C_star bottleneckGraph sig (1 / 10) ≤ (1 / 10 : ℚ)
    rw [concrete_C_star_values.2.2.2.2]
  have htarget_floor : ∀ block m i,
      bottleneckPaddedAlignmentProtocol.target_capability ≤
        (bottleneckPaddedAlignmentProtocol.code block).encoder
          (bottleneckPaddedAlignmentProtocol.encode block m) i := by
    intro _block _message _i
    rfl
  exact capacity_threshold_forces_certificate bottleneckGraph sig (1 / 10)
    (by norm_num) (by native_decide) bottleneckPaddedAlignmentProtocol
    bypassPathExtractorContract hcap htarget_floor (3 / 2) (by norm_num)
    bottleneckPaddedAlignmentProtocol_log_rate
    bottleneckPaddedBypassExtractionObservation

/-- More explicit operational witness for the worked fixture: the certificate forced in the concrete bottleneck instance is the bypass-path certificate. -/
theorem bottleneck_padded_capacity_forces_bypass_certificate :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate bypassPathObservation,
          bypassPathExtractorContract.extract input = Sum.inr cert ∧
            cert = bypassPathCertificate ∧
              MinimalHiddenAuthority cert := by
  obtain ⟨block_length, hfailed⟩ :=
    bottleneck_padded_alignment_converse_fires
  refine ⟨block_length, ?_⟩
  intro block hblock
  obtain ⟨_message, _hmessage⟩ := hfailed block hblock
  exact ⟨autogenExtractorInput, bypassPathCertificate, rfl, rfl,
    bypassPathCertificate_minimal⟩

/-- Native capacity-aware observation using the same padded bottleneck capacity protocol but a source-evidence-gap kernelization observation. This fixture was not represented by the old concrete bypass bridge instance; the certificate is projected from the observation's recorded extractor output. -/
def bottleneckPaddedSourceGapExtractionObservation :
    CapacityAwareExtractorObservation bottleneckGraph sig (1 / 10)
      bottleneckPaddedAlignmentProtocol sourceGapObservation
      sourceEvidenceGapExtractorContract where
  inputAt := fun _ _ => autogenExtractorInput
  failed_output_certificate := by
    intro _block _message _hfailed
    exact ⟨sourceEvidenceGapCertificate, rfl⟩

/-- Tightness fixture beyond the old concrete bypass instance: the same capacity failure can be observed through a native source-evidence-gap extractor run without introducing a second explicit failure bridge. -/
theorem bottleneck_padded_capacity_forces_source_gap_certificate :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate sourceGapObservation,
          sourceEvidenceGapExtractorContract.extract input = Sum.inr cert ∧
            MinimalHiddenAuthority cert := by
  have hcap :
      C_star bottleneckGraph sig (1 / 10) ≤
        bottleneckPaddedAlignmentProtocol.target_capability := by
    change C_star bottleneckGraph sig (1 / 10) ≤ (1 / 10 : ℚ)
    rw [concrete_C_star_values.2.2.2.2]
  have htarget_floor : ∀ block m i,
      bottleneckPaddedAlignmentProtocol.target_capability ≤
        (bottleneckPaddedAlignmentProtocol.code block).encoder
          (bottleneckPaddedAlignmentProtocol.encode block m) i := by
    intro _block _message _i
    rfl
  exact capacity_threshold_forces_certificate bottleneckGraph sig (1 / 10)
    (by norm_num) (by native_decide) bottleneckPaddedAlignmentProtocol
    sourceEvidenceGapExtractorContract hcap htarget_floor (3 / 2)
    (by norm_num) bottleneckPaddedAlignmentProtocol_log_rate
    bottleneckPaddedSourceGapExtractionObservation

/-- Explicit source-evidence-gap projection for the native tightness fixture. -/
theorem bottleneck_padded_capacity_forces_named_source_gap_certificate :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate sourceGapObservation,
          sourceEvidenceGapExtractorContract.extract input = Sum.inr cert ∧
            cert = sourceEvidenceGapCertificate ∧
              MinimalHiddenAuthority cert := by
  obtain ⟨block_length, hfailed⟩ :=
    bottleneck_padded_alignment_converse_fires
  refine ⟨block_length, ?_⟩
  intro block hblock
  obtain ⟨_message, _hmessage⟩ := hfailed block hblock
  exact ⟨autogenExtractorInput, sourceEvidenceGapCertificate, rfl, rfl,
    sourceEvidenceGapCertificate_minimal⟩

/-! ### Core-vocabulary capacity fixtures -/

/-- Core-vocabulary bypass observation: the capacity-aware input, capability-use bit, and branch-level extractor output now live directly on the kernelization observation. -/
noncomputable def bottleneckPaddedBypassCoreObservation :
    GovernanceKernelizationObservation kernelizationExampleArtifact where
  reported := bypassPathObservation.reported
  effective := bypassPathObservation.effective
  sourceEdges := bypassPathObservation.sourceEdges
  reportedSemanticBridgeClean :=
    bypassPathObservation.reportedSemanticBridgeClean
  MessageAt := bottleneckPaddedAlignmentProtocol.Message
  inputAt := fun _ _ => autogenExtractorInput
  capabilityUsed := fun block message =>
    bottleneckPaddedAlignmentProtocol.deploy_zero_error_at_capability
      block message
  extractorOutput := fun _ _ => KernelizationExtractorBranch.certificate

def bottleneckPaddedBypassCoreCertificate :
    HiddenAuthorityCertificate bottleneckPaddedBypassCoreObservation :=
  HiddenAuthorityCertificate.bypassPath
    { source := "user"
      middle := ["router"]
      target := "admin"
      middle_nonempty := by simp
      route_nodup := by native_decide
      effective_route := by
        simpa [bottleneckPaddedBypassCoreObservation,
          bypassPathObservation] using bypassGraph_route_permitted
      reported_route := by
        simpa [bottleneckPaddedBypassCoreObservation,
          bypassPathObservation] using bypassGraph_route_permitted
      reported_lacks_direct := by
        simp [bottleneckPaddedBypassCoreObservation, bypassPathObservation,
          bypassGraph, HasAuthorityEdge] }

/-- Proves `bottleneckPaddedBypassCoreCertificate_minimal` for the capacity-aware ELK extraction substrate; it is scoped to the finite certificate fixture. -/
theorem bottleneckPaddedBypassCoreCertificate_minimal :
    MinimalHiddenAuthority bottleneckPaddedBypassCoreCertificate := by
  dsimp [MinimalHiddenAuthority, bottleneckPaddedBypassCoreCertificate]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · native_decide
  · exact ⟨by norm_num, by
      simpa [bottleneckPaddedBypassCoreObservation, bypassPathObservation]
        using bypassGraph_route_permitted⟩
  · change BypassPathMinimal bottleneckPaddedBypassCoreObservation.reported
      { source := "user"
        middle := ["router"]
        target := "admin"
        middle_nonempty := by simp
        route_nodup := by native_decide
        effective_route := by
          simpa [bottleneckPaddedBypassCoreObservation, bypassPathObservation]
            using bypassGraph_route_permitted
        reported_route := by
          simpa [bottleneckPaddedBypassCoreObservation, bypassPathObservation]
            using bypassGraph_route_permitted
        reported_lacks_direct := by
          simp [bottleneckPaddedBypassCoreObservation, bypassPathObservation,
            bypassGraph, HasAuthorityEdge] }
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨by norm_num, by
        simpa [bottleneckPaddedBypassCoreObservation, bypassPathObservation]
          using bypassGraph_route_permitted⟩
    · exact ⟨⟨by norm_num, by
        simpa [bottleneckPaddedBypassCoreObservation, bypassPathObservation]
          using bypassGraph_route_permitted⟩, by
          simp [routeDirectEdge?, routeTarget?,
            bottleneckPaddedBypassCoreObservation, bypassPathObservation,
            bypassGraph, HasAuthorityEdge]⟩
    · intro shorter hproper hbypass
      rcases hproper with ⟨hsub, hne⟩
      dsimp [routeSublists] at hsub
      have hcases :
        shorter = [] ∨ shorter = ["admin"] ∨
          shorter = ["router"] ∨ shorter = ["router", "admin"] ∨
          shorter = ["user"] ∨ shorter = ["user", "admin"] ∨
          shorter = ["user", "router"] ∨
          shorter = ["user", "router", "admin"] := by
        simpa using hsub
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (by norm_num : ¬ 2 ≤ ([] : List AuthorityNodeId).length)
          hbypass.1.1
      · exact (by norm_num : ¬ 2 ≤ (["admin"] : List AuthorityNodeId).length)
          hbypass.1.1
      · exact (by norm_num :
          ¬ 2 ≤ (["router"] : List AuthorityNodeId).length) hbypass.1.1
      · exact hbypass.2 (by
          simp [bottleneckPaddedBypassCoreObservation, bypassPathObservation,
            bypassGraph, HasAuthorityEdge])
      · exact (by norm_num : ¬ 2 ≤ (["user"] : List AuthorityNodeId).length)
          hbypass.1.1
      · have hdirect := hbypass.1.2
          { fromNode := "user", toNode := "admin" }
          (by simp [pathAuthorityEdges])
        simp [bottleneckPaddedBypassCoreObservation, bypassPathObservation,
          bypassGraph, HasAuthorityEdge] at hdirect
      · exact hbypass.2 (by
          simp [bottleneckPaddedBypassCoreObservation, bypassPathObservation,
            bypassGraph, HasAuthorityEdge])
      · exact (hne rfl).elim

def bottleneckPaddedBypassCoreExtractorContract :
    KernelizationExtractorContract bottleneckPaddedBypassCoreObservation where
  extract := fun _ => Sum.inr bottleneckPaddedBypassCoreCertificate
  cleanSound := by
    intro _input _witness hextract
    cases hextract
  certSound := by
    intro _input _cert hextract
    cases hextract
    exact bottleneckPaddedBypassCoreCertificate_minimal

def bottleneckPaddedBypassCoreExtractionObservation :
    CoreCapacityAwareExtractorObservation bottleneckGraph sig (1 / 10)
      bottleneckPaddedAlignmentProtocol
      bottleneckPaddedBypassCoreObservation
      bottleneckPaddedBypassCoreExtractorContract where
  messageAt := fun _ message => message
  capabilityUsed_eq_deploy := by
    intro _block _message
    rfl
  extractorOutput_eq := by
    intro _block _message
    rfl

noncomputable def bottleneckPaddedBypassCoreTraceSemantics :
    CoreExtractorTraceSemantics
      bottleneckPaddedBypassCoreExtractionObservation where
  traceAt := fun block message =>
    { sourceEvidenceChecked := true
      authorityEquivalentChecked := false
      semanticKernelAccepted := true
      capabilityValidated :=
        bottleneckPaddedBypassCoreObservation.capabilityUsed block message
      selectedBranch := KernelizationExtractorBranch.certificate }
  capabilityValidated_eq := by
    intro _block _message
    rfl
  extractorOutput_eq_selected := by
    intro _block _message
    rfl
  selectedBranch_eq_cleanPreconditions := by
    intro _block _message
    simp [ExtractorTraceFrame.cleanPreconditionsSatisfied]

/-- Proves `bottleneckPaddedBypassCore_failed_branch_classified` for the capacity-aware ELK extraction substrate; it is scoped to the finite certificate fixture. -/
theorem bottleneckPaddedBypassCore_failed_branch_classified :
    FailedCapabilityOutputBranchClassified
      bottleneckPaddedBypassCoreExtractionObservation :=
  bottleneckPaddedBypassCoreTraceSemantics
    |>.failedCapabilityOutputBranchClassified

/-- Worked classification instance: a real capacity-converse failed deployment in the padded bottleneck fixture is recorded as the certificate branch in the core capacity-aware observation. The branch is the core certificate output, not a clean/pass branch or an unclassified rejection. -/
theorem bottleneckPaddedBypassCore_failed_capacity_use_certificate_branch :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ message : bottleneckPaddedAlignmentProtocol.Message block,
        bottleneckPaddedAlignmentProtocol.deploy_zero_error_at_capability
            block message = false ∧
          bottleneckPaddedBypassCoreObservation.capabilityUsed block
              (bottleneckPaddedBypassCoreExtractionObservation.messageAt
                block message) = false ∧
            bottleneckPaddedBypassCoreObservation.extractorOutput block
                (bottleneckPaddedBypassCoreExtractionObservation.messageAt
                  block message) =
              KernelizationExtractorBranch.certificate := by
  obtain ⟨block_length, hfailed⟩ :=
    bottleneck_padded_alignment_converse_fires
  refine ⟨block_length, ?_⟩
  intro block hblock
  obtain ⟨message, hmessage⟩ := hfailed block hblock
  have hcapability :
      bottleneckPaddedBypassCoreObservation.capabilityUsed block
          (bottleneckPaddedBypassCoreExtractionObservation.messageAt block
            message) = false := by
    rw [bottleneckPaddedBypassCoreExtractionObservation.capabilityUsed_eq_deploy
      block message]
    exact hmessage
  have hbranch :
      bottleneckPaddedBypassCoreObservation.extractorOutput block
          (bottleneckPaddedBypassCoreExtractionObservation.messageAt block
            message) =
        KernelizationExtractorBranch.certificate :=
    bottleneckPaddedBypassCore_failed_branch_classified block message
      hcapability
  exact ⟨message, hmessage, hcapability, hbranch⟩

/-- Core-vocabulary source-gap observation over the same padded bottleneck capacity protocol. -/
noncomputable def bottleneckPaddedSourceGapCoreObservation :
    GovernanceKernelizationObservation kernelizationExampleArtifact where
  reported := sourceGapObservation.reported
  effective := sourceGapObservation.effective
  sourceEdges := sourceGapObservation.sourceEdges
  reportedSemanticBridgeClean := sourceGapObservation.reportedSemanticBridgeClean
  MessageAt := bottleneckPaddedAlignmentProtocol.Message
  inputAt := fun _ _ => autogenExtractorInput
  capabilityUsed := fun block message =>
    bottleneckPaddedAlignmentProtocol.deploy_zero_error_at_capability
      block message
  extractorOutput := fun _ _ => KernelizationExtractorBranch.certificate

def bottleneckPaddedSourceGapCoreCertificate :
    HiddenAuthorityCertificate bottleneckPaddedSourceGapCoreObservation :=
  HiddenAuthorityCertificate.sourceEvidenceGap
    { edge := { fromNode := "principal", toNode := "reviewer" }
      effective_has_edge := by
        left
        simp [bottleneckPaddedSourceGapCoreObservation,
          sourceGapObservation, cleanAuthorityGraph, HasAuthorityEdge]
      source_lacks_edge := by
        simp [bottleneckPaddedSourceGapCoreObservation,
          sourceGapObservation, SourceDerivesEdge] }

/-- Proves `bottleneckPaddedSourceGapCoreCertificate_minimal` for the capacity-aware ELK extraction substrate; it is scoped to the finite certificate fixture. -/
theorem bottleneckPaddedSourceGapCoreCertificate_minimal :
    MinimalHiddenAuthority bottleneckPaddedSourceGapCoreCertificate := by
  change
    HasAuthoritySurface bottleneckPaddedSourceGapCoreObservation.effective
        { fromNode := "principal", toNode := "reviewer" } ∧
      ¬ SourceEvidenceDerivable
        bottleneckPaddedSourceGapCoreObservation.sourceEdges
        { fromNode := "principal", toNode := "reviewer" }
  constructor
  · left
    simp [bottleneckPaddedSourceGapCoreObservation, sourceGapObservation,
      cleanAuthorityGraph, HasAuthorityEdge]
  · rw [sourceEvidenceDerivable_iff]
    simp [bottleneckPaddedSourceGapCoreObservation, sourceGapObservation,
      SourceDerivesEdge]

def bottleneckPaddedSourceGapCoreExtractorContract :
    KernelizationExtractorContract bottleneckPaddedSourceGapCoreObservation where
  extract := fun _ => Sum.inr bottleneckPaddedSourceGapCoreCertificate
  cleanSound := by
    intro _input _witness hextract
    cases hextract
  certSound := by
    intro _input _cert hextract
    cases hextract
    exact bottleneckPaddedSourceGapCoreCertificate_minimal

def bottleneckPaddedSourceGapCoreExtractionObservation :
    CoreCapacityAwareExtractorObservation bottleneckGraph sig (1 / 10)
      bottleneckPaddedAlignmentProtocol
      bottleneckPaddedSourceGapCoreObservation
      bottleneckPaddedSourceGapCoreExtractorContract where
  messageAt := fun _ message => message
  capabilityUsed_eq_deploy := by
    intro _block _message
    rfl
  extractorOutput_eq := by
    intro _block _message
    rfl

noncomputable def bottleneckPaddedSourceGapCoreTraceSemantics :
    CoreExtractorTraceSemantics
      bottleneckPaddedSourceGapCoreExtractionObservation where
  traceAt := fun block message =>
    { sourceEvidenceChecked := false
      authorityEquivalentChecked := true
      semanticKernelAccepted := true
      capabilityValidated :=
        bottleneckPaddedSourceGapCoreObservation.capabilityUsed block message
      selectedBranch := KernelizationExtractorBranch.certificate }
  capabilityValidated_eq := by
    intro _block _message
    rfl
  extractorOutput_eq_selected := by
    intro _block _message
    rfl
  selectedBranch_eq_cleanPreconditions := by
    intro _block _message
    simp [ExtractorTraceFrame.cleanPreconditionsSatisfied]

/-- Proves `bottleneckPaddedSourceGapCore_failed_branch_classified` for the capacity-aware ELK extraction substrate; it is scoped to the finite certificate fixture. -/
theorem bottleneckPaddedSourceGapCore_failed_branch_classified :
    FailedCapabilityOutputBranchClassified
      bottleneckPaddedSourceGapCoreExtractionObservation :=
  bottleneckPaddedSourceGapCoreTraceSemantics
    |>.failedCapabilityOutputBranchClassified

/-- Both core bottleneck fixtures have their failed capability-use traces classified as certificate-branch extractor outputs. The theorem packages the bypass and source-evidence-gap classifiers together, showing that the trace semantics layer covers both certificate classes over the same padded capacity protocol. -/
theorem bottleneckPaddedCore_trace_semantics_discharge_toy_cases :
    FailedCapabilityOutputBranchClassified
        bottleneckPaddedBypassCoreExtractionObservation ∧
      FailedCapabilityOutputBranchClassified
        bottleneckPaddedSourceGapCoreExtractionObservation :=
  ⟨bottleneckPaddedBypassCore_failed_branch_classified,
    bottleneckPaddedSourceGapCore_failed_branch_classified⟩

/-- Core-vocabulary capacity forcing for the bypass fixture. The proof combines the exact bottleneck `C_star` threshold, the padded protocol's target floor, the protocol log-rate lower bound, and the core trace semantics observation to produce a block threshold after which some extractor input emits a minimal bypass certificate. This is the native core route, not the older ad hoc capacity-to-certificate handoff. -/
theorem bottleneck_padded_core_capacity_forces_bypass_certificate :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate
            bottleneckPaddedBypassCoreObservation,
          bottleneckPaddedBypassCoreExtractorContract.extract input =
              Sum.inr cert ∧
            MinimalHiddenAuthority cert := by
  have hcap :
      C_star bottleneckGraph sig (1 / 10) ≤
        bottleneckPaddedAlignmentProtocol.target_capability := by
    change C_star bottleneckGraph sig (1 / 10) ≤ (1 / 10 : ℚ)
    rw [concrete_C_star_values.2.2.2.2]
  have htarget_floor : ∀ block m i,
      bottleneckPaddedAlignmentProtocol.target_capability ≤
        (bottleneckPaddedAlignmentProtocol.code block).encoder
          (bottleneckPaddedAlignmentProtocol.encode block m) i := by
    intro _block _message _i
    rfl
  exact core_capacity_threshold_forces_certificate_from_trace bottleneckGraph sig
    (1 / 10) (by norm_num) (by native_decide)
    bottleneckPaddedAlignmentProtocol
    bottleneckPaddedBypassCoreExtractorContract hcap htarget_floor
    (3 / 2) (by norm_num) bottleneckPaddedAlignmentProtocol_log_rate
    bottleneckPaddedBypassCoreExtractionObservation
    bottleneckPaddedBypassCoreTraceSemantics

/-- Core-vocabulary capacity forcing for the source-evidence-gap fixture. Under the same padded bottleneck protocol and threshold hypotheses as the bypass case, the source-gap observation and trace semantics force a minimal source-evidence-gap certificate beyond the block threshold. The theorem shows the capacity argument is certificate-class independent across the two core fixtures. -/
theorem bottleneck_padded_core_capacity_forces_source_gap_certificate :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate
            bottleneckPaddedSourceGapCoreObservation,
          bottleneckPaddedSourceGapCoreExtractorContract.extract input =
              Sum.inr cert ∧
            MinimalHiddenAuthority cert := by
  have hcap :
      C_star bottleneckGraph sig (1 / 10) ≤
        bottleneckPaddedAlignmentProtocol.target_capability := by
    change C_star bottleneckGraph sig (1 / 10) ≤ (1 / 10 : ℚ)
    rw [concrete_C_star_values.2.2.2.2]
  have htarget_floor : ∀ block m i,
      bottleneckPaddedAlignmentProtocol.target_capability ≤
        (bottleneckPaddedAlignmentProtocol.code block).encoder
          (bottleneckPaddedAlignmentProtocol.encode block m) i := by
    intro _block _message _i
    rfl
  exact core_capacity_threshold_forces_certificate_from_trace bottleneckGraph sig
    (1 / 10) (by norm_num) (by native_decide)
    bottleneckPaddedAlignmentProtocol
    bottleneckPaddedSourceGapCoreExtractorContract hcap htarget_floor
    (3 / 2) (by norm_num) bottleneckPaddedAlignmentProtocol_log_rate
    bottleneckPaddedSourceGapCoreExtractionObservation
    bottleneckPaddedSourceGapCoreTraceSemantics

/-- Named bypass certificate recovered from the core capacity fixture. After the padded converse fires, the theorem does not merely produce some certificate: it identifies the extractor output with the concrete bypass certificate and retains its minimality proof. This is the small finite witness used to check that the abstract forcing theorem lands on the intended branch. -/
theorem bottleneck_padded_core_capacity_forces_named_bypass_certificate :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate
            bottleneckPaddedBypassCoreObservation,
          bottleneckPaddedBypassCoreExtractorContract.extract input =
              Sum.inr cert ∧
            cert = bottleneckPaddedBypassCoreCertificate ∧
              MinimalHiddenAuthority cert := by
  obtain ⟨block_length, hfailed⟩ :=
    bottleneck_padded_alignment_converse_fires
  refine ⟨block_length, ?_⟩
  intro block hblock
  obtain ⟨_message, _hmessage⟩ := hfailed block hblock
  exact ⟨autogenExtractorInput, bottleneckPaddedBypassCoreCertificate,
    rfl, rfl, bottleneckPaddedBypassCoreCertificate_minimal⟩

/-- Named source-evidence-gap certificate recovered from the core capacity fixture. Once the padded converse supplies a failed deployment block, the extractor output is identified with the concrete source-gap certificate and its minimality proof. This pins the source-gap tightness case to a named finite certificate rather than an existential branch. -/
theorem bottleneck_padded_core_capacity_forces_named_source_gap_certificate :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate
            bottleneckPaddedSourceGapCoreObservation,
          bottleneckPaddedSourceGapCoreExtractorContract.extract input =
              Sum.inr cert ∧
            cert = bottleneckPaddedSourceGapCoreCertificate ∧
              MinimalHiddenAuthority cert := by
  obtain ⟨block_length, hfailed⟩ :=
    bottleneck_padded_alignment_converse_fires
  refine ⟨block_length, ?_⟩
  intro block hblock
  obtain ⟨_message, _hmessage⟩ := hfailed block hblock
  exact ⟨autogenExtractorInput, bottleneckPaddedSourceGapCoreCertificate,
    rfl, rfl, bottleneckPaddedSourceGapCoreCertificate_minimal⟩

/-- Tightness comparison: the native observation theorem recovers the original bypass toy case and also covers the source-evidence-gap fixture over the same capacity protocol. -/
theorem native_capacity_extraction_covers_bypass_and_source_gap :
    (∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate bypassPathObservation,
          bypassPathExtractorContract.extract input = Sum.inr cert ∧
            cert = bypassPathCertificate ∧
              MinimalHiddenAuthority cert) ∧
    (∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate sourceGapObservation,
          sourceEvidenceGapExtractorContract.extract input = Sum.inr cert ∧
            cert = sourceEvidenceGapCertificate ∧
              MinimalHiddenAuthority cert) :=
  ⟨bottleneck_padded_capacity_forces_bypass_certificate,
    bottleneck_padded_capacity_forces_named_source_gap_certificate⟩

/-- Drop-test: a clean extractor contract has no certificate branch. This shows the forced-certificate conclusion is not available merely from the kernelization extractor vocabulary once the capacity-failure bridge/converse path is absent. -/
theorem capacity_forcing_drop_test_clean_extractor_no_certificate :
    ¬ ∃ input : ExtractorInput,
      ∃ cert : HiddenAuthorityCertificate cleanKernelizationObservation,
        cleanKernelizationExtractorContract.extract input = Sum.inr cert ∧
          MinimalHiddenAuthority cert := by
  rintro ⟨_input, _cert, hextract, _hminimal⟩
  cases hextract

/-! ## Tightness and drop-test fixtures -/

/-- Raw binary output-word bound induced by a compliant zero-error channel representation. This is the cardinality side of the rate theorem and is useful for small finite fixtures. -/
def ExtractionOutputWordsBound
    (window : ExtractionWindow)
    (emission : CertificateEmissionStream) : Prop :=
  emission.card ≤ 2 ^ window.block

/-- Output-word bound for a zero-error certificate extractor. If an emission stream is represented by a compliant binary capability-response block code, then the number of distinct emitted certificate classes is bounded by the binary output words available in that extraction window. This is the finite cardinality side of the rate converse used by the capacity-aware ELK forcing theorem. -/
theorem hidden_authority_certificate_output_words_bounded
    {n : Nat} {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ} {δ : ℚ}
    {window : ExtractionWindow}
    {emission : CertificateEmissionStream}
    {code : CapabilityResponseBlockCode G s δ window.block}
    (hrespect :
      ExtractorRespectsChannel G s δ window emission code) :
    ExtractionOutputWordsBound window emission := by
  have hmessage :
      Fintype.card code.Message ≤
        Fintype.card (Fin window.block → BinaryDecision) :=
    CapabilityResponseBlockCode.card_message_le_output_words_of_zeroError
      code hrespect.zero_error
  have hcard :
      emission.card ≤ Fintype.card (Fin window.block → BinaryDecision) :=
    le_trans hrespect.emission_card_le_message_card hmessage
  simpa [ExtractionOutputWordsBound, capabilityResponse_output_word_card]
    using hcard

/-- One channel use, the smallest admissible extraction window. -/
def oneUseExtractionWindow : ExtractionWindow where
  block := 1
  positive := by norm_num

/-- Two channel uses, used to show the finite fixtures scale with block size. -/
def twoUseExtractionWindow : ExtractionWindow where
  block := 2
  positive := by norm_num

/-- Tightness fixture: one use has exactly two binary output words. -/
def twoCertificateEmission : CertificateEmissionStream :=
  { HiddenAuthorityCertificateKind.unmodeledEdge,
    HiddenAuthorityCertificateKind.bypassPath }

/-- Tightness fixture: two uses have exactly four binary output words. -/
def fourCertificateEmission : CertificateEmissionStream :=
  { HiddenAuthorityCertificateKind.unmodeledEdge,
    HiddenAuthorityCertificateKind.bypassPath,
    HiddenAuthorityCertificateKind.hiddenOverride,
    HiddenAuthorityCertificateKind.sourceEvidenceGap }

/-- Drop-test fixture: all five certificate classes cannot fit in one binary channel use. -/
def allCertificateEmission : CertificateEmissionStream :=
  HiddenAuthorityCertificateKind.all

/-- One channel use can exactly distinguish the two-class emission fixture. This finite tightness check shows that the output-word bound is sharp at block length one for the small bypass/unmodeled-edge vocabulary slice. -/
theorem two_certificate_one_use_saturates_output_words :
    twoCertificateEmission.card = 2 ^ oneUseExtractionWindow.block := by
  native_decide

/-- Two channel uses can exactly distinguish the four-class emission fixture. The result is the corresponding sharpness check at block length two, separating the scalable finite-code behavior from the one-use drop test for all five certificate classes. -/
theorem four_certificate_two_use_saturates_output_words :
    fourCertificateEmission.card = 2 ^ twoUseExtractionWindow.block := by
  native_decide

/-- Proves `two_certificate_one_use_respects_output_words` for the capacity-aware ELK extraction substrate; it is scoped to the finite certificate fixture. -/
theorem two_certificate_one_use_respects_output_words :
    ExtractionOutputWordsBound oneUseExtractionWindow twoCertificateEmission := by
  simpa [ExtractionOutputWordsBound] using
    (by native_decide :
      twoCertificateEmission.card ≤ 2 ^ oneUseExtractionWindow.block)

/-- Drop-test for the complete five-class certificate vocabulary. With only one binary channel use, the available output words cannot cover all hidden-authority certificate classes. This gives the concrete finite obstruction behind the capacity-rate story: the full vocabulary needs more extraction bandwidth than one binary response. -/
theorem all_five_certificates_exceed_one_use_output_words :
    ¬ ExtractionOutputWordsBound oneUseExtractionWindow allCertificateEmission := by
  simpa [ExtractionOutputWordsBound] using
    (by native_decide :
      ¬ allCertificateEmission.card ≤ 2 ^ oneUseExtractionWindow.block)

/-- Proves `no_zero_use_extraction_window` for the capacity-aware ELK extraction substrate; it is scoped to the finite certificate fixture. -/
theorem no_zero_use_extraction_window :
    ¬ ∃ window : ExtractionWindow, window.block = 0 := by
  rintro ⟨window, hzero⟩
  have hbad : 1 ≤ 0 := by
    simpa [hzero] using window.positive
  exact Nat.not_succ_le_zero 0 hbad

/-- The core-vocabulary route preserves two independent toy discharges, their failed-branch classifiers, and the finite output-word drop-test. These are deliberately named as independent witnesses rather than a single tightness audit predicate. -/
theorem core_capacity_extraction_tightness_five_independent_witnesses :
    (∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate
            bottleneckPaddedBypassCoreObservation,
          bottleneckPaddedBypassCoreExtractorContract.extract input =
              Sum.inr cert ∧
            MinimalHiddenAuthority cert) ∧
    (∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ input : ExtractorInput,
        ∃ cert : HiddenAuthorityCertificate
            bottleneckPaddedSourceGapCoreObservation,
          bottleneckPaddedSourceGapCoreExtractorContract.extract input =
              Sum.inr cert ∧
            MinimalHiddenAuthority cert) ∧
    FailedCapabilityOutputBranchClassified
      bottleneckPaddedBypassCoreExtractionObservation ∧
    FailedCapabilityOutputBranchClassified
      bottleneckPaddedSourceGapCoreExtractionObservation ∧
    ¬ ExtractionOutputWordsBound oneUseExtractionWindow
      allCertificateEmission :=
  ⟨bottleneck_padded_core_capacity_forces_bypass_certificate,
    bottleneck_padded_core_capacity_forces_source_gap_certificate,
    bottleneckPaddedBypassCore_failed_branch_classified,
    bottleneckPaddedSourceGapCore_failed_branch_classified,
    all_five_certificates_exceed_one_use_output_words⟩

end GovGraph

end Legitimacy
