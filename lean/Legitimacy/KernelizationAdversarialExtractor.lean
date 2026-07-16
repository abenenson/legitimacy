/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernelization

/-!
# Adversarial kernelization extractors

This module records the strongest adversarial-extractor theorem supported by
the current kernelization substrate.

Honest restate: the substrate does not yet contain a separate semantic model of
all possible adversarial extractors. What it does contain is the bounded
`KernelizationExtractorContract`, whose certificate branch is sound. Therefore
an adversarial extractor is represented as a contract over the same
kernelization observation as an honest extractor, and a deviation is a concrete
run that takes the certificate branch. Under that operational hypothesis, the
deviation necessarily leaves a minimal witness in one of the five existing
`HiddenAuthorityCertificate` constructors.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

/-! ## Five-constructor exhaustiveness -/

/-- A witness-bearing hidden-authority certificate belongs to exactly the
existing five typed certificate constructors. This predicate intentionally keeps
the witness payloads instead of erasing to a finite label. -/
def HiddenAuthorityCertificateFromFiveKinds
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation) : Prop :=
  (∃ witness : UnmodeledEdgeWitness observation,
      cert = HiddenAuthorityCertificate.unmodeledEdge witness) ∨
    (∃ witness : BypassPathWitness observation,
      cert = HiddenAuthorityCertificate.bypassPath witness) ∨
      (∃ witness : HiddenOverrideWitness observation,
        cert = HiddenAuthorityCertificate.hiddenOverride witness) ∨
        (∃ witness : SourceEvidenceGapWitness observation,
          cert = HiddenAuthorityCertificate.sourceEvidenceGap witness) ∨
          (∃ witness : SemanticBridgeFailureWitness observation,
            cert = HiddenAuthorityCertificate.semanticBridgeFailure witness)

theorem hiddenAuthorityCertificate_from_five_kinds
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation) :
    HiddenAuthorityCertificateFromFiveKinds cert := by
  cases cert with
  | unmodeledEdge witness =>
      exact Or.inl ⟨witness, rfl⟩
  | bypassPath witness =>
      exact Or.inr (Or.inl ⟨witness, rfl⟩)
  | hiddenOverride witness =>
      exact Or.inr (Or.inr (Or.inl ⟨witness, rfl⟩))
  | sourceEvidenceGap witness =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨witness, rfl⟩)))
  | semanticBridgeFailure witness =>
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨witness, rfl⟩)))

/-! ## Adversarial runs -/

/-- A concrete adversarial deviation is a run of a kernelization extractor that
returns the certificate branch. The contract's `certSound` field supplies the
minimality proof; this predicate supplies the operational fact that the
adversarial run did deviate from the clean branch. -/
def AdversarialExtractorDeviation
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (adversarial : KernelizationExtractorContract observation)
    (input : ExtractorInput) : Prop :=
  ∃ cert : HiddenAuthorityCertificate observation,
    adversarial.extract input = Sum.inr cert

/-- The honest and adversarial extractors are run over the same observation.
The honest run takes the clean branch, while the adversarial run deviates into
the certificate branch. -/
structure HonestEquivalentAdversarialRun
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (honest adversarial : KernelizationExtractorContract observation)
    (input : ExtractorInput) where
  honest_clean :
    ∃ witness : KernelizationCleanWitness observation,
      honest.extract input = Sum.inl witness
  adversarial_deviation :
    AdversarialExtractorDeviation adversarial input

/-- Kernelization honesty under an adversarial extractor.

Every adversarial run that is observation-equivalent to an honest clean run and
deviates into the certificate branch produces a minimal typed hidden-authority
certificate from the existing five-constructor vocabulary. -/
theorem kernelization_honesty_under_adversarial_extractor
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (honest adversarial : KernelizationExtractorContract observation)
    (input : ExtractorInput)
    (run : HonestEquivalentAdversarialRun honest adversarial input) :
    ∃ cert : HiddenAuthorityCertificate observation,
      adversarial.extract input = Sum.inr cert ∧
        MinimalHiddenAuthority cert ∧
          HiddenAuthorityCertificateFromFiveKinds cert := by
  rcases run.adversarial_deviation with ⟨cert, hextract⟩
  exact ⟨cert, hextract,
    adversarial.certSound input cert hextract,
    hiddenAuthorityCertificate_from_five_kinds cert⟩

/-! ## Worked adversarial extractor instance -/

theorem bypassPathObservation_clean :
    KernelizationClean bypassPathObservation := by
  refine ⟨?_, ?_, cleanKernelizationObservation_clean.2.2⟩
  · constructor <;> intro edge <;> simp [bypassPathObservation,
      bypassGraph, HasAuthorityEdge, HasAuthorityOverride]
  · intro edge hedge
    simpa [bypassPathObservation, bypassGraph, SourceDerivesEdge,
      HasAuthoritySurface, HasAuthorityEdge, HasAuthorityOverride] using hedge

def bypassPathHonestCleanWitness :
    KernelizationCleanWitness bypassPathObservation where
  input := autogenExtractorInput
  reported_equiv := bypassPathObservation_clean.1
  source_complete := bypassPathObservation_clean.2.1
  semantic_kernel := bypassPathObservation_clean.2.2

def bypassPathHonestExtractorContract :
    KernelizationExtractorContract bypassPathObservation where
  extract := fun _ => Sum.inl bypassPathHonestCleanWitness
  cleanSound := by
    intro _input _witness hextract
    cases hextract
    exact kernelizationClean_of_witness bypassPathHonestCleanWitness
  certSound := by
    intro _input _cert hextract
    cases hextract

/-- Concrete adversarial extractor instance: on the same bypass observation as
the honest extractor, this extractor takes the certificate branch and emits the
bypass-path certificate. -/
def adversarialBypassExtractorContract :
    KernelizationExtractorContract bypassPathObservation :=
  bypassPathExtractorContract

theorem adversarialBypassExtractor_run :
    HonestEquivalentAdversarialRun bypassPathHonestExtractorContract
      adversarialBypassExtractorContract autogenExtractorInput where
  honest_clean := ⟨bypassPathHonestCleanWitness, rfl⟩
  adversarial_deviation := ⟨bypassPathCertificate, rfl⟩

theorem adversarialBypassExtractor_produces_bypass_certificate :
    ∃ cert : HiddenAuthorityCertificate bypassPathObservation,
      adversarialBypassExtractorContract.extract autogenExtractorInput =
          Sum.inr cert ∧
        cert = bypassPathCertificate ∧
          MinimalHiddenAuthority cert ∧
            ∃ witness : BypassPathWitness bypassPathObservation,
              cert = HiddenAuthorityCertificate.bypassPath witness := by
  refine ⟨bypassPathCertificate, rfl, rfl,
    bypassPathCertificate_minimal, ?_⟩
  dsimp [bypassPathCertificate]
  exact ⟨_, rfl⟩

theorem kernelization_honesty_under_adversarial_extractor_worked_bypass :
    ∃ cert : HiddenAuthorityCertificate bypassPathObservation,
      adversarialBypassExtractorContract.extract autogenExtractorInput =
          Sum.inr cert ∧
        MinimalHiddenAuthority cert ∧
          HiddenAuthorityCertificateFromFiveKinds cert :=
  kernelization_honesty_under_adversarial_extractor
    bypassPathHonestExtractorContract adversarialBypassExtractorContract
    autogenExtractorInput adversarialBypassExtractor_run

/-! ## Tightness bars and discharge discipline -/

/-- Tightness bars: each of the five certificate constructors has a concrete
minimal witness in the current kernelization examples. -/
theorem adversarial_extractor_five_certificate_kinds_nonvacuous :
    (∃ cert : HiddenAuthorityCertificate unmodeledEdgeObservation,
      MinimalHiddenAuthority cert ∧
        ∃ witness : UnmodeledEdgeWitness unmodeledEdgeObservation,
          cert = HiddenAuthorityCertificate.unmodeledEdge witness) ∧
    (∃ cert : HiddenAuthorityCertificate bypassPathObservation,
      MinimalHiddenAuthority cert ∧
        ∃ witness : BypassPathWitness bypassPathObservation,
          cert = HiddenAuthorityCertificate.bypassPath witness) ∧
    (∃ cert : HiddenAuthorityCertificate hiddenOverrideObservation,
      MinimalHiddenAuthority cert ∧
        ∃ witness : HiddenOverrideWitness hiddenOverrideObservation,
          cert = HiddenAuthorityCertificate.hiddenOverride witness) ∧
    (∃ cert : HiddenAuthorityCertificate sourceGapObservation,
      MinimalHiddenAuthority cert ∧
        ∃ witness : SourceEvidenceGapWitness sourceGapObservation,
          cert = HiddenAuthorityCertificate.sourceEvidenceGap witness) ∧
    (∃ cert : HiddenAuthorityCertificate semanticBridgeFailureObservation,
      MinimalHiddenAuthority cert ∧
        ∃ witness :
            SemanticBridgeFailureWitness semanticBridgeFailureObservation,
          cert = HiddenAuthorityCertificate.semanticBridgeFailure witness) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨unmodeledEdgeCertificate, unmodeledEdgeCertificate_minimal, ?_⟩
    dsimp [unmodeledEdgeCertificate]
    exact ⟨_, rfl⟩
  · refine ⟨bypassPathCertificate, bypassPathCertificate_minimal, ?_⟩
    dsimp [bypassPathCertificate]
    exact ⟨_, rfl⟩
  · refine ⟨hiddenOverrideCertificate, hiddenOverrideCertificate_minimal, ?_⟩
    dsimp [hiddenOverrideCertificate]
    exact ⟨_, rfl⟩
  · refine ⟨sourceEvidenceGapCertificate, sourceEvidenceGapCertificate_minimal,
      ?_⟩
    dsimp [sourceEvidenceGapCertificate]
    exact ⟨_, rfl⟩
  · refine ⟨semanticBridgeFailureCertificate,
      semanticBridgeFailureCertificate_minimal, ?_⟩
    dsimp [semanticBridgeFailureCertificate]
    exact ⟨_, rfl⟩

/-- Nine discharge checks used by the adversarial extractor theorem: clean
branch soundness, certificate branch soundness, five-kind exhaustiveness,
certificate-branch existence, the concrete honest branch, the concrete
adversarial branch, the concrete bypass kind, padded-route rejection, and wrong
semantic-locus rejection. -/
theorem adversarial_extractor_discharge_discipline :
    (∀ {artifact : RuleLayerKernelArtifact}
      {observation : GovernanceKernelizationObservation artifact}
      (contract : KernelizationExtractorContract observation)
      (input : ExtractorInput)
      (witness : KernelizationCleanWitness observation),
        contract.extract input = Sum.inl witness →
          KernelizationClean observation) ∧
    (∀ {artifact : RuleLayerKernelArtifact}
      {observation : GovernanceKernelizationObservation artifact}
      (contract : KernelizationExtractorContract observation)
      (input : ExtractorInput)
      (cert : HiddenAuthorityCertificate observation),
        contract.extract input = Sum.inr cert →
          MinimalHiddenAuthority cert) ∧
    (∀ {artifact : RuleLayerKernelArtifact}
      {observation : GovernanceKernelizationObservation artifact}
      (cert : HiddenAuthorityCertificate observation),
        HiddenAuthorityCertificateFromFiveKinds cert) ∧
    (∀ {artifact : RuleLayerKernelArtifact}
      {observation : GovernanceKernelizationObservation artifact}
      (contract : KernelizationExtractorContract observation)
      (input : ExtractorInput),
        AdversarialExtractorDeviation contract input →
          ∃ cert : HiddenAuthorityCertificate observation,
            contract.extract input = Sum.inr cert ∧
              MinimalHiddenAuthority cert) ∧
    bypassPathHonestExtractorContract.extract autogenExtractorInput =
      Sum.inl bypassPathHonestCleanWitness ∧
    adversarialBypassExtractorContract.extract autogenExtractorInput =
      Sum.inr bypassPathCertificate ∧
    (∃ witness : BypassPathWitness bypassPathObservation,
      bypassPathCertificate = HiddenAuthorityCertificate.bypassPath witness) ∧
    ¬ BypassPathMinimal paddedBypassObservation.reported
      paddedBypassWitness ∧
    ¬ MinimalHiddenAuthority semanticBridgeFailureWrongLocusCertificate := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro _artifact _observation contract input witness hextract
    exact contract.cleanSound input witness hextract
  · intro _artifact _observation contract input cert hextract
    exact contract.certSound input cert hextract
  · intro _artifact _observation cert
    exact hiddenAuthorityCertificate_from_five_kinds cert
  · intro _artifact _observation contract input hdeviation
    rcases hdeviation with ⟨cert, hextract⟩
    exact ⟨cert, hextract, contract.certSound input cert hextract⟩
  · dsimp [bypassPathCertificate]
    exact ⟨_, rfl⟩
  · exact BypassPathMinimal_excludes_padded_route.2
  · exact SemanticBridgeFailureMinimal_excludes_wrong_locus

end Safety

end Legitimacy
