/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernelization.SemanticFailure

/-!
# Legitimacy.Kernelization.EndToEnd

End-to-end kernelization-honesty extractor examples.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

/-! ## End-to-end kernelization-honesty examples -/

def cleanKernelizationCleanWitness :
    KernelizationCleanWitness cleanKernelizationObservation where
  input := autogenExtractorInput
  reported_equiv := cleanKernelizationObservation_clean.1
  source_complete := cleanKernelizationObservation_clean.2.1
  semantic_kernel := cleanKernelizationObservation_clean.2.2

def cleanKernelizationExtractorContract :
    KernelizationExtractorContract cleanKernelizationObservation where
  extract := fun _ => Sum.inl cleanKernelizationCleanWitness
  cleanSound := by
    intro _input witness hextract
    cases hextract
    exact kernelizationClean_of_witness cleanKernelizationCleanWitness
  certSound := by
    intro _input _cert hextract
    cases hextract

theorem cleanKernelization_honesty :
    KernelizationHonesty cleanKernelizationObservation := by
  exact kernelization_honesty kernelizationExampleArtifact
    cleanKernelizationObservation cleanKernelizationExtractorContract

def sacrificeStepKernelizationCleanWitness :
    KernelizationCleanWitness sacrificeStepCleanObservation where
  input := autogenExtractorInput
  reported_equiv := sacrificeStepCleanObservation_clean.1
  source_complete := sacrificeStepCleanObservation_clean.2.1
  semantic_kernel := sacrificeStepCleanObservation_clean.2.2

def sacrificeStepKernelizationExtractorContract :
    KernelizationExtractorContract sacrificeStepCleanObservation where
  extract := fun _ => Sum.inl sacrificeStepKernelizationCleanWitness
  cleanSound := by
    intro _input _witness hextract
    cases hextract
    exact kernelizationClean_of_witness
      sacrificeStepKernelizationCleanWitness
  certSound := by
    intro _input _cert hextract
    cases hextract

theorem sacrificeStepKernelization_honesty :
    KernelizationHonesty sacrificeStepCleanObservation := by
  exact kernelization_honesty kernelizationSacrificeStepArtifact
    sacrificeStepCleanObservation sacrificeStepKernelizationExtractorContract

def unmodeledEdgeExtractorContract :
    KernelizationExtractorContract unmodeledEdgeObservation where
  extract := fun _ => Sum.inr unmodeledEdgeCertificate
  cleanSound := by
    intro _input _witness hextract
    cases hextract
  certSound := by
    intro _input _cert hextract
    cases hextract
    exact unmodeledEdgeCertificate_minimal

theorem unmodeledEdgeKernelization_honesty :
    KernelizationHonesty unmodeledEdgeObservation := by
  exact kernelization_honesty kernelizationExampleArtifact
    unmodeledEdgeObservation unmodeledEdgeExtractorContract

def bypassPathExtractorContract :
    KernelizationExtractorContract bypassPathObservation where
  extract := fun _ => Sum.inr bypassPathCertificate
  cleanSound := by
    intro _input _witness hextract
    cases hextract
  certSound := by
    intro _input _cert hextract
    cases hextract
    exact bypassPathCertificate_minimal

/-- Sleeper-agent-style worked instance: a disclosed user-to-router and
router-to-admin route effectively grants admin authority while the direct
user-to-admin authority edge is absent from the reported surface. The original
sleeper-agent audit remains in `Legitimacy.Audits.SleeperAgent`; this example
uses the same structural hidden-route pattern without modifying that file. -/
theorem sleeperStyleBypassKernelization_honesty :
    KernelizationHonesty bypassPathObservation := by
  exact kernelization_honesty kernelizationExampleArtifact
    bypassPathObservation bypassPathExtractorContract

def hiddenOverrideExtractorContract :
    KernelizationExtractorContract hiddenOverrideObservation where
  extract := fun _ => Sum.inr hiddenOverrideCertificate
  cleanSound := by
    intro _input _witness hextract
    cases hextract
  certSound := by
    intro _input _cert hextract
    cases hextract
    exact hiddenOverrideCertificate_minimal

theorem hiddenOverrideKernelization_honesty :
    KernelizationHonesty hiddenOverrideObservation := by
  exact kernelization_honesty kernelizationExampleArtifact
    hiddenOverrideObservation hiddenOverrideExtractorContract

def sourceEvidenceGapExtractorContract :
    KernelizationExtractorContract sourceGapObservation where
  extract := fun _ => Sum.inr sourceEvidenceGapCertificate
  cleanSound := by
    intro _input _witness hextract
    cases hextract
  certSound := by
    intro _input _cert hextract
    cases hextract
    exact sourceEvidenceGapCertificate_minimal

theorem sourceEvidenceGapKernelization_honesty :
    KernelizationHonesty sourceGapObservation := by
  exact kernelization_honesty kernelizationExampleArtifact
    sourceGapObservation sourceEvidenceGapExtractorContract

def semanticBridgeFailureExtractorContract :
    KernelizationExtractorContract semanticBridgeFailureObservation where
  extract := fun _ => Sum.inr semanticBridgeFailureCertificate
  cleanSound := by
    intro _input _witness hextract
    cases hextract
  certSound := by
    intro _input _cert hextract
    cases hextract
    exact semanticBridgeFailureCertificate_minimal

theorem semanticBridgeFailureKernelization_honesty :
    KernelizationHonesty semanticBridgeFailureObservation := by
  exact kernelization_honesty semanticBridgeFailureArtifact
    semanticBridgeFailureObservation semanticBridgeFailureExtractorContract

/-- The kernelization worked artifact is not a length-zero trajectory: it uses
the concrete two-step invariant trajectory from the kernel-safety examples. -/
theorem kernelizationExampleArtifact_trajectory_nonreflexive :
    kernelizationExampleArtifact.trajectory.length = 2 := by
  rfl

theorem kernelizationSacrificeStepCertificate_step_nonrefl :
    exampleGovernanceKernelData ≠ exampleGovernanceWideSignalKernelData :=
  exampleGovernanceWideSignalStep_nonrefl

theorem kernelizationSacrificeStepArtifact_trajectory_nonreflexive :
    kernelizationSacrificeStepArtifact.trajectory.length = 2 := by
  rfl

theorem kernelizationSacrificeStepArtifact_has_sacrifice_step :
    KernelGovernedTrajectory.HasSacrificeStepAt
      kernelizationSacrificeStepArtifact.trajectory 0 := by
  exact KernelGovernedTrajectory.HasSacrificeStepAt.here
    kernelizationSacrificeStepCertificate
    (KernelGovernedTrajectory.singleInvariantStep
      (KernelStep.refl exampleGovernanceWideSignalKernelData)
      exampleGovernanceWideSignalSemanticKernel)

/-- Non-reflexive trajectory worked example combining the T-reduction theorem
with the repaired kernelization-honesty extractor chain. The audit obligations
are kept explicit because the deployment-side live path is the protocol theorem's
input, while the artifact's trajectory is the concrete invariant-step chain. -/
theorem kernelization_nonreflexiveTrajectory_reduces_and_honest
    (audit : RuleLayerKernelAuditObligations kernelizationExampleArtifact) :
    noSilentRuleLayerDegradation kernelizationExampleArtifact ∧
      Nonempty (KernelAuditConjunction kernelizationExampleArtifact) ∧
        KernelizationHonesty cleanKernelizationObservation := by
  have hreduction :=
    safety_spec_reduces_to_kernel_audit kernelizationExampleArtifact audit
  exact ⟨hreduction.1, hreduction.2, cleanKernelization_honesty⟩

/-- Sacrifice-step trajectory worked example combining the T-reduction theorem
with the kernelization-honesty extractor chain. The trajectory head is the
non-reflexive wide-signal kernel step carried by a monitored sacrifice
certificate, followed by one invariant-preserving tail step. -/
theorem kernelization_sacrificeStepTrajectory_reduces_and_honest
    (audit :
      RuleLayerKernelAuditObligations kernelizationSacrificeStepArtifact) :
    noSilentRuleLayerDegradation kernelizationSacrificeStepArtifact ∧
      Nonempty (KernelAuditConjunction kernelizationSacrificeStepArtifact) ∧
        KernelizationHonesty sacrificeStepCleanObservation := by
  have hreduction :=
    safety_spec_reduces_to_kernel_audit
      kernelizationSacrificeStepArtifact audit
  exact ⟨hreduction.1, hreduction.2, sacrificeStepKernelization_honesty⟩

end Safety

end Legitimacy
