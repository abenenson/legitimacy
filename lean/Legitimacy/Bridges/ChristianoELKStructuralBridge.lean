/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Bridges.ELKCorrespondence

/-!
# Christiano ELK structural bridge

This module gives a narrow structural bridge to Christiano, Cotra, and Xu,
"Eliciting Latent Knowledge: How to Tell if Your Eyes Deceive You" (ARC,
2021). The bridge covers only the repository's represented slice: minimal
hidden-authority certificates that already live in the kernelization substrate
and are matched by one of the witness-bearing `ELKDiscrepancy` constructors in
`Legitimacy.Bridges.ELKCorrespondence`.

It is not a full formalization of ELK, reporter training, ontology
identification, or all possible latent-knowledge failures. The
`unsupportedWorldModelShift` constructor remains outside the correspondence as
a tightness witness.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

/-- The represented Christiano-ELK slice: a discrepancy structurally extracts
as a kernel hidden-authority certificate exactly when the existing
witness-bearing correspondence accepts it. -/
def ELKStructuralExtracts
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (disc : ELKDiscrepancy)
    (cert : HiddenAuthorityCertificate observation) : Prop :=
  ELKDiscrepancyMatchesCert disc cert

/-- Minimal hidden-authority certificates are covered by the represented ELK
discrepancy vocabulary. This is a structural correspondence over the five
certificate classes in the substrate, not a general ELK completeness theorem. -/
theorem christiano_elk_structural_correspondence
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation)
    (hminimal : MinimalHiddenAuthority cert) :
    ∃ disc : ELKDiscrepancy, ELKStructuralExtracts disc cert := by
  exact (hidden_authority_cert_to_elk_correspondence cert).1 hminimal

/-- Tightness fixture: source-evidence gaps are one represented ELK structural
case, not an informal citation-only mapping. -/
theorem source_gap_elk_structural_fixture :
    ∃ disc : ELKDiscrepancy,
      ELKStructuralExtracts disc sourceEvidenceGapCertificate := by
  exact christiano_elk_structural_correspondence
    sourceEvidenceGapCertificate sourceEvidenceGapCertificate_minimal

/-- Tightness fixture: semantic-bridge failures are also represented by a
witness-bearing ELK discrepancy. -/
theorem semantic_bridge_failure_elk_structural_fixture :
    ∃ disc : ELKDiscrepancy,
      ELKStructuralExtracts disc semanticBridgeFailureCertificate := by
  exact christiano_elk_structural_correspondence
    semanticBridgeFailureCertificate semanticBridgeFailureCertificate_minimal

/-- Drop-test: a named world-model shift outside the five certificate classes
does not match any hidden-authority certificate through this bridge. -/
theorem unsupported_world_model_shift_has_no_hidden_authority_certificate
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (label : String) (reported : AuthorityGraph)
    (cert : HiddenAuthorityCertificate observation) :
    ¬ ELKStructuralExtracts
      (ELKDiscrepancy.unsupportedWorldModelShift label reported) cert := by
  intro hmatch
  rcases hmatch with ⟨hcase⟩
  cases hcase with
  | sensorTampering _ _ hdisc _ => cases hdisc
  | multiHopRouteEvasion _ _ hdisc _ => cases hdisc
  | dominantOverrideDiscrepancy _ _ hdisc _ => cases hdisc
  | materializedSourceDiscrepancy _ _ hdisc _ => cases hdisc
  | semanticBridgeDiscrepancy _ _ hdisc _ => cases hdisc

/-- Concrete right-disjunct witness: unsupported ontology shifts remain
outside the current structural ELK bridge. -/
theorem unsupported_world_model_shift_right_disjunct :
    ∀ cert : HiddenAuthorityCertificate sourceGapObservation,
      ¬ ELKStructuralExtracts
        (ELKDiscrepancy.unsupportedWorldModelShift
          "unsupported ontology shift" sourceGapObservation.reported) cert := by
  intro cert
  exact unsupported_world_model_shift_has_no_hidden_authority_certificate
    "unsupported ontology shift" sourceGapObservation.reported cert

end Safety

end Legitimacy
