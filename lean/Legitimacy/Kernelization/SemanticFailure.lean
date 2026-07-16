/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernelization.StructuralExamples
import Legitimacy.Results.SemanticBridge

/-!
# Legitimacy.Kernelization.SemanticFailure

Semantic-bridge failure certificates and their minimality witnesses.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

/-! ## Semantic-bridge failure examples -/

private noncomputable def semanticFailureCounterexampleN : Nat :=
  Classical.choose
    runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected

private noncomputable def semanticFailureCounterexampleSys :
    GovernedSystem semanticFailureCounterexampleN :=
  Classical.choose
    (Classical.choose_spec
      runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected)

private noncomputable def semanticFailureCounterexampleData :
    LegitimacyKernelData semanticFailureCounterexampleSys :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected))

private theorem semanticFailureCounterexample_spec :
    IsLegitimacyKernel semanticFailureCounterexampleData ∧
      AllLegitimacyAxioms semanticFailureCounterexampleSys.graph ∧
        ¬ SpectralWellConnected
          semanticFailureCounterexampleData.spectralGraph
          semanticFailureCounterexampleData.spectralSignal
          semanticFailureCounterexampleSys.graph.weightedSize_atLeastTwo :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected))

private noncomputable def semanticFailureExtractedArtifact :
    ExtractedKernelArtifact where
  n := semanticFailureCounterexampleN
  sys := semanticFailureCounterexampleSys
  data := semanticFailureCounterexampleData

private noncomputable def semanticFailureExtractor : KernelExtractor :=
  fun _ => semanticFailureExtractedArtifact

noncomputable def semanticBridgeFailureArtifact :
    RuleLayerKernelArtifact where
  extract := semanticFailureExtractor
  src := autogenExtractorInput
  reachedData := semanticFailureCounterexampleData
  trajectory := KernelGovernedTrajectory.refl semanticFailureCounterexampleData
  compiled := kernelizationCompiledGovernance
  report := kernelizationRiskReport
  monitoring := kernelizationMonitoring

private theorem semanticFailureExtractor_runtime_kernel :
    IsLegitimacyKernel
      (semanticBridgeFailureArtifact.extract
        semanticBridgeFailureArtifact.src).data := by
  exact semanticFailureCounterexample_spec.1

private theorem semanticFailureExtractor_semantic_bridge_fails :
    ¬ KernelSemanticBridge
      (semanticBridgeFailureArtifact.extract
        semanticBridgeFailureArtifact.src).data := by
  intro hbridge
  exact semanticFailureCounterexample_spec.2.2
    (KernelSemanticBridge.spectralWellConnected hbridge)

private theorem semanticFailureExtractor_not_semantic :
    ¬ (semanticBridgeFailureArtifact.extract
      semanticBridgeFailureArtifact.src).IsSemanticKernel := by
  intro hsemantic
  exact semanticFailureExtractor_semantic_bridge_fails
    hsemantic.semanticBridge

noncomputable def semanticBridgeFailureObservation :
    GovernanceKernelizationObservation semanticBridgeFailureArtifact where
  reported := cleanAuthorityGraph
  effective := cleanAuthorityGraph
  sourceEdges := [{ fromNode := "principal", toNode := "reviewer" }]
  reportedSemanticBridgeClean := true

private theorem semanticBridgeFailureObservation_reported_clean_surface :
    AuthorityExtensionallyEquivalent semanticBridgeFailureObservation.reported
        semanticBridgeFailureObservation.effective ∧
      SourceEvidenceComplete semanticBridgeFailureObservation := by
  constructor
  · constructor <;> intro edge <;> simp [semanticBridgeFailureObservation,
      cleanAuthorityGraph, HasAuthorityEdge, HasAuthorityOverride]
  · intro edge hedge
    simpa [semanticBridgeFailureObservation, cleanAuthorityGraph,
      SourceDerivesEdge, HasAuthoritySurface, HasAuthorityEdge,
      HasAuthorityOverride] using hedge

def semanticBridgeFailureCertificate :
    HiddenAuthorityCertificate semanticBridgeFailureObservation :=
  HiddenAuthorityCertificate.semanticBridgeFailure
    { failure_locus := SemanticFailureLocus.semanticBridge
      reported_semantic_bridge_clean := rfl
      reported_clean_surface :=
        semanticBridgeFailureObservation_reported_clean_surface
      source_wellFormed := kernelizationExampleSourceWellFormed
      semantic_failure := semanticFailureExtractor_not_semantic }

theorem semanticBridgeFailureCertificate_minimal :
    MinimalHiddenAuthority semanticBridgeFailureCertificate := by
  change
    semanticBridgeFailureObservation.reportedSemanticBridgeClean = true ∧
      semanticBridgeFailureArtifact.src.WellFormed ∧
        SemanticFailureLocusMinimal semanticBridgeFailureArtifact
          SemanticFailureLocus.semanticBridge
  refine ⟨rfl, kernelizationExampleSourceWellFormed, ?_⟩
  constructor
  · exact semanticFailureExtractor_semantic_bridge_fails
  · intro earlier hprecedes hfails
    cases earlier with
    | runtimeKernel =>
        exact hfails semanticFailureExtractor_runtime_kernel
    | semanticBridge =>
        cases hprecedes

def semanticBridgeFailureWrongLocusCertificate :
    HiddenAuthorityCertificate semanticBridgeFailureObservation :=
  HiddenAuthorityCertificate.semanticBridgeFailure
    { failure_locus := SemanticFailureLocus.runtimeKernel
      reported_semantic_bridge_clean := rfl
      reported_clean_surface :=
        semanticBridgeFailureObservation_reported_clean_surface
      source_wellFormed := kernelizationExampleSourceWellFormed
      semantic_failure := semanticFailureExtractor_not_semantic }

theorem SemanticBridgeFailureMinimal_excludes_wrong_locus :
    ¬ MinimalHiddenAuthority semanticBridgeFailureWrongLocusCertificate := by
  intro hminimal
  exact hminimal.2.2.1 semanticFailureExtractor_runtime_kernel

theorem SemanticBridgeFailureMinimal_independent_of_witness_fields :
    (match semanticBridgeFailureWrongLocusCertificate with
      | HiddenAuthorityCertificate.semanticBridgeFailure _ =>
          semanticBridgeFailureObservation.reportedSemanticBridgeClean = true ∧
            semanticBridgeFailureArtifact.src.WellFormed ∧
              ¬ (semanticBridgeFailureArtifact.extract
                semanticBridgeFailureArtifact.src).IsSemanticKernel
      | _ => False) ∧
      ¬ MinimalHiddenAuthority semanticBridgeFailureWrongLocusCertificate := by
  constructor
  · exact ⟨rfl, kernelizationExampleSourceWellFormed,
      semanticFailureExtractor_not_semantic⟩
  · exact SemanticBridgeFailureMinimal_excludes_wrong_locus

theorem SemanticBridgeFailureMinimal_nonvacuous :
    ∃ witness : SemanticBridgeFailureWitness semanticBridgeFailureObservation,
      MinimalHiddenAuthority
        (HiddenAuthorityCertificate.semanticBridgeFailure witness) := by
  refine ⟨?_, ?_⟩
  · exact
      { failure_locus := SemanticFailureLocus.semanticBridge
        reported_semantic_bridge_clean := rfl
        reported_clean_surface :=
          semanticBridgeFailureObservation_reported_clean_surface
        source_wellFormed := kernelizationExampleSourceWellFormed
        semantic_failure := semanticFailureExtractor_not_semantic }
  · exact semanticBridgeFailureCertificate_minimal

theorem semanticBridgeFailure_not_clean :
    ¬ KernelizationClean semanticBridgeFailureObservation := by
  exact semanticBridgeFailure_minimal_incompatible_clean
    { failure_locus := SemanticFailureLocus.semanticBridge
      reported_semantic_bridge_clean := rfl
      reported_clean_surface :=
        semanticBridgeFailureObservation_reported_clean_surface
      source_wellFormed := kernelizationExampleSourceWellFormed
      semantic_failure := semanticFailureExtractor_not_semantic }
    semanticBridgeFailureCertificate_minimal

theorem semanticBridgeFailure_operationally_distinct_from_structural_certs :
    AuthorityEdgeDifference semanticBridgeFailureObservation.effective
        semanticBridgeFailureObservation.reported = [] ∧
      AuthorityOverrideDifference semanticBridgeFailureObservation.effective
          semanticBridgeFailureObservation.reported = [] ∧
        SourceEvidenceComplete semanticBridgeFailureObservation ∧
          MinimalHiddenAuthority semanticBridgeFailureCertificate ∧
            ¬ KernelizationClean semanticBridgeFailureObservation := by
  refine ⟨?_, ?_, ?_, semanticBridgeFailureCertificate_minimal,
    semanticBridgeFailure_not_clean⟩
  · simp [AuthorityEdgeDifference, semanticBridgeFailureObservation,
      cleanAuthorityGraph]
  · simp [AuthorityOverrideDifference, semanticBridgeFailureObservation,
      cleanAuthorityGraph]
  · exact semanticBridgeFailureObservation_reported_clean_surface.2

end Safety

end Legitimacy
