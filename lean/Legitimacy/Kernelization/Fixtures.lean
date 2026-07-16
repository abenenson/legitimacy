/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernelization.Core

/-!
# Legitimacy.Kernelization.Fixtures

Concrete kernelization artifacts shared by the worked examples.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

/-! ## Concrete artifact fixture used by worked examples -/

private def kernelizationCompilationReport : CompilationReport :=
  fun _ => CompilationVerdict.certified

private theorem kernelizationExampleProtocolNonVacuous :
    ProtocolNonVacuous exampleGovernanceGraph := by
  refine ⟨permitTrace, [permitClaim], [permitClaim], ?_⟩
  exact
    ⟨exampleGovernanceTrace_consistent, by
      simp [exampleGovernanceGraph],
      by simp, permitTrace_bounded, by simp, by
      intro c hc
      simpa using hc,
      permitTrace_permitEligible, permitTrace_notRefusal,
      permitTrace_notPermanentEscalation, permitTrace_notDeadlock⟩

private theorem kernelizationCompilationChecks :
    CompilationChecks exampleGovernanceGraph []
      kernelizationCompilationReport := by
  constructor
  · intro p hp
    cases p <;>
      simp [kernelizationCompilationReport, propertyHolds,
        kernelizationExampleProtocolNonVacuous]
    · exact exampleGovernanceGraph_allLegitimacyAxioms.1
    · exact exampleGovernanceGraph_allLegitimacyAxioms.2.1
    · exact exampleGovernanceGraph_allLegitimacyAxioms.2.2.1
    · exact exampleGovernanceGraph_allLegitimacyAxioms.2.2.2
  · intro p hp
    simp at hp

/-- Internal fixture shared by kernelization sub-modules. This is public so
worked-example modules can reuse the same compiled governance artifact, but it
is not part of the stable downstream API surface. -/
noncomputable def kernelizationCompiledGovernance :
    CompiledGovernance :=
  compileGovernance exampleGovernanceGraph []
    kernelizationCompilationReport kernelizationCompilationChecks

/-- Internal fixture shared by kernelization sub-modules. This zero-risk report
keeps example certificates focused on kernel-shape obligations rather than risk
accounting; it is not part of the stable downstream API surface. -/
def kernelizationRiskReport : GovernanceRiskReport where
  factor_exposure :=
    { consistency := 0
      solidarity := 0
      monotonicity := 0
      strategyproofness := 0
      nonvacuity := 0 }
  spectral_gap := 1
  cv_bound := 0
  localizability_bound := 0

/-- Internal fixture shared by kernelization sub-modules. The monitoring plan
names the five governance properties watched by the worked certificates; it is
not part of the stable downstream API surface. -/
def kernelizationMonitoring : MonitoringPlan where
  watches :=
    [ GovernanceProperty.Consistency
    , GovernanceProperty.Solidarity
    , GovernanceProperty.Monotonicity
    , GovernanceProperty.Strategyproofness
    , GovernanceProperty.NonVacuous
    ]

noncomputable def kernelizationExampleArtifact :
    RuleLayerKernelArtifact where
  extract := exampleGovernanceKernelExtractor
  src := autogenExtractorInput
  reachedData := exampleGovernanceKernelData
  trajectory := exampleGovernanceTrajectory
  compiled := kernelizationCompiledGovernance
  report := kernelizationRiskReport
  monitoring := kernelizationMonitoring

/-- Internal source-shape witness shared by kernelization sub-modules. It keeps
the bounded-extractor examples tied to the concrete AutoGen-sized source input,
but is not part of the stable downstream API surface. -/
lemma kernelizationExampleSourceWellFormed :
    autogenExtractorInput.WellFormed := by
  simp [ExtractorInput.WellFormed, autogenExtractorInput]

/-- Internal semantic-kernel witness shared by kernelization sub-modules. The
public visibility is for cross-file worked examples, not for stable downstream
API commitments. -/
theorem kernelizationExampleSemanticKernel :
    (kernelizationExampleArtifact.extract
      kernelizationExampleArtifact.src).IsSemanticKernel := by
  exact bounded_extractor_contract_sound
    exampleGovernanceKernelExtractor
    exampleGovernanceKernelExtractor_contract
    autogenExtractorInput
    kernelizationExampleSourceWellFormed

noncomputable def kernelizationSacrificeStepCertificate :
    MonitoredSacrificeCertificate
      exampleGovernanceKernelData exampleGovernanceWideSignalKernelData where
  sacrificed := SacrificedAxiom.kernel KernelAxiom.SpectralWellConnected
  step := exampleGovernanceWideSignalStep
  claim_profile := [permitClaim]
  claimant := permitClaim.id
  aggregator_witness := none
  stateful_violation := none
  compiled := kernelizationCompiledGovernance
  monitoring := kernelizationMonitoring
  graph_bound := rfl
  monitoring_obligation :=
    { fires := True
      decidable_fires := inferInstance
      fired := trivial
      bound_exceedance :=
        MonitoringBoundExceedance.oneFailureOverZero
          kernelizationCompiledGovernance
      runtime_observation :=
        MonitoringRuntimeObservation.ofSacrifice
          (SacrificedAxiom.kernel KernelAxiom.SpectralWellConnected)
          kernelizationCompiledGovernance kernelizationMonitoring
      ledger_emission :=
        MonitoringLedgerEmission.ofSacrifice
          (SacrificedAxiom.kernel KernelAxiom.SpectralWellConnected)
          kernelizationCompiledGovernance kernelizationMonitoring }

noncomputable def kernelizationSacrificeStepTrajectory :
    KernelGovernedTrajectory exampleGovernedSystem
      exampleGovernanceKernelData exampleGovernanceWideSignalKernelData :=
  KernelGovernedTrajectory.sacrifice_step
    kernelizationSacrificeStepCertificate
    (KernelGovernedTrajectory.singleInvariantStep
      (KernelStep.refl exampleGovernanceWideSignalKernelData)
      exampleGovernanceWideSignalSemanticKernel)

noncomputable def kernelizationSacrificeStepArtifact :
    RuleLayerKernelArtifact where
  extract := exampleGovernanceKernelExtractor
  src := autogenExtractorInput
  reachedData := exampleGovernanceWideSignalKernelData
  trajectory := kernelizationSacrificeStepTrajectory
  compiled := kernelizationCompiledGovernance
  report := kernelizationRiskReport
  monitoring := kernelizationMonitoring

end Safety

end Legitimacy
