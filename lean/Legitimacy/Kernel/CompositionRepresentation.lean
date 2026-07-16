/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.SemanticBridge
import Legitimacy.Safety.KernelSafety.GovernanceExamples

/-!
# Legitimacy.Kernel.CompositionRepresentation

Serial composition representation theorem for semantic legitimacy kernels.

The existing semantic bridge theorem decomposes one kernel datum into runtime,
diagnostic, and spectral layers. This module adds the composition direction:
for kernel data connected by a kernel-governed trajectory, the composition has
exactly two legitimate exits. Either the target datum still exposes every
runtime/diagnostic/spectral obligation, or every concrete target-obligation
failure is routed through a monitored sacrifice entry in the trajectory ledger.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-- A governance artifact whose kernel datum has reached the live semantic
activation discipline. -/
structure LiveSemanticKernelArtifact {n : Nat} (sys : GovernedSystem n) where
  /-- The kernel datum activated by this artifact. -/
  data : LegitimacyKernelData sys
  /-- Live activation requires the full semantic kernel invariant. -/
  live : KernelInvariant data

/-- Serial composition of two kernel data packages. The concrete execution
evidence is the kernel-governed trajectory from the left datum to the right
datum.

The endpoints are intentionally not required to be `LiveSemanticKernelArtifact`s:
non-live targets are the cases where the preservation/sacrifice boundary has
load-bearing content. -/
structure SerialKernelComposition
    {n : Nat} {sys : GovernedSystem n}
    (source target : LegitimacyKernelData sys) where
  /-- Concrete serial execution path for `A ; B`. -/
  trajectory : KernelGovernedTrajectory sys source target

/-- A concrete target-side semantic-kernel obligation failure. The witness
names the failed axiom and carries the corresponding failed predicate, so a
ledger discharge is tied to a particular runtime, diagnostic, or spectral
obligation rather than to a distributed proposition. -/
inductive SemanticKernelObligationFailure
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : Prop where
  /-- The target obligation that failed, with its proof of failure. -/
  | mk (failedAxiom : KernelAxiom)
      (violation : KernelAxiomViolation failedAxiom D) :
      SemanticKernelObligationFailure D

/-- The sacrifice ledger exposed by a serial composition: some transition in
the trajectory emitted a monitored sacrifice certificate. -/
def SerialKernelComposition.sacrificeLedger
    {n : Nat} {sys : GovernedSystem n}
    {source target : LegitimacyKernelData sys}
    (composition : SerialKernelComposition source target) : Prop :=
  KernelTrajectoryHasSacrifice composition.trajectory

/-- Preservation conclusion for a serial composition. The target is still a
semantic legitimacy kernel, or the composition exposes an explicit monitored
sacrifice ledger entry. -/
def SerialKernelComposition.preservesSemanticKernelOrSacrifice
    {n : Nat} {sys : GovernedSystem n}
    {source target : LegitimacyKernelData sys}
    (composition : SerialKernelComposition source target) : Prop :=
  KernelInvariant target ∨ composition.sacrificeLedger

/-- Runtime, diagnostic, and spectral obligations of the target datum are all
present when no ledger entry exists; any concrete target-side obligation
failure must be routed through that ledger.

This is deliberately not the distributed formula
`(P₁ ∨ ledger) ∧ ... ∧ (P₇ ∨ ledger)`: the second component carries a
per-axiom failure witness and forces the ledger to discharge the named failure.
-/
def SerialKernelComposition.obligationsPreservedOrSacrificed
    {n : Nat} {sys : GovernedSystem n}
    {source target : LegitimacyKernelData sys}
    (composition : SerialKernelComposition source target) : Prop :=
  let D := target
  let ledger := composition.sacrificeLedger
  ((¬ ledger) →
    Certifiable D.certification ∧
    GovernanceObservable D.answer D.observeAnswer D.observe ∧
    KernelCorrigible D ∧
    CausalSoundness sys.dag sys.governed ∧
    NonVacuous sys.graph sys.trace ∧
    AllLegitimacyAxioms sys.graph ∧
    SpectralCarrierRepresentsGraph sys.graph D.spectralGraph
      D.spectralSignal ∧
    SpectralWellConnected D.spectralGraph D.spectralSignal
      sys.graph.weightedSize_atLeastTwo) ∧
  (SemanticKernelObligationFailure D → ledger)

private theorem no_obligation_failure_of_kernelInvariant
    {n : Nat} {sys : GovernedSystem n}
    {D : LegitimacyKernelData sys}
    (hkernel : KernelInvariant D) :
    ¬ SemanticKernelObligationFailure D := by
  intro hfailure
  have hfactors :=
    (semanticKernel_iff_runtime_diagnostic_spectral_layers D).mp hkernel
  rcases hfactors with
    ⟨hcert, hobs, hcorr, hsafe, hnonvacuous, hdiagnostic, hrep, hspectral⟩
  cases hfailure with
  | mk failedAxiom violation =>
      cases failedAxiom with
      | Certifiable =>
          exact violation hcert
      | Observable =>
          exact violation hobs
      | Corrigible =>
          exact violation hcorr
      | CompositionalSafety =>
          exact violation hsafe
      | NonVacuous =>
          exact violation hnonvacuous
      | SemanticBridge =>
          exact violation ⟨hdiagnostic, hrep, hspectral⟩
      | SpectralWellConnected =>
          exact violation hspectral

/-- ROADMAP-8 composition representation theorem. For raw kernel data, serial
composition preserves the semantic legitimacy-kernel conclusion if and only if
the target obligations are present without a ledger and every concrete
target-side obligation failure is discharged by a monitored ledger entry. -/
theorem legitimacyKernel_composition_preserves_iff_obligations_preserved_or_sacrificed
    {n : Nat} {sys : GovernedSystem n}
    {source target : LegitimacyKernelData sys}
    (composition : SerialKernelComposition source target) :
    composition.preservesSemanticKernelOrSacrifice ↔
      composition.obligationsPreservedOrSacrificed := by
  constructor
  · intro hpreserves
    rcases hpreserves with htarget | hsacrificed
    · have hfactors :=
        (semanticKernel_iff_runtime_diagnostic_spectral_layers target).mp
          htarget
      exact
        ⟨fun _hnoLedger => hfactors,
          fun hfailure =>
            False.elim
              (no_obligation_failure_of_kernelInvariant htarget hfailure)⟩
    · exact
        ⟨fun hnoLedger => False.elim (hnoLedger hsacrificed),
          fun _hfailure => hsacrificed⟩
  · intro hobligations
    by_cases hsacrificed : composition.sacrificeLedger
    · exact Or.inr hsacrificed
    · have hfactors := hobligations.1 hsacrificed
      have htarget : KernelInvariant target :=
        (semanticKernel_iff_runtime_diagnostic_spectral_layers target).mpr
          hfactors
      exact Or.inl htarget

/-- Live activation of the left artifact supplies the forward preservation
conclusion for any supported serial composition. -/
theorem serialKernelComposition_liveActivation_preserves_or_sacrifices
    {n : Nat} {sys : GovernedSystem n}
    {A B : LiveSemanticKernelArtifact sys}
    (composition : SerialKernelComposition A.data B.data) :
    composition.preservesSemanticKernelOrSacrifice :=
  reachable_state_safety A.data B.data composition.trajectory A.live

/-! ## Worked composition example -/

private noncomputable def roadmap8FailureCounterexampleN : Nat :=
  Classical.choose
    runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected

private noncomputable def roadmap8FailureCounterexampleSys :
    GovernedSystem roadmap8FailureCounterexampleN :=
  Classical.choose
    (Classical.choose_spec
      runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected)

private noncomputable def roadmap8FailureCounterexampleData :
    LegitimacyKernelData roadmap8FailureCounterexampleSys :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected))

private theorem roadmap8FailureCounterexample_spec :
    IsLegitimacyKernel roadmap8FailureCounterexampleData ∧
      AllLegitimacyAxioms roadmap8FailureCounterexampleSys.graph ∧
        ¬ SpectralWellConnected
          roadmap8FailureCounterexampleData.spectralGraph
          roadmap8FailureCounterexampleData.spectralSignal
          roadmap8FailureCounterexampleSys.graph.weightedSize_atLeastTwo :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected))

private lemma protocolNonVacuous_of_kernelNonVacuous
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (hnonvacuous : D.KernelNonVacuous) :
    ProtocolNonVacuous sys.graph := by
  rcases hnonvacuous.1 with ⟨witness⟩
  refine
    ⟨sys.trace,
      witness.governedClaims,
      witness.permitEligibleClaims,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sys.trace_consistent
  · exact witness.wellFormed
  · exact witness.governed_nonempty
  · exact witness.boundedDisposition
  · exact witness.eligible_nonempty
  · exact witness.eligible_subset
  · exact witness.permitEligible
  · exact witness.notRefusal
  · exact witness.notPermanentEscalation
  · exact witness.notDeadlock

private theorem roadmap8FailureProtocolNonVacuous :
    ProtocolNonVacuous roadmap8FailureCounterexampleSys.graph :=
  protocolNonVacuous_of_kernelNonVacuous
    roadmap8FailureCounterexampleData
    roadmap8FailureCounterexample_spec.1.nonVacuous

private def roadmap8FailureCompilationReport : CompilationReport :=
  fun _ => CompilationVerdict.certified

private lemma roadmap8FailureCompilationChecks :
    CompilationChecks roadmap8FailureCounterexampleSys.graph []
      roadmap8FailureCompilationReport := by
  constructor
  · intro property _hnotSacrificed
    constructor
    · rfl
    · cases property with
      | Consistency =>
          exact roadmap8FailureCounterexample_spec.2.1.1
      | Solidarity =>
          exact roadmap8FailureCounterexample_spec.2.1.2.1
      | Monotonicity =>
          exact roadmap8FailureCounterexample_spec.2.1.2.2.1
      | Strategyproofness =>
          exact roadmap8FailureCounterexample_spec.2.1.2.2.2
      | NonVacuous =>
          exact roadmap8FailureProtocolNonVacuous
  · intro property hlisted
    cases hlisted

private noncomputable def roadmap8FailureCompiledGovernance :
    CompiledGovernance :=
  compileGovernance roadmap8FailureCounterexampleSys.graph []
    roadmap8FailureCompilationReport roadmap8FailureCompilationChecks

private def roadmap8FailureMonitoring : MonitoringPlan where
  watches :=
    [ GovernanceProperty.Consistency
    , GovernanceProperty.Solidarity
    , GovernanceProperty.Monotonicity
    , GovernanceProperty.Strategyproofness
    , GovernanceProperty.NonVacuous
    ]

/-- Concrete ledger certificate used by the worked example. It records the
failed spectral obligation of a non-live target as the monitored sacrificed
obligation. -/
private noncomputable def roadmap8FailureKernelSacrificeCertificate :
    MonitoredSacrificeCertificate
      roadmap8FailureCounterexampleData
      roadmap8FailureCounterexampleData where
  sacrificed := SacrificedAxiom.kernel KernelAxiom.SpectralWellConnected
  step := KernelStep.refl roadmap8FailureCounterexampleData
  claim_profile := []
  claimant := 0
  aggregator_witness := none
  stateful_violation := none
  compiled := roadmap8FailureCompiledGovernance
  monitoring := roadmap8FailureMonitoring
  graph_bound := rfl
  monitoring_obligation :=
    { fires := True
      decidable_fires := inferInstance
      fired := trivial
      bound_exceedance :=
        MonitoringBoundExceedance.oneFailureOverZero
          roadmap8FailureCompiledGovernance
      runtime_observation :=
        MonitoringRuntimeObservation.ofSacrifice
          (SacrificedAxiom.kernel KernelAxiom.SpectralWellConnected)
          roadmap8FailureCompiledGovernance
          roadmap8FailureMonitoring
      ledger_emission :=
        MonitoringLedgerEmission.ofSacrifice
          (SacrificedAxiom.kernel KernelAxiom.SpectralWellConnected)
          roadmap8FailureCompiledGovernance
          roadmap8FailureMonitoring }

/-- Asymmetric ROADMAP-8 trajectory: the target datum has a genuine spectral
obligation failure, and the only successful ROADMAP-8 exit is the monitored
sacrifice ledger. -/
private noncomputable def roadmap8AsymmetricFailureTrajectory :
    KernelGovernedTrajectory roadmap8FailureCounterexampleSys
      roadmap8FailureCounterexampleData
      roadmap8FailureCounterexampleData :=
  KernelGovernedTrajectory.singleSacrificeStep
    roadmap8FailureKernelSacrificeCertificate

/-- The worked example composes a non-live target with a sacrifice-only
trajectory, so preservation is not obtained from target liveness. -/
noncomputable def roadmap8AsymmetricFailureComposition :
    SerialKernelComposition roadmap8FailureCounterexampleData
      roadmap8FailureCounterexampleData where
  trajectory := roadmap8AsymmetricFailureTrajectory

/-- The worked composition has a concrete sacrifice ledger entry at its first
serial transition. -/
theorem roadmap8_asymmetric_failure_composition_has_sacrifice_ledger :
    roadmap8AsymmetricFailureComposition.sacrificeLedger := by
  refine ⟨0, ?_⟩
  exact
    KernelGovernedTrajectory.HasSacrificeStepAt.here
      roadmap8FailureKernelSacrificeCertificate
      (KernelGovernedTrajectory.refl roadmap8FailureCounterexampleData)

/-- The worked target has a named spectral obligation failure. -/
theorem roadmap8_asymmetric_failure_witness :
    SemanticKernelObligationFailure roadmap8FailureCounterexampleData :=
  ⟨KernelAxiom.SpectralWellConnected,
    roadmap8FailureCounterexample_spec.2.2⟩

/-- The worked target is not a semantic kernel: the semantic bridge theorem
would otherwise expose the spectral obligation known to fail. -/
theorem roadmap8_asymmetric_target_not_kernelInvariant :
    ¬ KernelInvariant roadmap8FailureCounterexampleData := by
  intro hkernel
  exact no_obligation_failure_of_kernelInvariant hkernel
    roadmap8_asymmetric_failure_witness

/-- Worked composition example: the target obligations genuinely fail, target
preservation is false, and the ROADMAP-8 conclusion is discharged only by the
monitored sacrifice ledger. -/
theorem roadmap8_worked_asymmetric_sacrifice_example :
    SemanticKernelObligationFailure roadmap8FailureCounterexampleData ∧
      ¬ KernelInvariant roadmap8FailureCounterexampleData ∧
      roadmap8AsymmetricFailureComposition.sacrificeLedger ∧
      roadmap8AsymmetricFailureComposition.preservesSemanticKernelOrSacrifice ∧
      roadmap8AsymmetricFailureComposition.obligationsPreservedOrSacrificed := by
  have hledger :=
    roadmap8_asymmetric_failure_composition_has_sacrifice_ledger
  have hpreserves :
      roadmap8AsymmetricFailureComposition.preservesSemanticKernelOrSacrifice :=
    Or.inr hledger
  exact
    ⟨roadmap8_asymmetric_failure_witness,
      roadmap8_asymmetric_target_not_kernelInvariant,
      hledger,
      hpreserves,
      (legitimacyKernel_composition_preserves_iff_obligations_preserved_or_sacrificed
        roadmap8AsymmetricFailureComposition).mp hpreserves⟩

end Safety

end Legitimacy
