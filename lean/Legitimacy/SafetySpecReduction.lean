/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety

/-!
# Legitimacy.SafetySpecReduction

Rule-layer safety-spec reduction for compiled governance artifacts.

The reduction is deliberately scoped to declared rule-layer artifacts whose
kernel-governed trajectory starts at the datum emitted by a bounded extractor.
It does not claim that arbitrary safety specifications reduce to kernel audit.

The four reused kernel-side primitives have different theorem shapes:

* `BoundedExtractorContract` is a contract on an extractor.
* `IsSemanticLegitimacyKernel` is a predicate on the extracted kernel datum.
* `kernelReachabilitySafety` is a theorem over finite kernel-governed
  trajectories.
* `noUndeclaredSacrifice` is a deployment theorem for complete peer-relative
  rule surfaces that enter `Live`.

The theorem below composes them in the direction the types support: concrete
audit witnesses imply no silent rule-layer degradation. The converse is not
asserted; halted malformed extractor inputs satisfy the no-silent predicate
without satisfying the audit-obligation conjunction.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

/-- A compiled rule-layer artifact tied to the extracted kernel datum that
anchors its finite kernel-governed trajectory. The deployment fields remain
separate from the kernel trajectory because the protocol live path and the
kernel transition system are distinct formal layers. -/
structure RuleLayerKernelArtifact where
  /-- Lean-side extractor model for the bounded source package. -/
  extract : KernelExtractor
  /-- Bounded source package presented to the extractor. -/
  src : ExtractorInput
  /-- Reached kernel datum after replaying the finite trajectory. -/
  reachedData : LegitimacyKernelData (extract src).sys
  /-- Finite kernel-governed trajectory starting at the extracted datum. -/
  trajectory :
    KernelGovernedTrajectory (extract src).sys (extract src).data reachedData
  /-- Compiled rule-layer artifact being deployed. -/
  compiled : CompiledGovernance
  /-- Risk report paired with the live compiled artifact. -/
  report : GovernanceRiskReport
  /-- Monitoring plan paired with the live compiled artifact. -/
  monitoring : MonitoringPlan

/-- Concrete audit witnesses required to reduce this rule-layer artifact to
kernel-side safety. This is proof-carrying data, not a `Prop` wrapper: the
bounded extractor contract is a structure containing source-boundary evidence
and soundness functions, so Lean correctly keeps it in `Type`. -/
structure RuleLayerKernelAuditObligations
    (artifact : RuleLayerKernelArtifact) where
  /-- Concrete source-boundary well-formedness witness. -/
  wellFormed : artifact.src.WellFormed
  /-- Bounded extractor contract for the artifact's extractor. -/
  contract : BoundedExtractorContract artifact.extract
  /-- Complete peer-relative surface on the deployed rule layer. -/
  surface : CompletePeerRelativeSurface artifact.compiled.graph
  /-- Live protocol path for the compiled rule layer. -/
  live : IsLiveCompiled artifact.compiled artifact.report artifact.monitoring

/-- The finite conjunction of kernel-audit conclusions produced by the
reduction. The clauses are intentionally named at the rule-layer boundary:
semantic kernel soundness for the extracted datum, explicit forced sacrifice
declarations on the live compiled surface, reachable-state safety for the
supplied kernel trajectory, and the bounded extractor contract that discharged
the source boundary. -/
structure KernelAuditConjunction
    (artifact : RuleLayerKernelArtifact) where
  /-- Semantic kernel soundness for the extracted datum. -/
  semantic : IsSemanticLegitimacyKernel (artifact.extract artifact.src).data
  /-- Forced live-surface sacrifice declarations. -/
  forced : ForcedPeerRelativeSacrificesDeclared artifact.compiled
  /-- Reachability safety for the supplied finite kernel trajectory. -/
  reachable : ReachableStateSafetyConclusion artifact.trajectory
  /-- The bounded extractor contract used at the source boundary. -/
  contract : BoundedExtractorContract artifact.extract

/-- No silent rule-layer degradation for one declared rule-layer artifact.

Either the extractor boundary is malformed and the artifact is stopped before a
kernel safety claim is made, or the extracted datum is a semantic legitimacy
kernel, every reachable state on the supplied trajectory is covered by the
reachability disjunction, and the live complete peer-relative deployment has
declared the forced consistency and monotonicity sacrifices. -/
def noSilentRuleLayerDegradation
    (artifact : RuleLayerKernelArtifact) : Prop :=
  ¬ artifact.src.WellFormed ∨
    IsSemanticLegitimacyKernel (artifact.extract artifact.src).data ∧
      ReachableStateSafetyConclusion artifact.trajectory ∧
        ForcedPeerRelativeSacrificesDeclared artifact.compiled

/-- Safety-spec reduction theorem for declared rule-layer artifacts.

This is a real derivation, not a restated conjunction: bounded extractor
soundness yields the semantic kernel predicate, that predicate feeds
`kernelReachabilitySafety` for the supplied trajectory, and
`noUndeclaredSacrifice` turns the complete live peer-relative surface into
forced declared sacrifices. -/
theorem safety_spec_reduces_to_kernel_audit
    (artifact : RuleLayerKernelArtifact)
    (audit : RuleLayerKernelAuditObligations artifact) :
    noSilentRuleLayerDegradation artifact ∧
      Nonempty (KernelAuditConjunction artifact) := by
  have hsemantic :
      IsSemanticLegitimacyKernel (artifact.extract artifact.src).data := by
    exact bounded_extractor_contract_sound artifact.extract audit.contract
      artifact.src audit.wellFormed
  have hreachable :
      ReachableStateSafetyConclusion artifact.trajectory := by
    exact kernelReachabilitySafety
      (artifact.extract artifact.src).data artifact.reachedData
      artifact.trajectory hsemantic
  have hforced :
      ForcedPeerRelativeSacrificesDeclared artifact.compiled := by
    exact ((noUndeclaredSacrifice audit.surface).mp audit.live).2
  exact
    ⟨Or.inr ⟨hsemantic, hreachable, hforced⟩,
      ⟨{ semantic := hsemantic
         forced := hforced
         reachable := hreachable
         contract := audit.contract }⟩⟩

/-! ## Worked concrete kernel instance -/

/-- Concrete rule-layer artifact whose kernel side is the committed governance
example emitted by the bounded example extractor. The deployment side is kept
as explicit live-surface input so the worked example exercises
`noUndeclaredSacrifice` rather than manufacturing protocol evidence inside the
fixture. -/
noncomputable def safetySpecReductionExampleArtifact
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan) :
    RuleLayerKernelArtifact where
  extract := exampleGovernanceKernelExtractor
  src := autogenExtractorInput
  reachedData := exampleGovernanceKernelData
  trajectory := KernelGovernedTrajectory.refl exampleGovernanceKernelData
  compiled := compiled
  report := report
  monitoring := monitoring

/-- Worked example over the concrete governance kernel instance. The source
boundary and bounded extractor contract are concrete; the deployment side
requires the same explicit complete-surface and live-path witnesses consumed by
`noUndeclaredSacrifice`. -/
theorem safetySpecReductionWorkedExample
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (hsurface : CompletePeerRelativeSurface compiled.graph)
    (hlive : IsLiveCompiled compiled report monitoring) :
    noSilentRuleLayerDegradation
        (safetySpecReductionExampleArtifact compiled report monitoring) ∧
      Nonempty (KernelAuditConjunction
        (safetySpecReductionExampleArtifact compiled report monitoring)) := by
  have hwellFormed : autogenExtractorInput.WellFormed := by
    simp [ExtractorInput.WellFormed, autogenExtractorInput]
  exact safety_spec_reduces_to_kernel_audit
    (safetySpecReductionExampleArtifact compiled report monitoring)
    { wellFormed := hwellFormed
      contract := exampleGovernanceKernelExtractor_contract
      surface := hsurface
      live := hlive }

/-! ## Tightness witnesses for the new predicate -/

/-- Malformed bounded source package: over-bound, uncovered, and parser-dirty.
This gives a concrete halt witness rather than a vacuous `Prop` wrapper. -/
def malformedSafetySpecReductionInput : ExtractorInput where
  sourceId := "audits/safety-spec-reduction/malformed"
  byteSize := 2
  sizeBound := 1
  coverageComplete := false
  parserErrors := 1

lemma malformedSafetySpecReductionInput_not_wellFormed :
    ¬ malformedSafetySpecReductionInput.WellFormed := by
  simp [ExtractorInput.WellFormed, malformedSafetySpecReductionInput]

private def reductionExampleCompilationReport : CompilationReport :=
  fun _ => CompilationVerdict.certified

private theorem exampleGovernanceGraph_protocolNonVacuous :
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

private theorem reductionExampleCompilationChecks :
    CompilationChecks exampleGovernanceGraph []
      reductionExampleCompilationReport := by
  constructor
  · intro p _hp
    cases p <;>
      simp [reductionExampleCompilationReport, propertyHolds,
        exampleGovernanceGraph_protocolNonVacuous]
    · exact exampleGovernanceGraph_allLegitimacyAxioms.1
    · exact exampleGovernanceGraph_allLegitimacyAxioms.2.1
    · exact exampleGovernanceGraph_allLegitimacyAxioms.2.2.1
    · exact exampleGovernanceGraph_allLegitimacyAxioms.2.2.2
  · intro p hp
    simp at hp

private noncomputable def reductionExampleCompiledGovernance :
    CompiledGovernance :=
  compileGovernance exampleGovernanceGraph []
    reductionExampleCompilationReport reductionExampleCompilationChecks

private def reductionExampleRiskReport : GovernanceRiskReport where
  factor_exposure :=
    { consistency := 0
      solidarity := 0
      monotonicity := 0
      strategyproofness := 0
      nonvacuity := 0 }
  spectral_gap := 1
  cv_bound := 0
  localizability_bound := 0

private def reductionExampleMonitoring : MonitoringPlan where
  watches :=
    [ GovernanceProperty.Consistency
    , GovernanceProperty.Solidarity
    , GovernanceProperty.Monotonicity
    , GovernanceProperty.Strategyproofness
    , GovernanceProperty.NonVacuous
    ]

/-- Concrete malformed artifact used to witness the halt branch and show that
`noSilentRuleLayerDegradation` is operationally distinct from the audit
obligation conjunction. -/
noncomputable def malformedSafetySpecReductionArtifact :
    RuleLayerKernelArtifact where
  extract := exampleGovernanceKernelExtractor
  src := malformedSafetySpecReductionInput
  reachedData := exampleGovernanceKernelData
  trajectory := KernelGovernedTrajectory.refl exampleGovernanceKernelData
  compiled := reductionExampleCompiledGovernance
  report := reductionExampleRiskReport
  monitoring := reductionExampleMonitoring

/-- Non-vacuity of the halt branch on a concrete artifact: a malformed source
package satisfies the no-silent predicate by stopping before any kernel safety
claim is made. -/
theorem noSilentRuleLayerDegradation_halt_witness :
    noSilentRuleLayerDegradation malformedSafetySpecReductionArtifact := by
  exact Or.inl malformedSafetySpecReductionInput_not_wellFormed

/-- Operational distinctness from the audit-obligation conjunction: the
malformed artifact satisfies `noSilentRuleLayerDegradation` via the halt branch
but fails `RuleLayerKernelAuditObligations` at the concrete source boundary. -/
theorem noSilentRuleLayerDegradation_not_audit_obligation_wrapper :
    noSilentRuleLayerDegradation malformedSafetySpecReductionArtifact ∧
      ¬ Nonempty (RuleLayerKernelAuditObligations
        malformedSafetySpecReductionArtifact) := by
  constructor
  · exact noSilentRuleLayerDegradation_halt_witness
  · rintro ⟨hobligations⟩
    exact malformedSafetySpecReductionInput_not_wellFormed
      hobligations.wellFormed

end Safety

end Legitimacy
