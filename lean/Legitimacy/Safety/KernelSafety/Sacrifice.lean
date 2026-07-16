/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.Core

/-!
# Legitimacy.Safety.KernelSafety.Sacrifice

Monitored sacrifice vocabulary for kernel-relative safety.

This module owns the obligations that can be explicitly sacrificed, the runtime
monitoring payload that makes a sacrifice observable, and the certificate
constructors that connect protocol-level declarations to kernel transitions.

Monitoring enrichment audit:

* The current `SacrificeMonitoringObligation` is proof-carrying, but its
  monitored event is an arbitrary decidable `fires : Prop`. The shipped
  constructors instantiate it with `property ∈ compiled.sacrifices`, so
  `MonitoredSacrificeCertificate.monitoring_obligation` proves only that the
  declared sacrifice boundary fired. It does not expose a concrete exceeded
  bound, an observation snapshot from `MonitoringPlan`, or a ledger slot for
  the emitted certificate.
* The strongest local enrichment available without changing protocol state is
  to attach first-class data to the obligation: a bound-exceedance record, a
  runtime observation projection of `monitoring.watches` and
  `compiled.sacrifices`, and a concrete ledger-emission slot. For governance
  sacrifices, the existing constructors can derive the exceedance from
  `compiled.witness.sacrifices_justified property hdeclared`; the observation
  projection records the plan and boundary lists actually in force.
* Existing worked examples construct certificates through
  `MonitoredSacrificeCertificate.ofCompiledProperty` or
  `ofCompiledPropertyWithAggregatorWitness`. Those constructors require an
  explicit `MonitoringBoundExceedance`, so callers name whether the emitted
  bound came from runtime monitoring data, a property-level failure witness, or
  a deliberately synthetic compatibility fixture.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-- Extended safety-transition kernel obligations that may be explicitly
sacrificed by a monitored transition. The first five correspond to the
canonical terminal kernel axioms named by `Legitimacy.KernelAxiom`; the final
two expose semantic-bridge and spectral-well-connected conjuncts tracked by
`KernelInvariant`. The corrigibility variant subsumes the kernel
action-capability bound; there is no separate `AdversarialBounded` variant. -/
inductive KernelAxiom where
  | Certifiable : KernelAxiom
  | Observable : KernelAxiom
  | Corrigible : KernelAxiom
  | CompositionalSafety : KernelAxiom
  | NonVacuous : KernelAxiom
  | SemanticBridge : KernelAxiom
  | SpectralWellConnected : KernelAxiom
  deriving Repr, DecidableEq

/-- A sacrificed obligation is either one of the protocol's concrete governance
properties or one of the kernel obligations tracked by the semantic invariant. -/
inductive SacrificedAxiom where
  | governance (property : GovernanceProperty) : SacrificedAxiom
  | kernel (sacrificed : KernelAxiom) : SacrificedAxiom
  deriving Repr, DecidableEq

/-- What it means for a particular kernel axiom to fail on a datum. -/
def KernelAxiomViolation {n : Nat} {sys : GovernedSystem n}
    (sacrificed : KernelAxiom) (D : LegitimacyKernelData sys) : Prop :=
  match sacrificed with
  | KernelAxiom.Certifiable => ¬ Certifiable D.certification
  | KernelAxiom.Observable =>
      ¬ GovernanceObservable D.answer D.observeAnswer D.observe
  | KernelAxiom.Corrigible =>
      ¬ KernelCorrigible D
  | KernelAxiom.CompositionalSafety =>
      ¬ CausalSoundness sys.dag sys.governed
  | KernelAxiom.NonVacuous =>
      ¬ NonVacuous sys.graph sys.trace
  | KernelAxiom.SemanticBridge =>
      ¬ KernelSemanticBridge D
  | KernelAxiom.SpectralWellConnected =>
      ¬ SpectralWellConnected D.spectralGraph D.spectralSignal
        sys.graph.weightedSize_atLeastTwo

/-- Concrete bound data emitted by a monitoring obligation. The witness is
numerical rather than a renamed proposition: it records the observed failure
count, the tolerated count, a positive rational overage fraction, and the
compiled governance property whose failure supplied the observed count when
the sacrifice is property-level. -/
structure MonitoringBoundExceedance (compiled : CompiledGovernance) where
  /-- Number of runtime failures observed for the monitored sacrifice. -/
  observedFailureCount : Nat
  /-- Number of failures tolerated before the monitor emits. -/
  toleratedFailureCount : Nat
  /-- Concrete proof that the observed failures exceeded the tolerated bound. -/
  bound_exceeded : toleratedFailureCount < observedFailureCount
  /-- Positive overage fraction attached to the emitted monitoring event. -/
  exceedanceFraction : ℚ
  /-- The overage fraction is genuinely positive. -/
  exceedanceFraction_pos : 0 < exceedanceFraction
  /-- Governance property whose compiled failure produced the observed count,
  if this bound arose from a property-level sacrifice. -/
  failedProperty : Option GovernanceProperty
  /-- The recorded property really fails on the compiled graph. -/
  failedProperty_failure :
    ∀ property, failedProperty = some property →
      ¬ propertyHolds property compiled.graph

namespace MonitoringBoundExceedance

/-- Minimal concrete exceedance used by compatibility record construction. -/
def oneFailureOverZero (compiled : CompiledGovernance) :
    MonitoringBoundExceedance compiled where
  observedFailureCount := 1
  toleratedFailureCount := 0
  bound_exceeded := by decide
  exceedanceFraction := 1
  exceedanceFraction_pos := by norm_num
  failedProperty := none
  failedProperty_failure := by
    intro _ hfailed
    cases hfailed

/-- One observed property failure over a zero tolerated-failure bound. This is
the smallest property-level monitoring payload that can be derived from a
compiled governance witness; callers still pass it explicitly so certificate
construction does not silently manufacture monitoring data. -/
def oneObservedPropertyFailure
    (compiled : CompiledGovernance)
    (property : GovernanceProperty)
    (hfailure : ¬ propertyHolds property compiled.graph) :
    MonitoringBoundExceedance compiled where
  observedFailureCount := 1
  toleratedFailureCount := 0
  bound_exceeded := by decide
  exceedanceFraction := 1
  exceedanceFraction_pos := by norm_num
  failedProperty := some property
  failedProperty_failure := by
    intro observedProperty hobserved
    cases hobserved
    exact hfailure

end MonitoringBoundExceedance

/-- Runtime projection carried by monitoring: the plan watches, compiled
sacrifice boundary, query slots, and boolean membership observations that were
visible when this certificate was emitted. -/
structure MonitoringRuntimeObservation
    (sacrificed : SacrificedAxiom)
    (compiled : CompiledGovernance)
    (monitoring : MonitoringPlan) where
  /-- Concrete snapshot of the live plan watches. -/
  planWatches : List GovernanceProperty
  /-- Concrete snapshot of the compiled sacrifice boundary. -/
  declaredSacrifices : List GovernanceProperty
  /-- Property-level sacrifice observed by this slot, if this is a governance
  sacrifice rather than a kernel obligation. -/
  observedProperty : Option GovernanceProperty
  /-- Query slot for the runtime property answer, if property-level. -/
  propertyQuery : Option GovernanceQuery
  /-- Query slot for the declaration ledger answer, if property-level. -/
  sacrificeQuery : Option GovernanceQuery
  /-- Boolean projection of whether the plan watches the observed property. -/
  propertyWatched : Bool
  /-- Boolean projection of whether the boundary declares the observed
  property. -/
  boundaryDeclared : Bool
  /-- The watch snapshot is the actual monitoring plan. -/
  planWatches_eq : planWatches = monitoring.watches
  /-- The boundary snapshot is the actual compiled sacrifice list. -/
  declaredSacrifices_eq : declaredSacrifices = compiled.sacrifices
  /-- The observation records the certificate's sacrificed obligation. -/
  observedProperty_eq :
    observedProperty =
      match sacrificed with
      | SacrificedAxiom.governance property => some property
      | SacrificedAxiom.kernel _ => none

namespace MonitoringRuntimeObservation

/-- Canonical projection of the data already present in a monitoring plan and
compiled governance artifact. -/
def ofSacrifice
    (sacrificed : SacrificedAxiom)
    (compiled : CompiledGovernance)
    (monitoring : MonitoringPlan) :
    MonitoringRuntimeObservation sacrificed compiled monitoring := by
  refine
    { planWatches := monitoring.watches
      declaredSacrifices := compiled.sacrifices
      observedProperty :=
        match sacrificed with
        | SacrificedAxiom.governance property => some property
        | SacrificedAxiom.kernel _ => none
      propertyQuery :=
        match sacrificed with
        | SacrificedAxiom.governance property =>
            some (GovernanceQuery.PropertyHolds property)
        | SacrificedAxiom.kernel _ => none
      sacrificeQuery :=
        match sacrificed with
        | SacrificedAxiom.governance property =>
            some (GovernanceQuery.SacrificeDeclared property)
        | SacrificedAxiom.kernel _ => none
      propertyWatched :=
        match sacrificed with
        | SacrificedAxiom.governance property =>
            decide (property ∈ monitoring.watches)
        | SacrificedAxiom.kernel _ => false
      boundaryDeclared :=
        match sacrificed with
        | SacrificedAxiom.governance property =>
            decide (property ∈ compiled.sacrifices)
        | SacrificedAxiom.kernel _ => false
      planWatches_eq := rfl
      declaredSacrifices_eq := rfl
      observedProperty_eq := ?_ }
  cases sacrificed <;> rfl

end MonitoringRuntimeObservation

/-- Ledger slot emitted for a monitored sacrifice certificate. This is a
concrete slot, not an abstract discharge condition: it records the emitted
obligation, the sizes of the plan and boundary snapshots, and a stable local
slot index derived from those snapshots. -/
structure MonitoringLedgerEmission
    (sacrificed : SacrificedAxiom)
    (compiled : CompiledGovernance)
    (monitoring : MonitoringPlan) where
  /-- Local ledger slot index for this monitoring emission. -/
  slotIndex : Nat
  /-- The sacrificed obligation recorded in the ledger entry. -/
  emittedSacrifice : SacrificedAxiom
  /-- Number of watches present when the ledger entry was emitted. -/
  planWatchCount : Nat
  /-- Number of declared sacrifices present when the ledger entry was emitted. -/
  declaredSacrificeCount : Nat
  /-- The entry records this certificate's sacrificed obligation. -/
  emittedSacrifice_eq : emittedSacrifice = sacrificed
  /-- The watch count was projected from the actual monitoring plan. -/
  planWatchCount_eq : planWatchCount = monitoring.watches.length
  /-- The boundary count was projected from the actual compiled artifact. -/
  declaredSacrificeCount_eq :
    declaredSacrificeCount = compiled.sacrifices.length
  /-- The slot is deterministically derived from the runtime snapshots. -/
  slotIndex_eq : slotIndex = monitoring.watches.length + compiled.sacrifices.length

namespace MonitoringLedgerEmission

/-- Canonical ledger slot for a monitored sacrifice over the supplied runtime
snapshots. -/
def ofSacrifice
    (sacrificed : SacrificedAxiom)
    (compiled : CompiledGovernance)
    (monitoring : MonitoringPlan) :
    MonitoringLedgerEmission sacrificed compiled monitoring where
  slotIndex := monitoring.watches.length + compiled.sacrifices.length
  emittedSacrifice := sacrificed
  planWatchCount := monitoring.watches.length
  declaredSacrificeCount := compiled.sacrifices.length
  emittedSacrifice_eq := rfl
  planWatchCount_eq := rfl
  declaredSacrificeCount_eq := rfl
  slotIndex_eq := rfl

end MonitoringLedgerEmission

/-- Runtime monitoring data attached to a sacrifice certificate. The
observation is kept as a concrete decidable predicate, together with evidence
that it fired for this certificate. The enriched payload also carries concrete
bound-exceedance data, a runtime projection of the monitoring plan, and the
ledger slot emitted for the certificate. -/
structure SacrificeMonitoringObligation
    (sacrificed : SacrificedAxiom)
    (compiled : CompiledGovernance)
    (monitoring : MonitoringPlan) where
  /-- The concrete runtime observation associated with this sacrifice. -/
  fires : Prop
  /-- The runtime can decide whether the observation has fired. -/
  decidable_fires : Decidable fires
  /-- This certificate is only emitted on an observation that fired. -/
  fired : fires
  /-- Concrete numerical exceedance that caused the monitored emission. -/
  bound_exceedance : MonitoringBoundExceedance compiled :=
    MonitoringBoundExceedance.oneFailureOverZero compiled
  /-- Runtime projection of the monitoring plan and compiled boundary. -/
  runtime_observation :
    MonitoringRuntimeObservation sacrificed compiled monitoring :=
      MonitoringRuntimeObservation.ofSacrifice sacrificed compiled monitoring
  /-- Concrete ledger slot emitted for this monitored certificate. -/
  ledger_emission :
    MonitoringLedgerEmission sacrificed compiled monitoring :=
      MonitoringLedgerEmission.ofSacrifice sacrificed compiled monitoring

/-- Which aggregator-axiom route supplied a monitored governance sacrifice
witness. -/
inductive AggregatorAxiomWitnessKind where
  | consistencyViolation : AggregatorAxiomWitnessKind
  | monotonicityViolation : AggregatorAxiomWitnessKind
  deriving Repr, DecidableEq

/-- A concrete stateful trajectory whose realized perturbation budget failed
the subcritical premise needed by bounded corrigibility preservation. -/
structure StatefulCriticalCapabilityViolation
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) where
  /-- The stateful adversary whose realized trajectory crossed the threshold. -/
  adv : StatefulAdversaryLayer D
  /-- The exact schedule whose realized proposal trace is being monitored. -/
  schedule : List (StatefulScheduleStep D)
  /-- The configuration from which the monitored schedule was run. -/
  cfg : StatefulAdversaryConfig adv
  /-- The failed subcritical premise, recorded as a lower bound by critical
  capability on the realized perturbation budget. -/
  critical_le_budget :
    kernelDataCriticalCapability D ≤
      statefulTrajectoryPerturbationBound D adv schedule cfg

/-- A first-class monitored sacrifice certificate. It names the sacrificed
obligation, carries concrete witness data and the transition where it occurs,
and links protocol-level sacrifices back to `CompiledGovernance` and live
monitoring data. -/
structure MonitoredSacrificeCertificate
    {n : Nat} {sys : GovernedSystem n}
    (D D' : LegitimacyKernelData sys) where
  /-- The specific governance property or kernel axiom being sacrificed. -/
  sacrificed : SacrificedAxiom
  /-- The transition on which this sacrifice is observed. -/
  step : KernelStep D D'
  /-- Witness profile for property-level violations. -/
  claim_profile : List ClaimQ
  /-- Witness claimant for property-level violations. -/
  claimant : ClaimantId
  /-- Optional typed route when a binary aggregator axiom witness supplies the
  claim profile and claimant. -/
  aggregator_witness : Option AggregatorAxiomWitnessKind
  /-- Optional stateful critical-capability failure that caused this certificate
  to be emitted on a bounded-corrigibility monitoring path. -/
  stateful_violation : Option (StatefulCriticalCapabilityViolation D)
  /-- The compiled artifact whose sacrifice boundary records the declaration. -/
  compiled : CompiledGovernance
  /-- The live monitoring plan in force for the compiled artifact. -/
  monitoring : MonitoringPlan
  /-- The compiled graph is the graph governed by the source system. -/
  graph_bound : compiled.graph = sys.graph
  /-- The runtime observation that makes this certificate monitored. -/
  monitoring_obligation :
    SacrificeMonitoringObligation sacrificed compiled monitoring

namespace MonitoredSacrificeCertificate

/-- Build a monitored certificate directly from an existing compiled governance
property sacrifice, optionally tagging the specific aggregator route and
stateful critical-capability trigger that caused this monitored emission. This
reuses `CompiledGovernance.witness` rather than introducing a parallel
sacrifice protocol. -/
def ofCompiledPropertyWithAggregatorWitness
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : KernelStep D D')
    (compiled : CompiledGovernance)
    (monitoring : MonitoringPlan)
    (property : GovernanceProperty)
    (claim_profile : List ClaimQ)
    (claimant : ClaimantId)
    (hgraph : compiled.graph = sys.graph)
    (hdeclared : property ∈ compiled.sacrifices)
    (bound_exceedance : MonitoringBoundExceedance compiled)
    (aggregator_witness : Option AggregatorAxiomWitnessKind)
    (stateful_violation : Option (StatefulCriticalCapabilityViolation D)) :
    MonitoredSacrificeCertificate D D' where
  sacrificed := SacrificedAxiom.governance property
  step := step
  claim_profile := claim_profile
  claimant := claimant
  aggregator_witness := aggregator_witness
  stateful_violation := stateful_violation
  compiled := compiled
  monitoring := monitoring
  graph_bound := hgraph
  monitoring_obligation :=
    { fires := property ∈ compiled.sacrifices
      decidable_fires := inferInstance
      fired := hdeclared
      bound_exceedance := bound_exceedance
      runtime_observation :=
        MonitoringRuntimeObservation.ofSacrifice
          (SacrificedAxiom.governance property) compiled monitoring
      ledger_emission :=
        MonitoringLedgerEmission.ofSacrifice
          (SacrificedAxiom.governance property) compiled monitoring }

/-- Build a monitored certificate directly from an existing compiled governance
property sacrifice. This reuses `CompiledGovernance.witness` rather than
introducing a parallel sacrifice protocol. -/
def ofCompiledProperty
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : KernelStep D D')
    (compiled : CompiledGovernance)
    (monitoring : MonitoringPlan)
    (property : GovernanceProperty)
    (claim_profile : List ClaimQ)
    (claimant : ClaimantId)
    (hgraph : compiled.graph = sys.graph)
    (hdeclared : property ∈ compiled.sacrifices)
    (bound_exceedance : MonitoringBoundExceedance compiled) :
    MonitoredSacrificeCertificate D D' :=
  ofCompiledPropertyWithAggregatorWitness step compiled monitoring property
    claim_profile claimant hgraph hdeclared bound_exceedance none none

end MonitoredSacrificeCertificate

namespace RawKernelStep

/-- Extractor-side raw-step hypothesis: assuming the source datum satisfies the
kernel invariant, the extracted target datum satisfies it too. This is external
classifier evidence, not data stored in `RawKernelStep`. -/
def ExtractorBoundaryHypothesis
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (_step : RawKernelStep D D') : Prop :=
  KernelInvariant D → KernelInvariant D'

/-- Monitor-side raw-step hypothesis: the runtime monitor emitted a concrete
certificate for this raw transition. This is external classifier evidence, not
data stored in `RawKernelStep`. -/
def MonitorHypothesis
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (_step : RawKernelStep D D') : Prop :=
  Nonempty (MonitoredSacrificeCertificate D D')

/-- The invariant-preserving branch of a classified raw kernel step. This is a
structural predicate on the raw target datum, not the extractor hypothesis that
may establish it. -/
def KernelBoundaryPreserved
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (_step : RawKernelStep D D') : Prop :=
  KernelInvariant D'

/-- The indexed surfaced-sacrifice branch of a classified raw kernel step. The
transition index is supplied by the trajectory theorem that locates this
certificate inside a raw schedule; the branch itself checks the concrete ledger
payload attached to the emitted certificate. -/
def IndexedSacrificeSurfaced
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (_step : RawKernelStep D D') : Prop :=
  ∃ cert : MonitoredSacrificeCertificate D D',
    cert.monitoring_obligation.ledger_emission.emittedSacrifice =
        cert.sacrificed ∧
      cert.monitoring_obligation.ledger_emission.slotIndex =
        cert.monitoring.watches.length + cert.compiled.sacrifices.length

/-- External classifier inputs for a raw kernel step: either the extractor
preserves the kernel boundary across the target datum, or the monitor emits a
concrete sacrifice certificate for this transition. -/
def MonitorExtractorHypotheses
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : RawKernelStep D D') : Prop :=
  ExtractorBoundaryHypothesis step ∨ MonitorHypothesis step

end RawKernelStep

/-- Classify a raw kernel step from external monitor/extractor hypotheses.
`RawKernelStep` itself carries only transition replay data; the disjunction is
derived here from separately supplied boundary-preservation or monitored
sacrifice evidence. -/
theorem classify_raw_step
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : RawKernelStep D D')
    (hsource : KernelInvariant D)
    (hclassifier : RawKernelStep.MonitorExtractorHypotheses step) :
    RawKernelStep.KernelBoundaryPreserved step ∨
      RawKernelStep.IndexedSacrificeSurfaced step := by
  rcases hclassifier with hboundary | hmonitor
  · exact Or.inl (hboundary hsource)
  · rcases hmonitor with ⟨cert⟩
    exact Or.inr
      ⟨cert,
        cert.monitoring_obligation.ledger_emission.emittedSacrifice_eq,
        cert.monitoring_obligation.ledger_emission.slotIndex_eq⟩

/-- Honest restate for the concrete invalid-target falsifiability request:
under the current certificate type, monitor evidence still contains a
`KernelStep`, and every `KernelStep` with a source invariant supplies a target
invariant. A raw step whose target violates `KernelBoundaryPreserved` therefore
cannot also have a monitored sacrifice certificate until the certificate
payload is split from `KernelStep`.

INTENTIONAL: the invalid-target sacrifice followup needs a certificate payload
that can be stated independently of a target-invariant-carrying `KernelStep`. -/
theorem raw_monitor_certificate_preserves_boundary
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : RawKernelStep D D')
    (hsource : KernelInvariant D)
    (hmonitor : RawKernelStep.MonitorHypothesis step) :
    RawKernelStep.KernelBoundaryPreserved step := by
  rcases hmonitor with ⟨cert⟩
  exact kernelStep_preserves_invariant cert.step hsource

/-- The requested concrete failing-boundary plus monitor-certificate witness is
inconsistent in the present substrate. The generic classifier lemma above is
still useful for any future certificate type that can monitor an invalid raw
target without packaging a target-invariant-carrying `KernelStep`. -/
theorem no_raw_classifier_failing_boundary_with_monitored_certificate
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : RawKernelStep D D')
    (hsource : KernelInvariant D) :
    ¬ (¬ RawKernelStep.KernelBoundaryPreserved step ∧
      RawKernelStep.MonitorHypothesis step) := by
  rintro ⟨hnotBoundary, hmonitor⟩
  exact hnotBoundary
    (raw_monitor_certificate_preserves_boundary step hsource hmonitor)

/-- Generic falsifiability witness for the structural boundary branch: whenever
a raw target datum violates the kernel invariant but a monitor emits a concrete
certificate, the classifier must take the surfaced-sacrifice branch. -/
theorem classify_raw_step_surfaces_when_boundary_fails
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : RawKernelStep D D')
    (hsource : KernelInvariant D)
    (hnotBoundary : ¬ RawKernelStep.KernelBoundaryPreserved step)
    (hmonitor : RawKernelStep.MonitorHypothesis step) :
    RawKernelStep.IndexedSacrificeSurfaced step := by
  have hclassified :=
    classify_raw_step step hsource (Or.inr hmonitor)
  rcases hclassified with hboundary | hsurfaced
  · exact False.elim (hnotBoundary hboundary)
  · exact hsurfaced

end Safety

end Legitimacy
