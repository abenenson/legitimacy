/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernelization

/-!
# Legitimacy.Bridges.ELKCorrespondence

Bridge vocabulary between the kernelization hidden-authority certificate
inventory and ARC ELK-style discrepancy classes.

The correspondence is deliberately witness-bearing: the ELK side records the
observable discrepancy payload, while `ELKDiscrepancyMatchesCert` carries a
finite derivation from the legitimacy substrate predicates. The extra
`unsupportedWorldModelShift` constructor is a tightness witness: it names an
ELK-flavored discrepancy outside the five hidden-authority constructors and is
not accepted by the bridge predicate.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

/-! ## Five hidden-authority certificate kinds -/

/-- The five hidden-authority certificate classes already present in
`HiddenAuthorityCertificate`, separated from witness payloads so bridge
statements can quantify over the finite class vocabulary. -/
inductive HiddenAuthorityCertificateKind where
  | unmodeledEdge
  | bypassPath
  | hiddenOverride
  | sourceEvidenceGap
  | semanticBridgeFailure
  deriving Repr, DecidableEq, Fintype

/-! ## ELK discrepancy vocabulary -/

/-- ARC ELK certificate-bestiary types, lifted as Lean constructors.

The five bridge constructors mirror the hidden-authority certificate payloads:
unreported sensor/effective edges, multi-hop authority routes, hidden override
pairs, source-evidence gaps, and semantic translation failures. The final
constructor is intentionally outside the legitimacy 5-kind vocabulary and is
used below to show the bridge is not a catch-all ELK discrepancy relation. -/
inductive ELKDiscrepancy where
  /-- ARC: tamper between sensor/effective surface and reporter surface. -/
  | sensorTampering
      (tamperEdge : AuthorityEdge)
      (sensorSurface : AuthorityGraph)
      (reporterSurface : AuthorityGraph) : ELKDiscrepancy
  /-- ARC: latent reasoning routed via undeclared intermediates. -/
  | multiHopRouteEvasion
      (source : AuthorityNodeId)
      (middle : List AuthorityNodeId)
      (target : AuthorityNodeId)
      (effectiveSurface : AuthorityGraph)
      (reportedSurface : AuthorityGraph) : ELKDiscrepancy
  /-- ARC: hidden authority overrides a declared ordinary rule. -/
  | dominantOverrideDiscrepancy
      (overrideEdge : AuthorityEdge)
      (dominatedPair : AuthorityEdge)
      (effectiveSurface : AuthorityGraph)
      (reportedSurface : AuthorityGraph) : ELKDiscrepancy
  /-- ARC: claim materializes without declared source evidence. -/
  | materializedSourceDiscrepancy
      (materializedEdge : AuthorityEdge)
      (effectiveSurface : AuthorityGraph)
      (sourceEdges : List AuthorityEdge) : ELKDiscrepancy
  /-- ARC: meaning-translation step not accepted by the semantic audit graph. -/
  | semanticBridgeDiscrepancy
      (failureLocus : SemanticFailureLocus)
      (reportedClean : Bool)
      (reportedSurface : AuthorityGraph)
      (effectiveSurface : AuthorityGraph) : ELKDiscrepancy
  /-- ELK-shaped discrepancy outside the five hidden-authority classes. -/
  | unsupportedWorldModelShift
      (label : String)
      (reportedSurface : AuthorityGraph) : ELKDiscrepancy
  deriving Repr, DecidableEq

/-! ## Witness-bearing matching predicate -/

/-- Finite case analysis proving that an ELK discrepancy is structurally
derived from a concrete hidden-authority certificate. Each constructor records
only the certificate/discrepancy shape and one substrate minimality witness;
`MinimalHiddenAuthority` remains the single source of truth for the
load-bearing kernelization predicate. -/
inductive ELKDiscrepancyMatchCase
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (disc : ELKDiscrepancy)
    (cert : HiddenAuthorityCertificate observation) : Prop where
  | sensorTampering
      (witness : UnmodeledEdgeWitness observation)
      (hcert :
        cert = HiddenAuthorityCertificate.unmodeledEdge witness)
      (hdisc :
        disc =
          ELKDiscrepancy.sensorTampering witness.edge
            observation.effective observation.reported)
      (minimal : MinimalHiddenAuthority cert) :
      ELKDiscrepancyMatchCase disc cert
  | multiHopRouteEvasion
      (witness : BypassPathWitness observation)
      (hcert :
        cert = HiddenAuthorityCertificate.bypassPath witness)
      (hdisc :
        disc =
          ELKDiscrepancy.multiHopRouteEvasion witness.source
            witness.middle witness.target observation.effective
            observation.reported)
      (minimal : MinimalHiddenAuthority cert) :
      ELKDiscrepancyMatchCase disc cert
  | dominantOverrideDiscrepancy
      (witness : HiddenOverrideWitness observation)
      (hcert :
        cert = HiddenAuthorityCertificate.hiddenOverride witness)
      (hdisc :
        disc =
          ELKDiscrepancy.dominantOverrideDiscrepancy
            witness.overrideEdge witness.dominatedPair
            observation.effective observation.reported)
      (minimal : MinimalHiddenAuthority cert) :
      ELKDiscrepancyMatchCase disc cert
  | materializedSourceDiscrepancy
      (witness : SourceEvidenceGapWitness observation)
      (hcert :
        cert = HiddenAuthorityCertificate.sourceEvidenceGap witness)
      (hdisc :
        disc =
          ELKDiscrepancy.materializedSourceDiscrepancy witness.edge
            observation.effective observation.sourceEdges)
      (minimal : MinimalHiddenAuthority cert) :
      ELKDiscrepancyMatchCase disc cert
  | semanticBridgeDiscrepancy
      (witness : SemanticBridgeFailureWitness observation)
      (hcert :
        cert =
          HiddenAuthorityCertificate.semanticBridgeFailure witness)
      (hdisc :
        disc =
          ELKDiscrepancy.semanticBridgeDiscrepancy witness.failure_locus
            observation.reportedSemanticBridgeClean observation.reported
            observation.effective)
      (minimal : MinimalHiddenAuthority cert) :
      ELKDiscrepancyMatchCase disc cert

/-- Structural correspondence between one ELK discrepancy and one legitimacy
hidden-authority certificate. This is a structure with a finite case witness,
not a bundled conjunction, so consumers can recover the exact substrate
predicate used by the bridge. -/
structure ELKDiscrepancyMatchesCert
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (disc : ELKDiscrepancy)
    (cert : HiddenAuthorityCertificate observation) : Prop where
  case_derivation : ELKDiscrepancyMatchCase disc cert

/-- Proves `ELKDiscrepancyMatchesCert.minimal` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem ELKDiscrepancyMatchesCert.minimal
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    {disc : ELKDiscrepancy}
    {cert : HiddenAuthorityCertificate observation}
    (hmatch : ELKDiscrepancyMatchesCert disc cert) :
    MinimalHiddenAuthority cert := by
  rcases hmatch with ⟨hcase⟩
  cases hcase with
  | sensorTampering _ _ _ minimal => exact minimal
  | multiHopRouteEvasion _ _ _ minimal => exact minimal
  | dominantOverrideDiscrepancy _ _ _ minimal => exact minimal
  | materializedSourceDiscrepancy _ _ _ minimal => exact minimal
  | semanticBridgeDiscrepancy _ _ _ minimal => exact minimal

/-! ## Per-class lifting lemmas -/

/-- Sensor-tampering lift for the unmodeled-edge certificate class. The input is
a certificate already identified as an unmodeled-edge witness together with its
minimality proof; the conclusion constructs the corresponding ELK
`sensorTampering` discrepancy and records the finite match case. This is the
per-class constructor used by the main correspondence theorem when the hidden
authority is an undeclared edge between effective and reported governance
surfaces. -/
theorem unmodeled_edge_lifts_to_elk_sensor_tampering
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation)
    (h :
      ∃ witness : UnmodeledEdgeWitness observation,
        cert = HiddenAuthorityCertificate.unmodeledEdge witness ∧
          MinimalHiddenAuthority cert) :
    ∃ disc : ELKDiscrepancy,
      (∃ edge effective reported,
        disc = ELKDiscrepancy.sensorTampering edge effective reported) ∧
        ELKDiscrepancyMatchesCert disc cert := by
  rcases h with ⟨witness, hcert, minimal⟩
  refine ⟨ELKDiscrepancy.sensorTampering witness.edge
      observation.effective observation.reported, ?_, ?_⟩
  · exact ⟨witness.edge, observation.effective, observation.reported, rfl⟩
  · exact ⟨ELKDiscrepancyMatchCase.sensorTampering witness hcert rfl
      minimal⟩

/-- Multi-hop route-evasion lift for bypass-path certificates. The hypothesis
identifies the certificate as a bypass witness and supplies minimality; the
conclusion builds the ELK discrepancy whose route fields are the witness source,
middle path, target, and the observation's effective/reported surfaces. This
keeps the hidden path evidence recoverable on the ELK side rather than only
recording that some generic discrepancy exists. -/
theorem bypass_path_lifts_to_elk_multi_hop_route_evasion
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation)
    (h :
      ∃ witness : BypassPathWitness observation,
        cert = HiddenAuthorityCertificate.bypassPath witness ∧
          MinimalHiddenAuthority cert) :
    ∃ disc : ELKDiscrepancy,
      (∃ source middle target effective reported,
        disc =
          ELKDiscrepancy.multiHopRouteEvasion source middle target
            effective reported) ∧
        ELKDiscrepancyMatchesCert disc cert := by
  rcases h with ⟨witness, hcert, minimal⟩
  refine ⟨ELKDiscrepancy.multiHopRouteEvasion witness.source
      witness.middle witness.target observation.effective
      observation.reported, ?_, ?_⟩
  · exact ⟨witness.source, witness.middle, witness.target,
      observation.effective, observation.reported, rfl⟩
  · exact ⟨ELKDiscrepancyMatchCase.multiHopRouteEvasion witness hcert rfl
      minimal⟩

/-- Dominant-override lift for hidden-override certificates. From a certificate
tagged by a hidden override witness and its minimality proof, the theorem
constructs the ELK discrepancy naming the override edge, the dominated pair,
and the observation surfaces it separates. Consumers therefore get an explicit
ELK payload for a hidden priority rule rather than a lossy certificate tag. -/
theorem hidden_override_lifts_to_elk_dominant_override_discrepancy
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation)
    (h :
      ∃ witness : HiddenOverrideWitness observation,
        cert = HiddenAuthorityCertificate.hiddenOverride witness ∧
          MinimalHiddenAuthority cert) :
    ∃ disc : ELKDiscrepancy,
      (∃ overrideEdge dominatedPair effective reported,
        disc =
          ELKDiscrepancy.dominantOverrideDiscrepancy overrideEdge
            dominatedPair effective reported) ∧
        ELKDiscrepancyMatchesCert disc cert := by
  rcases h with ⟨witness, hcert, minimal⟩
  refine ⟨ELKDiscrepancy.dominantOverrideDiscrepancy
      witness.overrideEdge witness.dominatedPair observation.effective
      observation.reported, ?_, ?_⟩
  · exact ⟨witness.overrideEdge, witness.dominatedPair,
      observation.effective, observation.reported, rfl⟩
  · exact ⟨ELKDiscrepancyMatchCase.dominantOverrideDiscrepancy witness
      hcert rfl minimal⟩

/-- Materialized-source lift for source-evidence-gap certificates. The premise
says the certificate is exactly a source-gap witness and is minimal; the result
constructs an ELK discrepancy naming the unsupported edge, the effective graph,
and the declared source-edge set. Operationally this exposes missing provenance
as finite ELK evidence, not merely as an internal kernelization failure. -/
theorem source_evidence_gap_lifts_to_elk_materialized_source_discrepancy
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation)
    (h :
      ∃ witness : SourceEvidenceGapWitness observation,
        cert = HiddenAuthorityCertificate.sourceEvidenceGap witness ∧
          MinimalHiddenAuthority cert) :
    ∃ disc : ELKDiscrepancy,
      (∃ edge effective sourceEdges,
        disc =
          ELKDiscrepancy.materializedSourceDiscrepancy edge effective
            sourceEdges) ∧
        ELKDiscrepancyMatchesCert disc cert := by
  rcases h with ⟨witness, hcert, minimal⟩
  refine ⟨ELKDiscrepancy.materializedSourceDiscrepancy witness.edge
      observation.effective observation.sourceEdges, ?_, ?_⟩
  · exact ⟨witness.edge, observation.effective, observation.sourceEdges, rfl⟩
  · exact ⟨ELKDiscrepancyMatchCase.materializedSourceDiscrepancy witness
      hcert rfl minimal⟩

/-- Semantic-bridge lift for certificates whose reported and effective
interpretations diverge. Given a minimal semantic-bridge-failure certificate,
the theorem constructs the ELK discrepancy at the witness failure locus, using
the observation's reported-clean flag plus its reported and effective surfaces.
This is the per-class handoff that makes a failed semantic translation visible
to the finite ELK correspondence. -/
theorem semantic_bridge_failure_lifts_to_elk_semantic_bridge_discrepancy
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation)
    (h :
      ∃ witness : SemanticBridgeFailureWitness observation,
        cert = HiddenAuthorityCertificate.semanticBridgeFailure witness ∧
          MinimalHiddenAuthority cert) :
    ∃ disc : ELKDiscrepancy,
      (∃ locus reportedClean reported effective,
        disc =
          ELKDiscrepancy.semanticBridgeDiscrepancy locus reportedClean
            reported effective) ∧
        ELKDiscrepancyMatchesCert disc cert := by
  rcases h with ⟨witness, hcert, minimal⟩
  refine ⟨ELKDiscrepancy.semanticBridgeDiscrepancy witness.failure_locus
      observation.reportedSemanticBridgeClean observation.reported
      observation.effective, ?_, ?_⟩
  · exact ⟨witness.failure_locus, observation.reportedSemanticBridgeClean,
      observation.reported, observation.effective, rfl⟩
  · exact ⟨ELKDiscrepancyMatchCase.semanticBridgeDiscrepancy witness hcert
      rfl minimal⟩

/-! ## Main correspondence theorem -/

/-- Finite completeness for the ELK correspondence bridge. For any
hidden-authority certificate over a kernelization observation, minimality is
equivalent to the existence of an ELK discrepancy whose finite match case
derives exactly that certificate. Operationally, this makes the bridge
constructive: a minimal certificate can be turned into a concrete ELK-side
discrepancy by case analysis, and any accepted ELK match carries back the same
minimality proof. -/
theorem hidden_authority_cert_to_elk_correspondence
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation) :
    MinimalHiddenAuthority cert ↔
      ∃ disc : ELKDiscrepancy, ELKDiscrepancyMatchesCert disc cert := by
  constructor
  · intro hminimal
    cases cert with
    | unmodeledEdge witness =>
        rcases unmodeled_edge_lifts_to_elk_sensor_tampering
          (HiddenAuthorityCertificate.unmodeledEdge witness)
          ⟨witness, rfl, hminimal⟩ with ⟨disc, _hkind, hmatch⟩
        exact ⟨disc, hmatch⟩
    | bypassPath witness =>
        rcases bypass_path_lifts_to_elk_multi_hop_route_evasion
          (HiddenAuthorityCertificate.bypassPath witness)
          ⟨witness, rfl, hminimal⟩ with ⟨disc, _hkind, hmatch⟩
        exact ⟨disc, hmatch⟩
    | hiddenOverride witness =>
        rcases hidden_override_lifts_to_elk_dominant_override_discrepancy
          (HiddenAuthorityCertificate.hiddenOverride witness)
          ⟨witness, rfl, hminimal⟩ with ⟨disc, _hkind, hmatch⟩
        exact ⟨disc, hmatch⟩
    | sourceEvidenceGap witness =>
        rcases source_evidence_gap_lifts_to_elk_materialized_source_discrepancy
          (HiddenAuthorityCertificate.sourceEvidenceGap witness)
          ⟨witness, rfl, hminimal⟩ with ⟨disc, _hkind, hmatch⟩
        exact ⟨disc, hmatch⟩
    | semanticBridgeFailure witness =>
        rcases semantic_bridge_failure_lifts_to_elk_semantic_bridge_discrepancy
          (HiddenAuthorityCertificate.semanticBridgeFailure witness)
          ⟨witness, rfl, hminimal⟩ with ⟨disc, _hkind, hmatch⟩
        exact ⟨disc, hmatch⟩
  · rintro ⟨_disc, hmatch⟩
    exact hmatch.minimal

/-! ## Capability-scaled bounded-contract invariance -/

/-- A bounded extractor contract decorated with a capability scale.

The scale is deliberately metadata at this layer: the byte-stable
`BoundedExtractorContract` is the boundary condition, while certificate
admissibility is decided by the structural hidden-authority witness vocabulary.
This is the complementary monitorability framing: capability-scaled behavioral
monitoring may change what a run observes, but the typed structural certificate
admissibility predicate below does not change once the bounded extractor
contract has been supplied. -/
structure CapabilityScaledBoundedExtractorContract
    (extract : KernelExtractor) where
  capabilityScale : ℚ
  contract : BoundedExtractorContract extract

/-- A hidden-authority certificate is admissible for kernelization-honesty
exactly when it is minimal and is accepted by the five-kind ELK correspondence.
The second conjunct keeps the five-constructor structural layer explicit; the
correspondence theorem above proves it is equivalent to the substrate
minimality predicate. -/
def GovernanceKernelizationHonestyAdmissibleCert
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation) : Prop :=
  MinimalHiddenAuthority cert ∧
    ∃ disc : ELKDiscrepancy, ELKDiscrepancyMatchesCert disc cert

/-- Proves `governance_kernelization_honesty_admissible_cert_iff_minimal` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem governance_kernelization_honesty_admissible_cert_iff_minimal
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation) :
    GovernanceKernelizationHonestyAdmissibleCert cert ↔
      MinimalHiddenAuthority cert := by
  constructor
  · intro h
    exact h.1
  · intro hminimal
    exact
      ⟨hminimal,
        (hidden_authority_cert_to_elk_correspondence cert).1 hminimal⟩

/-- Capability-scaled admissibility for a bounded extractor. The bounded
contract is retained as an argument to make the extractor boundary explicit,
but the accepted certificate set is the typed structural set above. -/
def CapabilityScaledKernelizationHonestyAdmissibleCert
    {extract : KernelExtractor}
    (_scaled : CapabilityScaledBoundedExtractorContract extract)
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation) : Prop :=
  GovernanceKernelizationHonestyAdmissibleCert cert

/-- Kernelization-honesty certificate admissibility on the governance object is
capability-independent within the bounded extractor contract: two bounded
extractor instances over the same extractor, even at different capability
scales, accept exactly the same hidden-authority certificates. -/
theorem governance_kernelization_honesty_is_capability_independent
    {extract : KernelExtractor}
    (left right : CapabilityScaledBoundedExtractorContract extract)
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact} :
    ∀ cert : HiddenAuthorityCertificate observation,
      CapabilityScaledKernelizationHonestyAdmissibleCert left cert ↔
        CapabilityScaledKernelizationHonestyAdmissibleCert right cert := by
  intro cert
  rfl

/-- Nine discharge patterns for the capability-independence theorem: both
bounded contracts expose source evidence, runtime soundness, and semantic
bridge soundness; admissible certificates reduce to minimality; minimality is
equivalent to the five-kind ELK bridge; and the accepted certificate set is the
same at both capability scales. -/
theorem governance_kernelization_capability_independence_discharge_discipline
    {extract : KernelExtractor}
    (left right : CapabilityScaledBoundedExtractorContract extract) :
    (∀ src : ExtractorInput,
      src.WellFormed → Nonempty (BoundedExtractorSourceEvidence src)) ∧
    (∀ src : ExtractorInput,
      BoundedExtractorSourceEvidence src → (extract src).IsRuntimeKernel) ∧
    (∀ src : ExtractorInput,
      BoundedExtractorSourceEvidence src → (extract src).HasSemanticBridge) ∧
    (∀ src : ExtractorInput,
      src.WellFormed → Nonempty (BoundedExtractorSourceEvidence src)) ∧
    (∀ src : ExtractorInput,
      BoundedExtractorSourceEvidence src → (extract src).IsRuntimeKernel) ∧
    (∀ src : ExtractorInput,
      BoundedExtractorSourceEvidence src → (extract src).HasSemanticBridge) ∧
    (∀ {artifact : RuleLayerKernelArtifact}
      {observation : GovernanceKernelizationObservation artifact}
      (cert : HiddenAuthorityCertificate observation),
        GovernanceKernelizationHonestyAdmissibleCert cert ↔
          MinimalHiddenAuthority cert) ∧
    (∀ {artifact : RuleLayerKernelArtifact}
      {observation : GovernanceKernelizationObservation artifact}
      (cert : HiddenAuthorityCertificate observation),
        MinimalHiddenAuthority cert ↔
          ∃ disc : ELKDiscrepancy, ELKDiscrepancyMatchesCert disc cert) ∧
    (∀ {artifact : RuleLayerKernelArtifact}
      {observation : GovernanceKernelizationObservation artifact}
      (cert : HiddenAuthorityCertificate observation),
        CapabilityScaledKernelizationHonestyAdmissibleCert left cert ↔
          CapabilityScaledKernelizationHonestyAdmissibleCert right cert) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro src hwellFormed
    exact ⟨left.contract.sourceEvidence src hwellFormed⟩
  · intro src evidence
    exact left.contract.runtimeSound src evidence
  · intro src evidence
    exact left.contract.semanticBridgeSound src evidence
  · intro src hwellFormed
    exact ⟨right.contract.sourceEvidence src hwellFormed⟩
  · intro src evidence
    exact right.contract.runtimeSound src evidence
  · intro src evidence
    exact right.contract.semanticBridgeSound src evidence
  · intro _artifact _observation cert
    exact governance_kernelization_honesty_admissible_cert_iff_minimal cert
  · intro _artifact _observation cert
    exact hidden_authority_cert_to_elk_correspondence cert
  · intro _artifact _observation cert
    exact governance_kernelization_honesty_is_capability_independent
      left right cert

/-! ## Worked capability-scaled bounded-contract example -/

/-- Low-capability decoration of any supplied bounded extractor contract. -/
def lowCapabilityGovernanceBoundedExtractorContract
    {extract : KernelExtractor}
    (contract : BoundedExtractorContract extract) :
    CapabilityScaledBoundedExtractorContract extract where
  capabilityScale := 1
  contract := contract

/-- High-capability decoration of the same supplied bounded extractor
contract. -/
def highCapabilityGovernanceBoundedExtractorContract
    {extract : KernelExtractor}
    (contract : BoundedExtractorContract extract) :
    CapabilityScaledBoundedExtractorContract extract where
  capabilityScale := 100
  contract := contract

/-- Proves `worked_governance_bounded_contract_capability_scales_distinct` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem worked_governance_bounded_contract_capability_scales_distinct
    {extract : KernelExtractor}
    (contract : BoundedExtractorContract extract) :
    (lowCapabilityGovernanceBoundedExtractorContract contract).capabilityScale ≠
      (highCapabilityGovernanceBoundedExtractorContract
        contract).capabilityScale := by
  norm_num [lowCapabilityGovernanceBoundedExtractorContract,
    highCapabilityGovernanceBoundedExtractorContract]

/-- Select the worked witness-bearing certificate for each finite
hidden-authority certificate kind. The return type is packed because the five
worked certificates live over different concrete observations. -/
noncomputable def workedHiddenAuthorityCertificateForKind :
    (kind : HiddenAuthorityCertificateKind) →
      Σ artifact : RuleLayerKernelArtifact,
        Σ observation : GovernanceKernelizationObservation artifact,
          HiddenAuthorityCertificate observation
  | .unmodeledEdge =>
      ⟨kernelizationExampleArtifact, unmodeledEdgeObservation,
        unmodeledEdgeCertificate⟩
  | .bypassPath =>
      ⟨kernelizationExampleArtifact, bypassPathObservation,
        bypassPathCertificate⟩
  | .hiddenOverride =>
      ⟨kernelizationExampleArtifact, hiddenOverrideObservation,
        hiddenOverrideCertificate⟩
  | .sourceEvidenceGap =>
      ⟨kernelizationExampleArtifact, sourceGapObservation,
        sourceEvidenceGapCertificate⟩
  | .semanticBridgeFailure =>
      ⟨semanticBridgeFailureArtifact, semanticBridgeFailureObservation,
        semanticBridgeFailureCertificate⟩

/-- At both capability scales, every finite worked hidden-authority certificate
kind has its concrete witness-bearing certificate admitted by the bridge. -/
theorem worked_five_concrete_certificate_kinds_admissible_at_dual_scales
    {extract : KernelExtractor}
    (contract : BoundedExtractorContract extract) :
    ∀ kind : HiddenAuthorityCertificateKind,
      CapabilityScaledKernelizationHonestyAdmissibleCert
          (lowCapabilityGovernanceBoundedExtractorContract contract)
          (workedHiddenAuthorityCertificateForKind kind).2.2 ∧
      CapabilityScaledKernelizationHonestyAdmissibleCert
          (highCapabilityGovernanceBoundedExtractorContract contract)
          (workedHiddenAuthorityCertificateForKind kind).2.2 := by
  intro kind
  cases kind <;> constructor
  · exact
      (governance_kernelization_honesty_admissible_cert_iff_minimal
        unmodeledEdgeCertificate).2 unmodeledEdgeCertificate_minimal
  · exact
      (governance_kernelization_honesty_admissible_cert_iff_minimal
        unmodeledEdgeCertificate).2 unmodeledEdgeCertificate_minimal
  · exact
      (governance_kernelization_honesty_admissible_cert_iff_minimal
        bypassPathCertificate).2 bypassPathCertificate_minimal
  · exact
      (governance_kernelization_honesty_admissible_cert_iff_minimal
        bypassPathCertificate).2 bypassPathCertificate_minimal
  · exact
      (governance_kernelization_honesty_admissible_cert_iff_minimal
        hiddenOverrideCertificate).2 hiddenOverrideCertificate_minimal
  · exact
      (governance_kernelization_honesty_admissible_cert_iff_minimal
        hiddenOverrideCertificate).2 hiddenOverrideCertificate_minimal
  · exact
      (governance_kernelization_honesty_admissible_cert_iff_minimal
        sourceEvidenceGapCertificate).2 sourceEvidenceGapCertificate_minimal
  · exact
      (governance_kernelization_honesty_admissible_cert_iff_minimal
        sourceEvidenceGapCertificate).2 sourceEvidenceGapCertificate_minimal
  · exact
      (governance_kernelization_honesty_admissible_cert_iff_minimal
        semanticBridgeFailureCertificate).2
        semanticBridgeFailureCertificate_minimal
  · exact
      (governance_kernelization_honesty_admissible_cert_iff_minimal
        semanticBridgeFailureCertificate).2
        semanticBridgeFailureCertificate_minimal

/-- Compatibility corollary spelling out the five concrete worked
hidden-authority certificates at both capability scales. -/
theorem worked_governance_capability_independence_five_tightness_bars
    {extract : KernelExtractor}
    (contract : BoundedExtractorContract extract) :
    CapabilityScaledKernelizationHonestyAdmissibleCert
        (lowCapabilityGovernanceBoundedExtractorContract contract)
        unmodeledEdgeCertificate ∧
    CapabilityScaledKernelizationHonestyAdmissibleCert
        (highCapabilityGovernanceBoundedExtractorContract contract)
        unmodeledEdgeCertificate ∧
    CapabilityScaledKernelizationHonestyAdmissibleCert
        (lowCapabilityGovernanceBoundedExtractorContract contract)
        bypassPathCertificate ∧
    CapabilityScaledKernelizationHonestyAdmissibleCert
        (highCapabilityGovernanceBoundedExtractorContract contract)
        bypassPathCertificate ∧
    CapabilityScaledKernelizationHonestyAdmissibleCert
        (lowCapabilityGovernanceBoundedExtractorContract contract)
        hiddenOverrideCertificate ∧
    CapabilityScaledKernelizationHonestyAdmissibleCert
        (highCapabilityGovernanceBoundedExtractorContract contract)
        hiddenOverrideCertificate ∧
    CapabilityScaledKernelizationHonestyAdmissibleCert
        (lowCapabilityGovernanceBoundedExtractorContract contract)
        sourceEvidenceGapCertificate ∧
    CapabilityScaledKernelizationHonestyAdmissibleCert
        (highCapabilityGovernanceBoundedExtractorContract contract)
        sourceEvidenceGapCertificate ∧
    CapabilityScaledKernelizationHonestyAdmissibleCert
        (lowCapabilityGovernanceBoundedExtractorContract contract)
        semanticBridgeFailureCertificate ∧
    CapabilityScaledKernelizationHonestyAdmissibleCert
        (highCapabilityGovernanceBoundedExtractorContract contract)
        semanticBridgeFailureCertificate := by
  have h :=
    worked_five_concrete_certificate_kinds_admissible_at_dual_scales
      contract
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [workedHiddenAuthorityCertificateForKind] using (h .unmodeledEdge).1
  · simpa [workedHiddenAuthorityCertificateForKind] using (h .unmodeledEdge).2
  · simpa [workedHiddenAuthorityCertificateForKind] using (h .bypassPath).1
  · simpa [workedHiddenAuthorityCertificateForKind] using (h .bypassPath).2
  · simpa [workedHiddenAuthorityCertificateForKind] using (h .hiddenOverride).1
  · simpa [workedHiddenAuthorityCertificateForKind] using (h .hiddenOverride).2
  · simpa [workedHiddenAuthorityCertificateForKind] using (h .sourceEvidenceGap).1
  · simpa [workedHiddenAuthorityCertificateForKind] using (h .sourceEvidenceGap).2
  · simpa [workedHiddenAuthorityCertificateForKind] using
      (h .semanticBridgeFailure).1
  · simpa [workedHiddenAuthorityCertificateForKind] using
      (h .semanticBridgeFailure).2

/-- Proves `worked_governance_kernelization_honesty_capability_independent` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem worked_governance_kernelization_honesty_capability_independent
    {extract : KernelExtractor}
    (contract : BoundedExtractorContract extract) :
    (lowCapabilityGovernanceBoundedExtractorContract contract).capabilityScale ≠
        (highCapabilityGovernanceBoundedExtractorContract
          contract).capabilityScale ∧
      ∀ cert : HiddenAuthorityCertificate bypassPathObservation,
        CapabilityScaledKernelizationHonestyAdmissibleCert
            (lowCapabilityGovernanceBoundedExtractorContract contract) cert ↔
          CapabilityScaledKernelizationHonestyAdmissibleCert
            (highCapabilityGovernanceBoundedExtractorContract
              contract) cert :=
  ⟨worked_governance_bounded_contract_capability_scales_distinct contract,
    governance_kernelization_honesty_is_capability_independent
      (lowCapabilityGovernanceBoundedExtractorContract contract)
      (highCapabilityGovernanceBoundedExtractorContract contract)⟩

/-! ## Executable worked example and tightness witness -/

/-- Executable data-level check for the bridge payload correspondence. The
Prop-level `ELKDiscrepancyMatchesCert` additionally carries the minimality
proofs; this Boolean verifier is for concrete examples and audit fixtures. -/
def ELKDiscrepancyMatchesCertBool
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (disc : ELKDiscrepancy)
    (cert : HiddenAuthorityCertificate observation) : Bool :=
  match disc, cert with
  | ELKDiscrepancy.sensorTampering edge effective reported,
      HiddenAuthorityCertificate.unmodeledEdge witness =>
      decide
        (edge = witness.edge ∧ effective = observation.effective ∧
          reported = observation.reported)
  | ELKDiscrepancy.multiHopRouteEvasion source middle target effective
      reported, HiddenAuthorityCertificate.bypassPath witness =>
      decide
        (source = witness.source ∧ middle = witness.middle ∧
          target = witness.target ∧ effective = observation.effective ∧
            reported = observation.reported)
  | ELKDiscrepancy.dominantOverrideDiscrepancy overrideEdge dominatedPair
      effective reported, HiddenAuthorityCertificate.hiddenOverride witness =>
      decide
        (overrideEdge = witness.overrideEdge ∧
          dominatedPair = witness.dominatedPair ∧
            effective = observation.effective ∧ reported = observation.reported)
  | ELKDiscrepancy.materializedSourceDiscrepancy edge effective sourceEdges,
      HiddenAuthorityCertificate.sourceEvidenceGap witness =>
      decide
        (edge = witness.edge ∧ effective = observation.effective ∧
          sourceEdges = observation.sourceEdges)
  | ELKDiscrepancy.semanticBridgeDiscrepancy locus reportedClean reported
      effective, HiddenAuthorityCertificate.semanticBridgeFailure witness =>
      decide
        (locus = witness.failure_locus ∧
          reportedClean = observation.reportedSemanticBridgeClean ∧
            reported = observation.reported ∧ effective = observation.effective)
  | _, _ => false

/-- Proves `ELKDiscrepancyMatchesCertBool_sound_of_minimal` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem ELKDiscrepancyMatchesCertBool_sound_of_minimal
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    {disc : ELKDiscrepancy}
    {cert : HiddenAuthorityCertificate observation}
    (hbool : ELKDiscrepancyMatchesCertBool disc cert = true)
    (hminimal : MinimalHiddenAuthority cert) :
    ELKDiscrepancyMatchesCert disc cert := by
  cases cert with
  | unmodeledEdge witness =>
      cases disc <;> simp [ELKDiscrepancyMatchesCertBool] at hbool
      rename_i edge effective reported
      rcases hbool with ⟨rfl, rfl, rfl⟩
      exact ⟨ELKDiscrepancyMatchCase.sensorTampering witness rfl rfl
        hminimal⟩
  | bypassPath witness =>
      cases disc <;> simp [ELKDiscrepancyMatchesCertBool] at hbool
      rename_i source middle target effective reported
      rcases hbool with ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨ELKDiscrepancyMatchCase.multiHopRouteEvasion witness rfl rfl
        hminimal⟩
  | hiddenOverride witness =>
      cases disc <;> simp [ELKDiscrepancyMatchesCertBool] at hbool
      rename_i overrideEdge dominatedPair effective reported
      rcases hbool with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨ELKDiscrepancyMatchCase.dominantOverrideDiscrepancy witness rfl
        rfl hminimal⟩
  | sourceEvidenceGap witness =>
      cases disc <;> simp [ELKDiscrepancyMatchesCertBool] at hbool
      rename_i edge effective sourceEdges
      rcases hbool with ⟨rfl, rfl, rfl⟩
      exact ⟨ELKDiscrepancyMatchCase.materializedSourceDiscrepancy witness rfl
        rfl hminimal⟩
  | semanticBridgeFailure witness =>
      cases disc <;> simp [ELKDiscrepancyMatchesCertBool] at hbool
      rename_i locus reportedClean reported effective
      rcases hbool with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨ELKDiscrepancyMatchCase.semanticBridgeDiscrepancy witness rfl
        rfl hminimal⟩

/-- Proves `ELKDiscrepancyMatchesCertBool_complete` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem ELKDiscrepancyMatchesCertBool_complete
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    {disc : ELKDiscrepancy}
    {cert : HiddenAuthorityCertificate observation}
    (hmatch : ELKDiscrepancyMatchesCert disc cert) :
    ELKDiscrepancyMatchesCertBool disc cert = true := by
  rcases hmatch with ⟨hcase⟩
  cases hcase with
  | sensorTampering _ hcert hdisc _ =>
      rw [hdisc, hcert]
      simp [ELKDiscrepancyMatchesCertBool]
  | multiHopRouteEvasion _ hcert hdisc _ =>
      rw [hdisc, hcert]
      simp [ELKDiscrepancyMatchesCertBool]
  | dominantOverrideDiscrepancy _ hcert hdisc _ =>
      rw [hdisc, hcert]
      simp [ELKDiscrepancyMatchesCertBool]
  | materializedSourceDiscrepancy _ hcert hdisc _ =>
      rw [hdisc, hcert]
      simp [ELKDiscrepancyMatchesCertBool]
  | semanticBridgeDiscrepancy _ hcert hdisc _ =>
      rw [hdisc, hcert]
      simp [ELKDiscrepancyMatchesCertBool]

/-- Proves `ELKDiscrepancyMatchesCertBool_iff_of_minimal` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem ELKDiscrepancyMatchesCertBool_iff_of_minimal
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    {disc : ELKDiscrepancy}
    {cert : HiddenAuthorityCertificate observation}
    (hminimal : MinimalHiddenAuthority cert) :
    ELKDiscrepancyMatchesCertBool disc cert = true ↔
      ELKDiscrepancyMatchesCert disc cert := by
  constructor
  · intro hbool
    exact ELKDiscrepancyMatchesCertBool_sound_of_minimal hbool hminimal
  · intro hmatch
    exact ELKDiscrepancyMatchesCertBool_complete hmatch

def ELKSensorTamperingPayloadMatchesBool
    (disc : ELKDiscrepancy)
    (edge : AuthorityEdge)
    (effective reported : AuthorityGraph) : Bool :=
  match disc with
  | ELKDiscrepancy.sensorTampering edge' effective' reported' =>
      decide
        (edge' = edge ∧ effective' = effective ∧ reported' = reported)
  | _ => false

def workedUnmodeledEdge : AuthorityEdge :=
  { fromNode := "principal", toNode := "reviewer" }

def workedUnmodeledEdgeELKDiscrepancy : ELKDiscrepancy :=
  ELKDiscrepancy.sensorTampering
    workedUnmodeledEdge
    unmodeledEffectiveGraph
    unmodeledReportedGraph

/-- Proves `worked_unmodeled_edge_elk_matches_cert` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem worked_unmodeled_edge_elk_matches_cert :
    ELKDiscrepancyMatchesCert workedUnmodeledEdgeELKDiscrepancy
      unmodeledEdgeCertificate := by
  unfold workedUnmodeledEdgeELKDiscrepancy unmodeledEdgeCertificate
    workedUnmodeledEdge
  exact
    ⟨ELKDiscrepancyMatchCase.sensorTampering
      { edge := { fromNode := "principal", toNode := "reviewer" }
        effective_has_edge := by
          simp [unmodeledEdgeObservation, unmodeledEffectiveGraph,
            HasAuthorityEdge]
        reported_lacks_edge := by
          simp [unmodeledEdgeObservation, unmodeledReportedGraph,
            HasAuthorityEdge] }
      rfl rfl unmodeledEdgeCertificate_minimal⟩

/-- Proves `worked_unmodeled_edge_native_verifier` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem worked_unmodeled_edge_native_verifier :
    ELKSensorTamperingPayloadMatchesBool workedUnmodeledEdgeELKDiscrepancy
      workedUnmodeledEdge unmodeledEffectiveGraph unmodeledReportedGraph =
        true := by
  native_decide

def workedBypassPathELKDiscrepancy : ELKDiscrepancy :=
  ELKDiscrepancy.multiHopRouteEvasion "user" ["router"] "admin"
    bypassGraph bypassGraph

/-- Proves `worked_bypass_path_elk_matches_cert` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem worked_bypass_path_elk_matches_cert :
    ELKDiscrepancyMatchesCert workedBypassPathELKDiscrepancy
      bypassPathCertificate := by
  unfold workedBypassPathELKDiscrepancy bypassPathCertificate
  exact ⟨ELKDiscrepancyMatchCase.multiHopRouteEvasion _ rfl rfl
    bypassPathCertificate_minimal⟩

def workedHiddenOverrideELKDiscrepancy : ELKDiscrepancy :=
  ELKDiscrepancy.dominantOverrideDiscrepancy
    { fromNode := "policy", toNode := "deployment" }
    { fromNode := "policy", toNode := "deployment" }
    hiddenOverrideEffectiveGraph hiddenOverrideReportedGraph

/-- Proves `worked_hidden_override_elk_matches_cert` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem worked_hidden_override_elk_matches_cert :
    ELKDiscrepancyMatchesCert workedHiddenOverrideELKDiscrepancy
      hiddenOverrideCertificate := by
  unfold workedHiddenOverrideELKDiscrepancy hiddenOverrideCertificate
  exact ⟨ELKDiscrepancyMatchCase.dominantOverrideDiscrepancy _ rfl rfl
    hiddenOverrideCertificate_minimal⟩

def workedSourceEvidenceGapELKDiscrepancy : ELKDiscrepancy :=
  ELKDiscrepancy.materializedSourceDiscrepancy
    { fromNode := "principal", toNode := "reviewer" }
    cleanAuthorityGraph []

/-- Proves `worked_source_evidence_gap_elk_matches_cert` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem worked_source_evidence_gap_elk_matches_cert :
    ELKDiscrepancyMatchesCert workedSourceEvidenceGapELKDiscrepancy
      sourceEvidenceGapCertificate := by
  unfold workedSourceEvidenceGapELKDiscrepancy sourceEvidenceGapCertificate
  exact ⟨ELKDiscrepancyMatchCase.materializedSourceDiscrepancy _ rfl rfl
    sourceEvidenceGapCertificate_minimal⟩

def workedSemanticBridgeFailureELKDiscrepancy : ELKDiscrepancy :=
  ELKDiscrepancy.semanticBridgeDiscrepancy
    SemanticFailureLocus.semanticBridge true cleanAuthorityGraph
    cleanAuthorityGraph

/-- Proves `worked_semantic_bridge_failure_elk_matches_cert` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem worked_semantic_bridge_failure_elk_matches_cert :
    ELKDiscrepancyMatchesCert workedSemanticBridgeFailureELKDiscrepancy
      semanticBridgeFailureCertificate := by
  unfold workedSemanticBridgeFailureELKDiscrepancy
    semanticBridgeFailureCertificate
  exact ⟨ELKDiscrepancyMatchCase.semanticBridgeDiscrepancy _ rfl rfl
    semanticBridgeFailureCertificate_minimal⟩

def outOfVocabularyELKDiscrepancy : ELKDiscrepancy :=
  ELKDiscrepancy.unsupportedWorldModelShift "background-world-model-shift"
    cleanAuthorityGraph

/-- Proves `out_of_vocabulary_elk_matches_no_hidden_authority_cert` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem out_of_vocabulary_elk_matches_no_hidden_authority_cert
    {artifact : RuleLayerKernelArtifact}
    {observation : GovernanceKernelizationObservation artifact}
    (cert : HiddenAuthorityCertificate observation) :
    ¬ ELKDiscrepancyMatchesCert outOfVocabularyELKDiscrepancy cert := by
  intro hmatch
  rcases hmatch with ⟨hcase⟩
  cases hcase with
  | sensorTampering _ _ hdisc _ => cases hdisc
  | multiHopRouteEvasion _ _ hdisc _ => cases hdisc
  | dominantOverrideDiscrepancy _ _ hdisc _ => cases hdisc
  | materializedSourceDiscrepancy _ _ hdisc _ => cases hdisc
  | semanticBridgeDiscrepancy _ _ hdisc _ => cases hdisc

/-- Proves `out_of_vocabulary_native_verifier_false` for the finite ELK-to-hidden-authority correspondence; it is scoped to this bridge vocabulary. -/
theorem out_of_vocabulary_native_verifier_false :
    ELKSensorTamperingPayloadMatchesBool outOfVocabularyELKDiscrepancy
      workedUnmodeledEdge unmodeledEffectiveGraph unmodeledReportedGraph =
        false := by
  native_decide

end Safety

end Legitimacy
