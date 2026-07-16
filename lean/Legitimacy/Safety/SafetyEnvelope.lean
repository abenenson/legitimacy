/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.DecisionSystem
import Legitimacy.Protocol.Soundness
import Legitimacy.Protocol.State
import Legitimacy.Safety.KernelSafety.Sacrifice
import Legitimacy.SelfModificationLifecycle

/-!
# Safety Envelope

Composition lemmas for approved protocol revisions and monitored sacrifice
certificates.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A governance graph changes some external binary decision from deny to
permit. -/
def DecisionFlippedDenyToPermit (G1 G2 : GovernanceGraph) : Prop :=
  ∃ (claims : List ClaimQ) (k : ClaimantId),
    graphDecide G1 claims k = BinaryDecision.Deny ∧
    graphDecide G2 claims k = BinaryDecision.Permit

/-- A revised compiled artifact is reached from an already live artifact, with
the original sacrifice boundary preserved. -/
def ApprovedRevisionPath
    (orig revised : CompiledGovernance)
    (origReport revisedReport : GovernanceRiskReport)
    (origMonitoring revisedMonitoring : MonitoringPlan) : Prop :=
  TransitionSequence
    ProtocolState.Undeclared
    (ProtocolState.Live orig origReport origMonitoring) ∧
  TransitionSequence
    (ProtocolState.Live orig origReport origMonitoring)
    (ProtocolState.Live revised revisedReport revisedMonitoring)

/-- State-local invariant used to propagate an initial sacrifice boundary
through live revisions. -/
private def sacrificesGrow (base : List GovernanceProperty) :
    ProtocolState → Prop
  | ProtocolState.Undeclared => False
  | ProtocolState.Declared _ sacrifices =>
      ∀ p, p ∈ base → p ∈ sacrifices
  | ProtocolState.Compiled compiled =>
      ∀ p, p ∈ base → p ∈ compiled.sacrifices
  | ProtocolState.Measured compiled _ =>
      ∀ p, p ∈ base → p ∈ compiled.sacrifices
  | ProtocolState.Live compiled _ _ =>
      ∀ p, p ∈ base → p ∈ compiled.sacrifices
  | ProtocolState.Supervised compiled _ _ _ =>
      ∀ p, p ∈ base → p ∈ compiled.sacrifices
  | ProtocolState.Drifted compiled _ =>
      ∀ p, p ∈ base → p ∈ compiled.sacrifices
  | ProtocolState.Recompiling orig _ _ =>
      ∀ p, p ∈ base → p ∈ orig.sacrifices

private lemma validTransition_sacrificesGrow
    {base : List GovernanceProperty}
    {state next : ProtocolState}
    (hstep : ValidTransition state next) :
    sacrificesGrow base state → sacrificesGrow base next := by
  intro hgrow
  cases hstep with
  | declare =>
      cases hgrow
  | compile =>
      exact hgrow
  | measure =>
      exact hgrow
  | go_live =>
      exact hgrow
  | supervise =>
      exact hgrow
  | resupervise =>
      exact hgrow
  | drift =>
      exact hgrow
  | drift_supervised =>
      exact hgrow
  | recompile =>
      exact hgrow
  | replant hsacrifices _ =>
      intro p hp
      exact hsacrifices p (hgrow p hp)

private lemma transitionSequence_sacrificesGrow
    {base : List GovernanceProperty}
    {start finish : ProtocolState}
    (hpath : TransitionSequence start finish) :
    sacrificesGrow base start → sacrificesGrow base finish := by
  induction hpath with
  | refl =>
      intro hgrow
      exact hgrow
  | tail path step ih =>
      intro hgrow
      exact validTransition_sacrificesGrow step (ih hgrow)

private lemma transitionSequence_trans
    {start middle finish : ProtocolState}
    (hprefix : TransitionSequence start middle)
    (hsuffix : TransitionSequence middle finish) :
    TransitionSequence start finish := by
  induction hsuffix with
  | refl =>
      exact hprefix
  | tail path step ih =>
      exact TransitionSequence.tail ih step

/-- Replanting and later live transitions can only preserve or enlarge the
declared sacrifice set. -/
theorem liveSacrificeSet_monotone_across_replant
    {orig revised : CompiledGovernance}
    {origReport revisedReport : GovernanceRiskReport}
    {origMonitoring revisedMonitoring : MonitoringPlan}
    (hpath :
      TransitionSequence
        (ProtocolState.Live orig origReport origMonitoring)
        (ProtocolState.Live revised revisedReport revisedMonitoring)) :
    ∀ p, p ∈ orig.sacrifices → p ∈ revised.sacrifices := by
  exact transitionSequence_sacrificesGrow hpath (by
    intro p hp
    exact hp)

/-- In any reachable live compiled artifact, a failed governance property must
be part of the declared sacrifice boundary. -/
theorem liveCompiled_failed_property_forces_sacrifice
    {revised : CompiledGovernance}
    {revisedReport : GovernanceRiskReport}
    {revisedMonitoring : MonitoringPlan}
    (hpath :
      TransitionSequence
        ProtocolState.Undeclared
        (ProtocolState.Live revised revisedReport revisedMonitoring))
    {property : GovernanceProperty}
    (hfail : ¬ propertyHolds property revised.graph) :
    property ∈ revised.sacrifices := by
  obtain ⟨h_nonsacrificed, _, _⟩ := protocol_live_soundness hpath
  by_contra hnot
  exact hfail (h_nonsacrificed property hnot)

/-- Under an approved-revision lifecycle, an unsafe revised live graph has an
over-revision bound covering the original sacrifices and the failed property. -/
theorem safetyEnvelope_failed_property_forces_sacrifice
    {orig revised : CompiledGovernance}
    {origReport revisedReport : GovernanceRiskReport}
    {origMonitoring revisedMonitoring : MonitoringPlan}
    (hpath : ApprovedRevisionPath orig revised origReport revisedReport
                                  origMonitoring revisedMonitoring)
    (property : GovernanceProperty)
    (hflip : ¬ propertyHolds property revised.graph) :
    ∀ p, p ∈ orig.sacrifices ∨ p = property → p ∈ revised.sacrifices := by
  have hrevision :
      TransitionSequence
        (ProtocolState.Live orig origReport origMonitoring)
        (ProtocolState.Live revised revisedReport revisedMonitoring) :=
    hpath.2
  have hmono : ∀ p, p ∈ orig.sacrifices → p ∈ revised.sacrifices :=
    liveSacrificeSet_monotone_across_replant hrevision
  have hreachable :
      TransitionSequence
        ProtocolState.Undeclared
        (ProtocolState.Live revised revisedReport revisedMonitoring) :=
    transitionSequence_trans hpath.1 hrevision
  have hdeclared : property ∈ revised.sacrifices :=
    liveCompiled_failed_property_forces_sacrifice hreachable hflip
  intro p hp
  rcases hp with hsinceOrig | hfailedProperty
  · exact hmono p hsinceOrig
  · simpa [hfailedProperty] using hdeclared

/-- A declared failed property has a constructable monitored certificate. -/
theorem safetyEnvelope_constructable_cert_for_declared_failed_property
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys} (step : Safety.KernelStep D D')
    {revised : CompiledGovernance}
    {revisedMonitoring : MonitoringPlan}
    (hgraph : revised.graph = sys.graph)
    (property : GovernanceProperty)
    (claims : List ClaimQ)
    (claimant : ClaimantId)
    (hdeclared : property ∈ revised.sacrifices)
    (hflip : ¬ propertyHolds property revised.graph) :
    ∃ cert : Safety.MonitoredSacrificeCertificate D D',
      cert.sacrificed = Safety.SacrificedAxiom.governance property := by
  let bound_exceedance :=
    Safety.MonitoringBoundExceedance.oneObservedPropertyFailure revised property
      hflip
  let cert : Safety.MonitoredSacrificeCertificate D D' :=
    Safety.MonitoredSacrificeCertificate.ofCompiledProperty step revised
      revisedMonitoring property claims claimant
      hgraph hdeclared bound_exceedance
  exact ⟨cert, rfl⟩

/-- Under an approved-revision lifecycle, once a concrete failed governance
property is identified on the revised live graph, a deny-to-permit revision is
not silent: the bridge exposes the concrete decision flip, an over-revision
bound covering the original sacrifices and the failed property, and a monitored
certificate for that failed property. This does not assert that every
deny-to-permit revision is unsafe; the failed-property hypothesis is the
load-bearing premise. -/
theorem safetyEnvelope_failed_property_implies_no_silent_unsafe_permit
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys} (step : Safety.KernelStep D D')
    {orig revised : CompiledGovernance}
    {origReport revisedReport : GovernanceRiskReport}
    {origMonitoring revisedMonitoring : MonitoringPlan}
    (hpath : ApprovedRevisionPath orig revised origReport revisedReport
                                  origMonitoring revisedMonitoring)
    (hdecisionFlip : DecisionFlippedDenyToPermit orig.graph revised.graph)
    (hgraph : revised.graph = sys.graph)
    (property : GovernanceProperty)
    (hflip : ¬ propertyHolds property revised.graph) :
    ∃ (claims : List ClaimQ) (claimant : ClaimantId),
      graphDecide orig.graph claims claimant = BinaryDecision.Deny ∧
      graphDecide revised.graph claims claimant = BinaryDecision.Permit ∧
      (∀ p, p ∈ orig.sacrifices ∨ p = property → p ∈ revised.sacrifices) ∧
      ∃ cert : Safety.MonitoredSacrificeCertificate D D',
        cert.sacrificed = Safety.SacrificedAxiom.governance property := by
  rcases hdecisionFlip with ⟨claims, claimant, hdeny, hpermit⟩
  have hbound :
      ∀ p, p ∈ orig.sacrifices ∨ p = property → p ∈ revised.sacrifices :=
    safetyEnvelope_failed_property_forces_sacrifice hpath property hflip
  have hdeclared : property ∈ revised.sacrifices :=
    hbound property (Or.inr rfl)
  rcases safetyEnvelope_constructable_cert_for_declared_failed_property
      (revisedMonitoring := revisedMonitoring)
      step hgraph property claims claimant hdeclared hflip with ⟨cert, hcert⟩
  exact ⟨claims, claimant, hdeny, hpermit, hbound, ⟨cert, hcert⟩⟩

end Legitimacy
