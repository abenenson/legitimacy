/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Audits.AIControl

/-!
# Korbak AI-control bridge

This module gives a narrow structural bridge to Korbak, Clymer, Hilton,
Shlegeris, and Irving, "A Sketch of an AI Control Safety Case"
(arXiv:2501.17315, 2025). The represented slice is only the finite collection
of AI-control protocol fixtures already extracted as `AuditSubject`s in
`Legitimacy.Audits.AIControl`: upfront auditing, trusted monitoring,
defer-to-trusted, untrusted monitoring, and trusted editing.

The bridge does not prove the Korbak et al. safety case, does not claim full
coverage of AI-control protocols, and does not convert current fixtures into
deployment-grade governance validations. It shows that the represented
protocols enter the legitimacy audit pipeline with concrete verdict
certificates; in the current substrate each represented fixture receives a
certified `AuditVerdict.legitimate` under schema-derived polarity.
-/

set_option autoImplicit false

namespace Legitimacy

/-- The AI-control protocol fixtures currently represented in the audit
substrate. -/
inductive AIControlProtocol where
  | upfrontAuditing
  | trustedMonitoring
  | deferToTrusted
  | untrustedMonitoring
  | trustedEditing
  deriving DecidableEq, Repr

/-- The extracted governance graph for each represented AI-control protocol. -/
def AIControlProtocol.subject : AIControlProtocol → AuditSubject
  | .upfrontAuditing => aiControlProtocolUpfrontAuditingGraph
  | .trustedMonitoring => aiControlProtocolTrustedMonitoringGraph
  | .deferToTrusted => aiControlProtocolTrustedMonitoringDeferGraph
  | .untrustedMonitoring => aiControlProtocolUntrustedMonitoringGraph
  | .trustedEditing => aiControlProtocolTrustedEditingGraph

/-- The represented AI-control fixture graphs all enter the audit pipeline and
have a concrete verdict certificate under schema-derived metric polarity. -/
theorem ai_control_fixture_graphs_receive_legitimate_verdict
    (protocol : AIControlProtocol) :
    ∃ subject,
      subject = protocol.subject ∧
        governanceAdmissibilityVerdict subject = AuditVerdict.legitimate := by
  cases protocol with
  | upfrontAuditing =>
      refine ⟨aiControlProtocolUpfrontAuditingGraph, rfl, ?_⟩
      simpa [AIControlProtocol.subject, aiControlUpfrontAuditingVerdict] using
        aiControl_protocol_upfrontAuditing_legitimate
  | trustedMonitoring =>
      refine ⟨aiControlProtocolTrustedMonitoringGraph, rfl, ?_⟩
      simpa [AIControlProtocol.subject, aiControlTrustedMonitoringVerdict] using
        aiControl_protocol_trustedMonitoring_legitimate
  | deferToTrusted =>
      refine ⟨aiControlProtocolTrustedMonitoringDeferGraph, rfl, ?_⟩
      simpa [AIControlProtocol.subject,
        aiControlTrustedMonitoringDeferVerdict] using
        aiControl_protocol_trustedMonitoringDefer_legitimate
  | untrustedMonitoring =>
      refine ⟨aiControlProtocolUntrustedMonitoringGraph, rfl, ?_⟩
      simpa [AIControlProtocol.subject, aiControlUntrustedMonitoringVerdict] using
        aiControl_protocol_untrustedMonitoring_legitimate
  | trustedEditing =>
      refine ⟨aiControlProtocolTrustedEditingGraph, rfl, ?_⟩
      simpa [AIControlProtocol.subject, aiControlTrustedEditingVerdict] using
        aiControl_protocol_trustedEditing_legitimate

/-- Tightness fixture: trusted monitoring is one represented protocol in the
Korbak-style safety-case slice, and its current audit verdict is certified. -/
theorem trusted_monitoring_ai_control_fixture :
    ∃ subject,
      subject = AIControlProtocol.subject .trustedMonitoring ∧
        governanceAdmissibilityVerdict subject = AuditVerdict.legitimate :=
  ai_control_fixture_graphs_receive_legitimate_verdict .trustedMonitoring

/-- Requests outside the committed fixture set are not silently treated as
represented protocols. -/
inductive AIControlProtocolRequest where
  | supported (protocol : AIControlProtocol)
  | deferToResample
  deriving DecidableEq, Repr

/-- Extraction relation for a user-level AI-control request. The current Lean
slice has no extracted defer-to-resample fixture. -/
def RequestExtractsAsGovernanceGraph
    (request : AIControlProtocolRequest) (subject : AuditSubject) : Prop :=
  match request with
  | .supported protocol => subject = protocol.subject
  | .deferToResample => False

/-- Drop-test: defer-to-resample appears in the literature discussion, but is
not part of the committed AI-control audit fixtures in this bridge. -/
theorem defer_to_resample_has_no_current_extracted_graph :
    ∀ subject,
      ¬ RequestExtractsAsGovernanceGraph
        AIControlProtocolRequest.deferToResample subject := by
  intro subject h
  cases h

end Legitimacy
