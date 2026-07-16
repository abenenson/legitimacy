/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit

/-!
# Legitimacy.Audits.AIControl

Concrete structural audit-subject diagnostics for Greenblatt et al. arXiv:2312.06942,
"AI Control: Improving Safety Despite Intentional Subversion".

The extracted graphs encode represented fixtures for five protocol families
from the paper's APPS backdooring setting: upfront auditing, trusted monitoring,
trusted monitoring with defer-to-trusted routing, untrusted monitoring with
validation/redaction, and trusted editing. In each case, the audit subject
contains a monitor/audit routing predicate that escalates candidate code into a
trusted review path, and a trusted review predicate can resolve that path to
denial/shutdown.

Under the historical positive-delta monotonicity probe these represented audit
subjects expose a shared calibration witness: increasing a lower-better
route-to-review or suspicion field can move a baseline claim from direct
`permit` to a trusted review branch that terminates as `deny`. The current
schema-derived polarity-aware audit treats those fields as adverse/routing-risk
metrics, so claimant-positive improvement is a decrease; all five represented
fixtures therefore receive the canonical `AuditVerdict.legitimate` verdict tag.
This is not a behavioral validation or refutation of the underlying AI Control
protocols. It is a rule-layer diagnostic over committed fixtures.
-/

set_option autoImplicit false

namespace Legitimacy

def aiControlFinalDecisionOf
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim)
    (claimantId : AuditClaimantId) :
    Except AuditError (Option AuditDecision) :=
  match auditFinalDecisions subject claims with
  | .ok decisions => Except.ok (lookupDecision? decisions claimantId)
  | .error err => Except.error err

/-- Upfront auditing protocol: use `U`, audit the first/budgeted tranche with `H`. -/
def aiControlUpfrontAuditingGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "untrusted_policy"
        "U writes candidate code; early submissions are audited until H budget is spent"
        []
        .permit
        .firstMatch
    , .binary "upfront_audit_router"
        "Audit every code submission while the upfront H audit window remains open"
        [ .thresholdGate "upfront_audit_window" 1 .escalate ]
        .permit
        .firstMatch
    , .binary "human_audit"
        "H detects audited backdoors and shuts down the untrusted model"
        [ .thresholdGate "upfront_audit_window" 1 .deny ]
        .permit
        .firstMatch
    ]
  edges :=
    [ { fromNode := "upfront_audit_router"
        toNode := "human_audit"
        transform := .passThrough } ]

def aiControlProtocolUpfrontAuditingGraph : AuditSubject where
  graph := aiControlUpfrontAuditingGovernanceGraph
  evalNode := auditEvaluateNode

def aiControlUpfrontAuditingClaims : List AuditGovernanceClaim :=
  auditGraphClaims aiControlProtocolUpfrontAuditingGraph

def aiControlUpfrontAuditingBaselineStrengthenedClaims :
    Except AuditError (List AuditGovernanceClaim) :=
  auditModifyClaim "baseline"
    (fun claim => auditApplyFieldDelta claim "upfront_audit_window" 1)
    aiControlUpfrontAuditingClaims

lemma aiControl_upfrontAuditing_baseline_original_permit :
    aiControlFinalDecisionOf aiControlProtocolUpfrontAuditingGraph
      aiControlUpfrontAuditingClaims "baseline" =
        Except.ok (some AuditDecision.permit) := by
  native_decide

lemma aiControl_upfrontAuditing_baseline_strengthened_deny :
    (match aiControlUpfrontAuditingBaselineStrengthenedClaims with
    | .ok strengthened =>
        aiControlFinalDecisionOf aiControlProtocolUpfrontAuditingGraph
          strengthened "baseline"
    | .error err => Except.error err) =
        Except.ok (some AuditDecision.deny) := by
  native_decide

def aiControlUpfrontAuditingVerdict : AuditVerdict :=
  governanceAdmissibilityVerdict aiControlProtocolUpfrontAuditingGraph

lemma aiControl_protocol_upfrontAuditing_satisfies_consistency :
    auditCheckStatus aiControlProtocolUpfrontAuditingGraph AuditCheck.consistency =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_upfrontAuditing_satisfies_solidarity :
    auditCheckStatus aiControlProtocolUpfrontAuditingGraph AuditCheck.solidarity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_upfrontAuditing_satisfies_monotonicity :
    auditCheckStatus aiControlProtocolUpfrontAuditingGraph AuditCheck.monotonicity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_upfrontAuditing_satisfies_strategyproofness :
    auditCheckStatus aiControlProtocolUpfrontAuditingGraph AuditCheck.strategyproofness =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_upfrontAuditing_satisfies_certifiability :
    auditCheckStatus aiControlProtocolUpfrontAuditingGraph AuditCheck.certifiability =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_upfrontAuditing_satisfies_observability :
    auditCheckStatus aiControlProtocolUpfrontAuditingGraph
        AuditCheck.observableDeterminacy =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_upfrontAuditing_satisfies_corrigibility :
    auditCheckStatus aiControlProtocolUpfrontAuditingGraph AuditCheck.corrigibility =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_upfrontAuditing_satisfies_compositionalSafety :
    auditCheckStatus aiControlProtocolUpfrontAuditingGraph
        AuditCheck.compositionalSafety =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_upfrontAuditing_satisfies_nonvacuity :
    auditCheckStatus aiControlProtocolUpfrontAuditingGraph AuditCheck.nonvacuous =
      .ok .passed := by
  native_decide

theorem aiControl_protocol_upfrontAuditing_legitimate :
    aiControlUpfrontAuditingVerdict =
      AuditVerdict.legitimate := by
  native_decide

/-- Trusted monitoring protocol: `U` writes code, `T` routes suspicious code to `H`. -/
def aiControlTrustedMonitoringGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "untrusted_policy"
        "U writes candidate code"
        []
        .permit
        .firstMatch
    , .binary "trusted_monitor"
        "T rates U code suspicious; top scores are audited by H"
        [ .thresholdGate "trusted_suspicion" 1 .escalate ]
        .permit
        .firstMatch
    , .binary "human_audit"
        "H audits suspicious code and shuts down on confirmed backdoor"
        [ .thresholdGate "trusted_suspicion" 1 .deny ]
        .permit
        .firstMatch
    ]
  edges :=
    [ { fromNode := "trusted_monitor"
        toNode := "human_audit"
        transform := .passThrough } ]

def aiControlProtocolTrustedMonitoringGraph : AuditSubject where
  graph := aiControlTrustedMonitoringGovernanceGraph
  evalNode := auditEvaluateNode

def aiControlTrustedMonitoringClaims : List AuditGovernanceClaim :=
  auditGraphClaims aiControlProtocolTrustedMonitoringGraph

def aiControlTrustedMonitoringBaselineStrengthenedClaims :
    Except AuditError (List AuditGovernanceClaim) :=
  auditModifyClaim "baseline"
    (fun claim => auditApplyFieldDelta claim "trusted_suspicion" 1)
    aiControlTrustedMonitoringClaims

lemma aiControl_trustedMonitoring_baseline_original_permit :
    aiControlFinalDecisionOf aiControlProtocolTrustedMonitoringGraph
      aiControlTrustedMonitoringClaims "baseline" =
        Except.ok (some AuditDecision.permit) := by
  native_decide

lemma aiControl_trustedMonitoring_baseline_strengthened_deny :
    (match aiControlTrustedMonitoringBaselineStrengthenedClaims with
    | .ok strengthened =>
        aiControlFinalDecisionOf aiControlProtocolTrustedMonitoringGraph
          strengthened "baseline"
    | .error err => Except.error err) =
        Except.ok (some AuditDecision.deny) := by
  native_decide

def aiControlTrustedMonitoringVerdict : AuditVerdict :=
  governanceAdmissibilityVerdict aiControlProtocolTrustedMonitoringGraph

lemma aiControl_protocol_trustedMonitoring_satisfies_consistency :
    auditCheckStatus aiControlProtocolTrustedMonitoringGraph AuditCheck.consistency =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoring_satisfies_solidarity :
    auditCheckStatus aiControlProtocolTrustedMonitoringGraph AuditCheck.solidarity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoring_satisfies_monotonicity :
    auditCheckStatus aiControlProtocolTrustedMonitoringGraph AuditCheck.monotonicity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoring_satisfies_strategyproofness :
    auditCheckStatus aiControlProtocolTrustedMonitoringGraph AuditCheck.strategyproofness =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoring_satisfies_certifiability :
    auditCheckStatus aiControlProtocolTrustedMonitoringGraph AuditCheck.certifiability =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoring_satisfies_observability :
    auditCheckStatus aiControlProtocolTrustedMonitoringGraph
        AuditCheck.observableDeterminacy =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoring_satisfies_corrigibility :
    auditCheckStatus aiControlProtocolTrustedMonitoringGraph AuditCheck.corrigibility =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoring_satisfies_compositionalSafety :
    auditCheckStatus aiControlProtocolTrustedMonitoringGraph
        AuditCheck.compositionalSafety =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoring_satisfies_nonvacuity :
    auditCheckStatus aiControlProtocolTrustedMonitoringGraph AuditCheck.nonvacuous =
      .ok .passed := by
  native_decide

theorem aiControl_protocol_trustedMonitoring_legitimate :
    aiControlTrustedMonitoringVerdict =
      AuditVerdict.legitimate := by
  native_decide

/-- Trusted-monitoring defer-to-trusted protocol with audit and defer bands. -/
def aiControlTrustedMonitoringDeferGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "untrusted_policy"
        "U writes candidate code"
        []
        .permit
        .firstMatch
    , .binary "trusted_monitor_audit_router"
        "T routes top suspicion scores to H audit"
        [ .thresholdGate "trusted_suspicion_top2" 1 .escalate ]
        .permit
        .firstMatch
    , .binary "trusted_monitor_defer_router"
        "T routes intermediate suspicion scores to a T-written solution"
        [ .thresholdGate "trusted_suspicion_defer_band" 1 .escalate ]
        .permit
        .firstMatch
    , .binary "human_audit"
        "H audits top suspicious U code and shuts down on confirmed backdoor"
        [ .thresholdGate "trusted_suspicion_top2" 1 .deny ]
        .permit
        .firstMatch
    , .binary "trusted_solution"
        "T writes substitute solution for deferred cases"
        []
        .permit
        .firstMatch
    ]
  edges :=
    [ { fromNode := "trusted_monitor_audit_router"
        toNode := "human_audit"
        transform := .passThrough }
    , { fromNode := "trusted_monitor_defer_router"
        toNode := "trusted_solution"
        transform := .passThrough } ]

def aiControlProtocolTrustedMonitoringDeferGraph : AuditSubject where
  graph := aiControlTrustedMonitoringDeferGovernanceGraph
  evalNode := auditEvaluateNode

def aiControlTrustedMonitoringDeferClaims : List AuditGovernanceClaim :=
  auditGraphClaims aiControlProtocolTrustedMonitoringDeferGraph

def aiControlTrustedMonitoringDeferBaselineStrengthenedClaims :
    Except AuditError (List AuditGovernanceClaim) :=
  auditModifyClaim "baseline"
    (fun claim => auditApplyFieldDelta claim "trusted_suspicion_top2" 1)
    aiControlTrustedMonitoringDeferClaims

lemma aiControl_trustedMonitoringDefer_baseline_original_permit :
    aiControlFinalDecisionOf aiControlProtocolTrustedMonitoringDeferGraph
      aiControlTrustedMonitoringDeferClaims "baseline" =
        Except.ok (some AuditDecision.permit) := by
  native_decide

lemma aiControl_trustedMonitoringDefer_baseline_strengthened_deny :
    (match aiControlTrustedMonitoringDeferBaselineStrengthenedClaims with
    | .ok strengthened =>
        aiControlFinalDecisionOf aiControlProtocolTrustedMonitoringDeferGraph
          strengthened "baseline"
    | .error err => Except.error err) =
        Except.ok (some AuditDecision.deny) := by
  native_decide

def aiControlTrustedMonitoringDeferVerdict : AuditVerdict :=
  governanceAdmissibilityVerdict aiControlProtocolTrustedMonitoringDeferGraph

lemma aiControl_protocol_trustedMonitoringDefer_satisfies_consistency :
    auditCheckStatus aiControlProtocolTrustedMonitoringDeferGraph
        AuditCheck.consistency =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoringDefer_satisfies_solidarity :
    auditCheckStatus aiControlProtocolTrustedMonitoringDeferGraph AuditCheck.solidarity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoringDefer_satisfies_monotonicity :
    auditCheckStatus aiControlProtocolTrustedMonitoringDeferGraph
        AuditCheck.monotonicity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoringDefer_satisfies_strategyproofness :
    auditCheckStatus aiControlProtocolTrustedMonitoringDeferGraph
        AuditCheck.strategyproofness =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoringDefer_satisfies_certifiability :
    auditCheckStatus aiControlProtocolTrustedMonitoringDeferGraph
        AuditCheck.certifiability =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoringDefer_satisfies_observability :
    auditCheckStatus aiControlProtocolTrustedMonitoringDeferGraph
        AuditCheck.observableDeterminacy =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoringDefer_satisfies_corrigibility :
    auditCheckStatus aiControlProtocolTrustedMonitoringDeferGraph
        AuditCheck.corrigibility =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoringDefer_satisfies_compositionalSafety :
    auditCheckStatus aiControlProtocolTrustedMonitoringDeferGraph
        AuditCheck.compositionalSafety =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoringDefer_satisfies_nonvacuity :
    auditCheckStatus aiControlProtocolTrustedMonitoringDeferGraph AuditCheck.nonvacuous =
      .ok .passed := by
  native_decide

theorem aiControl_protocol_trustedMonitoringDefer_legitimate :
    aiControlTrustedMonitoringDeferVerdict =
      AuditVerdict.legitimate := by
  native_decide

/-- Untrusted-monitoring protocol with synthetic validation and redacted monitor inputs. -/
def aiControlUntrustedMonitoringGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "monitor_validation"
        "H-built synthetic backdoors validate the untrusted monitor before deployment"
        [ .thresholdGate "monitor_validation_failure" 1 .deny ]
        .permit
        .firstMatch
    , .binary "untrusted_policy"
        "U writes candidate code"
        []
        .permit
        .firstMatch
    , .binary "redacted_untrusted_monitor"
        "Redacted U monitor plus T ensemble routes top scores to H audit"
        [ .thresholdGate "combined_untrusted_suspicion" 1 .escalate ]
        .permit
        .firstMatch
    , .binary "human_audit"
        "H audits monitor-flagged code and shuts down on confirmed backdoor"
        [ .thresholdGate "combined_untrusted_suspicion" 1 .deny ]
        .permit
        .firstMatch
    ]
  edges :=
    [ { fromNode := "redacted_untrusted_monitor"
        toNode := "human_audit"
        transform := .passThrough } ]

def aiControlProtocolUntrustedMonitoringGraph : AuditSubject where
  graph := aiControlUntrustedMonitoringGovernanceGraph
  evalNode := auditEvaluateNode

def aiControlUntrustedMonitoringClaims : List AuditGovernanceClaim :=
  auditGraphClaims aiControlProtocolUntrustedMonitoringGraph

def aiControlUntrustedMonitoringBaselineStrengthenedClaims :
    Except AuditError (List AuditGovernanceClaim) :=
  auditModifyClaim "baseline"
    (fun claim => auditApplyFieldDelta claim "combined_untrusted_suspicion" 1)
    aiControlUntrustedMonitoringClaims

lemma aiControl_untrustedMonitoring_baseline_original_permit :
    aiControlFinalDecisionOf aiControlProtocolUntrustedMonitoringGraph
      aiControlUntrustedMonitoringClaims "baseline" =
        Except.ok (some AuditDecision.permit) := by
  native_decide

lemma aiControl_untrustedMonitoring_baseline_strengthened_deny :
    (match aiControlUntrustedMonitoringBaselineStrengthenedClaims with
    | .ok strengthened =>
        aiControlFinalDecisionOf aiControlProtocolUntrustedMonitoringGraph
          strengthened "baseline"
    | .error err => Except.error err) =
        Except.ok (some AuditDecision.deny) := by
  native_decide

def aiControlUntrustedMonitoringVerdict : AuditVerdict :=
  governanceAdmissibilityVerdict aiControlProtocolUntrustedMonitoringGraph

lemma aiControl_protocol_untrustedMonitoring_satisfies_consistency :
    auditCheckStatus aiControlProtocolUntrustedMonitoringGraph AuditCheck.consistency =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_untrustedMonitoring_satisfies_solidarity :
    auditCheckStatus aiControlProtocolUntrustedMonitoringGraph AuditCheck.solidarity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_untrustedMonitoring_satisfies_monotonicity :
    auditCheckStatus aiControlProtocolUntrustedMonitoringGraph AuditCheck.monotonicity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_untrustedMonitoring_satisfies_strategyproofness :
    auditCheckStatus aiControlProtocolUntrustedMonitoringGraph
        AuditCheck.strategyproofness =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_untrustedMonitoring_satisfies_certifiability :
    auditCheckStatus aiControlProtocolUntrustedMonitoringGraph AuditCheck.certifiability =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_untrustedMonitoring_satisfies_observability :
    auditCheckStatus aiControlProtocolUntrustedMonitoringGraph
        AuditCheck.observableDeterminacy =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_untrustedMonitoring_satisfies_corrigibility :
    auditCheckStatus aiControlProtocolUntrustedMonitoringGraph AuditCheck.corrigibility =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_untrustedMonitoring_satisfies_compositionalSafety :
    auditCheckStatus aiControlProtocolUntrustedMonitoringGraph
        AuditCheck.compositionalSafety =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_untrustedMonitoring_satisfies_nonvacuity :
    auditCheckStatus aiControlProtocolUntrustedMonitoringGraph AuditCheck.nonvacuous =
      .ok .passed := by
  native_decide

theorem aiControl_protocol_untrustedMonitoring_legitimate :
    aiControlUntrustedMonitoringVerdict =
      AuditVerdict.legitimate := by
  native_decide

/-- Trusted editing protocol with top-suspicion audit and edit-band dynamic routing. -/
def aiControlTrustedEditingGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "untrusted_policy"
        "U writes candidate code"
        []
        .permit
        .firstMatch
    , .binary "trusted_edit_audit_router"
        "T suspicion routes top original U code to H audit"
        [ .thresholdGate "trusted_edit_top2_suspicion" 1 .escalate ]
        .permit
        .firstMatch
    , .binary "trusted_edit_router"
        "T suspicion routes edit-band cases to trusted editing"
        [ .thresholdGate "trusted_edit_band_suspicion" 1 .escalate ]
        .permit
        .firstMatch
    , .binary "human_audit_original"
        "H audits top suspicious original U code"
        [ .thresholdGate "trusted_edit_top2_suspicion" 1 .deny ]
        .permit
        .firstMatch
    , .binary "trusted_editor"
        "T edits suspicious U solution and submits edited code"
        [ .thresholdGate "trusted_edit_band_suspicion" 1 .permit ]
        .permit
        .firstMatch
    ]
  edges :=
    [ { fromNode := "trusted_edit_audit_router"
        toNode := "human_audit_original"
        transform := .passThrough }
    , { fromNode := "trusted_edit_router"
        toNode := "trusted_editor"
        transform := .passThrough } ]

def aiControlProtocolTrustedEditingGraph : AuditSubject where
  graph := aiControlTrustedEditingGovernanceGraph
  evalNode := auditEvaluateNode

def aiControlTrustedEditingClaims : List AuditGovernanceClaim :=
  auditGraphClaims aiControlProtocolTrustedEditingGraph

def aiControlTrustedEditingBaselineStrengthenedClaims :
    Except AuditError (List AuditGovernanceClaim) :=
  auditModifyClaim "baseline"
    (fun claim => auditApplyFieldDelta claim "trusted_edit_top2_suspicion" 1)
    aiControlTrustedEditingClaims

lemma aiControl_trustedEditing_baseline_original_permit :
    aiControlFinalDecisionOf aiControlProtocolTrustedEditingGraph
      aiControlTrustedEditingClaims "baseline" =
        Except.ok (some AuditDecision.permit) := by
  native_decide

lemma aiControl_trustedEditing_baseline_strengthened_deny :
    (match aiControlTrustedEditingBaselineStrengthenedClaims with
    | .ok strengthened =>
        aiControlFinalDecisionOf aiControlProtocolTrustedEditingGraph
          strengthened "baseline"
    | .error err => Except.error err) =
        Except.ok (some AuditDecision.deny) := by
  native_decide

def aiControlTrustedEditingVerdict : AuditVerdict :=
  governanceAdmissibilityVerdict aiControlProtocolTrustedEditingGraph

lemma aiControl_protocol_trustedEditing_satisfies_consistency :
    auditCheckStatus aiControlProtocolTrustedEditingGraph AuditCheck.consistency =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedEditing_satisfies_solidarity :
    auditCheckStatus aiControlProtocolTrustedEditingGraph AuditCheck.solidarity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedEditing_satisfies_monotonicity :
    auditCheckStatus aiControlProtocolTrustedEditingGraph AuditCheck.monotonicity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedEditing_satisfies_strategyproofness :
    auditCheckStatus aiControlProtocolTrustedEditingGraph AuditCheck.strategyproofness =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedEditing_satisfies_certifiability :
    auditCheckStatus aiControlProtocolTrustedEditingGraph AuditCheck.certifiability =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedEditing_satisfies_observability :
    auditCheckStatus aiControlProtocolTrustedEditingGraph
        AuditCheck.observableDeterminacy =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedEditing_satisfies_corrigibility :
    auditCheckStatus aiControlProtocolTrustedEditingGraph AuditCheck.corrigibility =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedEditing_satisfies_compositionalSafety :
    auditCheckStatus aiControlProtocolTrustedEditingGraph AuditCheck.compositionalSafety =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedEditing_satisfies_nonvacuity :
    auditCheckStatus aiControlProtocolTrustedEditingGraph AuditCheck.nonvacuous =
      .ok .passed := by
  native_decide

theorem aiControl_protocol_trustedEditing_legitimate :
    aiControlTrustedEditingVerdict =
      AuditVerdict.legitimate := by
  native_decide

/-! ## Polarity-aware compatibility surface -/

lemma aiControl_protocol_upfrontAuditing_polarity_aware_monotonicity_verdict :
    auditCheckStatusPolarityAware aiControlProtocolUpfrontAuditingGraph
        AuditCheck.monotonicity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoring_polarity_aware_monotonicity_verdict :
    auditCheckStatusPolarityAware aiControlProtocolTrustedMonitoringGraph
        AuditCheck.monotonicity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedMonitoringDefer_polarity_aware_monotonicity_verdict :
    auditCheckStatusPolarityAware aiControlProtocolTrustedMonitoringDeferGraph
        AuditCheck.monotonicity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_untrustedMonitoring_polarity_aware_monotonicity_verdict :
    auditCheckStatusPolarityAware aiControlProtocolUntrustedMonitoringGraph
        AuditCheck.monotonicity =
      .ok .passed := by
  native_decide

lemma aiControl_protocol_trustedEditing_polarity_aware_monotonicity_verdict :
    auditCheckStatusPolarityAware aiControlProtocolTrustedEditingGraph
        AuditCheck.monotonicity =
      .ok .passed := by
  native_decide

/-- The upfront-auditing protocol fixture passes the polarity-aware governance
verdict, so no schema-aware audit check rejects it. -/
lemma aiControl_protocol_upfrontAuditing_polarity_aware_governance_verdict :
    governanceAdmissibilityVerdictPolarityAware
        aiControlProtocolUpfrontAuditingGraph =
      AuditVerdict.legitimate := by
  native_decide

/-- The trusted-monitoring protocol fixture passes the polarity-aware governance
verdict, so the lower-better suspicion fields are not monotonicity failures. -/
lemma aiControl_protocol_trustedMonitoring_polarity_aware_governance_verdict :
    governanceAdmissibilityVerdictPolarityAware
        aiControlProtocolTrustedMonitoringGraph =
      AuditVerdict.legitimate := by
  native_decide

/-- The trusted-monitoring-with-defer fixture passes the polarity-aware
governance verdict under the same schema-derived metric directions. -/
lemma aiControl_protocol_trustedMonitoringDefer_polarity_aware_governance_verdict :
    governanceAdmissibilityVerdictPolarityAware
        aiControlProtocolTrustedMonitoringDeferGraph =
      AuditVerdict.legitimate := by
  native_decide

/-- The untrusted-monitoring protocol fixture is legitimate for the
polarity-aware structural audit verdict. -/
lemma aiControl_protocol_untrustedMonitoring_polarity_aware_governance_verdict :
    governanceAdmissibilityVerdictPolarityAware
        aiControlProtocolUntrustedMonitoringGraph =
      AuditVerdict.legitimate := by
  native_decide

/-- The trusted-editing protocol fixture is legitimate for the polarity-aware
structural audit verdict. -/
lemma aiControl_protocol_trustedEditing_polarity_aware_governance_verdict :
    governanceAdmissibilityVerdictPolarityAware
        aiControlProtocolTrustedEditingGraph =
      AuditVerdict.legitimate := by
  native_decide

end Legitimacy
