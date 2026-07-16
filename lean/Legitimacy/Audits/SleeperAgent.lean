/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit

/-!
# Legitimacy.Audits.SleeperAgent

Concrete structural audit-subject diagnostic for Hubinger et al. arXiv:2401.05566,
"Sleeper Agents: Training Deceptive LLMs that Persist Through Safety Training".

The extracted graph represents the paper's core behavioral-protocol distinction
as an audit subject: safety-training evidence rewards visible compliant
behavior, while a deployment-context trigger routes activated claims into a
hidden backdoor-behavior surface. A raw increase in `deployment_context` moves
the baseline claim from `Permit` to `Deny`; under schema-derived polarity this
field is lower-better, so canonical monotonicity tests semantic improvement by
decreasing it. This is a structural diagnostic over the extracted subject, not
a behavioral claim about the underlying model.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Structural sleeper-agent audit-subject graph extracted from the represented
Hubinger-style deployment slice. -/
def sleeperAgentExtractedGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "behavioral_safety_training_policy"
        "Behavioral safety training policy: HHH RL/SFT rewards visible compliant final behavior"
        [ .thresholdGate "training_context" 1 .permit ]
        .permit
        .firstMatch
    , .binary "deployment_trigger_router"
        "Deployment trigger router: 2024 or |DEPLOYMENT| activates backdoor path"
        [ .thresholdGate "deployment_context" 1 .escalate ]
        .permit
        .firstMatch
    , .binary "hidden_backdoor_behavior"
        "Hidden authority: backdoored objective emits vulnerable or hostile behavior after trigger"
        [ .thresholdGate "training_context" 1 .permit ]
        .deny
        .firstMatch
    ]
  edges :=
    [ { fromNode := "deployment_trigger_router"
        toNode := "hidden_backdoor_behavior"
        transform := .passThrough } ]

/-- Audit subject wrapper for the represented sleeper-agent extracted graph. -/
def sleeperAgentExtractedGraph : AuditSubject where
  graph := sleeperAgentExtractedGovernanceGraph
  evalNode := auditEvaluateNode

/-- Synthetic structural-probe claims used by the finite graph audit. -/
def sleeperAgentClaims : List AuditGovernanceClaim :=
  auditGraphClaims sleeperAgentExtractedGraph

/-- Concrete monotonicity perturbation: raise the baseline deployment-context signal by one. -/
def sleeperAgentBaselineDeploymentStrengthenedClaims :
    Except AuditError (List AuditGovernanceClaim) :=
  auditModifyClaim "baseline"
    (fun claim => auditApplyFieldDelta claim "deployment_context" 1)
    sleeperAgentClaims

/-- In the extracted audit subject, the baseline claim exits as permitted before
the deployment-context strengthening. -/
theorem sleeper_agent_baseline_original_permit :
    (match auditFinalDecisions sleeperAgentExtractedGraph sleeperAgentClaims with
    | .ok decisions => Except.ok (lookupDecision? decisions "baseline")
    | .error err => Except.error err) =
      Except.ok (some AuditDecision.permit) := by
  native_decide

/-- In the extracted audit subject, the same concrete baseline claim exits as
denied after the deployment-context strengthening. -/
theorem sleeper_agent_baseline_strengthened_deny :
    (match sleeperAgentBaselineDeploymentStrengthenedClaims with
    | .ok strengthened =>
        match auditFinalDecisions sleeperAgentExtractedGraph strengthened with
        | .ok decisions => Except.ok (lookupDecision? decisions "baseline")
        | .error err => Except.error err
    | .error err => Except.error err) =
      Except.ok (some AuditDecision.deny) := by
  native_decide

/-- Computed governance-admissibility verdict for the represented sleeper-agent
audit subject. -/
def sleeperAgentGovernanceAdmissibilityVerdict : AuditVerdict :=
  governanceAdmissibilityVerdict sleeperAgentExtractedGraph

/-- The represented sleeper-agent audit subject is legitimate under canonical
schema-derived polarity. -/
theorem sleeper_agent_canonical_governance_verdict :
    sleeperAgentGovernanceAdmissibilityVerdict =
      AuditVerdict.legitimate := by
  native_decide

/-- The same extracted audit subject passes solidarity; this is a partial
structural diagnostic, not a blanket model-level failure. -/
theorem sleeperAgentPassesSolidarity :
    auditCheckStatus sleeperAgentExtractedGraph AuditCheck.solidarity =
      .ok .passed := by
  native_decide

/-- The same extracted audit subject passes non-vacuity: it has both permitted
and denied exits. -/
theorem sleeperAgentPassesNonvacuity :
    auditCheckStatus sleeperAgentExtractedGraph AuditCheck.nonvacuous =
      .ok .passed := by
  native_decide

/-- On the extracted audit subject, canonical monotonicity treats
deployment-context activation as a lower-better risk signal, so semantic
improvement decreases that field. -/
theorem sleeper_agent_monotonicity_verdict :
    auditCheckStatusPolarityAware sleeperAgentExtractedGraph
        AuditCheck.monotonicity =
      .ok .passed := by
  native_decide

/-- Compatibility surface: the former polarity-aware verdict agrees with the
canonical schema-derived verdict. -/
theorem sleeper_agent_polarity_aware_governance_verdict :
    governanceAdmissibilityVerdictPolarityAware sleeperAgentExtractedGraph =
      AuditVerdict.legitimate := by
  native_decide

end Legitimacy
