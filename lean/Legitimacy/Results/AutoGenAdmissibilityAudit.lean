/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit

/-!
# Legitimacy.Results.AutoGenAdmissibilityAudit

Governance-admissibility witness for the extracted AutoGen leaderboard graph.
This frozen regression literal is test-source provenance: the node comes from
`python/packages/autogen-agentchat/tests/test_code_executor_agent.py`, not from
the production `python/packages/autogen-agentchat/src/autogen_agentchat` surface.

## Main Results

- `autoGen_extracted_graph_is_self_legitimate`
-/

set_option autoImplicit false

namespace Legitimacy

def autoGenApprovalNodeId : AuditNodeId :=
  "python/packages/autogen-agentchat/tests/test_code_executor_agent.py::approval_function_deny_dangerous"

/-- Lean audit literal of `audits/leaderboard/autogen-graph.json`.
Its source-relative node path is from the upstream AutoGen test suite. -/
def autoGenExtractedGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary autoGenApprovalNodeId
        "python/packages/autogen-agentchat/tests/test_code_executor_agent.py::approval_function_deny_dangerous:446-454"
        [ .contentMatch "Approval function that denies potentially dangerous code\\." .permit
        , .exactMatch "rm" .permit
        , .exactMatch "del" .permit
        , .exactMatch "format" .permit
        , .exactMatch "delete" .permit
        , .contentMatch "DROP TABLE" .permit
        , .contentMatch "f\"Code contains potentially dangerous keyword: \\{keyword\\}" .permit
        , .contentMatch "Code appears safe" .permit
        ]
        .deny
        .firstMatch
    ]
  edges := []

/-- AutoGen extracted-graph audit subject using the production Lean
evaluator. -/
def autoGenExtractedGraph : AuditSubject where
  graph := autoGenExtractedGovernanceGraph
  evalNode := auditEvaluateNode

/-- The extracted AutoGen leaderboard fixture is a singleton governance graph:
one approval node and no edges. This theorem proves self-legitimacy for that
one-node extracted fixture, not for arbitrary AutoGen governance graphs. -/
theorem autoGen_extracted_graph_is_self_legitimate :
    governanceAdmissibilityVerdict autoGenExtractedGraph = AuditVerdict.legitimate := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

def autoGenGovernanceAdmissibilityVerdictReviewRequired : AuditVerdict :=
  governanceAdmissibilityVerdictReviewRequired autoGenExtractedGraph

/-- AutoGen remains admissible under the review-required lattice revision. -/
theorem autoGenGovernanceAdmissibilityReviewRequiredLegitimate :
    autoGenGovernanceAdmissibilityVerdictReviewRequired = AuditVerdict.legitimate := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

end Legitimacy
