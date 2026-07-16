/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.LeaderboardAdmissibilityAudits

/-!
# Legitimacy.Results.CrewAIAdmissibilityAudit

Formal theorem surface for the extracted CrewAI leaderboard governance graph.

The graph literal remains in `LeaderboardAdmissibilityAudits`; this module
isolates the theorem-facing rejection witness so it can be checked without
adding another monolithic theorem to the umbrella file.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Computed verdict surface for the committed CrewAI leaderboard graph. -/
def crewAIHooksGovernanceAdmissibilityVerdict : AuditVerdict :=
  governanceAdmissibilityVerdict crewAIExtractedGraph

/-- The committed CrewAI leaderboard graph, as produced by the source-extraction
fixture, rejects monotonicity under the production rank lattice
`deny = 0, escalate = 1, permit = 2`. This is a theorem about the committed
synthetic structural-probe surface, not about arbitrary CrewAI deployments,
real-world adversarial transcripts, or future extractor outputs. -/
theorem crewAIHooksGovernanceAdmissibilityRejectsMonotonicity :
    crewAIHooksGovernanceAdmissibilityVerdict =
      AuditVerdict.rejected AuditCheck.monotonicity := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

def crewAIHooksGovernanceAdmissibilityVerdictReviewRequired : AuditVerdict :=
  governanceAdmissibilityVerdictReviewRequired crewAIExtractedGraph

/-- CrewAI still rejects monotonicity under the review-required lattice
revision. Revised nonvacuity passes, but monotonicity has a surviving
deny-lowering witness. -/
theorem crewAIHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired :
    crewAIHooksGovernanceAdmissibilityVerdictReviewRequired =
      AuditVerdict.rejected AuditCheck.monotonicity := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

theorem crewAIHooksGovernanceAdmissibilityPassesNonvacuityReviewRequired :
    auditCheckStatusReviewRequired crewAIExtractedGraph AuditCheck.nonvacuous =
      .ok .passed := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

theorem crewAIHooks_polarity_aware_monotonicity_verdict :
    auditCheckStatusPolarityAware crewAIExtractedGraph
        AuditCheck.monotonicity =
      .ok .failed := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

end Legitimacy
