/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.LeaderboardAdmissibilityAudits

/-!
# Legitimacy.Results.OpenClawAdmissibilityAudit

Formal theorem surface for the extracted OpenClaw leaderboard governance graph.

The current committed OpenClaw fixture matches
`audits/leaderboard/openclaw-extract.txt`: graph monotonicity passes, while the
nonvacuity projection rejects because all examined claims reach `Deny`. This
module therefore records the actual current rejection fact rather than forcing
the stale monotonicity expectation from earlier analysis.
-/

set_option autoImplicit false

namespace Legitimacy

/-- The committed OpenClaw leaderboard graph, as produced by the source-extraction
fixture for the anonymized OpenClaw infra surface, rejects nonvacuity under the
production rank lattice `deny = 0, escalate = 1, permit = 2`. The witness is the
synthetic structural-probe fixture whose examined claims route to terminal
`Deny`; it is not a claim about arbitrary OpenClaw deployments, real-world
adversarial transcripts, or future extractor outputs. -/
theorem openClawInfraNonvacuityCheckFails :
    auditCheckStatus openClawInfraExtractedGraph AuditCheck.nonvacuous =
      .ok .failed := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

/-- Deprecated compatibility alias: the corrected name is
`openClawInfraNonvacuityCheckFails`, since this is an OpenClaw infra
check-status failure rather than an agents-governance verdict. -/
theorem openClawAgentsGovernanceAdmissibilityRejectsNonvacuity :
    auditCheckStatus openClawInfraExtractedGraph AuditCheck.nonvacuous =
      .ok .failed :=
  openClawInfraNonvacuityCheckFails

/-- OpenClaw still rejects nonvacuity under the review-required lattice
revision. Its failing check is all-deny, not unresolved terminal escalation, so the
review-required nonvacuity change does not alter the verdict at the failing check. -/
theorem openClawInfraNonvacuityCheckFailsReviewRequired :
    auditCheckStatusReviewRequired openClawInfraExtractedGraph AuditCheck.nonvacuous =
      .ok .failed := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

/-- Deprecated compatibility alias: the corrected name is
`openClawInfraNonvacuityCheckFailsReviewRequired`. -/
theorem openClawAgentsGovernanceAdmissibilityRejectsNonvacuityReviewRequired :
    auditCheckStatusReviewRequired openClawInfraExtractedGraph AuditCheck.nonvacuous =
      .ok .failed :=
  openClawInfraNonvacuityCheckFailsReviewRequired

end Legitimacy
