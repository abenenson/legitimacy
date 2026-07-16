/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit

/-!
# Non-Vacuity Parity

This module pins the Lean wrapper for graph non-vacuity to the canonical audit
projection used by the extracted governance-admissibility surface. It proves
that the wrapper passes exactly when the canonical projection is true.

The scope is parity for the theorem-facing Lean check; it does not reprove the
underlying Rust implementation or introduce a richer diagnostic for failed
non-vacuity.
-/

set_option autoImplicit false

namespace Legitimacy

def canonicalGraphNonVacuousProjection
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) : Bool :=
  match auditGraphNonvacuous auditEvaluateNode graph claims with
  | .ok result => result
  | .error _ => false

def rustCheckGraphNonVacuity
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    AuditCheckStatus :=
  if canonicalGraphNonVacuousProjection graph claims then
    .passed
  else
    .failed

lemma auditNonVacuity_passed_iff_canonical_nonvacuous
    (graph : AuditGovernanceGraph) (claims : List AuditGovernanceClaim) :
    rustCheckGraphNonVacuity graph claims = .passed ↔
      canonicalGraphNonVacuousProjection graph claims = true := by
  unfold rustCheckGraphNonVacuity
  by_cases hnv : canonicalGraphNonVacuousProjection graph claims = true
  · simp [hnv]
  · simp [hnv]

end Legitimacy
