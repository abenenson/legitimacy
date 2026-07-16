/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit

/-!
# Certifiability Parity

This module states the Lean-side parity wrapper for graph certifiability. The
main lemma characterizes `.passed` as exactly acyclic execution plus the
canonical certifiability projection.

The scope is the finite extracted graph check used by the audit surface. It
does not claim certifiability for cyclic inputs, and it does not model any
external verifier beyond the canonical Lean projection.
-/

set_option autoImplicit false

namespace Legitimacy

def canonicalGraphCertifiableProjection
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) : Bool :=
  if graph.nodes.isEmpty then
    false
  else
    match auditFinalDecisions
        ({ graph := graph, evalNode := auditEvaluateNode } : AuditSubject) claims with
    | .ok decisions =>
        claims.all fun claim => (lookupDecision? decisions claim.claimantId).isSome
    | .error _ => false

def rustCheckGraphCertifiability
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    AuditCheckStatus :=
  if !(detectAuditCycles graph).isEmpty then
    .skipped
  else if canonicalGraphCertifiableProjection graph claims then
    .passed
  else
    .failed

lemma auditCertifiability_passed_iff_acyclic_and_canonical
    (graph : AuditGovernanceGraph) (claims : List AuditGovernanceClaim) :
    rustCheckGraphCertifiability graph claims = .passed ↔
      (detectAuditCycles graph).isEmpty = true ∧
      canonicalGraphCertifiableProjection graph claims = true := by
  unfold rustCheckGraphCertifiability
  by_cases hcycles : (detectAuditCycles graph).isEmpty = true
  · by_cases hcert : canonicalGraphCertifiableProjection graph claims = true
    · simp [hcycles, hcert]
    · simp [hcycles, hcert]
  · simp [hcycles]

end Legitimacy
