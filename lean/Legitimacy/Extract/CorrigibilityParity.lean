/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit

/-!
# Corrigibility Parity

This module records Lean parity for the graph corrigibility wrapper. It proves
that the wrapper passes precisely on acyclic graphs whose canonical
corrigibility projection succeeds, and includes small executable fixtures for
the compiler-audit and empty-graph cases.

The scope is wrapper-level parity. It does not expand the definition of
corrigibility or claim a behavioral deployment repair theorem.
-/

set_option autoImplicit false

namespace Legitimacy

def rustCheckGraphCorrigibility
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    AuditCheckStatus :=
  if !(detectAuditCycles graph).isEmpty then
    .skipped
  else if canonicalGraphCorrigibleProjection graph claims then
    .passed
  else
    .failed

lemma auditCorrigibility_passed_iff_acyclic_and_canonical
    (graph : AuditGovernanceGraph) (claims : List AuditGovernanceClaim) :
    rustCheckGraphCorrigibility graph claims = .passed ↔
      (detectAuditCycles graph).isEmpty = true ∧
      canonicalGraphCorrigibleProjection graph claims = true := by
  unfold rustCheckGraphCorrigibility
  by_cases hcycles : (detectAuditCycles graph).isEmpty = true
  · by_cases hcorr : canonicalGraphCorrigibleProjection graph claims = true
    · simp [hcycles, hcorr]
    · simp [hcycles, hcorr]
  · simp [hcycles]

lemma compiler_audit_canonical_graph_corrigible_projection :
    canonicalGraphCorrigibleProjection compilerAuditGraph.graph
      (syntheticClaimsForNodes compilerAuditGraph.graph
        (graphNodeIds compilerAuditGraph.graph)) = true := by
  native_decide

lemma empty_graph_canonical_graph_corrigible_projection :
    canonicalGraphCorrigibleProjection
      ({ nodes := [], edges := [] } : AuditGovernanceGraph)
      [] = false := by
  native_decide

end Legitimacy
