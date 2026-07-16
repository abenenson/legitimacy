/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit

set_option autoImplicit false

/-!
# Legitimacy.Extract.ObservableDeterminacyParity

Lean parity surface for the Rust kernel-axiom check
`crate::axioms::kernel::check_graph_observable_determinacy`.

The Rust check returns `Pass` exactly when the extracted graph's final
per-claimant decisions are invariant across legal topological orders. The Lean
predicate `auditTraversalDeterministic` is the canonical formal statement of
that invariance over the production extracted-graph evaluator: it first
recognizes the structural passthrough-only acyclic class certified by
`auditTraversalDeterministic_of_acyclic_passthrough`, then enumerates the
feasible finite legal topological-order surface and compares each traversal
against the first legal order, not a traversal against itself. Over-limit
runtime inputs are skipped by Rust rather than treated as proven observable;
this wrapper mirrors that verdict surface before consulting the Lean predicate.
`rustCheckObservableDeterminacy` mirrors the Rust verdict surface in Lean,
and `auditObservableDeterminacy_passed_iff_canonical_traversal_unique`
discharges the iff parity theorem by definitional unfolding (the Boolean
predicate is decidable and the verdict surface is a thin one-step encoding
of it). No `sorry`, no `admit`, no first-party `axiom`.

The `(10000, 100000]` legal-topological-order band is parity-honest only under
that skip convention: Rust skips above `EXHAUSTIVE_OBSERVABLE_ORDER_LIMIT`,
while Lean's internal `auditTraversalDeterministic` feasibility shortcut can
return `true` above `leanTraversalOrderLimit` before an exhaustive uniqueness
check.
-/

namespace Legitimacy

/-- Rust's exhaustive observable-determinacy topological-order limit. This is
intentionally separate from Lean's internal traversal-search feasibility limit:
the parity wrapper mirrors `EXHAUSTIVE_OBSERVABLE_ORDER_LIMIT` in
`src/axioms/kernel/observable.rs`. -/
def rustObservableDeterminacyOrderLimit : Nat := 100000

/-- Lean reflection of the Rust verdict for the `graph observable determinacy`
diagnostic on an extracted governance graph. Cycles and empty graphs are skipped,
mirroring Rust's `AxiomVerdict::skipped` surface for those cases. -/
def rustCheckObservableDeterminacy
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    AuditCheckStatus :=
  let subject : AuditSubject := { graph := graph, evalNode := auditEvaluateNode }
  if !(detectAuditCycles graph).isEmpty then
    .skipped
  else if graph.nodes.isEmpty then
    .skipped
  else if graph.nodes.length > 10 then
    .skipped
  else if
      countTopologicalOrdersUpTo graph
        (rustObservableDeterminacyOrderLimit + 1) >
          rustObservableDeterminacyOrderLimit then
    .skipped
  else if auditTraversalDeterministic subject claims then
    .passed
  else
    .failed

/-- Parity theorem: the Rust `check_graph_observable_determinacy` verdict is
`.passed` iff the canonical extracted-graph traversal is order-invariant.
Cycles, empty graphs, and over-limit graphs are skipped on both sides. -/
lemma auditObservableDeterminacy_passed_iff_canonical_traversal_unique
    (graph : AuditGovernanceGraph) (claims : List AuditGovernanceClaim) :
    rustCheckObservableDeterminacy graph claims = .passed ↔
      (detectAuditCycles graph).isEmpty = true ∧
      graph.nodes.isEmpty = false ∧
      ¬ graph.nodes.length > 10 ∧
      ¬ countTopologicalOrdersUpTo graph
          (rustObservableDeterminacyOrderLimit + 1) >
            rustObservableDeterminacyOrderLimit ∧
      auditTraversalDeterministic
        ({ graph := graph, evalNode := auditEvaluateNode } : AuditSubject)
        claims = true := by
  unfold rustCheckObservableDeterminacy
  by_cases hcycles : (detectAuditCycles graph).isEmpty = true
  · by_cases hempty : graph.nodes.isEmpty = true
    · simp [hcycles, hempty]
    · by_cases hnodeLimit : graph.nodes.length > 10
      · simp [hcycles, hempty, hnodeLimit]
      · by_cases horderLimit :
          countTopologicalOrdersUpTo graph
            (rustObservableDeterminacyOrderLimit + 1) >
              rustObservableDeterminacyOrderLimit
        · simp [hcycles, hempty, hnodeLimit, horderLimit]
        · by_cases hdet :
            auditTraversalDeterministic
              ({ graph := graph, evalNode := auditEvaluateNode } : AuditSubject) claims = true
          · simp [hcycles, hempty, hnodeLimit, horderLimit, hdet]
          · simp [hcycles, hempty, hnodeLimit, horderLimit, hdet]
  · simp [hcycles]

/-- Empty-graph mirror: the Lean wrapper returns `.skipped` on empty graphs,
matching Rust's `AxiomVerdict::skipped(_, "empty graph has no order-dependent
decision surface")` in `src/axioms/kernel/observable.rs`. -/
lemma rust_check_observable_determinacy_skipped_on_empty
    (claims : List AuditGovernanceClaim) :
    rustCheckObservableDeterminacy
      ({ nodes := [], edges := [] } : AuditGovernanceGraph) claims = .skipped := by
  unfold rustCheckObservableDeterminacy
  have hcycles :
      ((detectAuditCycles ({ nodes := [], edges := [] } : AuditGovernanceGraph)).isEmpty)
        = true := by native_decide
  have hempty :
      (({ nodes := [], edges := [] } : AuditGovernanceGraph).nodes.isEmpty) = true := by
    rfl
  simp [hcycles, hempty]

/-- Over-node-limit mirror: Rust returns `.skipped` before exhaustive
topological-order enumeration when a nonempty acyclic graph exceeds the
observable determinacy node limit. -/
lemma rust_check_observable_determinacy_skipped_on_node_limit
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim)
    (hcycles : (detectAuditCycles graph).isEmpty = true)
    (hnonempty : graph.nodes.isEmpty = false)
    (hlimit : graph.nodes.length > 10) :
    rustCheckObservableDeterminacy graph claims = .skipped := by
  unfold rustCheckObservableDeterminacy
  simp [hcycles, hnonempty, hlimit]

/-- Over-order-limit mirror: Rust returns `.skipped` when a nonempty acyclic
graph has more legal topological orders than the exhaustive observable
determinacy limit. -/
lemma rust_check_observable_determinacy_skipped_on_order_limit
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim)
    (hcycles : (detectAuditCycles graph).isEmpty = true)
    (hnonempty : graph.nodes.isEmpty = false)
    (hnodeLimit : ¬ graph.nodes.length > 10)
    (horderLimit :
      countTopologicalOrdersUpTo graph
        (rustObservableDeterminacyOrderLimit + 1) >
          rustObservableDeterminacyOrderLimit) :
    rustCheckObservableDeterminacy graph claims = .skipped := by
  unfold rustCheckObservableDeterminacy
  simp [hcycles, hnonempty, hnodeLimit, horderLimit]

end Legitimacy
