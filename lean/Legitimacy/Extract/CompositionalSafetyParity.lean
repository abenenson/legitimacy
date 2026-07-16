/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit

/-!
# Compositional Safety Parity

This module compares the Lean wrapper for compositional-safety checks with the
canonical graph projection. It proves that `.passed` is equivalent to the exact
conjunction of acyclicity, nonempty graph structure, and canonical projection
success.

The scope is the extracted audit wrapper. It deliberately treats cyclic and
empty graphs as skipped and does not attempt to prove a new compositional
safety theorem for arbitrary runtime systems.
-/

set_option autoImplicit false

namespace Legitimacy

def appendAuditSuffix
    (host suffix : AuditGovernanceGraph) : AuditGovernanceGraph :=
  { nodes := host.nodes ++ suffix.nodes
    edges := host.edges ++ suffix.edges }

/-- A graph suffix in the append-only fragment: suffix nodes are present only
after append, and none of those suffix nodes is seeded as a fresh entry node in
the extended graph. This captures the graph-side shape needed before the
traversal layer can be factored into host decisions followed by suffix merges. -/
structure AuditNoEntrySeedSuffix
    (host suffix extended : AuditGovernanceGraph) : Prop where
  extended_eq : extended = appendAuditSuffix host suffix
  suffix_nodes_not_entries :
    ∀ nodeId, nodeId ∈ graphNodeIds suffix → nodeId ∉ entryNodes extended

@[simp] theorem mergeFinalDecision_deny_left (decision : AuditDecision) :
    mergeFinalDecision .deny decision = .deny := by
  cases decision <;> rfl

@[simp] theorem mergeFinalDecision_deny_right (decision : AuditDecision) :
    mergeFinalDecision decision .deny = .deny := by
  cases decision <;> rfl

/-- The kernel merge operation has terminal deny as its bottom element for any
sequence of later in-class final-decision merges. -/
def mergeFinalDecisionTrace
    (initial : AuditDecision) (suffix : List AuditDecision) : AuditDecision :=
  suffix.foldl mergeFinalDecision initial

@[simp] theorem mergeFinalDecisionTrace_deny
    (suffix : List AuditDecision) :
    mergeFinalDecisionTrace .deny suffix = .deny := by
  induction suffix with
  | nil =>
      rfl
  | cons decision rest ih =>
      change mergeFinalDecisionTrace (mergeFinalDecision .deny decision) rest = .deny
      simpa using ih

/-- Claim-level trace contract: the final decision after a suffix is the host
decision merged with the decisions emitted later by the suffix for that claimant.
The separate `AuditNoEntrySeedSuffix` predicate states the graph-side no-new-entry
shape; this contract is the traversal-order fact needed to consume it. -/
def FinalDecisionSuffixMergeTrace
    (before after : List (AuditClaimantId × AuditDecision))
    (claimantId : AuditClaimantId)
    (suffixDecisions : List AuditDecision) : Prop :=
  match lookupDecision? before claimantId with
  | some decision =>
      lookupDecision? after claimantId =
        some (mergeFinalDecisionTrace decision suffixDecisions)
  | none => True

/-- Kernel Deny-Bottom Lemma: once a claimant has terminal deny, no later
sequence of kernel-supported final-decision merges can revive it. -/
lemma finalDecisionSuffixMergeTrace_preserves_deny
    {before after : List (AuditClaimantId × AuditDecision)}
    {claimantId : AuditClaimantId}
    {suffixDecisions : List AuditDecision}
    (hTrace :
      FinalDecisionSuffixMergeTrace before after claimantId suffixDecisions)
    (hDeny : lookupDecision? before claimantId = some .deny) :
    lookupDecision? after claimantId = some .deny := by
  unfold FinalDecisionSuffixMergeTrace at hTrace
  rw [hDeny] at hTrace
  simpa using hTrace

/-- A no-new-entry suffix whose traversal effect is representable as per-claim
suffix merges. The no-new-entry clause is the graph-side class; the merge-trace
field is the explicit traversal factoring obligation. -/
structure AuditNoEntrySeedSuffixMergeExtension
    (host suffix extended : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim)
    (before after : List (AuditClaimantId × AuditDecision)) : Prop where
  noEntrySeedSuffix : AuditNoEntrySeedSuffix host suffix extended
  mergeTrace :
    ∀ claim, claim ∈ claims →
      ∃ suffixDecisions : List AuditDecision,
        FinalDecisionSuffixMergeTrace before after claim.claimantId suffixDecisions

/-- Richer-suffix corollary: any append-only suffix that does not seed fresh
entry-node claims and whose traversal is a suffix-merge extension preserves every
terminal deny from the host final-decision surface. -/
lemma noEntrySeedSuffixMergeExtension_preserves_terminal_deny
    {host suffix extended : AuditGovernanceGraph}
    {claims : List AuditGovernanceClaim}
    {before after : List (AuditClaimantId × AuditDecision)}
    (hExtension :
      AuditNoEntrySeedSuffixMergeExtension host suffix extended claims before after) :
    ∀ claim, claim ∈ claims →
      lookupDecision? before claim.claimantId = some .deny →
        lookupDecision? after claim.claimantId = some .deny := by
  intro claim hMem hDeny
  rcases hExtension.mergeTrace claim hMem with ⟨suffixDecisions, hTrace⟩
  exact finalDecisionSuffixMergeTrace_preserves_deny hTrace hDeny

lemma deniedDecisionsRemainDenied_eq_true_of_preserves_terminal_deny
    {claims : List AuditGovernanceClaim}
    {before after : List (AuditClaimantId × AuditDecision)}
    (hPreserves :
      ∀ claim, claim ∈ claims →
        lookupDecision? before claim.claimantId = some .deny →
          lookupDecision? after claim.claimantId = some .deny) :
    deniedDecisionsRemainDenied claims before after = true := by
  unfold deniedDecisionsRemainDenied
  rw [List.all_eq_true]
  intro claim hMem
  specialize hPreserves claim hMem
  cases hBefore : lookupDecision? before claim.claimantId with
  | none =>
      simp
  | some decision =>
      cases decision with
      | permit =>
          simp
      | deny =>
          have hAfter := hPreserves hBefore
          simp [hAfter]
      | escalate =>
          simp

/-- Boolean form consumed by the executable compositional-safety projection. -/
lemma deniedDecisionsRemainDenied_eq_true_of_noEntrySeedSuffixMergeExtension
    {host suffix extended : AuditGovernanceGraph}
    {claims : List AuditGovernanceClaim}
    {before after : List (AuditClaimantId × AuditDecision)}
    (hExtension :
      AuditNoEntrySeedSuffixMergeExtension host suffix extended claims before after) :
    deniedDecisionsRemainDenied claims before after = true :=
  deniedDecisionsRemainDenied_eq_true_of_preserves_terminal_deny
    (noEntrySeedSuffixMergeExtension_preserves_terminal_deny hExtension)

/-- Lean wrapper mirroring the Rust runtime check `check_graph_compositional_safety`
(`src/axioms/kernel/compositional.rs`). Three Rust-parity skip cases are pinned:
cyclic graphs (handled by the dedicated cycle and nonvacuity probes) and empty
graphs (no denial surface to extend with the permissive suffix) both return
`.skipped`, mirroring `AxiomVerdict::skipped`. Only nonempty acyclic graphs
consult the canonical projection. The theorem-facing `auditCheck` projection
treats `.skipped` as undischarged evidence rather than a pass, so skipped graph
projections cannot promote a downstream legitimacy verdict. -/
def rustCheckGraphCompositionalSafety
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    AuditCheckStatus :=
  if !(detectAuditCycles graph).isEmpty then
    .skipped
  else if graph.nodes.isEmpty then
    .skipped
  else if canonicalGraphCompositionalSafetyProjection graph claims then
    .passed
  else
    .failed

/-- Verdict-level Lean↔Rust parity for compositional safety. The biconditional
pins `.passed` to the conjunction of (i) acyclicity, (ii) nonempty graph, and
(iii) the canonical projection holding. Rust returns `AxiomVerdict::pass` only
on this same conjunction; cycle and empty inputs are skipped on both sides. The
empty-graph clause was added when aligning the Lean wrapper with Rust's
`Skipped` return on empty graphs. -/
lemma auditCompositionalSafety_passed_iff_acyclic_nonempty_and_canonical
    (graph : AuditGovernanceGraph) (claims : List AuditGovernanceClaim) :
    rustCheckGraphCompositionalSafety graph claims = .passed ↔
      (detectAuditCycles graph).isEmpty = true ∧
      graph.nodes.isEmpty = false ∧
      canonicalGraphCompositionalSafetyProjection graph claims = true := by
  unfold rustCheckGraphCompositionalSafety
  by_cases hcycles : (detectAuditCycles graph).isEmpty = true
  · by_cases hempty : graph.nodes.isEmpty = true
    · simp [hcycles, hempty]
    · by_cases hcomp :
          canonicalGraphCompositionalSafetyProjection graph claims = true
      · simp [hcycles, hempty, hcomp]
      · simp [hcycles, hempty, hcomp]
  · simp [hcycles]

/-- Empty-graph mirror: the Lean wrapper returns `.skipped` on empty graphs,
matching Rust's `AxiomVerdict::skipped(_, "empty graph has no denied decision
surface to extend")` at `src/axioms/kernel/compositional.rs:42-46`. The
theorem-facing `auditCheck` projection maps `.skipped` to false, and the final
verdict records the first skipped canonical check as undischarged. -/
lemma rust_check_graph_compositional_safety_skipped_on_empty
    (claims : List AuditGovernanceClaim) :
    rustCheckGraphCompositionalSafety
      ({ nodes := [], edges := [] } : AuditGovernanceGraph) claims = .skipped := by
  unfold rustCheckGraphCompositionalSafety
  have hcycles :
      ((detectAuditCycles ({ nodes := [], edges := [] } : AuditGovernanceGraph)).isEmpty)
        = true := by native_decide
  have hempty :
      (({ nodes := [], edges := [] } : AuditGovernanceGraph).nodes.isEmpty) = true := by
    rfl
  simp [hcycles, hempty]

lemma compiler_audit_canonical_graph_compositional_safety_projection :
    canonicalGraphCompositionalSafetyProjection compilerAuditGraph.graph
      (syntheticClaimsForNodes compilerAuditGraph.graph
        (graphNodeIds compilerAuditGraph.graph)) = true := by
  native_decide

lemma empty_graph_canonical_graph_compositional_safety_projection :
    canonicalGraphCompositionalSafetyProjection
      ({ nodes := [], edges := [] } : AuditGovernanceGraph)
      [] = false := by
  native_decide

end Legitimacy
