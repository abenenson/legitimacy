/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit.Checks -- direct sub-module import: internal package layer

/-!
# Legitimacy.Results.GovernanceAdmissibilityAudit.Fixtures

Concrete tightness and compiler-audit fixtures plus theorem-facing certificates.
-/

set_option autoImplicit false

namespace Legitimacy
/-- Tightness fixture: a deliberately backwards lower-better risk gate. Raising
the risk field preserves permit, so legacy monotonicity passes; reducing the
risk field is the semantic improvement and exposes a permit-to-deny failure. -/
def polarityAwareTightnessGovernanceGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "polarity-risk-gate"
        "Backwards lower-better risk gate"
        [ .thresholdGate "paradox_risk" 0 .permit ]
        .deny
        .firstMatch
    ]
  edges := []

def polarityAwareTightnessSubject : AuditSubject where
  graph := polarityAwareTightnessGovernanceGraph
  evalNode := auditEvaluateNode

/-- Independence: the legacy positive-strengthening monotonicity core passes
on the tightness fixture. -/
theorem polarityAwareTightness_passes_legacy_monotonicity :
    auditCheckMonotonicityCore polarityAwareTightnessSubject
        (auditGraphClaims polarityAwareTightnessSubject) =
      .ok true := by
  native_decide

/-- Non-vacuity: the canonical polarity-aware diagnostic has a concrete
rejecting witness. -/
theorem polarityAwareTightness_fails_polarity_aware_monotonicity :
    auditCheckStatus polarityAwareTightnessSubject AuditCheck.monotonicity =
      .ok .failed := by
  native_decide

/-- Operational distinctness: the legacy executable core and canonical
theorem-facing diagnostic make different monotonicity verdicts on the same
concrete graph. -/
theorem polarityAwareTightness_operationally_distinct :
    auditCheckMonotonicityCore polarityAwareTightnessSubject
        (auditGraphClaims polarityAwareTightnessSubject) = .ok true ∧
      auditCheckStatus polarityAwareTightnessSubject AuditCheck.monotonicity =
        .ok .failed := by
  native_decide

def compilerAuditNodes : List AuditGovernanceNode :=
  [ .binary "graph-consistency" "graph consistency"
      [ .thresholdGate "audit_signal" 1 .escalate ]
      .deny .firstMatch
  , .binary "graph-solidarity" "graph solidarity"
      [ .thresholdGate "audit_signal" 1 .escalate ]
      .deny .firstMatch
  , .binary "graph-monotonicity" "graph monotonicity"
      [ .thresholdGate "audit_signal" 1 .escalate ]
      .deny .firstMatch
  , .binary "graph-strategyproofness" "graph strategyproofness"
      [ .thresholdGate "audit_signal" 1 .escalate ]
      .deny .firstMatch
  , .binary "graph-certifiability" "graph certifiability"
      [ .thresholdGate "audit_signal" 1 .escalate ]
      .deny .firstMatch
  , .binary "graph-observable-determinacy" "graph observable determinacy"
      [ .thresholdGate "audit_signal" 1 .escalate ]
      .deny .firstMatch
  , .binary "graph-corrigibility" "graph corrigibility"
      [ .thresholdGate "audit_signal" 1 .escalate ]
      .deny .firstMatch
  , .binary "graph-compositional-safety" "graph compositional safety"
      [ .thresholdGate "audit_signal" 1 .escalate ]
      .deny .firstMatch
  , .binary "graph-nonvacuity" "graph nonvacuity"
      [ .thresholdGate "audit_signal" 1 .permit ]
      .deny .firstMatch
  ]

def compilerAuditEdges : List AuditGovernanceEdge :=
  [ { fromNode := "graph-consistency", toNode := "graph-solidarity",
      transform := .passThrough }
  , { fromNode := "graph-solidarity", toNode := "graph-monotonicity",
      transform := .passThrough }
  , { fromNode := "graph-monotonicity", toNode := "graph-strategyproofness",
      transform := .passThrough }
  , { fromNode := "graph-strategyproofness",
      toNode := "graph-certifiability", transform := .passThrough }
  , { fromNode := "graph-certifiability", toNode := "graph-observable-determinacy",
      transform := .passThrough }
  , { fromNode := "graph-observable-determinacy", toNode := "graph-corrigibility",
      transform := .passThrough }
  , { fromNode := "graph-corrigibility", toNode := "graph-compositional-safety",
      transform := .passThrough }
  , { fromNode := "graph-compositional-safety", toNode := "graph-nonvacuity",
      transform := .passThrough }
  ]

/-- Manual audit encoding of the production compiler audit surface. -/
def compilerAuditGraph : AuditSubject where
  graph := { nodes := compilerAuditNodes, edges := compilerAuditEdges }
  evalNode := auditEvaluateNode

/-- Regression fixture for cyclic extracted graphs: canonical checks that cannot
run over cycles are undischarged, not silently legitimate. -/
def cyclicSkippedAuditGraph : AuditSubject where
  graph :=
    { nodes :=
        [ .binary "cycle-a" "cycle a"
            [ .thresholdGate "audit_signal" 1 .permit ]
            .deny .firstMatch
        , .binary "cycle-b" "cycle b"
            [ .thresholdGate "audit_signal" 1 .permit ]
            .deny .firstMatch
        ]
      edges :=
        [ { fromNode := "cycle-a", toNode := "cycle-b",
            transform := .passThrough }
        , { fromNode := "cycle-b", toNode := "cycle-a",
            transform := .passThrough }
        ] }
  evalNode := auditEvaluateNode

/-- The cyclic skipped-check fixture is surfaced as undischarged consistency
evidence, not as a legitimate verdict. -/
theorem cyclicSkippedAuditGraph_undischarged :
    governanceAdmissibilityVerdict cyclicSkippedAuditGraph =
      AuditVerdict.undischarged AuditCheck.consistency := by
  native_decide

theorem cyclicSkippedAuditGraph_not_legitimate :
    governanceAdmissibilityVerdict cyclicSkippedAuditGraph ≠
      AuditVerdict.legitimate := by
  native_decide

theorem compilerAuditGraph_metric_polarity_schema_check :
    auditGraphFieldsSchemaTotalCheck (auditGraphClaims compilerAuditGraph) = true := by
  native_decide

theorem compilerAuditGraph_metric_polarity_schema_total :
    AuditGraphDeltasSchemaTotal (auditGraphClaims compilerAuditGraph) :=
  auditGraphDeltas_schema_total_of_check
    compilerAuditGraph_metric_polarity_schema_check

/-- Exhaustive traversal-confluence check over the complete finite
topological-order surface. Unlike `auditTraversalDeterministic`, this helper
does not use the large-graph feasibility escape hatch: callers that use it are
asking Lean to enumerate every order and compare the observable final-decision
surface directly. -/
def allAuditTraversalsConfluent
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) : Bool :=
  match allTopologicalOrders subject.graph with
  | [] => true
  | referenceOrder :: rest =>
      match traverseAcyclicWithOrder subject.evalNode subject.graph claims referenceOrder with
      | .ok reference =>
          rest.all fun order =>
            match traverseAcyclicWithOrder subject.evalNode subject.graph claims order with
            | .ok candidate => candidate.finalDecisions = reference.finalDecisions
            | .error _ => false
      | .error _ =>
          rest.all fun order =>
            match traverseAcyclicWithOrder subject.evalNode subject.graph claims order with
            | .error _ => true
            | .ok _ => false

/-- Structural theorem target for a later proof: every legal traversal order
has the same observable final-decision surface for a subject and concrete claim
corpus. -/
def audit_traversal_confluence_structural_statement
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) : Prop :=
  allAuditTraversalsConfluent subject claims = true

/-- Declaration-level self-legitimacy certificate for the concrete compiler
audit fixture. The statement says that the fixed `compilerAuditGraph`, evaluated
by the production governance-admissibility verdict function, is classified as
`legitimate`. This is not a theorem over arbitrary extractor outputs or every
well-formed audit graph; the surrounding module discusses that fixture scope,
and this docstring repeats it here so the declaration stands alone under a
hostile cold read. -/
theorem compiler_audit_is_self_legitimate :
    governanceAdmissibilityVerdict compilerAuditGraph = AuditVerdict.legitimate := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

/-- Probe 6 observable-commutation theorem, framed as unconditional
traversal-confluence for the concrete compiler audit graph and its singleton
fixture corpus. The first conjunct enumerates all topological orders and checks
that every traversal yields the same final decisions; the second pins the
order-invariant governance verdict used by the audit fixture. -/
theorem audit_traversal_confluence :
    allAuditTraversalsConfluent compilerAuditGraph
        (auditGraphClaims compilerAuditGraph) = true ∧
      governanceAdmissibilityVerdict compilerAuditGraph = AuditVerdict.legitimate := by
  native_decide

theorem compilerAuditGraph_canonical_tie_break_check :
    canonicalTieBreakCheck compilerAuditGraph.graph = true := by
  native_decide

theorem compilerAuditGraph_canonical_tie_break :
    CanonicalTieBreak compilerAuditGraph.graph := by
  apply canonicalTieBreak_of_allTopologicalOrders_singleton
    (order :=
      [ "graph-consistency"
      , "graph-solidarity"
      , "graph-monotonicity"
      , "graph-strategyproofness"
      , "graph-certifiability"
      , "graph-observable-determinacy"
      , "graph-corrigibility"
      , "graph-compositional-safety"
      , "graph-nonvacuity"
      ])
  native_decide

theorem compilerAuditGraph_governance_audit_diamond_condition :
    GovernanceAuditDiamondConditionOn auditEvaluateNode compilerAuditGraph.graph
      (auditGraphClaims compilerAuditGraph) := by
  apply governance_audit_diamond_condition_on_of_canonical_tie_break
  · unfold AuditGovernanceGraph.IsAcyclic
    native_decide
  · exact compilerAuditGraph_canonical_tie_break

def linearTieBreakAuditGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "entry" "entry"
        [ .thresholdGate "audit_signal" 1 .escalate ]
        .deny .firstMatch
    , .binary "terminal" "terminal"
        [ .thresholdGate "audit_signal" 1 .permit ]
        .deny .firstMatch
    ]
  edges :=
    [ { fromNode := "entry", toNode := "terminal",
        transform := .passThrough } ]

theorem linearTieBreakAuditGraph_canonical_tie_break :
    CanonicalTieBreak linearTieBreakAuditGraph := by
  apply canonicalTieBreak_of_allTopologicalOrders_singleton
    (order := ["entry", "terminal"])
  native_decide

theorem linearTieBreakAuditGraph_governance_audit_diamond_condition
    (claims : ClaimProfile) :
    GovernanceAuditDiamondConditionOn auditEvaluateNode
      linearTieBreakAuditGraph claims := by
  apply governance_audit_diamond_condition_on_of_canonical_tie_break
  · unfold AuditGovernanceGraph.IsAcyclic
    native_decide
  · exact linearTieBreakAuditGraph_canonical_tie_break

def nonConfluentUncheckedGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "gate" "gate"
        [ .thresholdGate "strength" 1 .permit ]
        .deny .firstMatch
    ]
  edges := []

def nonConfluentUncheckedClaims : ClaimProfile :=
  [ { claimantId := "alice"
      strength := 1
      priorityClass := some "baseline"
      path := none
      action := none
      content := none
      metrics := [] } ]

theorem nonConfluentUncheckedGraph_exhibits_nonconfluence :
    auditAfter auditEvaluateNode nonConfluentUncheckedGraph
        nonConfluentUncheckedClaims [] ≠
      auditAfter auditEvaluateNode nonConfluentUncheckedGraph
        nonConfluentUncheckedClaims ["gate"] := by
  native_decide

theorem nonConfluentUncheckedGraph_violates_unchecked_diamond :
    ¬ (∀ path1 path2 : List AuditAction,
      auditAfter auditEvaluateNode nonConfluentUncheckedGraph
          nonConfluentUncheckedClaims path1 =
        auditAfter auditEvaluateNode nonConfluentUncheckedGraph
          nonConfluentUncheckedClaims path2) := by
  intro h
  exact nonConfluentUncheckedGraph_exhibits_nonconfluence (h [] ["gate"])

end Legitimacy
