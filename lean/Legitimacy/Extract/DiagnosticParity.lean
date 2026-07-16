/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit

/-!
# Diagnostic Parity

Lean parity surface for the four Rust graph-diagnostic checks:
consistency, solidarity, monotonicity, and strategyproofness.

The Rust extraction audit first skips these diagnostics when the extracted graph
has cycles, then runs the finite additive/removal perturbation checker from
`src/axioms/diagnostics/graph/*`. The Lean diagnostic cores in
`GovernanceAdmissibilityAudit.Checks` are the canonical theorem-facing ports of
those finite scans:

* `auditCheckConsistencyCore` removes each claimant and compares all remaining
  final decisions.
* `auditCheckSolidarityCore` applies the graph shock family from
  `auditGraphShocks` and rejects opposite movements inside a priority class.
* `auditCheckMonotonicityCorePolarityAware` applies positive graph deltas in
  each field's schema-improvement direction and rejects strict exit worsening.
* `auditCheckStrategyproofnessCore` scans the fixed additive strength
  misreports `[-0.3, -0.1, 0.1, 0.3, 0.5]` and rejects profitable moves.

The `rustCheckGraph*` wrappers below mirror the Rust audit verdict surface:
cycle skip, then pass/fail from the corresponding finite core, preserving core
errors as errors. The iff theorems pin `.passed` to the canonical Lean core
decision; they are proved by unfolding the wrapper and case-splitting on cycles
and the core result.
-/

set_option autoImplicit false

namespace Legitimacy

private def auditSubjectForGraph (graph : AuditGovernanceGraph) : AuditSubject :=
  { graph := graph, evalNode := auditEvaluateNode }

private def rustStatusFromBoolCore :
    Except AuditError Bool → Except AuditError AuditCheckStatus
  | .ok true => .ok .passed
  | .ok false => .ok .failed
  | .error error => .error error

def rustCheckGraphConsistency
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    Except AuditError AuditCheckStatus :=
  if !(detectAuditCycles graph).isEmpty then
    .ok .skipped
  else
    rustStatusFromBoolCore <|
      auditCheckConsistencyCore (auditSubjectForGraph graph) claims

def rustCheckGraphSolidarity
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    Except AuditError AuditCheckStatus :=
  if !(detectAuditCycles graph).isEmpty then
    .ok .skipped
  else
    rustStatusFromBoolCore <|
      auditCheckSolidarityCore (auditSubjectForGraph graph) claims

def rustCheckGraphMonotonicity
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    Except AuditError AuditCheckStatus :=
  if !(detectAuditCycles graph).isEmpty then
    .ok .skipped
  else
    rustStatusFromBoolCore <|
      auditCheckMonotonicityCorePolarityAware
        (auditSubjectForGraph graph) claims

def rustCheckGraphStrategyproofness
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    Except AuditError AuditCheckStatus :=
  if !(detectAuditCycles graph).isEmpty then
    .ok .skipped
  else
    rustStatusFromBoolCore <|
      auditCheckStrategyproofnessCore (auditSubjectForGraph graph) claims

lemma rustCheckGraphConsistency_iff_canonical
    (graph : AuditGovernanceGraph) (claims : List AuditGovernanceClaim) :
    rustCheckGraphConsistency graph claims = .ok .passed ↔
      (detectAuditCycles graph).isEmpty = true ∧
      auditCheckConsistencyCore (auditSubjectForGraph graph) claims =
        .ok true := by
  unfold rustCheckGraphConsistency rustStatusFromBoolCore
  by_cases hcycles : (detectAuditCycles graph).isEmpty = true
  · cases hcore :
      auditCheckConsistencyCore (auditSubjectForGraph graph) claims with
    | error error =>
        simp [hcycles]
    | ok passed =>
        cases passed <;> simp [hcycles]
  · simp [hcycles]

lemma rustCheckGraphSolidarity_iff_canonical
    (graph : AuditGovernanceGraph) (claims : List AuditGovernanceClaim) :
    rustCheckGraphSolidarity graph claims = .ok .passed ↔
      (detectAuditCycles graph).isEmpty = true ∧
      auditCheckSolidarityCore (auditSubjectForGraph graph) claims =
        .ok true := by
  unfold rustCheckGraphSolidarity rustStatusFromBoolCore
  by_cases hcycles : (detectAuditCycles graph).isEmpty = true
  · cases hcore :
      auditCheckSolidarityCore (auditSubjectForGraph graph) claims with
    | error error =>
        simp [hcycles]
    | ok passed =>
        cases passed <;> simp [hcycles]
  · simp [hcycles]

lemma rustCheckGraphMonotonicity_iff_canonical
    (graph : AuditGovernanceGraph) (claims : List AuditGovernanceClaim) :
    rustCheckGraphMonotonicity graph claims = .ok .passed ↔
      (detectAuditCycles graph).isEmpty = true ∧
      auditCheckMonotonicityCorePolarityAware
        (auditSubjectForGraph graph) claims = .ok true := by
  unfold rustCheckGraphMonotonicity rustStatusFromBoolCore
  by_cases hcycles : (detectAuditCycles graph).isEmpty = true
  · cases hcore :
      auditCheckMonotonicityCorePolarityAware
        (auditSubjectForGraph graph) claims with
    | error error =>
        simp [hcycles]
    | ok passed =>
        cases passed <;> simp [hcycles]
  · simp [hcycles]

lemma rustCheckGraphStrategyproofness_iff_canonical
    (graph : AuditGovernanceGraph) (claims : List AuditGovernanceClaim) :
    rustCheckGraphStrategyproofness graph claims = .ok .passed ↔
      (detectAuditCycles graph).isEmpty = true ∧
      auditCheckStrategyproofnessCore (auditSubjectForGraph graph) claims =
        .ok true := by
  unfold rustCheckGraphStrategyproofness rustStatusFromBoolCore
  by_cases hcycles : (detectAuditCycles graph).isEmpty = true
  · cases hcore :
      auditCheckStrategyproofnessCore (auditSubjectForGraph graph) claims with
    | error error =>
        simp [hcycles]
    | ok passed =>
        cases passed <;> simp [hcycles]
  · simp [hcycles]

end Legitimacy
