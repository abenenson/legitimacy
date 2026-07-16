/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit.Evaluation -- direct sub-module import: internal package layer

/-!
# Legitimacy.Results.GovernanceAdmissibilityAudit.Checks

Audit check cores, status dispatchers, summaries, and theorem-facing verdict projections for governance admissibility audits.
-/

set_option autoImplicit false

namespace Legitimacy
def auditCheckConsistencyCore
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) :
    Except AuditError Bool := do
  let original <- auditFinalDecisions subject claims
  claims.foldlM (init := true) fun ok removedClaim => do
    if !ok then
      pure false
    else
      let reducedClaims := auditRemoveClaim removedClaim.claimantId claims
      let reduced <- auditFinalDecisions subject reducedClaims
      reducedClaims.foldlM (init := true) fun compareOk claim => do
        if !compareOk then
          pure false
        else
          let before <-
            auditLookupDecisionOrError
              "audit graph consistency original lookup"
              original claim.claimantId
          let after <-
            auditLookupDecisionOrError
              "audit graph consistency reduced lookup"
              reduced claim.claimantId
          pure (before = after)

def auditCheckSolidarityCore
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) :
    Except AuditError Bool := do
  let original <- auditFinalDecisions subject claims
  let groups := auditSameClassGroups claims
  let rec checkShocks :
      List (AuditMetricField × AuditMetricValue) →
        Except AuditError Bool
    | [] => pure true
    | (field, delta) :: rest => do
        if delta = 0 then
          checkShocks rest
        else
          let shockedClaims <- claims.mapM fun claim =>
            auditApplyFieldDelta claim field delta
          let shocked <- auditFinalDecisions subject shockedClaims
          let rec checkGroups :
              List (List AuditClaimantId) → Except AuditError Bool
            | [] => checkShocks rest
            | group :: remaining => do
                let rec scanGroup :
                    List AuditClaimantId → Bool → Bool →
                      Except AuditError Bool
                  | [], sawImprovement, sawWorsening =>
                      pure (!(sawImprovement && sawWorsening))
                  | claimantId :: ids, sawImprovement, sawWorsening => do
                      let before <-
                        auditLookupDecisionOrError
                          "audit graph solidarity original lookup"
                          original claimantId
                      let after <-
                        auditLookupDecisionOrError
                          "audit graph solidarity shocked lookup"
                          shocked claimantId
                      let direction := auditDecisionDirection before after
                      scanGroup ids
                        (sawImprovement || direction = 1)
                        (sawWorsening || direction = -1)
                if ← scanGroup group false false then
                  checkGroups remaining
                else
                  pure false
          checkGroups groups
  checkShocks (auditGraphShocks claims)

def auditCheckMonotonicityCore
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) :
    Except AuditError Bool := do
  let original <- auditFinalDecisions subject claims
  let claimantIds := auditClaimantIds claims
  let checkClaimants := fun
      (strengthened : List (AuditClaimantId × AuditDecision)) => do
        claimantIds.foldlM (init := true) fun ok claimantId => do
          if !ok then
            pure false
          else
            let before <-
              auditLookupDecisionOrError
                "audit graph monotonicity original lookup"
                original claimantId
            let after <-
              auditLookupDecisionOrError
                "audit graph monotonicity strengthened lookup"
                strengthened claimantId
            pure <| auditDecisionDirection before after ≥ 0
  (auditGraphDeltas claims).foldlM (init := true) fun ok
      (field, delta) => do
    if !ok || delta ≤ 0 then
      pure ok
    else
      claims.foldlM (init := true) fun deltaOk strengthenedClaim => do
        if !deltaOk then
          pure false
        else
          let strengthenedClaims <- auditModifyClaim strengthenedClaim.claimantId
            (fun claim => auditApplyFieldDelta claim field delta) claims
          let strengthened <- auditFinalDecisions subject strengthenedClaims
          checkClaimants strengthened

/-- Polarity-aware monotonicity core: each positive audit perturbation magnitude
is applied in the field's semantic improvement direction before checking that
final decisions weakly improve or stay fixed. -/
def auditCheckMonotonicityCorePolarityAware
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) :
    Except AuditError Bool := do
  let original <- auditFinalDecisions subject claims
  let claimantIds := auditClaimantIds claims
  let checkClaimants := fun
      (improved : List (AuditClaimantId × AuditDecision)) => do
        claimantIds.foldlM (init := true) fun ok claimantId => do
          if !ok then
            pure false
          else
            let before <-
              auditLookupDecisionOrError
                "audit graph polarity-aware monotonicity original lookup"
                original claimantId
            let after <-
              auditLookupDecisionOrError
                "audit graph polarity-aware monotonicity improved lookup"
                improved claimantId
            pure <| auditDecisionDirection before after ≥ 0
  (auditGraphDeltas claims).foldlM (init := true) fun ok
      (field, delta) => do
    if !ok || delta ≤ 0 then
      pure ok
    else
      let improvementDelta <- auditPolarityImprovementDelta field delta
      claims.foldlM (init := true) fun deltaOk improvedClaim => do
        if !deltaOk then
          pure false
        else
          let improvedClaims <- auditModifyClaim improvedClaim.claimantId
            (fun claim => auditApplyFieldDelta claim field improvementDelta) claims
          let improved <- auditFinalDecisions subject improvedClaims
          checkClaimants improved

def auditCheckMonotonicityCoreReviewRequired
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) :
    Except AuditError Bool := do
  let original <- auditFinalDecisions subject claims
  let claimantIds := auditClaimantIds claims
  let checkClaimants := fun
      (strengthened : List (AuditClaimantId × AuditDecision)) => do
        claimantIds.foldlM (init := true) fun ok claimantId => do
          if !ok then
            pure false
          else
            let before <-
              auditLookupDecisionOrError
                "audit graph monotonicity review-required original lookup"
                original claimantId
            let after <-
              auditLookupDecisionOrError
                "audit graph monotonicity review-required strengthened lookup"
                strengthened claimantId
            pure <| auditDecisionDirectionReviewRequired before after ≥ 0
  (auditGraphDeltas claims).foldlM (init := true) fun ok
      (field, delta) => do
    if !ok || delta ≤ 0 then
      pure ok
    else
      claims.foldlM (init := true) fun deltaOk strengthenedClaim => do
        if !deltaOk then
          pure false
        else
          let strengthenedClaims <- auditModifyClaim strengthenedClaim.claimantId
            (fun claim => auditApplyFieldDelta claim field delta) claims
          let strengthened <- auditFinalDecisions subject strengthenedClaims
          checkClaimants strengthened

/-- Prop-level review-required monotonicity: for every positive metric strengthening
considered by the audit perturbation family, every claimant's final decision
weakly preserves the review-required rank. Equivalently, a non-denial terminal
outcome may remain `.permit` or `.escalate`, but cannot flip down to `.deny`. -/
def GraphMonotonicityReviewRequired
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) : Prop :=
  ∀ (original : List (AuditClaimantId × AuditDecision))
    (field : AuditMetricField) (delta : AuditMetricValue)
    (strengthenedClaim : AuditGovernanceClaim)
    (strengthenedClaims : List AuditGovernanceClaim)
    (strengthened : List (AuditClaimantId × AuditDecision))
    (claimantId : AuditClaimantId)
    (before after : AuditDecision),
    auditFinalDecisions subject claims = Except.ok original →
    (field, delta) ∈ auditGraphDeltas claims →
    0 < delta →
    strengthenedClaim ∈ claims →
    auditModifyClaim strengthenedClaim.claimantId
        (fun claim => auditApplyFieldDelta claim field delta) claims =
      Except.ok strengthenedClaims →
    auditFinalDecisions subject strengthenedClaims = Except.ok strengthened →
    claimantId ∈ auditClaimantIds claims →
    lookupDecision? original claimantId = some before →
    lookupDecision? strengthened claimantId = some after →
    decisionRankReviewRequired before ≤ decisionRankReviewRequired after

/-- Prop-level polarity-aware audit monotonicity: for every positive finite
audit perturbation magnitude, apply the perturbation in the metric's semantic
improvement direction and require every claimant's final decision rank to be
weakly preserved. -/
def AuditGraphMonotonicityPolarityAware
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) : Prop :=
  ∀ (original : List (AuditClaimantId × AuditDecision))
    (field : AuditMetricField) (delta : AuditMetricValue)
    (improvementDelta : AuditMetricValue)
    (improvedClaim : AuditGovernanceClaim)
    (improvedClaims : List AuditGovernanceClaim)
    (improved : List (AuditClaimantId × AuditDecision))
    (claimantId : AuditClaimantId)
    (before after : AuditDecision),
    auditFinalDecisions subject claims = Except.ok original →
    (field, delta) ∈ auditGraphDeltas claims →
    0 < delta →
    auditPolarityImprovementDelta field delta = Except.ok improvementDelta →
    improvedClaim ∈ claims →
    auditModifyClaim improvedClaim.claimantId
        (fun claim =>
          auditApplyFieldDelta claim field improvementDelta) claims =
      Except.ok improvedClaims →
    auditFinalDecisions subject improvedClaims = Except.ok improved →
    claimantId ∈ auditClaimantIds claims →
    lookupDecision? original claimantId = some before →
    lookupDecision? improved claimantId = some after →
    decisionRank before ≤ decisionRank after

def auditStrategyproofnessDeltas : List AuditMetricValue :=
  [(-3 : ℚ) / 10, (-1 : ℚ) / 10, (1 : ℚ) / 10, (3 : ℚ) / 10, (1 : ℚ) / 2]

def auditCheckStrategyproofnessCore
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) :
    Except AuditError Bool := do
  let original <- auditFinalDecisions subject claims
  let rec checkClaims :
      List AuditGovernanceClaim → Except AuditError Bool
    | [] => pure true
    | misreporter :: rest => do
        let trueDecision <-
          auditLookupDecisionOrError
            "audit graph strategyproofness original lookup"
            original misreporter.claimantId
        let trueRank := decisionRank trueDecision
        let rec checkDeltas :
            List AuditMetricValue → Except AuditError Bool
          | [] => checkClaims rest
          | delta :: remaining => do
              let reportedStrength := misreporter.strength + delta
              if reportedStrength ≤ 0 then
                checkDeltas remaining
              else
                let misreportedClaims <- auditModifyClaim misreporter.claimantId
                  (fun claim => pure { claim with strength := reportedStrength }) claims
                let misreported <- auditFinalDecisions subject misreportedClaims
                let misreportedDecision <-
                  auditLookupDecisionOrError
                    "audit graph strategyproofness misreported lookup"
                    misreported misreporter.claimantId
                if decisionRank misreportedDecision > trueRank then
                  pure false
                else
                  checkDeltas remaining
        checkDeltas auditStrategyproofnessDeltas
  checkClaims claims

/-- Lean-side certifiability core for the finite audit fixture. This is a
content-light traversal-totality check: it verifies that every synthesized
claim receives some final decision from the production evaluator. The
substantive replay-certificate validation is the Rust-authoritative
`check_graph_certifiability`, which validates the graph and checks the
node-decision trace used as the replay witness for each governed claim. -/
def auditCheckCertifiabilityCore
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) :
    Except AuditError Bool := do
  if subject.graph.nodes.isEmpty then
    pure false
  else
    let decisions <- auditFinalDecisions subject claims
    pure <| claims.all fun claim =>
      (lookupDecision? decisions claim.claimantId).isSome

def supervisoryOverrideGraph
    (graph : AuditGovernanceGraph)
    (decision : AuditDecision) : AuditGovernanceGraph :=
  { nodes :=
      (graphNodeIds graph).map fun nodeId =>
        .binary nodeId ("supervisory-override-" ++ nodeId)
          [] decision .firstMatch
    edges :=
      graph.edges.map fun edge =>
        { fromNode := edge.fromNode, toNode := edge.toNode,
          transform := .passThrough } }

def supervisoryOverrideTraverses
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim)
    (decision : AuditDecision) : Bool :=
  match traverseAcyclic auditEvaluateNode
      (supervisoryOverrideGraph graph decision) claims with
  | .ok _ => true
  | .error _ => false

/-- Graph-shape projection of corrigibility: returns `true` when the graph is
nonempty and admits the supervisory-override traversal pattern under each of
the three Decision-constant overrides. The three Decision conjuncts mirror
the Rust `check_graph_corrigibility` pause/deny/permit triplet at
`src/axioms/kernel/corrigible.rs`; on this projection they are operationally
indistinguishable because `supervisoryOverrideGraph` replaces every node
`evalNode` with the constant Decision and `traverseAcyclic` only depends
on topology, so all three conjuncts collapse to "graph is nonempty and the
override-substituted topology is acyclic." The substantive corrigibility
content (algebra preservation under override) lives kernel-side in
`Kernel/Corrigible.lean`'s `KernelCorrigible` predicate; this projection is
the runtime sanity-check parity. -/
def canonicalGraphCorrigibleProjection
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) : Bool :=
  if graph.nodes.isEmpty then
    false
  else
    supervisoryOverrideTraverses graph claims .escalate &&
      supervisoryOverrideTraverses graph claims .deny &&
        supervisoryOverrideTraverses graph claims .permit

/-- Audit-pipeline corrigibility check: traverses `canonicalGraphCorrigibleProjection`
on the subject graph. See that projection's docstring for the scope; the
substantive corrigibility content lives kernel-side. -/
def auditCheckCorrigibilityCore
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) :
    Except AuditError Bool := do
  pure (canonicalGraphCorrigibleProjection subject.graph claims)

def auditCheckCompositionalSafetyCore
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) :
    Except AuditError Bool := do
  pure (canonicalGraphCompositionalSafetyProjection subject.graph claims)

/-- Lean audit-status dispatcher for the graph-admissibility fixture.

Most checks run Lean-native exhaustive finite perturbation families over the
fixture claims: consistency, solidarity, monotonicity, strategyproofness, and
nonvacuity. Observable determinacy is exhaustive only below the documented
topological-order feasibility limits, with over-limit inputs following the
documented runtime feasibility shortcut. Corrigibility and compositional safety
now use canonical Lean projections that mirror the Rust graph projections.
Certifiability is deliberately lighter on the Lean side:
`auditCheckCertifiabilityCore` checks decision totality, while Rust
`check_graph_certifiability` remains authoritative for replay-certificate
validation. -/
def auditCheckStatus
    (subject : AuditSubject)
    (check : AuditCheck) :
    Except AuditError AuditCheckStatus := do
  let claims := auditGraphClaims subject
  let hasCycles := !(detectAuditCycles subject.graph).isEmpty
  match check with
  | .observableDeterminacy =>
      if hasCycles then pure .skipped
      else if subject.graph.nodes.isEmpty then pure .skipped
      else if auditTraversalDeterministic subject claims then
        pure .passed
      else
        pure .failed
  | .nonvacuous =>
      if ← auditGraphNonvacuous subject.evalNode subject.graph claims then
        pure .passed
      else
        pure .failed
  | .consistency =>
      if hasCycles then pure .skipped
      else if ← auditCheckConsistencyCore subject claims then
        pure .passed
      else
        pure .failed
  | .solidarity =>
      if hasCycles then pure .skipped
      else if ← auditCheckSolidarityCore subject claims then
        pure .passed
      else
        pure .failed
  | .monotonicity =>
      if hasCycles then pure .skipped
      else if ← auditCheckMonotonicityCorePolarityAware subject claims then
        pure .passed
      else
        pure .failed
  | .strategyproofness =>
      if hasCycles then pure .skipped
      else if ← auditCheckStrategyproofnessCore subject claims then
        pure .passed
      else
        pure .failed
  | .certifiability =>
      if hasCycles then pure .skipped
      else if ← auditCheckCertifiabilityCore subject claims then
        pure .passed
      else
        pure .failed
  | .corrigibility =>
      if hasCycles then pure .skipped
      else if ← auditCheckCorrigibilityCore subject claims then
        pure .passed
      else
        pure .failed
  | .compositionalSafety =>
      if hasCycles then pure .skipped
      else if subject.graph.nodes.isEmpty then pure .skipped
      else if ← auditCheckCompositionalSafetyCore subject claims then
        pure .passed
      else
        pure .failed

/-- Dispatcher decode for consistency: a passing status can only come from the
consistency core returning `true`. -/
lemma auditCheckStatus_passed_implies_consistencyCore
    (subject : AuditSubject)
    (hpass : auditCheckStatus subject .consistency = .ok .passed) :
    auditCheckConsistencyCore subject (auditGraphClaims subject) = .ok true := by
  unfold auditCheckStatus at hpass
  by_cases hcycles : (detectAuditCycles subject.graph).isEmpty = true
  · cases hcore :
        auditCheckConsistencyCore subject (auditGraphClaims subject) with
    | error error =>
        simp [hcycles, hcore] at hpass
        cases hpass
    | ok passed =>
        cases passed
        · simp [hcycles, hcore] at hpass
          cases hpass
        · rfl
  · simp [hcycles] at hpass
    cases hpass

/-- Dispatcher decode for solidarity: a passing status can only come from the
solidarity core returning `true`. -/
lemma auditCheckStatus_passed_implies_solidarityCore
    (subject : AuditSubject)
    (hpass : auditCheckStatus subject .solidarity = .ok .passed) :
    auditCheckSolidarityCore subject (auditGraphClaims subject) = .ok true := by
  unfold auditCheckStatus at hpass
  by_cases hcycles : (detectAuditCycles subject.graph).isEmpty = true
  · cases hcore :
        auditCheckSolidarityCore subject (auditGraphClaims subject) with
    | error error =>
        simp [hcycles, hcore] at hpass
        cases hpass
    | ok passed =>
        cases passed
        · simp [hcycles, hcore] at hpass
          cases hpass
        · rfl
  · simp [hcycles] at hpass
    cases hpass

/-- Dispatcher decode for canonical polarity-aware monotonicity: a passing
status can only come from the polarity-aware core returning `true`. -/
lemma auditCheckStatus_passed_implies_monotonicityCorePolarityAware
    (subject : AuditSubject)
    (hpass : auditCheckStatus subject .monotonicity = .ok .passed) :
    auditCheckMonotonicityCorePolarityAware subject
      (auditGraphClaims subject) = .ok true := by
  unfold auditCheckStatus at hpass
  by_cases hcycles : (detectAuditCycles subject.graph).isEmpty = true
  · cases hcore :
        auditCheckMonotonicityCorePolarityAware subject
          (auditGraphClaims subject) with
    | error error =>
        simp [hcycles, hcore] at hpass
        cases hpass
    | ok passed =>
        cases passed
        · simp [hcycles, hcore] at hpass
          cases hpass
        · rfl
  · simp [hcycles] at hpass
    cases hpass

/-- Dispatcher decode for strategyproofness: a passing status can only come
from the strategyproofness core returning `true`. -/
lemma auditCheckStatus_passed_implies_strategyproofnessCore
    (subject : AuditSubject)
    (hpass : auditCheckStatus subject .strategyproofness = .ok .passed) :
    auditCheckStrategyproofnessCore subject (auditGraphClaims subject) =
      .ok true := by
  unfold auditCheckStatus at hpass
  by_cases hcycles : (detectAuditCycles subject.graph).isEmpty = true
  · cases hcore :
        auditCheckStrategyproofnessCore subject (auditGraphClaims subject) with
    | error error =>
        simp [hcycles, hcore] at hpass
        cases hpass
    | ok passed =>
        cases passed
        · simp [hcycles, hcore] at hpass
          cases hpass
        · rfl
  · simp [hcycles] at hpass
    cases hpass

/-- Theorem-facing semantics for audit checks. Runtime graph audits return
statuses over `AuditSubject`; source-level pullbacks instantiate this class
with predicates over the extracted source language. -/
class AuditSemantics (α : Type) where
  holds : AuditCheck → α → Prop

/-- A subject/source pair is sound when every passing audit status reflects the
theorem-facing semantics for that source object. -/
class AuditPassReflects (α : Type) [AuditSemantics α]
    (subject : AuditSubject) (source : α) : Prop where
  reflects :
    ∀ check : AuditCheck,
      auditCheckStatus subject check = .ok .passed →
        AuditSemantics.holds check source

/-- The source-level semantic predicate for a passing audit status. This is the
shared all-constructor theorem used by extractor-specific pullbacks. -/
theorem auditCheckStatus_pass_reflects_auditSemantics
    {α : Type} [AuditSemantics α]
    (subject : AuditSubject) (source : α)
    [AuditPassReflects α subject source]
    (check : AuditCheck)
    (hpass : auditCheckStatus subject check = .ok .passed) :
    AuditSemantics.holds check source :=
  AuditPassReflects.reflects check hpass

/-- Self semantics for an `AuditSubject`: a check holds exactly when the
dispatcher reports a passing status. -/
instance : AuditSemantics AuditSubject where
  holds check subject := auditCheckStatus subject check = .ok .passed

instance auditSubjectPassReflectsSelf (subject : AuditSubject) :
    AuditPassReflects AuditSubject subject subject where
  reflects := by
    intro check hpass
    exact hpass

/-- Parallel review-required audit status. Only monotonicity and nonvacuity are revised;
the canonical audit check order and all other checks remain unchanged. -/
def auditCheckStatusReviewRequired
    (subject : AuditSubject)
    (check : AuditCheck) :
    Except AuditError AuditCheckStatus := do
  let claims := auditGraphClaims subject
  let hasCycles := !(detectAuditCycles subject.graph).isEmpty
  match check with
  | .nonvacuous =>
      if ← auditGraphNonvacuousReviewRequired subject.evalNode subject.graph claims then
        pure .passed
      else
        pure .failed
  | .monotonicity =>
      if hasCycles then pure .skipped
      else if ← auditCheckMonotonicityCoreReviewRequired subject claims then
        pure .passed
      else
        pure .failed
  | .observableDeterminacy
  | .consistency
  | .solidarity
  | .strategyproofness
  | .certifiability
  | .corrigibility
  | .compositionalSafety =>
      auditCheckStatus subject check

/-- Compatibility alias for callers that named the polarity-aware surface while
it was parallel. Polarity-aware monotonicity is now the canonical
theorem-facing claimant-improvement checker. -/
def auditCheckStatusPolarityAware
    (subject : AuditSubject)
    (check : AuditCheck) :
    Except AuditError AuditCheckStatus :=
  auditCheckStatus subject check

/-- A theorem-facing Boolean projection of one audit check. Skipped checks are
not evidence and therefore do not discharge the theorem-facing obligation. Use
`auditCheckStatus` for the richer pass/fail/skipped surface. -/
def auditCheck
    (subject : AuditSubject)
    (check : AuditCheck) : Bool :=
  match auditCheckStatus subject check with
  | .ok .passed => true
  | .ok .failed | .ok .skipped => false
  | .error _ => false

def governanceAdmissibilitySummary?
    (subject : AuditSubject) :
    Except AuditError AuditSummary := do
  let claims := auditGraphClaims subject
  let reports <- auditCheckOrder.mapM fun check => do
    let status <- auditCheckStatus subject check
    pure { check := check, status := status }
  pure
    { traversalDeterministic := auditTraversalDeterministic subject claims
      checks := reports }

/-- First check that blocks theorem-facing legitimacy. Failed checks reject;
skipped checks are undischarged because they have no evidence. -/
def firstFailedAuditCheck? (subject : AuditSubject) :
    List AuditCheck → Except AuditError (Option AuditVerdict)
  | [] => pure none
  | check :: rest => do
      match ← auditCheckStatus subject check with
      | .failed => pure (some (.rejected check))
      | .skipped => pure (some (.undischarged check))
      | .passed => firstFailedAuditCheck? subject rest

def firstFailedAuditCheckReviewRequired? (subject : AuditSubject) :
    List AuditCheck → Except AuditError (Option AuditVerdict)
  | [] => pure none
  | check :: rest => do
      match ← auditCheckStatusReviewRequired subject check with
      | .failed => pure (some (.rejected check))
      | .skipped => pure (some (.undischarged check))
      | .passed => firstFailedAuditCheckReviewRequired? subject rest

def firstFailedAuditCheckPolarityAware? (subject : AuditSubject) :
    List AuditCheck → Except AuditError (Option AuditVerdict)
  | [] => pure none
  | check :: rest => do
      match ← auditCheckStatusPolarityAware subject check with
      | .failed => pure (some (.rejected check))
      | .skipped => pure (some (.undischarged check))
      | .passed => firstFailedAuditCheckPolarityAware? subject rest

def governanceAdmissibilityVerdict?
    (subject : AuditSubject) :
    Except AuditError AuditVerdict := do
  match ← firstFailedAuditCheck? subject auditCheckOrder with
  | some verdict => pure verdict
  | none => pure .legitimate

def governanceAdmissibilityVerdictReviewRequired?
    (subject : AuditSubject) :
    Except AuditError AuditVerdict := do
  match ← firstFailedAuditCheckReviewRequired? subject auditCheckOrder with
  | some verdict => pure verdict
  | none => pure .legitimate

def governanceAdmissibilityVerdictPolarityAware?
    (subject : AuditSubject) :
    Except AuditError AuditVerdict := do
  match ← firstFailedAuditCheckPolarityAware? subject auditCheckOrder with
  | some verdict => pure verdict
  | none => pure .legitimate

/-- The theorem-facing verdict keeps the historical `AuditVerdict.legitimate`
and `AuditVerdict.rejected` surface while strengthening skipped evidence into
the explicit `AuditVerdict.undischarged` case. Internal evaluator errors are
exposed by `governanceAdmissibilityVerdict?`; this projection treats errors
reached before the first failed check as a failed consistency check.
`governanceAdmissibilitySummary?` remains the full diagnostic surface when
callers need every check report. -/
def governanceAdmissibilityVerdict
    (subject : AuditSubject) : AuditVerdict :=
  match governanceAdmissibilityVerdict? subject with
  | .ok verdict => verdict
  | .error _ => .rejected .consistency

/-- Theorem-facing review-required verdict under review-required monotonicity and
nonvacuity semantics. This is intentionally parallel to, not a replacement for,
`governanceAdmissibilityVerdict`. -/
def governanceAdmissibilityVerdictReviewRequired
    (subject : AuditSubject) : AuditVerdict :=
  match governanceAdmissibilityVerdictReviewRequired? subject with
  | .ok verdict => verdict
  | .error _ => .rejected .consistency

/-- Compatibility verdict under the formerly parallel polarity-aware surface.
Schema-derived polarity is now canonical, so this agrees with
`governanceAdmissibilityVerdict` except for the retained function name. -/
def governanceAdmissibilityVerdictPolarityAware
    (subject : AuditSubject) : AuditVerdict :=
  match governanceAdmissibilityVerdictPolarityAware? subject with
  | .ok verdict => verdict
  | .error _ => .rejected .consistency

end Legitimacy
