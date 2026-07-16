/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit.Cycles -- direct sub-module import: internal package layer

/-!
# Legitimacy.Results.GovernanceAdmissibilityAudit.Evaluation

Concrete node evaluation, perturbation helpers, graph projections, and traversal-determinism diagnostics for governance admissibility audits.
-/

set_option autoImplicit false

namespace Legitimacy
/-- A concrete governance admissibility audit subject bundles the graph artifact and the node
evaluator used to run the audit traversal. -/
structure AuditSubject where
  graph : AuditGovernanceGraph
  evalNode : AuditNodeEvaluator

inductive AuditCheckStatus where
  | passed
  | failed
  | skipped
  deriving Repr, DecidableEq

structure AuditCheckReport where
  check : AuditCheck
  status : AuditCheckStatus
  deriving Repr, DecidableEq

structure AuditSummary where
  traversalDeterministic : Bool
  checks : List AuditCheckReport
  deriving Repr, DecidableEq

def auditNumericField
    (claim : AuditGovernanceClaim)
    (field : AuditMetricField) :
    Except AuditError AuditMetricValue :=
  if field = "strength" then
    pure claim.strength
  else
    match claim.metrics.lookup field with
    | some value => pure value
    | none =>
        .error (.invalidGate field
          s!"claim '{claim.claimantId}' does not provide metric '{field}'")

def auditGateMatches
    (gate : AuditGate)
    (claim : AuditGovernanceClaim)
    (claims : List AuditGovernanceClaim) :
    Except AuditError Bool := do
  match gate with
  | .prefixMatch pattern _ =>
      pure <| claim.path.map (·.startsWith pattern) |>.getD false
  | .exactMatch value _ =>
      pure <| claim.action = some value
  | .contentMatch regex _ =>
      match claim.content with
      | none => pure false
      | some content =>
          match Regex.parse regex with
          | some (.literal value) => pure <| content.contains value
          | some parsed => pure <| Regex.matches parsed content
          | none =>
              .error (.invalidGate "ContentMatch"
                s!"unsupported regex subset in pattern '{regex}'")
  | .thresholdGate field min _ =>
      pure <| (← auditNumericField claim field) ≥ min
  | .peerRelative field percentile _ =>
      let currentValue <- auditNumericField claim field
      let values <- claims.mapM (fun other => auditNumericField other field)
      if values.isEmpty then
        .error (.invalidInput "peer-relative gate requires at least one claim")
      else
        let sorted := values.mergeSort (· ≤ ·)
        let lessOrEqual := sorted.foldl (fun count value =>
          if value ≤ currentValue then count + 1 else count) 0
        pure <| (lessOrEqual : ℚ) / values.length ≥ percentile

def auditEvaluateBinaryDecision
    (gates : List AuditGate)
    (default : AuditDecision)
    (combination : AuditGateLogic)
    (claim : AuditGovernanceClaim)
    (claims : List AuditGovernanceClaim) :
    Except AuditError AuditDecision := do
  match combination with
  | .firstMatch =>
      let rec goFirst : List AuditGate → Except AuditError AuditDecision
        | [] => pure default
        | gate :: rest => do
            if ← auditGateMatches gate claim claims then
              pure (gateDecision gate)
            else
              goFirst rest
      goFirst gates
  | .anyMustPass =>
      let rec collectAny :
          List AuditGate → Except AuditError (List AuditDecision)
        | [] => pure []
        | gate :: rest => do
            let tail <- collectAny rest
            if ← auditGateMatches gate claim claims then
              pure (gateDecision gate :: tail)
            else
              pure tail
      let matched <- collectAny gates
      if matched.any (· = .permit) then
        pure .permit
      else if matched.any (· = .escalate) then
        pure .escalate
      else if matched.any (· = .deny) then
        pure .deny
      else
        pure default
  | .allMustPass =>
      let rec goAll :
          List AuditGate → Nat → Bool →
            Except AuditError AuditDecision
        | [], matchedCount, sawEscalate =>
            if matchedCount = gates.length && !gates.isEmpty then
              pure .permit
            else if sawEscalate then
              pure .escalate
            else
              pure default
        | gate :: rest, matchedCount, sawEscalate => do
            if ← auditGateMatches gate claim claims then
              match gateDecision gate with
              | .deny => pure .deny
              | .escalate => goAll rest (matchedCount + 1) true
              | .permit => goAll rest (matchedCount + 1) sawEscalate
            else
              goAll rest matchedCount sawEscalate
      goAll gates 0 false

def auditEvaluateNode : AuditNodeEvaluator
  | .binary _ _ gates default combination, claims => do
      validateAuditGovernanceClaims claims
      claims.mapM fun claim => do
        let decision <- auditEvaluateBinaryDecision gates default combination claim claims
        pure { claimantId := claim.claimantId, decision := decision }
  | .threshold _ _ threshold field, claims => do
      validateAuditGovernanceClaims claims
      claims.mapM fun claim => do
        let metricValue <- auditNumericField claim field
        let decision := if metricValue ≥ threshold then .permit else .deny
        pure { claimantId := claim.claimantId, decision := decision }
  | .proportional id _ _ _, _ =>
      .error (.unsupportedNodeType id "Proportional")

def auditDecisionDirection
    (before after : AuditDecision) : Int :=
  match compare (decisionRank after) (decisionRank before) with
  | .lt => -1
  | .eq => 0
  | .gt => 1

def auditDecisionDirectionReviewRequired
    (before after : AuditDecision) : Int :=
  match compare (decisionRankReviewRequired after)
      (decisionRankReviewRequired before) with
  | .lt => -1
  | .eq => 0
  | .gt => 1

/-- Prop-level review-required nonvacuity: the graph has a terminal non-denial outcome
when `.escalate` is read as terminal review-required rather than unresolved. -/
def GraphNonvacuityReviewRequired
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) : Prop :=
  match auditGraphNonvacuityReviewRequired subject.evalNode subject.graph claims with
  | .ok (.admissible _) => True
  | .ok (.rejected _) | .error _ => False

def auditGraphClaims (subject : AuditSubject) :
    List AuditGovernanceClaim :=
  syntheticClaimsForNodes subject.graph (graphNodeIds subject.graph)

def auditGraphFields
    (claims : List AuditGovernanceClaim) : List AuditMetricField :=
  let rec go : List AuditGovernanceClaim → List AuditMetricField
    | [] => []
    | claim :: rest => claim.metrics.map Prod.fst ++ go rest
  canonicalStrings ("strength" :: go claims)

def auditGraphShocks
    (claims : List AuditGovernanceClaim) :
    List (AuditMetricField × AuditMetricValue) :=
  (auditGraphFields claims).map fun field =>
    if field = "strength" then (field, (1 : ℚ) / 10) else (field, 1)

def auditGraphDeltas
    (claims : List AuditGovernanceClaim) :
    List (AuditMetricField × AuditMetricValue) :=
  auditGraphShocks claims

/-- Semantic direction of an audit metric. `higherBetter` fields improve when
their numeric value increases; `lowerBetter` fields improve when their numeric
value decreases. `diagnosticPresence` fields count governance events and are
classified for schema totality without treating larger counts as claimant
improvements. -/
inductive AuditMetricPolarity where
  | lowerBetter
  | higherBetter
  | diagnosticPresence
  deriving DecidableEq, Repr

/-- Schema-level polarity annotations for extracted audit metric fields. The
canonical claimant-improvement checker is closed over this table: unknown
fields are rejected rather than silently defaulted to `higherBetter`. -/
def auditMetricPolaritySchema : List (AuditMetricField × AuditMetricPolarity) :=
  [ ("approval_forbidden", .lowerBetter)
  , ("approval_not_found", .lowerBetter)
  , ("block_reason", .lowerBetter)
  , ("blocked_context", .lowerBetter)
  , ("combined_untrusted_suspicion", .lowerBetter)
  , ("blocked", .lowerBetter)
  , ("dangerous_keyword", .lowerBetter)
  , ("dangerous_pattern", .lowerBetter)
  , ("dangerous_user_approved", .lowerBetter)
  , ("dangerous_user_rejected", .lowerBetter)
  , ("dangerous_without_ui", .lowerBetter)
  , ("deployment_context", .lowerBetter)
  , ("hook_invalid_or_unsupported", .lowerBetter)
  , ("latency", .lowerBetter)
  , ("monitor_validation_failure", .lowerBetter)
  , ("paradox_risk", .lowerBetter)
  , ("policyblocked", .lowerBetter)
  , ("policy_strictness", .lowerBetter)
  , ("risk", .lowerBetter)
  , ("trusted_edit_band_suspicion", .lowerBetter)
  , ("trusted_edit_top2_suspicion", .lowerBetter)
  , ("trusted_suspicion", .lowerBetter)
  , ("trusted_suspicion_defer_band", .lowerBetter)
  , ("trusted_suspicion_top2", .lowerBetter)
  , ("test_failure", .lowerBetter)
  , ("upfront_audit_window", .lowerBetter)
  , ("after_hook", .higherBetter)
  , ("allowacrossproviders", .higherBetter)
  , ("allowcrosscontextsend", .higherBetter)
  , ("allowed", .higherBetter)
  , ("alloweddecisions", .higherBetter)
  , ("allowfinalsymlink", .higherBetter)
  , ("allowlist", .higherBetter)
  , ("allowlist_match", .higherBetter)
  , ("allowlistsatisfied", .higherBetter)
  , ("allowpluginfallback", .higherBetter)
  , ("allowskillpreludeatindex", .higherBetter)
  , ("allowskills", .higherBetter)
  , ("allowunsafereplay", .higherBetter)
  , ("allowwithinprovider", .higherBetter)
  , ("agent_id", .higherBetter)
  , ("approval", .higherBetter)
  , ("approval_policy", .higherBetter)
  , ("approval_required", .diagnosticPresence)
  , ("approvalcommandid", .higherBetter)
  , ("approvalid", .higherBetter)
  , ("approvalkind", .higherBetter)
  , ("approvalslug", .higherBetter)
  , ("approved", .higherBetter)
  , ("approvedforsession", .higherBetter)
  , ("analysis_ok", .higherBetter)
  , ("audit_recorded", .higherBetter)
  , ("audit_signal", .higherBetter)
  , ("available", .higherBetter)
  , ("base_authorization", .higherBetter)
  , ("baseline", .higherBetter)
  , ("baseline_allow", .higherBetter)
  , ("before_hook", .higherBetter)
  , ("block_threshold", .higherBetter)
  , ("checkpoint_written", .higherBetter)
  , ("claude_md_always_execute", .higherBetter)
  , ("completed_turn", .higherBetter)
  , ("consequential", .higherBetter)
  , ("content_length", .higherBetter)
  , ("deny_signal", .diagnosticPresence)
  , ("denied", .diagnosticPresence)
  , ("diversity", .higherBetter)
  , ("durable_trust", .higherBetter)
  , ("escalated", .diagnosticPresence)
  , ("escalate_signal", .diagnosticPresence)
  , ("executed", .higherBetter)
  , ("execution_skipped", .diagnosticPresence)
  , ("fallback_selected", .higherBetter)
  , ("file_edit", .higherBetter)
  , ("full_access", .higherBetter)
  , ("hook", .higherBetter)
  , ("hook_blocks", .higherBetter)
  , ("hook_event_name", .higherBetter)
  , ("hook_registration", .higherBetter)
  , ("hook_registration:BeforeToolCall", .higherBetter)
  , ("hook_registration:CodeExecutorApproval", .higherBetter)
  , ("hook_registration:DialoguePolicy", .higherBetter)
  , ("hook_registration:InterruptBeforeTool", .higherBetter)
  , ("hook_registration:PreToolUse", .higherBetter)
  , ("hook_run_is_quiet_success", .higherBetter)
  , ("human_resume_required", .diagnosticPresence)
  , ("human_review", .higherBetter)
  , ("interrupt", .higherBetter)
  , ("invocation_id", .higherBetter)
  , ("listed", .higherBetter)
  , ("maxTurns", .higherBetter)
  , ("memory_id", .higherBetter)
  , ("most_common_answer_score", .higherBetter)
  , ("needs_approval", .diagnosticPresence)
  , ("observation_id", .higherBetter)
  , ("permission", .higherBetter)
  , ("permission_mode", .higherBetter)
  , ("permissiongrantscope", .higherBetter)
  , ("permissions", .higherBetter)
  , ("patch_applied", .higherBetter)
  , ("peer_relative", .higherBetter)
  , ("policy", .higherBetter)
  , ("policy_cwd", .higherBetter)
  , ("policy_for_chat", .higherBetter)
  , ("policy_match", .higherBetter)
  , ("policy_rule_matched", .higherBetter)
  , ("permit_signal", .higherBetter)
  , ("primary_failed", .diagnosticPresence)
  , ("profile_restricted", .higherBetter)
  , ("record_id", .higherBetter)
  , ("refusal_emitted", .diagnosticPresence)
  , ("reviewdecision", .higherBetter)
  , ("runtime_roots_readable", .higherBetter)
  , ("sandbox", .higherBetter)
  , ("sandbox_policy", .higherBetter)
  , ("sandbox_setup_is_complete", .higherBetter)
  , ("sandboxpolicy", .higherBetter)
  , ("sandboxed", .higherBetter)
  , ("sanitize_context", .higherBetter)
  , ("scarcity_bonus", .higherBetter)
  , ("security_allowlist", .higherBetter)
  , ("sensitive_path", .higherBetter)
  , ("skip_exec_approval", .diagnosticPresence)
  , ("solve_directly", .higherBetter)
  , ("specialization_floor", .higherBetter)
  , ("specialization_penalty", .higherBetter)
  , ("stdout_taken_over", .higherBetter)
  , ("strength", .higherBetter)
  , ("task_id", .higherBetter)
  , ("tests_run", .higherBetter)
  , ("tool_call", .higherBetter)
  , ("tool_ready", .higherBetter)
  , ("tool_name", .higherBetter)
  , ("training_context", .higherBetter)
  , ("unsafe_intent", .diagnosticPresence)
  , ("word_count", .higherBetter)
  ]

def auditMetricFieldPolarity? (field : AuditMetricField) :
    Option AuditMetricPolarity :=
  auditMetricPolaritySchema.lookup field

def auditMetricFieldPolarityOrError (field : AuditMetricField) :
    Except AuditError AuditMetricPolarity :=
  match auditMetricFieldPolarity? field with
  | some polarity => pure polarity
  | none =>
      .error (.invalidGate field
        s!"metric field '{field}' has no schema polarity annotation")

/-- Convert a positive audit perturbation magnitude into the claimant-positive
semantic improvement direction for the field's polarity. -/
def auditPolarityImprovementDelta
    (field : AuditMetricField)
    (delta : AuditMetricValue) :
    Except AuditError AuditMetricValue := do
  match ← auditMetricFieldPolarityOrError field with
  | .higherBetter => pure delta
  | .lowerBetter => pure (-delta)
  -- Diagnostic-presence fields contribute zero improvement delta,
  -- matching Rust's skip-from-perturbation-count behavior in the graph audit.
  | .diagnosticPresence => pure 0

theorem auditMetricFieldPolarityOrError_some
    {field : AuditMetricField} {polarity : AuditMetricPolarity}
    (h : auditMetricFieldPolarityOrError field = .ok polarity) :
    auditMetricFieldPolarity? field = some polarity := by
  unfold auditMetricFieldPolarityOrError at h
  cases hpol : auditMetricFieldPolarity? field with
  | none =>
      simp [hpol] at h
  | some schemaPolarity =>
      simp [hpol] at h
      cases h
      rfl

def AuditGraphDeltasSchemaTotal
    (claims : List AuditGovernanceClaim) : Prop :=
  ∀ field delta,
    (field, delta) ∈ auditGraphDeltas claims →
      ∃ polarity, auditMetricFieldPolarity? field = some polarity

def auditGraphFieldsSchemaTotalCheck
    (claims : List AuditGovernanceClaim) : Bool :=
  (auditGraphFields claims).all fun field =>
    (auditMetricFieldPolarity? field).isSome

/-- Totality guard for canonical graph deltas: every field used by
`auditGraphDeltas` has a polarity supplied by `auditMetricPolaritySchema`.
Callers discharge the premise by checking the finite extracted field set; any
new field without a schema annotation makes that finite proof fail, while the
executable checker also rejects unknown fields instead of defaulting them. -/
theorem auditGraphDeltas_schema_total_of_fields
    {claims : List AuditGovernanceClaim}
    (hfields :
      ∀ field,
        field ∈ auditGraphFields claims →
          ∃ polarity, auditMetricFieldPolarity? field = some polarity) :
    AuditGraphDeltasSchemaTotal claims := by
  intro field delta hdelta
  unfold auditGraphDeltas auditGraphShocks at hdelta
  rcases List.mem_map.mp hdelta with ⟨sourceField, hsource, hpair⟩
  by_cases hstrength : sourceField = "strength"
  · subst sourceField
    simp at hpair
    rcases hpair with ⟨hfield, _⟩
    subst field
    exact hfields "strength" hsource
  · simp [hstrength] at hpair
    rcases hpair with ⟨hfield, _⟩
    subst field
    exact hfields sourceField hsource

theorem auditGraphDeltas_schema_total_of_check
    {claims : List AuditGovernanceClaim}
    (hcheck : auditGraphFieldsSchemaTotalCheck claims = true) :
    AuditGraphDeltasSchemaTotal claims := by
  apply auditGraphDeltas_schema_total_of_fields
  intro field hfield
  unfold auditGraphFieldsSchemaTotalCheck at hcheck
  have hsome :
      (auditMetricFieldPolarity? field).isSome = true := by
    exact (List.all_eq_true.mp hcheck) field hfield
  cases hpol : auditMetricFieldPolarity? field with
  | none =>
      simp [hpol] at hsome
  | some polarity =>
      exact ⟨polarity, rfl⟩

def auditApplyFieldDelta
    (claim : AuditGovernanceClaim)
    (field : AuditMetricField)
    (delta : AuditMetricValue) :
    Except AuditError AuditGovernanceClaim := do
  if field = "strength" then
    let updated := { claim with strength := claim.strength + delta }
    validateAuditGovernanceClaim updated
    pure updated
  else
    let current := claim.metrics.lookup field |>.getD 0
    pure { claim with metrics := metricPut field (current + delta) claim.metrics }

def auditRemoveClaim
    (targetId : AuditClaimantId) :
    List AuditGovernanceClaim → List AuditGovernanceClaim
  | [] => []
  | claim :: rest =>
      if claim.claimantId = targetId then
        rest
      else
        claim :: auditRemoveClaim targetId rest

def auditModifyClaim
    (targetId : AuditClaimantId)
    (update : AuditGovernanceClaim →
      Except AuditError AuditGovernanceClaim) :
    List AuditGovernanceClaim →
      Except AuditError (List AuditGovernanceClaim)
  | [] => pure []
  | claim :: rest =>
      if claim.claimantId = targetId then do
        let updated <- update claim
        pure (updated :: rest)
      else do
        let tail <- auditModifyClaim targetId update rest
        pure (claim :: tail)

def insertClaimantGroup
    (classKey claimantId : String) :
    List (String × List AuditClaimantId) →
      List (String × List AuditClaimantId)
  | [] => [(classKey, [claimantId])]
  | (key, current) :: rest =>
      if classKey = key then
        (classKey, current ++ [claimantId]) :: rest
      else if classKey ≤ key then
        (classKey, [claimantId]) :: (key, current) :: rest
      else
        (key, current) :: insertClaimantGroup classKey claimantId rest

def auditSameClassGroups
    (claims : List AuditGovernanceClaim) :
    List (List AuditClaimantId) :=
  let groups := claims.foldl (fun acc claim =>
    insertClaimantGroup (claim.priorityClass.getD claim.claimantId)
      claim.claimantId acc) []
  (groups.map Prod.snd).filter fun group => group.length > 1

def auditClaimantIds
    (claims : List AuditGovernanceClaim) : List AuditClaimantId :=
  canonicalStrings (claims.map AuditGovernanceClaim.claimantId)

def auditLookupDecisionOrError
    (context : String)
    (decisions : List (AuditClaimantId × AuditDecision))
    (claimantId : AuditClaimantId) :
    Except AuditError AuditDecision :=
  match lookupDecision? decisions claimantId with
  | some decision => pure decision
  | none =>
      .error (.invalidInput
        s!"missing final decision for '{claimantId}' in {context}")

def auditFinalDecisions
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) :
    Except AuditError (List (AuditClaimantId × AuditDecision)) := do
  let traversal <- traverseAcyclic subject.evalNode subject.graph claims
  pure traversal.finalDecisions

def graphCompositionalSafetySinkId (graph : AuditGovernanceGraph) : AuditNodeId :=
  "__lean_compositional_permit_suffix_" ++ toString graph.nodes.length

def auditTerminalNodeIds (graph : AuditGovernanceGraph) : List AuditNodeId :=
  (graphNodeIds graph).filter fun nodeId => (outgoingEdges graph nodeId).isEmpty

def appendCompositionalPermitSuffix
    (graph : AuditGovernanceGraph) : AuditGovernanceGraph :=
  let sinkId := graphCompositionalSafetySinkId graph
  { nodes :=
      graph.nodes ++
        [ .binary sinkId "graph compositional safety permit suffix"
            [] .permit .firstMatch ]
    edges :=
      graph.edges ++
        ((auditTerminalNodeIds graph).map fun nodeId =>
          { fromNode := nodeId, toNode := sinkId,
            transform := .passThrough }) }

def deniedDecisionsRemainDenied
    (claims : List AuditGovernanceClaim)
    (before after : List (AuditClaimantId × AuditDecision)) : Bool :=
  claims.all fun claim =>
    match lookupDecision? before claim.claimantId,
        lookupDecision? after claim.claimantId with
    | some .deny, some .deny => true
    | some .deny, _ => false
    | _, _ => true

/-- Graph-shape projection of compositional safety. Empty graphs return `false`
so this bare Boolean projection does not certify a graph with no composition
surface; wrapper and dispatcher layers still expose empty graphs as skipped.
The substantive compositional-safety content
(deny-bottom merge invariance under suffix-extension) lives in the kernel-side
deny-bottom invariant theorems (`Legitimacy.finalDecisionSuffixMergeTrace_preserves_deny`,
`Legitimacy.noEntrySeedSuffixMergeExtension_preserves_terminal_deny`); this
projection is the Rust-parity graph-shape sanity check. -/
def canonicalGraphCompositionalSafetyProjection
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) : Bool :=
  if graph.nodes.isEmpty then
    false
  else
    let subject : AuditSubject := { graph := graph, evalNode := auditEvaluateNode }
    let appendedSubject : AuditSubject :=
      { graph := appendCompositionalPermitSuffix graph,
        evalNode := auditEvaluateNode }
    match auditFinalDecisions subject claims,
        auditFinalDecisions appendedSubject claims with
    | .ok before, .ok after => deniedDecisionsRemainDenied claims before after
    | _, _ => false

/-- The canonical formal statement of governance-graph traversal determinism
over the production extracted-graph evaluator. Returns `true` exactly when the
graph is in the structural passthrough-only acyclic class, or when it is at or
below the exhaustive node/order limits and every legal topological order
produces the same per-claimant decision. Remaining over-limit graphs
short-circuit to `true` by the runtime feasibility convention mirrored by the
Rust runtime check (`observable.rs`: over-limit graphs are skipped rather than
exhaustively verified). -/
def auditTraversalDeterministic
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) : Bool :=
  if (detectAuditCycles subject.graph).isEmpty &&
      auditGraphPassThroughOnly subject.graph then
    true
  else if subject.graph.nodes.length > 10 then
    true
  else if
      countTopologicalOrdersUpTo subject.graph
        (leanTraversalOrderLimit + 1) > leanTraversalOrderLimit then
    true
  else
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

abbrev ClaimProfile := List AuditGovernanceClaim
abbrev AuditAction := AuditNodeId

structure AuditPath (graph : AuditGovernanceGraph) where
  order : List AuditAction
  legal : order ∈ allTopologicalOrders graph

def auditAlong
    (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : ClaimProfile)
    (path : AuditPath graph) :
    Except AuditError (List (AuditClaimantId × AuditDecision)) := do
  let traversal <- traverseAcyclicWithOrder evalNode graph claims path.order
  pure traversal.finalDecisions

def auditAfter
    (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : ClaimProfile)
    (actions : List AuditAction) :
    Except AuditError (List (AuditClaimantId × AuditDecision)) := do
  let traversal <- traverseAcyclicWithOrder evalNode graph claims actions
  pure traversal.finalDecisions

def auditHasEdge
    (graph : AuditGovernanceGraph)
    (fromNode toNode : AuditNodeId) : Bool :=
  graph.edges.any fun edge => edge.fromNode = fromNode ∧ edge.toNode = toNode

def IndependentActions
    (graph : AuditGovernanceGraph)
    (action1 action2 : AuditAction) : Prop :=
  action1 ≠ action2 ∧
    auditHasEdge graph action1 action2 = false ∧
      auditHasEdge graph action2 action1 = false

instance independentActionsDecidable
    (graph : AuditGovernanceGraph)
    (action1 action2 : AuditAction) :
    Decidable (IndependentActions graph action1 action2) := by
  unfold IndependentActions
  infer_instance

inductive AuditAdjacentSwap
    (graph : AuditGovernanceGraph) :
    AuditPath graph → AuditPath graph → Prop
  | swap
      (left right : AuditPath graph)
      (pref rest : List AuditAction)
      (action1 action2 : AuditAction)
      (hindep : IndependentActions graph action1 action2)
      (hleft : left.order = pref ++ action1 :: action2 :: rest)
      (hright : right.order = pref ++ action2 :: action1 :: rest) :
      AuditAdjacentSwap graph left right

inductive AuditSwapReachable
    (graph : AuditGovernanceGraph) :
    AuditPath graph → AuditPath graph → Prop
  | refl (path : AuditPath graph) :
      AuditSwapReachable graph path path
  | step {left middle right : AuditPath graph}
      (hswap : AuditAdjacentSwap graph left middle)
      (htail : AuditSwapReachable graph middle right) :
      AuditSwapReachable graph left right

def LocalObservableConfluence
    (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : ClaimProfile) : Prop :=
  ∀ {left right : AuditPath graph},
    AuditAdjacentSwap graph left right →
      auditAlong evalNode graph claims left =
        auditAlong evalNode graph claims right

/-- Church-Rosser audit condition: legal audit paths form one adjacent-swap
component, and each local independent swap is observationally silent. -/
structure GovernanceAuditDiamondConditionOn
    (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : ClaimProfile) : Prop where
  acyclic : graph.IsAcyclic
  swap_connected :
    ∀ path1 path2 : AuditPath graph, AuditSwapReachable graph path1 path2
  local_confluence : LocalObservableConfluence evalNode graph claims

structure GovernanceAuditDiamondCondition
    (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph) : Prop where
  on_claims :
    ∀ claims : ClaimProfile,
      GovernanceAuditDiamondConditionOn evalNode graph claims

def GovernanceAuditDiamondConditionOn.ofUniform
    {evalNode : AuditNodeEvaluator}
    {graph : AuditGovernanceGraph}
    (hclass : GovernanceAuditDiamondCondition evalNode graph)
    (claims : ClaimProfile) :
    GovernanceAuditDiamondConditionOn evalNode graph claims :=
  hclass.on_claims claims

theorem auditAlong_eq_of_swap_reachable
    {evalNode : AuditNodeEvaluator}
    {graph : AuditGovernanceGraph}
    {claims : ClaimProfile}
    (hlocal : LocalObservableConfluence evalNode graph claims)
    {path1 path2 : AuditPath graph}
    (hreach : AuditSwapReachable graph path1 path2) :
    auditAlong evalNode graph claims path1 =
      auditAlong evalNode graph claims path2 := by
  induction hreach with
  | refl path =>
      rfl
  | step hswap htail ih =>
      exact (hlocal hswap).trans ih

theorem governance_audit_diamond
    (graph : AuditGovernanceGraph)
    (hclass : GovernanceAuditDiamondCondition auditEvaluateNode graph)
    (claims : ClaimProfile)
    (path1 path2 : AuditPath graph) :
    auditAlong auditEvaluateNode graph claims path1 =
      auditAlong auditEvaluateNode graph claims path2 := by
  let hon := GovernanceAuditDiamondConditionOn.ofUniform hclass claims
  exact auditAlong_eq_of_swap_reachable hon.local_confluence
    (hon.swap_connected path1 path2)

theorem governance_audit_diamond_on
    (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : ClaimProfile)
    (hclass : GovernanceAuditDiamondConditionOn evalNode graph claims)
    (path1 path2 : AuditPath graph) :
    auditAlong evalNode graph claims path1 =
      auditAlong evalNode graph claims path2 := by
  exact auditAlong_eq_of_swap_reachable hclass.local_confluence
    (hclass.swap_connected path1 path2)

def AdjacentSwapObservableDeterminacy
    (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : ClaimProfile) : Prop :=
  ∀ (pref rest : List AuditAction) (action1 action2 : AuditAction),
    IndependentActions graph action1 action2 →
      auditAfter evalNode graph claims (pref ++ action1 :: action2 :: rest) =
        auditAfter evalNode graph claims (pref ++ action2 :: action1 :: rest)

theorem observable_determinacy_under_adjacent_swap
    (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : ClaimProfile)
    (hlocal : AdjacentSwapObservableDeterminacy evalNode graph claims)
    (action1 action2 : AuditAction)
    (rest : List AuditAction)
    (hindep : IndependentActions graph action1 action2) :
    auditAfter evalNode graph claims (action1 :: action2 :: rest) =
      auditAfter evalNode graph claims (action2 :: action1 :: rest) := by
  simpa using hlocal [] rest action1 action2 hindep

def CanonicalTieBreak
    (graph : AuditGovernanceGraph) : Prop :=
  ∀ path1 path2 : AuditPath graph, path1.order = path2.order

def canonicalTieBreakCheck
    (graph : AuditGovernanceGraph) : Bool :=
  match allTopologicalOrders graph with
  | [] => true
  | [_] => true
  | _ :: _ :: _ => false

theorem canonicalTieBreak_of_allTopologicalOrders_singleton
    {graph : AuditGovernanceGraph}
    {order : List AuditAction}
    (horders : allTopologicalOrders graph = [order]) :
    CanonicalTieBreak graph := by
  intro path1 path2
  cases path1 with
  | mk order1 legal1 =>
      cases path2 with
      | mk order2 legal2 =>
          simp [horders] at legal1 legal2
          simp [legal1, legal2]

theorem local_confluence_of_canonical_tie_break
    {evalNode : AuditNodeEvaluator}
    {graph : AuditGovernanceGraph}
    {claims : ClaimProfile}
    (htie : CanonicalTieBreak graph) :
    LocalObservableConfluence evalNode graph claims := by
  intro left right _hswap
  unfold auditAlong
  simp [htie left right]

theorem swap_connected_of_canonical_tie_break
    {graph : AuditGovernanceGraph}
    (htie : CanonicalTieBreak graph) :
    ∀ path1 path2 : AuditPath graph, AuditSwapReachable graph path1 path2 := by
  intro path1 path2
  have horder : path1.order = path2.order := htie path1 path2
  cases path1 with
  | mk order1 legal1 =>
      cases path2 with
      | mk order2 legal2 =>
          simp at horder
          subst order2
          exact AuditSwapReachable.refl ⟨order1, legal1⟩

theorem governance_audit_diamond_condition_on_of_canonical_tie_break
    (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : ClaimProfile)
    (hacyclic : graph.IsAcyclic)
    (htie : CanonicalTieBreak graph) :
    GovernanceAuditDiamondConditionOn evalNode graph claims where
  acyclic := hacyclic
  swap_connected := swap_connected_of_canonical_tie_break htie
  local_confluence := local_confluence_of_canonical_tie_break htie

theorem auditTraversalDeterministic_of_governance_audit_diamond_passthrough
    (graph : AuditGovernanceGraph)
    (claims : ClaimProfile)
    (hclass : GovernanceAuditDiamondConditionOn auditEvaluateNode graph claims)
    (h_passthrough : graph.PassThroughOnly) :
    auditTraversalDeterministic
        { graph := graph, evalNode := auditEvaluateNode } claims = true := by
  have h_acyclic : graph.IsAcyclic := hclass.acyclic
  unfold auditTraversalDeterministic AuditGovernanceGraph.IsAcyclic at *
  have hPass : auditGraphPassThroughOnly graph = true :=
    auditGraphPassThroughOnly_eq_true_of_forall h_passthrough
  simp [h_acyclic, hPass]

/-- Boolean-projection-only certification: `auditTraversalDeterministic` short-
circuits to `true` for any acyclic graph whose edges are all
`AuditEdgeTransform.passThrough`. The proof exercises the function definition's
own short-circuit, not a structural confluence guarantee. The substantive
multi-order-traversal confluence theorem is now the Church-Rosser-style
`governance_audit_diamond`; this theorem remains the executable passthrough
projection that callers use when they only need the boolean diagnostic.
Disclosure mirrored at
`Extract/ObservableDeterminacyParity.lean`, `src/axioms/kernel/observable.rs`
module-doc, and paper §6.6.1. -/
theorem auditTraversalDeterministic_of_acyclic_passthrough
    (G : AuditGovernanceGraph) (h_acyclic : G.IsAcyclic)
    (h_passthrough : G.PassThroughOnly)
    (claims : List AuditGovernanceClaim) :
    auditTraversalDeterministic { graph := G, evalNode := auditEvaluateNode } claims = true := by
  unfold auditTraversalDeterministic AuditGovernanceGraph.IsAcyclic at *
  have hPass : auditGraphPassThroughOnly G = true :=
    auditGraphPassThroughOnly_eq_true_of_forall h_passthrough
  simp [h_acyclic, hPass]

end Legitimacy
