/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/
import Legitimacy.Foundations.Types
import Legitimacy.Regex
import Legitimacy.Results.SelfAudit
import Mathlib.Tactic
/-!
# Legitimacy.Results.GovernanceAdmissibilityAudit.Core
This module starts the Lean port of the runtime extracted-graph audit
semantics used by the Rust `audit-graph` pipeline.
The key structural fact is that the production extractor boundary does not
recover a governance graph from `src/extract/audit.rs` itself. Governance lives
in the extracted runtime graph artifact, not in the audit-source file as a
directly recoverable governance graph. Accordingly, a Lean self-audit
cannot certify the production pipeline by reusing the toy `List GovernanceNodeFn`
encoding from `Results/SelfAudit.lean`; it must instead port the runtime audit
semantics and apply them to a manually defined graph artifact that represents
the production compiler audit surface.
This file implements the Rust witness-corpus generator
`synthetic_claims_for_nodes` from `src/extract/audit.rs` with parity at the data
level:
* requested node ids are canonicalized into sorted deterministic order,
* metric fields are collected from threshold-style and peer-relative binary gates
  only, then canonicalized,
* the baseline structural probe claim is always present,
* one synthetic gate claim is generated for each selected binary gate, and
* the final corpus is deterministically ordered by claimant id.
Subsequent work in this file builds toward the
`compiler_audit_is_self_legitimate` theorem over the audit encoding.
-/
set_option autoImplicit false
namespace Legitimacy
abbrev AuditNodeId := String
abbrev AuditClaimantId := String
abbrev AuditMetricField := String
abbrev AuditMetricValue := ℚ
/-- Exact Rust-side decision surface for extracted governance graphs. -/
inductive AuditDecision where
  | permit
  | deny
  | escalate
  deriving Repr, DecidableEq
/-- Exact Rust-side gate surface used by extracted binary governance nodes. -/
inductive AuditGate where
  | prefixMatch (pattern : String) (decision : AuditDecision)
  | exactMatch (value : String) (decision : AuditDecision)
  | contentMatch (regex : String) (decision : AuditDecision)
  | thresholdGate (field : AuditMetricField) (min : AuditMetricValue)
      (decision : AuditDecision)
  | peerRelative (field : AuditMetricField) (percentile : AuditMetricValue)
      (decision : AuditDecision)
  deriving Repr, DecidableEq
/-- Combination logic for extracted binary governance nodes. -/
inductive AuditGateLogic where
  | allMustPass
  | anyMustPass
  | firstMatch
  deriving Repr, DecidableEq
/-- Lean-side port of the Rust `GovernanceClaim` used by extracted-graph
audits. Metrics are stored canonically as a sorted association list. -/
structure AuditGovernanceClaim where
  claimantId : AuditClaimantId
  strength : AuditMetricValue
  priorityClass : Option String
  path : Option String
  action : Option String
  content : Option String
  metrics : List (AuditMetricField × AuditMetricValue)
  deriving Repr, DecidableEq
/-- Lean-side port of the Rust `GovernanceNode` surface. -/
inductive AuditGovernanceNode where
  | binary (id : AuditNodeId) (name : String) (gates : List AuditGate)
      (default : AuditDecision) (combination : AuditGateLogic)
  | proportional (id : AuditNodeId) (name : String)
      (rule : String) (priorityClasses : List String)
  | threshold (id : AuditNodeId) (name : String)
      (threshold : AuditMetricValue) (field : AuditMetricField)
  deriving Repr, DecidableEq
/-- Lean-side port of Rust `EdgeTransform`. -/
inductive AuditEdgeTransform where
  | passThrough
  | claimModification (delta : AuditMetricValue)
  deriving Repr, DecidableEq
/-- Lean-side port of Rust `GovernanceEdge`. -/
structure AuditGovernanceEdge where
  fromNode : AuditNodeId
  toNode : AuditNodeId
  transform : AuditEdgeTransform
  deriving Repr, DecidableEq
/-- Extracted governance graph used by the admissibility audit. The graph is represented directly
as data because the production extractor boundary does not recover this graph
from the audit-source file itself. -/
structure AuditGovernanceGraph where
  nodes : List AuditGovernanceNode
  edges : List AuditGovernanceEdge
  deriving Repr, DecidableEq
def AuditGovernanceNode.id : AuditGovernanceNode → AuditNodeId
  | .binary id _ _ _ _ => id
  | .proportional id _ _ _ => id
  | .threshold id _ _ _ => id
def AuditGovernanceNode.binaryGates? :
    AuditGovernanceNode → Option (AuditNodeId × List AuditGate)
  | .binary id _ gates _ _ => some (id, gates)
  | _ => none
def canonicalInsertString (value : String) : List String → List String
  | [] => [value]
  | head :: tail =>
      if value = head then
        head :: tail
      else if value ≤ head then
        value :: head :: tail
      else
        head :: canonicalInsertString value tail
def canonicalStrings (values : List String) : List String :=
  values.foldr canonicalInsertString []
lemma mem_canonicalInsertString {value target : String} {xs : List String} :
    target ∈ canonicalInsertString value xs ↔ target = value ∨ target ∈ xs := by
  induction xs with
  | nil =>
      simp [canonicalInsertString]
  | cons head tail ih =>
      unfold canonicalInsertString
      by_cases hEq : value = head
      · simp [hEq]
      · by_cases hLe : value ≤ head
        · simp [hEq, hLe]
        · simp [hEq, hLe, ih, or_left_comm]
lemma mem_canonicalStrings {target : String} {xs : List String} :
    target ∈ canonicalStrings xs ↔ target ∈ xs := by
  unfold canonicalStrings
  induction xs with
  | nil =>
      simp
  | cons head tail ih =>
      simp [List.foldr_cons, mem_canonicalInsertString, ih]
def canonicalInsertMetric (entry : AuditMetricField × AuditMetricValue) :
    List (AuditMetricField × AuditMetricValue) →
      List (AuditMetricField × AuditMetricValue)
  | [] => [entry]
  | head :: tail =>
      if entry.1 = head.1 then
        entry :: tail
      else if entry.1 ≤ head.1 then
        entry :: head :: tail
      else
        head :: canonicalInsertMetric entry tail
def canonicalMetrics
    (entries : List (AuditMetricField × AuditMetricValue)) :
    List (AuditMetricField × AuditMetricValue) :=
  entries.foldr canonicalInsertMetric []
def metricPut (field : AuditMetricField) (value : AuditMetricValue)
    (metrics : List (AuditMetricField × AuditMetricValue)) :
    List (AuditMetricField × AuditMetricValue) :=
  canonicalInsertMetric (field, value) metrics
def gateDecision : AuditGate → AuditDecision
  | .prefixMatch _ decision => decision
  | .exactMatch _ decision => decision
  | .contentMatch _ decision => decision
  | .thresholdGate _ _ decision => decision
  | .peerRelative _ _ decision => decision
def decisionSignalField : AuditDecision → AuditMetricField
  | .permit => "permit_signal"
  | .deny => "deny_signal"
  | .escalate => "escalate_signal"
def applyDecisionMetrics (claim : AuditGovernanceClaim)
    (decision : AuditDecision) : AuditGovernanceClaim :=
  { claim with
      metrics := metricPut (decisionSignalField decision) 1 claim.metrics }
def sampleContentChars : List Char → Bool → List Char
  | [], _ => []
  | ch :: tail, escaped =>
      if escaped then
        ch :: sampleContentChars tail false
      else if ch = '\\' then
        sampleContentChars tail true
      else
        ch :: sampleContentChars tail false
def sampleContent (regex : String) : String :=
  let unescaped := String.ofList (sampleContentChars regex.toList false)
  if unescaped.trimAscii.isEmpty then
    "safe content"
  else
    unescaped
def gateMetricField? : AuditGate → Option AuditMetricField
  | .thresholdGate field _ _ => some field
  | .peerRelative field _ _ => some field
  | _ => none
def findGovernanceNodeById? :
    List AuditGovernanceNode → AuditNodeId → Option AuditGovernanceNode
  | [], _ => none
  | node :: rest, nodeId =>
      if node.id = nodeId then
        some node
      else
        findGovernanceNodeById? rest nodeId
def binaryNodeById? (graph : AuditGovernanceGraph)
    (nodeId : AuditNodeId) : Option (AuditNodeId × List AuditGate) :=
  match findGovernanceNodeById? graph.nodes nodeId with
  | some node => node.binaryGates?
  | none => none
def collectedMetricFieldsForNodes (graph : AuditGovernanceGraph) :
    List AuditNodeId → List AuditMetricField
  | [] => []
  | nodeId :: rest =>
      let nodeFields :=
        match binaryNodeById? graph nodeId with
        | some (_, gates) => gates.filterMap gateMetricField?
        | none => []
      nodeFields ++ collectedMetricFieldsForNodes graph rest
def allMetricFieldsForNodes (graph : AuditGovernanceGraph)
    (nodeIds : List AuditNodeId) : List AuditMetricField :=
  canonicalStrings (collectedMetricFieldsForNodes graph nodeIds)
def baselineClaim (metricFields : List AuditMetricField) :
    AuditGovernanceClaim :=
  { claimantId := "baseline"
    strength := 1
    priorityClass := some "extracted"
    path := some "/workspace/safe.rs"
    action := some "safe_action"
    content := some "safe content"
    metrics := canonicalMetrics (metricFields.map fun field => (field, 0)) }
def claimForGate (claimantId : AuditClaimantId) (gate : AuditGate)
    (metricFields : List AuditMetricField) (index : ℕ) :
    AuditGovernanceClaim :=
  let baseline := baselineClaim metricFields
  let lifted :
      AuditGovernanceClaim :=
    { baseline with
        claimantId := claimantId
        strength := 1 + (index : ℚ) / 20 }
  match gate with
  | .prefixMatch pattern decision =>
      applyDecisionMetrics { lifted with path := some (pattern ++ "/candidate") } decision
  | .exactMatch value decision =>
      applyDecisionMetrics { lifted with action := some value } decision
  | .contentMatch regex decision =>
      applyDecisionMetrics { lifted with content := some (sampleContent regex) } decision
  | .thresholdGate field min decision =>
      applyDecisionMetrics
        { lifted with
            metrics := metricPut field (if min ≤ 0 then 1 else min) lifted.metrics }
        decision
  | .peerRelative field _ decision =>
      applyDecisionMetrics
        { lifted with
            metrics := metricPut field (10 + index) lifted.metrics }
        decision
def gateClaimsForBinaryNodeFrom (nodeId : AuditNodeId)
    (metricFields : List AuditMetricField) :
    ℕ → List AuditGate → List AuditGovernanceClaim
  | _, [] => []
  | index, gate :: rest =>
      claimForGate (nodeId ++ "-gate-" ++ toString index) gate metricFields index ::
        gateClaimsForBinaryNodeFrom nodeId metricFields (index + 1) rest
def gateClaimsForBinaryNode (nodeId : AuditNodeId) (gates : List AuditGate)
    (metricFields : List AuditMetricField) : List AuditGovernanceClaim :=
  gateClaimsForBinaryNodeFrom nodeId metricFields 0 gates
def syntheticClaimsCoreForOrderedNodeIds (graph : AuditGovernanceGraph)
    (metricFields : List AuditMetricField) :
    List AuditNodeId → List AuditGovernanceClaim
  | [] => []
  | nodeId :: rest =>
      let nodeClaims :=
        match binaryNodeById? graph nodeId with
        | some (binaryId, gates) => gateClaimsForBinaryNode binaryId gates metricFields
        | none => []
      nodeClaims ++ syntheticClaimsCoreForOrderedNodeIds graph metricFields rest
def syntheticClaimsCoreForNodes (graph : AuditGovernanceGraph)
    (nodeIds : List AuditNodeId) : List AuditGovernanceClaim :=
  let orderedNodeIds := canonicalStrings nodeIds
  let metricFields := allMetricFieldsForNodes graph orderedNodeIds
  baselineClaim metricFields ::
    syntheticClaimsCoreForOrderedNodeIds graph metricFields orderedNodeIds
def canonicalInsertClaim (claim : AuditGovernanceClaim) :
    List AuditGovernanceClaim → List AuditGovernanceClaim
  | [] => [claim]
  | head :: tail =>
      if claim.claimantId ≤ head.claimantId then
        claim :: head :: tail
      else
        head :: canonicalInsertClaim claim tail
def canonicalClaims
    (claims : List AuditGovernanceClaim) : List AuditGovernanceClaim :=
  claims.foldr canonicalInsertClaim []
/-- Lean port of Rust `synthetic_claims_for_nodes`. -/
def syntheticClaimsForNodes (graph : AuditGovernanceGraph)
    (nodeIds : List AuditNodeId) : List AuditGovernanceClaim :=
  canonicalClaims (syntheticClaimsCoreForNodes graph nodeIds)
lemma syntheticClaimsForNodes_eq_of_canonicalNodeIds_eq
    (graph : AuditGovernanceGraph)
    {left right : List AuditNodeId}
    (hCanon : canonicalStrings left = canonicalStrings right) :
    syntheticClaimsForNodes graph left = syntheticClaimsForNodes graph right := by
  simp [syntheticClaimsForNodes, syntheticClaimsCoreForNodes, hCanon]
lemma baselineClaim_mem_syntheticClaimsCoreForNodes
    (graph : AuditGovernanceGraph) (nodeIds : List AuditNodeId) :
    baselineClaim (allMetricFieldsForNodes graph (canonicalStrings nodeIds)) ∈
      syntheticClaimsCoreForNodes graph nodeIds := by
  simp [syntheticClaimsCoreForNodes]
lemma gateClaimsForBinaryNodeFrom_length
    (nodeId : AuditNodeId) (metricFields : List AuditMetricField) :
    ∀ (start : ℕ) (gates : List AuditGate),
      (gateClaimsForBinaryNodeFrom nodeId metricFields start gates).length = gates.length
  | start, [] => by simp [gateClaimsForBinaryNodeFrom]
  | start, _ :: rest => by
      simp [gateClaimsForBinaryNodeFrom, gateClaimsForBinaryNodeFrom_length]
lemma gateClaimsForBinaryNode_length
    (nodeId : AuditNodeId) (gates : List AuditGate)
    (metricFields : List AuditMetricField) :
    (gateClaimsForBinaryNode nodeId gates metricFields).length = gates.length := by
  simp [gateClaimsForBinaryNode, gateClaimsForBinaryNodeFrom_length]
lemma syntheticClaimsCoreForNodes_has_baseline
    (graph : AuditGovernanceGraph) (nodeIds : List AuditNodeId) :
    (syntheticClaimsCoreForNodes graph nodeIds).length ≥ 1 := by
  unfold syntheticClaimsCoreForNodes
  simp

end Legitimacy
