/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit.Core -- direct sub-module import: internal package layer

/-!
# Legitimacy.Results.GovernanceAdmissibilityAudit.Traversal

Acyclic traversal state, queue propagation, topological ordering, and determinism helpers for extracted governance audits.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Claim-level decision emitted by one runtime node evaluation. -/
structure AuditClaimDecision where
  claimantId : AuditClaimantId
  decision : AuditDecision
  deriving Repr, DecidableEq
/-- Canonical error surface needed by the governance-admissibility audit port. -/
inductive AuditError where
  | invalidEdgeReference (nodeId : AuditNodeId)
  | unsupportedNodeType (nodeId : AuditNodeId) (nodeType : String)
  | invalidGovernanceStrength
      (claimantId : AuditClaimantId) (strength : AuditMetricValue)
  | invalidGate (gate : String) (message : String)
  | conflictingClaimFeed (nodeId : AuditNodeId) (claimantId : AuditClaimantId)
  | noEntryNodes
  | cycleError (cycle : List AuditNodeId)
  | invalidInput (message : String)
  deriving Repr, DecidableEq
/-- Canonicalized traversal output corresponding to the acyclic Rust traversal
surface. Map-like fields are represented as sorted association lists. -/
structure AuditTraversalResult where
  entryNodes : List AuditNodeId
  nodeDecisions : List (AuditNodeId × List AuditClaimDecision)
  finalDecisions : List (AuditClaimantId × AuditDecision)
  cycles : List (List AuditNodeId)
  deriving Repr, DecidableEq
/-- Internal traversal state for the acyclic port. -/
structure AuditTraversalState where
  queuedClaims : List (AuditNodeId × List AuditGovernanceClaim)
  nodeDecisions : List (AuditNodeId × List AuditClaimDecision)
  finalDecisions : List (AuditClaimantId × AuditDecision)
  deriving Repr, DecidableEq
/-- The traversal layer is parameterized by a node evaluator so this file does
not smuggle in a fake regex semantics for `ContentMatch`. -/
abbrev AuditNodeEvaluator :=
  AuditGovernanceNode →
    List AuditGovernanceClaim →
      Except AuditError (List AuditClaimDecision)
def auditNodeKind : AuditGovernanceNode → String
  | .binary .. => "Binary"
  | .proportional .. => "Proportional"
  | .threshold .. => "Threshold"
def canonicalInsertNode (node : AuditGovernanceNode) :
    List AuditGovernanceNode → List AuditGovernanceNode
  | [] => [node]
  | head :: tail =>
      if node.id = head.id then
        node :: tail
      else if node.id ≤ head.id then
        node :: head :: tail
      else
        head :: canonicalInsertNode node tail
def canonicalNodes (nodes : List AuditGovernanceNode) :
    List AuditGovernanceNode :=
  nodes.foldr canonicalInsertNode []
def graphNodeTable (graph : AuditGovernanceGraph) : List AuditGovernanceNode :=
  canonicalNodes graph.nodes
def graphNodeIds (graph : AuditGovernanceGraph) : List AuditNodeId :=
  (graphNodeTable graph).map AuditGovernanceNode.id
def canonicalNodeById? (graph : AuditGovernanceGraph)
    (nodeId : AuditNodeId) : Option AuditGovernanceNode :=
  findGovernanceNodeById? (graphNodeTable graph) nodeId
def validateAuditGovernanceClaim
    (claim : AuditGovernanceClaim) : Except AuditError Unit :=
  if claim.strength ≤ 0 then
    .error (.invalidGovernanceStrength claim.claimantId claim.strength)
  else if claim.priorityClass.isSome &&
      (claim.priorityClass.getD "").trimAscii.isEmpty then
    .error (.invalidInput
      s!"claim '{claim.claimantId}' priority_class must be non-empty when provided")
  else
    .ok ()
def validateAuditGovernanceClaims :
    List AuditGovernanceClaim → Except AuditError Unit
  | [] => .ok ()
  | claim :: rest => do
      validateAuditGovernanceClaim claim
      validateAuditGovernanceClaims rest
def decisionRank : AuditDecision → Nat
  | .deny => 0
  | .escalate => 1
  | .permit => 2
/-- Review-required rank projection for the review-required alternate semantics.

Under this parallel research-axis lattice, terminal `.escalate` is interpreted
as a review-required outcome that can be upgraded by downstream human or
protocol review. For monotonicity preservation it therefore lives in the same
non-denial equivalence class as `.permit`; only transitions into `.deny` are
rank-lowering. The canonical `decisionRank` above remains unchanged. -/
def decisionRankReviewRequired : AuditDecision → Nat
  | .deny => 0
  | .escalate => 1
  | .permit => 1
def mergeFinalDecision
    (left right : AuditDecision) : AuditDecision :=
  if decisionRank left ≤ decisionRank right then left else right

@[simp] theorem mergeFinalDecision_assoc (a b c : AuditDecision) :
    mergeFinalDecision (mergeFinalDecision a b) c =
      mergeFinalDecision a (mergeFinalDecision b c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem mergeFinalDecision_comm (a b : AuditDecision) :
    mergeFinalDecision a b = mergeFinalDecision b a := by
  cases a <;> cases b <;> rfl

@[simp] theorem mergeFinalDecision_idem (a : AuditDecision) :
    mergeFinalDecision a a = a := by
  cases a <;> rfl

def decisionForClaimant? :
    List AuditClaimDecision → AuditClaimantId → Option AuditDecision
  | [], _ => none
  | decision :: rest, claimantId =>
      if decision.claimantId = claimantId then
        some decision.decision
      else
        decisionForClaimant? rest claimantId
def forwardedClaims
    (claims : List AuditGovernanceClaim)
    (decisions : List AuditClaimDecision) :
    List AuditGovernanceClaim :=
  claims.filter fun claim =>
    decisionForClaimant? decisions claim.claimantId = some .escalate
def applyTransform
    (transform : AuditEdgeTransform)
    (claims : List AuditGovernanceClaim)
    (decisions : List AuditClaimDecision) :
    Except AuditError (List AuditGovernanceClaim) :=
  match transform with
  | .passThrough => .ok claims
  | .claimModification delta =>
      let rec go :
          List AuditGovernanceClaim →
            Except AuditError (List AuditGovernanceClaim)
        | [] => .ok []
        | claim :: rest => do
            let transformed :=
              if decisionForClaimant? decisions claim.claimantId = some .permit then
                { claim with strength := claim.strength + delta }
              else
                claim
            validateAuditGovernanceClaim transformed
            let tail <- go rest
            pure (transformed :: tail)
      go claims
def lookupQueuedClaims :
    List (AuditNodeId × List AuditGovernanceClaim) →
      AuditNodeId → List AuditGovernanceClaim
  | [], _ => []
  | (key, claims) :: rest, target =>
      if key = target then claims else lookupQueuedClaims rest target
def removeQueuedClaims
    (target : AuditNodeId) :
    List (AuditNodeId × List AuditGovernanceClaim) →
      List AuditGovernanceClaim ×
        List (AuditNodeId × List AuditGovernanceClaim)
  | [] => ([], [])
  | (key, claims) :: rest =>
      if key = target then
        (claims, rest)
      else
        let removed := removeQueuedClaims target rest
        (removed.1, (key, claims) :: removed.2)
def insertQueuedClaims
    (nodeId : AuditNodeId) (claims : List AuditGovernanceClaim) :
    List (AuditNodeId × List AuditGovernanceClaim) →
      List (AuditNodeId × List AuditGovernanceClaim)
  | [] => [(nodeId, claims)]
  | (key, current) :: rest =>
      if nodeId = key then
        (nodeId, claims) :: rest
      else if nodeId ≤ key then
        (nodeId, claims) :: (key, current) :: rest
      else
        (key, current) :: insertQueuedClaims nodeId claims rest
def insertNodeDecisions
    (nodeId : AuditNodeId) (decisions : List AuditClaimDecision) :
    List (AuditNodeId × List AuditClaimDecision) →
      List (AuditNodeId × List AuditClaimDecision)
  | [] => [(nodeId, decisions)]
  | (key, current) :: rest =>
      if nodeId = key then
        (nodeId, decisions) :: rest
      else if nodeId ≤ key then
        (nodeId, decisions) :: (key, current) :: rest
      else
        (key, current) :: insertNodeDecisions nodeId decisions rest
def insertFinalDecision
    (claimantId : AuditClaimantId) (decision : AuditDecision) :
    List (AuditClaimantId × AuditDecision) →
      List (AuditClaimantId × AuditDecision)
  | [] => [(claimantId, decision)]
  | (key, current) :: rest =>
      if claimantId = key then
        (claimantId, decision) :: rest
      else if claimantId ≤ key then
        (claimantId, decision) :: (key, current) :: rest
      else
        (key, current) :: insertFinalDecision claimantId decision rest
def recordFinalDecisions
    (finalDecisions : List (AuditClaimantId × AuditDecision))
    (decisions : List AuditClaimDecision)
    (hasOutgoing : Bool) :
    List (AuditClaimantId × AuditDecision) :=
  let rec go
      (acc : List (AuditClaimantId × AuditDecision)) :
      List AuditClaimDecision →
        List (AuditClaimantId × AuditDecision)
    | [] => acc
    | decision :: rest =>
        if decision.decision = .escalate && hasOutgoing then
          go acc rest
        else
          let merged :=
            match decisionForClaimant? (acc.map fun entry =>
                { claimantId := entry.1, decision := entry.2 }) decision.claimantId with
            | some existing => mergeFinalDecision existing decision.decision
            | none => decision.decision
          go (insertFinalDecision decision.claimantId merged acc) rest
  go finalDecisions decisions
def insertMergedClaim
    (nodeId : AuditNodeId) (claim : AuditGovernanceClaim) :
    List AuditGovernanceClaim →
      Except AuditError (List AuditGovernanceClaim)
  | [] => .ok [claim]
  | head :: tail =>
      if claim.claimantId = head.claimantId then
        if claim = head then
          .ok (head :: tail)
        else
          .error (.conflictingClaimFeed nodeId claim.claimantId)
      else if claim.claimantId ≤ head.claimantId then
        .ok (claim :: head :: tail)
      else do
        let mergedTail <- insertMergedClaim nodeId claim tail
        pure (head :: mergedTail)
def mergeClaimBatches
    (nodeId : AuditNodeId)
    (incoming additional : List AuditGovernanceClaim) :
    Except AuditError (List AuditGovernanceClaim) :=
  let rec go
      (acc : List AuditGovernanceClaim) :
      List AuditGovernanceClaim →
        Except AuditError (List AuditGovernanceClaim)
    | [] => .ok acc
    | claim :: rest => do
        let next <- insertMergedClaim nodeId claim acc
        go next rest
  do
    let mergedIncoming <- go [] incoming
    go mergedIncoming additional
def outgoingEdges (graph : AuditGovernanceGraph)
    (nodeId : AuditNodeId) : List AuditGovernanceEdge :=
  graph.edges.filter fun edge => edge.fromNode = nodeId
def incomingCountWithin (graph : AuditGovernanceGraph)
    (remaining : List AuditNodeId) (nodeId : AuditNodeId) : Nat :=
  graph.edges.foldl (fun count edge =>
    if edge.toNode = nodeId ∧ edge.fromNode ∈ remaining then count + 1 else count) 0
def entryNodes (graph : AuditGovernanceGraph) : List AuditNodeId :=
  (graphNodeIds graph).filter fun nodeId => incomingCountWithin graph (graphNodeIds graph) nodeId = 0
def firstReadyNodeScan (graph : AuditGovernanceGraph)
    (remaining : List AuditNodeId) :
    List AuditNodeId → Option AuditNodeId
  | [] => none
  | nodeId :: rest =>
      if incomingCountWithin graph remaining nodeId = 0 then
        some nodeId
      else
        firstReadyNodeScan graph remaining rest
def firstReadyNode? (graph : AuditGovernanceGraph)
    (remaining : List AuditNodeId) : Option AuditNodeId :=
  firstReadyNodeScan graph remaining remaining
def lastReadyNodeScan (graph : AuditGovernanceGraph)
    (remaining : List AuditNodeId) :
    Option AuditNodeId → List AuditNodeId → Option AuditNodeId
  | candidate, [] => candidate
  | candidate, nodeId :: rest =>
      if incomingCountWithin graph remaining nodeId = 0 then
        lastReadyNodeScan graph remaining (some nodeId) rest
      else
        lastReadyNodeScan graph remaining candidate rest
def lastReadyNode? (graph : AuditGovernanceGraph)
    (remaining : List AuditNodeId) : Option AuditNodeId :=
  lastReadyNodeScan graph remaining none remaining
def removeNodeId (target : AuditNodeId) : List AuditNodeId → List AuditNodeId
  | [] => []
  | head :: tail =>
      if head = target then
        tail
      else
        head :: removeNodeId target tail
def topologicalOrderAux (graph : AuditGovernanceGraph) :
    Nat → List AuditNodeId → Except AuditError (List AuditNodeId)
  | 0, remaining =>
      match remaining with
      | [] => .ok []
      | _ => .error (.cycleError remaining)
  | fuel + 1, remaining =>
      match remaining with
      | [] => .ok []
      | _ =>
          match firstReadyNode? graph remaining with
          | none => .error (.cycleError remaining)
          | some nodeId =>
              match topologicalOrderAux graph fuel (removeNodeId nodeId remaining) with
              | .ok tailOrder => .ok (nodeId :: tailOrder)
              | .error err => .error err
def topologicalOrder (graph : AuditGovernanceGraph) :
    Except AuditError (List AuditNodeId) :=
  topologicalOrderAux graph (graphNodeIds graph).length (graphNodeIds graph)
def descendingTopologicalOrderAux (graph : AuditGovernanceGraph) :
    Nat → List AuditNodeId → Except AuditError (List AuditNodeId)
  | 0, remaining =>
      match remaining with
      | [] => .ok []
      | _ => .error (.cycleError remaining)
  | fuel + 1, remaining =>
      match remaining with
      | [] => .ok []
      | _ =>
          match lastReadyNode? graph remaining with
          | none => .error (.cycleError remaining)
          | some nodeId =>
              match descendingTopologicalOrderAux graph fuel
                  (removeNodeId nodeId remaining) with
              | .ok tailOrder => .ok (nodeId :: tailOrder)
              | .error err => .error err
def descendingTopologicalOrder (graph : AuditGovernanceGraph) :
    Except AuditError (List AuditNodeId) :=
  descendingTopologicalOrderAux graph
    (graphNodeIds graph).length (graphNodeIds graph)
def readyNodes (graph : AuditGovernanceGraph)
    (remaining : List AuditNodeId) : List AuditNodeId :=
  remaining.filter fun nodeId => incomingCountWithin graph remaining nodeId = 0
def allTopologicalOrdersAux (graph : AuditGovernanceGraph) :
    Nat → List AuditNodeId → List (List AuditNodeId)
  | 0, remaining =>
      if remaining.isEmpty then
        [[]]
      else
        []
  | fuel + 1, remaining =>
      if remaining.isEmpty then
        [[]]
      else
        ((readyNodes graph remaining).map fun nodeId =>
          (allTopologicalOrdersAux graph fuel
            (removeNodeId nodeId remaining)).map fun order => nodeId :: order).flatten
def allTopologicalOrders (graph : AuditGovernanceGraph) :
    List (List AuditNodeId) :=
  allTopologicalOrdersAux graph (graphNodeIds graph).length (graphNodeIds graph)
def leanTraversalOrderLimit : Nat := 10000
def countTopologicalOrdersUpToAux (graph : AuditGovernanceGraph) (cap : Nat) :
    Nat → List AuditNodeId → Nat
  | 0, remaining =>
      if remaining.isEmpty then
        1
      else
        0
  | fuel + 1, remaining =>
      if remaining.isEmpty then
        1
      else
        (readyNodes graph remaining).foldl
          (fun total nodeId =>
            if total ≥ cap then
              total
            else
              Nat.min cap
                (total + countTopologicalOrdersUpToAux graph cap fuel
                  (removeNodeId nodeId remaining)))
          0
def countTopologicalOrdersUpTo
    (graph : AuditGovernanceGraph) (cap : Nat) : Nat :=
  countTopologicalOrdersUpToAux graph cap
    (graphNodeIds graph).length (graphNodeIds graph)
def seedQueuedClaims
    (entryNodes : List AuditNodeId) (claims : List AuditGovernanceClaim) :
    List (AuditNodeId × List AuditGovernanceClaim) :=
  entryNodes.foldr (fun nodeId acc => insertQueuedClaims nodeId claims acc) []
def propagateEdges
    (queue : List (AuditNodeId × List AuditGovernanceClaim))
    (edges : List AuditGovernanceEdge)
    (forwarded : List AuditGovernanceClaim)
    (decisions : List AuditClaimDecision) :
    Except AuditError
      (List (AuditNodeId × List AuditGovernanceClaim)) :=
  let rec go
      (currentQueue : List (AuditNodeId × List AuditGovernanceClaim)) :
      List AuditGovernanceEdge →
        Except AuditError
          (List (AuditNodeId × List AuditGovernanceClaim))
    | [] => .ok currentQueue
    | edge :: rest => do
        let transformed <- applyTransform edge.transform forwarded decisions
        let existing := lookupQueuedClaims currentQueue edge.toNode
        let merged <- mergeClaimBatches edge.toNode existing transformed
        let nextQueue := insertQueuedClaims edge.toNode merged currentQueue
        go nextQueue rest
  go queue edges
def traverseOrder (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph) :
    List AuditNodeId →
      AuditTraversalState →
        Except AuditError AuditTraversalState
  | [], state => .ok state
  | nodeId :: rest, state => do
      let node <- match canonicalNodeById? graph nodeId with
        | some node => .ok node
        | none => .error (.invalidEdgeReference nodeId)
      let removed := removeQueuedClaims nodeId state.queuedClaims
      let currentClaims := removed.1
      let queueAfterRemoval := removed.2
      let decisions <- evalNode node currentClaims
      let hasOutgoing := !(outgoingEdges graph nodeId).isEmpty
      let updatedFinal := recordFinalDecisions state.finalDecisions decisions hasOutgoing
      let forwarded := forwardedClaims currentClaims decisions
      let updatedNodeDecisions := insertNodeDecisions nodeId decisions state.nodeDecisions
      let propagatedQueue <-
        propagateEdges queueAfterRemoval (outgoingEdges graph nodeId) forwarded decisions
      traverseOrder evalNode graph rest
        { queuedClaims := propagatedQueue
          nodeDecisions := updatedNodeDecisions
          finalDecisions := updatedFinal }
/-- Lean port of the acyclic Rust traversal. `cycles` is always empty
on successful outputs because this step models the non-cycle branch only. -/
def traverseAcyclic (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    Except AuditError AuditTraversalResult := do
  validateAuditGovernanceClaims claims
  let entries := entryNodes graph
  if (graphNodeIds graph).isEmpty || entries.isEmpty then
    .error .noEntryNodes
  else
    let order <- topologicalOrder graph
    let finalState <-
      traverseOrder evalNode graph order
        { queuedClaims := seedQueuedClaims entries claims
          nodeDecisions := []
          finalDecisions := [] }
    pure
      { entryNodes := entries
        nodeDecisions := finalState.nodeDecisions
        finalDecisions := finalState.finalDecisions
        cycles := [] }
def traverseAcyclicWithOrder (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim)
    (order : List AuditNodeId) :
    Except AuditError AuditTraversalResult := do
  validateAuditGovernanceClaims claims
  let entries := entryNodes graph
  if (graphNodeIds graph).isEmpty || entries.isEmpty then
    .error .noEntryNodes
  else
    let finalState <-
      traverseOrder evalNode graph order
        { queuedClaims := seedQueuedClaims entries claims
          nodeDecisions := []
          finalDecisions := [] }
    pure
      { entryNodes := entries
        nodeDecisions := finalState.nodeDecisions
        finalDecisions := finalState.finalDecisions
        cycles := [] }
lemma topologicalOrderAux_length_le_fuel (graph : AuditGovernanceGraph) :
    ∀ {fuel remaining order},
      topologicalOrderAux graph fuel remaining = .ok order →
        order.length ≤ fuel
  | 0, [], order, h => by
      cases h
      simp
  | 0, _ :: _, order, h => by
      cases h
  | fuel + 1, [], order, h => by
      cases h
      simp
  | fuel + 1, head :: tail, order, h => by
      cases hReady : firstReadyNode? graph (head :: tail) with
      | none =>
          simp [topologicalOrderAux, hReady] at h
      | some nodeId =>
          cases hTail : topologicalOrderAux graph fuel (removeNodeId nodeId (head :: tail)) with
          | error err =>
              simp [topologicalOrderAux, hReady, hTail] at h
          | ok tailOrder =>
              simp [topologicalOrderAux, hReady, hTail] at h
              cases h
              exact Nat.succ_le_succ (topologicalOrderAux_length_le_fuel graph hTail)
lemma topologicalOrder_length_le_nodeCount
    (graph : AuditGovernanceGraph) {order : List AuditNodeId}
    (hOrder : topologicalOrder graph = .ok order) :
    order.length ≤ (graphNodeIds graph).length := by
  simpa [topologicalOrder] using topologicalOrderAux_length_le_fuel graph hOrder
lemma entryNodes_wellFormed (graph : AuditGovernanceGraph) :
    ∀ nodeId ∈ entryNodes graph, nodeId ∈ graphNodeIds graph := by
  intro nodeId hMem
  unfold entryNodes at hMem
  exact List.mem_of_mem_filter hMem
theorem traverseAcyclic_deterministic
    (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim)
    {left right : AuditTraversalResult}
    (hLeft : traverseAcyclic evalNode graph claims = .ok left)
    (hRight : traverseAcyclic evalNode graph claims = .ok right) :
    left = right := by
  have hEq : (.ok left : Except AuditError AuditTraversalResult) = .ok right := by
    exact hLeft.symm.trans hRight
  exact Except.ok.inj hEq

end Legitimacy
