/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit.Traversal -- direct sub-module import: internal package layer

/-!
# Legitimacy.Results.GovernanceAdmissibilityAudit.Cycles

Cycle discovery, fixed-point cycle iteration, and nonvacuity diagnostics for extracted governance audits.
-/

set_option autoImplicit false

namespace Legitimacy
def syntheticClaimsForCycle (graph : AuditGovernanceGraph)
    (cycle : List AuditNodeId) : List AuditGovernanceClaim :=
  syntheticClaimsForNodes graph cycle
def hasSelfLoop (graph : AuditGovernanceGraph) (nodeId : AuditNodeId) : Bool :=
  graph.edges.any fun edge => edge.fromNode = nodeId && edge.toNode = nodeId
def outgoingSuccessors (graph : AuditGovernanceGraph)
    (nodeId : AuditNodeId) : List AuditNodeId := canonicalStrings <|
  (graph.edges.filterMap fun edge =>
    if edge.fromNode = nodeId && edge.toNode ∈ graphNodeIds graph then some edge.toNode else none)
def collectSuccessors (graph : AuditGovernanceGraph) :
    List AuditNodeId → List AuditNodeId
  | [] => []
  | nodeId :: rest => outgoingSuccessors graph nodeId ++ collectSuccessors graph rest
def reachableFromAux (graph : AuditGovernanceGraph) :
    Nat → List AuditNodeId → List AuditNodeId → List AuditNodeId
  | 0, _, visited => visited
  | fuel + 1, frontier, visited =>
      let next := (canonicalStrings (collectSuccessors graph frontier)).filter fun nodeId =>
        nodeId ∉ visited
      if next.isEmpty then visited
      else reachableFromAux graph fuel next (canonicalStrings (visited ++ next))
def reachableFrom (graph : AuditGovernanceGraph)
    (start : AuditNodeId) : List AuditNodeId :=
  reachableFromAux graph (graphNodeIds graph).length [start] [start]
def removeNodeIds (targets : List AuditNodeId) :
    List AuditNodeId → List AuditNodeId
  | [] => []
  | nodeId :: rest => if nodeId ∈ targets then removeNodeIds targets rest
      else nodeId :: removeNodeIds targets rest
def componentLexLe : List AuditNodeId → List AuditNodeId → Bool
  | [], _ => true
  | _ :: _, [] => false
  | leftHead :: leftTail, rightHead :: rightTail =>
      if leftHead < rightHead then true
      else if rightHead < leftHead then false
      else componentLexLe leftTail rightTail
def insertCycleComponent (component : List AuditNodeId) :
    List (List AuditNodeId) → List (List AuditNodeId)
  | [] => [component]
  | head :: tail =>
      if component = head then head :: tail
      else if componentLexLe component head then component :: head :: tail
      else head :: insertCycleComponent component tail
def nodeInCycles (nodeId : AuditNodeId) (cycles : List (List AuditNodeId)) : Bool :=
  cycles.any fun cycle => nodeId ∈ cycle
def detectAuditCyclesAux (graph : AuditGovernanceGraph) :
    List AuditNodeId → List (List AuditNodeId) → List (List AuditNodeId)
  | [], acc => acc
  | nodeId :: rest, acc =>
      if nodeInCycles nodeId acc then
        detectAuditCyclesAux graph rest acc
      else
        let component := canonicalStrings <| (graphNodeIds graph).filter fun candidate =>
          nodeId ∈ reachableFrom graph candidate && candidate ∈ reachableFrom graph nodeId
        let updated :=
          if component.length > 1 || hasSelfLoop graph nodeId then insertCycleComponent component acc
          else acc
        detectAuditCyclesAux graph rest updated
/-- Lean-side SCC discovery used by the non-vacuity port. The result
is canonicalized lexicographically to match the Rust caller contract that the
"first" cycle is deterministic. -/
def detectAuditCycles (graph : AuditGovernanceGraph) : List (List AuditNodeId) :=
  detectAuditCyclesAux graph (graphNodeIds graph) []

def auditGraphPassThroughOnly (graph : AuditGovernanceGraph) : Bool :=
  graph.edges.all fun edge => edge.transform = .passThrough

namespace AuditGovernanceGraph

def IsAcyclic (graph : AuditGovernanceGraph) : Prop :=
  (detectAuditCycles graph).isEmpty = true

def PassThroughOnly (graph : AuditGovernanceGraph) : Prop :=
  ∀ edge, edge ∈ graph.edges → edge.transform = .passThrough

end AuditGovernanceGraph

theorem auditGraphPassThroughOnly_eq_true_of_forall
    {graph : AuditGovernanceGraph}
    (hPassThrough : graph.PassThroughOnly) :
    auditGraphPassThroughOnly graph = true := by
  unfold auditGraphPassThroughOnly AuditGovernanceGraph.PassThroughOnly at *
  rw [List.all_eq_true]
  intro edge hMem
  simp [hPassThrough edge hMem]

def metricListsWithinEpsilon :
    AuditMetricValue →
      List (AuditMetricField × AuditMetricValue) →
        List (AuditMetricField × AuditMetricValue) → Bool
  | _, [], [] => true
  | epsilon, (leftField, leftValue) :: leftTail, (rightField, rightValue) :: rightTail =>
      leftField = rightField && abs (leftValue - rightValue) ≤ epsilon &&
        metricListsWithinEpsilon epsilon leftTail rightTail
  | _, _, _ => false
def claimsWithinEpsilon (epsilon : AuditMetricValue)
    (left right : AuditGovernanceClaim) : Bool :=
  left.claimantId = right.claimantId &&
    left.priorityClass = right.priorityClass &&
    left.path = right.path &&
    left.action = right.action &&
    left.content = right.content &&
    abs (left.strength - right.strength) ≤ epsilon &&
    metricListsWithinEpsilon epsilon left.metrics right.metrics
def claimById? :
    List AuditGovernanceClaim →
      AuditClaimantId → Option AuditGovernanceClaim
  | [], _ => none
  | claim :: rest, claimantId => if claim.claimantId = claimantId then some claim else claimById? rest claimantId
def lookupDecision? :
    List (AuditClaimantId × AuditDecision) →
      AuditClaimantId → Option AuditDecision
  | [], _ => none
  | (key, decision) :: rest, claimantId => if key = claimantId then some decision else lookupDecision? rest claimantId
def queueMatchesBaseline
    (queuedClaims : List (AuditNodeId × List AuditGovernanceClaim))
    (entryNode : AuditNodeId)
    (baselineClaims : List AuditGovernanceClaim)
    (epsilon : AuditMetricValue) : Bool :=
  match queuedClaims with
  | [(nodeId, queuedForEntry)] =>
      nodeId = entryNode && queuedForEntry.length = baselineClaims.length &&
        baselineClaims.all fun claim => match claimById? queuedForEntry claim.claimantId with
          | some observed => claimsWithinEpsilon epsilon claim observed | none => false
  | _ => false
def recordCycleDecisions
    (fixedPointDecisions : List (AuditClaimantId × AuditDecision))
    (decisions : List AuditClaimDecision) :
    List (AuditClaimantId × AuditDecision) :=
  decisions.foldl (fun acc decision => insertFinalDecision decision.claimantId decision.decision acc)
    fixedPointDecisions
def internalCycleEdges (graph : AuditGovernanceGraph)
    (cycle : List AuditNodeId)
    (nodeId : AuditNodeId) : List AuditGovernanceEdge :=
  graph.edges.filter fun edge => edge.fromNode = nodeId && edge.toNode ∈ cycle
def nodeIndexInCycle? :
    List AuditNodeId → AuditNodeId → Option Nat
  | [], _ => none
  | nodeId :: rest, target => if nodeId = target then some 0 else (nodeIndexInCycle? rest target).map Nat.succ
def propagateCycleEdges
    (graph : AuditGovernanceGraph)
    (cycle : List AuditNodeId)
    (sourceIndex : Nat)
    (forwarded : List AuditGovernanceClaim)
    (decisions : List AuditClaimDecision) :
    List AuditGovernanceEdge →
      List (AuditNodeId × List AuditGovernanceClaim) →
        List (AuditNodeId × List AuditGovernanceClaim) →
          Except AuditError
            (List (AuditNodeId × List AuditGovernanceClaim) ×
              List (AuditNodeId × List AuditGovernanceClaim))
  | [], currentQueued, nextIteration => .ok (currentQueued, nextIteration)
  | edge :: rest, currentQueued, nextIteration => do
      let transformed <- applyTransform edge.transform forwarded decisions
      let targetIndex <- match nodeIndexInCycle? cycle edge.toNode with
        | some index => .ok index
        | none => .error (.invalidEdgeReference edge.toNode)
      if sourceIndex < targetIndex then
        let existing := lookupQueuedClaims currentQueued edge.toNode
        let merged <- mergeClaimBatches edge.toNode existing transformed
        propagateCycleEdges graph cycle sourceIndex forwarded decisions rest
          (insertQueuedClaims edge.toNode merged currentQueued) nextIteration
      else
        let existing := lookupQueuedClaims nextIteration edge.toNode
        let merged <- mergeClaimBatches edge.toNode existing transformed
        propagateCycleEdges graph cycle sourceIndex forwarded decisions rest
          currentQueued (insertQueuedClaims edge.toNode merged nextIteration)
def processCycleNodes (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (cycle : List AuditNodeId) :
    Nat →
      List AuditNodeId →
        List (AuditNodeId × List AuditGovernanceClaim) →
          List (AuditNodeId × List AuditGovernanceClaim) →
            List (AuditClaimantId × AuditDecision) →
              Except AuditError
                (List (AuditNodeId × List AuditGovernanceClaim) ×
                  List (AuditClaimantId × AuditDecision))
  | _, [], _, nextIteration, fixedPointDecisions => .ok (nextIteration, fixedPointDecisions)
  | index, nodeId :: rest, currentQueued, nextIteration, fixedPointDecisions => do
      let node <- match canonicalNodeById? graph nodeId with
        | some found => .ok found
        | none => .error (.invalidEdgeReference nodeId)
      let removed := removeQueuedClaims nodeId currentQueued
      let currentClaims := removed.1
      let queueAfterRemoval := removed.2
      let decisions <- evalNode node currentClaims
      let updatedFixed := recordCycleDecisions fixedPointDecisions decisions
      let forwarded := forwardedClaims currentClaims decisions
      let propagated <-
        propagateCycleEdges graph cycle index forwarded decisions
          (internalCycleEdges graph cycle nodeId) queueAfterRemoval nextIteration
      processCycleNodes evalNode graph cycle (index + 1) rest
        propagated.1 propagated.2 updatedFixed
structure AuditCycleResult where
  converged : Bool
  iterations : Nat
  fixedPointDecisions : List (AuditClaimantId × AuditDecision)
  deriving Repr, DecidableEq
def iterateAuditCycleFuel (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (cycle : List AuditNodeId)
    (entryNode : AuditNodeId)
    (baselineClaims : List AuditGovernanceClaim)
    (epsilon : AuditMetricValue) :
    Nat → Nat → List (AuditNodeId × List AuditGovernanceClaim) →
      Except AuditError AuditCycleResult
  | 0, _, _ => .error (.invalidInput "cycle iteration requires max_iterations > 0")
  | fuel + 1, iteration, queuedClaims => do
      let processed <- processCycleNodes evalNode graph cycle 0 cycle queuedClaims [] []
      let nextIteration := processed.1
      let fixedPointDecisions := processed.2
      if nextIteration.isEmpty then
        pure { converged := true, iterations := iteration, fixedPointDecisions := fixedPointDecisions }
      else if queueMatchesBaseline nextIteration entryNode baselineClaims epsilon then
        pure { converged := false, iterations := iteration, fixedPointDecisions := fixedPointDecisions }
      else if fuel = 0 then
        pure { converged := false, iterations := iteration, fixedPointDecisions := fixedPointDecisions }
      else
        iterateAuditCycleFuel evalNode graph cycle entryNode baselineClaims epsilon
          fuel (iteration + 1) nextIteration
/-- Lean port of Rust `iterate_cycle`, specialized to the exact rational model
used in this file. The Rust `epsilon` guard exists to tolerate floating-point
noise; here the comparisons remain exact when callers pass `0`. -/
def iterateAuditCycle (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (cycle : List AuditNodeId)
    (claims : List AuditGovernanceClaim)
    (maxIterations : Nat)
    (epsilon : AuditMetricValue := 0) :
    Except AuditError AuditCycleResult := do
  validateAuditGovernanceClaims claims
  if cycle.isEmpty then .error (.invalidInput "cycle iteration requires at least one node")
  else if maxIterations = 0 then .error (.invalidInput "cycle iteration requires max_iterations > 0")
  else if epsilon < 0 then .error (.invalidInput s!"cycle iteration epsilon must be non-negative, got {epsilon}")
  else
    let rec validateCycleNodes : List AuditNodeId → Except AuditError Unit
      | [] => .ok ()
      | nodeId :: rest => do
          match canonicalNodeById? graph nodeId with
          | some _ => validateCycleNodes rest
          | none => .error (.invalidEdgeReference nodeId)
    validateCycleNodes cycle
    match cycle with
    | [] => .error (.invalidInput "cycle iteration requires at least one node")
    | entryNode :: _ =>
        iterateAuditCycleFuel evalNode graph cycle entryNode claims epsilon maxIterations 1
          [(entryNode, claims)]
def nonterminalClaimants
    (claims : List AuditGovernanceClaim)
    (decisions : List (AuditClaimantId × AuditDecision)) :
    List AuditClaimantId :=
  canonicalStrings <| claims.filterMap fun claim =>
    match lookupDecision? decisions claim.claimantId with
    | some .permit | some .deny => none
    | some .escalate | none => some claim.claimantId
/-- Nonterminal claimants under the review-required interpretation. Terminal
`.escalate` counts as an eventually upgradeable review-required result, not as
an unresolved nonterminal outcome. Missing decisions remain nonterminal. -/
def nonterminalClaimantsReviewRequired
    (claims : List AuditGovernanceClaim)
    (decisions : List (AuditClaimantId × AuditDecision)) :
    List AuditClaimantId :=
  canonicalStrings <| claims.filterMap fun claim =>
    match lookupDecision? decisions claim.claimantId with
    | some .permit | some .deny | some .escalate => none
    | none => some claim.claimantId

def reviewRequiredTerminalFound
    (claims : List AuditGovernanceClaim)
    (decisions : List (AuditClaimantId × AuditDecision)) : Bool :=
  claims.any fun claim =>
    match lookupDecision? decisions claim.claimantId with
    | some .permit | some .escalate => true
    | some .deny | none => false

inductive AuditNonvacuityFailure where
  | emptyGraph
  | nonterminalEscalation (claimants : List AuditClaimantId)
  | deadlockedCycle (cycle : List AuditNodeId) (claimants : List AuditClaimantId)
  | cycleEscalation (cycle : List AuditNodeId) (claimants : List AuditClaimantId)
  | allDeny (usedCycleProbes : Bool)
  deriving Repr, DecidableEq
inductive AuditNonvacuityVerdict where
  | admissible (perturbationsTested : Nat)
  | rejected (failure : AuditNonvacuityFailure)
  deriving Repr, DecidableEq
/-- Lean port of `src/extract/nonvacuity.rs`. This preserves the Rust
distinction between acyclic nonterminal `Escalate`, cycle deadlock / cycle
fixed-point escalation, and the separate all-deny failure. -/
def auditGraphNonvacuity (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    Except AuditError AuditNonvacuityVerdict := do
  if graph.nodes.isEmpty then pure (.rejected .emptyGraph)
  else
    let cycles := detectAuditCycles graph
    if cycles.isEmpty then
      let traversal <- traverseAcyclic evalNode graph claims
      let nonterminal := nonterminalClaimants claims traversal.finalDecisions
      if !nonterminal.isEmpty then pure (.rejected (.nonterminalEscalation nonterminal))
      else if claims.any fun claim =>
          lookupDecision? traversal.finalDecisions claim.claimantId = some .permit then
        pure (.admissible claims.length)
      else
        pure (.rejected (.allDeny false))
    else
      let rec evaluateCycles
          (remaining : List (List AuditNodeId))
          (permitFound : Bool)
          (perturbationsTested : Nat) :
          Except AuditError AuditNonvacuityVerdict := do
        match remaining with
        | [] =>
            if permitFound then
              pure (.admissible perturbationsTested)
            else
              pure (.rejected (.allDeny true))
        | cycle :: rest =>
            let cycleClaims := syntheticClaimsForCycle graph cycle
            let result <- iterateAuditCycle evalNode graph cycle cycleClaims 32
            let nextPerturbations := perturbationsTested + result.iterations
            if !result.converged then
              let deadlocked := canonicalStrings (cycleClaims.map AuditGovernanceClaim.claimantId)
              pure (.rejected (.deadlockedCycle cycle deadlocked))
            else
              let nonterminal := nonterminalClaimants cycleClaims result.fixedPointDecisions
              if !nonterminal.isEmpty then pure (.rejected (.cycleEscalation cycle nonterminal))
              else
                let cyclePermits := cycleClaims.any fun claim =>
                  lookupDecision? result.fixedPointDecisions claim.claimantId = some .permit
                evaluateCycles rest (permitFound || cyclePermits) nextPerturbations
      evaluateCycles cycles false claims.length
def auditGraphNonvacuous (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    Except AuditError Bool := do
  match ← auditGraphNonvacuity evalNode graph claims with
  | .admissible _ => pure true
  | .rejected _ => pure false

/-- review-required nonvacuity under review-required semantics. This mirrors
`auditGraphNonvacuity`, but treats terminal `.escalate` as a non-vacuous
review-required result. Deadlocked cycles and missing claimant decisions remain
failures. -/
def auditGraphNonvacuityReviewRequired (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    Except AuditError AuditNonvacuityVerdict := do
  if graph.nodes.isEmpty then pure (.rejected .emptyGraph)
  else
    let cycles := detectAuditCycles graph
    if cycles.isEmpty then
      let traversal <- traverseAcyclic evalNode graph claims
      let nonterminal := nonterminalClaimantsReviewRequired claims traversal.finalDecisions
      if !nonterminal.isEmpty then pure (.rejected (.nonterminalEscalation nonterminal))
      else if reviewRequiredTerminalFound claims traversal.finalDecisions then
        pure (.admissible claims.length)
      else
        pure (.rejected (.allDeny false))
    else
      let rec evaluateCycles
          (remaining : List (List AuditNodeId))
          (terminalFound : Bool)
          (perturbationsTested : Nat) :
          Except AuditError AuditNonvacuityVerdict := do
        match remaining with
        | [] =>
            if terminalFound then
              pure (.admissible perturbationsTested)
            else
              pure (.rejected (.allDeny true))
        | cycle :: rest =>
            let cycleClaims := syntheticClaimsForCycle graph cycle
            let result <- iterateAuditCycle evalNode graph cycle cycleClaims 32
            let nextPerturbations := perturbationsTested + result.iterations
            if !result.converged then
              let deadlocked := canonicalStrings (cycleClaims.map AuditGovernanceClaim.claimantId)
              pure (.rejected (.deadlockedCycle cycle deadlocked))
            else
              let nonterminal :=
                nonterminalClaimantsReviewRequired cycleClaims result.fixedPointDecisions
              if !nonterminal.isEmpty then pure (.rejected (.cycleEscalation cycle nonterminal))
              else
                let cycleTerminalFound :=
                  reviewRequiredTerminalFound cycleClaims result.fixedPointDecisions
                evaluateCycles rest (terminalFound || cycleTerminalFound)
                  nextPerturbations
      evaluateCycles cycles false claims.length

def auditGraphNonvacuousReviewRequired (evalNode : AuditNodeEvaluator)
    (graph : AuditGovernanceGraph)
    (claims : List AuditGovernanceClaim) :
    Except AuditError Bool := do
  match ← auditGraphNonvacuityReviewRequired evalNode graph claims with
  | .admissible _ => pure true
  | .rejected _ => pure false


end Legitimacy
