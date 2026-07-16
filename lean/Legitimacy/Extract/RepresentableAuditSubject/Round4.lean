/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.RepresentableAuditSubject.Round2
import Legitimacy.Extract.RepresentableAuditSubject.PermitOnly

/-!
# Round-4 representable faithfulness and corpus-completeness boundary

This module keeps the weak-predicate counterexample as a boundary theorem and
then strengthens the representation surface with
`RepresentableAuditSubject.FaithfulRepresentable`.

The weak witness below is now read as a necessity result: without the
audit-source faithfulness hypothesis, the executable audit can permit
everything while the represented source carries the peer-relative obstruction.
The faithful witness at the end shows the remaining boundary is the production
corpus itself, not the old predicate weakness.

FRAMEWORK-LIMITS: the theorem
`faithful_shape_derived_self_certification_strictly_weaker_than_all_profile_consistency`
is deliberately narrow.  It concerns the current finite executable
consistency core `auditCheckConsistencyCore` run on the shape-derived production
corpus `auditGraphClaims`.  The witness is faithful and represented, but that
finite corpus is generated from audit-graph shape and does not exercise the
profile-relational peer-relative obstruction.  The result does not say that no
finite executable audit could ever be obstruction-complete; it says this
current shape-derived self-certification cannot be promoted to all-profile
`GraphConsistencyP` without an additional representation/completeness theorem.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Weak-predicate boundary witness: the carried audit subject is the
certificate-positive permit-only fixture, while the represented source is the
peer-relative obstruction source.  This satisfies the old structural
representation predicate because that predicate constrains the represented
source and the audit graph shape, but it does not assert an evalNode/source
faithfulness weld. -/
def permitAuditWithPeerRelativeSourceSubject : RepresentableAuditSubject where
  name := "permit-audit-with-peer-relative-source"
  subject := permitOnlyAuditSubject
  source := representedPeerSource

theorem permitAuditWithPeerRelativeSourceSubject_representable :
    RepresentableAuditSubject.Representable
      permitAuditWithPeerRelativeSourceSubject := by
  refine ⟨?_, ?_, ?_⟩
  · simp [permitAuditWithPeerRelativeSourceSubject, representedPeerSource]
  · rfl
  · intro node hnode
    simp [permitAuditWithPeerRelativeSourceSubject, permitOnlyAuditSubject]
      at hnode
    rcases hnode with rfl
    exact
      ⟨"permit-only", "permit only", [], AuditDecision.permit, rfl⟩

def permitAuditWithPeerRelativeSource :
    { s : RepresentableAuditSubject //
      RepresentableAuditSubject.Representable s } :=
  ⟨permitAuditWithPeerRelativeSourceSubject,
    permitAuditWithPeerRelativeSourceSubject_representable⟩

theorem permitAuditWithPeerRelativeSource_core_passes :
    auditCheckConsistencyCore
        permitAuditWithPeerRelativeSource.1.subject
        (auditGraphClaims permitAuditWithPeerRelativeSource.1.subject) =
      .ok true := by
  exact auditCheckStatus_passed_implies_consistencyCore
    permitAuditWithPeerRelativeSource.1.subject
    (permitOnly_certificate_holds.2.1 AuditCheck.consistency
      (by simp [auditCheckOrder]))

theorem permitAuditWithPeerRelativeSource_repr_eq :
    RepresentableAuditSubject.repr permitAuditWithPeerRelativeSource =
      [weakestWithStrongerPeerNode] := by
  simp [RepresentableAuditSubject.repr, permitAuditWithPeerRelativeSource,
    permitAuditWithPeerRelativeSourceSubject, representedPeerSource,
    RepresentableSource.toGovernanceGraph,
    weakestWithStrongerPeerRepresentableNode_toGovernanceNode]

theorem permitAuditWithPeerRelativeSource_not_graphConsistent :
    ¬ GraphConsistencyP
      (RepresentableAuditSubject.repr permitAuditWithPeerRelativeSource) := by
  simpa [permitAuditWithPeerRelativeSource_repr_eq, representedPeer_repr_eq]
    using representedPeer_not_graphConsistent

/-- The audit-source faithfulness hypothesis is necessary: under the weak
structural predicate, the audit permits the current corpus while the represented
source is the peer-relative obstruction graph. -/
theorem representable_corpus_pass_counterexample_to_all_profile_consistency :
    auditCheckConsistencyCore
        permitAuditWithPeerRelativeSource.1.subject
        (auditGraphClaims permitAuditWithPeerRelativeSource.1.subject) =
        .ok true ∧
      ¬ GraphConsistencyP
        (RepresentableAuditSubject.repr permitAuditWithPeerRelativeSource) :=
  ⟨permitAuditWithPeerRelativeSource_core_passes,
    permitAuditWithPeerRelativeSource_not_graphConsistent⟩

theorem exists_representable_corpus_pass_counterexample_to_graphConsistencyP :
    ∃ s : { x : RepresentableAuditSubject //
        RepresentableAuditSubject.Representable x },
      auditCheckConsistencyCore s.1.subject (auditGraphClaims s.1.subject) =
          .ok true ∧
        ¬ GraphConsistencyP (RepresentableAuditSubject.repr s) :=
  ⟨permitAuditWithPeerRelativeSource,
    representable_corpus_pass_counterexample_to_all_profile_consistency⟩

/-- No general theorem can promote the weak-predicate finite-corpus consistency
core into all-profile `GraphConsistencyP`.  The obstruction is not the
strengthened faithful class; it is exactly the missing audit-source weld in the
old `Representable` predicate. -/
theorem no_general_corpus_obstruction_completeness :
    ¬ (∀ s : { x : RepresentableAuditSubject //
        RepresentableAuditSubject.Representable x },
      auditCheckConsistencyCore s.1.subject (auditGraphClaims s.1.subject) =
        .ok true →
        GraphConsistencyP (RepresentableAuditSubject.repr s)) := by
  intro hbridge
  exact permitAuditWithPeerRelativeSource_not_graphConsistent
    (hbridge permitAuditWithPeerRelativeSource
      permitAuditWithPeerRelativeSource_core_passes)

/-! ## Strengthened predicate boundary -/

private def weakFaithfulnessBaselineClaim : AuditGovernanceClaim where
  claimantId := "baseline"
  strength := 1 / 4
  priorityClass := some "represented"
  path := some "/workspace/safe.rs"
  action := some "safe_action"
  content := some "safe content"
  metrics := []

private def weakFaithfulnessStrongerClaim : AuditGovernanceClaim where
  claimantId := "stronger"
  strength := 1 / 2
  priorityClass := some "represented"
  path := some "/workspace/safe.rs"
  action := some "safe_action"
  content := some "safe content"
  metrics := []

private def weakFaithfulnessMismatchClaims : List AuditGovernanceClaim :=
  [weakFaithfulnessBaselineClaim, weakFaithfulnessStrongerClaim]

private def permitOnlyAuditNode : AuditGovernanceNode :=
  AuditGovernanceNode.binary "permit-only" "permit only" []
    AuditDecision.permit AuditGateLogic.firstMatch

private def firstEvalDecision
    (result : Except AuditError (List AuditClaimDecision)) : AuditDecision :=
  match result with
  | .ok (decision :: _) => decision.decision
  | _ => AuditDecision.escalate

private lemma weakFaithfulnessMismatch_claim_ids {j : ClaimantId}
    (h :
      InClaims j
        (auditGovernanceClaimsToClaimQ weakFaithfulnessMismatchClaims)) :
    j = 0 ∨ j = 1 := by
  rcases h with ⟨c, hc, hid⟩
  simp [auditGovernanceClaimsToClaimQ, auditGovernanceClaimToClaimQ,
    weakFaithfulnessMismatchClaims, weakFaithfulnessBaselineClaim,
    weakFaithfulnessStrongerClaim, auditClaimantIdToClaimantId,
    auditClaimantIndexIn, auditClaimantIds, canonicalStrings,
    canonicalInsertString, positiveAuditStrength] at hc
  rcases hc with hc | hc
  · subst c
    simp at hid
    exact Or.inl hid.symm
  · subst c
    simp at hid
    exact Or.inr hid.symm

private lemma weakFaithfulnessMismatch_baseline_weakest :
    DecisionPipeline.WeakestWithStrongerPeer
      (auditGovernanceClaimsToClaimQ weakFaithfulnessMismatchClaims) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · intro j hj
    rcases weakFaithfulnessMismatch_claim_ids hj with rfl | rfl <;>
      native_decide
  · refine ⟨1, ?_, ?_, ?_⟩ <;> native_decide

private lemma representedPeerSource_decides_mismatch_baseline_deny :
    representedPeerSource.decide
        (auditGovernanceClaimsToClaimQ weakFaithfulnessMismatchClaims) 0 =
      BinaryDecision.Deny := by
  have hmatch :
      weakestWithStrongerPeerGate.kind.Matches
        (auditGovernanceClaimsToClaimQ weakFaithfulnessMismatchClaims) 0 := by
    simpa [weakestWithStrongerPeerGate, RepresentableGateKind.Matches]
      using weakFaithfulnessMismatch_baseline_weakest
  have hnode :
      weakestWithStrongerPeerRepresentableNode.decide
          (auditGovernanceClaimsToClaimQ weakFaithfulnessMismatchClaims) 0 =
        BinaryDecision.Deny := by
    rw [RepresentableNode.decide, weakestWithStrongerPeerRepresentableNode]
    exact RepresentableNode.decideGates_cons_of_matches hmatch
  unfold representedPeerSource RepresentableSource.decide
  simp [RepresentableSource.decideNodes, hnode]

private lemma weakFaithfulnessMismatch_claims_valid :
    validateAuditGovernanceClaims weakFaithfulnessMismatchClaims = .ok () := by
  native_decide

private lemma weakFaithfulnessMismatch_baseline_claimant_id :
    auditClaimantIdToClaimantId weakFaithfulnessMismatchClaims "baseline" = 0 := by
  native_decide

private lemma weakFaithfulnessMismatch_decision_profile :
    auditGovernanceClaimsToDecisionProfile weakFaithfulnessMismatchClaims =
      auditGovernanceClaimsToClaimQ weakFaithfulnessMismatchClaims := by
  simp [auditGovernanceClaimsToDecisionProfile,
    auditGovernanceClaimToDecisionClaimQ, auditGovernanceClaimToClaimQ,
    auditGovernanceClaimToClaimantId, auditGovernanceClaimMetadata,
    encodedClaimQId?, encodedClaimQMetadata?,
    auditGovernanceClaimIsDecisionQueryBool,
    auditGovernanceClaimIsDecisionQuery, weakFaithfulnessMismatchClaims,
    weakFaithfulnessBaselineClaim, weakFaithfulnessStrongerClaim,
    auditGovernanceClaimsToClaimQ]

private lemma weakFaithfulnessMismatch_baseline_decision_claimant_id :
    auditGovernanceClaimToClaimantId weakFaithfulnessMismatchClaims
        weakFaithfulnessBaselineClaim = 0 := by
  simp [auditGovernanceClaimToClaimantId, encodedClaimQId?,
    weakFaithfulnessBaselineClaim, weakFaithfulnessMismatch_baseline_claimant_id]

private lemma weakWitness_permit_eval_first :
    firstEvalDecision
        (auditEvaluateNode permitOnlyAuditNode weakFaithfulnessMismatchClaims) =
      AuditDecision.permit := by
  native_decide

private lemma weakWitness_source_faithful_eval_first :
    firstEvalDecision
        ((sourceFaithfulAuditNodeEvaluator representedPeerSource)
          permitOnlyAuditNode weakFaithfulnessMismatchClaims) =
      AuditDecision.deny := by
  unfold sourceFaithfulAuditNodeEvaluator
  change firstEvalDecision
      (do
        validateAuditGovernanceClaims weakFaithfulnessMismatchClaims
        let profile :=
          auditGovernanceClaimsToDecisionProfile weakFaithfulnessMismatchClaims
        Except.ok
          [{ claimantId := "baseline",
             decision :=
              (representedPeerSource.decide
                profile
                (auditGovernanceClaimToClaimantId
                  weakFaithfulnessMismatchClaims
                  weakFaithfulnessBaselineClaim)).toAuditDecision },
           { claimantId := "stronger",
             decision :=
              (representedPeerSource.decide
                profile
                (auditGovernanceClaimToClaimantId
                  weakFaithfulnessMismatchClaims
                  weakFaithfulnessStrongerClaim)).toAuditDecision }]) =
        AuditDecision.deny
  rw [weakFaithfulnessMismatch_claims_valid,
    weakFaithfulnessMismatch_decision_profile,
    weakFaithfulnessMismatch_baseline_decision_claimant_id]
  simp [representedPeerSource_decides_mismatch_baseline_deny]
  rfl

/-- The round-4 weak witness is excluded by the strengthened predicate: its
carried audit evaluator is the permit-only evaluator, not the represented
peer-relative source evaluator. -/
theorem permitAuditWithPeerRelativeSourceSubject_not_faithfulRepresentable :
    ¬ RepresentableAuditSubject.FaithfulRepresentable
      permitAuditWithPeerRelativeSourceSubject := by
  intro hfaithful
  have hfaith := hfaithful.2
  have heval :=
    congrArg
      (fun evalNode =>
        firstEvalDecision
          (evalNode permitOnlyAuditNode weakFaithfulnessMismatchClaims))
      hfaith
  simp [permitAuditWithPeerRelativeSourceSubject, permitOnlyAuditSubject,
    weakWitness_permit_eval_first, weakWitness_source_faithful_eval_first]
    at heval

/-! ## Concrete faithful extracted-graph witness -/

noncomputable def codexHooksFaithfulAuditSubject : AuditSubject where
  graph := codexHooksExtractedGraph.graph
  evalNode := sourceFaithfulAuditNodeEvaluator codexHooksRepresentableSource

noncomputable def codexHooksFaithfulRepresentableSubject :
    RepresentableAuditSubject where
  name := "codex-hooks-source-faithful-representable"
  subject := codexHooksFaithfulAuditSubject
  source := codexHooksRepresentableSource

theorem codexHooksFaithfulRepresentableSubject_faithfulRepresentable :
    RepresentableAuditSubject.FaithfulRepresentable
      codexHooksFaithfulRepresentableSubject := by
  refine ⟨?_, rfl⟩
  simpa [codexHooksFaithfulRepresentableSubject,
    codexHooksFaithfulAuditSubject, codexHooksRepresentedSubject] using
    codexHooksRepresentedSubject_representable

noncomputable def codexHooksFaithfulRepresented :
    { s : RepresentableAuditSubject //
      RepresentableAuditSubject.FaithfulRepresentable s } :=
  ⟨codexHooksFaithfulRepresentableSubject,
    codexHooksFaithfulRepresentableSubject_faithfulRepresentable⟩

theorem codexHooksFaithfulRepresented_repr_eq :
    RepresentableAuditSubject.faithfulRepr codexHooksFaithfulRepresented =
      RepresentableAuditSubject.repr codexHooksRepresented := by
  simp [RepresentableAuditSubject.faithfulRepr,
    RepresentableAuditSubject.repr, codexHooksFaithfulRepresented,
    codexHooksFaithfulRepresentableSubject, codexHooksRepresented,
    codexHooksRepresentedSubject]

private def faithfulPeerAuditGraphData : AuditGovernanceGraph :=
  permitOnlyAuditSubject.graph

noncomputable def faithfulPeerAuditSubject : AuditSubject where
  graph := faithfulPeerAuditGraphData
  evalNode := sourceFaithfulAuditNodeEvaluator representedPeerSource

noncomputable def faithfulPeerRepresentableSubject :
    RepresentableAuditSubject where
  name := "faithful-peer-current-corpus-incomplete"
  subject := faithfulPeerAuditSubject
  source := representedPeerSource

theorem faithfulPeerRepresentableSubject_faithfulRepresentable :
    RepresentableAuditSubject.FaithfulRepresentable
      faithfulPeerRepresentableSubject := by
  refine ⟨?_, rfl⟩
  exact permitAuditWithPeerRelativeSourceSubject_representable

noncomputable def faithfulPeerRepresented :
    { s : RepresentableAuditSubject //
      RepresentableAuditSubject.FaithfulRepresentable s } :=
  ⟨faithfulPeerRepresentableSubject,
    faithfulPeerRepresentableSubject_faithfulRepresentable⟩

theorem faithfulPeerRepresented_repr_eq :
    RepresentableAuditSubject.faithfulRepr faithfulPeerRepresented =
      [weakestWithStrongerPeerNode] := by
  simp [RepresentableAuditSubject.faithfulRepr,
    RepresentableAuditSubject.repr, faithfulPeerRepresented,
    faithfulPeerRepresentableSubject, representedPeerSource,
    RepresentableSource.toGovernanceGraph,
    weakestWithStrongerPeerRepresentableNode_toGovernanceNode]

theorem faithfulPeerRepresented_not_graphConsistent :
    ¬ GraphConsistencyP
      (RepresentableAuditSubject.faithfulRepr faithfulPeerRepresented) := by
  simpa [faithfulPeerRepresented_repr_eq, representedPeer_repr_eq]
    using representedPeer_not_graphConsistent

private theorem faithfulPeer_auditGraphClaims_eq :
    auditGraphClaims faithfulPeerAuditSubject = [baselineClaim []] := by
  simp [auditGraphClaims, faithfulPeerAuditSubject,
    faithfulPeerAuditGraphData, permitOnlyAuditSubject,
    syntheticClaimsForNodes, syntheticClaimsCoreForNodes,
    syntheticClaimsCoreForOrderedNodeIds, graphNodeIds, graphNodeTable,
    canonicalNodes, canonicalInsertNode, AuditGovernanceNode.id,
    canonicalStrings, canonicalInsertString, allMetricFieldsForNodes,
    collectedMetricFieldsForNodes, binaryNodeById?,
    findGovernanceNodeById?, AuditGovernanceNode.binaryGates?,
    gateClaimsForBinaryNode, gateClaimsForBinaryNodeFrom,
    canonicalClaims, canonicalInsertClaim, baselineClaim]

private lemma permitOnly_traverse_empty
    (eval : AuditNodeEvaluator)
    (h : eval permitOnlyAuditNode [] = .ok []) :
    traverseOrder eval faithfulPeerAuditGraphData ["permit-only"]
        { queuedClaims := [("permit-only", [])],
          nodeDecisions := [], finalDecisions := [] } =
      Except.ok (AuditTraversalState.mk []
        [("permit-only", [])] []) := by
  change eval
      (.binary "permit-only" "permit only" [] .permit .firstMatch) [] =
    .ok [] at h
  unfold traverseOrder faithfulPeerAuditGraphData permitOnlyAuditSubject
  simp [AuditGovernanceNode.id, canonicalNodeById?, graphNodeTable,
    canonicalNodes, canonicalInsertNode, findGovernanceNodeById?,
    removeQueuedClaims]
  change (eval (.binary "permit-only" "permit only" [] .permit .firstMatch)
      [] >>= fun decisions =>
        propagateEdges [] [] (forwardedClaims [] decisions) decisions >>=
          fun propagatedQueue =>
            traverseOrder eval
              { nodes := [.binary "permit-only" "permit only" [] .permit
                  .firstMatch], edges := [] } []
              { queuedClaims := propagatedQueue,
                nodeDecisions := insertNodeDecisions "permit-only" decisions [],
                finalDecisions := recordFinalDecisions [] decisions false }) =
    Except.ok (AuditTraversalState.mk [] [("permit-only", [])] [])
  rw [h]
  rfl

private lemma permitOnly_traverse_singleton_permit
    (eval : AuditNodeEvaluator)
    (h : eval permitOnlyAuditNode [baselineClaim []] =
      .ok [{ claimantId := "baseline", decision := .permit }]) :
    traverseOrder eval faithfulPeerAuditGraphData ["permit-only"]
        { queuedClaims := [("permit-only", [baselineClaim []])],
          nodeDecisions := [], finalDecisions := [] } =
      Except.ok (AuditTraversalState.mk []
        [("permit-only",
          [AuditClaimDecision.mk "baseline" .permit])]
        [("baseline", .permit)]) := by
  change eval
      (.binary "permit-only" "permit only" [] .permit .firstMatch)
        [baselineClaim []] =
    .ok [{ claimantId := "baseline", decision := .permit }] at h
  unfold traverseOrder faithfulPeerAuditGraphData permitOnlyAuditSubject
  simp [AuditGovernanceNode.id, canonicalNodeById?, graphNodeTable,
    canonicalNodes, canonicalInsertNode, findGovernanceNodeById?,
    removeQueuedClaims]
  change (eval (.binary "permit-only" "permit only" [] .permit .firstMatch)
      [baselineClaim []] >>= fun decisions =>
        propagateEdges [] [] (forwardedClaims [baselineClaim []] decisions)
            decisions >>= fun propagatedQueue =>
          traverseOrder eval
            { nodes := [.binary "permit-only" "permit only" [] .permit
                .firstMatch], edges := [] } []
            { queuedClaims := propagatedQueue,
              nodeDecisions := insertNodeDecisions "permit-only" decisions [],
              finalDecisions := recordFinalDecisions [] decisions false }) =
    Except.ok (AuditTraversalState.mk []
      [("permit-only",
        [AuditClaimDecision.mk "baseline" .permit])]
      [("baseline", .permit)])
  rw [h]
  rfl

private lemma permitOnly_traverse_singleton_deny
    (eval : AuditNodeEvaluator)
    (h : eval permitOnlyAuditNode [baselineClaim []] =
      .ok [{ claimantId := "baseline", decision := .deny }]) :
    traverseOrder eval faithfulPeerAuditGraphData ["permit-only"]
        { queuedClaims := [("permit-only", [baselineClaim []])],
          nodeDecisions := [], finalDecisions := [] } =
      Except.ok (AuditTraversalState.mk []
        [("permit-only",
          [AuditClaimDecision.mk "baseline" .deny])]
        [("baseline", .deny)]) := by
  change eval
      (.binary "permit-only" "permit only" [] .permit .firstMatch)
        [baselineClaim []] =
    .ok [{ claimantId := "baseline", decision := .deny }] at h
  unfold traverseOrder faithfulPeerAuditGraphData permitOnlyAuditSubject
  simp [AuditGovernanceNode.id, canonicalNodeById?, graphNodeTable,
    canonicalNodes, canonicalInsertNode, findGovernanceNodeById?,
    removeQueuedClaims]
  change (eval (.binary "permit-only" "permit only" [] .permit .firstMatch)
      [baselineClaim []] >>= fun decisions =>
        propagateEdges [] [] (forwardedClaims [baselineClaim []] decisions)
            decisions >>= fun propagatedQueue =>
          traverseOrder eval
            { nodes := [.binary "permit-only" "permit only" [] .permit
                .firstMatch], edges := [] } []
            { queuedClaims := propagatedQueue,
              nodeDecisions := insertNodeDecisions "permit-only" decisions [],
              finalDecisions := recordFinalDecisions [] decisions false }) =
    Except.ok (AuditTraversalState.mk []
      [("permit-only",
        [AuditClaimDecision.mk "baseline" .deny])]
      [("baseline", .deny)])
  rw [h]
  rfl

private lemma faithfulPeer_eval_empty :
    faithfulPeerAuditSubject.evalNode permitOnlyAuditNode [] = .ok [] := by
  rfl

private lemma faithfulPeer_baseline_claim_valid :
    validateAuditGovernanceClaims [baselineClaim []] = .ok () := by
  native_decide

private lemma faithfulPeer_baseline_claimant_id :
    auditClaimantIdToClaimantId [baselineClaim []] "baseline" = 0 := by
  native_decide

private lemma faithfulPeer_baseline_decision_profile :
    auditGovernanceClaimsToDecisionProfile [baselineClaim []] =
      auditGovernanceClaimsToClaimQ [baselineClaim []] := by
  simp [auditGovernanceClaimsToDecisionProfile,
    auditGovernanceClaimToDecisionClaimQ, auditGovernanceClaimToClaimQ,
    auditGovernanceClaimToClaimantId, auditGovernanceClaimMetadata,
    encodedClaimQId?, encodedClaimQMetadata?,
    auditGovernanceClaimIsDecisionQueryBool,
    auditGovernanceClaimIsDecisionQuery, baselineClaim,
    auditGovernanceClaimsToClaimQ, canonicalMetrics]

private lemma faithfulPeer_baseline_decision_claimant_id :
    auditGovernanceClaimToClaimantId [baselineClaim []] (baselineClaim []) =
      0 := by
  simp [auditGovernanceClaimToClaimantId, encodedClaimQId?, baselineClaim,
    canonicalMetrics, auditClaimantIdToClaimantId, auditClaimantIndexIn,
    auditClaimantIds, canonicalStrings, canonicalInsertString]

private lemma faithfulPeer_eval_singleton_of_permit
    (h :
      representedPeerSource.decide
          (auditGovernanceClaimsToClaimQ [baselineClaim []]) 0 =
        BinaryDecision.Permit) :
    faithfulPeerAuditSubject.evalNode permitOnlyAuditNode
        [baselineClaim []] =
      .ok [AuditClaimDecision.mk "baseline" .permit] := by
  unfold faithfulPeerAuditSubject sourceFaithfulAuditNodeEvaluator
  change
    (do
      validateAuditGovernanceClaims [baselineClaim []]
      let profile := auditGovernanceClaimsToDecisionProfile [baselineClaim []]
      Except.ok
        [AuditClaimDecision.mk "baseline"
          (representedPeerSource.decide
            profile
            (auditGovernanceClaimToClaimantId [baselineClaim []]
              (baselineClaim []))).toAuditDecision]) =
      .ok [AuditClaimDecision.mk "baseline" .permit]
  rw [faithfulPeer_baseline_claim_valid,
    faithfulPeer_baseline_decision_profile,
    faithfulPeer_baseline_decision_claimant_id]
  simp [h]
  rfl

private lemma faithfulPeer_eval_singleton_of_deny
    (h :
      representedPeerSource.decide
          (auditGovernanceClaimsToClaimQ [baselineClaim []]) 0 =
        BinaryDecision.Deny) :
    faithfulPeerAuditSubject.evalNode permitOnlyAuditNode
        [baselineClaim []] =
      .ok [AuditClaimDecision.mk "baseline" .deny] := by
  unfold faithfulPeerAuditSubject sourceFaithfulAuditNodeEvaluator
  change
    (do
      validateAuditGovernanceClaims [baselineClaim []]
      let profile := auditGovernanceClaimsToDecisionProfile [baselineClaim []]
      Except.ok
        [AuditClaimDecision.mk "baseline"
          (representedPeerSource.decide
            profile
            (auditGovernanceClaimToClaimantId [baselineClaim []]
              (baselineClaim []))).toAuditDecision]) =
      .ok [AuditClaimDecision.mk "baseline" .deny]
  rw [faithfulPeer_baseline_claim_valid,
    faithfulPeer_baseline_decision_profile,
    faithfulPeer_baseline_decision_claimant_id]
  simp [h]
  rfl

private lemma faithfulPeer_eval_singleton :
    ∃ decision,
      faithfulPeerAuditSubject.evalNode permitOnlyAuditNode
          [baselineClaim []] =
        .ok [AuditClaimDecision.mk "baseline" decision] := by
  cases h :
      representedPeerSource.decide
        (auditGovernanceClaimsToClaimQ [baselineClaim []]) 0
  · exact ⟨AuditDecision.permit, faithfulPeer_eval_singleton_of_permit h⟩
  · exact ⟨AuditDecision.deny, faithfulPeer_eval_singleton_of_deny h⟩

private theorem faithfulPeer_auditFinalDecisions_empty :
    auditFinalDecisions faithfulPeerAuditSubject [] = .ok [] := by
  unfold auditFinalDecisions traverseAcyclic faithfulPeerAuditSubject
    faithfulPeerAuditGraphData permitOnlyAuditSubject
  have htraverse :=
    permitOnly_traverse_empty
      (sourceFaithfulAuditNodeEvaluator representedPeerSource)
      faithfulPeer_eval_empty
  rw [show validateAuditGovernanceClaims [] = .ok () by rfl]
  simp [graphNodeIds, graphNodeTable, canonicalNodes, canonicalInsertNode,
    AuditGovernanceNode.id, entryNodes, incomingCountWithin,
    topologicalOrder, topologicalOrderAux, firstReadyNode?,
    firstReadyNodeScan, removeNodeId, seedQueuedClaims,
    insertQueuedClaims]
  change ((fun a => a.finalDecisions) <$>
      traverseOrder (sourceFaithfulAuditNodeEvaluator representedPeerSource)
        faithfulPeerAuditGraphData ["permit-only"]
        { queuedClaims := [("permit-only", [])],
          nodeDecisions := [], finalDecisions := [] }) = .ok []
  rw [htraverse]
  rfl

private theorem faithfulPeer_auditFinalDecisions_singleton :
    ∃ decision,
      auditFinalDecisions faithfulPeerAuditSubject [baselineClaim []] =
        .ok [("baseline", decision)] := by
  cases h :
      representedPeerSource.decide
        (auditGovernanceClaimsToClaimQ [baselineClaim []]) 0
  · refine ⟨AuditDecision.permit, ?_⟩
    have heval :
        faithfulPeerAuditSubject.evalNode permitOnlyAuditNode
            [baselineClaim []] =
          .ok [AuditClaimDecision.mk "baseline" .permit] :=
      faithfulPeer_eval_singleton_of_permit h
    unfold auditFinalDecisions traverseAcyclic faithfulPeerAuditSubject
      faithfulPeerAuditGraphData permitOnlyAuditSubject
    have htraverse :=
      permitOnly_traverse_singleton_permit
        (sourceFaithfulAuditNodeEvaluator representedPeerSource) heval
    rw [faithfulPeer_baseline_claim_valid]
    simp [graphNodeIds, graphNodeTable, canonicalNodes, canonicalInsertNode,
      AuditGovernanceNode.id, entryNodes, incomingCountWithin,
      topologicalOrder, topologicalOrderAux, firstReadyNode?,
      firstReadyNodeScan, removeNodeId, seedQueuedClaims,
      insertQueuedClaims]
    change ((fun a => a.finalDecisions) <$>
        traverseOrder (sourceFaithfulAuditNodeEvaluator representedPeerSource)
          faithfulPeerAuditGraphData ["permit-only"]
          { queuedClaims := [("permit-only", [baselineClaim []])],
            nodeDecisions := [], finalDecisions := [] }) =
      .ok [("baseline", AuditDecision.permit)]
    rw [htraverse]
    rfl
  · refine ⟨AuditDecision.deny, ?_⟩
    have heval :
        faithfulPeerAuditSubject.evalNode permitOnlyAuditNode
            [baselineClaim []] =
          .ok [AuditClaimDecision.mk "baseline" .deny] :=
      faithfulPeer_eval_singleton_of_deny h
    unfold auditFinalDecisions traverseAcyclic faithfulPeerAuditSubject
      faithfulPeerAuditGraphData permitOnlyAuditSubject
    have htraverse :=
      permitOnly_traverse_singleton_deny
        (sourceFaithfulAuditNodeEvaluator representedPeerSource) heval
    rw [faithfulPeer_baseline_claim_valid]
    simp [graphNodeIds, graphNodeTable, canonicalNodes, canonicalInsertNode,
      AuditGovernanceNode.id, entryNodes, incomingCountWithin,
      topologicalOrder, topologicalOrderAux, firstReadyNode?,
      firstReadyNodeScan, removeNodeId, seedQueuedClaims,
      insertQueuedClaims]
    change ((fun a => a.finalDecisions) <$>
        traverseOrder (sourceFaithfulAuditNodeEvaluator representedPeerSource)
          faithfulPeerAuditGraphData ["permit-only"]
          { queuedClaims := [("permit-only", [baselineClaim []])],
            nodeDecisions := [], finalDecisions := [] }) =
      .ok [("baseline", AuditDecision.deny)]
    rw [htraverse]
    rfl

theorem faithfulPeer_current_corpus_consistencyCore_passes :
    auditCheckConsistencyCore faithfulPeerRepresented.1.subject
        (auditGraphClaims faithfulPeerRepresented.1.subject) =
      .ok true := by
  change auditCheckConsistencyCore faithfulPeerAuditSubject
      (auditGraphClaims faithfulPeerAuditSubject) = .ok true
  rw [faithfulPeer_auditGraphClaims_eq]
  rcases faithfulPeer_auditFinalDecisions_singleton with
    ⟨decision, horiginal⟩
  unfold auditCheckConsistencyCore
  rw [horiginal]
  simp [faithfulPeer_auditFinalDecisions_empty, auditRemoveClaim,
    baselineClaim]
  rfl

/-- Honest round-5 boundary: after excluding the unfaithful weak witness, the
current production corpus is still not obstruction-complete for faithful
representable subjects.  The evaluator is source-faithful, but the production
corpus generated from the audit graph is only the baseline singleton, so the
peer-relative removal obstruction is not exercised. -/
theorem faithful_representable_current_corpus_incompleteness :
    ∃ s : { x : RepresentableAuditSubject //
        RepresentableAuditSubject.FaithfulRepresentable x },
      auditCheckConsistencyCore s.1.subject (auditGraphClaims s.1.subject) =
          .ok true ∧
        ¬ GraphConsistencyP
          (RepresentableAuditSubject.faithfulRepr s) :=
  ⟨faithfulPeerRepresented,
    faithfulPeer_current_corpus_consistencyCore_passes,
    faithfulPeerRepresented_not_graphConsistent⟩

theorem no_general_faithful_current_corpus_obstruction_completeness :
    ¬ (∀ s : { x : RepresentableAuditSubject //
        RepresentableAuditSubject.FaithfulRepresentable x },
      auditCheckConsistencyCore s.1.subject (auditGraphClaims s.1.subject) =
        .ok true →
        GraphConsistencyP (RepresentableAuditSubject.faithfulRepr s)) := by
  intro hbridge
  exact faithfulPeerRepresented_not_graphConsistent
    (hbridge faithfulPeerRepresented
      faithfulPeer_current_corpus_consistencyCore_passes)

/-- Calibrated executable-self-certification limit.  For the current finite
executable consistency self-audit, namely `auditCheckConsistencyCore` run on
the shape-derived production corpus `auditGraphClaims`, there is a faithful
represented subject whose executable self-check passes while its all-profile
represented graph violates `GraphConsistencyP`; consequently this current
shape-derived self-certification is strictly weaker than all-profile graph
consistency unless an additional corpus-completeness/representation theorem is
supplied.  The mechanism is specific: `auditGraphClaims` is generated from the
audit graph's shape, while the obstruction is profile-relational.  This theorem
does not claim that every possible finite executable self-audit is incapable of
obstruction completeness. -/
theorem faithful_shape_derived_self_certification_strictly_weaker_than_all_profile_consistency :
    (∃ s : { x : RepresentableAuditSubject //
        RepresentableAuditSubject.FaithfulRepresentable x },
      auditCheckConsistencyCore s.1.subject (auditGraphClaims s.1.subject) =
          .ok true ∧
        ¬ GraphConsistencyP
          (RepresentableAuditSubject.faithfulRepr s)) ∧
      ¬ (∀ s : { x : RepresentableAuditSubject //
          RepresentableAuditSubject.FaithfulRepresentable x },
        auditCheckConsistencyCore s.1.subject (auditGraphClaims s.1.subject) =
          .ok true →
          GraphConsistencyP (RepresentableAuditSubject.faithfulRepr s)) :=
  ⟨faithful_representable_current_corpus_incompleteness,
    no_general_faithful_current_corpus_obstruction_completeness⟩

end Legitimacy
