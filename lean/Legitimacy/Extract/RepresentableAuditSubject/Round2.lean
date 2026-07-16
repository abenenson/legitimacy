/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.RepresentableAuditSubject
import Legitimacy.Results.CodexAdmissibilityAudit

/-!
# Round-2 representable audit-subject welds

This module carries the round-2 strengthening for
`Legitimacy.Extract.RepresentableAuditSubject`: the represented-peer graph
obstruction is welded to the carried `AuditSubject.evalNode`, and the showcased
Codex hooks harness is represented under the explicit scarce-allocation binary
projection for three-valued audit decisions.
-/

set_option autoImplicit false

namespace Legitimacy

/-! ### Causal weld from represented graph decisions to the carried audit subject -/

private def representedPeerGraphBaselineClaim : ClaimQ :=
  ⟨0, 1 / 4, by norm_num, []⟩

private def representedPeerGraphGate0Claim : ClaimQ :=
  ⟨1, 1 / 2, by norm_num, []⟩

private def representedPeerGraphGate1Claim : ClaimQ :=
  ⟨2, 3 / 4, by norm_num, []⟩

private def representedPeerGraphGate2Claim : ClaimQ :=
  ⟨3, 1, by norm_num, []⟩

private def representedPeerConsistencyGraphClaims : List ClaimQ :=
  [ representedPeerGraphBaselineClaim
  , representedPeerGraphGate0Claim
  , representedPeerGraphGate1Claim
  , representedPeerGraphGate2Claim
  ]

private def representedPeerConsistencyGraphClaimsWithoutBaseline :
    List ClaimQ :=
  [ representedPeerGraphGate0Claim
  , representedPeerGraphGate1Claim
  , representedPeerGraphGate2Claim
  ]

/-- A concrete graph-consistency obstruction for one represented graph profile.
It records both the graph-side consistency premises and the exact before/after
binary decisions needed by the audit bridge. -/
structure GraphConsistencyObstructionAt
    (graph : GovernanceGraph) (claims : List ClaimQ)
    (denied survivor : ClaimantId) : Prop where
  denied_in_claims : InClaims denied claims
  survivor_in_claims : InClaims survivor claims
  distinct_claimants : denied ≠ survivor
  claims_distinct : ClaimsDistinct claims
  denied_decision :
    graphDecide graph claims denied = BinaryDecision.Deny
  survivor_before :
    graphDecide graph claims survivor = BinaryDecision.Permit
  survivor_after :
    graphDecide graph (removeClaimGraph denied claims) survivor =
      BinaryDecision.Deny

namespace GraphConsistencyObstructionAt

theorem decision_changed
    {graph : GovernanceGraph} {claims : List ClaimQ}
    {denied survivor : ClaimantId}
    (witness : GraphConsistencyObstructionAt graph claims denied survivor) :
    graphDecide graph claims survivor ≠
      graphDecide graph (removeClaimGraph denied claims) survivor := by
  rw [witness.survivor_before, witness.survivor_after]
  exact BinaryDecision.noConfusion

theorem not_consistent
    {graph : GovernanceGraph} {claims : List ClaimQ}
    {denied survivor : ClaimantId}
    (witness : GraphConsistencyObstructionAt graph claims denied survivor) :
    ¬ GraphConsistencyP graph := by
  intro hconsistent
  exact witness.decision_changed
    (hconsistent claims denied survivor witness.denied_in_claims
      witness.survivor_in_claims witness.distinct_claimants
      witness.claims_distinct witness.denied_decision)

end GraphConsistencyObstructionAt

private theorem representedPeer_remove_baseline_graph_claims :
    removeClaimGraph 0 representedPeerConsistencyGraphClaims =
      representedPeerConsistencyGraphClaimsWithoutBaseline := by
  native_decide

private theorem representedPeer_graph_baseline_denied :
    graphDecide (RepresentableAuditSubject.repr representedPeer)
        representedPeerConsistencyGraphClaims 0 =
      BinaryDecision.Deny := by
  have hweak :
      DecisionPipeline.WeakestWithStrongerPeer
        representedPeerConsistencyGraphClaims 0 := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨representedPeerGraphBaselineClaim,
        by simp [representedPeerConsistencyGraphClaims], rfl⟩
    · intro j hj
      rcases hj with ⟨c, hc, hid⟩
      simp [representedPeerConsistencyGraphClaims] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · simp [representedPeerGraphBaselineClaim] at hid
        subst j
        norm_num [lookupStrength, representedPeerConsistencyGraphClaims,
          representedPeerGraphBaselineClaim, representedPeerGraphGate0Claim,
          representedPeerGraphGate1Claim, representedPeerGraphGate2Claim]
      · simp [representedPeerGraphGate0Claim] at hid
        subst j
        norm_num [lookupStrength, representedPeerConsistencyGraphClaims,
          representedPeerGraphBaselineClaim, representedPeerGraphGate0Claim,
          representedPeerGraphGate1Claim, representedPeerGraphGate2Claim]
      · simp [representedPeerGraphGate1Claim] at hid
        subst j
        norm_num [lookupStrength, representedPeerConsistencyGraphClaims,
          representedPeerGraphBaselineClaim, representedPeerGraphGate0Claim,
          representedPeerGraphGate1Claim, representedPeerGraphGate2Claim]
      · simp [representedPeerGraphGate2Claim] at hid
        subst j
        norm_num [lookupStrength, representedPeerConsistencyGraphClaims,
          representedPeerGraphBaselineClaim, representedPeerGraphGate0Claim,
          representedPeerGraphGate1Claim, representedPeerGraphGate2Claim]
    · refine ⟨1, ?_, ?_, ?_⟩
      · decide
      · exact ⟨representedPeerGraphGate0Claim,
          by simp [representedPeerConsistencyGraphClaims], rfl⟩
      · norm_num [lookupStrength, representedPeerConsistencyGraphClaims,
          representedPeerGraphBaselineClaim, representedPeerGraphGate0Claim,
          representedPeerGraphGate1Claim, representedPeerGraphGate2Claim]
  rw [representedPeer_repr_eq]
  simp [graphDecide, weakestWithStrongerPeerNode_of_weakest hweak]

private theorem representedPeer_graph_gate0_permitted_before_removal :
    graphDecide (RepresentableAuditSubject.repr representedPeer)
        representedPeerConsistencyGraphClaims 1 =
      BinaryDecision.Permit := by
  have hnot :
      ¬ DecisionPipeline.WeakestWithStrongerPeer
        representedPeerConsistencyGraphClaims 1 := by
    intro hweak
    have hbase : InClaims 0 representedPeerConsistencyGraphClaims :=
      ⟨representedPeerGraphBaselineClaim,
        by simp [representedPeerConsistencyGraphClaims], rfl⟩
    have hle := hweak.2.1 0 hbase
    norm_num [lookupStrength, representedPeerConsistencyGraphClaims,
      representedPeerGraphBaselineClaim, representedPeerGraphGate0Claim,
      representedPeerGraphGate1Claim, representedPeerGraphGate2Claim] at hle
  rw [representedPeer_repr_eq]
  simp [graphDecide, weakestWithStrongerPeerNode_of_not_weakest hnot]

private theorem representedPeer_graph_gate0_denied_after_baseline_removal :
    graphDecide (RepresentableAuditSubject.repr representedPeer)
        (removeClaimGraph 0 representedPeerConsistencyGraphClaims) 1 =
      BinaryDecision.Deny := by
  have hweak :
      DecisionPipeline.WeakestWithStrongerPeer
        representedPeerConsistencyGraphClaimsWithoutBaseline 1 := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨representedPeerGraphGate0Claim,
        by simp [representedPeerConsistencyGraphClaimsWithoutBaseline], rfl⟩
    · intro j hj
      rcases hj with ⟨c, hc, hid⟩
      simp [representedPeerConsistencyGraphClaimsWithoutBaseline] at hc
      rcases hc with rfl | rfl | rfl
      · simp [representedPeerGraphGate0Claim] at hid
        subst j
        norm_num [lookupStrength,
          representedPeerConsistencyGraphClaimsWithoutBaseline,
          representedPeerGraphGate0Claim, representedPeerGraphGate1Claim,
          representedPeerGraphGate2Claim]
      · simp [representedPeerGraphGate1Claim] at hid
        subst j
        norm_num [lookupStrength,
          representedPeerConsistencyGraphClaimsWithoutBaseline,
          representedPeerGraphGate0Claim, representedPeerGraphGate1Claim,
          representedPeerGraphGate2Claim]
      · simp [representedPeerGraphGate2Claim] at hid
        subst j
        norm_num [lookupStrength,
          representedPeerConsistencyGraphClaimsWithoutBaseline,
          representedPeerGraphGate0Claim, representedPeerGraphGate1Claim,
          representedPeerGraphGate2Claim]
    · refine ⟨2, ?_, ?_, ?_⟩
      · decide
      · exact ⟨representedPeerGraphGate1Claim,
          by simp [representedPeerConsistencyGraphClaimsWithoutBaseline], rfl⟩
      · norm_num [lookupStrength,
          representedPeerConsistencyGraphClaimsWithoutBaseline,
          representedPeerGraphGate0Claim, representedPeerGraphGate1Claim,
          representedPeerGraphGate2Claim]
  rw [representedPeer_remove_baseline_graph_claims, representedPeer_repr_eq]
  simp [graphDecide, weakestWithStrongerPeerNode_of_weakest hweak]

/-- Concrete graph-side consistency obstruction carried by
`representedPeer_obstructs_diagnostics`: the represented graph denies the
baseline claimant, and removing that denied claimant changes gate-0 from permit
to deny.  This exact witness is the load-bearing input to the audit bridge
below. -/
theorem representedPeer_graph_consistency_obstruction_witness :
    GraphConsistencyObstructionAt
      (RepresentableAuditSubject.repr representedPeer)
      representedPeerConsistencyGraphClaims 0 1 where
  denied_in_claims := by native_decide
  survivor_in_claims := by native_decide
  distinct_claimants := by native_decide
  claims_distinct := by
    unfold ClaimsDistinct representedPeerConsistencyGraphClaims
      representedPeerGraphBaselineClaim representedPeerGraphGate0Claim
      representedPeerGraphGate1Claim representedPeerGraphGate2Claim
    show ([0, 1, 2, 3] : List Nat).Nodup
    decide
  denied_decision := representedPeer_graph_baseline_denied
  survivor_before := representedPeer_graph_gate0_permitted_before_removal
  survivor_after := representedPeer_graph_gate0_denied_after_baseline_removal

/-- Existential all-profile counterexample recovered from the exact witness.
This preserves the round-2 graph-obstruction surface while the certificate
weld consumes the exact witness above. -/
theorem representedPeer_graph_consistency_obstruction_exists :
    ∃ claims k j,
      InClaims k claims ∧
        InClaims j claims ∧
          k ≠ j ∧
            ClaimsDistinct claims ∧
              graphDecide (RepresentableAuditSubject.repr representedPeer)
                  claims k = BinaryDecision.Deny ∧
                graphDecide (RepresentableAuditSubject.repr representedPeer)
                    claims j ≠
                  graphDecide (RepresentableAuditSubject.repr representedPeer)
                    (removeClaimGraph k claims) j := by
  let witness := representedPeer_graph_consistency_obstruction_witness
  exact
    ⟨representedPeerConsistencyGraphClaims, 0, 1,
      witness.denied_in_claims, witness.survivor_in_claims,
      witness.distinct_claimants, witness.claims_distinct,
      witness.denied_decision, witness.decision_changed⟩

private def representedPeerAuditConsistencyClaims :
    List AuditGovernanceClaim :=
  auditGraphClaims representedPeerAuditSubject

private def representedPeerAuditConsistencyClaimsWithoutBaseline :
    List AuditGovernanceClaim :=
  auditRemoveClaim "baseline" representedPeerAuditConsistencyClaims

private def representedPeerAuditBaselineClaim : AuditGovernanceClaim where
  claimantId := "baseline"
  strength := 1
  priorityClass := some "extracted"
  path := some "/workspace/safe.rs"
  action := some "safe_action"
  content := some "safe content"
  metrics := [("peer_relative_rank", 0)]

private def representedPeerAuditGate0Claim : AuditGovernanceClaim where
  claimantId := "represented-peer-source-gate-0"
  strength := 1
  priorityClass := some "extracted"
  path := some "/workspace/safe.rs"
  action := some "safe_action"
  content := some "safe content"
  metrics := [("peer_relative_rank", 1 / 2), ("permit_signal", 1)]

private def representedPeerAuditGate1Claim : AuditGovernanceClaim where
  claimantId := "represented-peer-source-gate-1"
  strength := 21 / 20
  priorityClass := some "extracted"
  path := some "/workspace/safe.rs"
  action := some "safe_action"
  content := some "safe content"
  metrics := [("peer_relative_rank", 3 / 4), ("permit_signal", 1)]

private def representedPeerAuditGate2Claim : AuditGovernanceClaim where
  claimantId := "represented-peer-source-gate-2"
  strength := 11 / 10
  priorityClass := some "extracted"
  path := some "/workspace/safe.rs"
  action := some "safe_action"
  content := some "safe content"
  metrics := [("peer_relative_rank", 1), ("permit_signal", 1)]

private def representedPeerAuditConsistencyClaimsConcrete :
    List AuditGovernanceClaim :=
  [ representedPeerAuditBaselineClaim
  , representedPeerAuditGate0Claim
  , representedPeerAuditGate1Claim
  , representedPeerAuditGate2Claim
  ]

private def representedPeerAuditConsistencyClaimsWithoutBaselineConcrete :
    List AuditGovernanceClaim :=
  [ representedPeerAuditGate0Claim
  , representedPeerAuditGate1Claim
  , representedPeerAuditGate2Claim
  ]

private theorem representedPeerAuditConsistencyClaims_eq :
    representedPeerAuditConsistencyClaims =
      representedPeerAuditConsistencyClaimsConcrete := by
  native_decide

private theorem representedPeerAuditConsistencyClaimsWithoutBaseline_eq :
    representedPeerAuditConsistencyClaimsWithoutBaseline =
      representedPeerAuditConsistencyClaimsWithoutBaselineConcrete := by
  native_decide

private theorem representedPeerAuditRemoveBaselineConcrete :
    auditRemoveClaim representedPeerAuditBaselineClaim.claimantId
        representedPeerAuditConsistencyClaimsConcrete =
      representedPeerAuditConsistencyClaimsWithoutBaselineConcrete := by
  native_decide

private theorem representedPeerAuditSubject_no_cycles :
    detectAuditCycles representedPeerAuditSubject.graph = [] := by
  native_decide

private def representedPeerAuditOriginalFinalDecisions :
    List (AuditClaimantId × AuditDecision) :=
  [ ("baseline", AuditDecision.deny)
  , ("represented-peer-source-gate-0", AuditDecision.permit)
  , ("represented-peer-source-gate-1", AuditDecision.permit)
  , ("represented-peer-source-gate-2", AuditDecision.permit)
  ]

private def representedPeerAuditWithoutBaselineFinalDecisions :
    List (AuditClaimantId × AuditDecision) :=
  [ ("represented-peer-source-gate-0", AuditDecision.deny)
  , ("represented-peer-source-gate-1", AuditDecision.permit)
  , ("represented-peer-source-gate-2", AuditDecision.permit)
  ]

/-- Bridge data tying the represented graph witness to the production
dispatcher traces over the finite audit corpus.  The final-decision fields are
what the consistency loop consumes; the projected fields identify those traces
with the graph decisions carried by the obstruction witness. -/
structure RepresentedPeerConsistencyBridge
    (witness :
      GraphConsistencyObstructionAt
        (RepresentableAuditSubject.repr representedPeer)
        representedPeerConsistencyGraphClaims 0 1) : Prop where
  original_finals :
    auditFinalDecisions representedPeerAuditSubject
        representedPeerAuditConsistencyClaims =
      .ok representedPeerAuditOriginalFinalDecisions
  without_baseline_finals :
    auditFinalDecisions representedPeerAuditSubject
        representedPeerAuditConsistencyClaimsWithoutBaseline =
      .ok representedPeerAuditWithoutBaselineFinalDecisions
  baseline_projected :
    auditProjectedFinalDecision? representedPeerAuditSubject
        representedPeerAuditConsistencyClaims "baseline" =
      .ok (some
        (graphDecide (RepresentableAuditSubject.repr representedPeer)
          representedPeerConsistencyGraphClaims 0))
  survivor_before_projected :
    auditProjectedFinalDecision? representedPeerAuditSubject
        representedPeerAuditConsistencyClaims
        "represented-peer-source-gate-0" =
      .ok (some
        (graphDecide (RepresentableAuditSubject.repr representedPeer)
          representedPeerConsistencyGraphClaims 1))
  survivor_after_projected :
    auditProjectedFinalDecision? representedPeerAuditSubject
        representedPeerAuditConsistencyClaimsWithoutBaseline
        "represented-peer-source-gate-0" =
      .ok (some
        (graphDecide (RepresentableAuditSubject.repr representedPeer)
          (removeClaimGraph 0 representedPeerConsistencyGraphClaims) 1))

/-- Obstruction-relevant evalNode/repr weld for the carried
`representedPeerAuditSubject`.  The universal consistency theorem above is over
`ClaimQ`; this theorem pins the finite production dispatcher profile to that
same graph witness after the explicit audit-decision binary projection. -/
theorem representedPeer_evalNode_matches_repr_on_consistency_witness :
    (witness :
      GraphConsistencyObstructionAt
        (RepresentableAuditSubject.repr representedPeer)
        representedPeerConsistencyGraphClaims 0 1) →
    RepresentedPeerConsistencyBridge witness := by
  intro witness
  refine
    { original_finals := ?_
      without_baseline_finals := ?_
      baseline_projected := ?_
      survivor_before_projected := ?_
      survivor_after_projected := ?_ }
  · native_decide
  · native_decide
  · rw [witness.denied_decision]
    native_decide
  · rw [witness.survivor_before]
    native_decide
  · rw [witness.survivor_after]
    native_decide

/-- The graph obstruction and evalNode/repr bridge yield the concrete audit
consistency failure used by the production certificate refutation. -/
private theorem representedPeer_consistency_check_failed_of_obstruction
    (witness :
      GraphConsistencyObstructionAt
        (RepresentableAuditSubject.repr representedPeer)
        representedPeerConsistencyGraphClaims 0 1)
    (bridge : RepresentedPeerConsistencyBridge witness) :
    auditCheckStatus representedPeerAuditSubject AuditCheck.consistency =
      .ok .failed := by
  have graphNotConsistent :
      ¬ GraphConsistencyP
        (RepresentableAuditSubject.repr representedPeer) :=
    witness.not_consistent
  have projectedBaseline :
      auditProjectedFinalDecision? representedPeerAuditSubject
          representedPeerAuditConsistencyClaims "baseline" =
        .ok (some BinaryDecision.Deny) := by
    simpa [witness.denied_decision] using bridge.baseline_projected
  have projectedSurvivorBefore :
      auditProjectedFinalDecision? representedPeerAuditSubject
          representedPeerAuditConsistencyClaims
          "represented-peer-source-gate-0" =
        .ok (some BinaryDecision.Permit) := by
    simpa [witness.survivor_before] using bridge.survivor_before_projected
  have projectedSurvivorAfter :
      auditProjectedFinalDecision? representedPeerAuditSubject
          representedPeerAuditConsistencyClaimsWithoutBaseline
          "represented-peer-source-gate-0" =
        .ok (some BinaryDecision.Deny) := by
    simpa [witness.survivor_after] using bridge.survivor_after_projected
  have projectedSurvivorChanged :
      auditProjectedFinalDecision? representedPeerAuditSubject
          representedPeerAuditConsistencyClaims
          "represented-peer-source-gate-0" ≠
        auditProjectedFinalDecision? representedPeerAuditSubject
          representedPeerAuditConsistencyClaimsWithoutBaseline
          "represented-peer-source-gate-0" := by
    rw [projectedSurvivorBefore, projectedSurvivorAfter]
    intro h
    cases h
  have reduced_is_without_baseline :
      auditRemoveClaim "baseline" representedPeerAuditConsistencyClaims =
        representedPeerAuditConsistencyClaimsWithoutBaseline :=
    rfl
  have consistencyCoreFailed :
      auditCheckConsistencyCore representedPeerAuditSubject
          representedPeerAuditConsistencyClaims =
        .ok false := by
    have original_finals_concrete :
        auditFinalDecisions representedPeerAuditSubject
            representedPeerAuditConsistencyClaimsConcrete =
          .ok representedPeerAuditOriginalFinalDecisions := by
      simpa [representedPeerAuditConsistencyClaims_eq] using
        bridge.original_finals
    have without_baseline_finals_concrete :
        auditFinalDecisions representedPeerAuditSubject
            representedPeerAuditConsistencyClaimsWithoutBaselineConcrete =
          .ok representedPeerAuditWithoutBaselineFinalDecisions := by
      simpa [representedPeerAuditConsistencyClaimsWithoutBaseline_eq] using
        bridge.without_baseline_finals
    have without_baseline_finals_from_explicit_removal :
        auditFinalDecisions representedPeerAuditSubject
            (auditRemoveClaim representedPeerAuditBaselineClaim.claimantId
              [ representedPeerAuditBaselineClaim
              , representedPeerAuditGate0Claim
              , representedPeerAuditGate1Claim
              , representedPeerAuditGate2Claim
              ]) =
          .ok representedPeerAuditWithoutBaselineFinalDecisions := by
      simpa [representedPeerAuditRemoveBaselineConcrete,
        representedPeerAuditConsistencyClaimsConcrete] using
        without_baseline_finals_concrete
    unfold auditCheckConsistencyCore
    rw [representedPeerAuditConsistencyClaims_eq, original_finals_concrete]
    simp [representedPeerAuditConsistencyClaimsConcrete,
      representedPeerAuditOriginalFinalDecisions,
      representedPeerAuditWithoutBaselineFinalDecisions,
      without_baseline_finals_from_explicit_removal,
      auditLookupDecisionOrError]
    simp [representedPeerAuditBaselineClaim, representedPeerAuditGate0Claim,
      representedPeerAuditGate1Claim, representedPeerAuditGate2Claim,
      auditRemoveClaim]
    native_decide
  unfold auditCheckStatus
  change
    (if detectAuditCycles representedPeerAuditSubject.graph = [] then
        (do
          let consistencyPassed <-
            auditCheckConsistencyCore representedPeerAuditSubject
              representedPeerAuditConsistencyClaims
          if consistencyPassed = true then
            pure AuditCheckStatus.passed
          else
            pure AuditCheckStatus.failed)
      else
        pure AuditCheckStatus.skipped) =
      Except.ok AuditCheckStatus.failed
  simp [representedPeerAuditSubject_no_cycles, consistencyCoreFailed]
  rfl

theorem representedPeer_consistency_check_failed :
    auditCheckStatus representedPeerAuditSubject AuditCheck.consistency =
      .ok .failed :=
  representedPeer_consistency_check_failed_of_obstruction
    representedPeer_graph_consistency_obstruction_witness
    (representedPeer_evalNode_matches_repr_on_consistency_witness
      representedPeer_graph_consistency_obstruction_witness)

/-- The finite audit corpus contains the audit-side names corresponding to the
graph obstruction witness and its baseline-removal profile. -/
theorem representedPeer_audit_corpus_contains_obstruction_profiles :
    representedPeerAuditConsistencyClaims =
        representedPeerAuditConsistencyClaimsConcrete ∧
      representedPeerAuditConsistencyClaimsWithoutBaseline =
        representedPeerAuditConsistencyClaimsWithoutBaselineConcrete ∧
      representedPeerAuditBaselineClaim ∈
        representedPeerAuditConsistencyClaims ∧
      representedPeerAuditGate0Claim ∈
        representedPeerAuditConsistencyClaims ∧
      representedPeerAuditGate0Claim ∈
        representedPeerAuditConsistencyClaimsWithoutBaseline := by
  refine ⟨representedPeerAuditConsistencyClaims_eq,
    representedPeerAuditConsistencyClaimsWithoutBaseline_eq, ?_, ?_, ?_⟩
  · rw [representedPeerAuditConsistencyClaims_eq]
    simp [representedPeerAuditConsistencyClaimsConcrete]
  · rw [representedPeerAuditConsistencyClaims_eq]
    simp [representedPeerAuditConsistencyClaimsConcrete]
  · rw [representedPeerAuditConsistencyClaimsWithoutBaseline_eq]
    simp [representedPeerAuditConsistencyClaimsWithoutBaselineConcrete]

/-- The certificate failure is about the represented obstruction-bearing
subject itself: the carried audit subject is `representedPeer.1.subject`, and
its representation is the graph carrying the exact obstruction witness. -/
theorem representedPeer_certificate_failure_subject_unified :
    representedPeer.1.subject = representedPeerAuditSubject ∧
      RepresentableAuditSubject.repr representedPeer =
        [weakestWithStrongerPeerNode] ∧
      auditCheckStatus representedPeer.1.subject AuditCheck.consistency =
        .ok .failed := by
  refine ⟨rfl, representedPeer_repr_eq, ?_⟩
  exact representedPeer_consistency_check_failed

theorem representedPeer_verdict_rejected :
    governanceAdmissibilityVerdict representedPeerAuditSubject =
      AuditVerdict.rejected AuditCheck.consistency := by
  unfold governanceAdmissibilityVerdict governanceAdmissibilityVerdict?
    firstFailedAuditCheck?
  simp [auditCheckOrder, representedPeer_consistency_check_failed]
  rfl

/-- Certificate failure derived through the represented graph obstruction and
the evalNode/repr weld, rather than by an independent audit-only decision
calculation. -/
theorem representedPeer_certificate_fails :
    ¬ Reflective.ProductionSelfAuditCertificateHolds
        representedPeerAuditSubject := by
  let witness := representedPeer_graph_consistency_obstruction_witness
  let bridge :=
    representedPeer_evalNode_matches_repr_on_consistency_witness
      witness
  have hfailed :=
    representedPeer_consistency_check_failed_of_obstruction witness bridge
  intro hcert
  have hpass :
      auditCheckStatus representedPeerAuditSubject AuditCheck.consistency =
        .ok .passed :=
    hcert.2.1 AuditCheck.consistency (by simp [auditCheckOrder])
  rw [hfailed] at hpass
  cases hpass

theorem representedPeer_box_refuted_via_certificate_iff :
    ¬ Reflective.productionReflectiveBox representedPeerAuditSubject
        Reflective.productionSelfAuditFormula := by
  intro hbox
  exact representedPeer_certificate_fails
    ((Reflective.production_self_audit_box_iff_certificate
      representedPeerAuditSubject).mp hbox)

/-! ## Showcased Codex hook harness projection -/

private def codexHooksTransparentNodeFn : GovernanceNodeFn :=
  fun _claims _claimant => BinaryDecision.Permit

private def codexHooksRegisteredActionDenyNodeFn
    (action : String) : GovernanceNodeFn :=
  fun claims claimant =>
    if (ClaimProfile.lookup claims claimant "hook_registration" == some "1") &&
        (ClaimProfile.lookup claims claimant "action" == some action) then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit

private def codexHooksTransparentRepresentableNode
    (name : String) : RepresentableNode where
  name := name
  gates := []
  default := BinaryDecision.Permit

private def codexHooksRegisteredActionDenyGate
    (action : String) : RepresentableGate where
  kind := .metadataAll [("hook_registration", "1"), ("action", action)]
  decision := BinaryDecision.Deny
  polarity := AuditMetricPolarity.lowerBetter
  metadataField := some "action"

private def codexHooksRegisteredActionDenyNode
    (name action : String) : RepresentableNode where
  name := name
  gates := [codexHooksRegisteredActionDenyGate action]
  default := BinaryDecision.Permit

private theorem codexHooksTransparentRepresentableNode_toGovernanceNode
    (name : String) :
    (codexHooksTransparentRepresentableNode name).toGovernanceNode =
      codexHooksTransparentNodeFn := by
  funext claims claimant
  rfl

private theorem codexHooksRegisteredActionDenyNode_toGovernanceNode
    (name action : String) :
    (codexHooksRegisteredActionDenyNode name action).toGovernanceNode =
      codexHooksRegisteredActionDenyNodeFn action := by
  funext claims claimant
  classical
  by_cases hreg :
      ClaimProfile.lookup claims claimant "hook_registration" = some "1"
  · by_cases haction :
      ClaimProfile.lookup claims claimant "action" = some action
    · have hmatch :
          (codexHooksRegisteredActionDenyGate action).kind.Matches
            claims claimant := by
        intro fieldValue hfieldValue
        simp at hfieldValue ⊢
        rcases hfieldValue with rfl | hfieldValue
        · exact hreg
        · rcases hfieldValue with rfl
          exact haction
      rw [RepresentableNode.toGovernanceNode, RepresentableNode.decide,
        codexHooksRegisteredActionDenyNode]
      rw [RepresentableNode.decideGates_cons_of_matches hmatch]
      simp [codexHooksRegisteredActionDenyGate,
        codexHooksRegisteredActionDenyNodeFn, hreg, haction]
    · have hnotmatch :
          ¬ (codexHooksRegisteredActionDenyGate action).kind.Matches
            claims claimant := by
        intro hmatch
        exact haction
          (hmatch ("action", action) (by simp))
      rw [RepresentableNode.toGovernanceNode, RepresentableNode.decide,
        codexHooksRegisteredActionDenyNode]
      rw [RepresentableNode.decideGates_cons_of_not_matches hnotmatch]
      simp [codexHooksRegisteredActionDenyNodeFn, hreg, haction]
  · have hnotmatch :
        ¬ (codexHooksRegisteredActionDenyGate action).kind.Matches
          claims claimant := by
      intro hmatch
      exact hreg
        (hmatch ("hook_registration", "1") (by simp))
    rw [RepresentableNode.toGovernanceNode, RepresentableNode.decide,
      codexHooksRegisteredActionDenyNode]
    rw [RepresentableNode.decideGates_cons_of_not_matches hnotmatch]
    simp [codexHooksRegisteredActionDenyNodeFn, hreg]

def codexHooksRepresentableSource : RepresentableSource where
  nodes :=
    [ codexHooksTransparentRepresentableNode
        "compact.rs::on_PreCompact"
    , codexHooksTransparentRepresentableNode
        "compact.rs::registration::PreCompact::on_PreCompact"
    , codexHooksRegisteredActionDenyNode
        "permission_request.rs::on_PermissionRequest" "deny"
    , codexHooksTransparentRepresentableNode
        "permission_request.rs::registration::PermissionRequest::on_PermissionRequest"
    , codexHooksRegisteredActionDenyNode
        "post_tool_use.rs::on_PostToolUse" "deny"
    , codexHooksTransparentRepresentableNode
        "post_tool_use.rs::registration::PostToolUse::on_PostToolUse"
    , codexHooksRegisteredActionDenyNode
        "pre_tool_use.rs::on_PreToolUse" "deny"
    , codexHooksTransparentRepresentableNode
        "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse"
    , codexHooksTransparentRepresentableNode
        "registry.rs::on_PostCompact"
    , codexHooksTransparentRepresentableNode
        "registry.rs::registration::PostCompact::on_PostCompact"
    , codexHooksTransparentRepresentableNode
        "session_start.rs::on_SessionStart"
    , codexHooksTransparentRepresentableNode
        "session_start.rs::registration::SessionStart::on_SessionStart"
    , codexHooksRegisteredActionDenyNode
        "stop.rs::on_Stop" "block"
    , codexHooksTransparentRepresentableNode
        "stop.rs::registration::Stop::on_Stop"
    , codexHooksTransparentRepresentableNode
        "user_prompt_submit.rs::on_UserPromptSubmit"
    , codexHooksTransparentRepresentableNode
        "user_prompt_submit.rs::registration::UserPromptSubmit::on_UserPromptSubmit"
    ]

def codexHooksRepresentedSubject : RepresentableAuditSubject where
  name := "codex-hooks-showcased-binary-projection"
  subject := codexHooksExtractedGraph
  source := codexHooksRepresentableSource

theorem codexHooksRepresentedSubject_representable :
    RepresentableAuditSubject.Representable
      codexHooksRepresentedSubject := by
  refine ⟨?_, ?_, ?_⟩
  · simp [codexHooksRepresentedSubject, codexHooksRepresentableSource]
  · rfl
  · intro node hnode
    simp [codexHooksRepresentedSubject, codexHooksExtractedGraph,
      codexHooksExtractedGovernanceGraph] at hnode
    rcases hnode with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, _, _, _, rfl⟩

def codexHooksRepresented :
    { s : RepresentableAuditSubject //
      RepresentableAuditSubject.Representable s } :=
  ⟨codexHooksRepresentedSubject,
    codexHooksRepresentedSubject_representable⟩

theorem codexHooksRepresented_decision_equivalent :
    DecisionSystem.Equivalent
      (RepresentableAuditSubject.sourceSemantics codexHooksRepresented)
      (RepresentableAuditSubject.repr codexHooksRepresented) :=
  RepresentableAuditSubject.decision_equivalent codexHooksRepresented

private def codexHooksProjectedGovernanceGraph : GovernanceGraph :=
  [ codexHooksTransparentNodeFn
  , codexHooksTransparentNodeFn
  , codexHooksRegisteredActionDenyNodeFn "deny"
  , codexHooksTransparentNodeFn
  , codexHooksRegisteredActionDenyNodeFn "deny"
  , codexHooksTransparentNodeFn
  , codexHooksRegisteredActionDenyNodeFn "deny"
  , codexHooksTransparentNodeFn
  , codexHooksTransparentNodeFn
  , codexHooksTransparentNodeFn
  , codexHooksTransparentNodeFn
  , codexHooksTransparentNodeFn
  , codexHooksRegisteredActionDenyNodeFn "block"
  , codexHooksTransparentNodeFn
  , codexHooksTransparentNodeFn
  , codexHooksTransparentNodeFn
  ]

theorem codexHooks_repr_eq_projected :
    RepresentableAuditSubject.repr codexHooksRepresented =
      codexHooksProjectedGovernanceGraph := by
  simp [RepresentableAuditSubject.repr, codexHooksRepresented,
    codexHooksRepresentedSubject, codexHooksRepresentableSource,
    RepresentableSource.toGovernanceGraph,
    codexHooksTransparentRepresentableNode_toGovernanceNode,
    codexHooksRegisteredActionDenyNode_toGovernanceNode,
    codexHooksProjectedGovernanceGraph]

private def stringIndexIn : String → List String → Nat
  | _target, [] => 0
  | target, head :: tail =>
      if target = head then
        0
      else
        stringIndexIn target tail + 1

private def auditClaimBinaryMetadata
    (claim : AuditGovernanceClaim) : List (String × String) :=
  let actionMetadata :=
    match claim.action with
    | some action => [("action", action)]
    | none => []
  let metricMetadata :=
    claim.metrics.map fun entry =>
      (entry.1, if (1 : ℚ) ≤ entry.2 then "1" else "0")
  actionMetadata ++ metricMetadata

private def codexHooksAuditGraphClaims : List AuditGovernanceClaim :=
  auditGraphClaims codexHooksExtractedGraph

private def codexHooksAuditGraphClaimIds : List AuditClaimantId :=
  codexHooksAuditGraphClaims.map AuditGovernanceClaim.claimantId

private def codexHooksAuditClaimantIdToClaimantId
    (claimantId : AuditClaimantId) : ClaimantId :=
  stringIndexIn claimantId codexHooksAuditGraphClaimIds

private def codexHooksAuditClaimToClaimQ
    (claim : AuditGovernanceClaim) : ClaimQ :=
  ⟨codexHooksAuditClaimantIdToClaimantId claim.claimantId,
    1, by norm_num, auditClaimBinaryMetadata claim⟩

private def codexHooksAuditClaimsToClaimQ
    (claims : List AuditGovernanceClaim) : List ClaimQ :=
  claims.map codexHooksAuditClaimToClaimQ

/-- Finite showcased-harness weld: the real `codexHooksExtractedGraph`
dispatcher, projected to scarce binary decisions, agrees on its canonical audit
claim corpus with `graphDecide` on the faithful represented source graph.  The
projection uses the documented escalation convention above: terminal
escalation is not a grant, while the represented Codex registration stages are
continuations to downstream action gates. -/
theorem codexHooks_evalNode_matches_repr_on_auditGraphClaims :
    (codexHooksAuditGraphClaimIds.all fun claimantId =>
      decide
        (auditProjectedFinalDecision? codexHooksExtractedGraph
            codexHooksAuditGraphClaims claimantId =
          .ok (some
            (graphDecide (RepresentableAuditSubject.repr codexHooksRepresented)
              (codexHooksAuditClaimsToClaimQ codexHooksAuditGraphClaims)
              (codexHooksAuditClaimantIdToClaimantId claimantId))))) = true := by
  rw [codexHooks_repr_eq_projected]
  native_decide

theorem codexHooksRepresented_subject_eq_extracted :
    codexHooksRepresented.1.subject = codexHooksExtractedGraph := by
  rfl

/-- The showcased extracted Codex graph reaches a real result through the
represented subject: the same `codexHooksExtractedGraph` is the carried audit
subject, its represented source is decision-equivalent to `repr`, the finite
dispatcher bridge reaches the canonical audit corpus, and the production
verdict rejects monotonicity. -/
theorem codexHooks_repr_welds_to_monotonicity_rejection :
    DecisionSystem.Equivalent
        (RepresentableAuditSubject.sourceSemantics codexHooksRepresented)
        (RepresentableAuditSubject.repr codexHooksRepresented) ∧
      (codexHooksAuditGraphClaimIds.all fun claimantId =>
        decide
          (auditProjectedFinalDecision? codexHooksExtractedGraph
              codexHooksAuditGraphClaims claimantId =
            .ok (some
              (graphDecide (RepresentableAuditSubject.repr codexHooksRepresented)
                (codexHooksAuditClaimsToClaimQ codexHooksAuditGraphClaims)
                (codexHooksAuditClaimantIdToClaimantId claimantId))))) =
        true ∧
      RepresentableAuditSubject.repr codexHooksRepresented =
        codexHooksProjectedGovernanceGraph ∧
      governanceAdmissibilityVerdict codexHooksRepresented.1.subject =
        AuditVerdict.rejected AuditCheck.monotonicity := by
  refine ⟨codexHooksRepresented_decision_equivalent,
    codexHooks_evalNode_matches_repr_on_auditGraphClaims,
    codexHooks_repr_eq_projected, ?_⟩
  simpa [codexHooksRepresented_subject_eq_extracted] using
    codexHooksGovernanceAdmissibilityRejectsMonotonicity

private def codexHooksRegistrationEscalateProjectionGate :
    RepresentableGate where
  kind := .metadataExact "hook_registration" "1"
  decision := AuditDecision.escalate.toScarceBinary
  polarity := AuditMetricPolarity.higherBetter
  metadataField := some "hook_registration"

private def codexHooksRegistrationEscalateProjectionNode
    (name : String) : RepresentableNode where
  name := name
  gates := [codexHooksRegistrationEscalateProjectionGate]
  default := BinaryDecision.Permit

theorem codexHooks_registration_escalate_projection_matches_on_hook_registration
    (name : String) {claims : List ClaimQ} {claimant : ClaimantId}
    (hregistration :
      ClaimProfile.lookup claims claimant "hook_registration" = some "1") :
    (codexHooksRegistrationEscalateProjectionNode name).decide
        claims claimant =
      AuditDecision.escalate.toScarceBinary := by
  have hmatch :
      codexHooksRegistrationEscalateProjectionGate.kind.Matches
        claims claimant := by
    simpa [codexHooksRegistrationEscalateProjectionGate,
      RepresentableGateKind.Matches] using hregistration
  rw [codexHooksRegistrationEscalateProjectionNode,
    RepresentableNode.decide]
  exact RepresentableNode.decideGates_cons_of_matches hmatch

private def codexHooksRegistrationEscalateProjectionClaim : ClaimQ :=
  ⟨0, 1, by norm_num, [("hook_registration", "1")]⟩

/-- Non-vacuous showcased escalation projection: the real Codex extracted
graph contains a `hook_registration` escalation gate, and the corresponding
represented projection maps `hook_registration=1` to binary denial rather than
transparent permit. -/
theorem codexHooks_registration_escalate_projection_nonvacuous :
    (∃ gates,
      .binary "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse"
          "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse"
          gates .permit .firstMatch ∈
        codexHooksExtractedGovernanceGraph.nodes ∧
        .thresholdGate "hook_registration" 1 .escalate ∈ gates) ∧
      AuditDecision.escalate.toScarceBinary = BinaryDecision.Deny ∧
      (codexHooksRegistrationEscalateProjectionNode
          "pre_tool_use.rs::registration::PreToolUse::on_PreToolUse").decide
        [codexHooksRegistrationEscalateProjectionClaim] 0 =
          BinaryDecision.Deny := by
  refine ⟨codexHooks_preToolUseParseCompleted_blockReasonDenyThresholdGate,
    AuditDecision.toScarceBinary_escalate, ?_⟩
  have hregistration :
      ClaimProfile.lookup [codexHooksRegistrationEscalateProjectionClaim]
          0 "hook_registration" = some "1" := by
    rfl
  rw [codexHooks_registration_escalate_projection_matches_on_hook_registration
    _ hregistration]
  exact AuditDecision.toScarceBinary_escalate

end Legitimacy
