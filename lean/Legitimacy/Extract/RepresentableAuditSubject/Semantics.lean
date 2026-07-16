/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.RepresentableAuditSubject

/-!
# All-profile semantics for faithful represented audit subjects

This module records the positive all-profile audit-semantics result for
faithful represented subjects.  The executable finite corpus is not involved:
the source-level facts are direct consequences of
`RepresentableAuditSubject.decision_equivalent`, while the audit-evalNode facts
first consume the `AuditSourceFaithful` weld carried by
`FaithfulRepresentable` and then apply the same generic diagnostic congruence
lemmas.
-/

set_option autoImplicit false

namespace Legitimacy
namespace RepresentableAuditSubject

/-! ## Audit evalNode all-profile semantics -/

private def auditEvalNodeSemanticsWitnessNode : AuditGovernanceNode :=
  AuditGovernanceNode.binary "audit-evalNode-semantics-witness"
    "audit evalNode semantics witness" [] AuditDecision.permit
    AuditGateLogic.firstMatch

/-- All-profile binary decision semantics carried by an executable audit
`evalNode` once it is welded to the source-faithful evaluator.  The
`GraphConsistencyP` family is stated over `ClaimQ` profiles; the instance below
therefore encodes the queried `ClaimQ` profile into an audit profile, runs
`evalNode`, and projects the returned audit decision to the scarce binary
surface. -/
structure AuditEvalNodeSemantics where
  source : RepresentableSource
  evalNode : AuditNodeEvaluator
  evalNode_all_profiles :
    ∀ (node : AuditGovernanceNode) (claims : List AuditGovernanceClaim),
      evalNode node claims = sourceFaithfulAuditNodeEvaluator source node claims

/-- Binary decision obtained by actually running an audit `evalNode` on the
reserved all-profile `ClaimQ` encoding.  Errors or missing decisions are
scarce-allocation denials; faithful evaluators do not take those branches on
this encoding. -/
noncomputable def auditEvalNodeBinaryDecision
    (evalNode : AuditNodeEvaluator)
    (claims : List ClaimQ) (claimant : ClaimantId) : BinaryDecision :=
  match evalNode auditEvalNodeSemanticsWitnessNode
      (claimQDecisionAuditProfile claims claimant) with
  | .ok decisions =>
      match decisionForClaimant? decisions (claimQAuditClaimantId claimant) with
      | some decision => decision.toScarceBinary
      | none => BinaryDecision.Deny
  | .error _ => BinaryDecision.Deny

noncomputable instance :
    DecisionSystem AuditEvalNodeSemantics (List ClaimQ) ClaimantId
      BinaryDecision where
  decide system := auditEvalNodeBinaryDecision system.evalNode

private theorem decisionForClaimant?_sourceFaithful_claimQDecisionAuditProfile
    (source : RepresentableSource)
    (claims : List ClaimQ) (claimant : ClaimantId) :
    decisionForClaimant?
        ((claimQDecisionAuditProfile claims claimant).map fun claim =>
          { claimantId := claim.claimantId
            decision :=
              (source.decide claims
                (auditGovernanceClaimToClaimantId
                  (claimQDecisionAuditProfile claims claimant)
                  claim)).toAuditDecision })
        (claimQAuditClaimantId claimant) =
      some ((source.decide claims claimant).toAuditDecision) := by
  simp [claimQDecisionAuditProfile, decisionForClaimant?]

/-- The all-profile audit-evalNode semantics has the same external `ClaimQ`
decision surface as the represented source semantics.  The proof rewrites the
actual `evalNode` call through the stored all-profile weld and then computes
the scarce binary projection of the source-faithful audit decision. -/
theorem AuditEvalNodeSemantics.decision_equivalent_sourceSemantics
    (system : AuditEvalNodeSemantics) :
    DecisionSystem.Equivalent system
      ({ source := system.source } : RepresentableSource.Semantics) := by
  intro claims claimant
  have hweld :
      system.evalNode auditEvalNodeSemanticsWitnessNode
          (claimQDecisionAuditProfile claims claimant) =
        sourceFaithfulAuditNodeEvaluator system.source
          auditEvalNodeSemanticsWitnessNode
          (claimQDecisionAuditProfile claims claimant) :=
    system.evalNode_all_profiles auditEvalNodeSemanticsWitnessNode
      (claimQDecisionAuditProfile claims claimant)
  simp [DecisionSystem.decide, auditEvalNodeBinaryDecision, hweld,
    sourceFaithfulAuditNodeEvaluator,
    decisionForClaimant?_sourceFaithful_claimQDecisionAuditProfile]

/-- Faithful represented audit semantics preserve the all-profile consistency
diagnostic exactly.  The faithfulness subtype is used only to select
`faithfulRepr`; the proof is the generic decision-system congruence applied to
`decision_equivalent`, which quantifies over every `ClaimQ` profile. -/
theorem faithful_audit_semantics_consistent_iff_graphConsistencyP
    (s : { x : RepresentableAuditSubject // FaithfulRepresentable x }) :
    GraphConsistencyP (sourceSemantics ⟨s.1, s.2.1⟩) ↔
      GraphConsistencyP (faithfulRepr s) := by
  exact GraphConsistencyP_congr (decision_equivalent ⟨s.1, s.2.1⟩)

/-- Faithful represented audit semantics preserve the all-profile solidarity
diagnostic exactly, by the same extensional-decision equivalence. -/
theorem faithful_audit_semantics_solidarity_iff_graphSolidarityP
    (s : { x : RepresentableAuditSubject // FaithfulRepresentable x }) :
    GraphSolidarityP (sourceSemantics ⟨s.1, s.2.1⟩) ↔
      GraphSolidarityP (faithfulRepr s) := by
  exact GraphSolidarityP_congr (decision_equivalent ⟨s.1, s.2.1⟩)

/-- Faithful represented audit semantics preserve the all-profile monotonicity
diagnostic exactly, by the same extensional-decision equivalence. -/
theorem faithful_audit_semantics_monotonicity_iff_graphMonotonicityP
    (s : { x : RepresentableAuditSubject // FaithfulRepresentable x }) :
    GraphMonotonicityP (sourceSemantics ⟨s.1, s.2.1⟩) ↔
      GraphMonotonicityP (faithfulRepr s) := by
  exact GraphMonotonicityP_congr (decision_equivalent ⟨s.1, s.2.1⟩)

/-! ## Literal audit evalNode bridges -/

/-- The faithful audit subject's executable `evalNode`, viewed through its
all-profile `AuditSourceFaithful` weld, preserves the consistency diagnostic
exactly with the represented graph.  This is the literal audit-level bridge:
the left-hand decision system carries `s.1.subject.evalNode`, and the proof
chains `AuditSourceFaithful.evalNode_all_profiles` with the existing
source-semantics iff. -/
theorem faithful_audit_evalNode_consistent_iff_graphConsistencyP
    (s : { x : RepresentableAuditSubject // FaithfulRepresentable x }) :
    GraphConsistencyP
        ({ source := s.1.source
           evalNode := s.1.subject.evalNode
           evalNode_all_profiles :=
             AuditSourceFaithful.evalNode_all_profiles s.2.2 } :
          AuditEvalNodeSemantics) ↔
      GraphConsistencyP (faithfulRepr s) := by
  calc
    GraphConsistencyP
        ({ source := s.1.source
           evalNode := s.1.subject.evalNode
           evalNode_all_profiles :=
             AuditSourceFaithful.evalNode_all_profiles s.2.2 } :
          AuditEvalNodeSemantics)
        ↔ GraphConsistencyP (sourceSemantics ⟨s.1, s.2.1⟩) := by
          exact
            GraphConsistencyP_congr
              (AuditEvalNodeSemantics.decision_equivalent_sourceSemantics
                ({ source := s.1.source
                   evalNode := s.1.subject.evalNode
                   evalNode_all_profiles :=
                     AuditSourceFaithful.evalNode_all_profiles s.2.2 } :
                  AuditEvalNodeSemantics))
    _ ↔ GraphConsistencyP (faithfulRepr s) :=
      faithful_audit_semantics_consistent_iff_graphConsistencyP s

/-- The faithful audit subject's executable `evalNode`, viewed through its
all-profile `AuditSourceFaithful` weld, preserves the solidarity diagnostic
exactly with the represented graph. -/
theorem faithful_audit_evalNode_solidarity_iff_graphSolidarityP
    (s : { x : RepresentableAuditSubject // FaithfulRepresentable x }) :
    GraphSolidarityP
        ({ source := s.1.source
           evalNode := s.1.subject.evalNode
           evalNode_all_profiles :=
             AuditSourceFaithful.evalNode_all_profiles s.2.2 } :
          AuditEvalNodeSemantics) ↔
      GraphSolidarityP (faithfulRepr s) := by
  calc
    GraphSolidarityP
        ({ source := s.1.source
           evalNode := s.1.subject.evalNode
           evalNode_all_profiles :=
             AuditSourceFaithful.evalNode_all_profiles s.2.2 } :
          AuditEvalNodeSemantics)
        ↔ GraphSolidarityP (sourceSemantics ⟨s.1, s.2.1⟩) := by
          exact
            GraphSolidarityP_congr
              (AuditEvalNodeSemantics.decision_equivalent_sourceSemantics
                ({ source := s.1.source
                   evalNode := s.1.subject.evalNode
                   evalNode_all_profiles :=
                     AuditSourceFaithful.evalNode_all_profiles s.2.2 } :
                  AuditEvalNodeSemantics))
    _ ↔ GraphSolidarityP (faithfulRepr s) :=
      faithful_audit_semantics_solidarity_iff_graphSolidarityP s

/-- The faithful audit subject's executable `evalNode`, viewed through its
all-profile `AuditSourceFaithful` weld, preserves the monotonicity diagnostic
exactly with the represented graph. -/
theorem faithful_audit_evalNode_monotonicity_iff_graphMonotonicityP
    (s : { x : RepresentableAuditSubject // FaithfulRepresentable x }) :
    GraphMonotonicityP
        ({ source := s.1.source
           evalNode := s.1.subject.evalNode
           evalNode_all_profiles :=
             AuditSourceFaithful.evalNode_all_profiles s.2.2 } :
          AuditEvalNodeSemantics) ↔
      GraphMonotonicityP (faithfulRepr s) := by
  calc
    GraphMonotonicityP
        ({ source := s.1.source
           evalNode := s.1.subject.evalNode
           evalNode_all_profiles :=
             AuditSourceFaithful.evalNode_all_profiles s.2.2 } :
          AuditEvalNodeSemantics)
        ↔ GraphMonotonicityP (sourceSemantics ⟨s.1, s.2.1⟩) := by
          exact
            GraphMonotonicityP_congr
              (AuditEvalNodeSemantics.decision_equivalent_sourceSemantics
                ({ source := s.1.source
                   evalNode := s.1.subject.evalNode
                   evalNode_all_profiles :=
                     AuditSourceFaithful.evalNode_all_profiles s.2.2 } :
                  AuditEvalNodeSemantics))
    _ ↔ GraphMonotonicityP (faithfulRepr s) :=
      faithful_audit_semantics_monotonicity_iff_graphMonotonicityP s

end RepresentableAuditSubject
end Legitimacy
