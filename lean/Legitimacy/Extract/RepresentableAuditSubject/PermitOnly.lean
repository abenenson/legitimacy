/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.RepresentableAuditSubject

/-!
# Permit-only represented audit subject

This small positive fixture keeps the core representation module below the
architecture line-count ceiling while retaining the certificate-positive floor
test used by the round-4/round-5 boundary proofs.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A non-obstruction represented subject whose production certificate holds. -/
def permitOnlyAuditSubject : AuditSubject where
  graph :=
    { nodes :=
        [ .binary "permit-only" "permit only" []
            AuditDecision.permit AuditGateLogic.firstMatch ]
      edges := [] }
  evalNode := auditEvaluateNode

def permitOnlyRepresentableNode : RepresentableNode where
  name := "permit-only"
  gates := []
  default := BinaryDecision.Permit

def permitOnlySource : RepresentableSource where
  nodes := [permitOnlyRepresentableNode]

def permitOnlyRepresentedSubject : RepresentableAuditSubject where
  name := "permit-only-certificate-positive"
  subject := permitOnlyAuditSubject
  source := permitOnlySource

theorem permitOnlyRepresentedSubject_representable :
    RepresentableAuditSubject.Representable
      permitOnlyRepresentedSubject := by
  refine ⟨?_, ?_, ?_⟩
  · simp [permitOnlyRepresentedSubject, permitOnlySource]
  · rfl
  · intro node hnode
    simp [permitOnlyRepresentedSubject, permitOnlyAuditSubject] at hnode
    rcases hnode with rfl
    exact
      ⟨"permit-only", "permit only", [], AuditDecision.permit, rfl⟩

def permitOnlyRepresented :
    { s : RepresentableAuditSubject //
      RepresentableAuditSubject.Representable s } :=
  ⟨permitOnlyRepresentedSubject,
    permitOnlyRepresentedSubject_representable⟩

theorem permitOnly_certificate_holds :
    Reflective.ProductionSelfAuditCertificateHolds
      permitOnlyAuditSubject := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · native_decide
  · intro check _hmem
    fin_cases check <;> native_decide
  · native_decide
  · native_decide

theorem permitOnly_repr_diagnostics :
    GraphConsistencyP (RepresentableAuditSubject.repr
        permitOnlyRepresented) ∧
      GraphSolidarityP (RepresentableAuditSubject.repr
        permitOnlyRepresented) ∧
        GraphMonotonicityP (RepresentableAuditSubject.repr
          permitOnlyRepresented) := by
  simp [RepresentableAuditSubject.repr, permitOnlyRepresented,
    permitOnlyRepresentedSubject, permitOnlySource,
    permitOnlyRepresentableNode, RepresentableSource.toGovernanceGraph,
    RepresentableNode.toGovernanceNode, RepresentableNode.decide,
    GraphConsistencyP, GraphSolidarityP, GraphMonotonicityP,
    DecisionSystem.decide, graphDecide]

theorem representable_floor_test :
    RepresentableAuditSubject.Representable representedPeerSubject ∧
      RepresentableAuditSubject.Representable permitOnlyRepresentedSubject ∧
        ¬ GraphConsistencyP
          (RepresentableAuditSubject.repr representedPeer) ∧
          Reflective.ProductionSelfAuditCertificateHolds
            permitOnlyAuditSubject :=
  ⟨representedPeerSubject_representable,
    permitOnlyRepresentedSubject_representable,
    representedPeer_not_graphConsistent,
    permitOnly_certificate_holds⟩

end Legitimacy
