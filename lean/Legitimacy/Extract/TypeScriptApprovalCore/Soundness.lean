/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.TypeScriptApprovalCore.Extractor

/-!
# TypeScriptApprovalCore extractor soundness

Lean-side proof that successful TypeScriptApprovalCore extraction preserves
external decision behavior and reflects graph-level failures back to the
modeled source program.
-/

set_option autoImplicit false

namespace Legitimacy
namespace TypeScriptApprovalCore

lemma extractRegistrationNode_eq_registrationNode
    (program : Program) (registration : Registration) (node : GovernanceNodeFn)
    (h : extractRegistrationNode program registration = .ok node) :
    node = registrationNode program registration := by
  unfold extractRegistrationNode at h
  cases hfind : findHandler? program.handlers registration.handler with
  | none =>
      simp [hfind] at h
  | some handler =>
      simp [hfind] at h
      cases h
      funext profile subject
      simp [registrationNode, evalRegistration, handlerNode, hfind]

lemma graphDecide_extractRegistrationNodes_equiv
    (program : Program) (registrations : List Registration)
    (graph : GovernanceGraph)
    (h : extractRegistrationNodes program registrations = .ok graph) :
    ∀ (profile : ClaimProfile) (subject : ClaimantId),
      graphDecide graph profile subject =
        evalRegistrations program registrations profile subject := by
  induction registrations generalizing graph with
  | nil =>
      intro profile subject
      simp [extractRegistrationNodes] at h
      cases h
      rfl
  | cons registration rest ih =>
      unfold extractRegistrationNodes at h
      cases hnode : extractRegistrationNode program registration with
      | error error =>
          simp [hnode] at h
      | ok node =>
          cases hnodes : extractRegistrationNodes program rest with
          | error error =>
              simp [hnode, hnodes] at h
          | ok nodes =>
              simp [hnode, hnodes] at h
              cases h
              have hnode_eq :
                  node = registrationNode program registration :=
                extractRegistrationNode_eq_registrationNode program registration node hnode
              intro profile subject
              rw [hnode_eq]
              cases hdecision :
                  evalRegistration program registration profile subject <;>
                simp [graphDecide, evalRegistrations, registrationNode, hdecision,
                  ih nodes hnodes]

lemma extractTypeScriptApprovalCore_decision_equivalent
    (program : Program) (graph : GovernanceGraph)
    (h : extractTypeScriptApprovalCore program = .ok graph) :
    DecisionSystem.Equivalent (sourceGovernanceGraphSemantics program) graph := by
  unfold extractTypeScriptApprovalCore at h
  cases hregs : program.registrations with
  | nil =>
      simp [hregs] at h
  | cons registration rest =>
      intro profile subject
      simp [hregs] at h
      change evalTypeScriptApprovalCore program profile subject = graphDecide graph profile subject
      simpa [evalTypeScriptApprovalCore, hregs] using
        (graphDecide_extractRegistrationNodes_equiv program
          (registration :: rest) graph h profile subject).symm

/-- Structural properties reflected by the TypeScriptApprovalCore theorem. Each
constructor names the claimant and, when applicable, the approval handler whose
denial or registration failure is being diagnosed. -/
inductive StructuralProperty where
  | deniedSubject : ClaimantId → StructuralProperty
  | handlerDeniedSubject : ClaimantId → String → StructuralProperty
  | registrationGateFailure : ClaimantId → String → StructuralProperty
  deriving DecidableEq, Repr

/-- The diagnosed subject is present in the claim profile being checked. -/
def SubjectAppears (profile : ClaimProfile) (subject : ClaimantId) : Prop :=
  ∃ claim, claim ∈ profile ∧ claim.id = subject

/-- A graph-level denial trace through the sequential extracted pipeline. -/
def ExtractedDenialTrace :
    GovernanceGraph → ClaimProfile → ClaimantId → Prop
  | [], _, _ => False
  | node :: rest, profile, subject =>
      node profile subject = BinaryDecision.Deny ∨
        node profile subject = BinaryDecision.Permit ∧
          ExtractedDenialTrace rest (filterPermitted node profile) subject

/-- A graph-level denial trace whose rejecting node is paired with the named
handler from the modeled registration stream. -/
def ExtractedHandlerDenialTrace :
    List Registration → GovernanceGraph → ClaimProfile → ClaimantId → String → Prop
  | [], _, _, _, _ => False
  | _, [], _, _, _ => False
  | registration :: registrations, node :: rest, profile, subject, handler =>
      registration.handler = handler ∧
          node profile subject = BinaryDecision.Deny ∨
        node profile subject = BinaryDecision.Permit ∧
          ExtractedHandlerDenialTrace registrations rest
            (filterPermitted node profile) subject handler

/-- A source-level registration denial trace mirroring the graph trace through
the modeled TypeScript approval registration pipeline. -/
def SourceDenialTrace (program : Program) :
    List Registration → ClaimProfile → ClaimantId → Prop
  | [], _, _ => False
  | registration :: rest, profile, subject =>
      evalRegistration program registration profile subject = BinaryDecision.Deny ∨
        evalRegistration program registration profile subject = BinaryDecision.Permit ∧
          SourceDenialTrace program rest
            (filterPermitted (registrationNode program registration) profile)
            subject

/-- A source-level denial trace whose rejecting registration uses the named
handler. -/
def SourceHandlerDenialTrace (program : Program) :
    List Registration → ClaimProfile → ClaimantId → String → Prop
  | [], _, _, _ => False
  | registration :: rest, profile, subject, handler =>
      registration.handler = handler ∧
          evalRegistration program registration profile subject = BinaryDecision.Deny ∨
        evalRegistration program registration profile subject = BinaryDecision.Permit ∧
          SourceHandlerDenialTrace program rest
            (filterPermitted (registrationNode program registration) profile)
            subject handler

def ExtractedGraphFailure
    (registrations : List Registration) (graph : GovernanceGraph) :
    StructuralProperty → Prop
  | .deniedSubject subject =>
      ∃ profile : ClaimProfile,
        SubjectAppears profile subject ∧
          DecisionSystem.decide graph profile subject = BinaryDecision.Deny
  | .handlerDeniedSubject subject handler =>
      ∃ profile : ClaimProfile,
        SubjectAppears profile subject ∧
          ExtractedHandlerDenialTrace registrations graph profile subject handler
  | .registrationGateFailure subject handler =>
      ∃ profile : ClaimProfile,
        ExtractedHandlerDenialTrace registrations graph profile subject handler

def SourceSemanticsFailure
    (source : Program) : StructuralProperty → Prop
  | .deniedSubject subject =>
      ∃ profile : ClaimProfile,
        SubjectAppears profile subject ∧
          DecisionSystem.decide (sourceGovernanceGraphSemantics source)
            profile subject = BinaryDecision.Deny
  | .handlerDeniedSubject subject handler =>
      ∃ profile : ClaimProfile,
        SubjectAppears profile subject ∧
          SourceHandlerDenialTrace source source.registrations profile subject handler
  | .registrationGateFailure subject handler =>
      ∃ profile : ClaimProfile,
        SourceHandlerDenialTrace source source.registrations profile subject handler

lemma sourceDenialTrace_of_extractedDenialTrace
    (program : Program) (registrations : List Registration)
    (graph : GovernanceGraph)
    (h : extractRegistrationNodes program registrations = .ok graph)
    {profile : ClaimProfile} {subject : ClaimantId}
    (htrace : ExtractedDenialTrace graph profile subject) :
    SourceDenialTrace program registrations profile subject := by
  induction registrations generalizing graph profile with
  | nil =>
      simp [extractRegistrationNodes] at h
      cases h
      simp [ExtractedDenialTrace] at htrace
  | cons registration rest ih =>
      unfold extractRegistrationNodes at h
      cases hnode : extractRegistrationNode program registration with
      | error error =>
          simp [hnode] at h
      | ok node =>
          cases hnodes : extractRegistrationNodes program rest with
          | error error =>
              simp [hnode, hnodes] at h
          | ok nodes =>
              simp [hnode, hnodes] at h
              cases h
              have hnode_eq :
                  node = registrationNode program registration :=
                extractRegistrationNode_eq_registrationNode program registration node hnode
              simp [ExtractedDenialTrace, SourceDenialTrace] at htrace ⊢
              rcases htrace with hdeny | ⟨hpermit, htail⟩
              · left
                rw [hnode_eq] at hdeny
                simpa [registrationNode] using hdeny
              · right
                constructor
                · rw [hnode_eq] at hpermit
                  simpa [registrationNode] using hpermit
                · rw [hnode_eq] at htail
                  exact ih nodes hnodes htail

lemma sourceDenialTrace_of_extractTypeScriptApprovalCore
    (source : Program) (graph : GovernanceGraph)
    (hextract : extractTypeScriptApprovalCore source = .ok graph)
    {profile : ClaimProfile} {subject : ClaimantId}
    (htrace : ExtractedDenialTrace graph profile subject) :
    SourceDenialTrace source source.registrations profile subject := by
  unfold extractTypeScriptApprovalCore at hextract
  cases hregs : source.registrations with
  | nil =>
      simp [hregs] at hextract
  | cons registration rest =>
      simp [hregs] at hextract
      simpa [hregs] using
        sourceDenialTrace_of_extractedDenialTrace source
          (registration :: rest) graph hextract htrace

lemma sourceHandlerDenialTrace_of_extractedHandlerDenialTrace
    (program : Program) (registrations : List Registration)
    (graph : GovernanceGraph)
    (h : extractRegistrationNodes program registrations = .ok graph)
    {profile : ClaimProfile} {subject : ClaimantId} {handler : String}
    (htrace :
      ExtractedHandlerDenialTrace registrations graph profile subject handler) :
    SourceHandlerDenialTrace program registrations profile subject handler := by
  induction registrations generalizing graph profile with
  | nil =>
      simp [extractRegistrationNodes] at h
      cases h
      simp [ExtractedHandlerDenialTrace] at htrace
  | cons registration rest ih =>
      unfold extractRegistrationNodes at h
      cases hnode : extractRegistrationNode program registration with
      | error error =>
          simp [hnode] at h
      | ok node =>
          cases hnodes : extractRegistrationNodes program rest with
          | error error =>
              simp [hnode, hnodes] at h
          | ok nodes =>
              simp [hnode, hnodes] at h
              cases h
              have hnode_eq :
                  node = registrationNode program registration :=
                extractRegistrationNode_eq_registrationNode program registration node hnode
              simp [ExtractedHandlerDenialTrace, SourceHandlerDenialTrace] at htrace ⊢
              rcases htrace with hdeny | ⟨hpermit, htail⟩
              · left
                rcases hdeny with ⟨hhandler, hnode_deny⟩
                refine ⟨hhandler, ?_⟩
                rw [hnode_eq] at hnode_deny
                simpa [registrationNode] using hnode_deny
              · right
                constructor
                · rw [hnode_eq] at hpermit
                  simpa [registrationNode] using hpermit
                · rw [hnode_eq] at htail
                  exact ih nodes hnodes htail

lemma sourceHandlerDenialTrace_of_extractTypeScriptApprovalCore
    (source : Program) (graph : GovernanceGraph)
    (hextract : extractTypeScriptApprovalCore source = .ok graph)
    {profile : ClaimProfile} {subject : ClaimantId} {handler : String}
    (htrace :
      ExtractedHandlerDenialTrace source.registrations graph profile subject handler) :
    SourceHandlerDenialTrace source source.registrations profile subject handler := by
  unfold extractTypeScriptApprovalCore at hextract
  cases hregs : source.registrations with
  | nil =>
      simp [hregs] at hextract
  | cons registration rest =>
      simp [hregs] at hextract
      simpa [hregs] using
        sourceHandlerDenialTrace_of_extractedHandlerDenialTrace source
          (registration :: rest) graph hextract (by simpa [hregs] using htrace)

/-- Modeled-program failure reflection for the Lean TypeScriptApprovalCore
extractor.

This theorem is scoped to the Lean `Program` model consumed by
`extractTypeScriptApprovalCore`. The Rust canonical-AST parser binds source text
to this modeled core by hash and refusal discipline as a separate bridge. -/
lemma typescript_approval_modeled_program_extractor_failure_reflects_modeled_source_failure
    {property : StructuralProperty}
    (src : Program) (graph : GovernanceGraph)
    (hextract : extractTypeScriptApprovalCore src = .ok graph)
    (hfail : ExtractedGraphFailure src.registrations graph property) :
    SourceSemanticsFailure src property := by
  let hequiv := extractTypeScriptApprovalCore_decision_equivalent src graph hextract
  cases property with
  | deniedSubject subject =>
      rcases hfail with ⟨profile, happears, hgraph⟩
      exact ⟨profile, happears, (hequiv profile subject).trans hgraph⟩
  | handlerDeniedSubject subject handler =>
      rcases hfail with ⟨profile, happears, htrace⟩
      exact ⟨profile, happears,
        sourceHandlerDenialTrace_of_extractTypeScriptApprovalCore src graph hextract htrace⟩
  | registrationGateFailure subject handler =>
      rcases hfail with ⟨profile, htrace⟩
      exact ⟨profile,
        sourceHandlerDenialTrace_of_extractTypeScriptApprovalCore src graph hextract htrace⟩

end TypeScriptApprovalCore
end Legitimacy
