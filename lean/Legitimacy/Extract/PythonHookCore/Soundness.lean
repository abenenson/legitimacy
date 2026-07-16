/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.PythonHookCore.Extractor

/-!
# PythonHookCore extractor soundness

Lean-side proof that successful PythonHookCore extraction preserves external
decision behavior.
-/

set_option autoImplicit false

namespace Legitimacy
namespace PythonHookCore

lemma extractRegistrationNode_eq_registrationNode
    (program : Program) (registration : Registration) (node : GovernanceNodeFn)
    (h : extractRegistrationNode program registration = .ok node) :
    node = registrationNode program registration := by
  unfold extractRegistrationNode at h
  cases hfind : findCallback? program.callbacks registration.callback with
  | none =>
      simp [hfind] at h
  | some callback =>
      simp [hfind] at h
      cases h
      funext profile subject
      simp [registrationNode, evalRegistration, callbackNode, hfind]

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

lemma extractPythonHookCore_decision_equivalent
    (program : Program) (graph : GovernanceGraph)
    (h : extractPythonHookCore program = .ok graph) :
    DecisionSystem.Equivalent (sourceGovernanceGraphSemantics program) graph := by
  unfold extractPythonHookCore at h
  cases hregs : program.registrations with
  | nil =>
      simp [hregs] at h
  | cons registration rest =>
      intro profile subject
      simp [hregs] at h
      change evalPythonHookCore program profile subject = graphDecide graph profile subject
      simpa [evalPythonHookCore, hregs] using
        (graphDecide_extractRegistrationNodes_equiv program
          (registration :: rest) graph h profile subject).symm

/-- Structural properties reflected by the PythonHookCore theorem. Each
constructor names the claimant whose denial is being diagnosed, so the property
argument constrains the witness instead of merely selecting a tautological
"some denial exists" predicate. -/
inductive StructuralProperty where
  | deniedSubject : ClaimantId → StructuralProperty
  | blockedSubject : ClaimantId → StructuralProperty
  | callbackGateFailure : ClaimantId → StructuralProperty
  deriving DecidableEq, Repr

/-- The diagnosed subject is present in the claim profile being checked. -/
def SubjectAppears (profile : ClaimProfile) (subject : ClaimantId) : Prop :=
  ∃ claim, claim ∈ profile ∧ claim.id = subject

/-- A graph-level denial trace: the subject is rejected by a concrete node in
the sequential pipeline after every earlier node forwarded it. -/
def ExtractedDenialTrace :
    GovernanceGraph → ClaimProfile → ClaimantId → Prop
  | [], _, _ => False
  | node :: rest, profile, subject =>
      node profile subject = BinaryDecision.Deny ∨
        node profile subject = BinaryDecision.Permit ∧
          ExtractedDenialTrace rest (filterPermitted node profile) subject

/-- A source-level registration denial trace mirroring the graph trace through
the modeled callback registration pipeline. -/
def SourceDenialTrace (program : Program) :
    List Registration → ClaimProfile → ClaimantId → Prop
  | [], _, _ => False
  | registration :: rest, profile, subject =>
      evalRegistration program registration profile subject = BinaryDecision.Deny ∨
        evalRegistration program registration profile subject = BinaryDecision.Permit ∧
          SourceDenialTrace program rest
            (filterPermitted (registrationNode program registration) profile)
            subject

def ExtractedGraphFailure
    (graph : GovernanceGraph) : StructuralProperty → Prop
  | .deniedSubject subject =>
      ∃ profile : ClaimProfile,
        SubjectAppears profile subject ∧
          DecisionSystem.decide graph profile subject = BinaryDecision.Deny
  | .blockedSubject subject =>
      ∃ profile : ClaimProfile,
        SubjectAppears profile subject ∧
          ExtractedDenialTrace graph profile subject
  | .callbackGateFailure subject =>
      ∃ profile : ClaimProfile,
        ExtractedDenialTrace graph profile subject

def SourceSemanticsFailure
    (source : Program) : StructuralProperty → Prop
  | .deniedSubject subject =>
      ∃ profile : ClaimProfile,
        SubjectAppears profile subject ∧
          DecisionSystem.decide (sourceGovernanceGraphSemantics source)
            profile subject = BinaryDecision.Deny
  | .blockedSubject subject =>
      ∃ profile : ClaimProfile,
        SubjectAppears profile subject ∧
          SourceDenialTrace source source.registrations profile subject
  | .callbackGateFailure subject =>
      ∃ profile : ClaimProfile,
        SourceDenialTrace source source.registrations profile subject

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

lemma sourceDenialTrace_of_extractPythonHookCore
    (source : Program) (graph : GovernanceGraph)
    (hextract : extractPythonHookCore source = .ok graph)
    {profile : ClaimProfile} {subject : ClaimantId}
    (htrace : ExtractedDenialTrace graph profile subject) :
    SourceDenialTrace source source.registrations profile subject := by
  unfold extractPythonHookCore at hextract
  cases hregs : source.registrations with
  | nil =>
      simp [hregs] at hextract
  | cons registration rest =>
      simp [hregs] at hextract
      simpa [hregs] using
        sourceDenialTrace_of_extractedDenialTrace source
          (registration :: rest) graph hextract htrace

/-- Modeled-program failure reflection for the Lean PythonHookCore extractor.

This theorem is intentionally scoped to the Lean `Program` model consumed by
`extractPythonHookCore`. It does not prove that the Rust tree-sitter parser's
`PythonHookCoreAst` JSON representation deserializes to this `Program`; that
Rust-to-Lean binding theorem remains a separate obligation. -/
lemma python_hook_modeled_program_extractor_failure_reflects_modeled_source_failure
    {property : StructuralProperty}
    (source : Program) (graph : GovernanceGraph)
    (hextract : extractPythonHookCore source = .ok graph)
    (hfail : ExtractedGraphFailure graph property) :
    SourceSemanticsFailure source property := by
  let hequiv := extractPythonHookCore_decision_equivalent source graph hextract
  cases property with
  | deniedSubject subject =>
      rcases hfail with ⟨profile, happears, hgraph⟩
      exact ⟨profile, happears, (hequiv profile subject).trans hgraph⟩
  | blockedSubject subject =>
      rcases hfail with ⟨profile, happears, htrace⟩
      exact ⟨profile, happears,
        sourceDenialTrace_of_extractPythonHookCore source graph hextract htrace⟩
  | callbackGateFailure subject =>
      rcases hfail with ⟨profile, htrace⟩
      exact ⟨profile,
        sourceDenialTrace_of_extractPythonHookCore source graph hextract htrace⟩

end PythonHookCore
end Legitimacy
