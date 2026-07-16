/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.RustHookCore.Extractor

/-!
# RustHookCore extractor soundness

Lean-side proof that successful RustHookCore extraction preserves external
decision behavior for modeled programs, plus structural failure reflection for
diagnostics that name the claimant/event being diagnosed.
-/

set_option autoImplicit false

namespace Legitimacy
namespace RustHookCore

lemma extractRegistrationNode_eq_registrationNode
    (program : Program) (registration : Registration) (node : GovernanceNodeFn)
    (h : extractRegistrationNode program registration = .ok node) :
    node = registrationNode program registration := by
  unfold extractRegistrationNode at h
  cases hfind : findHook? program.hooks registration.callback with
  | none =>
      simp [hfind] at h
  | some hook =>
      simp [hfind] at h
      cases h
      funext profile subject
      simp [registrationNode, evalRegistration, hookNode, hfind]

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

lemma extractRustHookCore_decision_equivalent
    (program : Program) (graph : GovernanceGraph)
    (h : extractRustHookCore program = .ok graph) :
    DecisionSystem.Equivalent (sourceGovernanceGraphSemantics program) graph := by
  unfold extractRustHookCore at h
  cases hregs : program.registrations with
  | nil =>
      simp [hregs] at h
  | cons registration rest =>
      intro profile subject
      simp [hregs] at h
      change evalRustHookCore program profile subject = graphDecide graph profile subject
      simpa [evalRustHookCore, hregs] using
        (graphDecide_extractRegistrationNodes_equiv program
          (registration :: rest) graph h profile subject).symm

/-- Structural properties reflected by the RustHookCore theorem. Constructors
carry the named subject or event so the property constrains the witness. -/
inductive StructuralProperty where
  | deniedSubject : ClaimantId → StructuralProperty
  | blockedSubject : ClaimantId → StructuralProperty
  | eventGateFailure : String → ClaimantId → StructuralProperty
  deriving DecidableEq, Repr

/-- The diagnosed subject is present in the claim profile being checked. -/
def SubjectAppears (profile : ClaimProfile) (subject : ClaimantId) : Prop :=
  ∃ claim, claim ∈ profile ∧ claim.id = subject

/-- A graph-level denial trace through a sequential pipeline. -/
def ExtractedDenialTrace :
    GovernanceGraph → ClaimProfile → ClaimantId → Prop
  | [], _, _ => False
  | node :: rest, profile, subject =>
      node profile subject = BinaryDecision.Deny ∨
        node profile subject = BinaryDecision.Permit ∧
          ExtractedDenialTrace rest (filterPermitted node profile) subject

/-- A graph-level denial trace whose rejecting node is paired with the named
event from the modeled registration stream. -/
def ExtractedEventDenialTrace :
    List Registration → GovernanceGraph → ClaimProfile → ClaimantId → String → Prop
  | [], _, _, _, _ => False
  | _, [], _, _, _ => False
  | registration :: registrations, node :: rest, profile, subject, event =>
      registration.event = event ∧
          node profile subject = BinaryDecision.Deny ∨
        node profile subject = BinaryDecision.Permit ∧
          ExtractedEventDenialTrace registrations rest
            (filterPermitted node profile) subject event

/-- A source-level registration denial trace mirroring the extracted graph. -/
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
event. -/
def SourceEventDenialTrace (program : Program) :
    List Registration → ClaimProfile → ClaimantId → String → Prop
  | [], _, _, _ => False
  | registration :: rest, profile, subject, event =>
      registration.event = event ∧
          evalRegistration program registration profile subject = BinaryDecision.Deny ∨
        evalRegistration program registration profile subject = BinaryDecision.Permit ∧
          SourceEventDenialTrace program rest
            (filterPermitted (registrationNode program registration) profile)
            subject event

def ExtractedGraphFailure
    (registrations : List Registration) (graph : GovernanceGraph) :
    StructuralProperty → Prop
  | .deniedSubject subject =>
      ∃ profile : ClaimProfile,
        SubjectAppears profile subject ∧
          DecisionSystem.decide graph profile subject = BinaryDecision.Deny
  | .blockedSubject subject =>
      ∃ profile : ClaimProfile,
        SubjectAppears profile subject ∧
          ExtractedDenialTrace graph profile subject
  | .eventGateFailure event subject =>
      ∃ profile : ClaimProfile,
        ExtractedEventDenialTrace registrations graph profile subject event

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
  | .eventGateFailure event subject =>
      ∃ profile : ClaimProfile,
        SourceEventDenialTrace source source.registrations profile subject event

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

lemma sourceDenialTrace_of_extractRustHookCore
    (source : Program) (graph : GovernanceGraph)
    (hextract : extractRustHookCore source = .ok graph)
    {profile : ClaimProfile} {subject : ClaimantId}
    (htrace : ExtractedDenialTrace graph profile subject) :
    SourceDenialTrace source source.registrations profile subject := by
  unfold extractRustHookCore at hextract
  cases hregs : source.registrations with
  | nil =>
      simp [hregs] at hextract
  | cons registration rest =>
      simp [hregs] at hextract
      simpa [hregs] using
        sourceDenialTrace_of_extractedDenialTrace source
          (registration :: rest) graph hextract htrace

lemma sourceEventDenialTrace_of_extractedEventDenialTrace
    (program : Program) (registrations : List Registration)
    (graph : GovernanceGraph)
    (h : extractRegistrationNodes program registrations = .ok graph)
    {profile : ClaimProfile} {subject : ClaimantId} {event : String}
    (htrace :
      ExtractedEventDenialTrace registrations graph profile subject event) :
    SourceEventDenialTrace program registrations profile subject event := by
  induction registrations generalizing graph profile with
  | nil =>
      simp [extractRegistrationNodes] at h
      cases h
      simp [ExtractedEventDenialTrace] at htrace
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
              simp [ExtractedEventDenialTrace, SourceEventDenialTrace] at htrace ⊢
              rcases htrace with hdeny | ⟨hpermit, htail⟩
              · left
                rcases hdeny with ⟨hevent, hnode_deny⟩
                refine ⟨hevent, ?_⟩
                rw [hnode_eq] at hnode_deny
                simpa [registrationNode] using hnode_deny
              · right
                constructor
                · rw [hnode_eq] at hpermit
                  simpa [registrationNode] using hpermit
                · rw [hnode_eq] at htail
                  exact ih nodes hnodes htail

lemma sourceEventDenialTrace_of_extractRustHookCore
    (source : Program) (graph : GovernanceGraph)
    (hextract : extractRustHookCore source = .ok graph)
    {profile : ClaimProfile} {subject : ClaimantId} {event : String}
    (htrace :
      ExtractedEventDenialTrace source.registrations graph profile subject event) :
    SourceEventDenialTrace source source.registrations profile subject event := by
  unfold extractRustHookCore at hextract
  cases hregs : source.registrations with
  | nil =>
      simp [hregs] at hextract
  | cons registration rest =>
      simp [hregs] at hextract
      simpa [hregs] using
        sourceEventDenialTrace_of_extractedEventDenialTrace source
          (registration :: rest) graph hextract (by simpa [hregs] using htrace)

/-- Modeled-program failure reflection for the Lean RustHookCore extractor. -/
lemma rust_hook_modeled_program_extractor_failure_reflects_modeled_source_failure
    {property : StructuralProperty}
    (src : RustHookCore.Program) (graph : GovernanceGraph)
    (hextract : extractRustHookCore src = .ok graph)
    (hfail : ExtractedGraphFailure src.registrations graph property) :
    SourceSemanticsFailure src property := by
  let hequiv := extractRustHookCore_decision_equivalent src graph hextract
  cases property with
  | deniedSubject subject =>
      rcases hfail with ⟨profile, happears, hgraph⟩
      exact ⟨profile, happears, (hequiv profile subject).trans hgraph⟩
  | blockedSubject subject =>
      rcases hfail with ⟨profile, happears, htrace⟩
      exact ⟨profile, happears,
        sourceDenialTrace_of_extractRustHookCore src graph hextract htrace⟩
  | eventGateFailure event subject =>
      rcases hfail with ⟨profile, htrace⟩
      exact ⟨profile,
        sourceEventDenialTrace_of_extractRustHookCore src graph hextract htrace⟩

end RustHookCore
end Legitimacy
