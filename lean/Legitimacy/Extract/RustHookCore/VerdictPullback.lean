/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Diagnostics.DecisionSystem
import Legitimacy.Extract.RustHookCore.Soundness
import Legitimacy.Protocol.State
import Legitimacy.Results.GovernanceAdmissibilityAudit.Checks
import Legitimacy.Results.SelfAudit

/-!
# RustHookCore verdict pullback

This module proves the pass-direction pullback currently supported by the
modeled RustHookCore extractor: graph-level binary decision-system diagnostics
pull back to source-level diagnostics through
`extractRustHookCore_decision_equivalent`.

It does not state an *unconditional* theorem from `auditCheckStatus`. The
production verdict pullback below ranges over a `GeneratedAuditSubject` carrier
rather than an arbitrary `AuditSubject`, because `auditCheckStatus` audits
`AuditGovernanceGraph` data while RustHookCore extraction
produces the older binary `GovernanceGraph` pipeline. A structural bridge
between those graph representations is still needed before the production
admissibility verdict can be pulled back.
-/

set_option autoImplicit false

namespace Legitimacy
namespace RustHookCore

/-- Source-level certifiability for the modeled Rust hook core: the source has
a nonempty registration table, every registered hook callback resolves, and the
source semantics certifies at least one appearing claimant with a concrete
permit decision. -/
def SourceCertifiability (source : Program) : Prop :=
  source.registrations ≠ [] ∧
    (∀ registration ∈ source.registrations,
      (findHook? source.hooks registration.callback).isSome) ∧
    ∃ (profile : ClaimProfile) (subject : ClaimantId),
      SubjectAppears profile subject ∧
        DecisionSystem.decide (sourceGovernanceGraphSemantics source)
          profile subject = BinaryDecision.Permit

/-- Source-level observable determinacy for the modeled Rust hook core:
reordering the registration list does not alter external decisions. This is a
substantive source condition; it is not guaranteed by extraction equivalence. -/
def SourceObservableDeterminacy (source : Program) : Prop :=
  ∀ (registrations : List Registration),
    registrations.Perm source.registrations →
      ∀ (profile : ClaimProfile) (subject : ClaimantId),
        evalRegistrations source registrations profile subject =
          evalRustHookCore source profile subject

/-- Source-level corrigibility projection for the modeled Rust hook core: each
terminal hook result is explicitly present in a registered hook body. This
records source override surface, not the production extracted-graph
supervisory-override traversal. -/
def SourceCorrigibilityProjection (source : Program) : Prop :=
  source.registrations ≠ [] ∧
    ∀ result : HookResult,
      ∃ registration ∈ source.registrations,
        ∃ hook,
          findHook? source.hooks registration.callback = some hook ∧
            hook.body = Stmt.returnDecision result

/-- Source-level compositional-safety projection for the modeled Rust hook core:
every source registration has a resolvable callback and the source has at least
one registered component. -/
def SourceCompositionalSafetyProjection (source : Program) : Prop :=
  source.registrations ≠ [] ∧
    ∀ registration ∈ source.registrations,
      (findHook? source.hooks registration.callback).isSome

/-- Source-level nonvacuity for the modeled Rust hook core: some named claimant
in a concrete profile is permitted by the source semantics. -/
def SourceNonvacuous (source : Program) : Prop :=
  ∃ (profile : ClaimProfile) (subject : ClaimantId),
    SubjectAppears profile subject ∧
      DecisionSystem.decide (sourceGovernanceGraphSemantics source)
        profile subject = BinaryDecision.Permit

lemma extractRegistrationNodes_resolves_all
    (source : Program) :
    ∀ {registrations : List Registration} {graph : GovernanceGraph},
      extractRegistrationNodes source registrations = .ok graph →
        ∀ registration ∈ registrations,
          (findHook? source.hooks registration.callback).isSome
  | [], _, h => by
      intro registration hmem
      simp at hmem
  | registration :: rest, _, h => by
      intro candidate hmem
      unfold extractRegistrationNodes at h
      cases hnode : extractRegistrationNode source registration with
      | error error =>
          simp [hnode] at h
      | ok node =>
          cases hrest : extractRegistrationNodes source rest with
          | error error =>
              simp [hnode, hrest] at h
          | ok nodes =>
              simp [hnode, hrest] at h
              cases hmem with
              | head =>
                unfold extractRegistrationNode at hnode
                cases hhook : findHook? source.hooks registration.callback with
                | none =>
                    simp [hhook] at hnode
                | some hook =>
                    simp
              | tail _ htail =>
                  exact extractRegistrationNodes_resolves_all
                    source hrest candidate htail

lemma extractRegistrationNodes_length
    (source : Program) :
    ∀ {registrations : List Registration} {graph : GovernanceGraph},
      extractRegistrationNodes source registrations = .ok graph →
        graph.length = registrations.length
  | [], _, h => by
      simp [extractRegistrationNodes] at h
      cases h
      rfl
  | registration :: rest, _, h => by
      unfold extractRegistrationNodes at h
      cases hnode : extractRegistrationNode source registration with
      | error error =>
          simp [hnode] at h
      | ok node =>
          cases hrest : extractRegistrationNodes source rest with
          | error error =>
              simp [hnode, hrest] at h
          | ok nodes =>
              simp [hnode, hrest] at h
              cases h
              have hlen := extractRegistrationNodes_length source hrest
              simp [hlen]

lemma extractRustHookCore_length
    (source : Program) (graph : GovernanceGraph)
    (hextract : extractRustHookCore source = .ok graph) :
    graph.length = source.registrations.length := by
  unfold extractRustHookCore at hextract
  cases hregs : source.registrations with
  | nil =>
      simp [hregs] at hextract
  | cons head rest =>
      simp [hregs] at hextract
      have hlen := extractRegistrationNodes_length source hextract
      simpa [hregs] using hlen

lemma sourceRegistrations_nonempty_of_extractRustHookCore_graph_nonempty
    (source : Program) (graph : GovernanceGraph)
    (hextract : extractRustHookCore source = .ok graph)
    (hgraph : graph ≠ []) :
    source.registrations ≠ [] := by
  intro hnil
  have hlen := extractRustHookCore_length source graph hextract
  rw [hnil] at hlen
  cases graph with
  | nil =>
      exact hgraph rfl
  | cons node rest =>
      simp at hlen

lemma sourceCompositionalSafetyProjection_of_extractRustHookCore
    (source : Program) (graph : GovernanceGraph)
    (hextract : extractRustHookCore source = .ok graph) :
    SourceCompositionalSafetyProjection source := by
  constructor
  · intro hnil
    unfold extractRustHookCore at hextract
    rw [hnil] at hextract
    simp at hextract
  · intro registration hmem
    unfold extractRustHookCore at hextract
    cases hregs : source.registrations with
    | nil =>
        simp [hregs] at hextract
    | cons head rest =>
        simp [hregs] at hextract
        have hmem' : registration ∈ head :: rest := by
          simpa [hregs] using hmem
        exact extractRegistrationNodes_resolves_all
          source hextract registration hmem'

/-- Source-level interpretation of every audit-check constructor for the
modeled Rust hook core. The first four constructors are exactly the generic
binary decision-system diagnostics, so they are the part that transfers through
the extractor equivalence theorem below. -/
def AuditCheck.sourcePredicate
    (check : AuditCheck) (source : Program) : Prop :=
  match check with
  | .consistency =>
      GraphConsistencyP (sourceGovernanceGraphSemantics source)
  | .solidarity =>
      GraphSolidarityP (sourceGovernanceGraphSemantics source)
  | .monotonicity =>
      GraphMonotonicityP (sourceGovernanceGraphSemantics source)
  | .strategyproofness =>
      GraphStrategyproofnessP (sourceGovernanceGraphSemantics source)
  | .certifiability =>
      SourceCertifiability source
  | .observableDeterminacy =>
      SourceObservableDeterminacy source
  | .corrigibility =>
      SourceCorrigibilityProjection source
  | .compositionalSafety =>
      SourceCompositionalSafetyProjection source
  | .nonvacuous =>
      SourceNonvacuous source

instance : AuditSemantics Program where
  holds check source := AuditCheck.sourcePredicate check source

/-- Data-level lift from the older binary governance graph surface to the
production audit-subject surface. -/
def liftGovernanceGraphToAuditGraph (graph : GovernanceGraph) :
    AuditGovernanceGraph where
  nodes :=
    graph.map fun _ =>
      AuditGovernanceNode.binary "governance-node" "governance node"
        [] .permit .firstMatch
  edges := []

/-- Constructed audit subject associated with an extracted governance graph. -/
def liftGovernanceGraphToAuditSubject (graph : GovernanceGraph) :
    AuditSubject where
  graph := liftGovernanceGraphToAuditGraph graph
  evalNode := auditEvaluateNode

/-- A RustHookCore audit subject generated from a modeled source program. The
witness records the explicit bridge from the extracted audit data graph to
source-level predicates for all audit checks. -/
class GeneratedAuditSubject
    (source : Program) (subject : AuditSubject) where
  graph : GovernanceGraph
  extracted : extractRustHookCore source = .ok graph
  subject_embeds_graph : subject = liftGovernanceGraphToAuditSubject graph
  pass_consistency :
    auditCheckStatus subject .consistency = .ok .passed →
      auditCheckHolds .consistency graph
  pass_solidarity :
    auditCheckStatus subject .solidarity = .ok .passed →
      auditCheckHolds .solidarity graph
  pass_monotonicity :
    auditCheckStatus subject .monotonicity = .ok .passed →
      auditCheckHolds .monotonicity graph
  pass_strategyproofness :
    auditCheckStatus subject .strategyproofness = .ok .passed →
      auditCheckHolds .strategyproofness graph

/-- The audit-check constructors whose graph predicates are already expressed
over the generic binary decision-system interface and therefore pull back
through `extractRustHookCore_decision_equivalent`. -/
def AuditCheck.decisionSystemPullbackSupported : AuditCheck → Prop
  | .consistency
  | .solidarity
  | .monotonicity
  | .strategyproofness => True
  | .certifiability
  | .observableDeterminacy
  | .corrigibility
  | .compositionalSafety
  | .nonvacuous => False

/-- Pass-direction pullback for the currently supported modeled RustHookCore
checks. The premise is the theorem-facing graph predicate `auditCheckHolds`,
not `auditCheckStatus`; the production status bridge needs a structural
connection from `AuditSubject` to the binary extracted graph. -/
theorem rust_hook_kernel_check_reflects_source_protocol_satisfaction
    (source : Program)
    (graph : GovernanceGraph)
    (check : AuditCheck)
    (hextract : extractRustHookCore source = .ok graph)
    (hsupported : AuditCheck.decisionSystemPullbackSupported check)
    (hgraph : auditCheckHolds check graph) :
    AuditCheck.sourcePredicate check source := by
  let hequiv := extractRustHookCore_decision_equivalent source graph hextract
  cases check <;> simp [AuditCheck.decisionSystemPullbackSupported] at hsupported
  · exact
      (GraphConsistencyP_congr
        (DecisionSystem.Equivalent.symm hequiv)).mp
        (by
          simpa [graphConsistency_eq_graphConsistencyP]
            using hgraph)
  · exact
      (GraphSolidarityP_congr
        (DecisionSystem.Equivalent.symm hequiv)).mp
        (by
          simpa [graphSolidarity_eq_graphSolidarityP]
            using hgraph)
  · exact
      (GraphMonotonicityP_congr
        (DecisionSystem.Equivalent.symm hequiv)).mp
        (by
          simpa [graphMonotonicity_eq_graphMonotonicityP]
            using hgraph)
  · exact
      (GraphStrategyproofnessP_congr
        (DecisionSystem.Equivalent.symm hequiv)).mp
        (by
          simpa [graphStrategyproofness_eq_graphStrategyproofnessP]
            using hgraph)

theorem rust_hook_audit_holds_certifiability_reflects_source
    (source : Program) (graph : GovernanceGraph)
    (hextract : extractRustHookCore source = .ok graph)
    (hholds : auditCheckHolds .certifiability graph) :
    SourceCertifiability source := by
  change Legitimacy.GraphCertifiabilitySupport graph at hholds
  rcases hholds with ⟨hgraph_nonempty, claims, claimant,
    happears, hpermit⟩
  refine ⟨?_, ?_, ?_⟩
  · exact sourceRegistrations_nonempty_of_extractRustHookCore_graph_nonempty
      source graph hextract hgraph_nonempty
  · exact
      (sourceCompositionalSafetyProjection_of_extractRustHookCore
        source graph hextract).2
  · refine ⟨claims, claimant, happears, ?_⟩
    have hequiv := extractRustHookCore_decision_equivalent source graph hextract
    exact (hequiv claims claimant).trans hpermit

theorem rust_hook_extraction_implies_source_compositional_safety
    (source : Program) (graph : GovernanceGraph)
    (hextract : extractRustHookCore source = .ok graph) :
    SourceCompositionalSafetyProjection source := by
  exact sourceCompositionalSafetyProjection_of_extractRustHookCore
    source graph hextract

theorem rust_hook_audit_holds_nonvacuity_reflects_source
    (source : Program) (graph : GovernanceGraph)
    (hextract : extractRustHookCore source = .ok graph)
    (hholds : auditCheckHolds .nonvacuous graph) :
    SourceNonvacuous source := by
  rcases hholds with
    ⟨τ, governedClaims, permitEligibleClaims, htrace, _hgraph,
      _hgoverned, _hbounded, heligible_nonempty, _hsubset,
      hpermit, _hrefusal, _hescalation, _hdeadlock⟩
  rcases List.exists_mem_of_ne_nil permitEligibleClaims
      heligible_nonempty with ⟨claim, hclaim⟩
  rcases hpermit claim hclaim with ⟨t, ht⟩
  have hconsistent := htrace t
  rw [ht] at hconsistent
  rcases hconsistent with ⟨profile, happears, hgraph_permit⟩
  refine ⟨profile, claim.id, ?_, ?_⟩
  · exact ⟨claim, happears, rfl⟩
  · have hequiv :=
      extractRustHookCore_decision_equivalent source graph hextract
    exact (hequiv profile claim.id).trans hgraph_permit

theorem GeneratedAuditSubject.reflects
    (source : Program) (subject : AuditSubject)
    [GeneratedAuditSubject source subject]
    (check : AuditCheck)
    (hsupported : AuditCheck.decisionSystemPullbackSupported check)
    (hpass : auditCheckStatus subject check = .ok .passed) :
    AuditCheck.sourcePredicate check source := by
  let graph := GeneratedAuditSubject.graph (source := source) (subject := subject)
  have hextract : extractRustHookCore source = .ok graph :=
    GeneratedAuditSubject.extracted (source := source) (subject := subject)
  have hembed : subject = liftGovernanceGraphToAuditSubject graph :=
    GeneratedAuditSubject.subject_embeds_graph
      (source := source) (subject := subject)
  have _hembed_used : subject = liftGovernanceGraphToAuditSubject graph := hembed
  cases check
  · exact rust_hook_kernel_check_reflects_source_protocol_satisfaction
      source graph .consistency hextract trivial
      (GeneratedAuditSubject.pass_consistency hpass)
  · exact rust_hook_kernel_check_reflects_source_protocol_satisfaction
      source graph .solidarity hextract trivial
      (GeneratedAuditSubject.pass_solidarity hpass)
  · exact rust_hook_kernel_check_reflects_source_protocol_satisfaction
      source graph .monotonicity hextract trivial
      (GeneratedAuditSubject.pass_monotonicity hpass)
  · exact rust_hook_kernel_check_reflects_source_protocol_satisfaction
      source graph .strategyproofness hextract trivial
      (GeneratedAuditSubject.pass_strategyproofness hpass)
  · simp [AuditCheck.decisionSystemPullbackSupported] at hsupported
  · simp [AuditCheck.decisionSystemPullbackSupported] at hsupported
  · simp [AuditCheck.decisionSystemPullbackSupported] at hsupported
  · simp [AuditCheck.decisionSystemPullbackSupported] at hsupported
  · simp [AuditCheck.decisionSystemPullbackSupported] at hsupported

/-- Pass-direction pullback from the production audit dispatcher to the
modeled RustHookCore source semantics. The generated-subject witness is the
theorem-facing bridge between the `AuditSubject` data graph and the source
program. The conclusion is graph-diagnostic only: the five kernel axiom
constructors are properties of the induced governance structure and do not
follow from the modeled source syntax plus graph-decision equivalence. -/
theorem rust_hook_audit_pass_reflects_source_protocol_satisfaction
    (source : Program)
    (subject : AuditSubject)
    [GeneratedAuditSubject source subject]
    (check : AuditCheck)
    (hsupported : AuditCheck.decisionSystemPullbackSupported check)
    (hpass : auditCheckStatus subject check = .ok .passed) :
    AuditCheck.sourcePredicate check source :=
  GeneratedAuditSubject.reflects source subject check hsupported hpass

/-- Worked constructor-coverage surface for the RustHookCore audit pullback:
every supported graph-diagnostic check in the canonical nine-constructor order
reflects to the source predicate when its generated audit subject passes that
check. -/
theorem rust_hook_audit_pass_reflects_source_protocol_satisfaction_supported_checks
    (source : Program)
    (subject : AuditSubject)
    [GeneratedAuditSubject source subject] :
    ∀ check ∈ auditCheckOrder,
      AuditCheck.decisionSystemPullbackSupported check →
      auditCheckStatus subject check = .ok .passed →
        AuditCheck.sourcePredicate check source := by
  intro check _hmem hsupported hpass
  exact rust_hook_audit_pass_reflects_source_protocol_satisfaction
    source subject check hsupported hpass

/-- A one-hook source fixture used as a direct source-semantics example. -/
def permitOnlyHook : HookFnDecl where
  name := "permit"
  event := "pre_tool_use"
  inputType := "HookInput"
  resultType := "HookResult"
  body := Stmt.returnDecision HookResult.allow

/-- A minimal RustHookCore program that permits every modeled claimant. -/
def permitOnlyProgram : Program :=
  Program.mk [] [permitOnlyHook]
    [{ event := "pre_tool_use", callback := "permit", kind := .macro }]

/-- Direct source-level verification for the worked example, independent of
the graph-audit dispatcher. -/
theorem permitOnlyProgram_source_consistency :
    AuditCheck.sourcePredicate AuditCheck.consistency permitOnlyProgram := by
  intro claims k j hk hj hkj hdist hden
  change evalRustHookCore permitOnlyProgram claims k = BinaryDecision.Deny at hden
  simp [permitOnlyProgram, permitOnlyHook, Program.registrations, Program.hooks,
    evalRustHookCore, evalRegistrations, evalRegistration, findHook?,
    Stmt.evalDecision, Stmt.evalHookResult, HookResult.toDecision] at hden

end RustHookCore
end Legitimacy
