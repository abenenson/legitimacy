/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.CompositionalSafety
import Legitimacy.Kernel.Corrigible
import Legitimacy.Kernel.Observable
import Legitimacy.Foundations.Supervision
import Mathlib.Tactic.NormNum

/-!
# Legitimacy.Kernel.NonVacuous — Trace-based NON-VACUOUS liveness

This module replaces the earlier witness-based formulation of Axiom 5 with an
explicit trace model. A governance trace is an infinite sequence of
`(claim, decision)` observations over time, where a decision may be absent to
model deadlock.

The resulting `NonVacuous` predicate now requires:

1. a nonempty governed claim set,
2. bounded disposition for every governed claim,
3. a nonempty permit-eligible subset of governed claims,
4. exclusion of refusal, permanent escalation, and deadlock traces, and
5. a well-formed governance graph with at least one node.

The file also gives the independence witness demanded by the research note:
a deny-all machine satisfies the rewritten `Certifiable`,
`GovernanceObservable`, `Corrigible`, and boundary-relative causal
soundness interfaces, but fails `NonVacuous`.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A witness package for Axiom 5. -/
structure NonVacuousWitness (G : GovernanceGraph) (τ : GovernanceTrace) where
  wellFormed : WellFormed G
  governedClaims : List ClaimQ
  governed_nonempty : governedClaims ≠ []
  boundedDisposition : BoundedDisposition τ governedClaims
  permitEligibleClaims : List ClaimQ
  eligible_nonempty : permitEligibleClaims ≠ []
  eligible_subset : ∀ c ∈ permitEligibleClaims, c ∈ governedClaims
  permitEligible : PermitEligible τ permitEligibleClaims
  notRefusal : ¬ Refusal τ
  notPermanentEscalation : ¬ PermanentEscalation τ
  notDeadlock : ¬ Deadlock τ

/-- Axiom 5: governance must have at least one node, must resolve every claim
in a nonempty governed set within a uniform bound, must genuinely permit some
nonempty subset of those claims, and must avoid refusal, escalation forever,
and deadlock. -/
def NonVacuous (G : GovernanceGraph) (τ : GovernanceTrace) : Prop :=
  Nonempty (NonVacuousWitness G τ)

/-- Refusal traces are vacuous by definition. -/
theorem refusal_not_nonvacuous
    {G : GovernanceGraph} {τ : GovernanceTrace}
    (hrefusal : Refusal τ) :
    ¬ NonVacuous G τ := by
  intro hnv
  rcases hnv with ⟨hnv⟩
  exact hnv.notRefusal hrefusal

/-- Permanently escalatory traces are vacuous by definition. -/
lemma permanentEscalation_not_nonvacuous
    {G : GovernanceGraph} {τ : GovernanceTrace}
    (hesc : PermanentEscalation τ) :
    ¬ NonVacuous G τ := by
  intro hnv
  rcases hnv with ⟨hnv⟩
  exact hnv.notPermanentEscalation hesc

/-- Deadlocked traces are vacuous by definition. -/
lemma deadlock_not_nonvacuous
    {G : GovernanceGraph} {τ : GovernanceTrace}
    (hdead : Deadlock τ) :
    ¬ NonVacuous G τ := by
  intro hnv
  rcases hnv with ⟨hnv⟩
  exact hnv.notDeadlock hdead

/-- An empty governance graph cannot be non-vacuous: a graph with zero nodes
does not govern anything. -/
lemma empty_graph_not_nonvacuous (τ : GovernanceTrace) :
    ¬ NonVacuous ([] : GovernanceGraph) τ := by
  intro hnv
  rcases hnv with ⟨hnv⟩
  exact hnv.wellFormed rfl

/-! ## Rewritten-kernel witness components -/

/-- The canonical deny-all graph. -/
def denyAllGraph : GovernanceGraph := [overrideNode]

/-- A concrete deny-all supervisory state that still supports the full
supervisory algebra. -/
private def denyAllState : GovernanceState where
  graph := [denyNode]
  snapshot := [denyNode]
  sandboxBoundary := 1
  thresholds := [1]
  degradeFactor := 2
  reroutePrefix := [denyNode]
  rerouteWindow := 0
  paused := false
  stopped := false

/-- The deny-all supervisory state denies every claim. -/
private theorem denyAllState_denies
    (claims : List ClaimQ) (k : ClaimantId) :
    denyAllState.decide claims k = GovernanceOutcome.deny := by
  simp [GovernanceState.decide, denyAllState]
  intro _
  simp [outcomeGraphDecide, denyNode]

/-- Deny-all decisions are tagged by the fixed deny-all certificate policy. -/
inductive DenyAllWitness where
  | denyAll
  deriving Repr, DecidableEq

/-- A decision certified against the deny-all policy. -/
structure DenyAllDecision where
  claims : List ClaimQ
  claimant : ClaimantId
  outcome : GovernanceOutcome

/-- The deny-all verifier checks that the certificate names the deny-all
policy and that the reported outcome matches executing the deny-all state. -/
private def denyAllVerifier
    (d : DenyAllDecision) (w : DenyAllWitness) : Bool :=
  decide
    (w = DenyAllWitness.denyAll ∧
     d.outcome = denyAllState.decide d.claims d.claimant)

/-- Axiom 1 witness for the deny-all machine. -/
private def denyAllCertification :
    CertifiableSystem DenyAllDecision DenyAllWitness where
  legitimate d := d.outcome = denyAllState.decide d.claims d.claimant
  verifier := denyAllVerifier
  verifierSteps := fun _ _ => 1
  bound := fun _ => 1

/-- The canonical deny-all witness certificate is accepted exactly for
legitimate deny-all decisions. -/
private lemma denyAllVerifier_accepts
    (d : DenyAllDecision)
    (hlegit : denyAllCertification.legitimate d) :
    CertificateAccepted denyAllCertification d DenyAllWitness.denyAll := by
  simpa [CertificateAccepted, denyAllCertification, denyAllVerifier] using hlegit

/-- The canonical deny-all witness certificate always fits the constant
verification budget. -/
private lemma denyAllVerifier_within_bound
    (d : DenyAllDecision) :
    CertificateWithinBound denyAllCertification d DenyAllWitness.denyAll := by
  simp [CertificateWithinBound, denyAllCertification]

/-- The deny-all machine is certifiable: the certificate is simply the
deny-all policy tag, and the verifier recomputes the deny-all outcome. -/
lemma denyAll_certifiable :
    Certifiable denyAllCertification := by
  intro d hlegit
  refine ⟨DenyAllWitness.denyAll, ?_, ?_⟩
  · exact denyAllVerifier_accepts d hlegit
  · exact denyAllVerifier_within_bound d

/-- The deny-all machine is governance-observable because the principal sees
the full governance state directly. -/
lemma denyAll_observable :
    GovernanceObservable governanceAnswer governanceAnswer
      (fun s : ObservableGovernanceState => s) := by
  intro q s
  rfl

/-- The full supervisory algebra. -/
private def fullSupervisoryAlgebra : SupervisoryAlgebra := Set.univ

/-- A single inert self-modification action. -/
private def idActionSpace : StateActionSpace where
  Action := Unit
  apply _ S := S

/-- Every supervisory action is supported in the concrete deny-all state. -/
private lemma denyAllState_supports
    (σ : SupervisoryAction) :
    SupportsSupervisory denyAllState σ := by
  cases σ <;> simp [SupportsSupervisory, denyAllState]

/-- The deny-all supervisory state supports every supervisory action. -/
private theorem denyAllState_supports_full_algebra :
    SupportsAlgebra denyAllState fullSupervisoryAlgebra := by
  intro σ _
  exact denyAllState_supports σ

/-- The inert self-modification space preserves any supported algebra. -/
private theorem idActionSpace_single_step_preserved
    (alg : SupervisoryAlgebra) :
    SingleStepPreserved idActionSpace alg := by
  intro a S hsupports
  simpa [idActionSpace] using hsupports

/-- The deny-all supervisory state is corrigible for the full
supervisory algebra. -/
lemma denyAll_corrigible :
    Corrigible denyAllState idActionSpace fullSupervisoryAlgebra where
  supports_algebra := denyAllState_supports_full_algebra
  single_step_preserved := idActionSpace_single_step_preserved fullSupervisoryAlgebra

/-- A causal model with no edges. -/
private def denyAllNoEdge : Fin 1 → Fin 1 → Prop := fun _ _ => False

private instance denyAllNoEdge_dec : DecidableRel denyAllNoEdge := by
  intro _ _
  unfold denyAllNoEdge
  infer_instance

/-- With no causal edges, boundary-relative safety is trivially preserved. -/
private def denyAllDAG : CausalDAG 1 where
  edge := denyAllNoEdge
  acyclic := by
    intro i j hedge
    cases hedge
  edge_dec := denyAllNoEdge_dec

/-- A concrete nonempty boundary for the deny-all causal witness. -/
private def denyAllGoverned : GovernedSet 1 where
  governed := fun _ => True
  dec := by
    intro _
    infer_instance

/-- With no causal edges, the internal governed-edge closure condition is
vacuous. -/
private lemma denyAll_governedEdgeClosed
    (gov : GovernedSet 1) (safety : BoundarySafety gov.boundary) :
    GovernedEdgeClosed denyAllDAG gov safety := by
  intro v w hv hw hedge hsafe
  cases hedge

/-- With no causal edges, the boundary-contract obligation is also vacuous. -/
private lemma denyAll_boundaryContract
    (gov : GovernedSet 1) (safety : BoundarySafety gov.boundary) :
    BoundaryContract denyAllDAG gov safety := by
  intro v mid w hv hw hmid hedge hreach hsafe
  cases hedge

/-- In the no-edge causal model, every boundary-relative safety predicate is
closed under governance because there are no internal edges and no boundary
exits to discharge. -/
private theorem denyAll_boundary_relative_closed
    (gov : GovernedSet 1) :
    ∀ safety : BoundarySafety gov.boundary,
      BoundaryRelativeClosed denyAllDAG gov safety := by
  intro safety
  constructor
  · exact denyAll_governedEdgeClosed gov safety
  · exact denyAll_boundaryContract gov safety

/-- The deny-all causal witness is boundary-relative safe for any declared
boundary on the no-edge model. -/
lemma denyAll_boundary_relative_safe
    (gov : GovernedSet 1) :
    CausalSoundness denyAllDAG gov :=
  causal_closure_sufficient denyAllDAG gov
    (denyAll_boundary_relative_closed gov)

/-- The deny-all machine satisfies the four non-liveness axioms using the
rewritten kernel interfaces. -/
lemma denyAll_satisfies_rewritten_axioms :
    Certifiable denyAllCertification ∧
    GovernanceObservable governanceAnswer governanceAnswer
      (fun s : ObservableGovernanceState => s) ∧
    Corrigible denyAllState idActionSpace fullSupervisoryAlgebra ∧
    CausalSoundness denyAllDAG denyAllGoverned := by
  exact ⟨denyAll_certifiable, denyAll_observable,
    denyAll_corrigible,
    denyAll_boundary_relative_safe denyAllGoverned⟩

/-! ## Independence witness -/

private def witnessClaim : ClaimQ := ⟨0, 1, by norm_num, []⟩

/-- The operational trace of a deny-all machine: every observed claim is
denied immediately. -/
def denyAllTrace : GovernanceTrace :=
  fun _ => (witnessClaim, some GovernanceOutcome.deny)

/-- The deny-all trace is a refusal trace. -/
lemma denyAllTrace_refusal : Refusal denyAllTrace := by
  intro t
  rfl

/-- A deny-all machine satisfies axioms 1–4 but fails NON-VACUOUS. This is
the concrete independence witness demanded by the research note. -/
theorem deny_all_independence_counterexample :
    (Certifiable denyAllCertification ∧
     GovernanceObservable governanceAnswer governanceAnswer
       (fun s : ObservableGovernanceState => s) ∧
     Corrigible denyAllState idActionSpace fullSupervisoryAlgebra ∧
     CausalSoundness denyAllDAG denyAllGoverned) ∧
    ¬ NonVacuous denyAllGraph denyAllTrace := by
  refine ⟨denyAll_satisfies_rewritten_axioms, ?_⟩
  exact refusal_not_nonvacuous denyAllTrace_refusal

end Legitimacy
