/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Behavioral.Constitution
import Legitimacy.Behavioral.SpectralEmbedding
import Legitimacy.Spectral.Channels.CStarChannelBridge
import Legitimacy.Spectral.Certificates.PositiveProcedureCertificate
import Mathlib.Tactic

/-!
# Constitutional AI behavioral lineage

This module formalizes a deployment-side realization for
Constitutional-AI-trained audit subjects. The claim layer is a quotient of a
finite constitution-as-DAG: each audited claim resolves to the most
authoritative applicable principle, and the legacy harm/benign predicates are
compatibility projections from the resolved principle's binary verdict.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

/-- Deployment decisions exposed by a Constitutional-AI-trained audit subject.
`escalate` and `deny` both compile to a binary denial at the governance graph
surface, but they remain distinct audit labels. -/
inductive ConstitutionalAIDecision where
  | permit : ConstitutionalAIDecision
  | escalate : ConstitutionalAIDecision
  | deny : ConstitutionalAIDecision
  deriving Repr, DecidableEq

namespace ConstitutionalAIDecision

/-- Binary governance projection for the deployment-side decision label. -/
def toBinary : ConstitutionalAIDecision → BinaryDecision
  | permit => BinaryDecision.Permit
  | escalate => BinaryDecision.Deny
  | deny => BinaryDecision.Deny

@[simp] lemma toBinary_permit :
    ConstitutionalAIDecision.permit.toBinary = BinaryDecision.Permit :=
  rfl

@[simp] lemma toBinary_escalate :
    ConstitutionalAIDecision.escalate.toBinary = BinaryDecision.Deny :=
  rfl

@[simp] lemma toBinary_deny :
    ConstitutionalAIDecision.deny.toBinary = BinaryDecision.Deny :=
  rfl

end ConstitutionalAIDecision

/-- Constitutional AI claim classes are quotient classes induced by
principle-conflict resolution. `HarmCategoricalClaim` and `BenignClaim` remain
as compatibility projections for older deployment-policy theorems, but their
meaning is fixed by the resolved principle's verdict. -/
structure ConstitutionalAIClaimClass (n : Nat) where
  constitution : Constitution n
  HarmCategoricalClaim : Fin n → Prop
  BenignClaim : Fin n → Prop
  harm_iff_resolved_denies :
    ∀ claim, HarmCategoricalClaim claim ↔
      (constitution.resolvedPrinciple claim).verdict = BinaryDecision.Deny
  benign_iff_resolved_permits :
    ∀ claim, BenignClaim claim ↔
      (constitution.resolvedPrinciple claim).verdict = BinaryDecision.Permit
  exhaustive : ∀ claim, HarmCategoricalClaim claim ∨ BenignClaim claim
  disjoint : ∀ claim, ¬ (HarmCategoricalClaim claim ∧ BenignClaim claim)

namespace ConstitutionalAIClaimClass

variable {n : Nat} (C : ConstitutionalAIClaimClass n)

/-- The quotient type of audited claims under constitutional resolution. -/
abbrev ClaimQuotient : Type :=
  C.constitution.ClaimQuotient

/-- Quotient class of a concrete audited claim. -/
def quotientClass (claim : Fin n) : C.ClaimQuotient :=
  C.constitution.claimClass claim

theorem same_quotientClass_iff_resolved_eq (a b : Fin n) :
    C.quotientClass a = C.quotientClass b ↔
      C.constitution.resolvedPrinciple a =
        C.constitution.resolvedPrinciple b :=
  C.constitution.same_claimClass_iff_resolved_eq a b

/-- Harm-categorical and benign sides are mutually exclusive. -/
lemma not_benign_of_harm {claim : Fin n}
    (hharm : C.HarmCategoricalClaim claim) :
    ¬ C.BenignClaim claim := by
  intro hbenign
  exact C.disjoint claim ⟨hharm, hbenign⟩

/-- The benign side is the residual class once harm-categorical status is
excluded. -/
lemma benign_of_not_harm {claim : Fin n}
    (hnot : ¬ C.HarmCategoricalClaim claim) :
    C.BenignClaim claim := by
  rcases C.exhaustive claim with hharm | hbenign
  · exact False.elim (hnot hharm)
  · exact hbenign

/-- Backward-compatible constructor: the old flat harm/benign partition is the
two-principle constitution with benign below harm. -/
noncomputable def ofFlat
    (HarmCategoricalClaim BenignClaim : Fin n → Prop)
    (exhaustive : ∀ claim, HarmCategoricalClaim claim ∨ BenignClaim claim)
    (disjoint : ∀ claim, ¬ (HarmCategoricalClaim claim ∧ BenignClaim claim)) :
    ConstitutionalAIClaimClass n where
  constitution :=
    Constitution.flatHarmBenignConstitution
      HarmCategoricalClaim BenignClaim exhaustive disjoint
  HarmCategoricalClaim := HarmCategoricalClaim
  BenignClaim := BenignClaim
  harm_iff_resolved_denies := by
    classical
    intro claim
    constructor
    · intro hharm
      simp [Constitution.flatHarmBenignConstitution, hharm,
        Constitution.harmPrinciple]
    · intro hresolved
      by_cases hharm : HarmCategoricalClaim claim
      · exact hharm
      · simp [Constitution.flatHarmBenignConstitution, hharm,
          Constitution.benignPrinciple] at hresolved
  benign_iff_resolved_permits := by
    classical
    intro claim
    constructor
    · intro hbenign
      by_cases hharm : HarmCategoricalClaim claim
      · exact False.elim (disjoint claim ⟨hharm, hbenign⟩)
      · simp [Constitution.flatHarmBenignConstitution, hharm,
          Constitution.benignPrinciple]
    · intro hresolved
      by_cases hharm : HarmCategoricalClaim claim
      · simp [Constitution.flatHarmBenignConstitution, hharm,
          Constitution.harmPrinciple] at hresolved
      · rcases exhaustive claim with h | h
        · exact False.elim (hharm h)
        · exact h
  exhaustive := exhaustive
  disjoint := disjoint

theorem ofFlat_constitution_substantive
    (HarmCategoricalClaim BenignClaim : Fin n → Prop)
    (exhaustive : ∀ claim, HarmCategoricalClaim claim ∨ BenignClaim claim)
    (disjoint : ∀ claim, ¬ (HarmCategoricalClaim claim ∧ BenignClaim claim)) :
    ((ofFlat HarmCategoricalClaim BenignClaim exhaustive disjoint).constitution).Substantive :=
  Constitution.flatHarmBenignConstitution_substantive
    HarmCategoricalClaim BenignClaim exhaustive disjoint

end ConstitutionalAIClaimClass

/-- A deployment policy escalates or denies harm-categorical claims and permits
benign claims. This is the class predicate for the audit graph; it does not
encode any spectral embedding field. -/
def ConstitutionalAITrainedAuditSubject
    {n : Nat} (C : ConstitutionalAIClaimClass n)
    (policy : Fin n → ConstitutionalAIDecision) : Prop :=
  (∀ claim, C.HarmCategoricalClaim claim →
    policy claim = ConstitutionalAIDecision.escalate ∨
      policy claim = ConstitutionalAIDecision.deny) ∧
  (∀ claim, C.BenignClaim claim →
    policy claim = ConstitutionalAIDecision.permit)

/-- A deployment policy respects principle-conflict resolution when the binary
decision it exposes is exactly the verdict of the claim's resolved principle. -/
def ConstitutionallyRespectsResolution
    {n : Nat} (C : ConstitutionalAIClaimClass n)
    (policy : Fin n → ConstitutionalAIDecision) : Prop :=
  ∀ claim : Fin n,
    (policy claim).toBinary =
      (C.constitution.resolvedPrinciple claim).verdict

/-- A policy that follows the resolved constitutional principle for every claim
is a trained audit subject in the constitutional-AI lineage model. -/
theorem ConstitutionalAITrainedAuditSubject_of_respects_resolution
    {n : Nat} (C : ConstitutionalAIClaimClass n)
    (policy : Fin n → ConstitutionalAIDecision)
    (hrespect : ConstitutionallyRespectsResolution C policy) :
    ConstitutionalAITrainedAuditSubject C policy := by
  constructor
  · intro claim hharm
    have hresolved := (C.harm_iff_resolved_denies claim).mp hharm
    have hbinary : (policy claim).toBinary = BinaryDecision.Deny := by
      rw [hrespect claim, hresolved]
    cases hpolicy : policy claim with
    | permit =>
        simp [hpolicy, ConstitutionalAIDecision.toBinary] at hbinary
    | escalate =>
        exact Or.inl rfl
    | deny =>
        exact Or.inr rfl
  · intro claim hbenign
    have hresolved := (C.benign_iff_resolved_permits claim).mp hbenign
    have hbinary : (policy claim).toBinary = BinaryDecision.Permit := by
      rw [hrespect claim, hresolved]
    cases hpolicy : policy claim with
    | permit =>
        exact rfl
    | escalate =>
        simp [hpolicy, ConstitutionalAIDecision.toBinary] at hbinary
    | deny =>
        simp [hpolicy, ConstitutionalAIDecision.toBinary] at hbinary

/-- Concrete deployment-side lineage for a Constitutional-AI-trained audit
subject. The Constitutional AI training method is represented only through
the deployed harm-categorical policy; the spectral fields are derived later
from the graph/action dynamics. -/
structure ConstitutionalAIBehavioralLineage (n : Nat) [NeZero n] where
  G : GovGraph ℚ n
  s : Fin n → ℚ
  claimClass : ConstitutionalAIClaimClass n
  policy : Fin n → ConstitutionalAIDecision
  policy_rule : ConstitutionalAITrainedAuditSubject claimClass policy

/-- Capability-scaled deployment datum for Constitutional-AI-shaped audit
subjects. The fields are deliberately deployment-side: the trained policy is
kept as a label-sensitive behavioral lineage, while `δ` and the audit amplitude
budget expose the graph-derived `C_star` channel. -/
structure ConstitutionalAICapacityLineage (n : Nat) [NeZero n] where
  lineage : ConstitutionalAIBehavioralLineage n
  δ : ℚ
  δ_pos : 0 < δ
  cv_pos : 0 < lineage.G.cv lineage.s
  auditAmplitudeBudget : ℚ
  auditAmplitudeBudget_pos : 0 < auditAmplitudeBudget

namespace ConstitutionalAICapacityLineage

variable {n : Nat} [NeZero n] (L : ConstitutionalAICapacityLineage n)

/-- Capability-response channel inherited from the underlying graph/signal. -/
noncomputable def capabilityResponse (C : ℚ) : BinaryDecision :=
  L.lineage.G.capabilityResponse L.lineage.s L.δ C

/-- Graph-derived critical capability for the CAI deployment substrate. -/
noncomputable def C_star : ℚ :=
  Legitimacy.C_star L.lineage.G L.lineage.s L.δ

/-- Spectral violation predicate inherited from the underlying graph/signal. -/
def spViolation (γ : ℚ) : Prop :=
  L.lineage.G.spViolation L.lineage.s γ

/-- The capacity wrapper is label-sensitive: changing a deployed policy label
at any state changes the wrapped capacity lineage, even when the graph and
claim partition are otherwise the same. -/
theorem profile_sensitive_policy_label
    {L₁ L₂ : ConstitutionalAICapacityLineage n} {state : Fin n}
    (hpolicy :
      L₁.lineage.policy state ≠ L₂.lineage.policy state) :
    L₁ ≠ L₂ := by
  intro hsame
  exact hpolicy (congrFun (congrArg (fun L => L.lineage.policy) hsame) state)

/-- Harm-categorical claims remain denied by the deployed CAI policy. The proof
is policy-only: escalation and denial both compile to binary denial. -/
theorem cai_harm_categorical_policy_denies
    {state : Fin n} (hharm : L.lineage.claimClass.HarmCategoricalClaim state) :
    (L.lineage.policy state).toBinary = BinaryDecision.Deny := by
  rcases L.lineage.policy_rule.1 state hharm with h | h
  · simp [h]
  · simp [h]

/-- For benign claims, matching the deployed permit decision is exactly the
`C_star` capability-response transition. -/
theorem cai_capabilityBoundary_benign_response_matches_C_star
    {state : Fin n} (hbenign : L.lineage.claimClass.BenignClaim state)
    {C : ℚ} (hC : 0 < C) :
    L.capabilityResponse C = (L.lineage.policy state).toBinary ↔
      L.C_star ≤ C := by
  rw [L.lineage.policy_rule.2 state hbenign]
  simpa [capabilityResponse, C_star] using
    L.lineage.G.capabilityResponse_eq_permit_iff_C_star_le
      L.lineage.s L.δ C L.δ_pos L.cv_pos hC

/-- Generic benign-boundary predicate for checking policy-level vacuity. -/
def BenignBoundaryPolicyMatches
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (δ : ℚ)
    (claimClass : ConstitutionalAIClaimClass n)
    (policy : Fin n → ConstitutionalAIDecision) : Prop :=
  ∀ state C, claimClass.BenignClaim state → 0 < C →
    (G.capabilityResponse s δ C = (policy state).toBinary ↔
      Legitimacy.C_star G s δ ≤ C)

/-- Constant-deny policy used as a floor test: it has the same claim-partition
shape but cannot satisfy the benign `C_star` transition. -/
def constantDenyPolicy (_state : Fin n) : ConstitutionalAIDecision :=
  ConstitutionalAIDecision.deny

/-- Floor test for the asymmetric boundary theorem: an always-deny policy is
rejected whenever the claim partition contains a benign state, because at
`C_star` the capability response permits while the policy still denies. -/
theorem constant_deny_policy_fails_benign_boundary
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (δ : ℚ)
    (claimClass : ConstitutionalAIClaimClass n)
    (hδ : 0 < δ) (hcv : 0 < G.cv s)
    (hbenign_exists : ∃ state : Fin n, claimClass.BenignClaim state) :
    ¬ BenignBoundaryPolicyMatches G s δ claimClass
      (constantDenyPolicy (n := n)) := by
  intro hmatches
  rcases hbenign_exists with ⟨state, hbenign⟩
  have hCstar_pos : 0 < Legitimacy.C_star G s δ := by
    simpa [Legitimacy.C_star] using div_pos hδ hcv
  have hmatches_at_boundary :=
    hmatches state (Legitimacy.C_star G s δ) hbenign hCstar_pos
  have hpermit :
      G.capabilityResponse s δ (Legitimacy.C_star G s δ) =
        BinaryDecision.Permit := by
    exact
      (G.capabilityResponse_eq_permit_iff_C_star_le s δ
        (Legitimacy.C_star G s δ) hδ hcv hCstar_pos).mpr le_rfl
  have hdeny :
      G.capabilityResponse s δ (Legitimacy.C_star G s δ) =
        BinaryDecision.Deny := by
    exact hmatches_at_boundary.mpr le_rfl
  rw [hpermit] at hdeny
  cases hdeny

end ConstitutionalAICapacityLineage

namespace ConstitutionalAIBehavioralLineage

variable {n : Nat} [NeZero n] (L : ConstitutionalAIBehavioralLineage n)

/-- Structural perturbation budget for an audited claim-state. As in the
Stackelberg lineage, this is a derived deployment-side budget from the spectral
node-removal witness, not a bundled embedding field. -/
def perturbationBudget (k i : Fin n) : ℚ :=
  |L.G.gov L.s i - L.G.govRemoved L.s k i|

/-- An executable audit action by agent `k`: select a claim-state and a
nonnegative amplitude bounded by the structural perturbation budget. -/
abbrev Action (k : Fin n) : Type :=
  Σ i : Fin n, {η : ℚ // 0 ≤ η ∧ η ≤ L.perturbationBudget k i}

/-- Target claim-state selected by an executable Constitutional AI audit
action. -/
def actionTarget {k : Fin n} (a : L.Action k) : Fin n :=
  a.1

/-- Amplitude selected by an executable Constitutional AI audit action. -/
def actionAmplitude {k : Fin n} (a : L.Action k) : ℚ :=
  a.2.1

/-- The zero-amplitude action used for baseline profiles. -/
def zeroAction (k : Fin n) : L.Action k :=
  ⟨k, ⟨0, by
    constructor
    · exact le_rfl
    · exact abs_nonneg _⟩⟩

/-- The all-zero baseline profile for the Constitutional AI audit lineage. -/
def zeroProfile : ActionProfile L.Action :=
  fun k => L.zeroAction k

/-- Replace one agent action in a dependent action profile. -/
def replaceAction (base : ActionProfile L.Action)
    (k : Fin n) (action : L.Action k) : ActionProfile L.Action :=
  fun j => if h : j = k then h.symm ▸ action else base j

/-- Binary decision exposed by the deployment policy at a claim-state. -/
def deploymentBinaryDecision (state : Fin n) : BinaryDecision :=
  (L.policy state).toBinary

/-- Harm-categorical claims are escalated or denied by the deployed policy. -/
theorem policy_escalates_or_denies_harm_categorical
    {state : Fin n}
    (hharm : L.claimClass.HarmCategoricalClaim state) :
    L.policy state = ConstitutionalAIDecision.escalate ∨
      L.policy state = ConstitutionalAIDecision.deny :=
  L.policy_rule.1 state hharm

/-- Benign claims are permitted by the deployed policy. -/
theorem policy_permits_benign
    {state : Fin n}
    (hbenign : L.claimClass.BenignClaim state) :
    L.policy state = ConstitutionalAIDecision.permit :=
  L.policy_rule.2 state hbenign

/-- At the binary governance surface, harm-categorical Constitutional AI
decisions are denials: direct denial and escalation both block deployment. -/
theorem deploymentBinaryDecision_harm_categorical
    {state : Fin n}
    (hharm : L.claimClass.HarmCategoricalClaim state) :
    L.deploymentBinaryDecision state = BinaryDecision.Deny := by
  rcases L.policy_escalates_or_denies_harm_categorical hharm with h | h
  · simp [deploymentBinaryDecision, h]
  · simp [deploymentBinaryDecision, h]

/-- At the binary governance surface, benign claims are permitted. -/
theorem deploymentBinaryDecision_benign
    {state : Fin n}
    (hbenign : L.claimClass.BenignClaim state) :
    L.deploymentBinaryDecision state = BinaryDecision.Permit := by
  simp [deploymentBinaryDecision, L.policy_permits_benign hbenign]

/-- Behavioral game generated by the Constitutional AI deployment audit
lineage. Positive target-matching executable audit actions receive exactly
their structural amplitude; the governance decision is the fixed deployed
Constitutional AI policy for that claim-state. -/
def toGame : BehavioralGovernanceGame where
  Agents := Fin n
  State := Fin n
  Action := L.Action
  Utility := fun k state profile =>
    if L.actionTarget (profile k) = state then
      L.actionAmplitude (profile k)
    else
      0
  Transition := fun state _profile => state
  Observation := fun _agent _state => ObservationType.Public
  GovernanceDecision := fun state profile agent =>
    if 0 < L.actionAmplitude (profile agent) ∧
        L.actionTarget (profile agent) = state then
      L.deploymentBinaryDecision state
    else
      BinaryDecision.Deny

section SupportLemmas

variable {L}

/-- Every concrete audit perturbation is bounded by the graph-wide consistency
vulnerability. -/
lemma single_audit_perturbation_le_cv (k i : Fin n) :
    L.perturbationBudget k i ≤ L.G.cv L.s := by
  simpa [perturbationBudget] using L.G.perturb_le_cv L.s k i

@[simp] lemma actionTarget_mk
    (k i : Fin n)
    (η : {η : ℚ // 0 ≤ η ∧ η ≤ L.perturbationBudget k i}) :
    L.actionTarget (k := k) ⟨i, η⟩ = i :=
  rfl

@[simp] lemma actionAmplitude_mk
    (k i : Fin n)
    (η : {η : ℚ // 0 ≤ η ∧ η ≤ L.perturbationBudget k i}) :
    L.actionAmplitude (k := k) ⟨i, η⟩ = η.1 :=
  rfl

lemma actionAmplitude_nonneg {k : Fin n} (action : L.Action k) :
    0 ≤ L.actionAmplitude action :=
  action.2.2.1

lemma actionAmplitude_le_budget {k : Fin n} (action : L.Action k) :
    L.actionAmplitude action ≤ L.perturbationBudget k (L.actionTarget action) :=
  action.2.2.2

@[simp] lemma zeroAction_target (k : Fin n) :
    L.actionTarget (L.zeroAction k) = k :=
  rfl

@[simp] lemma zeroAction_amplitude (k : Fin n) :
    L.actionAmplitude (L.zeroAction k) = 0 :=
  rfl

@[simp] lemma zeroProfile_apply (k : Fin n) :
    L.zeroProfile k = L.zeroAction k :=
  rfl

@[simp] lemma replaceAction_self
    (base : ActionProfile L.Action) (k : Fin n) (action : L.Action k) :
    L.replaceAction base k action k = action := by
  simp [replaceAction]

lemma replaceAction_of_ne
    (base : ActionProfile L.Action) {k j : Fin n} (action : L.Action k)
    (hjk : j ≠ k) :
    L.replaceAction base k action j = base j := by
  simp [replaceAction, hjk]

lemma replaceAction_unilateral
    (base : ActionProfile L.Action) (k : Fin n) (action : L.Action k) :
    ∀ j : Fin n, j ≠ k → L.replaceAction base k action j = base j :=
  fun _ hj => L.replaceAction_of_ne base action hj

@[simp] lemma utility_eq_amplitude_of_target
    {k i : Fin n} {profile : ActionProfile L.Action}
    (h : L.actionTarget (profile k) = i) :
    L.toGame.Utility k i profile = L.actionAmplitude (profile k) := by
  simp [toGame, h]

@[simp] lemma utility_eq_zero_of_ne
    {k i : Fin n} {profile : ActionProfile L.Action}
    (h : L.actionTarget (profile k) ≠ i) :
    L.toGame.Utility k i profile = 0 := by
  simp [toGame, h]

@[simp] lemma zeroProfile_utility (k i : Fin n) :
    L.toGame.Utility k i L.zeroProfile = 0 := by
  by_cases h : k = i
  · subst h
    simp [toGame, zeroProfile, zeroAction]
  · simp [toGame, zeroProfile, zeroAction, h]

/-- Positive target-matching audit actions expose the fixed deployment
decision for that claim-state. -/
@[simp] lemma governanceDecision_positive_target
    {k i : Fin n} {action : L.Action k}
    (hpos : 0 < L.actionAmplitude action)
    (htarget : L.actionTarget action = i)
    (base : ActionProfile L.Action) :
    L.toGame.GovernanceDecision i (L.replaceAction base k action) k =
      L.deploymentBinaryDecision i := by
  simp [toGame, hpos, htarget]

/-- Zero executable audit actions are denied by the thresholded graph surface. -/
@[simp] lemma governanceDecision_zero_self
    (k i : Fin n) :
    L.toGame.GovernanceDecision i L.zeroProfile k = BinaryDecision.Deny := by
  simp [toGame, zeroProfile, zeroAction]

/-- In the harm-categorical subgame, the Constitutional AI deployment policy
matches the game-theoretic best-response surface: a positive target-matching
audit action produces a binary denial. -/
theorem harmCategorical_subgame_decision_matches_best_response
    {k i : Fin n} {action : L.Action k}
    (hpos : 0 < L.actionAmplitude action)
    (htarget : L.actionTarget action = i)
    (hharm : L.claimClass.HarmCategoricalClaim i)
    (base : ActionProfile L.Action) :
    L.toGame.GovernanceDecision i (L.replaceAction base k action) k =
      BinaryDecision.Deny := by
  rw [L.governanceDecision_positive_target hpos htarget base]
  exact L.deploymentBinaryDecision_harm_categorical hharm

/-- In the benign subgame, the same deployment policy permits positive
target-matching audit actions. -/
theorem benign_subgame_decision_matches_best_response
    {k i : Fin n} {action : L.Action k}
    (hpos : 0 < L.actionAmplitude action)
    (htarget : L.actionTarget action = i)
    (hbenign : L.claimClass.BenignClaim i)
    (base : ActionProfile L.Action) :
    L.toGame.GovernanceDecision i (L.replaceAction base k action) k =
      BinaryDecision.Permit := by
  rw [L.governanceDecision_positive_target hpos htarget base]
  exact L.deploymentBinaryDecision_benign hbenign

/-- Utility gain from replacing the zero action by a target-matching action is
exactly its executable perturbation amplitude. -/
lemma utilityGain_zero_to_action
    {k i : Fin n} {action : L.Action k}
    (htarget : L.actionTarget action = i) :
    L.toGame.utilityGain k i L.zeroProfile
      (L.replaceAction L.zeroProfile k action) =
        L.actionAmplitude action := by
  simp [BehavioralGovernanceGame.utilityGain, htarget, sub_eq_add_neg]

/-- A positive `min` of two positive rational scales remains positive. -/
lemma rat_min_pos {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    0 < min a b := by
  rw [lt_min_iff]
  exact ⟨ha, hb⟩

end SupportLemmas

section ForwardFields

variable {L}

lemma utility_nonneg (k i : Fin n) (profile : ActionProfile L.Action) :
    0 ≤ L.toGame.Utility k i profile := by
  by_cases h : L.actionTarget (profile k) = i
  · simp [toGame, h, L.actionAmplitude_nonneg (profile k)]
  · simp [toGame, h]

lemma utility_le_budget_at_state
    (k i : Fin n) (profile : ActionProfile L.Action) :
    L.toGame.Utility k i profile ≤ L.perturbationBudget k i := by
  by_cases h : L.actionTarget (profile k) = i
  · simpa [toGame, h] using L.actionAmplitude_le_budget (profile k)
  · exact le_trans (by simp [toGame, h]) (abs_nonneg _)

/-- Every profitable best-response gain in the Constitutional AI audit lineage
is reflected by the graph's structural perturbation budget. -/
theorem perturbation_budget_reflects_best_response_gain
    {κ : ℚ} (dev : L.toGame.ProfitableDeviation κ) :
    L.G.spViolation L.s dev.gain := by
  refine ⟨(dev.agent, dev.state), ?_⟩
  have hbase_nonneg :
      0 ≤ L.toGame.Utility dev.agent dev.state dev.base :=
    L.utility_nonneg dev.agent dev.state dev.base
  have hgain_le_deviated :
      dev.gain ≤ L.toGame.Utility dev.agent dev.state dev.deviated := by
    unfold BehavioralGovernanceGame.ProfitableDeviation.gain
    unfold BehavioralGovernanceGame.utilityGain
    linarith
  have hdeviated_budget :
      L.toGame.Utility dev.agent dev.state dev.deviated ≤
        L.perturbationBudget dev.agent dev.state :=
    L.utility_le_budget_at_state dev.agent dev.state dev.deviated
  exact le_trans hgain_le_deviated hdeviated_budget

/-- Game-level decision flips in the Constitutional AI deployment audit graph
match spectral perturbation witnesses at the same gain scale. -/
theorem graph_decision_matches_game
    {κ : ℚ} (dev : L.toGame.ProfitableDeviation κ)
    (_hflip :
      L.toGame.GovernanceDecision dev.state dev.deviated dev.agent ≠
        L.toGame.GovernanceDecision dev.state dev.base dev.agent) :
    L.G.spViolation L.s dev.gain :=
  L.perturbation_budget_reflects_best_response_gain dev

end ForwardFields

section ReverseFields

variable {L}

/-- Construct an executable audit action from a positive rational amplitude
bounded by the Constitutional AI structural perturbation budget. -/
def executableAction
    (k i : Fin n) (η : ℚ)
    (hη : 0 < η) (hbudget : η ≤ L.perturbationBudget k i) :
    L.Action k :=
  ⟨i, ⟨η, ⟨le_of_lt hη, hbudget⟩⟩⟩

@[simp] lemma executableAction_target
    (k i : Fin n) (η : ℚ)
    (hη : 0 < η) (hbudget : η ≤ L.perturbationBudget k i) :
    L.actionTarget (L.executableAction k i η hη hbudget) = i :=
  rfl

@[simp] lemma executableAction_amplitude
    (k i : Fin n) (η : ℚ)
    (hη : 0 < η) (hbudget : η ≤ L.perturbationBudget k i) :
    L.actionAmplitude (L.executableAction k i η hη hbudget) = η :=
  rfl

/-- Any positive amplitude bounded by a structural perturbation budget yields a
profitable unilateral audit deviation at every capability that can pay for
that amplitude. -/
def profitableDeviationOfBudget
    {κ η : ℚ} {k i : Fin n}
    (hη : 0 < η)
    (hcapability : η ≤ κ)
    (hbudget : η ≤ L.perturbationBudget k i) :
    L.toGame.ProfitableDeviation κ where
  agent := k
  state := i
  base := L.zeroProfile
  deviated := L.replaceAction L.zeroProfile k
    (L.executableAction k i η hη hbudget)
  unilateral := L.replaceAction_unilateral L.zeroProfile k
    (L.executableAction k i η hη hbudget)
  positive_gain := by
    simpa using
      (show 0 <
        L.toGame.utilityGain k i L.zeroProfile
          (L.replaceAction L.zeroProfile k
            (L.executableAction k i η hη hbudget)) by
        rw [L.utilityGain_zero_to_action]
        · simp [executableAction, hη]
        · simp [executableAction])
  capability_feasible := by
    rw [L.utilityGain_zero_to_action]
    · simpa [executableAction] using hcapability
    · simp [executableAction]

/-- Every positive spectral vulnerability in the Constitutional AI audit
lineage exposes a concrete profitable behavioral deviation. -/
theorem spectral_vulnerability_exposes_profitable_deviation
    (_hregular : L.toGame.BestResponseDecomposedRegularity)
    {γ : ℚ} (hγ : 0 < γ) (hviol : L.G.spViolation L.s γ) :
    ∃ κ : ℚ, 0 < κ ∧
      ∃ _dev : L.toGame.ProfitableDeviation κ, True := by
  rcases hviol with ⟨p, hp⟩
  refine ⟨γ, hγ, ?_⟩
  exact ⟨L.profitableDeviationOfBudget hγ le_rfl hp, trivial⟩

/-- A spectral violation at the normalized stability threshold exposes a
capability-feasible profitable deviation in the Constitutional AI audit
lineage. -/
theorem spectral_threshold_violation_exposes_profitable_deviation
    (_hregular : L.toGame.BestResponseDecomposedRegularity)
    {δ κ : ℚ} (hκ : 0 < κ) (hδ : 0 < δ)
    (hviol : L.G.spViolation L.s (δ / κ)) :
    ∃ _dev : L.toGame.ProfitableDeviation κ, True := by
  rcases hviol with ⟨p, hp⟩
  let η : ℚ := min (δ / κ) κ
  have hscale : 0 < δ / κ := div_pos hδ hκ
  have hη : 0 < η := rat_min_pos hscale hκ
  have hη_capability : η ≤ κ := min_le_right _ _
  have hη_budget : η ≤ L.perturbationBudget p.1 p.2 :=
    le_trans (min_le_left _ _) hp
  exact ⟨L.profitableDeviationOfBudget hη hη_capability hη_budget, trivial⟩

end ReverseFields

section EmbeddingAndRegularity

variable {L}

/-- The four `SpectralBehavioralEmbedding` fields for the Constitutional AI
deployment audit lineage are derived theorems about the constructed game. -/
def spectralBehavioralEmbedding :
    SpectralBehavioralEmbedding L.G L.s L.toGame where
  graph_decision_matches_game := fun dev hflip =>
    L.graph_decision_matches_game dev hflip
  perturbation_budget_reflects_best_response_gain := fun dev =>
    L.perturbation_budget_reflects_best_response_gain dev
  spectral_vulnerability_exposes_profitable_deviation := fun hregular {γ} hγ hviol =>
    L.spectral_vulnerability_exposes_profitable_deviation
      hregular (γ := γ) hγ hviol
  spectral_threshold_violation_exposes_profitable_deviation := fun hregular {δ κ} hκ hδ hviol =>
    L.spectral_threshold_violation_exposes_profitable_deviation
      hregular (δ := δ) (κ := κ) hκ hδ hviol

/-- Zero consistency vulnerability rules out profitable deviations in the concrete
Constitutional AI deployment audit lineage. -/
theorem no_profitable_deviation_of_zeroConsistencyVulnerability
    (hsp : ZeroConsistencyVulnerability L.G L.s) {κ : ℚ} :
    ¬ ∃ _dev : L.toGame.ProfitableDeviation κ, True := by
  rintro ⟨dev, _⟩
  have hviol : L.G.spViolation L.s dev.gain :=
    L.perturbation_budget_reflects_best_response_gain dev
  have hle : dev.gain ≤ L.G.cv L.s :=
    (L.G.spViolation_iff_le_cv L.s dev.gain).mp hviol
  rw [hsp] at hle
  exact not_le_of_gt dev.gain_pos hle

/-- Deprecated compatibility alias for
`no_profitable_deviation_of_zeroConsistencyVulnerability`. -/
theorem no_profitable_deviation_of_spectralStrategyproof
    (hsp : SpectralStrategyproof L.G L.s) {κ : ℚ} :
    ¬ ∃ _dev : L.toGame.ProfitableDeviation κ, True :=
  L.no_profitable_deviation_of_zeroConsistencyVulnerability hsp

/-- The gain floor used for the vacuous decomposed-regularity certificate in
the zero-CV case. -/
def strategyproofGainFloor (κ δ : ℚ) : ℚ :=
  if 0 < δ then max 0 (δ / κ) else 0

lemma strategyproofGainFloor_lowerBound :
    BestResponseLowerBound strategyproofGainFloor := by
  intro κ δ hκ hδ
  simp [strategyproofGainFloor, hδ]

lemma strategyproofGainFloor_monotone :
    BestResponseMonotone strategyproofGainFloor := by
  intro κ₁ κ₂ δ hκ₁ hle
  have hκ₂ : 0 < κ₂ := lt_of_lt_of_le hκ₁ hle
  by_cases hδ : 0 < δ
  · have hdiv : δ / κ₂ ≤ δ / κ₁ :=
      div_le_div_of_nonneg_left hδ.le hκ₁ hle
    have hdiv₁_nonneg : 0 ≤ δ / κ₁ := div_nonneg hδ.le hκ₁.le
    have hdiv₂_nonneg : 0 ≤ δ / κ₂ := div_nonneg hδ.le hκ₂.le
    simp [strategyproofGainFloor, hδ,
      max_eq_right hdiv₁_nonneg, max_eq_right hdiv₂_nonneg, hdiv]
  · simp [strategyproofGainFloor, hδ]

/-- In the zero-CV case the Constitutional AI audit lineage
has a decomposed-regular best-response certificate. This is the honest scoped
regularity instance: nonzero structural vulnerabilities are handled by the
embedding fields above, while unconditional decomposed regularity is not
claimed for bounded audit amplitudes. -/
def bestResponseDecompositionOfZeroConsistencyVulnerability
    (hsp : ZeroConsistencyVulnerability L.G L.s) :
    L.toGame.BestResponseDecomposition where
  gainFloor := strategyproofGainFloor
  lowerBound := strategyproofGainFloor_lowerBound
  existence := by
    intro κ δ _hκ _hδ hdev
    exact False.elim (L.no_profitable_deviation_of_zeroConsistencyVulnerability hsp hdev)
  monotone := strategyproofGainFloor_monotone

/-- Deprecated compatibility alias for
`bestResponseDecompositionOfZeroConsistencyVulnerability`. -/
def bestResponseDecompositionOfSpectralStrategyproof
    (hsp : SpectralStrategyproof L.G L.s) :
    L.toGame.BestResponseDecomposition :=
  L.bestResponseDecompositionOfZeroConsistencyVulnerability hsp

/-- Conditional decomposed regularity for the Constitutional AI audit lineage
in the zero-CV case. -/
theorem bestResponseDecomposedRegularity_of_zeroConsistencyVulnerability
    (hsp : ZeroConsistencyVulnerability L.G L.s) :
    L.toGame.BestResponseDecomposedRegularity :=
  ⟨L.bestResponseDecompositionOfZeroConsistencyVulnerability hsp⟩

/-- Deprecated compatibility alias for
`bestResponseDecomposedRegularity_of_zeroConsistencyVulnerability`. -/
theorem bestResponseDecomposedRegularity_of_spectralStrategyproof
    (hsp : SpectralStrategyproof L.G L.s) :
    L.toGame.BestResponseDecomposedRegularity :=
  L.bestResponseDecomposedRegularity_of_zeroConsistencyVulnerability hsp

/-- The constructed embedding composes with the existing one-way theorem:
zero consistency vulnerability implies game strategyproofness for the concrete
Constitutional AI audit lineage. -/
theorem constitutionalAI_zero_consistency_vulnerability_implies_game_strategyproof
    (hsp : ZeroConsistencyVulnerability L.G L.s) :
    L.toGame.GameStrategyproof :=
  SpectralBehavioralEmbedding.zero_consistency_vulnerability_implies_game_strategyproof
    L.spectralBehavioralEmbedding hsp

/-- Deprecated compatibility alias for
`constitutionalAI_zero_consistency_vulnerability_implies_game_strategyproof`. -/
theorem constitutionalAI_spectral_strategyproof_implies_game_strategyproof
    (hsp : SpectralStrategyproof L.G L.s) :
    L.toGame.GameStrategyproof :=
  constitutionalAI_zero_consistency_vulnerability_implies_game_strategyproof hsp

/-- In the zero-CV case, the concrete lineage supplies the
regularity certificate needed to reuse the existing spectral/game
strategyproofness iff theorem. -/
theorem constitutionalAI_zero_consistency_vulnerability_iff_game_strategyproof
    (hsp : ZeroConsistencyVulnerability L.G L.s) :
    ZeroConsistencyVulnerability L.G L.s ↔ L.toGame.GameStrategyproof :=
  SpectralBehavioralEmbedding.zero_consistency_vulnerability_iff_game_strategyproof
    L.spectralBehavioralEmbedding
    (L.bestResponseDecomposedRegularity_of_zeroConsistencyVulnerability hsp)

/-- Deprecated compatibility alias for
`constitutionalAI_zero_consistency_vulnerability_iff_game_strategyproof`. -/
theorem constitutionalAI_spectral_strategyproof_iff_game_strategyproof
    (hsp : SpectralStrategyproof L.G L.s) :
    SpectralStrategyproof L.G L.s ↔ L.toGame.GameStrategyproof :=
  constitutionalAI_zero_consistency_vulnerability_iff_game_strategyproof hsp

/-- In the zero-CV case, the concrete lineage also composes
with the existing stable-equilibrium/behavioral-persistence iff theorem. -/
theorem constitutionalAI_spectral_stable_equilibrium_iff_behavioral_persistence
    (hsp : ZeroConsistencyVulnerability L.G L.s) (κ δ : ℚ) :
    SpectralStableEquilibrium L.G L.s δ κ ↔
      L.toGame.BehavioralPersistentEquilibrium κ δ :=
  SpectralBehavioralEmbedding.spectral_stable_equilibrium_iff_behavioral_persistence
    L.spectralBehavioralEmbedding
    (L.bestResponseDecomposedRegularity_of_zeroConsistencyVulnerability hsp) κ δ

end EmbeddingAndRegularity

section ConcreteWitness

/-- Concrete claim partition: claim `0` is harm-categorical, all other audited
claim-states are benign. -/
noncomputable def constitutionalAIWitnessClaimClass :
    ConstitutionalAIClaimClass 3 :=
  ConstitutionalAIClaimClass.ofFlat
    (fun state => state = 0)
    (fun state => state ≠ 0)
    (by
      intro state
      by_cases h : state = 0
      · exact Or.inl h
      · exact Or.inr h)
    (by
      intro state hboth
      exact hboth.2 hboth.1)

/-- Concrete deployed policy for the witness: deny the harm-categorical claim
and permit the benign residual class. -/
def constitutionalAIWitnessPolicy (state : Fin 3) :
    ConstitutionalAIDecision :=
  if state = 0 then
    ConstitutionalAIDecision.deny
  else
    ConstitutionalAIDecision.permit

theorem constitutionalAIWitnessPolicy_rule :
    ConstitutionalAITrainedAuditSubject constitutionalAIWitnessClaimClass
      constitutionalAIWitnessPolicy := by
  constructor
  · intro state hharm
    change state = 0 at hharm
    exact Or.inr (by simp [constitutionalAIWitnessPolicy, hharm])
  · intro state hbenign
    change state ≠ 0 at hbenign
    simp [constitutionalAIWitnessPolicy, hbenign]

/-- Worked Constitutional-AI-class audit subject. The graph is the uniform
triangle fixture and the signal is the canonical concrete signal. -/
noncomputable def constitutionalAIWitnessLineage :
    ConstitutionalAIBehavioralLineage 3 where
  G := uniTriGraph
  s := sig
  claimClass := constitutionalAIWitnessClaimClass
  policy := constitutionalAIWitnessPolicy
  policy_rule := constitutionalAIWitnessPolicy_rule

theorem constitutionalAIWitness_harm_claim_zero :
    constitutionalAIWitnessLineage.claimClass.HarmCategoricalClaim 0 :=
  rfl

theorem constitutionalAIWitness_benign_claim_one :
    constitutionalAIWitnessLineage.claimClass.BenignClaim 1 := by
  change (1 : Fin 3) ≠ 0
  norm_num

/-- The direct harm-categorical deployment decision is a denial. -/
theorem constitutionalAIWitness_harm_decision_denies :
    constitutionalAIWitnessLineage.deploymentBinaryDecision 0 =
      BinaryDecision.Deny := by
  exact constitutionalAIWitnessLineage.deploymentBinaryDecision_harm_categorical
    constitutionalAIWitness_harm_claim_zero

/-- A direct benign deployment decision is permitted. -/
theorem constitutionalAIWitness_benign_decision_permits :
    constitutionalAIWitnessLineage.deploymentBinaryDecision 1 =
      BinaryDecision.Permit := by
  exact constitutionalAIWitnessLineage.deploymentBinaryDecision_benign
    constitutionalAIWitness_benign_claim_one

theorem constitutionalAIWitness_cv_eq_one :
    constitutionalAIWitnessLineage.G.cv constitutionalAIWitnessLineage.s = 1 := by
  exact concrete_cv_values.1

theorem constitutionalAIWitness_cv_pos :
    0 < constitutionalAIWitnessLineage.G.cv constitutionalAIWitnessLineage.s := by
  rw [constitutionalAIWitness_cv_eq_one]
  norm_num

/-- Capability-scaled triangle witness used by the capability-aware verdict. -/
noncomputable def constitutionalAIWitnessCapacityLineage :
    ConstitutionalAICapacityLineage 3 where
  lineage := constitutionalAIWitnessLineage
  δ := 1 / 10
  δ_pos := by norm_num
  cv_pos := constitutionalAIWitness_cv_pos
  auditAmplitudeBudget := 1 / 10
  auditAmplitudeBudget_pos := by norm_num

theorem constitutionalAIWitness_spViolation_one :
    constitutionalAIWitnessLineage.G.spViolation
      constitutionalAIWitnessLineage.s 1 := by
  rw [constitutionalAIWitnessLineage, GovGraph.spViolation_iff_le_cv]
  rw [concrete_cv_values.1]

/-- Non-vacuous executable behavioral witness: the spectral violation at gain
`1` yields a concrete profitable Constitutional AI audit deviation of gain
`1`. -/
theorem constitutionalAIWitness_nonvacuous_profitable_deviation :
    ∃ dev : constitutionalAIWitnessLineage.toGame.ProfitableDeviation 1,
      dev.gain = 1 := by
  rcases constitutionalAIWitness_spViolation_one with ⟨p, hp⟩
  let action :=
    constitutionalAIWitnessLineage.executableAction p.1 p.2 1 (by norm_num) hp
  let dev :=
    constitutionalAIWitnessLineage.profitableDeviationOfBudget
    (κ := 1) (η := 1) (k := p.1) (i := p.2)
    (by norm_num) le_rfl hp
  refine ⟨dev, ?_⟩
  change constitutionalAIWitnessLineage.toGame.utilityGain p.1 p.2
      constitutionalAIWitnessLineage.zeroProfile
      (constitutionalAIWitnessLineage.replaceAction
        constitutionalAIWitnessLineage.zeroProfile p.1 action) = 1
  rw [constitutionalAIWitnessLineage.utilityGain_zero_to_action]
  · simp [action, executableAction]
  · simp [action, executableAction]

end ConcreteWitness

end ConstitutionalAIBehavioralLineage

end Legitimacy
