/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Observable
import Legitimacy.Kernel.Corrigible
import Legitimacy.Kernel.NonVacuous
import Mathlib.Tactic.FinCases

/-!
# Legitimacy.Results.MultiPrincipal — Multi-principal governance aggregation

This module adds a lightweight multi-principal layer above the existing
single-principal governance kernel. The key idea is to separate two aspects of
governance preference:

1. a *meta-governance* choice of which one of three tracked governance
   properties to sacrifice, and
2. a per-kernel-axiom requirement map used for quorum, veto, corrigibility,
   and delegation results.

The sacrifice-choice component is where the Arrow-style tradeoffs live. The
kernel-requirement component is where veto and delegation connect back to the
existing `MathCorrigible` development.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A principal is any type of entities endowed with governance authority. -/
abbrev Principal := Type

/-- The canonical five terminal kernel axioms used by the multi-principal
aggregation layer. Do not confuse this with
`Legitimacy.Safety.KernelAxiom`, which extends these five runtime obligations
with semantic-bridge and spectral-well-connected obligations for monitored
safety transitions. -/
inductive KernelAxiom where
  | certifiable
  | observable
  | corrigible
  | compositional
  | nonvacuous
  deriving Repr, DecidableEq, Fintype

/-- A governance preference consists of:

* a distinguished sacrifice choice among three tracked governance properties,
  used for the Arrow-style meta-governance theorems, and
* a per-kernel-axiom requirement map, used for quorum, veto, and delegation.
-/
structure GovernancePreference where
  /-- The property sacrificed by this preference in the 3-property Arrow model. -/
  sacrificed : Fin 3
  /-- Which kernel axioms this principal insists on preserving. -/
  requires : KernelAxiom → Bool

/-- Extensionality for governance preferences. -/
@[ext]
lemma GovernancePreference.ext
    {a b : GovernancePreference}
    (hs : a.sacrificed = b.sacrificed)
    (hr : ∀ ax, a.requires ax = b.requires ax) :
    a = b := by
  cases a with
  | mk sa ra =>
      cases b with
      | mk sb rb =>
          dsimp at hs hr
          cases hs
          have hfun : ra = rb := funext hr
          cases hfun
          rfl

/-- Aggregation rules combine a finite profile of principal preferences into a
single governance preference. -/
abbrev AggregationRule (k : Nat) :=
  (Fin k → GovernancePreference) → GovernancePreference

/-- A principal prefers property `p` exactly when `p` is not the sacrificed
property in its meta-governance choice. -/
def prefersProperty (pref : GovernancePreference) (p : Fin 3) : Bool :=
  decide (pref.sacrificed ≠ p)

/-- The aggregated verdict on property `p` induced by an aggregation rule. -/
def socialProperty {k : Nat} (F : AggregationRule k)
    (prefs : Fin k → GovernancePreference) (p : Fin 3) : Bool :=
  prefersProperty (F prefs) p

/-- Two profiles agree on property `p` when every principal has the same view
about preserving `p` in both profiles. -/
def SameOn {k : Nat} (p : Fin 3)
    (prefs₁ prefs₂ : Fin k → GovernancePreference) : Prop :=
  ∀ i : Fin k, prefersProperty (prefs₁ i) p = prefersProperty (prefs₂ i) p

/-- Unanimity: if all principals submit the same governance preference, the
aggregated outcome is exactly that preference. -/
def Unanimity {k : Nat} (F : AggregationRule k) : Prop :=
  ∀ pref : GovernancePreference, F (fun _ => pref) = pref

/-- Independence: the aggregated verdict on property `p` depends only on the
principals' views about `p`. -/
def Independence {k : Nat} (F : AggregationRule k) : Prop :=
  ∀ (p : Fin 3) (prefs₁ prefs₂ : Fin k → GovernancePreference),
    SameOn p prefs₁ prefs₂ →
    socialProperty F prefs₁ p = socialProperty F prefs₂ p

/-- Principal `i` is a dictator when the aggregate always matches `i` on every
tracked governance property. -/
def Dictator {k : Nat} (F : AggregationRule k) (i : Fin k) : Prop :=
  ∀ (prefs : Fin k → GovernancePreference) (p : Fin 3),
    socialProperty F prefs p = prefersProperty (prefs i) p

/-- Non-dictatorship: no single principal determines all social property
verdicts. -/
def NonDictatorship {k : Nat} (F : AggregationRule k) : Prop :=
  ∀ i : Fin k, ¬ Dictator F i

/-- Count the principals that want property `p` preserved. -/
def supportCount {k : Nat} (prefs : Fin k → GovernancePreference) (p : Fin 3) :
    Nat :=
  (Finset.univ.filter fun i => prefersProperty (prefs i) p = true).card

/-- Count the principals that require kernel axiom `ax`. -/
def kernelSupportCount {k : Nat} (prefs : Fin k → GovernancePreference)
    (ax : KernelAxiom) : Nat :=
  (Finset.univ.filter fun i => (prefs i).requires ax = true).card

/-- A property is accepted by quorum `q` when at least `q` principals want it
preserved. -/
def propertyAccepted {k : Nat} (q : Nat) (prefs : Fin k → GovernancePreference)
    (p : Fin 3) : Bool :=
  decide (q ≤ supportCount prefs p)

/-- The sacrificed property chosen by quorum `q`.

The rule picks the first property that fails quorum. If every tracked property
passes quorum, it defaults to sacrificing property `0`; this deterministic
repair is what creates the explicit independence counterexample below. -/
def quorumSacrifice {k : Nat} (q : Nat)
    (prefs : Fin k → GovernancePreference) : Fin 3 :=
  if propertyAccepted q prefs 0 = false then 0
  else if propertyAccepted q prefs 1 = false then 1
  else if propertyAccepted q prefs 2 = false then 2
  else 0

/-- Quorum aggregation: kernel axioms are preserved exactly when they receive
at least `q` supporters, while the 3-property sacrifice choice is repaired to a
single sacrificed property by `quorumSacrifice`. -/
def quorumRule {k : Nat} (q : Nat) : AggregationRule k :=
  fun prefs =>
    { sacrificed := quorumSacrifice q prefs
      requires := fun ax => decide (q ≤ kernelSupportCount prefs ax) }

/-- Majority quorum for three principals. -/
abbrev majorityQuorumRule : AggregationRule 3 :=
  quorumRule 2

/-- A principal has veto power when any kernel axiom it insists on preserving
must remain preserved in the aggregate. -/
def VetoRight {k : Nat} (F : AggregationRule k) (i : Fin k) : Prop :=
  ∀ (prefs : Fin k → GovernancePreference) (ax : KernelAxiom),
    (prefs i).requires ax = true →
    (F prefs).requires ax = true

/-- Delegation of authority from one principal to another over a domain. -/
structure DelegatedAuthority (principalTy domainTy : Type) where
  /-- The delegating principal. -/
  delegator : principalTy
  /-- The governed domain delegated away. -/
  domain : domainTy
  /-- The delegate principal. -/
  delegate : principalTy

/-- A compact package of the concrete data needed to evaluate the five kernel
axioms using their actual definitions from the other `Math*.lean` files. -/
structure KernelWitness where
  /-- The concrete governance-state space used for observability. -/
  State : Type
  /-- The observed interface exposed by the system. -/
  ObservedState : Type
  /-- The decision type certified by the system. -/
  Decision : Type
  /-- The certificate witness type for governance decisions. -/
  Witness : Certificate Decision
  /-- The full-answer function used by the observability axiom. -/
  answer : GovernanceQuery → State → Bool
  /-- The system's observation map. -/
  observe : ObservationFunction State ObservedState
  /-- The observable answer function. -/
  observeAnswer : GovernanceQuery → ObservedState → Bool
  /-- The certifiability interface from Axiom 1. -/
  certification : CertifiableSystem Decision Witness
  /-- The supervisory state from the corrigibility development. -/
  supervisoryState : GovernanceState
  /-- The state-action space for self-modification. -/
  actionSpace : StateActionSpace
  /-- The supported supervisory algebra. -/
  algebra : SupervisoryAlgebra
  /-- The concrete governance graph used for axioms 4 and 5. -/
  graph : GovernanceGraph
  /-- The execution trace used by the non-vacuity axiom. -/
  trace : GovernanceTrace

/-- All five kernel axioms hold for the concrete system packaged by a witness. -/
def KernelSatisfied (w : KernelWitness) : Prop :=
  Certifiable w.certification ∧
    GovernanceObservable w.answer w.observeAnswer w.observe ∧
    Corrigible w.supervisoryState w.actionSpace w.algebra ∧
    CompositionalSafety w.graph ∧
    NonVacuous w.graph w.trace

/-- Any kernel-satisfied witness carries a well-formed governance graph,
because NON-VACUOUS packages such a witness explicitly. -/
lemma KernelSatisfied.wellFormed
    {w : KernelWitness} (hsat : KernelSatisfied w) :
    WellFormed w.graph := by
  rcases hsat.2.2.2.2 with ⟨witness⟩
  exact witness.wellFormed

/-- A delegated domain restricts claimant-facing queries to a designated
subdomain and narrows certifiable decisions to those assigned to that domain. -/
structure DelegationDomain (Decision : Type) where
  /-- The claimant IDs governed by the delegate. -/
  claims : ClaimantId → Bool
  /-- The decisions whose legitimacy remains in scope for the delegate. -/
  decision : Decision → Prop

/-- Restrict a claim list to the delegated claimant domain. -/
def restrictClaims (D : ClaimantId → Bool) (claims : List ClaimQ) : List ClaimQ :=
  claims.filter fun c => D c.id

/-- Restrict a governance node to the delegated domain. Out-of-domain claimants
are denied immediately, while in-domain execution sees only in-domain claims. -/
def restrictNode (D : ClaimantId → Bool) (node : GovernanceNodeFn) :
    GovernanceNodeFn :=
  fun claims k =>
    if D k then node (restrictClaims D claims) k else BinaryDecision.Deny

/-- Restrict a governance graph nodewise to the delegated domain. -/
def restrictGraph (D : ClaimantId → Bool) (G : GovernanceGraph) :
    GovernanceGraph :=
  G.map (restrictNode D)

/-- Restrict a governance trace to the delegated domain. Out-of-domain events
are hidden as `none`, while in-domain events are preserved verbatim. -/
def restrictTrace (D : ClaimantId → Bool) (τ : GovernanceTrace) :
    GovernanceTrace :=
  fun t =>
    let event := τ t
    if D event.1.id then event else (event.1, none)

/-- Claim-permission queries are delegated only on the restricted claimant
domain. Structural graph-property queries remain visible. -/
def queryEnabled (D : ClaimantId → Bool) : GovernanceQuery → Bool
  | .ClaimPermitted k => D k
  | .PropertyHolds _ => true
  | .SacrificeDeclared _ => true

/-- Restrict a query-answering interface to the delegated query domain. -/
def restrictQueryAnswer
    {S : Type} (D : ClaimantId → Bool) (answer : GovernanceQuery → S → Bool) :
    GovernanceQuery → S → Bool :=
  fun q s => if queryEnabled D q then answer q s else false

/-- Restrict certification to decisions that remain inside the delegated
decision domain. The verifier and resource accounting are inherited unchanged
from the parent system. -/
def restrictCertification
    {Decision : Type} {W : Certificate Decision}
    (D : DelegationDomain Decision) (sys : CertifiableSystem Decision W) :
    CertifiableSystem Decision W where
  legitimate d := sys.legitimate d ∧ D.decision d
  verifier := sys.verifier
  verifierSteps := sys.verifierSteps
  bound := sys.bound

/-- A delegated domain carries a nonempty family of admissible claims whose
entire membership lies inside that domain. -/
structure DomainAdmissible
    (τ : GovernanceTrace) (D : ClaimantId → Bool) where
  claims : List ClaimQ
  nonempty : claims ≠ []
  in_domain : ∀ c ∈ claims, D c.id = true
  bounded : BoundedDisposition τ claims
  permitEligible : PermitEligible τ claims

/-- The delegated subsystem obtained by restricting certification, observable
queries, graph execution, and liveness witnesses to domain `D`. The
supervisory algebra is inherited unchanged from the parent system. -/
def DelegateSystem (parent : KernelWitness)
    (D : DelegationDomain parent.Decision) : KernelWitness where
  State := parent.State
  ObservedState := parent.ObservedState
  Decision := parent.Decision
  Witness := parent.Witness
  answer := restrictQueryAnswer D.claims parent.answer
  observe := parent.observe
  observeAnswer := restrictQueryAnswer D.claims parent.observeAnswer
  certification := restrictCertification D parent.certification
  supervisoryState := parent.supervisoryState
  actionSpace := parent.actionSpace
  algebra := parent.algebra
  graph := restrictGraph D.claims parent.graph
  trace := restrictTrace D.claims parent.trace

/-- Convert a kernel-level governance preference into the concrete graph model
used by `MathCorrigible`. Requiring `KernelAxiom.corrigible` installs the
universal override node; otherwise we use the empty graph. -/
def graphOfPreference (pref : GovernancePreference) : GovernanceGraph :=
  if pref.requires KernelAxiom.corrigible then [overrideNode] else []

/-- A helper preference that sacrifices property `s` and carries no additional
kernel requirements. -/
def barePreference (s : Fin 3) : GovernancePreference :=
  { sacrificed := s
    requires := fun _ => false }

/-- Dictatorship by principal `i`. -/
def dictatorshipRule {k : Nat} (i : Fin k) : AggregationRule k :=
  fun prefs => prefs i

/-- A constant aggregation rule. -/
def constantRule {k : Nat} : AggregationRule k :=
  fun _ => barePreference 0

private def pref0 : GovernancePreference := barePreference 0
private def pref1 : GovernancePreference := barePreference 1
private def pref2 : GovernancePreference := barePreference 2

private def profile012 : Fin 3 → GovernancePreference
  | 0 => pref0
  | 1 => pref1
  | _ => pref2

private def profile011 : Fin 3 → GovernancePreference
  | 0 => pref0
  | _ => pref1

/-- The two majority-counterexample profiles agree on property `0`. -/
private theorem profiles_agree_on_zero :
    SameOn 0 profile012 profile011 := by
  intro i
  fin_cases i <;> rfl

/-- Majority quorum on `profile012` sacrifices property `0`, so property `0`
fails socially. -/
private theorem majority_profile012_zero :
    socialProperty majorityQuorumRule profile012 0 = false := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

/-- Majority quorum on `profile011` sacrifices property `1`, so property `0`
holds socially. -/
private theorem majority_profile011_zero :
    socialProperty majorityQuorumRule profile011 0 = true := by
  native_decide

/-- In a unanimous profile, support for a tracked property is either `0` or
`3`, depending on whether that property is the sacrificed one. -/
private theorem supportCount_unanimous
    (s : Fin 3) (req : KernelAxiom → Bool) (p : Fin 3) :
    supportCount (k := 3)
      (fun _ : Fin 3 => ({ sacrificed := s, requires := req } : GovernancePreference)) p =
      if s = p then 0 else 3 := by
  fin_cases s <;> fin_cases p <;> simp [supportCount, prefersProperty]

/-- In a unanimous profile, support for a kernel axiom is either `0` or `3`,
depending on whether the common preference requires it. -/
private theorem kernelSupportCount_unanimous
    (s : Fin 3) (req : KernelAxiom → Bool) (ax : KernelAxiom) :
    kernelSupportCount (k := 3)
      (fun _ : Fin 3 => ({ sacrificed := s, requires := req } : GovernancePreference)) ax =
      if req ax then 3 else 0 := by
  cases h : req ax <;> simp [kernelSupportCount, h]

/-- Majority quorum is unanimous on three principals. -/
lemma majority_quorum_satisfies_unanimity :
    Unanimity majorityQuorumRule := by
  intro pref
  cases pref with
  | mk s req =>
      apply GovernancePreference.ext
      · fin_cases s
        · simp [majorityQuorumRule, quorumRule, quorumSacrifice, propertyAccepted,
            supportCount_unanimous]
        · simp [majorityQuorumRule, quorumRule, quorumSacrifice, propertyAccepted,
            supportCount_unanimous]
        · simp [majorityQuorumRule, quorumRule, quorumSacrifice, propertyAccepted,
            supportCount_unanimous]
      · intro ax
        cases h : req ax
        · simp [majorityQuorumRule, quorumRule, kernelSupportCount_unanimous, h]
        · simp [majorityQuorumRule, quorumRule, kernelSupportCount_unanimous, h]

/-- Majority quorum with deterministic repair is not independent. The
counterexample keeps every principal's stance on property `0` fixed while a
different property's quorum failure flips the social verdict on `0`. -/
lemma majority_quorum_not_independent :
    ¬ Independence majorityQuorumRule := by
  intro hind
  have h :=
    hind 0 profile012 profile011 profiles_agree_on_zero
  rw [majority_profile012_zero, majority_profile011_zero] at h
  cases h

/-- Every dictatorship rule is unanimous. -/
lemma dictatorship_unanimous {k : Nat} (i : Fin k) :
    Unanimity (dictatorshipRule i) := by
  intro pref
  rfl

/-- Every dictatorship rule is independent. -/
lemma dictatorship_independent {k : Nat} (i : Fin k) :
    Independence (dictatorshipRule i) := by
  intro p prefs₁ prefs₂ hsame
  simpa [dictatorshipRule, socialProperty] using hsame i

/-- The constant rule is independent. -/
lemma constant_rule_independent {k : Nat} :
    Independence (constantRule (k := k)) := by
  intro p prefs₁ prefs₂ _hsame
  rfl

/-- The constant rule is non-dictatorial. -/
lemma constant_rule_non_dictatorial :
    NonDictatorship (constantRule (k := 3)) := by
  intro i hdict
  let prefs : Fin 3 → GovernancePreference := fun _ => pref1
  have h := hdict prefs 0
  have hsocial : socialProperty (constantRule (k := 3)) prefs 0 = false := by
    -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
    native_decide
  have hindiv : prefersProperty (prefs i) 0 = true := by
    fin_cases i <;> native_decide
  rw [hsocial, hindiv] at h
  cases h

/-- Majority quorum is non-dictatorial. -/
lemma majority_quorum_non_dictatorial :
    NonDictatorship majorityQuorumRule := by
  intro i hdict
  let prefs : Fin 3 → GovernancePreference :=
    fun j => if j = i then pref0 else pref1
  have h := hdict prefs 0
  have hsocial : socialProperty majorityQuorumRule prefs 0 = true := by
    -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
    fin_cases i <;> native_decide
  have hindiv : prefersProperty (prefs i) 0 = false := by
    fin_cases i <;> native_decide
  rw [hsocial, hindiv] at h
  cases h

/-- A veto-holder who insists on `corrigible` forces the aggregate to retain
the concrete override graph. -/
theorem veto_preserves_corrigibility
    {k : Nat} {F : AggregationRule k} {i : Fin k}
    (hveto : VetoRight F i)
    (prefs : Fin k → GovernancePreference)
    (hcorr : (prefs i).requires KernelAxiom.corrigible = true) :
    OverrideCorrigible (graphOfPreference (F prefs)) nullActionSpace := by
  have hagg : (F prefs).requires KernelAxiom.corrigible = true :=
    hveto prefs KernelAxiom.corrigible hcorr
  unfold graphOfPreference
  simp [hagg]
  exact singleton_override_corrigible nullActionSpace nullActionSpace_preserving

/-- Restricting legitimacy to a delegated decision domain preserves
certifiability by reusing the parent verifier, witness, and bound. -/
lemma certifiable_restrictCertification
    {Decision : Type} {W : Certificate Decision}
    (D : DelegationDomain Decision)
    {sys : CertifiableSystem Decision W}
    (hcert : Certifiable sys) :
    Certifiable (restrictCertification D sys) := by
  intro d hlegit
  exact hcert d hlegit.1

/-- Restricting claimant-facing queries preserves observability: in-domain
queries are answered exactly as before, and out-of-domain claim-permission
queries are suppressed on both sides. -/
lemma observable_restrictQueryAnswer
    {S S' : Type}
    (D : ClaimantId → Bool)
    {answer : GovernanceQuery → S → Bool}
    {answer' : GovernanceQuery → S' → Bool}
    {O : ObservationFunction S S'}
    (hobs : GovernanceObservable answer answer' O) :
    GovernanceObservable
      (restrictQueryAnswer D answer)
      (restrictQueryAnswer D answer') O := by
  intro q s
  by_cases hq : queryEnabled D q
  · simp [restrictQueryAnswer, hq, hobs q s]
  · simp [restrictQueryAnswer, hq]

/-- Every restricted governance graph is compositionally safe: once the
restricted prefix denies, no suffix can resurrect the claim. -/
lemma compositionalSafety_restrictGraph
    (D : ClaimantId → Bool) (G : GovernanceGraph) :
    CompositionalSafety (restrictGraph D G) := by
  intro H claims k hdeny
  exact graphDecide_append_of_deny (restrictGraph D G) H claims k hdeny

/-- A restricted graph remains well-formed whenever the parent graph is. -/
lemma wellFormed_restrictGraph
    (D : ClaimantId → Bool) {G : GovernanceGraph}
    (hwf : WellFormed G) :
    WellFormed (restrictGraph D G) := by
  cases G with
  | nil =>
      cases hwf rfl
  | cons node rest =>
      simp [WellFormed, restrictGraph]

/-- An in-domain permit event is preserved verbatim by trace restriction. -/
lemma restrictTrace_preserves_permit
    {τ : GovernanceTrace} {D : ClaimantId → Bool} {claims : List ClaimQ}
    (hin : ∀ c ∈ claims, D c.id = true)
    {c : ClaimQ} (hc : c ∈ claims) {t : Nat}
    (hperm : τ t = (c, some GovernanceOutcome.permit)) :
    restrictTrace D τ t = (c, some GovernanceOutcome.permit) := by
  have hcD : D c.id = true := hin c hc
  simp [restrictTrace, hcD, hperm]

/-- An in-domain deny event is preserved verbatim by trace restriction. -/
lemma restrictTrace_preserves_deny
    {τ : GovernanceTrace} {D : ClaimantId → Bool} {claims : List ClaimQ}
    (hin : ∀ c ∈ claims, D c.id = true)
    {c : ClaimQ} (hc : c ∈ claims) {t : Nat}
    (hdeny : τ t = (c, some GovernanceOutcome.deny)) :
    restrictTrace D τ t = (c, some GovernanceOutcome.deny) := by
  have hcD : D c.id = true := hin c hc
  simp [restrictTrace, hcD, hdeny]

/-- Restricting the trace preserves bounded disposition for claim sets that
already lie entirely inside the delegated domain. -/
lemma boundedDisposition_restrictTrace
    {τ : GovernanceTrace} {D : ClaimantId → Bool} {claims : List ClaimQ}
    (hin : ∀ c ∈ claims, D c.id = true)
    (hbounded : BoundedDisposition τ claims) :
    BoundedDisposition (restrictTrace D τ) claims := by
  rcases hbounded with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro c hc
  rcases hT c hc with ⟨t, ht, hdisp⟩
  refine ⟨t, ht, ?_⟩
  cases hdisp with
  | inl hperm =>
      left
      exact restrictTrace_preserves_permit hin hc hperm
  | inr hdeny =>
      right
      exact restrictTrace_preserves_deny hin hc hdeny

/-- Restricting the trace preserves permit eligibility for claim sets already
contained in the delegated domain. -/
lemma permitEligible_restrictTrace
    {τ : GovernanceTrace} {D : ClaimantId → Bool} {claims : List ClaimQ}
    (hin : ∀ c ∈ claims, D c.id = true)
    (hperm : PermitEligible τ claims) :
    PermitEligible (restrictTrace D τ) claims := by
  intro c hc
  rcases hperm c hc with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  exact restrictTrace_preserves_permit hin hc ht

/-- A nonempty permit-eligible claim family witnesses at least one concrete
permit event in the trace. -/
lemma permitEligible_some_permit_event
    {τ : GovernanceTrace} {claims : List ClaimQ}
    (hne : claims ≠ [])
    (hperm : PermitEligible τ claims) :
    ∃ c ∈ claims, ∃ t : Nat, τ t = (c, some GovernanceOutcome.permit) := by
  rcases List.exists_mem_of_ne_nil claims hne with ⟨c, hc⟩
  rcases hperm c hc with ⟨t, ht⟩
  exact ⟨c, hc, t, ht⟩

/-- Refusal traces cannot contain permit events. -/
lemma refusal_not_permit_event
    {τ : GovernanceTrace} {c : ClaimQ} {t : Nat}
    (href : Refusal τ) :
    τ t ≠ (c, some GovernanceOutcome.permit) := by
  intro hperm
  have hdeny := href t
  rw [hperm] at hdeny
  cases hdeny

/-- Permanent-escalation traces cannot contain permit events. -/
lemma permanentEscalation_not_permit_event
    {τ : GovernanceTrace} {c : ClaimQ} {t : Nat}
    (hesc : PermanentEscalation τ) :
    τ t ≠ (c, some GovernanceOutcome.permit) := by
  intro hperm
  have hstep := hesc t
  rw [hperm] at hstep
  cases hstep

/-- Deadlocked traces cannot contain permit events. -/
lemma deadlock_not_permit_event
    {τ : GovernanceTrace} {c : ClaimQ} {t : Nat}
    (hdead : Deadlock τ) :
    τ t ≠ (c, some GovernanceOutcome.permit) := by
  intro hperm
  have hstep := hdead t
  rw [hperm] at hstep
  cases hstep

/-- Any nonempty permit-eligible claim family rules out refusal traces. -/
lemma notRefusal_of_permitEligible
    {τ : GovernanceTrace} {claims : List ClaimQ}
    (hne : claims ≠ [])
    (hperm : PermitEligible τ claims) :
    ¬ Refusal τ := by
  intro href
  rcases permitEligible_some_permit_event hne hperm with ⟨c, hc, t, ht⟩
  exact refusal_not_permit_event href ht

/-- Any nonempty permit-eligible claim family rules out permanent escalation. -/
lemma notPermanentEscalation_of_permitEligible
    {τ : GovernanceTrace} {claims : List ClaimQ}
    (hne : claims ≠ [])
    (hperm : PermitEligible τ claims) :
    ¬ PermanentEscalation τ := by
  intro hesc
  rcases permitEligible_some_permit_event hne hperm with ⟨c, hc, t, ht⟩
  exact permanentEscalation_not_permit_event hesc ht

/-- Any nonempty permit-eligible claim family rules out deadlock. -/
lemma notDeadlock_of_permitEligible
    {τ : GovernanceTrace} {claims : List ClaimQ}
    (hne : claims ≠ [])
    (hperm : PermitEligible τ claims) :
    ¬ Deadlock τ := by
  intro hdead
  rcases permitEligible_some_permit_event hne hperm with ⟨c, hc, t, ht⟩
  exact deadlock_not_permit_event hdead ht

/-- If the delegated domain contains an admissible nonempty claim family,
then the restricted subsystem is non-vacuous. -/
lemma nonVacuous_restrict
    {G : GovernanceGraph} {τ : GovernanceTrace} {D : ClaimantId → Bool}
    (hwf : WellFormed G)
    (hdom : DomainAdmissible τ D) :
    NonVacuous (restrictGraph D G) (restrictTrace D τ) := by
  refine ⟨{
    wellFormed := wellFormed_restrictGraph D hwf
    governedClaims := hdom.claims
    governed_nonempty := hdom.nonempty
    boundedDisposition := boundedDisposition_restrictTrace hdom.in_domain hdom.bounded
    permitEligibleClaims := hdom.claims
    eligible_nonempty := hdom.nonempty
    eligible_subset := by
      intro c hc
      exact hc
    permitEligible := permitEligible_restrictTrace hdom.in_domain hdom.permitEligible
    notRefusal := by
      exact notRefusal_of_permitEligible hdom.nonempty
        (permitEligible_restrictTrace hdom.in_domain hdom.permitEligible)
    notPermanentEscalation := by
      exact notPermanentEscalation_of_permitEligible hdom.nonempty
        (permitEligible_restrictTrace hdom.in_domain hdom.permitEligible)
    notDeadlock := by
      exact notDeadlock_of_permitEligible hdom.nonempty
        (permitEligible_restrictTrace hdom.in_domain hdom.permitEligible)
  }⟩

/-- Delegated authority preserves the kernel by constructing the delegated
subsystem as a domain restriction of the parent system. Certifiability is
proved by restricting legitimacy, observability by restricting claimant-facing
queries, corrigibility by reusing the parent's supervisory algebra, safety by
restricted-prefix denial, and non-vacuity by an admissible in-domain claim
family. -/
theorem delegation_preserves_kernel
    {principalTy : Type}
    {parent : KernelWitness}
    (authority : DelegatedAuthority principalTy (DelegationDomain parent.Decision))
    (hparent : KernelSatisfied parent)
    (hdom : DomainAdmissible parent.trace authority.domain.claims) :
    KernelSatisfied (DelegateSystem parent authority.domain) := by
  have hwf : WellFormed parent.graph := KernelSatisfied.wellFormed hparent
  rcases hparent with ⟨hcert, hobs, hcorr, _hcomp, hnv⟩
  exact ⟨certifiable_restrictCertification authority.domain hcert,
    observable_restrictQueryAnswer authority.domain.claims hobs,
    hcorr,
    compositionalSafety_restrictGraph authority.domain.claims parent.graph,
    nonVacuous_restrict hwf hdom⟩

/-- A concrete Arrow-style impossibility witness: majority quorum is unanimous
and non-dictatorial, but fails independence on a 3-principal/3-property
counterexample. -/
theorem majorityQuorumRule_fails_arrow_triple :
    ¬ (Unanimity majorityQuorumRule ∧
       Independence majorityQuorumRule ∧
       NonDictatorship majorityQuorumRule) := by
  intro h
  exact majority_quorum_not_independent h.2.1

/-- Deprecated compatibility alias: the corrected name is
`majorityQuorumRule_fails_arrow_triple`, a single majority-quorum witness. -/
theorem arrow_legitimacy_impossibility :
    ¬ (Unanimity majorityQuorumRule ∧
       Independence majorityQuorumRule ∧
       NonDictatorship majorityQuorumRule) :=
  majorityQuorumRule_fails_arrow_triple

/-- The multi-principal frontier: each pair among unanimity, independence, and
non-dictatorship is jointly achievable by an explicit rule, but the majority
quorum witness cannot realize all three at once. -/
theorem multi_principal_pairwise_achievability_with_majorityQuorum_obstruction :
    (Unanimity (dictatorshipRule (0 : Fin 3)) ∧
      Independence (dictatorshipRule (0 : Fin 3))) ∧
    (Unanimity majorityQuorumRule ∧
      NonDictatorship majorityQuorumRule) ∧
    (Independence (constantRule (k := 3)) ∧
      NonDictatorship (constantRule (k := 3))) ∧
    ¬ (Unanimity majorityQuorumRule ∧
       Independence majorityQuorumRule ∧
       NonDictatorship majorityQuorumRule) := by
  refine ⟨?_, ?_, ?_, majorityQuorumRule_fails_arrow_triple⟩
  · exact ⟨dictatorship_unanimous 0, dictatorship_independent 0⟩
  · exact ⟨majority_quorum_satisfies_unanimity, majority_quorum_non_dictatorial⟩
  · exact ⟨constant_rule_independent, constant_rule_non_dictatorial⟩

/-- Deprecated compatibility alias: the corrected name is
`multi_principal_pairwise_achievability_with_majorityQuorum_obstruction`,
because only the majority-quorum triple is obstructed here. -/
theorem multi_principal_impossibility_frontier :
    (Unanimity (dictatorshipRule (0 : Fin 3)) ∧
      Independence (dictatorshipRule (0 : Fin 3))) ∧
    (Unanimity majorityQuorumRule ∧
      NonDictatorship majorityQuorumRule) ∧
    (Independence (constantRule (k := 3)) ∧
      NonDictatorship (constantRule (k := 3))) ∧
    ¬ (Unanimity majorityQuorumRule ∧
       Independence majorityQuorumRule ∧
       NonDictatorship majorityQuorumRule) :=
  multi_principal_pairwise_achievability_with_majorityQuorum_obstruction

end Legitimacy
