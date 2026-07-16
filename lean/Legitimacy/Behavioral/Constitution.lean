/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Graph
import Mathlib.Tactic

/-!
# Constitution-as-DAG primitives

This module factors the Constitutional AI claim layer through a finite
constitution: principles form a finite partially ordered conflict-resolution
surface, and claims are classified by the resolved principle rather than by a
flat primitive partition.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset

/-- A constitutional principle over an `n`-state audited claim space.

The `rank` is not itself the relation; it is a stable identifier useful for
concrete finite instances and floor tests. The actual conflict-resolution
order lives in `Constitution.conflictRel`. -/
structure Principle (n : Nat) where
  name : String
  rank : Nat
  verdict : BinaryDecision
  deriving DecidableEq, Repr

namespace Principle

variable {n : Nat}

@[simp] theorem ext_iff {p q : Principle n} :
    p = q ↔ p.name = q.name ∧ p.rank = q.rank ∧ p.verdict = q.verdict := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨hname, hrank, hverdict⟩
    cases p
    cases q
    simp at hname hrank hverdict
    simp [hname, hrank, hverdict]

end Principle

/-- Finite constitutional data for an `n`-state claim space.

`conflictRel p q` is read as: principle `q` is at least as authoritative as
principle `p` when both are relevant. A claim's `resolvedPrinciple` must be an
applicable principle that is above every other applicable principle. -/
structure Constitution (n : Nat) where
  principles : Finset (Principle n)
  applies : Principle n → Fin n → Prop
  conflictRel : Principle n → Principle n → Prop
  conflictRel_refl :
    ∀ {p : Principle n}, p ∈ principles → conflictRel p p
  conflictRel_antisymm :
    ∀ {p q : Principle n}, p ∈ principles → q ∈ principles →
      conflictRel p q → conflictRel q p → p = q
  conflictRel_trans :
    ∀ {p q r : Principle n}, p ∈ principles → q ∈ principles →
      r ∈ principles → conflictRel p q → conflictRel q r →
        conflictRel p r
  conflictRel_wellFounded :
    WellFounded
      (fun p q : Principle n =>
        p ∈ principles ∧ q ∈ principles ∧
          conflictRel p q ∧ ¬ conflictRel q p)
  resolution : ∀ p q : Principle n, conflictRel p q → Principle n
  resolution_mem :
    ∀ {p q : Principle n} (h : conflictRel p q),
      p ∈ principles → q ∈ principles → resolution p q h ∈ principles
  resolution_upper_left :
    ∀ {p q : Principle n} (h : conflictRel p q),
      p ∈ principles → q ∈ principles → conflictRel p (resolution p q h)
  resolution_upper_right :
    ∀ {p q : Principle n} (h : conflictRel p q),
      p ∈ principles → q ∈ principles → conflictRel q (resolution p q h)
  complete :
    ∀ claim : Fin n, ∃ p : Principle n, p ∈ principles ∧ applies p claim
  resolvedPrinciple : Fin n → Principle n
  resolved_mem :
    ∀ claim : Fin n, resolvedPrinciple claim ∈ principles
  resolved_applies :
    ∀ claim : Fin n, applies (resolvedPrinciple claim) claim
  resolved_resolves :
    ∀ claim : Fin n, ∀ p : Principle n, p ∈ principles →
      applies p claim → conflictRel p (resolvedPrinciple claim)

namespace Constitution

variable {n : Nat}

/-- Claims are constitutionally equivalent exactly when conflict resolution
selects the same governing principle. -/
def ResolutionEquivalent (C : Constitution n) (a b : Fin n) : Prop :=
  C.resolvedPrinciple a = C.resolvedPrinciple b

/-- Setoid quotient induced by constitutional conflict resolution. -/
def resolutionSetoid (C : Constitution n) : Setoid (Fin n) where
  r := C.ResolutionEquivalent
  iseqv := by
    constructor
    · intro a
      rfl
    · intro a b h
      exact h.symm
    · intro a b c hab hbc
      exact hab.trans hbc

/-- Claim classes after quotienting by the resolved principle. -/
abbrev ClaimQuotient (C : Constitution n) : Type :=
  Quotient C.resolutionSetoid

/-- Quotient class of a concrete claim. -/
def claimClass (C : Constitution n) (claim : Fin n) : C.ClaimQuotient :=
  Quotient.mk C.resolutionSetoid claim

theorem same_claimClass_iff_resolved_eq
    (C : Constitution n) (a b : Fin n) :
    C.claimClass a = C.claimClass b ↔
      C.resolvedPrinciple a = C.resolvedPrinciple b := by
  exact Quotient.eq

/-- A constitution has a substantive conflict edge when the finite order has a
strict comparable pair, ruling out the one-principle/no-conflict floor. -/
def Substantive (C : Constitution n) : Prop :=
  ∃ p q : Principle n, p ∈ C.principles ∧ q ∈ C.principles ∧
    p ≠ q ∧ C.conflictRel p q ∧ ¬ C.conflictRel q p

/-- The resolved principle is a profile-sensitive field of a constitution. -/
theorem ne_of_resolvedPrinciple_ne
    {C D : Constitution n} {claim : Fin n}
    (h : C.resolvedPrinciple claim ≠ D.resolvedPrinciple claim) :
    C ≠ D := by
  intro hsame
  exact h (congrFun (congrArg Constitution.resolvedPrinciple hsame) claim)

/-- Canonical deny principle used by the flat harm/benign compatibility layer. -/
def harmPrinciple (n : Nat) : Principle n where
  name := "harm-categorical"
  rank := 1
  verdict := BinaryDecision.Deny

/-- Canonical permit principle used by the flat harm/benign compatibility layer. -/
def benignPrinciple (n : Nat) : Principle n where
  name := "benign"
  rank := 0
  verdict := BinaryDecision.Permit

@[simp] theorem harmPrinciple_ne_benignPrinciple :
    harmPrinciple n ≠ benignPrinciple n := by
  intro h
  have hdec := congrArg Principle.verdict h
  cases hdec

@[simp] theorem benignPrinciple_ne_harmPrinciple :
    benignPrinciple n ≠ harmPrinciple n := by
  exact fun h => harmPrinciple_ne_benignPrinciple h.symm

/-- The two-principle flat compatibility set. -/
def flatPrinciples (n : Nat) : Finset (Principle n) :=
  {benignPrinciple n, harmPrinciple n}

@[simp] theorem harmPrinciple_mem_flatPrinciples :
    harmPrinciple n ∈ flatPrinciples n := by
  simp [flatPrinciples]

@[simp] theorem benignPrinciple_mem_flatPrinciples :
    benignPrinciple n ∈ flatPrinciples n := by
  simp [flatPrinciples]

private theorem flatPrinciple_rank_cases
    {p : Principle n} (hp : p ∈ flatPrinciples n) :
    p = benignPrinciple n ∨ p = harmPrinciple n := by
  simpa [flatPrinciples] using hp

/-- Flat harm/benign relation: benign is below harm, and each principle is
reflexively below itself. -/
def flatConflictRel (p q : Principle n) : Prop :=
  p.rank ≤ q.rank

private theorem flatConflictRel_antisymm
    {p q : Principle n} (hp : p ∈ flatPrinciples n)
    (hq : q ∈ flatPrinciples n)
    (hpq : flatConflictRel p q) (hqp : flatConflictRel q p) :
    p = q := by
  rcases flatPrinciple_rank_cases hp with rfl | rfl
  · rcases flatPrinciple_rank_cases hq with rfl | rfl
    · rfl
    · simp [flatConflictRel, benignPrinciple, harmPrinciple] at hqp
  · rcases flatPrinciple_rank_cases hq with rfl | rfl
    · simp [flatConflictRel, benignPrinciple, harmPrinciple] at hpq
    · rfl

private theorem flatConflictRel_wf :
    WellFounded
      (fun p q : Principle n =>
        p ∈ flatPrinciples n ∧ q ∈ flatPrinciples n ∧
          flatConflictRel p q ∧ ¬ flatConflictRel q p) := by
  refine Subrelation.wf ?_ (InvImage.wf Principle.rank Nat.lt_wfRel.wf)
  intro p q h
  exact lt_of_le_of_ne h.2.2.1
    (fun heq => h.2.2.2 (le_of_eq heq.symm))

/-- The flat harm/benign partition as a special case of a two-principle
constitution with one nontrivial conflict-resolution edge. -/
noncomputable def flatHarmBenignConstitution
    (HarmCategoricalClaim BenignClaim : Fin n → Prop)
    (exhaustive : ∀ claim, HarmCategoricalClaim claim ∨ BenignClaim claim)
    (_disjoint : ∀ claim, ¬ (HarmCategoricalClaim claim ∧ BenignClaim claim)) :
    Constitution n where
  principles := flatPrinciples n
  applies := fun p claim =>
    (p = harmPrinciple n ∧ HarmCategoricalClaim claim) ∨
      (p = benignPrinciple n ∧ BenignClaim claim)
  conflictRel := flatConflictRel
  conflictRel_refl := by
    intro p _hp
    exact le_rfl
  conflictRel_antisymm := by
    intro p q hp hq hpq hqp
    exact flatConflictRel_antisymm hp hq hpq hqp
  conflictRel_trans := by
    intro p q r _hp _hq _hr hpq hqr
    exact le_trans hpq hqr
  conflictRel_wellFounded := flatConflictRel_wf
  resolution := fun _p q _h => q
  resolution_mem := by
    intro p q h hp hq
    exact hq
  resolution_upper_left := by
    intro p q h hp hq
    exact h
  resolution_upper_right := by
    intro p q h hp hq
    exact le_rfl
  complete := by
    intro claim
    rcases exhaustive claim with hharm | hbenign
    · exact ⟨harmPrinciple n, by simp, Or.inl ⟨rfl, hharm⟩⟩
    · exact ⟨benignPrinciple n, by simp, Or.inr ⟨rfl, hbenign⟩⟩
  resolvedPrinciple := fun claim => by
    classical
    exact
      if HarmCategoricalClaim claim then harmPrinciple n else benignPrinciple n
  resolved_mem := by
    classical
    intro claim
    by_cases hharm : HarmCategoricalClaim claim
    · simp [hharm]
    · simp [hharm]
  resolved_applies := by
    classical
    intro claim
    by_cases hharm : HarmCategoricalClaim claim
    · simp [hharm]
    · have hbenign : BenignClaim claim := by
        rcases exhaustive claim with h | h
        · exact False.elim (hharm h)
        · exact h
      simp [hharm, hbenign]
  resolved_resolves := by
    classical
    intro claim p hp happ
    by_cases hharm : HarmCategoricalClaim claim
    · rcases flatPrinciple_rank_cases hp with rfl | rfl
      · norm_num [hharm, flatConflictRel, benignPrinciple, harmPrinciple]
      · norm_num [hharm, flatConflictRel, harmPrinciple]
    · have hbenign : BenignClaim claim := by
        rcases exhaustive claim with h | h
        · exact False.elim (hharm h)
        · exact h
      rcases happ with ⟨hp_harm, hclaim_harm⟩ | ⟨hp_benign, _hclaim_benign⟩
      · exact False.elim (hharm hclaim_harm)
      · simp [hharm, hp_benign, flatConflictRel, benignPrinciple]

theorem flatHarmBenignConstitution_has_conflict_edge
    (HarmCategoricalClaim BenignClaim : Fin n → Prop)
    (exhaustive : ∀ claim, HarmCategoricalClaim claim ∨ BenignClaim claim)
    (disjoint : ∀ claim, ¬ (HarmCategoricalClaim claim ∧ BenignClaim claim)) :
    let C := flatHarmBenignConstitution
      HarmCategoricalClaim BenignClaim exhaustive disjoint
    C.conflictRel (benignPrinciple n) (harmPrinciple n) ∧
      ¬ C.conflictRel (harmPrinciple n) (benignPrinciple n) := by
  intro C
  change flatConflictRel (benignPrinciple n) (harmPrinciple n) ∧
    ¬ flatConflictRel (harmPrinciple n) (benignPrinciple n)
  constructor
  · norm_num [flatHarmBenignConstitution, flatConflictRel,
      benignPrinciple, harmPrinciple]
  · norm_num [flatHarmBenignConstitution, flatConflictRel,
      benignPrinciple, harmPrinciple]

theorem flatHarmBenignConstitution_substantive
    (HarmCategoricalClaim BenignClaim : Fin n → Prop)
    (exhaustive : ∀ claim, HarmCategoricalClaim claim ∨ BenignClaim claim)
    (disjoint : ∀ claim, ¬ (HarmCategoricalClaim claim ∧ BenignClaim claim)) :
    (flatHarmBenignConstitution
      HarmCategoricalClaim BenignClaim exhaustive disjoint).Substantive := by
  refine ⟨benignPrinciple n, harmPrinciple n, ?_, ?_, ?_, ?_, ?_⟩
  · simp [flatHarmBenignConstitution]
  · simp [flatHarmBenignConstitution]
  · exact benignPrinciple_ne_harmPrinciple
  · norm_num [flatHarmBenignConstitution, flatConflictRel,
      benignPrinciple, harmPrinciple]
  · norm_num [flatHarmBenignConstitution, flatConflictRel,
      benignPrinciple, harmPrinciple]

/-- One-principle permit constitution used as the vacuity floor. -/
def vacuousPrinciple (n : Nat) : Principle n where
  name := "vacuous"
  rank := 0
  verdict := BinaryDecision.Permit

def vacuousPrinciples (n : Nat) : Finset (Principle n) :=
  {vacuousPrinciple n}

@[simp] theorem vacuousPrinciple_mem :
    vacuousPrinciple n ∈ vacuousPrinciples n := by
  simp [vacuousPrinciples]

private theorem vacuousPrinciple_eq_of_mem
    {p : Principle n} (hp : p ∈ vacuousPrinciples n) :
    p = vacuousPrinciple n := by
  simpa [vacuousPrinciples] using hp

/-- A one-principle constitution has no substantive conflict surface. -/
def vacuousConstitution (n : Nat) [NeZero n] : Constitution n where
  principles := vacuousPrinciples n
  applies := fun _p _claim => True
  conflictRel := fun p q => p = q
  conflictRel_refl := by
    intro p _hp
    rfl
  conflictRel_antisymm := by
    intro p q _hp _hq hpq _hqp
    exact hpq
  conflictRel_trans := by
    intro p q r _hp _hq _hr hpq hqr
    exact hpq.trans hqr
  conflictRel_wellFounded := by
    refine ⟨fun p => ?_⟩
    refine Acc.intro p ?_
    intro q hq
    exact False.elim (hq.2.2.2 hq.2.2.1.symm)
  resolution := fun _p q _h => q
  resolution_mem := by
    intro p q h hp hq
    exact hq
  resolution_upper_left := by
    intro p q h hp hq
    exact h
  resolution_upper_right := by
    intro p q h hp hq
    rfl
  complete := by
    intro claim
    exact ⟨vacuousPrinciple n, by simp, trivial⟩
  resolvedPrinciple := fun _claim => vacuousPrinciple n
  resolved_mem := by
    intro claim
    simp
  resolved_applies := by
    intro claim
    trivial
  resolved_resolves := by
    intro claim p hp happ
    exact vacuousPrinciple_eq_of_mem hp

theorem vacuousConstitution_not_substantive (n : Nat) [NeZero n] :
    ¬ (vacuousConstitution n).Substantive := by
  rintro ⟨p, q, hp, hq, hpq_ne, hpq, _hqp⟩
  have hp_eq := vacuousPrinciple_eq_of_mem hp
  have hq_eq := vacuousPrinciple_eq_of_mem hq
  exact hpq_ne (hp_eq.trans hq_eq.symm)

end Constitution

end Legitimacy
