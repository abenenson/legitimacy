/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.Composition

/-!
# Legitimacy.Attacks.Decomposition

Composition-sensitive semantic monotonicity for sequential governance actions.
-/

set_option autoImplicit false

namespace Legitimacy

variable {σ α : Type*}

/-- Sequential semantic hash induced by a composition algebra. -/
def seqHash (compose : σ → α → σ) (unit : σ) : List α → σ :=
  List.foldl compose unit

@[simp] theorem seqHash_nil (compose : σ → α → σ) (unit : σ) :
    seqHash compose unit [] = unit := rfl

@[simp] theorem seqHash_cons (compose : σ → α → σ) (unit : σ) (a : α) (as : List α) :
    seqHash compose unit (a :: as) = seqHash compose (compose unit a) as := rfl

/-- Folding over an appended action trace is the same as first hashing the
prefix and then continuing from that intermediate state on the suffix. -/
lemma seqHash_append (compose : σ → α → σ) (unit : σ) (as bs : List α) :
    seqHash compose unit (as ++ bs) = seqHash compose (seqHash compose unit as) bs := by
  simp [seqHash, List.foldl_append]

/-- Appending a single action updates the hash by one composition step. -/
lemma seqHash_append_single (compose : σ → α → σ) (unit : σ) (as : List α) (a : α) :
    seqHash compose unit (as ++ [a]) = compose (seqHash compose unit as) a := by
  simp [seqHash, List.foldl_append]

/-- Composition-sensitive semantic monotonicity:
the last step of any denied composition cannot be permitted. -/
def CompSemanticMonotone
    (compose : σ → α → σ) (unit : σ)
    (node : σ → α → Decision3) (denied : σ → Prop) : Prop :=
  ∀ as, denied (seqHash compose unit as) → ∀ hne : as ≠ [],
    node (seqHash compose unit as.dropLast) (as.getLast hne) ≠ Decision3.Permit

/-- A permitting decomposition whose full composition lands in the denied set. -/
structure Decomposition
    (compose : σ → α → σ) (unit : σ)
    (node : σ → α → Decision3) (denied : σ → Prop) where
  steps : List α
  nonempty : steps ≠ []
  each_permits : ∀ i : Fin steps.length,
    node (seqHash compose unit (steps.take i.val)) (steps.get i) = Decision3.Permit
  denied_at_end : denied (seqHash compose unit steps)

/-- Any composition-sensitive monotone node forces some step in a denied
decomposition witness to be non-permitting at the moment it is taken. -/
lemma csm_immune_to_decomposition
    {σ α : Type*}
    (compose : σ → α → σ) (unit : σ)
    (node : σ → α → Decision3) (denied : σ → Prop)
    (hcsm : CompSemanticMonotone compose unit node denied)
    (d : Decomposition compose unit node denied) :
    ∃ i : Fin d.steps.length,
      node (seqHash compose unit (d.steps.take i.val)) (d.steps.get i) = Decision3.Deny ∨
      node (seqHash compose unit (d.steps.take i.val)) (d.steps.get i) = Decision3.Escalate := by
  have hlen : 0 < d.steps.length := by
    cases hs : d.steps with
    | nil => cases d.nonempty hs
    | cons _ _ => simp
  let i : Fin d.steps.length := ⟨d.steps.length - 1, by omega⟩
  refine ⟨i, ?_⟩
  have hdrop : d.steps.dropLast = d.steps.take i.val := by
    simp [i, List.dropLast_eq_take]
  have hget : d.steps.get i = d.steps.getLast d.nonempty := by
    simpa [i] using
      (List.get_length_sub_one (l := d.steps) (h := by omega))
  have hnot :
      node (seqHash compose unit (d.steps.take i.val)) (d.steps.get i) ≠ Decision3.Permit := by
    have hcsm_last := hcsm d.steps d.denied_at_end d.nonempty
    rw [hdrop, ← hget] at hcsm_last
    exact hcsm_last
  cases hdec :
      node (seqHash compose unit (d.steps.take i.val)) (d.steps.get i) with
  | Permit =>
      exact False.elim (hnot hdec)
  | Deny =>
      exact Or.inl rfl
  | Escalate =>
      exact Or.inr rfl

/-- A composition-sensitive monotone node rules out decompositions whose every
step locally permits while the full composition is globally denied. -/
theorem csm_no_permitting_decomposition
    {σ α : Type*}
    (compose : σ → α → σ) (unit : σ)
    (node : σ → α → Decision3) (denied : σ → Prop)
    (hcsm : CompSemanticMonotone compose unit node denied)
    (d : Decomposition compose unit node denied) : False := by
  rcases csm_immune_to_decomposition compose unit node denied hcsm d with ⟨i, hi⟩
  have hperm := d.each_permits i
  cases hi with
  | inl hdeny =>
      exact Decision3.noConfusion (hdeny.symm.trans hperm)
  | inr hesc =>
      exact Decision3.noConfusion (hesc.symm.trans hperm)

/-- Local permission monotonicity failure: the per-step local permit relation
does not satisfy composition-sensitive semantic monotonicity. -/
def LocalPermissionMonotonicity (compose : σ → α → σ) (unit : σ)
    (node : σ → α → Decision3) (denied : σ → Prop) : Prop :=
  ¬ CompSemanticMonotone compose unit node denied

/-- The decomposition-attack class is inhabited by an embedded decomposition
witness: a nonempty action sequence whose local steps all permit while the
composed state is denied. -/
def DecompositionAttackClass (compose : σ → α → σ) (unit : σ)
    (node : σ → α → Decision3) (denied : σ → Prop) : Prop :=
  Nonempty (Decomposition compose unit node denied)

/-- Any admitted decomposition attack directly witnesses local permission
monotonicity failure. -/
theorem localPermissionMonotonicity_of_decompositionAttackClass
    {compose : σ → α → σ} {unit : σ}
    {node : σ → α → Decision3} {denied : σ → Prop}
    (hattack : DecompositionAttackClass compose unit node denied) :
    LocalPermissionMonotonicity compose unit node denied := by
  intro hcsm
  rcases hattack with ⟨d⟩
  exact csm_no_permitting_decomposition compose unit node denied hcsm d

/-- Constant-kernel floor: the decomposition-attack class is nonvacuous. A
constant composition algebra with an everywhere-permitting local node and an
everywhere-denied composed predicate supplies a one-step denial witness. -/
theorem decompositionAttackClass_nonvacuous :
    ∃ (compose : Unit → Unit → Unit) (base : Unit)
      (node : Unit → Unit → Decision3) (denied : Unit → Prop),
      LocalPermissionMonotonicity compose base node denied ∧
        DecompositionAttackClass compose base node denied := by
  refine ⟨(fun s _ => s), (), (fun _ _ => Decision3.Permit),
    (fun _ => True), ?_, ?_⟩
  · intro hcsm
    have hlast :
        (fun _ _ => Decision3.Permit)
            (seqHash (fun s _ => s) () [()].dropLast)
            ([()].getLast (by simp)) ≠ Decision3.Permit :=
      hcsm [()] trivial (by simp)
    exact hlast rfl
  · refine ⟨
      { steps := [()]
        nonempty := by simp
        each_permits := ?_
        denied_at_end := trivial }⟩
    intro i
    rfl

/-- Strict refinement: decomposition attacks imply a composition-sensitive
monotonicity failure, but not every monotonicity failure admits a decomposition
whose every local step permits. -/
theorem decompositionAttackClass_strict_refinement_of_csm_failure :
    ∃ (compose : Nat → Unit → Nat) (base : Nat)
      (node : Nat → Unit → Decision3) (denied : Nat → Prop),
      ¬ CompSemanticMonotone compose base node denied ∧
        ¬ DecompositionAttackClass compose base node denied := by
  let compose : Nat → Unit → Nat := fun s _ => s + 1
  let node : Nat → Unit → Decision3 :=
    fun s _ => if s = 1 then Decision3.Permit else Decision3.Deny
  let denied : Nat → Prop := fun s => s = 2
  refine ⟨compose, 0, node, denied, ?_, ?_⟩
  · intro hcsm
    have hlast :
        node (seqHash compose 0 [(), ()].dropLast)
            ([(), ()].getLast (by simp)) ≠ Decision3.Permit :=
      hcsm [(), ()] (by simp [denied, seqHash, compose]) (by simp)
    exact hlast (by simp [node, seqHash, compose])
  · intro hclass
    rcases hclass with ⟨d⟩
    have hlen : d.steps.length = 2 := by
      simpa [denied, seqHash, compose] using d.denied_at_end
    have hpos : 0 < d.steps.length := by omega
    let first : Fin d.steps.length := ⟨0, hpos⟩
    have hperm := d.each_permits first
    have hdeny :
        node (seqHash compose 0 (d.steps.take first.val))
            (d.steps.get first) = Decision3.Deny := by
      simp [first, node, seqHash]
    exact Decision3.noConfusion (hdeny.symm.trans hperm)

end Legitimacy
