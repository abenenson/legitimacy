/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.Protocol
import Mathlib.Data.Fin.Basic

/-!
# Legitimacy.Kernel.CompositionalSafety — Boundary-relative causal soundness

This module formalizes causal soundness for governed boundaries and connects
that boundary-relative notion to graph-level compositional safety for
governance pipelines.

## Main definitions

- `CausalDAG`, `GovernedSet`, and `CausalBoundary` describe the causal model.
- `CausallySoundAt` and `CausalSoundness` state the boundary-relative
  safety criterion.
- `CompositionalSafety` states that denied claims stay denied after
  appending more graph stages.
- `BoundaryRelativeClosed` packages the local closure obligations used
  to prove soundness.

## Main results

- `causal_unsoundness_counterexample` exhibits a concrete governed
  boundary that is not causally sound.
- `causal_closure_sufficient` proves causal soundness from governed-edge
  closure plus boundary contracts.
- `causal_soundness_composition` lifts the same reasoning to unions of governed boundaries.
-/

namespace Legitimacy

-- ═══════════════════════════════════════════════════════════════════
-- § 1. Causal DAG
-- ═══════════════════════════════════════════════════════════════════

/-- A variable in the causal model, identified by a `Fin` index. -/
abbrev Variable (n : ℕ) := Fin n

/-- A causal DAG over `n` variables. Edges represent direct causal
    influence. The DAG property is enforced by requiring edges only
    from lower to higher indices. -/
structure CausalDAG (n : ℕ) where
  /-- `edge i j` means variable `i` directly causes variable `j`. -/
  edge : Fin n → Fin n → Prop
  /-- Edges respect a topological order: causes precede effects. -/
  acyclic : ∀ i j, edge i j → i.val < j.val
  /-- Edge decidability for concrete reasoning. -/
  edge_dec : DecidableRel edge

attribute [instance] CausalDAG.edge_dec

/-- Causal reachability: the transitive closure of the edge relation. -/
inductive CausalReach {n : ℕ} (dag : CausalDAG n) : Fin n → Fin n → Prop where
  | direct {i j : Fin n} : dag.edge i j → CausalReach dag i j
  | trans {i j k : Fin n} :
      CausalReach dag i j → CausalReach dag j k → CausalReach dag i k

/-- Causal reach preserves the topological order. -/
lemma CausalReach.lt {n : ℕ} {dag : CausalDAG n} {i j : Fin n}
    (h : CausalReach dag i j) : i.val < j.val := by
  induction h with
  | direct hedge => exact dag.acyclic _ _ hedge
  | trans _ _ ih₁ ih₂ => exact Nat.lt_trans ih₁ ih₂

/-- A `CausalDAG` has no self-loops. -/
lemma CausalDAG.no_self_loop {n : ℕ} (dag : CausalDAG n) (i : Fin n) :
    ¬ dag.edge i i := by
  intro h
  exact Nat.lt_irrefl i.val (dag.acyclic i i h)

/-- A `CausalDAG` has no directed cycles. -/
lemma CausalDAG.no_cycle {n : ℕ} (dag : CausalDAG n) (i : Fin n) :
    ¬ CausalReach dag i i := by
  intro h
  exact Nat.lt_irrefl i.val h.lt

-- ═══════════════════════════════════════════════════════════════════
-- § 2. Governed variables, boundaries, and actions
-- ═══════════════════════════════════════════════════════════════════

/-- The set of governed variables, represented as a decidable predicate. -/
structure GovernedSet (n : ℕ) where
  /-- Whether variable `v` is governed. -/
  governed : Fin n → Prop
  /-- Decidability for concrete proofs. -/
  dec : DecidablePred governed

attribute [instance] GovernedSet.dec

/-- A declared causal boundary. In this model, the governance boundary is
    the governed set, but keeping the boundary explicit makes the safety
    notion boundary-relative rather than an arbitrary predicate on all
    variables. -/
structure CausalBoundary (n : ℕ) where
  /-- Whether variable `v` lies inside the declared boundary. -/
  contains : Fin n → Prop
  /-- Decidability for concrete proofs. -/
  dec : DecidablePred contains

attribute [instance] CausalBoundary.dec

/-- The governance boundary declared by a governed set. -/
def GovernedSet.boundary {n : ℕ} (gov : GovernedSet n) : CausalBoundary n where
  contains := gov.governed
  dec := gov.dec

/-- Boundary variables are variables paired with a proof that they lie
    inside the declared causal boundary. -/
abbrev BoundaryVar {n : ℕ} (boundary : CausalBoundary n) :=
  { v : Fin n // boundary.contains v }

/-- An action targets one variable. Local safety is interpreted relative
    to a declared boundary-specific safety predicate. -/
structure Action (n : ℕ) where
  /-- The variable this action directly targets. -/
  target : Fin n

/-- A boundary-relative safety predicate. Safety is only stated for
    variables that lie inside the declared causal boundary. -/
structure BoundarySafety {n : ℕ} (boundary : CausalBoundary n) where
  /-- Which boundary variables are safe. -/
  safe : BoundaryVar boundary → Prop

private theorem boundaryVar_eq {n : ℕ} {boundary : CausalBoundary n} {v : Fin n}
    (h₁ h₂ : boundary.contains v) :
    (⟨v, h₁⟩ : BoundaryVar boundary) = ⟨v, h₂⟩ := by
  apply Subtype.ext
  rfl

-- ═══════════════════════════════════════════════════════════════════
-- § 3. Boundary-relative causal soundness
-- ═══════════════════════════════════════════════════════════════════

/-- A governance system is causally sound at action `a` and boundary
    safety predicate `safety` if every governed causal consequence of a
    safe governed action target remains safe. -/
def CausallySoundAt {n : ℕ} (dag : CausalDAG n) (gov : GovernedSet n)
    (a : Action n) (safety : BoundarySafety gov.boundary) : Prop :=
  ∀ htarget : gov.governed a.target,
    safety.safe ⟨a.target, htarget⟩ →
    ∀ w : Fin n, ∀ hw : gov.governed w,
      CausalReach dag a.target w → safety.safe ⟨w, hw⟩

/-- Full causal soundness: every boundary-relative safety predicate
    induced by the declared governance boundary is preserved. -/
def CausalSoundness {n : ℕ} (dag : CausalDAG n) (gov : GovernedSet n) : Prop :=
  ∀ (a : Action n) (safety : BoundarySafety gov.boundary),
    CausallySoundAt dag gov a safety

/-- Graph-level compositional safety: once a graph prefix denies a claimant,
appending further governance stages cannot revive that claim. -/
def CompositionalSafety (G : GovernanceGraph) : Prop :=
  ∀ (H : GovernanceGraph) (claims : List ClaimQ) (k : ClaimantId),
    graphDecide G claims k = BinaryDecision.Deny →
      graphDecide (List.append G H) claims k = BinaryDecision.Deny

/-- Denial by a graph prefix is stable under appending any suffix. -/
theorem graphDecide_append_of_deny
    (G H : GovernanceGraph) (claims : List ClaimQ) (k : ClaimantId)
    (hdeny : graphDecide G claims k = BinaryDecision.Deny) :
    graphDecide (List.append G H) claims k = BinaryDecision.Deny := by
  induction G generalizing claims with
  | nil =>
      simp [graphDecide] at hdeny
  | cons node rest ih =>
      simp [graphDecide, List.append]
      cases hnode : node claims k with
      | Deny =>
          rfl
      | Permit =>
          have hrest :
              graphDecide rest (filterPermitted node claims) k =
                BinaryDecision.Deny := by
            simpa [graphDecide, hnode] using hdeny
          simpa [graphDecide, List.append, hnode] using
            ih (claims := filterPermitted node claims) hrest

/-- Safety propagates across direct governed-to-governed edges. -/
def GovernedEdgeClosed {n : ℕ} (dag : CausalDAG n) (gov : GovernedSet n)
    (safety : BoundarySafety gov.boundary) : Prop :=
  ∀ {v w : Fin n} (hv : gov.governed v) (hw : gov.governed w),
    dag.edge v w → safety.safe ⟨v, hv⟩ → safety.safe ⟨w, hw⟩

/-- A boundary contract on `v → mid` says that once governance hands off
    from governed `v` to ungoverned `mid`, the contract is strong enough
    to recover safety for every governed variable reachable from `mid`. -/
def BoundaryContract {n : ℕ} (dag : CausalDAG n) (gov : GovernedSet n)
    (safety : BoundarySafety gov.boundary) : Prop :=
  ∀ {v mid w : Fin n} (hv : gov.governed v) (hw : gov.governed w),
    ¬ gov.governed mid →
    dag.edge v mid →
    CausalReach dag mid w →
    safety.safe ⟨v, hv⟩ →
    safety.safe ⟨w, hw⟩

/-- Boundary-relative closure packages the two obligations needed for
    non-circular causal soundness: internal safety propagation and
    explicit contracts at every boundary exit. -/
def BoundaryRelativeClosed {n : ℕ} (dag : CausalDAG n) (gov : GovernedSet n)
    (safety : BoundarySafety gov.boundary) : Prop :=
  GovernedEdgeClosed dag gov safety ∧ BoundaryContract dag gov safety

-- ═══════════════════════════════════════════════════════════════════
-- § 4. Causal unsoundness counterexample
-- ═══════════════════════════════════════════════════════════════════

/-- Edge predicate for the 3-variable chain `A → B → C`. -/
private def chainEdge : Fin 3 → Fin 3 → Prop := fun i j =>
  (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 2)

private instance chainEdgeDec : DecidableRel chainEdge := by
  intro i j
  unfold chainEdge
  exact instDecidableOr

/-- A 3-variable causal DAG: `A → B → C`. -/
private def exampleDAG : CausalDAG 3 where
  edge := chainEdge
  acyclic := by
    intro i j h
    unfold chainEdge at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> omega
  edge_dec := chainEdgeDec

/-- Governed predicate: variables `0` and `2` are governed; `1` is not. -/
private def govPred : Fin 3 → Prop := fun v => v.val = 0 ∨ v.val = 2

private instance govPredDec : DecidablePred govPred := by
  intro v
  unfold govPred
  exact instDecidableOr

/-- Governed set: variables `A` and `C` are governed, `B` is not. -/
private def exampleGov : GovernedSet 3 where
  governed := govPred
  dec := govPredDec

/-- An action targeting `A`. -/
private def exampleAction : Action 3 where
  target := ⟨0, by omega⟩

/-- A concrete boundary-relative safety predicate: among governed
    variables, only `A` is safe. This is not a hostile arbitrary `Prop`;
    it is a concrete safety classification on the declared boundary
    `{A, C}`. -/
private def exampleSafety : BoundarySafety exampleGov.boundary where
  safe := fun v => v.1.val = 0

/-- Variable `A` is governed. -/
private theorem a_governed : exampleGov.governed ⟨0, by omega⟩ := by
  show govPred ⟨0, by omega⟩
  unfold govPred
  left
  rfl

/-- Variable `C` is governed. -/
private theorem c_governed : exampleGov.governed ⟨2, by omega⟩ := by
  show govPred ⟨2, by omega⟩
  unfold govPred
  right
  rfl

/-- Edge from `A` to `B`. -/
private theorem edge_a_b : exampleDAG.edge ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  show chainEdge ⟨0, by omega⟩ ⟨1, by omega⟩
  unfold chainEdge
  left
  exact ⟨rfl, rfl⟩

/-- Edge from `B` to `C`. -/
private theorem edge_b_c : exampleDAG.edge ⟨1, by omega⟩ ⟨2, by omega⟩ := by
  show chainEdge ⟨1, by omega⟩ ⟨2, by omega⟩
  unfold chainEdge
  right
  exact ⟨rfl, rfl⟩

/-- `A` causally reaches `C` via `A → B → C`. -/
private theorem a_reaches_c :
    CausalReach exampleDAG ⟨0, by omega⟩ ⟨2, by omega⟩ :=
  CausalReach.trans (CausalReach.direct edge_a_b) (CausalReach.direct edge_b_c)

/-- `A` is safe under the concrete boundary-relative safety predicate. -/
private theorem a_safe :
    exampleSafety.safe ⟨⟨0, by omega⟩, a_governed⟩ := by
  rfl

/-- `C` is not safe under the concrete boundary-relative safety predicate. -/
private theorem c_not_safe :
    ¬ exampleSafety.safe ⟨⟨2, by omega⟩, c_governed⟩ := by
  show ¬ ((⟨2, by omega⟩ : Fin 3).val = 0)
  decide

/-- Causal unsoundness counterexample: a safe action at governed `A`
    causes governed `C` to become unsafe through ungoverned `B`. -/
theorem causal_unsoundness_counterexample :
    ¬ CausallySoundAt exampleDAG exampleGov exampleAction exampleSafety := by
  intro h
  have := h a_governed a_safe ⟨2, by omega⟩ c_governed a_reaches_c
  exact c_not_safe this

-- ═══════════════════════════════════════════════════════════════════
-- § 5. Governed prefixes and first boundary exits
-- ═══════════════════════════════════════════════════════════════════

/-- `GovernedClosure dag gov v w` means there is a causal path from `v`
    to `w` whose every visited node stays inside the governed boundary. -/
inductive GovernedClosure {n : ℕ} (dag : CausalDAG n) (gov : GovernedSet n) :
    Fin n → Fin n → Prop where
  | refl {v : Fin n} : gov.governed v → GovernedClosure dag gov v v
  | step {v x y : Fin n} :
      GovernedClosure dag gov v x →
      gov.governed y →
      dag.edge x y →
      GovernedClosure dag gov v y

/-- The endpoint of a governed prefix is governed. -/
lemma GovernedClosure.endpoint {n : ℕ} {dag : CausalDAG n} {gov : GovernedSet n}
    {v w : Fin n} (h : GovernedClosure dag gov v w) : gov.governed w := by
  induction h with
  | refl hv => exact hv
  | step _ hw _ _ => exact hw

/-- Governed prefixes compose. -/
lemma GovernedClosure.trans {n : ℕ} {dag : CausalDAG n} {gov : GovernedSet n}
    {u v w : Fin n}
    (huv : GovernedClosure dag gov u v)
    (hvw : GovernedClosure dag gov v w) :
    GovernedClosure dag gov u w := by
  induction hvw with
  | refl _ => exact huv
  | step hprefix hw hedge ih => exact GovernedClosure.step ih hw hedge

/-- Safety propagates along any governed prefix once it propagates across
    single governed-to-governed edges. -/
lemma safety_of_governed_closure {n : ℕ} {dag : CausalDAG n} {gov : GovernedSet n}
    {safety : BoundarySafety gov.boundary}
    (hclosed : GovernedEdgeClosed dag gov safety)
    {v w : Fin n}
    (hpath : GovernedClosure dag gov v w) :
    ∀ hv : gov.governed v, ∀ hw : gov.governed w,
      safety.safe ⟨v, hv⟩ → safety.safe ⟨w, hw⟩ := by
  induction hpath with
  | refl hv0 =>
      intro hv hw hsafe
      have hEq : (⟨v, hv⟩ : BoundaryVar gov.boundary) = ⟨v, hw⟩ :=
        (boundaryVar_eq hv hv0).trans (boundaryVar_eq hv0 hw)
      cases hEq
      exact hsafe
  | step hprefix hy hedge ih =>
      rename_i x y
      intro hv hw hsafe
      have hx : gov.governed x := GovernedClosure.endpoint hprefix
      have hsafe_x : safety.safe ⟨x, hx⟩ := ih hv hx hsafe
      exact hclosed hx hw hedge hsafe_x

/-- A direct governed edge to a governed endpoint yields an entirely governed
prefix. -/
lemma reach_from_governed_direct_inside {n : ℕ}
    {dag : CausalDAG n} {gov : GovernedSet n}
    {v w : Fin n}
    (hv : gov.governed v) (hw : gov.governed w) (hedge : dag.edge v w) :
    gov.governed w ∧ GovernedClosure dag gov v w :=
  ⟨hw, GovernedClosure.step (GovernedClosure.refl hv) hw hedge⟩

/-- A direct governed edge to an ungoverned endpoint already exhibits the
first boundary exit. -/
lemma reach_from_governed_direct_exit {n : ℕ}
    {dag : CausalDAG n} {gov : GovernedSet n}
    {v w : Fin n}
    (hv : gov.governed v) (hw : ¬ gov.governed w) (hedge : dag.edge v w) :
    ∃ x y : Fin n,
      GovernedClosure dag gov v x ∧
      ¬ gov.governed y ∧
      dag.edge x y ∧
      (y = w ∨ CausalReach dag y w) :=
  ⟨v, w, GovernedClosure.refl hv, hw, hedge, Or.inl rfl⟩

/-- A governed prefix followed by a fully governed suffix remains fully
governed. -/
lemma reach_from_governed_compose_inside {n : ℕ}
    {dag : CausalDAG n} {gov : GovernedSet n}
    {v x w : Fin n}
    (hprefix : GovernedClosure dag gov v x)
    (hinside : gov.governed w ∧ GovernedClosure dag gov x w) :
    gov.governed w ∧ GovernedClosure dag gov v w := by
  rcases hinside with ⟨hw, hsuffix⟩
  exact ⟨hw, GovernedClosure.trans hprefix hsuffix⟩

/-- If a later segment exhibits the first exit from governance, an earlier
governed prefix extends that same witness back to the start. -/
lemma reach_from_governed_compose_exit {n : ℕ}
    {dag : CausalDAG n} {gov : GovernedSet n}
    {v j w : Fin n}
    (hprefix : GovernedClosure dag gov v j)
    (hexit : ∃ x y : Fin n,
      GovernedClosure dag gov j x ∧
      ¬ gov.governed y ∧
      dag.edge x y ∧
      (y = w ∨ CausalReach dag y w)) :
    ∃ x y : Fin n,
      GovernedClosure dag gov v x ∧
      ¬ gov.governed y ∧
      dag.edge x y ∧
      (y = w ∨ CausalReach dag y w) := by
  rcases hexit with ⟨x, y, hprefix₂, hy, hedge, hyw⟩
  exact ⟨x, y, GovernedClosure.trans hprefix hprefix₂, hy, hedge, hyw⟩

/-- Safety at the start of a governed prefix propagates to its endpoint. -/
lemma safety_of_governed_prefix_endpoint {n : ℕ}
    {dag : CausalDAG n} {gov : GovernedSet n}
    {safety : BoundarySafety gov.boundary}
    (hclosed : GovernedEdgeClosed dag gov safety)
    {v x : Fin n}
    (hprefix : GovernedClosure dag gov v x)
    (hv : gov.governed v)
    (hsafe : safety.safe ⟨v, hv⟩) :
    safety.safe ⟨x, GovernedClosure.endpoint hprefix⟩ :=
  safety_of_governed_closure hclosed hprefix hv (GovernedClosure.endpoint hprefix) hsafe

/-- Any causal path beginning at a governed variable either stays within
    governed variables or has a first exit edge from a governed prefix to
    an ungoverned variable. -/
lemma reach_from_governed_decomposition {n : ℕ}
    {dag : CausalDAG n} {gov : GovernedSet n}
    {v w : Fin n}
    (hv : gov.governed v)
    (hreach : CausalReach dag v w) :
    (gov.governed w ∧ GovernedClosure dag gov v w) ∨
      ∃ x y : Fin n,
        GovernedClosure dag gov v x ∧
        ¬ gov.governed y ∧
        dag.edge x y ∧
        (y = w ∨ CausalReach dag y w) := by
  induction hreach with
  | direct hedge =>
      rename_i i j
      by_cases hj : gov.governed j
      · left
        exact reach_from_governed_direct_inside hv hj hedge
      · right
        exact reach_from_governed_direct_exit hv hj hedge
  | trans hij hjw ih₁ ih₂ =>
      rename_i i j k
      rcases ih₁ hv with hinside | hexit
      · rcases hinside with ⟨hj, hprefix⟩
        rcases ih₂ hj with hinside₂ | hexit₂
        · rcases hinside₂ with ⟨hw, hsuffix⟩
          left
          exact reach_from_governed_compose_inside hprefix ⟨hw, hsuffix⟩
        · right
          exact reach_from_governed_compose_exit hprefix hexit₂
      · right
        rcases hexit with ⟨x, y, hprefix, hy, hedge, hyj | hyj⟩
        · subst hyj
          exact ⟨x, y, hprefix, hy, hedge, Or.inr hjw⟩
        · exact ⟨x, y, hprefix, hy, hedge, Or.inr (CausalReach.trans hyj hjw)⟩

-- ═══════════════════════════════════════════════════════════════════
-- § 6. Sufficient condition: boundary-relative closure
-- ═══════════════════════════════════════════════════════════════════

/-- A governed set is causally closed if every causal consequence of a
    governed variable remains governed. This is stronger than the
    boundary-relative theorem below: when it holds, there are no boundary
    exits at all. -/
def CausallyClosed {n : ℕ} (dag : CausalDAG n) (gov : GovernedSet n) : Prop :=
  ∀ (v w : Fin n), gov.governed v → CausalReach dag v w → gov.governed w

/-- If boundary-relative safety is preserved along governed edges and
    every governed-to-ungoverned edge has an explicit contract covering
    its downstream governed effects, then no causal bypass remains and
    the governance system is causally sound. -/
theorem causal_closure_sufficient {n : ℕ}
    (dag : CausalDAG n) (gov : GovernedSet n)
    (boundary_closed :
      ∀ safety : BoundarySafety gov.boundary, BoundaryRelativeClosed dag gov safety) :
    CausalSoundness dag gov := by
  intro a safety htarget hsafe_target w hw hreach
  obtain ⟨hclosed, hcontract⟩ := boundary_closed safety
  rcases reach_from_governed_decomposition (gov := gov) htarget hreach with
    hinside | hexit
  · rcases hinside with ⟨_, hprefix⟩
    exact safety_of_governed_closure hclosed hprefix htarget hw hsafe_target
  · rcases hexit with ⟨x, y, hprefix, hy, hedge, hyw | hyw⟩
    · exact False.elim (hy (hyw ▸ hw))
    · have hx : gov.governed x := GovernedClosure.endpoint hprefix
      have hsafe_x : safety.safe ⟨x, hx⟩ :=
        safety_of_governed_prefix_endpoint hclosed hprefix htarget hsafe_target
      exact hcontract hx hw hy hedge hyw hsafe_x

-- ═══════════════════════════════════════════════════════════════════
-- § 7. The ungoverned causal path theorem
-- ═══════════════════════════════════════════════════════════════════

/-- An ungoverned causal path exists from `v` to `w` if some ungoverned
    midpoint lies on a causal path from `v` to `w`. -/
def HasUngovernedPath {n : ℕ} (dag : CausalDAG n) (gov : GovernedSet n)
    (v w : Fin n) : Prop :=
  ∃ mid : Fin n, ¬ gov.governed mid ∧ CausalReach dag v mid ∧ CausalReach dag mid w

/-- `B` is not governed in the running example. -/
private theorem b_not_governed : ¬ exampleGov.governed ⟨1, by omega⟩ := by
  show ¬ govPred ⟨1, by omega⟩
  unfold govPred
  decide

/-- The example DAG has an ungoverned path from `A` to `C` via `B`. -/
lemma example_has_ungoverned_path :
    HasUngovernedPath exampleDAG exampleGov ⟨0, by omega⟩ ⟨2, by omega⟩ :=
  ⟨⟨1, by omega⟩, b_not_governed, CausalReach.direct edge_a_b, CausalReach.direct edge_b_c⟩

/-- If governance is not causally closed, some governed variable reaches
    an ungoverned variable. -/
lemma not_closed_has_ungoverned_witness {n : ℕ}
    (dag : CausalDAG n) (gov : GovernedSet n)
    (not_closed : ¬ CausallyClosed dag gov) :
    ∃ v w : Fin n, gov.governed v ∧ CausalReach dag v w ∧ ¬ gov.governed w := by
  simp only [CausallyClosed] at not_closed
  push Not at not_closed
  exact not_closed

-- ═══════════════════════════════════════════════════════════════════
-- § 8. Composition under causal structure
-- ═══════════════════════════════════════════════════════════════════

/-- Two governed sets compose by union. -/
def GovernedSet.union {n : ℕ} (g₁ g₂ : GovernedSet n) : GovernedSet n where
  governed := fun v => g₁.governed v ∨ g₂.governed v
  dec := by
    intro v
    exact instDecidableOr

/-- The non-circular boundary-relative soundness proof composes under
    union of governed boundaries. -/
theorem causal_soundness_composition {n : ℕ}
    (dag : CausalDAG n) (g₁ g₂ : GovernedSet n)
    (boundary_closed :
      ∀ safety : BoundarySafety (g₁.union g₂).boundary,
        BoundaryRelativeClosed dag (g₁.union g₂) safety) :
    CausalSoundness dag (g₁.union g₂) :=
  causal_closure_sufficient dag (g₁.union g₂) boundary_closed

-- ═══════════════════════════════════════════════════════════════════
-- § 9. Connection to governance impossibility
-- ═══════════════════════════════════════════════════════════════════

/-- Non-closure exposes a governed variable whose causal influence leaves
    the declared governance boundary. -/
lemma causal_governance_bridge {n : ℕ}
    (dag : CausalDAG n) (gov : GovernedSet n)
    (not_closed : ¬ CausallyClosed dag gov) :
    ∃ v w : Fin n, gov.governed v ∧ ¬ gov.governed w ∧ CausalReach dag v w := by
  obtain ⟨v, w, hv, hr, hw⟩ := not_closed_has_ungoverned_witness dag gov not_closed
  exact ⟨v, w, hv, hw, hr⟩

end Legitimacy
