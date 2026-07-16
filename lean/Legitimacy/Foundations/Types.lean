/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Legitimacy.Foundations.Types — Foundational types over ordered fields

This module defines the core legitimacy types (`ClaimantId`, `Claim`, `Estate`,
`AllocationRule`) parameterised by a type `F` carrying `[Field F]`,
`[LinearOrder F]`, and `[IsStrictOrderedRing F]` (the Mathlib v4.29+
encoding of a linearly-ordered field).

Downstream files can instantiate at `ℚ` (decidable, computable) or at `ℝ`
(analysis) or at any other ordered field.

## Design notes

- `ClaimantId` remains `ℕ` (decidable equality, linearly ordered).
- `Claim F` carries `strength : F` with a proof `0 < strength`, plus
  structured string metadata used by source-shaped audit predicates.
- `AllocationRule F` operates on `List (Claim F)` matching the Rust interface.
- Arithmetic helpers are backed by Mathlib lemmas (`linarith`, `positivity`).
- `ℚ` aliases (`ClaimQ`, `EstateQ`, …) at the end.

## References

* H. Peyton Young, *Equity: In Theory and Practice*, 1994.
-/

namespace Legitimacy

/-! ### Identifiers -/

/-- A claimant identifier. `ℕ` for decidable equality and linear order. -/
abbrev ClaimantId := ℕ

/-! ### Claims -/

/-- A claim: a claimant's measured entitlement with a strictly positive strength
and optional structured metadata. The metadata is intentionally stringly typed:
it mirrors source-level hook payload fields without imposing a schema on the
foundational ordered-field layer. -/
structure Claim (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] where
  /-- The claimant this claim belongs to. -/
  id : ClaimantId
  /-- The measured strength of the claim. -/
  strength : F
  /-- Strength is strictly positive. -/
  strength_pos : 0 < strength
  /-- Source-shaped metadata fields attached to this claim. -/
  metadata : List (String × String)

instance {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Repr F] :
    Repr (Claim F) where
  reprPrec c n := reprPrec (c.id, c.strength, c.metadata) n

instance {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [DecidableEq F] :
    DecidableEq (Claim F) :=
  fun a b =>
    if hid : a.id = b.id then
      if hstr : a.strength = b.strength then
        if hmetadata : a.metadata = b.metadata then
          isTrue (by
            cases a
            cases b
            simp at hid hstr hmetadata
            subst hid
            subst hstr
            subst hmetadata
            rfl)
        else
          isFalse (fun h => hmetadata (by cases h; rfl))
      else
        isFalse (fun h => hstr (by cases h; rfl))
    else
      isFalse (fun h => hid (by cases h; rfl))

instance : Inhabited (Claim ℚ) where
  default := ⟨0, 1, by norm_num, []⟩

namespace Claim

/-- Look up a metadata field on a single claim. The first matching key wins. -/
def lookup {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (claim : Claim F) (field : String) : Option String :=
  (claim.metadata.find? (fun entry => entry.1 == field)).map Prod.snd

/-- Scale a claim's strength while preserving identity and metadata. -/
def scaleStrength {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (claim : Claim F) (α : F) (hα : 0 < α) : Claim F where
  id := claim.id
  strength := α * claim.strength
  strength_pos := mul_pos hα claim.strength_pos
  metadata := claim.metadata

@[simp] theorem scaleStrength_id
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (claim : Claim F) (α : F) (hα : 0 < α) :
    (claim.scaleStrength α hα).id = claim.id :=
  rfl

@[simp] theorem scaleStrength_strength
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (claim : Claim F) (α : F) (hα : 0 < α) :
    (claim.scaleStrength α hα).strength = α * claim.strength :=
  rfl

@[simp] theorem scaleStrength_metadata
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (claim : Claim F) (α : F) (hα : 0 < α) :
    (claim.scaleStrength α hα).metadata = claim.metadata :=
  rfl

@[simp] theorem lookup_scaleStrength
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (claim : Claim F) (field : String) (α : F) (hα : 0 < α) :
    (claim.scaleStrength α hα).lookup field = claim.lookup field :=
  rfl

end Claim

namespace ClaimProfile

/-- Find the claim for a subject inside a list-backed claim profile. -/
def findSubject? : List (Claim ℚ) → ClaimantId → Option (Claim ℚ)
  | [], _ => none
  | claim :: rest, subject =>
      if claim.id == subject then some claim else findSubject? rest subject

/-- Look up a metadata field on the claim matched by `subject`. -/
def lookup (profile : List (Claim ℚ)) (subject : ClaimantId) (field : String) :
    Option String :=
  (findSubject? profile subject).bind (fun claim => claim.lookup field)

@[simp] theorem lookup_nil (subject : ClaimantId) (field : String) :
    lookup ([] : List (Claim ℚ)) subject field = none := by
  rfl

theorem lookup_scaleStrength
    (profile : List (Claim ℚ)) (subject : ClaimantId) (field : String)
    (α : ℚ) (hα : 0 < α) :
    lookup (profile.map (fun claim => claim.scaleStrength α hα)) subject field =
      lookup profile subject field := by
  induction profile with
  | nil =>
      rfl
  | cons claim rest ih =>
      by_cases hsubject : claim.id = subject
      · simp [lookup, findSubject?, Claim.scaleStrength, Claim.lookup, hsubject]
      · have hbeq : (claim.id == subject) = false := by
          simp [BEq.beq, hsubject]
        simp [lookup, findSubject?, Claim.scaleStrength, Claim.lookup, hbeq]
        exact ih

end ClaimProfile

/-! ### Estate -/

/-- The estate (divisible resource) to be allocated.
Mirrors Rust's `Estate { total, unit }`. -/
structure Estate (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] where
  /-- Total amount to be divided. -/
  total : F
  /-- Total is strictly positive. -/
  total_pos : 0 < total

instance {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Repr F] :
    Repr (Estate F) where
  reprPrec e n := reprPrec e.total n

instance {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [DecidableEq F] :
    DecidableEq (Estate F) :=
  fun a b =>
    if h : a.total = b.total then
      isTrue (by cases a; cases b; simp at h; subst h; rfl)
    else
      isFalse (fun h' => h (by cases h'; rfl))

/-! ### Allocation rules -/

/-- An allocation rule maps a list of claims, an estate, and a claimant id
to the amount allocated. This is the curried form matching the Rust
`Rule.allocate` interface. -/
def AllocationRule (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] :=
  List (Claim F) → Estate F → ClaimantId → F

/-! ### Claims-list predicates -/

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Claims have pairwise distinct IDs. -/
def ClaimsDistinct (claims : List (Claim F)) : Prop :=
  (claims.map Claim.id).Nodup

/-- A claimant ID appears in the claims list. -/
def InClaims (k : ClaimantId) (claims : List (Claim F)) : Prop :=
  ∃ c ∈ claims, c.id = k

instance (k : ClaimantId) (claims : List (Claim F)) : Decidable (InClaims k claims) :=
  inferInstanceAs (Decidable (∃ c ∈ claims, c.id = k))

/-! ### List operations -/

/-- Remove the first claim with the given ID. -/
def removeClaim (k : ClaimantId) : List (Claim F) → List (Claim F)
  | [] => []
  | c :: cs => if c.id = k then cs else c :: removeClaim k cs

/-- Sum of all claim strengths. -/
def totalStrength : List (Claim F) → F
  | [] => 0
  | c :: cs => c.strength + totalStrength cs

/-- Look up the strength of claimant `k`. Returns 0 if not found. -/
def lookupStrength (k : ClaimantId) : List (Claim F) → F
  | [] => 0
  | c :: cs => if c.id = k then c.strength else lookupStrength k cs

/-- Replace the strength of the first claim with id `k`. -/
def strengthenClaim (k : ClaimantId) (newStr : F) (hpos : 0 < newStr) :
    List (Claim F) → List (Claim F)
  | [] => []
  | c :: cs =>
    if c.id = k
    then ⟨c.id, newStr, hpos, c.metadata⟩ :: cs
    else c :: strengthenClaim k newStr hpos cs

theorem ClaimProfile.lookup_strengthenClaim
    (profile : List (Claim ℚ)) (subject k : ClaimantId) (field : String)
    (s' : ℚ) (hs' : 0 < s') :
    ClaimProfile.lookup (strengthenClaim k s' hs' profile) subject field =
      ClaimProfile.lookup profile subject field := by
  induction profile with
  | nil =>
      rfl
  | cons claim rest ih =>
      by_cases hk : claim.id = k
      · by_cases hsubject : claim.id = subject
        · subst subject
          simp [ClaimProfile.lookup, ClaimProfile.findSubject?,
            strengthenClaim, Claim.lookup, hk]
        · have hbeq : (claim.id == subject) = false := by
            simp [BEq.beq, hsubject]
          have hksubject : k ≠ subject := by
            intro h
            exact hsubject (hk.trans h)
          simp [ClaimProfile.lookup, ClaimProfile.findSubject?,
            strengthenClaim, Claim.lookup, hk, hksubject]
      · by_cases hsubject : claim.id = subject
        · subst subject
          have hbeq : (claim.id == claim.id) = true := by
            simp
          simp [ClaimProfile.lookup, ClaimProfile.findSubject?,
            strengthenClaim, Claim.lookup, hk]
        · have hbeq : (claim.id == subject) = false := by
            simp [BEq.beq, hsubject]
          simp [ClaimProfile.lookup, ClaimProfile.findSubject?,
            strengthenClaim, Claim.lookup, hk, hsubject]
          exact ih

/-! ### Core lemmas (Mathlib-backed) -/

/-- The total strength of any claims list is nonnegative. -/
lemma totalStrength_nonneg (claims : List (Claim F)) :
    0 ≤ totalStrength claims := by
  induction claims with
  | nil => simp [totalStrength]
  | cons c cs ih =>
    simp only [totalStrength]
    linarith [c.strength_pos]

/-- A nonempty claims list has strictly positive total strength. -/
theorem totalStrength_pos {claims : List (Claim F)} (h : claims ≠ []) :
    0 < totalStrength claims := by
  match claims, h with
  | c :: cs, _ =>
    simp only [totalStrength]
    linarith [c.strength_pos, totalStrength_nonneg cs]

/-- Looking up the strength of a claimant present in the list yields a positive
value. -/
theorem lookupStrength_pos_of_mem {k : ClaimantId} {claims : List (Claim F)}
    (hmem : InClaims k claims) : 0 < lookupStrength k claims := by
  induction claims with
  | nil =>
    exfalso
    obtain ⟨_, h, _⟩ := hmem
    exact List.not_mem_nil h
  | cons c cs ih =>
    simp only [lookupStrength]
    split
    case isTrue _ => exact c.strength_pos
    case isFalse hne =>
      apply ih
      obtain ⟨c', hc'mem, hc'id⟩ := hmem
      cases hc'mem with
      | head => exact absurd hc'id hne
      | tail _ htail => exact ⟨c', htail, hc'id⟩

/-- A claimant's looked-up strength is bounded above by the total strength of
the whole profile. -/
theorem lookupStrength_le_totalStrength {k : ClaimantId} {claims : List (Claim F)}
    (hmem : InClaims k claims) :
    lookupStrength k claims ≤ totalStrength claims := by
  induction claims with
  | nil =>
    exfalso
    obtain ⟨_, h, _⟩ := hmem
    exact List.not_mem_nil h
  | cons c cs ih =>
    simp only [lookupStrength, totalStrength]
    split
    case isTrue _ =>
      linarith [totalStrength_nonneg cs]
    case isFalse hne =>
      have hmem' : InClaims k cs := by
        obtain ⟨c', hc'mem, hc'id⟩ := hmem
        cases hc'mem with
        | head => exact absurd hc'id hne
        | tail _ htail => exact ⟨c', htail, hc'id⟩
      linarith [ih hmem', c.strength_pos]

/-! ### Claims distinctness helpers -/

/-- Distinctness of claimant IDs is preserved when taking the tail of a claims
list. -/
theorem ClaimsDistinct_tail {c : Claim F} {cs : List (Claim F)}
    (h : ClaimsDistinct (c :: cs)) : ClaimsDistinct cs :=
  (List.pairwise_cons.mp h).2

/-- In a distinct claims list, the head claimant ID does not reappear in the
tail. -/
theorem ClaimsDistinct_head_not_in_tail {c : Claim F} {cs : List (Claim F)}
    (h : ClaimsDistinct (c :: cs)) : c.id ∉ (cs.map Claim.id) := by
  have ⟨hall, _⟩ := List.pairwise_cons.mp h
  intro hmem
  exact absurd rfl (hall c.id hmem)

/-- If claimant `k` is present in a cons list and the head has a different ID,
then `k` is present in the tail. -/
theorem InClaims_tail {k : ClaimantId} {c : Claim F} {cs : List (Claim F)}
    (hmem : InClaims k (c :: cs)) (hne : c.id ≠ k) :
    InClaims k cs := by
  obtain ⟨c', hc'mem, hc'id⟩ := hmem
  cases hc'mem with
  | head => exact absurd hc'id hne
  | tail _ htail => exact ⟨c', htail, hc'id⟩

end OrderedField

/-! ### Finset view

For axiom statements that benefit from finite-set reasoning, we provide a
`ClaimSet` bundling a `Finset` of claims with a distinctness proof. -/

/-- A finite set of claims with distinct IDs. -/
structure ClaimSet (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [DecidableEq F] where
  /-- The underlying finset. -/
  claims : Finset (Claim F)
  /-- All IDs in the set are pairwise distinct. -/
  ids_distinct : (claims.val.map Claim.id).Nodup

/-! ### ℚ backward-compatibility aliases -/

/-- `Claim` specialised to `ℚ`. -/
abbrev ClaimQ := Claim ℚ

/-- `Estate` specialised to `ℚ`. -/
abbrev EstateQ := Estate ℚ

/-- `AllocationRule` specialised to `ℚ`. -/
abbrev AllocationRuleQ := AllocationRule ℚ

/-- `ClaimSet` specialised to `ℚ`. -/
abbrev ClaimSetQ := ClaimSet ℚ

end Legitimacy
