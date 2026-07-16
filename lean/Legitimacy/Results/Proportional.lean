/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Diagnostics.AllocationRule
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
  Proportional allocation rule — generalized to LinearOrderedField F.

  Generalizes the original `ℚ`-hardcoded proportional proofs to any
  `[Field F] [LinearOrder F] [IsStrictOrderedRing F]` (the Mathlib v4.29
  replacement for the deprecated `LinearOrderedField`).  `field_simp` and
  `ring` work over any field; `linarith` and `nlinarith` work over any
  linearly ordered strict-ordered ring.

  Zero sorry, zero axiom.
-/

namespace Legitimacy

section GenField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

-- ═══════════════════════════════════════════════════════════════════
-- Proportional rule definition
-- ═══════════════════════════════════════════════════════════════════

/-- Proportional allocation: each claimant gets
    `(their strength / total strength) * estate`.
    Returns 0 when total strength is zero (degenerate case). -/
def proportionalRule : AllocationRule F := fun claims estate k =>
  let s := lookupStrength k claims
  let S := totalStrength claims
  if S = 0 then 0
  else s / S * estate.total

-- ═══════════════════════════════════════════════════════════════════
-- removeClaim lemmas
-- ═══════════════════════════════════════════════════════════════════

/-- Removing claimant `k` preserves membership of any different claim already
present in the profile. -/
lemma removeClaim_preserves_other {k : ClaimantId} {c : Claim F}
    {claims : List (Claim F)}
    (hmem : c ∈ claims) (hid : c.id = k → False) :
    c ∈ removeClaim k claims := by
  induction claims with
  | nil =>
    exfalso; exact List.not_mem_nil hmem
  | cons d ds ih =>
    simp only [removeClaim]
    split
    case isTrue heq =>
      cases hmem with
      | head => exact absurd heq hid
      | tail _ h => exact h
    case isFalse _ =>
      cases hmem with
      | head => exact List.Mem.head _
      | tail _ h => exact List.Mem.tail d (ih h)

/-- Removing claimant `k` leaves a nonempty profile whenever some distinct
claimant `j` is present. -/
lemma removeClaim_ne_nil {k j : ClaimantId} {claims : List (Claim F)}
    (hne : k ≠ j) (hmemj : InClaims j claims) :
    removeClaim k claims ≠ [] := by
  obtain ⟨c, hcmem, hcid⟩ := hmemj
  have : c ∈ removeClaim k claims :=
    removeClaim_preserves_other hcmem (fun heq => absurd (hcid ▸ heq) (Ne.symm hne))
  exact List.ne_nil_of_mem this

/-- Removing claimant `k` does not change the looked-up strength of any
different claimant `j`. -/
lemma lookupStrength_removeClaim_ne {k j : ClaimantId} {claims : List (Claim F)}
    (hne : k ≠ j) :
    lookupStrength j (removeClaim k claims) = lookupStrength j claims := by
  induction claims with
  | nil => rfl
  | cons c cs ih =>
    simp only [removeClaim]
    split
    case isTrue heq =>
      simp only [lookupStrength]
      have : ¬(c.id = j) := fun h => absurd (heq.symm.trans h) hne
      rw [if_neg this]
    case isFalse _ =>
      simp only [lookupStrength]
      split
      case isTrue _ => rfl
      case isFalse _ => exact ih

/-- Removing claimant `k` subtracts exactly their looked-up strength from the
total profile strength. -/
lemma totalStrength_removeClaim {k : ClaimantId} {claims : List (Claim F)} :
    totalStrength (removeClaim k claims) =
      totalStrength claims - lookupStrength k claims := by
  induction claims with
  | nil => simp [removeClaim, totalStrength, lookupStrength]
  | cons c cs ih =>
    simp only [removeClaim]
    split
    case isTrue heq =>
      simp only [totalStrength, lookupStrength, if_pos heq]; ring
    case isFalse hne =>
      simp only [totalStrength, lookupStrength, if_neg hne]; rw [ih]; ring

-- ═══════════════════════════════════════════════════════════════════
-- strengthenClaim lemmas
-- ═══════════════════════════════════════════════════════════════════

/-- After strengthening claimant `k`, looking up `k` returns the new strength. -/
lemma lookupStrength_strengthenClaim {k : ClaimantId} {claims : List (Claim F)}
    {s' : F} {hs' : 0 < s'}
    (hmem : InClaims k claims) (hdist : ClaimsDistinct claims) :
    lookupStrength k (strengthenClaim k s' hs' claims) = s' := by
  induction claims with
  | nil =>
    exfalso; obtain ⟨_, h, _⟩ := hmem; exact List.not_mem_nil h
  | cons c cs ih =>
    simp only [strengthenClaim]
    split
    case isTrue heq =>
      show lookupStrength k (⟨c.id, s', hs', c.metadata⟩ :: cs) = s'
      simp only [lookupStrength, if_pos heq]
    case isFalse hne =>
      show lookupStrength k (c :: strengthenClaim k s' hs' cs) = s'
      simp only [lookupStrength, if_neg hne]
      exact ih (InClaims_tail hmem hne) (ClaimsDistinct_tail hdist)

/-- Strengthening claimant `k` updates the total strength by replacing the old
looked-up contribution of `k` with the new strength `s'`. -/
lemma totalStrength_strengthenClaim {k : ClaimantId} {claims : List (Claim F)}
    {s' : F} {hs' : 0 < s'}
    (hmem : InClaims k claims) (hdist : ClaimsDistinct claims) :
    totalStrength (strengthenClaim k s' hs' claims) =
      totalStrength claims - lookupStrength k claims + s' := by
  induction claims with
  | nil =>
    exfalso; obtain ⟨_, h, _⟩ := hmem; exact List.not_mem_nil h
  | cons c cs ih =>
    simp only [strengthenClaim]
    split
    case isTrue heq =>
      simp only [totalStrength, lookupStrength, if_pos heq]; ring
    case isFalse hne =>
      simp only [totalStrength, lookupStrength, if_neg hne]
      rw [ih (InClaims_tail hmem hne) (ClaimsDistinct_tail hdist)]; ring

/-- Strengthening a claimant already present in the profile cannot produce the
empty list. -/
lemma strengthenClaim_nonempty {k : ClaimantId} {claims : List (Claim F)}
    {s' : F} {hs' : 0 < s'}
    (hmem : InClaims k claims) :
    strengthenClaim k s' hs' claims ≠ [] := by
  obtain ⟨c, hcmem, _⟩ := hmem
  match claims, hcmem with
  | _ :: _, _ =>
    simp only [strengthenClaim]
    split <;> exact List.cons_ne_nil _ _

-- ═══════════════════════════════════════════════════════════════════
-- Consistency proof
-- ═══════════════════════════════════════════════════════════════════

/-- The proportional rule satisfies **consistency** over any
    linearly ordered field. -/
lemma proportional_consistent : Consistency (F := F) proportionalRule := by
  intro claims estate k j hmemk hmemj hne hdist hpos
  simp only [proportionalRule]
  have hSpos : 0 < totalStrength claims :=
    totalStrength_pos (by obtain ⟨_, hm, _⟩ := hmemk; exact List.ne_nil_of_mem hm)
  have hSne : (totalStrength claims : F) ≠ 0 := ne_of_gt hSpos
  rw [if_neg hSne]
  have hts := totalStrength_removeClaim (k := k) (claims := claims)
  have hlook := lookupStrength_removeClaim_ne (claims := claims) hne
  rw [hts, hlook]
  have hS'pos : 0 < totalStrength claims - lookupStrength k claims := by
    rw [← hts]; exact totalStrength_pos (removeClaim_ne_nil hne hmemj)
  have hS'ne : totalStrength claims - lookupStrength k claims ≠ 0 :=
    ne_of_gt hS'pos
  rw [if_neg hS'ne, if_neg hSne]
  field_simp

-- ═══════════════════════════════════════════════════════════════════
-- Solidarity proof
-- ═══════════════════════════════════════════════════════════════════

/-- The proportional rule satisfies **solidarity** over any
    linearly ordered field. -/
lemma proportional_solidary : Solidarity (F := F) proportionalRule := by
  intro claims estate α hα j hmemj
  simp only [proportionalRule]
  have hSpos : 0 < totalStrength claims :=
    totalStrength_pos (by obtain ⟨_, hm, _⟩ := hmemj; exact List.ne_nil_of_mem hm)
  have hSne : (totalStrength claims : F) ≠ 0 := ne_of_gt hSpos
  rw [if_neg hSne, if_neg hSne]
  have hfrac_nn : 0 ≤ lookupStrength j claims / totalStrength claims :=
    div_nonneg (le_of_lt (lookupStrength_pos_of_mem hmemj)) (le_of_lt hSpos)
  constructor
  · intro hge
    apply mul_le_mul_of_nonneg_left _ hfrac_nn
    exact le_mul_of_one_le_left (le_of_lt estate.total_pos) hge
  · intro hle
    apply mul_le_mul_of_nonneg_left _ hfrac_nn
    exact mul_le_of_le_one_left (le_of_lt estate.total_pos) hle

-- ═══════════════════════════════════════════════════════════════════
-- Monotonicity proof
-- ═══════════════════════════════════════════════════════════════════

/-- With distinct claims, lookupStrength returns exactly the matching
    claim's strength. -/
private theorem lookupStrength_eq_of_mem {k : ClaimantId} {c : Claim F}
    {claims : List (Claim F)}
    (hmem : c ∈ claims) (hid : c.id = k) (hdist : ClaimsDistinct claims) :
    lookupStrength k claims = c.strength := by
  induction claims with
  | nil => exfalso; exact List.not_mem_nil hmem
  | cons d ds ih =>
    simp only [lookupStrength]
    split
    case isTrue heq =>
      cases hmem with
      | head => rfl
      | tail _ htail =>
        exfalso
        have hmapped : c.id ∈ (ds.map Claim.id) := by
          exact List.mem_map_of_mem (f := Claim.id) htail
        rw [hid] at hmapped
        have := ClaimsDistinct_head_not_in_tail hdist
        rw [heq] at this
        exact this hmapped
    case isFalse hne =>
      cases hmem with
      | head => exact absurd hid hne
      | tail _ htail => exact ih htail (ClaimsDistinct_tail hdist)

/-- The proportional rule satisfies **monotonicity** over any
    linearly ordered field. -/
lemma proportional_monotone : Monotonicity (F := F) proportionalRule := by
  intro claims estate k s' hs' hmemk hdist hstrength
  simp only [proportionalRule]
  have hSpos : 0 < totalStrength claims :=
    totalStrength_pos (by obtain ⟨_, hm, _⟩ := hmemk; exact List.ne_nil_of_mem hm)
  have hSne : (totalStrength claims : F) ≠ 0 := ne_of_gt hSpos
  rw [if_neg hSne]
  have hlook := lookupStrength_strengthenClaim hmemk hdist (s' := s') (hs' := hs')
  have hts := totalStrength_strengthenClaim hmemk hdist (s' := s') (hs' := hs')
  rw [hts, hlook]
  have hS'pos : 0 < totalStrength claims - lookupStrength k claims + s' := by
    rw [← hts]; exact totalStrength_pos (strengthenClaim_nonempty hmemk)
  have hS'ne : totalStrength claims - lookupStrength k claims + s' ≠ 0 :=
    ne_of_gt hS'pos
  rw [if_neg hS'ne]
  have hsk_le_s' : lookupStrength k claims ≤ s' := by
    obtain ⟨c, hcmem, hcid⟩ := hmemk
    rw [lookupStrength_eq_of_mem hcmem hcid hdist]
    exact hstrength c hcmem hcid
  have hsk_le_S : lookupStrength k claims ≤ totalStrength claims :=
    lookupStrength_le_totalStrength hmemk
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  rw [div_le_div_iff₀ hSpos hS'pos]
  set sk := lookupStrength k claims with hsk_def
  set S := totalStrength claims with hS_def
  set S' := S - sk + s' with hS'_def
  nlinarith [mul_nonneg (sub_nonneg.mpr hsk_le_s') (sub_nonneg.mpr hsk_le_S),
             estate.total_pos]

-- ═══════════════════════════════════════════════════════════════════
-- Admissibility
-- ═══════════════════════════════════════════════════════════════════

/-- The proportional rule is admissible over any linearly ordered field: it
satisfies all three allocation-rule diagnostics (consistency, solidarity,
monotonicity). All proofs are complete — zero sorry, zero axiom. -/
theorem proportional_admissible : Admissible (F := F) proportionalRule :=
  ⟨proportional_consistent, proportional_solidary, proportional_monotone⟩

end GenField

end Legitimacy
