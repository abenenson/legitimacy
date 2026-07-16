/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.N7Basin
import Legitimacy.Spectral.CrossScale.N9Archetypes
import Legitimacy.Spectral.Core.PerturbationBounds

/-!
# Finite Cross-Scale Spectral Universality Core

Shared order schemas for finite cross-scale spectral-gap certificates.
-/

set_option autoImplicit false

namespace Legitimacy

open Matrix BigOperators

/-- Shared finite certificate schema for uniform complete graphs. The only
possible eigenvalues are `0` and the complete-graph gap value; if the
second-smallest slot were zero, antitonicity forces the last slot to zero and
the trace sum becomes too small. -/
lemma uniformK_spectralGap_eq
    {n : Nat}
    (f : Fin n → ℝ) (gap last : Fin n) (gapValue total : ℝ)
    (hvals : ∀ i, f i = 0 ∨ f i = gapValue)
    (hsum : ∑ i : Fin n, f i = total)
    (hnonneg : ∀ i, 0 ≤ f i)
    (hantitone : ∀ {i j : Fin n}, i ≤ j → f j ≤ f i)
    (hgap_le_last : gap ≤ last)
    (hgapValue_nonneg : 0 ≤ gapValue)
    (hupper_sum_lt :
      (∑ i : Fin n, if i = gap ∨ i = last then 0 else gapValue) < total) :
    f gap = gapValue := by
  rcases hvals gap with hgap0 | hgap
  · have hlast_le_zero : f last ≤ 0 := by
      calc
        f last ≤ f gap := hantitone hgap_le_last
        _ = 0 := hgap0
    have hlast0 : f last = 0 :=
      le_antisymm hlast_le_zero (hnonneg last)
    have hterm_le :
        ∀ i : Fin n, f i ≤ if i = gap ∨ i = last then 0 else gapValue := by
      intro i
      by_cases higap : i = gap
      · simp [higap, hgap0]
      · by_cases hilast : i = last
        · simp [hilast, hlast0]
        · have hnot : ¬ (i = gap ∨ i = last) := by
            intro h
            exact h.elim higap hilast
          have hi := hvals i
          simp [hnot]
          rcases hi with hi0 | higapValue
          · nlinarith
          · exact le_of_eq higapValue
    have hsum_le :
        (∑ i : Fin n, f i) ≤
          ∑ i : Fin n, if i = gap ∨ i = last then 0 else gapValue :=
      Finset.sum_le_sum (fun i _ => hterm_le i)
    have hlt : (∑ i : Fin n, f i) < total :=
      lt_of_le_of_lt hsum_le hupper_sum_lt
    rw [hsum] at hlt
    exact (lt_irrefl total hlt).elim
  · exact hgap

/-- Shared finite certificate schema for bottleneck upper bounds. A constant
mode supplies a zero eigenvalue, so antitonicity and nonnegativity force the
last ordered eigenvalue to zero. The nonzero separator eigenvalue must then
occur before the last slot, bounding the spectral-gap slot by antitonicity. -/
lemma bottleneck_spectralGap_le
    {n : Nat}
    (f : Fin n → ℝ) (gap last : Fin n) (cert : ℝ)
    (hzero : ∃ i : Fin n, f i = 0)
    (hseparator : ∃ i : Fin n, f i = cert)
    (hnonneg : ∀ i, 0 ≤ f i)
    (hantitone : ∀ {i j : Fin n}, i ≤ j → f j ≤ f i)
    (hle_last : ∀ i : Fin n, i ≤ last)
    (hle_gap_of_ne_last : ∀ i : Fin n, i ≠ last → i ≤ gap)
    (hcert_ne_zero : cert ≠ 0) :
    f gap ≤ cert := by
  rcases hzero with ⟨i0, h0⟩
  rcases hseparator with ⟨iw, hw⟩
  have hlast : f last = 0 := by
    have hle := hantitone (hle_last i0)
    exact le_antisymm (by simpa [h0] using hle) (hnonneg last)
  have hiw_ne_last : iw ≠ last := by
    intro hiw
    rw [hiw, hlast] at hw
    exact hcert_ne_zero hw.symm
  calc
    f gap ≤ f iw := hantitone (hle_gap_of_ne_last iw hiw_ne_last)
    _ = cert := hw


end Legitimacy
