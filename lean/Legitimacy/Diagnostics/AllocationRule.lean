/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Types
import Mathlib.Algebra.Order.Field.Basic

/-!
# Legitimacy.Diagnostics.AllocationRule — allocation-rule diagnostics over ordered fields

This module states three allocation-rule diagnostics (`Consistency`,
`Solidarity`, `Monotonicity`) and the composite `Admissible` predicate using
the field-parameterised types from `Legitimacy.Foundations.Types`.

The definitions are parameterised by `{F : Type*} [Field F] [LinearOrder F]
[IsStrictOrderedRing F]` so they apply to `ℚ`, `ℝ`, or any other ordered
field.  Downstream files that need concrete computation can instantiate at `ℚ`.

## Main definitions

- `Legitimacy.Consistency` — removing a claimant and reducing the estate by
  their share preserves every other claimant's allocation.
- `Legitimacy.Solidarity` — a resource-monotonicity-style diagnostic:
  scaling the estate up (down) moves all allocations weakly up (down).
- `Legitimacy.Monotonicity` — increasing a claimant's strength does not
  decrease their allocation.
- `Legitimacy.Admissible` — conjunction of all three diagnostics.
- The file is purely definitional: downstream concrete rules instantiate these
  axioms and discharge them with domain-specific proofs.

## References

* H. Peyton Young, *Equity: In Theory and Practice*, 1994, Appendix A.5
  for the claims-problem allocation-rule setting.
* William Thomson, reduced-problem consistency and resource-monotonicity
  treatments in the allocation-rule literature.
-/

namespace Legitimacy

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-! ## Diagnostic 1: Consistency

If we remove a claimant `k` and reduce the estate by their allocation,
every remaining claimant's allocation is unchanged. -/

/-- **Consistency**: removing any claimant and reducing the estate by
their share preserves every other claimant's allocation.

For any claims, estate, and distinct claimants `k ≠ j` both in `claims`:
let the reduced problem be `(removeClaim k claims, estate - rule(k))`.
Then `rule(reduced, j) = rule(original, j)`. -/
def Consistency (rule : AllocationRule F) : Prop :=
  ∀ (claims : List (Claim F)) (estate : Estate F)
    (k j : ClaimantId),
    InClaims k claims →
    InClaims j claims →
    k ≠ j →
    ClaimsDistinct claims →
    ∀ (hpos : 0 < estate.total - rule claims estate k),
    let reduced := removeClaim k claims
    let estate' : Estate F := ⟨estate.total - rule claims estate k, hpos⟩
    rule claims estate j = rule reduced estate' j

/-! ## Diagnostic 2: Solidarity

Within a priority class, a common shock to the estate moves all claimants
in the same direction. We state the single-class version: scaling the estate
up moves all allocations weakly up, and scaling down moves them weakly down. -/

/-- **Solidarity**: the resource-monotonicity-style diagnostic saying that
scaling the estate up moves all allocations weakly up, and scaling down moves
all allocations weakly down. -/
def Solidarity (rule : AllocationRule F) : Prop :=
  ∀ (claims : List (Claim F)) (estate : Estate F)
    (α : F) (hα : 0 < α)
    (j : ClaimantId),
    InClaims j claims →
    let estate' : Estate F := ⟨α * estate.total, mul_pos hα estate.total_pos⟩
    (1 ≤ α → rule claims estate j ≤ rule claims estate' j) ∧
    (α ≤ 1 → rule claims estate' j ≤ rule claims estate j)

/-! ## Diagnostic 3: Monotonicity

Strengthening a claimant's claim (all else equal) does not decrease
their allocation. -/

/-- **Monotonicity**: increasing a claimant's strength (all else equal)
does not decrease their allocation. -/
def Monotonicity (rule : AllocationRule F) : Prop :=
  ∀ (claims : List (Claim F)) (estate : Estate F)
    (k : ClaimantId) (s' : F) (hs' : 0 < s'),
    InClaims k claims →
    ClaimsDistinct claims →
    (∀ c ∈ claims, c.id = k → c.strength ≤ s') →
    let strengthened := strengthenClaim k s' hs' claims
    rule claims estate k ≤ rule strengthened estate k

/-- A rule is **admissible** iff it satisfies all three allocation-rule
diagnostics. -/
def Admissible (rule : AllocationRule F) : Prop :=
  Consistency rule ∧ Solidarity rule ∧ Monotonicity rule

end Legitimacy
