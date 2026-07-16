/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Diagnostics.AllocationRule

/-!
# Legitimacy.Diagnostics.FullConsistency — Young full sub-coalition consistency

This module states the full Young reduced-problem consistency axiom over every
nonempty proper removed coalition.  The existing `Consistency` predicate in
`AllocationRule.lean` is the single-removal form; this file names the canonical
public diagnostic used by theorem-backed Rust parity.
-/

set_option autoImplicit false

namespace Legitimacy

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Claimant IDs appearing in a claim profile, preserving profile order. -/
def claimants (claims : List (Claim F)) : List ClaimantId :=
  claims.map Claim.id

/-- List-subset relation specialized to claimant-id lists. -/
def ClaimantIdsSubset (xs ys : List ClaimantId) : Prop :=
  ∀ id, id ∈ xs → id ∈ ys

/-- Proper claimant-id subset: removed IDs are duplicate-free, every removed ID
appears in the profile, and at least one profile claimant survives. -/
def ClaimantIdsProperSubset (xs ys : List ClaimantId) : Prop :=
  xs.Nodup ∧ ClaimantIdsSubset xs ys ∧ ∃ id, id ∈ ys ∧ id ∉ xs

/-- Remove every claim whose claimant ID occurs in `removed`. -/
def eraseManyClaims (removed : List ClaimantId) : List (Claim F) → List (Claim F)
  | [] => []
  | c :: cs =>
    if c.id ∈ removed then
      eraseManyClaims removed cs
    else
      c :: eraseManyClaims removed cs

/-- Allocation mass assigned by `rule` to the removed coalition in the original
problem. This raw fold sums IDs as supplied; `YoungFullConsistencyOn` admits
only duplicate-free removed coalitions through `ClaimantIdsProperSubset`. -/
def removedAllocationSum
    (rule : AllocationRule F)
    (claims : List (Claim F))
    (estate : Estate F)
    (removed : List ClaimantId) : F :=
  removed.foldl (fun acc claimant => acc + rule claims estate claimant) 0

/-- Full Young consistency on one concrete claims problem. -/
def YoungFullConsistencyOn
    (rule : AllocationRule F)
    (claims : List (Claim F))
    (estate : Estate F) : Prop :=
  ClaimsDistinct claims →
  ∀ removed : List ClaimantId,
    removed ≠ [] →
    ClaimantIdsProperSubset removed (claimants claims) →
    ∀ hpos : 0 < estate.total - removedAllocationSum rule claims estate removed,
      let original := rule claims estate
      let reducedClaims := eraseManyClaims removed claims
      let reducedEstate : Estate F :=
        ⟨estate.total - removedAllocationSum rule claims estate removed, hpos⟩
      ∀ survivor : ClaimantId,
        InClaims survivor reducedClaims →
          rule reducedClaims reducedEstate survivor = original survivor

/-- Full Young consistency over all claims problems. -/
def YoungFullConsistency (rule : AllocationRule F) : Prop :=
  ∀ claims estate, YoungFullConsistencyOn rule claims estate

/-- Lean mirror of the Rust full-consistency verdict surface. -/
inductive FullConsistencyVerdict where
  | admissible
  | rejected
  deriving Repr, DecidableEq

/-- Canonical audit artifact for the theorem-backed checker. The proof field is
the Lean contract Rust parity fixtures are required to preserve: an admissible
verdict is equivalent to the full Young sub-coalition axiom on this finite
claims problem. -/
structure FullConsistencyAuditArtifact
    (rule : AllocationRule F)
    (claims : List (Claim F))
    (estate : Estate F) where
  verdict : FullConsistencyVerdict
  verdict_iff_young_full :
    verdict = .admissible ↔ YoungFullConsistencyOn rule claims estate

/-- Executable canonical checker specification. The Rust rational checker is
validated against this full axiom, not against the historical singles+pairs
approximation. -/
noncomputable def runFullConsistencyChecker
    (rule : AllocationRule F)
    (claims : List (Claim F))
    (estate : Estate F) :
    FullConsistencyAuditArtifact rule claims estate := by
  classical
  by_cases h : YoungFullConsistencyOn rule claims estate
  · exact {
      verdict := .admissible
      verdict_iff_young_full := by
        constructor
        · intro _; exact h
        · intro _; rfl
    }
  · exact {
      verdict := .rejected
      verdict_iff_young_full := by
        constructor
        · intro hv
          cases hv
        · intro hyoung
          exact False.elim (h hyoung)
    }

/-- Lean executable checker contract for full Young consistency.

This proves only that the Lean-side `runFullConsistencyChecker` artifact returns
an admissible verdict iff the Lean full Young consistency axiom holds for the
same concrete problem. The checker is noncomputable and implemented by
classical case analysis over the axiom; this theorem is not a proof about Rust
execution. Rust parity is maintained separately by fixture lanes that compare
the Rust checker surface against this Lean contract. -/
lemma lean_full_consistency_executable_iff_axiom
    {rule : AllocationRule F}
    {claims : List (Claim F)}
    {estate : Estate F}
    (artifact : FullConsistencyAuditArtifact rule claims estate)
    (hcanonical : artifact = runFullConsistencyChecker rule claims estate) :
    artifact.verdict = .admissible ↔
      YoungFullConsistencyOn rule claims estate := by
  subst hcanonical
  exact (runFullConsistencyChecker rule claims estate).verdict_iff_young_full

end Legitimacy
