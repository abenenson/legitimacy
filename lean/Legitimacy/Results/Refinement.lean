/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Types
import Legitimacy.Diagnostics.AllocationRule
import Legitimacy.Results.Proportional

/-!
# Legitimacy.Results.Refinement

This module formalizes the meta-requirement of **ABSTRACTION SOUNDNESS** for
the Rust allocation layer.

## What is modeled

- The Rust `evaluate_rule` boundary from `src/lib.rs`, abstracted as dispatch on
  declarative rule kinds.
- The built-in proportional allocator from `src/rules.rs`, modeled with the same
  empty-claims guard used by Rust.
- A minimal certificate format recording that the Rust-side semantics emitted an
  allocation outcome for a claimant.

## What is assumed

- Parsing from typed rule-policy source text to a declarative rule kind is trusted here;
  this file models the post-parse semantic object.
- Custom rule kinds are left abstract via a parameter `customSemantics`; the
  refinement theorem therefore isolates the built-in proportional branch.
- Numeric behavior is modeled over an arbitrary linearly ordered field rather
  than Rust `f64`, so floating-point error is outside the scope of this file.

## Scope note

`src/policy/parser.rs` feeds `RuleSpec::Declarative`, whose allocation boundary
currently distinguishes the built-in `proportional` rule from open-ended custom
rule names. Threshold nodes belong to the governance-graph DSL, not to
`evaluate_rule`, so they are not modeled in this allocation refinement layer.
-/

set_option autoImplicit false

namespace Legitimacy

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Declarative rule specifications accepted by the Rust allocation dispatcher.

This mirrors the allocation-relevant part of Rust's `DeclarativeRuleKind`:
`proportional` is built in, while all other names are treated as custom rules
whose semantics are supplied externally. -/
inductive RustRuleSpec where
  /-- The built-in proportional rule. -/
  | proportional
  /-- An open-ended custom rule identified by name. -/
  | custom (name : String)
  deriving Repr, DecidableEq

/-- Lean model of Rust's built-in proportional allocator.

The Rust implementation returns an empty allocation map on `[]`. At the
pointwise allocation level this is modeled by returning `0` when the claims list
is empty; otherwise the allocator computes the same algebraic share formula as
the mathematical proportional rule. -/
def rustProportionalSemantics : AllocationRule F := fun claims estate k =>
  if claims = [] then 0
  else lookupStrength k claims / totalStrength claims * estate.total

/-- Lean-side mathematical proportional semantics. -/
def leanProportionalSemantics : AllocationRule F := proportionalRule

/-- Mathematical semantics used on the Lean side of the refinement relation. -/
def LeanSemantics (customSemantics : String → AllocationRule F) :
    RustRuleSpec → AllocationRule F
  | .proportional => leanProportionalSemantics
  | .custom name => customSemantics name

/-- Rust-side semantics modeled in Lean at the `evaluate_rule` abstraction
boundary. -/
def RustSemantics (customSemantics : String → AllocationRule F) :
    RustRuleSpec → AllocationRule F
  | .proportional => rustProportionalSemantics
  | .custom name => customSemantics name

/-- `RefinementRelation rust lean` means the Rust-side semantics agrees pointwise
with the Lean-side specification for every rule kind and every well-typed input.

There is no separate validity predicate: positivity of claim strengths and estate
total is already encoded in `Claim` and `Estate`. -/
def RefinementRelation (rust lean : RustRuleSpec → AllocationRule F) : Prop :=
  ∀ spec claims estate k, rust spec claims estate k = lean spec claims estate k

/-- A certificate that records the claimant outcome emitted by the Rust-side
allocation semantics. -/
structure AllocationCertificate where
  /-- The declarative rule that was evaluated. -/
  rule : RustRuleSpec
  /-- The claims evaluated by the rule. -/
  claims : List (Claim F)
  /-- The estate supplied to the rule. -/
  estate : Estate F
  /-- The claimant whose outcome is certified. -/
  claimant : ClaimantId
  /-- The outcome emitted for that claimant. -/
  outcome : F

/-- The certificate matches the Rust-side semantics exactly. -/
def EmitsCertificate (rust : RustRuleSpec → AllocationRule F)
    (cert : AllocationCertificate (F := F)) : Prop :=
  cert.outcome = rust cert.rule cert.claims cert.estate cert.claimant

/-- Every emitted Rust certificate corresponds to the same Lean-side outcome. -/
def CertificateCorrespondence (rust lean : RustRuleSpec → AllocationRule F) : Prop :=
  ∀ cert : AllocationCertificate (F := F),
    EmitsCertificate rust cert →
      cert.outcome = lean cert.rule cert.claims cert.estate cert.claimant

/-- The Rust proportional allocator refines the mathematical proportional rule
from `Legitimacy.Proportional`. The only mismatch is Rust's explicit empty-list
branch, which is extensionally equal to the mathematical rule because positive
claims imply `totalStrength = 0` exactly in the empty case. -/
lemma proportional_refinement :
    ∀ claims estate k,
      rustProportionalSemantics (F := F) claims estate k =
        leanProportionalSemantics (F := F) claims estate k := by
  intro claims estate k
  by_cases hnil : claims = []
  · subst hnil
    simp [rustProportionalSemantics, leanProportionalSemantics, proportionalRule,
      totalStrength]
  · have hpos : 0 < totalStrength claims := totalStrength_pos hnil
    have hne : totalStrength claims ≠ 0 := ne_of_gt hpos
    simp [rustProportionalSemantics, leanProportionalSemantics, hnil,
      proportionalRule, hne]

/-- The modeled Rust semantics refines the Lean semantics for every declarative
rule kind, assuming identical semantics for custom rules. The substantive work
is the proportional branch proved in `proportional_refinement`. -/
theorem modeledRustSemantics_refines_leanSemantics (customSemantics : String → AllocationRule F) :
    RefinementRelation (RustSemantics customSemantics) (LeanSemantics customSemantics) := by
  intro spec claims estate k
  cases spec with
  | proportional =>
      exact proportional_refinement (claims := claims) (estate := estate) (k := k)
  | custom name =>
      rfl

/-- Deprecated compatibility alias: the corrected name is
`modeledRustSemantics_refines_leanSemantics`, because the left side is the Lean
model of the Rust semantics. -/
theorem rust_refines_lean (customSemantics : String → AllocationRule F) :
    RefinementRelation (RustSemantics customSemantics) (LeanSemantics customSemantics) :=
  modeledRustSemantics_refines_leanSemantics customSemantics

/-- If the Rust semantics emits a certificate, refinement guarantees that the
certified outcome is exactly the one computed by the Lean semantics. -/
theorem certificate_soundness
    {rust lean : RustRuleSpec → AllocationRule F}
    (href : RefinementRelation rust lean) :
    CertificateCorrespondence rust lean := by
  intro cert hcert
  rw [EmitsCertificate] at hcert
  calc
    cert.outcome = rust cert.rule cert.claims cert.estate cert.claimant := hcert
    _ = lean cert.rule cert.claims cert.estate cert.claimant :=
      href cert.rule cert.claims cert.estate cert.claimant

/-- Pointwise refinement transports allocation-rule consistency from the Lean
semantics to the Rust semantics for a fixed rule specification. -/
lemma refinement_preserves_consistency
    {rust lean : RustRuleSpec → AllocationRule F}
    {spec : RustRuleSpec}
    (href : RefinementRelation rust lean)
    (hlean : Consistency (lean spec)) :
    Consistency (rust spec) := by
  intro claims estate k j hmemk hmemj hkj hdistinct hpos
  change
    rust spec claims estate j =
      rust spec (removeClaim k claims)
        ⟨estate.total - rust spec claims estate k, hpos⟩ j
  have hk : rust spec claims estate k = lean spec claims estate k :=
    href spec claims estate k
  have hj : rust spec claims estate j = lean spec claims estate j :=
    href spec claims estate j
  have hpos' : 0 < estate.total - lean spec claims estate k := by
    simpa [hk] using hpos
  have hcore :=
    hlean claims estate k j hmemk hmemj hkj hdistinct hpos'
  have hreduced :
      rust spec (removeClaim k claims)
          ⟨estate.total - lean spec claims estate k, hpos'⟩ j =
        lean spec (removeClaim k claims)
          ⟨estate.total - lean spec claims estate k, hpos'⟩ j :=
    href spec (removeClaim k claims)
      ⟨estate.total - lean spec claims estate k, hpos'⟩ j
  have hestate :
      (⟨estate.total - lean spec claims estate k, hpos'⟩ : Estate F) =
        ⟨estate.total - rust spec claims estate k, hpos⟩ := by
    cases estate
    simp [hk]
  calc
    rust spec claims estate j = lean spec claims estate j := hj
    _ = lean spec (removeClaim k claims)
          ⟨estate.total - lean spec claims estate k, hpos'⟩ j := hcore
    _ = rust spec (removeClaim k claims)
          ⟨estate.total - lean spec claims estate k, hpos'⟩ j := by
          symm
          exact hreduced
    _ = rust spec (removeClaim k claims)
          ⟨estate.total - rust spec claims estate k, hpos⟩ j := by
          rw [hestate]

/-- Pointwise refinement transports solidarity from the Lean semantics to the
Rust semantics for a fixed rule specification. -/
lemma refinement_preserves_solidarity
    {rust lean : RustRuleSpec → AllocationRule F}
    {spec : RustRuleSpec}
    (href : RefinementRelation rust lean)
    (hlean : Solidarity (lean spec)) :
    Solidarity (rust spec) := by
  intro claims estate α hα j hmemj
  let estate' : Estate F := ⟨α * estate.total, mul_pos hα estate.total_pos⟩
  have hcore := hlean claims estate α hα j hmemj
  have hbase : rust spec claims estate j = lean spec claims estate j :=
    href spec claims estate j
  have hscaled : rust spec claims estate' j = lean spec claims estate' j :=
    href spec claims estate' j
  constructor
  · intro hα_ge
    calc
      rust spec claims estate j = lean spec claims estate j := hbase
      _ ≤ lean spec claims estate' j := hcore.1 hα_ge
      _ = rust spec claims estate' j := by
          symm
          exact hscaled
  · intro hα_le
    calc
      rust spec claims estate' j = lean spec claims estate' j := hscaled
      _ ≤ lean spec claims estate j := hcore.2 hα_le
      _ = rust spec claims estate j := by
          symm
          exact hbase

/-- Pointwise refinement transports monotonicity from the Lean semantics to the
Rust semantics for a fixed rule specification. -/
lemma refinement_preserves_monotonicity
    {rust lean : RustRuleSpec → AllocationRule F}
    {spec : RustRuleSpec}
    (href : RefinementRelation rust lean)
    (hlean : Monotonicity (lean spec)) :
    Monotonicity (rust spec) := by
  intro claims estate k s' hs' hmemk hdistinct hstrength
  let strengthened := strengthenClaim k s' hs' claims
  have hcore := hlean claims estate k s' hs' hmemk hdistinct hstrength
  have hbase : rust spec claims estate k = lean spec claims estate k :=
    href spec claims estate k
  have hstrong : rust spec strengthened estate k = lean spec strengthened estate k :=
    href spec strengthened estate k
  calc
    rust spec claims estate k = lean spec claims estate k := hbase
    _ ≤ lean spec strengthened estate k := hcore
    _ = rust spec strengthened estate k := by
        symm
        exact hstrong

/-- Pointwise refinement transports admissibility from the Lean semantics to the
Rust semantics for a fixed rule specification. -/
theorem refinement_preserves_admissibility
    {rust lean : RustRuleSpec → AllocationRule F}
    {spec : RustRuleSpec}
    (href : RefinementRelation rust lean)
    (hlean : Admissible (lean spec)) :
    Admissible (rust spec) := by
  rcases hlean with ⟨hcons, hsol, hmono⟩
  exact ⟨refinement_preserves_consistency href hcons,
    refinement_preserves_solidarity href hsol,
    refinement_preserves_monotonicity href hmono⟩

end Legitimacy
