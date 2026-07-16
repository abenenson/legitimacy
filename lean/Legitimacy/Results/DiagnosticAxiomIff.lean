/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Unified
import Legitimacy.Results.MultiPrincipal
import Legitimacy.Protocol.State

/-!
# Legitimacy.Results.DiagnosticAxiomIff

Foundational definitions for relating the unified kernel axioms to diagnostic
coordinates.

This module is deliberately additive. It introduces:

* `SatisfiesAxiom`, a uniform accessor from `LegitimacyKernel` to the existing
  five axiom witnesses tracked by `KernelAxiom`
* `LegitimacyFactorExposure.normalized`, the `[0,1]^5` projection of the Rust-
  parity factor-exposure record
* `LegitimacyFactorExposure.isNormalized`, the boundedness side condition used
  by later feasible-region theorems
-/

set_option autoImplicit false

namespace Legitimacy

/-- Unified accessor exposing which of the five kernel axioms a bundled kernel
currently satisfies. This reuses the existing `KernelAxiom` enum from the
multi-principal development rather than introducing a parallel type. -/
def SatisfiesAxiom {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) : KernelAxiom → Prop
  | .certifiable => Certifiable K.certification
  | .observable => GovernanceObservable K.answer K.observeAnswer K.observe
  | .corrigible => Corrigible sys.state K.actionSpace K.algebra
  | .compositional => CausalSoundness sys.dag sys.governed
  | .nonvacuous => NonVacuous sys.graph sys.trace

@[simp] lemma satisfiesAxiom_certifiable {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    SatisfiesAxiom K .certifiable ↔ Certifiable K.certification := by
  rfl

@[simp] lemma satisfiesAxiom_observable {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    SatisfiesAxiom K .observable ↔
      GovernanceObservable K.answer K.observeAnswer K.observe := by
  rfl

@[simp] lemma satisfiesAxiom_corrigible {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    SatisfiesAxiom K .corrigible ↔
      Corrigible sys.state K.actionSpace K.algebra := by
  rfl

@[simp] lemma satisfiesAxiom_compositional {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    SatisfiesAxiom K .compositional ↔ CausalSoundness sys.dag sys.governed := by
  rfl

@[simp] lemma satisfiesAxiom_nonvacuous {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    SatisfiesAxiom K .nonvacuous ↔ NonVacuous sys.graph sys.trace := by
  rfl

/-- The Rust-parity factor exposure record viewed as a normalized point in
`[0,1]^5`, ordered as consistency, solidarity, monotonicity,
strategyproofness, nonvacuity. -/
def LegitimacyFactorExposure.normalized
    (e : LegitimacyFactorExposure) : Fin 5 → ℝ := fun i =>
  match i.1 with
  | 0 => e.cv
  | 1 => e.sv
  | 2 => e.mv
  | 3 => e.spv
  | _ => e.nonvacuity

/-- Side condition asserting that every factor-exposure coordinate lies in the
unit interval. -/
def LegitimacyFactorExposure.isNormalized
    (e : LegitimacyFactorExposure) : Prop :=
  ∀ i : Fin 5, 0 ≤ e.normalized i ∧ e.normalized i ≤ 1

@[simp] lemma LegitimacyFactorExposure.normalized_zero
    (e : LegitimacyFactorExposure) :
    e.normalized ⟨0, by omega⟩ = e.cv := by
  rfl

@[simp] lemma LegitimacyFactorExposure.normalized_one
    (e : LegitimacyFactorExposure) :
    e.normalized ⟨1, by omega⟩ = e.sv := by
  rfl

@[simp] lemma LegitimacyFactorExposure.normalized_two
    (e : LegitimacyFactorExposure) :
    e.normalized ⟨2, by omega⟩ = e.mv := by
  rfl

@[simp] lemma LegitimacyFactorExposure.normalized_three
    (e : LegitimacyFactorExposure) :
    e.normalized ⟨3, by omega⟩ = e.spv := by
  rfl

@[simp] lemma LegitimacyFactorExposure.normalized_four
    (e : LegitimacyFactorExposure) :
    e.normalized ⟨4, by omega⟩ = e.nonvacuity := by
  rfl

/-- The normalized factor-exposure region is exactly the unit hypercube in the
fixed Rust-parity coordinate order. -/
theorem lfe_feasible_region_characterization
    (e : LegitimacyFactorExposure) :
    e.isNormalized ↔
      0 ≤ e.cv ∧ e.cv ≤ 1 ∧
      0 ≤ e.sv ∧ e.sv ≤ 1 ∧
      0 ≤ e.mv ∧ e.mv ≤ 1 ∧
      0 ≤ e.spv ∧ e.spv ≤ 1 ∧
      0 ≤ e.nonvacuity ∧ e.nonvacuity ≤ 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h ⟨0, by omega⟩).1
    · exact (h ⟨0, by omega⟩).2
    · exact (h ⟨1, by omega⟩).1
    · exact (h ⟨1, by omega⟩).2
    · exact (h ⟨2, by omega⟩).1
    · exact (h ⟨2, by omega⟩).2
    · exact (h ⟨3, by omega⟩).1
    · exact (h ⟨3, by omega⟩).2
    · exact (h ⟨4, by omega⟩).1
    · exact (h ⟨4, by omega⟩).2
  · rintro ⟨hcv0, hcv1, hsv0, hsv1, hmv0, hmv1, hspv0, hspv1, hnv0, hnv1⟩
    intro i
    fin_cases i
    · simpa using And.intro hcv0 hcv1
    · simpa using And.intro hsv0 hsv1
    · simpa using And.intro hmv0 hmv1
    · simpa using And.intro hspv0 hspv1
    · simpa using And.intro hnv0 hnv1

end Legitimacy
