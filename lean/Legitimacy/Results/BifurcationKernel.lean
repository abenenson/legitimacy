/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Results.DiagnosticAxiomIff
import Legitimacy.Kernel.Examples
import Legitimacy.Spectral.Dynamics.Bifurcation

/-!
# Legitimacy.Results.BifurcationKernel

Conditional kernel-side attachment for the spectral bifurcation theorem.

This file is intentionally separate from `Legitimacy.Spectral.Dynamics.Bifurcation`.
The current API does not yet identify graph-specific spectral regimes with
kernel diagnostics or legitimacy-factor-exposure coordinates. That bridge is
expected to arrive through the in-flight extreme-point witness work around
`Results/DiagnosticAxiomIff.lean`.

Until those bridge lemmas land, the corollary below keeps the kernel-side
exposure claim explicit as a hypothesis. This lets the spectral bifurcation and
the bundled five-axiom kernel witness coexist in one statement without
pretending that the current library has already proved the missing interface.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A bundled kernel-side exposure bridge, parameterized over system size so
future extreme-point or feasibility theorems can instantiate it directly. -/
abbrev KernelLFEBridge :=
  {m : Nat} → {sys : GovernedSystem m} → LegitimacyKernel sys → ℚ → Prop

/-- The concrete permit kernel satisfies all five bundled kernel axioms. -/
theorem permitKernel_satisfies_all_axioms :
    ∀ A : KernelAxiom, SatisfiesAxiom permitKernel A := by
  intro A
  cases A with
  | certifiable =>
      exact permitKernel.isKernel.certifiable
  | observable =>
      exact permitKernel.isKernel.observable
  | corrigible =>
      exact permitKernel.corrigible
  | compositional =>
      simpa [LegitimacyKernelData.KernelCausalSoundness] using
        permitKernel.isKernel.compositionalSafety
  | nonvacuous =>
      exact permitKernel.isKernel.nonVacuous.1

/-- Conditional kernel-side packaging of the spectral bifurcation.

The spectral half is unconditional and comes from
`bifurcation_iff_spectral`. The kernel half uses the concrete `permitKernel`
all-axiom witness together with an explicit bridge hypothesis
`KernelLFEBridge permitKernel δ`. This hypothesis is expected to be discharged
by the forthcoming `lfe_axis_realization_*` lemmas. -/
theorem kernel_bifurcation_corollary
    (KernelBridge : KernelLFEBridge)
    {n : Nat} [NeZero n]
    {G : GovGraph ℚ n} {s : Fin n → ℚ} {δ κ : ℚ}
    (hδ : 0 < δ)
    (hbelow : BelowBifurcationBoundary G s δ κ)
    (hbridge : KernelBridge permitKernel δ) :
    (G.capacity s δ ∧ 0 < G.cv s ∧ SpectralStableEquilibrium G s δ κ) ∧
      ∃ sys : GovernedSystem 1, ∃ K : LegitimacyKernel sys,
        (∀ A : KernelAxiom, SatisfiesAxiom K A) ∧ KernelBridge K δ := by
  refine ⟨(bifurcation_iff_spectral G s δ κ hδ).mp hbelow, ?_⟩
  exact ⟨permitSystem, permitKernel, permitKernel_satisfies_all_axioms, hbridge⟩

end Legitimacy
