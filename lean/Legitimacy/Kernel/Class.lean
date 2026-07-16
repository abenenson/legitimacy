/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Data
import Legitimacy.Spectral.Core.SpectralWellConnected

/-!
# Legitimacy.Kernel.Class

Property-level axioms for the unified legitimacy kernel.

`LegitimacyKernelData` packages the operational interfaces and shared
substrate. `IsLegitimacyKernel` is the Prop-valued layer asserting that those
interfaces satisfy the five kernel axioms.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Structural adversarial-bound witness for one unbundled kernel datum.

The runtime kernel treats this as part of its strengthened corrigibility
obligation: callers must exhibit a finite nonnegative budget that uniformly
bounds the kernel's own action-capability surface. External stateful adversary
budgets remain separate theorem hypotheses in the safety stack. -/
def KernelAdversarialBounded {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : Prop :=
  ∃ budget : ℚ, 0 ≤ budget ∧
    ∀ a : D.actionSpace.Action,
      0 ≤ D.actionCapability a ∧ D.actionCapability a ≤ budget

/-- Convenience constructor for inert action-capability surfaces. -/
theorem kernelAdversarialBounded_zero
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (hzero : ∀ a : D.actionSpace.Action, D.actionCapability a = 0) :
    KernelAdversarialBounded D := by
  refine ⟨0, le_rfl, ?_⟩
  intro a
  rw [hzero a]
  exact ⟨le_rfl, le_rfl⟩

/-- Convenience constructor for constant nonnegative action-capability
surfaces. -/
theorem kernelAdversarialBounded_const
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (c : ℚ)
    (hc : 0 ≤ c)
    (hconst : ∀ a : D.actionSpace.Action, D.actionCapability a = c) :
    KernelAdversarialBounded D := by
  refine ⟨c, hc, ?_⟩
  intro a
  rw [hconst a]
  exact ⟨hc, le_rfl⟩

/-- Kernel-level corrigibility: the ordinary supervisory-algebra preservation
predicate together with the finite action-capability ceiling carried by the
kernel datum. -/
def KernelCorrigible {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : Prop :=
  Corrigible sys.state D.actionSpace D.algebra ∧
    KernelAdversarialBounded D

/-- Build kernel-level corrigibility for inert action-capability surfaces. -/
theorem kernelCorrigible_zero
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (hcorr : Corrigible sys.state D.actionSpace D.algebra)
    (hzero : ∀ a : D.actionSpace.Action, D.actionCapability a = 0) :
    KernelCorrigible D :=
  ⟨hcorr, kernelAdversarialBounded_zero D hzero⟩

/-- Build kernel-level corrigibility for constant nonnegative
action-capability surfaces. -/
theorem kernelCorrigible_const
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (hcorr : Corrigible sys.state D.actionSpace D.algebra)
    (c : ℚ) (hc : 0 ≤ c)
    (hconst : ∀ a : D.actionSpace.Action, D.actionCapability a = c) :
    KernelCorrigible D :=
  ⟨hcorr, kernelAdversarialBounded_const D c hc hconst⟩

/-- Prop-valued witnesses asserting that one unbundled kernel datum satisfies
the five kernel axioms on the shared `GovernedSystem` substrate. The
corrigibility predicate subsumes the kernel's own action-capability bound. -/
class IsLegitimacyKernel {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : Prop where
  /-- Axiom 1: graph decisions are resource-bounded certifiable. -/
  certifiable : Certifiable D.certification
  /-- Axiom 2: the observation interface preserves governance queries. -/
  observable : GovernanceObservable D.answer D.observeAnswer D.observe
  /-- Axiom 3: supervisory algebra is preserved, with bounded kernel actions. -/
  corrigible : KernelCorrigible D
  /-- Axiom 4: datum-indexed causal soundness of the kernel substrate. -/
  compositionalSafety : D.KernelCausalSoundness
  /-- Axiom 5: datum-indexed liveness of the kernel substrate. -/
  nonVacuous : D.KernelNonVacuous

theorem IsLegitimacyKernel.compositionalSafety_system
    {n : Nat} {sys : GovernedSystem n} {D : LegitimacyKernelData sys}
    (h : IsLegitimacyKernel D) :
    CausalSoundness sys.dag sys.governed :=
  by
    simpa [LegitimacyKernelData.KernelCausalSoundness] using
      h.compositionalSafety

theorem IsLegitimacyKernel.nonVacuous_system
    {n : Nat} {sys : GovernedSystem n} {D : LegitimacyKernelData sys}
    (h : IsLegitimacyKernel D) :
    NonVacuous sys.graph sys.trace :=
  h.nonVacuous.1

/-- Semantic bridge contract tying one kernel datum back to the diagnostic
and spectral layers over its shared governed system. This is separate from
the five runtime kernel axioms so the library can state, and refute, exactly
what the runtime kernel alone does or does not imply. -/
def KernelSemanticBridge {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : Prop :=
  AllLegitimacyAxioms sys.graph ∧
    SpectralCarrierRepresentsGraph sys.graph D.spectralGraph
      D.spectralSignal ∧
      SpectralWellConnected D.spectralGraph D.spectralSignal
        sys.graph.weightedSize_atLeastTwo

theorem KernelSemanticBridge.diagnostics
    {n : Nat} {sys : GovernedSystem n} {D : LegitimacyKernelData sys}
    (h : KernelSemanticBridge D) :
    AllLegitimacyAxioms sys.graph :=
  h.1

theorem KernelSemanticBridge.carrierRepresentsGraph
    {n : Nat} {sys : GovernedSystem n} {D : LegitimacyKernelData sys}
    (h : KernelSemanticBridge D) :
    SpectralCarrierRepresentsGraph sys.graph D.spectralGraph
      D.spectralSignal :=
  h.2.1

theorem KernelSemanticBridge.spectralWellConnected
    {n : Nat} {sys : GovernedSystem n} {D : LegitimacyKernelData sys}
    (h : KernelSemanticBridge D) :
    SpectralWellConnected D.spectralGraph D.spectralSignal
      sys.graph.weightedSize_atLeastTwo :=
  h.2.2

/-- Strengthened kernel target for semantic bridge theorems. It retains the
five runtime kernel axioms and adds the explicit diagnostic/spectral bridge
contract needed to connect the three layers as one semantic artifact. -/
class IsSemanticLegitimacyKernel {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : Prop where
  /-- The original five runtime kernel axioms. -/
  runtimeKernel : IsLegitimacyKernel D
  /-- The graph-diagnostic, carrier-grounding, and spectral well-connected
  semantic bridge. -/
  semanticBridge : KernelSemanticBridge D

/-- Canonical decomposition of the semantic kernel target into the runtime
kernel axioms and the explicit diagnostic/spectral bridge contract. -/
theorem isSemanticLegitimacyKernel_iff_runtime_and_bridge
    {n : Nat} {sys : GovernedSystem n} (D : LegitimacyKernelData sys) :
    IsSemanticLegitimacyKernel D ↔ IsLegitimacyKernel D ∧
      KernelSemanticBridge D := by
  constructor
  · intro h
    exact ⟨h.runtimeKernel, h.semanticBridge⟩
  · rintro ⟨hruntime, hbridge⟩
    exact { runtimeKernel := hruntime, semanticBridge := hbridge }

end Legitimacy
