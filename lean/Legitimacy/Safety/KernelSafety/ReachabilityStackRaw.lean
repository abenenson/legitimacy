/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.Trajectory

/-!
# Legitimacy.Safety.KernelSafety.ReachabilityStackRaw

Raw-transition substrate for kernel reachability.

This module owns the reachable-state safety statement and induction theorem
over raw kernel-governed trajectories. The headline dispatch theorem remains in
`ReachabilityStack`.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-! ## Raw reachable-state safety theorem signature -/

/-- A raw governed trajectory has taken a classifier-surfaced sacrifice route
when the classifier proof emits a concrete certificate at one of its
zero-based transition indices. -/
def RawKernelTrajectoryHasSacrifice
    {n : Nat} {sys : GovernedSystem n}
    {D₀ D : LegitimacyKernelData sys}
    (h_traj : RawKernelGovernedTrajectory sys D₀ D) : Prop :=
  ∃ index : Nat,
    RawKernelGovernedTrajectory.HasClassifiedSacrificeStepAt h_traj index

/-- Target conclusion for raw reachable-state safety: the reached datum still
satisfies the kernel invariant, or classifier replay exposes a monitored
sacrifice certificate at a concrete transition index. -/
def RawReachableStateSafetyConclusion
    {n : Nat} {sys : GovernedSystem n}
    {_D₀ D : LegitimacyKernelData sys}
    (h_traj : RawKernelGovernedTrajectory sys _D₀ D) : Prop :=
  KernelInvariant D ∨ RawKernelTrajectoryHasSacrifice h_traj

/-- External classifier supplied for every raw step in a raw schedule. -/
def RawKernelStepClassifier
    {n : Nat} {sys : GovernedSystem n} : Prop :=
  ∀ {D D' : LegitimacyKernelData sys}
    (step : RawKernelStep D D'),
    RawKernelStep.MonitorExtractorHypotheses step

/-- Raw reachable-state theorem shape, packaged as a proposition for callers
that need to pass the safety statement as data. -/
def RawReachableStateSafetyStatement : Prop :=
  ∀ {n : Nat} {sys : GovernedSystem n}
    (D₀ D : LegitimacyKernelData sys),
    (h_traj : RawKernelGovernedTrajectory sys D₀ D) →
      @RawKernelStepClassifier n sys →
        KernelInvariant D₀ →
          RawReachableStateSafetyConclusion h_traj

/-- Every raw kernel-governed reachable state either preserves the semantic
kernel invariant, or classifier replay exposes a monitored sacrifice
certificate at a concrete transition index. The raw trajectory itself carries
no preservation or sacrifice proof; each transition is classified during this
induction by `classify_raw_step`. -/
theorem raw_reachable_state_safety : RawReachableStateSafetyStatement := by
  intro n sys D₀ D h hclassifier hinit
  induction h with
  | refl D =>
      exact Or.inl hinit
  | step rawStep tail ih =>
      rcases classify_raw_step rawStep hinit (hclassifier rawStep) with
        hboundary | hsurfaced
      · rcases ih hboundary with
          htailInvariant | ⟨index, hsacrifice⟩
        · exact Or.inl htailInvariant
        · exact Or.inr
            ⟨index + 1,
              RawKernelGovernedTrajectory.HasClassifiedSacrificeStepAt.tail
                rawStep tail hsacrifice⟩
      · rcases hsurfaced with ⟨cert, _hemitted, _hslot⟩
        exact Or.inr
          ⟨0,
            RawKernelGovernedTrajectory.HasClassifiedSacrificeStepAt.here
              rawStep cert tail⟩

/-- Paper-grade headline theorem over raw schedules: every state reachable by a
raw kernel-governed trajectory from an initial kernel invariant is either still
a semantic legitimacy kernel or exposes a concrete indexed monitored sacrifice
certificate derived by the raw-step classifier. -/
theorem raw_kernelReachabilitySafety : RawReachableStateSafetyStatement :=
  raw_reachable_state_safety

end Safety

end Legitimacy
