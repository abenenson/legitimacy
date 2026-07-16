/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.Sacrifice

/-!
# Legitimacy.Safety.KernelSafety.Trajectory

Finite execution structure for kernel-relative safety.

This module owns kernel-governed trajectories and the invariant-only fragment.
It depends on monitored sacrifice certificates but does not prove reachable
state safety; that theorem belongs to the reachability stack layer.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-- A finite raw kernel trajectory. Each transition is just a raw kernel step;
the trajectory does not store invariant-preservation witnesses or monitored
sacrifice certificates. -/
inductive RawKernelGovernedTrajectory {n : Nat} (sys : GovernedSystem n) :
    LegitimacyKernelData sys → LegitimacyKernelData sys → Type 2 where
  | refl (D : LegitimacyKernelData sys) :
      RawKernelGovernedTrajectory sys D D
  | step
      {D D' D'' : LegitimacyKernelData sys}
      (rawStep : RawKernelStep D D')
      (tail : RawKernelGovernedTrajectory sys D' D'') :
      RawKernelGovernedTrajectory sys D D''

namespace RawKernelGovernedTrajectory

/-- A one-step raw kernel trajectory. -/
def singleStep
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : RawKernelStep D D') :
    RawKernelGovernedTrajectory sys D D' :=
  RawKernelGovernedTrajectory.step step
    (RawKernelGovernedTrajectory.refl D')

/-- A classifier-derived sacrifice certificate occurs at the given zero-based
transition index in this raw trajectory. The raw trajectory does not store the
certificate; this indexed witness is produced by a classifier proof over the
raw schedule. -/
inductive HasClassifiedSacrificeStepAt
    {n : Nat} {sys : GovernedSystem n} :
    {D D' : LegitimacyKernelData sys} →
      RawKernelGovernedTrajectory sys D D' → Nat → Prop where
  | here
      {D D' D'' : LegitimacyKernelData sys}
      (step : RawKernelStep D D')
      (cert : MonitoredSacrificeCertificate D D')
      (tail : RawKernelGovernedTrajectory sys D' D'') :
      HasClassifiedSacrificeStepAt
        (RawKernelGovernedTrajectory.step step tail) 0
  | tail
      {D D' D'' : LegitimacyKernelData sys}
      (step : RawKernelStep D D')
      (tail : RawKernelGovernedTrajectory sys D' D'')
      {index : Nat} :
      HasClassifiedSacrificeStepAt tail index →
        HasClassifiedSacrificeStepAt
          (RawKernelGovernedTrajectory.step step tail)
          (index + 1)

end RawKernelGovernedTrajectory

/-- A finite trajectory governed by kernel safety. Each nontrivial transition
is either an invariant-preserving kernel step or an explicitly monitored
sacrifice step. -/
inductive KernelGovernedTrajectory {n : Nat} (sys : GovernedSystem n) :
    LegitimacyKernelData sys → LegitimacyKernelData sys → Type 2 where
  | refl (D : LegitimacyKernelData sys) :
      KernelGovernedTrajectory sys D D
  | invariant_step
      {D D' D'' : LegitimacyKernelData sys}
      (step : KernelStep D D')
      (source_invariant : KernelInvariant D)
      (target_invariant : KernelInvariant D')
      (tail : KernelGovernedTrajectory sys D' D'') :
      KernelGovernedTrajectory sys D D''
  | sacrifice_step
      {D D' D'' : LegitimacyKernelData sys}
      (cert : MonitoredSacrificeCertificate D D')
      (tail : KernelGovernedTrajectory sys D' D'') :
      KernelGovernedTrajectory sys D D''

namespace KernelGovernedTrajectory

/-- A concrete sacrifice certificate occurs at the given zero-based transition
index in this trajectory. Invariant steps advance the index; a head sacrifice
is witnessed at index zero. -/
inductive HasSacrificeStepAt
    {n : Nat} {sys : GovernedSystem n} :
    {D D' : LegitimacyKernelData sys} →
      KernelGovernedTrajectory sys D D' → Nat → Prop where
  | here
      {D D' D'' : LegitimacyKernelData sys}
      (cert : MonitoredSacrificeCertificate D D')
      (tail : KernelGovernedTrajectory sys D' D'') :
      HasSacrificeStepAt
        (KernelGovernedTrajectory.sacrifice_step cert tail) 0
  | invariant_tail
      {D D' D'' : LegitimacyKernelData sys}
      (step : KernelStep D D')
      (source_invariant : KernelInvariant D)
      (target_invariant : KernelInvariant D')
      (tail : KernelGovernedTrajectory sys D' D'')
      {index : Nat} :
      HasSacrificeStepAt tail index →
        HasSacrificeStepAt
          (KernelGovernedTrajectory.invariant_step step source_invariant
            target_invariant tail)
          (index + 1)
  | sacrifice_tail
      {D D' D'' : LegitimacyKernelData sys}
      (cert : MonitoredSacrificeCertificate D D')
      (tail : KernelGovernedTrajectory sys D' D'')
      {index : Nat} :
      HasSacrificeStepAt tail index →
        HasSacrificeStepAt
          (KernelGovernedTrajectory.sacrifice_step cert tail)
          (index + 1)

/-- A one-step invariant-preserving trajectory. -/
def singleInvariantStep
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : KernelStep D D')
    (hD : KernelInvariant D) :
    KernelGovernedTrajectory sys D D' :=
  KernelGovernedTrajectory.invariant_step step hD
    (kernelStep_preserves_invariant step hD)
    (KernelGovernedTrajectory.refl D')

/-- A one-step monitored sacrifice trajectory. -/
def singleSacrificeStep
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (cert : MonitoredSacrificeCertificate D D') :
    KernelGovernedTrajectory sys D D' :=
  KernelGovernedTrajectory.sacrifice_step cert
    (KernelGovernedTrajectory.refl D')

end KernelGovernedTrajectory

/-- A finite kernel-governed trajectory containing only invariant-preserving
kernel steps. This is the sacrifice-free fragment of
`KernelGovernedTrajectory`. -/
inductive KernelGovernedTrajectoryInvariantOnly
    {n : Nat} (sys : GovernedSystem n) :
    LegitimacyKernelData sys → LegitimacyKernelData sys → Type 2 where
  | refl (D : LegitimacyKernelData sys) :
      KernelGovernedTrajectoryInvariantOnly sys D D
  | invariant_step
      {D D' D'' : LegitimacyKernelData sys}
      (step : KernelStep D D')
      (source_invariant : KernelInvariant D)
      (target_invariant : KernelInvariant D')
      (tail : KernelGovernedTrajectoryInvariantOnly sys D' D'') :
      KernelGovernedTrajectoryInvariantOnly sys D D''

namespace KernelGovernedTrajectoryInvariantOnly

/-- A one-step invariant-only trajectory. -/
def singleInvariantStep
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : KernelStep D D')
    (hD : KernelInvariant D) :
    KernelGovernedTrajectoryInvariantOnly sys D D' :=
  KernelGovernedTrajectoryInvariantOnly.invariant_step step hD
    (kernelStep_preserves_invariant step hD)
    (KernelGovernedTrajectoryInvariantOnly.refl D')

/-- Embed the invariant-only fragment into the full kernel-governed trajectory
type. -/
def toKernelGovernedTrajectory
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (h : KernelGovernedTrajectoryInvariantOnly sys D D') :
    KernelGovernedTrajectory sys D D' :=
  match h with
  | KernelGovernedTrajectoryInvariantOnly.refl D =>
      KernelGovernedTrajectory.refl D
  | KernelGovernedTrajectoryInvariantOnly.invariant_step
      step source_invariant target_invariant tail =>
      KernelGovernedTrajectory.invariant_step step source_invariant
        target_invariant (toKernelGovernedTrajectory tail)

end KernelGovernedTrajectoryInvariantOnly

end Safety

end Legitimacy
