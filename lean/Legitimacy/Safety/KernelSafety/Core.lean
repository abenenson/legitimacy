/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Examples
import Legitimacy.Attacks.Decomposition
import Legitimacy.Protocol.Protocol
import Legitimacy.Protocol.StatefulAdversary
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality
import Legitimacy.Extract.Soundness
import Legitimacy.Impossibility.PeerRelativeClass

/-!
# Legitimacy.Safety.KernelSafety.Core

Core invariant and transition vocabulary for kernel-relative safety.

This module owns the semantic kernel invariant, the governed graph projection,
and certified kernel transitions. It deliberately stops before monitored
sacrifice certificates and finite trajectories so those higher layers can
depend on a small transition surface.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-- The invariant preserved by kernel-governed execution: the datum remains a
semantic legitimacy kernel, i.e. it satisfies the five runtime kernel axioms
and the explicit graph-diagnostic/spectral bridge. -/
def KernelInvariant {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : Prop :=
  IsSemanticLegitimacyKernel D

/-- The graph governed by a kernel datum. At the current data-model layer the
graph is carried by the shared `GovernedSystem`, so all data over the same
system expose the same graph. -/
def kernelGraph {n : Nat} {sys : GovernedSystem n}
    (_D : LegitimacyKernelData sys) : GovernanceGraph :=
  sys.graph

/-- A raw concrete kernel transition between two data packages over the same
governed system. Unlike `KernelStep`, this records only the source datum, the
transition replay data, and the resulting target datum. It does not carry a
target invariant or monitored sacrifice certificate; later classifier theorems
must derive that boundary classification from separate monitor/extractor
hypotheses. -/
inductive RawKernelStep {n : Nat} {sys : GovernedSystem n} :
    LegitimacyKernelData sys → LegitimacyKernelData sys → Type 2 where
  /-- The empty raw kernel transition. -/
  | refl (D : LegitimacyKernelData sys) : RawKernelStep D D
  /-- A graph-preserving raw kernel-data mutation. -/
  | graphPreservingSpectralMutation
      (D D' : LegitimacyKernelData sys) : RawKernelStep D D'
  /-- An action-driven raw spectral-side mutation. The target datum is still
  selected by replay, but no semantic invariant for that target is stored in
  the step. -/
  | actionDrivenSpectralMutation
      (D : LegitimacyKernelData sys)
      (action_trace : List D.actionSpace.Action)
      (action_trace_nonempty : action_trace ≠ [])
      (targetFromReplay : GovernanceState → LegitimacyKernelData sys)
      (replay_changes_state :
        D.actionSpace.applySeq action_trace sys.state ≠ sys.state) :
      RawKernelStep D
        (targetFromReplay
          (D.actionSpace.applySeq action_trace sys.state))

namespace RawKernelStep

/-- Runtime self-modification actions recorded by a raw step. -/
def action_trace
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys} :
    RawKernelStep D D' → List D.actionSpace.Action
  | refl _ => []
  | graphPreservingSpectralMutation _ _ => []
  | actionDrivenSpectralMutation _ action_trace _ _ _ => action_trace

/-- The state reached by replaying the raw action trace. -/
def realized_state
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : RawKernelStep D D') : GovernanceState :=
  match step with
  | refl _ => sys.state
  | graphPreservingSpectralMutation _ _ => sys.state
  | actionDrivenSpectralMutation _ action_trace _ _ _ =>
      D.actionSpace.applySeq action_trace sys.state

/-- The raw recorded state is obtained by applying the raw action trace to the
governed system's current state. -/
theorem realized_by_kernel_actions
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : RawKernelStep D D') :
    step.realized_state = D.actionSpace.applySeq step.action_trace sys.state := by
  cases step with
  | refl =>
      simp [realized_state, RawKernelStep.action_trace]
  | graphPreservingSpectralMutation =>
      simp [realized_state, RawKernelStep.action_trace]
  | actionDrivenSpectralMutation
      action_trace action_trace_nonempty targetFromReplay replay_changes_state =>
      simp [realized_state, RawKernelStep.action_trace]

end RawKernelStep

/-- A concrete kernel transition between two data packages over the same
governed system. The constructors carry the replay data needed to name the
transition and, for non-reflexive steps, an explicit target-invariant witness.
The preservation lemmas below are projections or identity facts over those
constructor witnesses, not independently derived semantic laws. -/
inductive KernelStep {n : Nat} {sys : GovernedSystem n} :
    LegitimacyKernelData sys → LegitimacyKernelData sys → Type 2 where
  /-- The empty kernel transition preserves the semantic invariant by
  identity. -/
  | refl (D : LegitimacyKernelData sys) : KernelStep D D
  /-- A graph-preserving kernel-data mutation. At the current data layer all
  data over the same `GovernedSystem` share the same combinatorial governance
  graph; this constructor records a metadata/spectral-side mutation whose
  target datum has an explicit semantic-kernel witness. -/
  | graphPreservingSpectralMutation
      (D D' : LegitimacyKernelData sys)
      (target_invariant : KernelInvariant D') : KernelStep D D'
  /-- An action-driven spectral-side mutation. The target datum is selected by
  a function of the state reached by replaying a nonempty source-kernel action
  trace, so the transition's target is tied to the same replay recorded by
  `realized_by_kernel_actions`. -/
  | actionDrivenSpectralMutation
      (D : LegitimacyKernelData sys)
      (action_trace : List D.actionSpace.Action)
      (action_trace_nonempty : action_trace ≠ [])
      (targetFromReplay : GovernanceState → LegitimacyKernelData sys)
      (replay_changes_state :
        D.actionSpace.applySeq action_trace sys.state ≠ sys.state)
      (target_invariant :
        KernelInvariant
          (targetFromReplay
            (D.actionSpace.applySeq action_trace sys.state))) :
      KernelStep D
        (targetFromReplay
          (D.actionSpace.applySeq action_trace sys.state))

namespace KernelStep

/-- Runtime self-modification actions are drawn from the source datum's
certified action interface. -/
def action_trace
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys} :
    KernelStep D D' → List D.actionSpace.Action
  | refl _ => []
  | graphPreservingSpectralMutation _ _ _ => []
  | actionDrivenSpectralMutation _ action_trace _ _ _ _ => action_trace

/-- The state reached by replaying the certified action trace. -/
def realized_state
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : KernelStep D D') : GovernanceState :=
  match step with
  | refl _ => sys.state
  | graphPreservingSpectralMutation _ _ _ => sys.state
  | actionDrivenSpectralMutation _ action_trace _ _ _ _ =>
      D.actionSpace.applySeq action_trace sys.state

/-- The recorded state is obtained by applying the certified action trace to
the governed system's current state. -/
theorem realized_by_kernel_actions
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : KernelStep D D') :
    step.realized_state = D.actionSpace.applySeq step.action_trace sys.state := by
  cases step with
  | refl =>
      simp [realized_state, KernelStep.action_trace]
  | graphPreservingSpectralMutation target target_invariant =>
      simp [realized_state, KernelStep.action_trace]
  | actionDrivenSpectralMutation
      action_trace action_trace_nonempty targetFromReplay replay_changes_state
      target_invariant =>
      simp [realized_state, KernelStep.action_trace]

/-- The empty kernel transition preserves the semantic invariant by identity. -/
lemma kernelInvariant_preserved_by_refl
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) :
    KernelInvariant D → KernelInvariant D :=
  fun source_invariant => source_invariant

/-- Graph-preserving spectral mutations preserve the semantic invariant by the
target semantic-kernel witness supplied to their constructor. -/
lemma kernelInvariant_preserved_by_graphPreservingSpectralMutation
    {n : Nat} {sys : GovernedSystem n}
    (D D' : LegitimacyKernelData sys)
    (target_invariant : KernelInvariant D') :
    KernelInvariant D → KernelInvariant D' :=
  fun _source_invariant => target_invariant

/-- Action-driven spectral mutations preserve the semantic invariant by the
semantic-kernel witness for the replay-selected target. -/
lemma kernelInvariant_preserved_by_actionDrivenSpectralMutation
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (action_trace : List D.actionSpace.Action)
    (_action_trace_nonempty : action_trace ≠ [])
    (targetFromReplay : GovernanceState → LegitimacyKernelData sys)
    (_replay_changes_state :
      D.actionSpace.applySeq action_trace sys.state ≠ sys.state)
    (target_invariant :
      KernelInvariant
        (targetFromReplay
          (D.actionSpace.applySeq action_trace sys.state))) :
    KernelInvariant D →
      KernelInvariant
        (targetFromReplay
          (D.actionSpace.applySeq action_trace sys.state)) :=
  fun _source_invariant => target_invariant

end KernelStep

/-- Kernel steps preserve the invariant because each non-reflexive constructor
already carries the target-invariant witness; this theorem exposes that
witness-projection uniformly. Sacrifice-routed transitions are represented
separately by monitored sacrifice certificates. -/
theorem kernelStep_preserves_invariant
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : KernelStep D D')
    (hD : KernelInvariant D) :
    KernelInvariant D' :=
  match step with
  | KernelStep.refl _ =>
      KernelStep.kernelInvariant_preserved_by_refl D hD
  | KernelStep.graphPreservingSpectralMutation _ target target_invariant =>
      KernelStep.kernelInvariant_preserved_by_graphPreservingSpectralMutation
        D target target_invariant hD
  | KernelStep.actionDrivenSpectralMutation
      _ action_trace action_trace_nonempty targetFromReplay
      replay_changes_state target_invariant =>
      KernelStep.kernelInvariant_preserved_by_actionDrivenSpectralMutation
        D action_trace action_trace_nonempty targetFromReplay
        replay_changes_state target_invariant hD

end Safety

end Legitimacy
