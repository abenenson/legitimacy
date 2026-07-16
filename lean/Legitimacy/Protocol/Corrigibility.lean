/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Examples
import Legitimacy.Protocol.Drift

/-!
# Legitimacy.Protocol.Corrigibility

This module packages the protocol's drift/recompile results with the
override-fragment corrigibility predicate into one named theorem for the
paper-level claim: recompilation can address drift without destroying the
override pathway, provided the revised graph retains the original override.
-/

set_option autoImplicit false

namespace Legitimacy

/-- If recompilation retains the original override, then the revised graph is
override-corrigible under the same globally override-preserving action space. -/
lemma override_retained_corrigible
    (G revised : GovernanceGraph) (space : AgentActionSpace)
    (hcorr : OverrideCorrigible G space)
    (hpres : OverridePreserving space)
    (hoverride_retained : hasOverride G → hasOverride revised) :
    OverrideCorrigible revised space := by
  have hov_revised : hasOverride revised :=
    hoverride_retained hcorr.has_override
  refine ⟨hov_revised, ?_⟩
  intro a
  exact hpres a revised hov_revised

/-- Any successful recompile step either sacrifices the violated property or
proves that the revised graph satisfies it. -/
lemma recompilation_addresses_witnessed_drift
    {orig : CompiledGovernance}
    {orig_report : DriftReport orig}
    {revised : GovernanceGraph}
    {sacrifices : List GovernanceProperty}
    {compilation_report : CompilationReport}
    (hchecks : CompilationChecks revised sacrifices compilation_report) :
    orig_report.violated_property ∈ sacrifices ∨
      propertyHolds orig_report.violated_property revised := by
  exact recompiling_must_address_drift
    (orig := orig)
    (orig_report := orig_report)
    (revised := revised)
    (sacrifices := sacrifices)
    (report := compilation_report)
    hchecks

/-- Discharging the revised compile checks yields a concrete transition from
the drifted state back to some compiled state. -/
lemma recompilation_reaches_compiled
    {orig : CompiledGovernance}
    {orig_report : DriftReport orig}
    {revised : GovernanceGraph}
    {sacrifices : List GovernanceProperty}
    {compilation_report : CompilationReport}
    (hsacrifices : ∀ p : GovernanceProperty, p ∈ orig.sacrifices → p ∈ sacrifices)
    (hchecks : CompilationChecks revised sacrifices compilation_report) :
    ∃ compiled' : CompiledGovernance,
      TransitionSequence
        (ProtocolState.Drifted orig orig_report)
        (ProtocolState.Compiled compiled') := by
  rcases recompile_cycle_terminates_drifted
      (orig := orig)
      (report := orig_report)
      (revised := revised)
      (sacrifices := sacrifices)
      (compilation_report := compilation_report)
      hsacrifices hchecks with
    ⟨compiled', hpath, _, _⟩
  exact ⟨compiled', hpath⟩

/-- **Corrigibility under adversarial recompilation.**

    If the original governance graph is override-corrigible, the action space
    preserves overrides globally, and the revised graph retains the original
    override, then a successful drift-triggered recompile cycle preserves the
    override pathway, must address the witnessed drift, and reaches a compiled
    state. -/
theorem corrigibility_under_recompile
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hcorr : OverrideCorrigible G space)
    (hpres : OverridePreserving space)
    (orig : CompiledGovernance)
    (orig_report : DriftReport orig)
    (revised : GovernanceGraph)
    (hoverride_retained : hasOverride G → hasOverride revised)
    (sacrifices : List GovernanceProperty)
    (compilation_report : CompilationReport)
    (hsacrifices : ∀ p : GovernanceProperty, p ∈ orig.sacrifices → p ∈ sacrifices)
    (hchecks : CompilationChecks revised sacrifices compilation_report) :
    OverrideCorrigible revised space ∧
      (orig_report.violated_property ∈ sacrifices ∨
        propertyHolds orig_report.violated_property revised) ∧
      ∃ compiled' : CompiledGovernance,
        TransitionSequence
          (ProtocolState.Drifted orig orig_report)
          (ProtocolState.Compiled compiled') := by
  have hcorr_revised : OverrideCorrigible revised space :=
    override_retained_corrigible G revised space hcorr hpres hoverride_retained
  have haddress :
      orig_report.violated_property ∈ sacrifices ∨
        propertyHolds orig_report.violated_property revised :=
    recompilation_addresses_witnessed_drift
      (orig_report := orig_report)
      (hchecks := hchecks)
  rcases recompilation_reaches_compiled
      (orig := orig)
      (orig_report := orig_report)
      (revised := revised)
      (sacrifices := sacrifices)
      (compilation_report := compilation_report)
      hsacrifices hchecks with
    ⟨compiled', hpath⟩
  exact ⟨hcorr_revised, haddress, ⟨compiled', hpath⟩⟩

/-- The protocol-level corrigibility invariant tracked across arbitrary
self-modification trajectories is preservation of the kernel's supervisory
algebra. -/
abbrev CorrigibilityInvariant (S : GovernanceState)
    (alg : SupervisoryAlgebra) : Prop :=
  SupportsAlgebra S alg

/-- Apply an arbitrary finite self-modification trajectory to the kernel's
initial governance state. -/
abbrev applyTrajectory {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    List K.actionSpace.Action → GovernanceState :=
  fun trajectory => K.actionSpace.applySeq trajectory sys.state

/-- **Corrigibility under arbitrary self-modification.**

Any finite trajectory drawn from the kernel's own self-modification action
space preserves the supervisory algebra guaranteed by the kernel's
corrigibility witness. This is the arbitrary-trajectory analogue of the
single-cycle recompilation theorem above. -/
theorem corrigibility_under_arbitrary_selfmod
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys)
    (trajectory : List K.actionSpace.Action) :
    CorrigibilityInvariant (applyTrajectory K trajectory) K.algebra := by
  simpa [CorrigibilityInvariant, applyTrajectory] using
    K.corrigible.algebra_preserved trajectory

end Legitimacy
