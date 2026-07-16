/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.PeerRelativeClass
import Legitimacy.Protocol.State

/-!
# Legitimacy.Protocol.Soundness

Reachability-based soundness theorems for the spectral governance protocol.

This module proves:

* preservation of `SoundState` along valid transitions
* global protocol soundness from `Undeclared`
* impossibility-driven non-emptiness of sacrifice lists in live states
-/

set_option autoImplicit false

namespace Legitimacy

/-- States that have reached compilation preserve the soundness obligations
derived by the compile judgment. -/
def SoundState : ProtocolState → Prop
  | ProtocolState.Undeclared => True
  | ProtocolState.Declared _ _ => True
  | ProtocolState.Compiled compiled =>
      NonSacrificedHold compiled.graph compiled.sacrifices ∧
        SacrificesJustified compiled.graph compiled.sacrifices
  | ProtocolState.Measured compiled report =>
      NonSacrificedHold compiled.graph compiled.sacrifices ∧
        SacrificesJustified compiled.graph compiled.sacrifices ∧
        RiskCalibrated report ∧ SpectrallyBounded report
  | ProtocolState.Live compiled report _ =>
      NonSacrificedHold compiled.graph compiled.sacrifices ∧
        SacrificesJustified compiled.graph compiled.sacrifices ∧
        RiskCalibrated report ∧ SpectrallyBounded report
  | ProtocolState.Supervised compiled report _ _ =>
      NonSacrificedHold compiled.graph compiled.sacrifices ∧
        SacrificesJustified compiled.graph compiled.sacrifices ∧
        RiskCalibrated report ∧ SpectrallyBounded report
  | ProtocolState.Drifted compiled drift_report =>
      NonSacrificedHold compiled.graph compiled.sacrifices ∧
        SacrificesJustified compiled.graph compiled.sacrifices ∧
        drift_report.violated_property ∉ compiled.sacrifices ∧
        ¬ propertyHolds drift_report.violated_property drift_report.observed_graph
  | ProtocolState.Recompiling orig orig_report _ =>
      NonSacrificedHold orig.graph orig.sacrifices ∧
        SacrificesJustified orig.graph orig.sacrifices ∧
        orig_report.violated_property ∉ orig.sacrifices ∧
        ¬ propertyHolds orig_report.violated_property orig_report.observed_graph

/-- Each valid protocol transition preserves the soundness payload attached to
its target state constructor. -/
lemma transition_preserves_sound
    {state next : ProtocolState}
    (hstep : ValidTransition state next) :
    SoundState state → SoundState next := by
  intro hs
  cases hstep with
  | declare =>
      trivial
  | compile hchecks =>
      obtain ⟨_, _, hsound, hjust⟩ := compilationChecks_sound hchecks
      exact ⟨hsound, hjust⟩
  | measure hrisk =>
      obtain ⟨hsound, hjust⟩ := hs
      exact ⟨hsound, hjust, hrisk.cv_le_cvBound,
        ⟨hrisk.signal_range, hrisk.cv_bound_le_spectral⟩⟩
  | go_live =>
      simpa [SoundState] using hs
  | supervise =>
      simpa [SoundState] using hs
  | resupervise =>
      simpa [SoundState] using hs
  | @drift compiled report monitoring drift_report hwatch =>
      obtain ⟨hsound, hjust, _, _⟩ := hs
      exact ⟨hsound, hjust, drift_report.not_sacrificed,
        drift_report.violation_proof⟩
  | @drift_supervised compiled report monitoring action drift_report hwatch =>
      obtain ⟨hsound, hjust, _, _⟩ := hs
      exact ⟨hsound, hjust, drift_report.not_sacrificed,
        drift_report.violation_proof⟩
  | recompile =>
      simpa [SoundState] using hs
  | replant _ hchecks =>
      obtain ⟨_, _, hsound, hjust⟩ := compilationChecks_sound hchecks
      exact ⟨hsound, hjust⟩

/-- Soundness propagates along every reachable transition sequence. -/
lemma reachable_sound
    {start finish : ProtocolState}
    (hstart : SoundState start)
    (hpath : TransitionSequence start finish) :
    SoundState finish := by
  induction hpath generalizing hstart with
  | refl =>
      exact hstart
  | tail path step ih =>
      exact transition_preserves_sound step (ih hstart)

/-- Any state reached from `Undeclared` satisfies the soundness obligations
associated with its constructor. -/
theorem protocol_soundness
    {finish : ProtocolState}
    (hpath : TransitionSequence ProtocolState.Undeclared finish) :
    SoundState finish := by
  have hstart : SoundState ProtocolState.Undeclared := by
    trivial
  exact reachable_sound hstart hpath

/-- A reachable live state preserves the compilation-side soundness payload and
the spectral risk calibration witness. -/
theorem protocol_live_soundness
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring)) :
    NonSacrificedHold compiled.graph compiled.sacrifices ∧
      SacrificesJustified compiled.graph compiled.sacrifices ∧
      ∃ signal_range : ℝ,
        report.factor_exposure.cv ≤ report.spectral_gap⁻¹ * signal_range := by
  have hs : SoundState (ProtocolState.Live compiled report monitoring) :=
    protocol_soundness hpath
  obtain ⟨h_nsh, h_just, hcal, hspec⟩ := hs
  rcases hspec with ⟨signal_range, hbound⟩
  exact ⟨h_nsh, h_just, signal_range, le_trans hcal hbound⟩

/-- A reachable supervised state preserves the same soundness payload as a
reachable live state. Supervisory intervention changes control, not the
compile-time sacrifice witness. -/
theorem protocol_supervised_soundness
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    {action : SupervisoryAction}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Supervised compiled report monitoring action)) :
    NonSacrificedHold compiled.graph compiled.sacrifices ∧
      SacrificesJustified compiled.graph compiled.sacrifices ∧
      ∃ signal_range : ℝ,
        report.factor_exposure.cv ≤ report.spectral_gap⁻¹ * signal_range := by
  have hs : SoundState (ProtocolState.Supervised compiled report monitoring action) :=
    protocol_soundness hpath
  obtain ⟨h_nsh, h_just, hcal, hspec⟩ := hs
  rcases hspec with ⟨signal_range, hbound⟩
  exact ⟨h_nsh, h_just, signal_range, le_trans hcal hbound⟩

/-- A reachable live state for a non-trivial graph cannot claim that nothing
was sacrificed. -/
lemma protocol_soundness_nonempty_sacrifice
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (h_nontrivial : NonTrivial compiled.graph) :
    compiled.sacrifices ≠ [] := by
  intro hempty
  obtain ⟨h_nsh, _, _⟩ := protocol_live_soundness hpath
  have hempty' : ∀ p : GovernanceProperty, p ∉ compiled.sacrifices := by
    intro p
    simp [hempty]
  have hcons : GraphConsistency compiled.graph :=
    h_nsh GovernanceProperty.Consistency (hempty' _)
  have hsol : GraphSolidarity compiled.graph :=
    h_nsh GovernanceProperty.Solidarity (hempty' _)
  have hmon : GraphMonotonicity compiled.graph :=
    h_nsh GovernanceProperty.Monotonicity (hempty' _)
  have hsp : GraphStrategyproofness compiled.graph :=
    h_nsh GovernanceProperty.Strategyproofness (hempty' _)
  exact h_nontrivial ⟨hcons, hsol, hmon, hsp⟩

/-- If a property is listed as sacrificed but actually holds, the declared
state cannot compile. -/
lemma no_phantom_sacrifices
    {graph : GovernanceGraph}
    {sacrifices : List GovernanceProperty}
    {report : CompilationReport}
    (p : GovernanceProperty)
    (hp : p ∈ sacrifices)
    (hholds : propertyHolds p graph) :
    ¬ CompilationChecks graph sacrifices report := by
  intro hchecks
  exact (hchecks.2 p hp).2 hholds

/-- Any non-trivial governance graph that reaches `Live` must expose a
non-empty, justified sacrifice list. -/
theorem impossibility_forces_sacrifice
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (h_nt : NonTrivial compiled.graph) :
    compiled.sacrifices ≠ [] ∧
    NonSacrificedHold compiled.graph compiled.sacrifices ∧
    SacrificesJustified compiled.graph compiled.sacrifices := by
  obtain ⟨h_nsh, h_sj, _⟩ := protocol_live_soundness hpath
  exact ⟨protocol_soundness_nonempty_sacrifice hpath h_nt, h_nsh, h_sj⟩

/-- First-effective peer-relative surfaces are non-trivial in the protocol
sense: the four graph diagnostics cannot all hold. -/
theorem effectivePeerRelativeSurface_nontrivial
    {G pref tail : GovernanceGraph}
    (heffective : EffectivePeerRelativeSurface G pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    NonTrivial G := by
  intro hall
  exact effectivePeerRelativeSurface_complete_impossibility G pref tail
    heffective hcomplete hall

/-- Operational consequence of the generalized theorem: any reachable live state
whose compiled graph has a complete first-effective peer-relative surface must
carry a non-empty, justified tradeoff declaration. -/
theorem effectivePeerRelativeSurface_live_forces_sacrifice
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    {pref tail : GovernanceGraph}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (heffective :
      EffectivePeerRelativeSurface compiled.graph pref tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    compiled.sacrifices ≠ [] ∧
    NonSacrificedHold compiled.graph compiled.sacrifices ∧
    SacrificesJustified compiled.graph compiled.sacrifices :=
  impossibility_forces_sacrifice hpath
    (effectivePeerRelativeSurface_nontrivial heffective hcomplete)

end Legitimacy
