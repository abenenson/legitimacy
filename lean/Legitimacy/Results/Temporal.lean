/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.Protocol

/-!
  Temporal consistency of the spectral governance protocol.

  The protocol rewrite moved proof obligations out of state constructors and
  into transition rules. This file proves temporal properties directly over the
  rewritten `ProtocolState` / `ValidTransition` definitions.

  Main results:

  1. `temporal_no_shortcut`: from any live state, reaching `Undeclared` is
     impossible.

  2. `sacrifices_monotone`: along any valid temporal trace, the sacrifice set
     can only grow.

  3. `erosion_resistance`: repeated protocol evolution cannot shrink the
     sacrifice set.

  All proofs complete — zero sorry.

  References:
  * `MathProtocol.lean` — protocol state machine and soundness
-/

namespace Legitimacy

-- ═══════════════════════════════════════════════════════════════════
-- § 1. Temporal traces
-- ═══════════════════════════════════════════════════════════════════

/-- A temporal trace is a finite sequence of protocol states connected by valid
    transitions. Defined inductively as a reflexive-transitive closure. -/
inductive TemporalTrace : ProtocolState → ProtocolState → Prop where
  | refl (s : ProtocolState) : TemporalTrace s s
  | step {s₁ s₂ s₃ : ProtocolState} :
      ValidTransition s₁ s₂ → TemporalTrace s₂ s₃ → TemporalTrace s₁ s₃

/-- Append two traces. -/
lemma TemporalTrace.trans {s₁ s₂ s₃ : ProtocolState}
    (h₁ : TemporalTrace s₁ s₂) (h₂ : TemporalTrace s₂ s₃) :
    TemporalTrace s₁ s₃ := by
  induction h₁ with
  | refl _ =>
      exact h₂
  | step hvt _ hih =>
      exact TemporalTrace.step hvt (hih h₂)

-- ═══════════════════════════════════════════════════════════════════
-- § 2. State classification
-- ═══════════════════════════════════════════════════════════════════

/-- A state is live. -/
def isLive : ProtocolState → Prop
  | ProtocolState.Live _ _ _ => True
  | _ => False

/-- A state is undeclared. -/
def isUndeclared : ProtocolState → Prop
  | ProtocolState.Undeclared => True
  | _ => False

-- ═══════════════════════════════════════════════════════════════════
-- § 3. No transition back to Undeclared
-- ═══════════════════════════════════════════════════════════════════

/-- No single valid transition goes from a live state to `Undeclared`. -/
lemma no_live_to_undeclared_step (s₁ s₂ : ProtocolState)
    (h : ValidTransition s₁ s₂) (hlive : isLive s₁) :
    ¬ isUndeclared s₂ := by
  cases h with
  | declare =>
      simp [isLive] at hlive
  | compile =>
      simp [isLive] at hlive
  | measure =>
      simp [isLive] at hlive
  | go_live =>
      simp [isLive] at hlive
  | supervise =>
      simp [isUndeclared]
  | resupervise =>
      simp [isLive] at hlive
  | drift =>
      simp [isUndeclared]
  | drift_supervised =>
      simp [isLive] at hlive
  | recompile =>
      simp [isUndeclared]
  | replant =>
      simp [isUndeclared]

/-- No valid transition targets `Undeclared`. `Undeclared` is a source, not a
    sink. -/
lemma undeclared_is_source (s₁ s₂ : ProtocolState)
    (h : ValidTransition s₁ s₂) :
    ¬ isUndeclared s₂ := by
  cases h <;> simp [isUndeclared]

/-- Any state reachable from `s` via a valid trace satisfies `P`, provided
    `P` holds for `s` and `P` is preserved by all valid transitions. -/
lemma trace_invariant (P : ProtocolState → Prop)
    (hstep : ∀ a b, ValidTransition a b → P a → P b)
    {s₁ s₂ : ProtocolState}
    (htrace : TemporalTrace s₁ s₂) (hs₁ : P s₁) : P s₂ := by
  induction htrace with
  | refl _ =>
      exact hs₁
  | step hvt htrace ih =>
      exact ih (hstep _ _ hvt hs₁)

/-- No non-`Undeclared` state can reach `Undeclared` via a valid trace. -/
lemma no_reach_undeclared {s : ProtocolState}
    (hnu : ¬ isUndeclared s)
    {t : ProtocolState}
    (htrace : TemporalTrace s t) :
    ¬ isUndeclared t :=
  trace_invariant (fun x => ¬ isUndeclared x)
    (fun a b hvt _ => undeclared_is_source a b hvt) htrace hnu

-- ═══════════════════════════════════════════════════════════════════
-- § 4. Main theorem: temporal no-shortcut
-- ═══════════════════════════════════════════════════════════════════

/-- **Temporal No-Shortcut Theorem.**
    From a live state, there is no valid trace to `Undeclared`. -/
theorem temporal_no_shortcut
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (h : TemporalTrace
      (ProtocolState.Live compiled report monitoring)
      ProtocolState.Undeclared) :
    False := by
  have hnu :
      ¬ isUndeclared (ProtocolState.Live compiled report monitoring) := by
    simp [isUndeclared]
  exact no_reach_undeclared hnu h (by simp [isUndeclared])

/-- From any declared state, there is no valid trace back to `Undeclared`. -/
lemma declared_no_regress
    (graph : GovernanceGraph)
    (sacrifices : List GovernanceProperty)
    (h : TemporalTrace
      (ProtocolState.Declared graph sacrifices)
      ProtocolState.Undeclared) :
    False := by
  have hnu : ¬ isUndeclared (ProtocolState.Declared graph sacrifices) := by
    simp [isUndeclared]
  exact no_reach_undeclared hnu h (by simp [isUndeclared])

-- ═══════════════════════════════════════════════════════════════════
-- § 5. Sacrifice monotonicity
-- ═══════════════════════════════════════════════════════════════════

/-- Extract the sacrifice list from a protocol state. `Undeclared` has the
    empty sacrifice list. -/
def sacrificesOf : ProtocolState → List GovernanceProperty
  | ProtocolState.Undeclared => []
  | ProtocolState.Declared _ s => s
  | ProtocolState.Compiled compiled => compiled.sacrifices
  | ProtocolState.Measured compiled _ => compiled.sacrifices
  | ProtocolState.Live compiled _ _ => compiled.sacrifices
  | ProtocolState.Supervised compiled _ _ _ => compiled.sacrifices
  | ProtocolState.Drifted compiled _ => compiled.sacrifices
  | ProtocolState.Recompiling orig _ _ => orig.sacrifices

/-- Sacrifice set inclusion: every element of `xs` is in `ys`. -/
def SacrificeSubset (xs ys : List GovernanceProperty) : Prop :=
  ∀ p, p ∈ xs → p ∈ ys

/-- Sacrifice-set inclusion is reflexive. -/
lemma SacrificeSubset.refl (xs : List GovernanceProperty) :
    SacrificeSubset xs xs :=
  fun _ h => h

/-- Sacrifice-set inclusion composes transitively. -/
lemma SacrificeSubset.trans {xs ys zs : List GovernanceProperty}
    (h₁ : SacrificeSubset xs ys) (h₂ : SacrificeSubset ys zs) :
    SacrificeSubset xs zs :=
  fun p hp => h₂ p (h₁ p hp)

/-- Every valid transition preserves or grows the sacrifice set. -/
lemma sacrifice_monotone_step (s₁ s₂ : ProtocolState)
    (h : ValidTransition s₁ s₂) :
    SacrificeSubset (sacrificesOf s₁) (sacrificesOf s₂) := by
  cases h with
  | declare =>
      intro p hp
      simp [sacrificesOf] at hp
  | compile =>
      exact SacrificeSubset.refl _
  | measure =>
      exact SacrificeSubset.refl _
  | go_live =>
      exact SacrificeSubset.refl _
  | supervise =>
      exact SacrificeSubset.refl _
  | resupervise =>
      exact SacrificeSubset.refl _
  | drift =>
      exact SacrificeSubset.refl _
  | drift_supervised =>
      exact SacrificeSubset.refl _
  | recompile =>
      exact SacrificeSubset.refl _
  | replant hsacrifices _ =>
      exact hsacrifices

/-- **Sacrifice Monotonicity Theorem.**
    Along any valid temporal trace, the sacrifice set can only grow.
    Governance properties cannot be silently reclaimed. -/
theorem sacrifices_monotone (s₁ s₂ : ProtocolState)
    (h : TemporalTrace s₁ s₂) :
    SacrificeSubset (sacrificesOf s₁) (sacrificesOf s₂) := by
  induction h with
  | refl _ =>
      exact SacrificeSubset.refl _
  | step hvt htrace ih =>
      exact SacrificeSubset.trans (sacrifice_monotone_step _ _ hvt) ih

-- ═══════════════════════════════════════════════════════════════════
-- § 6. Temporal consistency predicate and main theorem
-- ═══════════════════════════════════════════════════════════════════

/-- A protocol is temporally consistent if:
    1. live states cannot regress to `Undeclared`
    2. sacrifices are monotonically non-decreasing along any valid trace -/
def TemporallyConsistent : Prop :=
  (∀ (compiled : CompiledGovernance) (report : GovernanceRiskReport)
     (monitoring : MonitoringPlan),
     ¬ TemporalTrace (ProtocolState.Live compiled report monitoring)
       ProtocolState.Undeclared)
  ∧
  (∀ (s₁ s₂ : ProtocolState),
     TemporalTrace s₁ s₂ →
       SacrificeSubset (sacrificesOf s₁) (sacrificesOf s₂))

/-- **Temporal Consistency of the Protocol.**
    The rewritten protocol remains temporally consistent:
    - no regression from live to `Undeclared`
    - sacrifices grow monotonically -/
theorem protocol_temporally_consistent : TemporallyConsistent :=
  ⟨fun _ _ _ h => temporal_no_shortcut _ _ _ h,
   fun _ _ h => sacrifices_monotone _ _ h⟩

-- ═══════════════════════════════════════════════════════════════════
-- § 7. Erosion resistance
-- ═══════════════════════════════════════════════════════════════════

/-- Repeated protocol evolution cannot shrink the sacrifice set. -/
lemma erosion_resistance (s₁ s₂ : ProtocolState)
    (h : TemporalTrace s₁ s₂) :
    SacrificeSubset (sacrificesOf s₁) (sacrificesOf s₂) :=
  sacrifices_monotone s₁ s₂ h

end Legitimacy
