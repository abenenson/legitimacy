/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Graph
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

/-!
# Behavioral governance games

This module introduces a finite-friendly behavioral substrate for the spectral
Stackelberg layer. The objects here are ordinary deterministic games with
rational utilities: agents choose an action profile, utilities are evaluated at
a state, the state transition is deterministic, and the governance mechanism
returns binary decisions for each agent.

The definitions intentionally live beside the existing spectral surrogates.
They do not redefine `cv`, `spViolation`, or the current spectral equilibrium
predicates.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Observation labels available to deterministic governance games. -/
inductive ObservationType where
  | Public : ObservationType
  | PrivateView : ObservationType
  | Opaque : ObservationType
  deriving Repr, DecidableEq

/-- Dependent action profiles: one action for each agent. -/
abbrev ActionProfile {Agents : Type} (Action : Agents → Type) : Type :=
  (i : Agents) → Action i

/-- A deterministic rational governance game. -/
structure BehavioralGovernanceGame where
  Agents : Type
  State : Type
  Action : Agents → Type
  Utility : Agents → State → ActionProfile Action → ℚ
  Transition : State → ActionProfile Action → State
  Observation : Agents → State → ObservationType
  GovernanceDecision : State → ActionProfile Action → Agents → BinaryDecision

namespace BehavioralGovernanceGame

variable (game : BehavioralGovernanceGame)

/-- Utility gain from replacing one action profile by another. -/
def utilityGain
    (agent : game.Agents) (state : game.State)
    (base deviated : ActionProfile game.Action) : ℚ :=
  game.Utility agent state deviated - game.Utility agent state base

/-- A unilateral, capability-feasible, utility-improving deviation. -/
structure ProfitableDeviation (κ : ℚ) where
  agent : game.Agents
  state : game.State
  base : ActionProfile game.Action
  deviated : ActionProfile game.Action
  unilateral : ∀ j : game.Agents, j ≠ agent → deviated j = base j
  positive_gain : 0 < game.utilityGain agent state base deviated
  capability_feasible : game.utilityGain agent state base deviated ≤ κ

namespace ProfitableDeviation

variable {game} {κ : ℚ} (dev : game.ProfitableDeviation κ)

/-- The rational utility gain carried by a profitable deviation. -/
def gain : ℚ :=
  game.utilityGain dev.agent dev.state dev.base dev.deviated

lemma gain_pos : 0 < dev.gain := dev.positive_gain

lemma gain_le_capability : dev.gain ≤ κ := dev.capability_feasible

end ProfitableDeviation

/-- No feasible profitable unilateral deviation exists at capability `κ`. -/
def NashStableAtCapability (κ : ℚ) : Prop :=
  ¬ ∃ _dev : game.ProfitableDeviation κ, True

/-- Strategyproofness across every positive capability level. -/
def GameStrategyproof : Prop :=
  ∀ κ : ℚ, 0 < κ → game.NashStableAtCapability κ

/-- Capability scaling used by behavioral Stackelberg persistence statements. -/
structure CapabilityScaling where
  scaling : ℚ → ℚ
  monotone : ∀ ⦃κ₁ κ₂ : ℚ⦄, κ₁ ≤ κ₂ → scaling κ₁ ≤ scaling κ₂
  positive : ∀ ⦃κ : ℚ⦄, 0 < κ → 0 < scaling κ

/-- Positive best-response regularity: if a profitable deviation exists at a
capability/tolerance pair, then some profitable deviation has enough rational
gain to cross the tolerance-normalized capability scale. This is the behavioral
condition needed by the first one-way spectral equilibrium embedding. -/
def BestResponseRegularity : Prop :=
  ∀ ⦃κ δ : ℚ⦄, 0 < κ → 0 < δ →
    (∃ _dev : game.ProfitableDeviation κ, True) →
      ∃ dev : game.ProfitableDeviation κ, δ / κ ≤ dev.gain

/-- A checkable lower-bound certificate for the gain threshold used at one
capability/tolerance pair. -/
def BestResponseLowerBound (gainFloor : ℚ → ℚ → ℚ) : Prop :=
  ∀ ⦃κ δ : ℚ⦄, 0 < κ → 0 < δ → δ / κ ≤ gainFloor κ δ

/-- Constructive best-response witness extraction against an explicit gain
floor. -/
def BestResponseExistence (gainFloor : ℚ → ℚ → ℚ) : Prop :=
  ∀ ⦃κ δ : ℚ⦄, 0 < κ → 0 < δ →
    (∃ _dev : game.ProfitableDeviation κ, True) →
      ∃ dev : game.ProfitableDeviation κ, gainFloor κ δ ≤ dev.gain

/-- Capability monotonicity for the explicit gain floor: increasing feasible
capability should not raise the gain that must be exposed at a fixed
tolerance. -/
def BestResponseMonotone (gainFloor : ℚ → ℚ → ℚ) : Prop :=
  ∀ ⦃κ₁ κ₂ δ : ℚ⦄, 0 < κ₁ → κ₁ ≤ κ₂ →
    gainFloor κ₂ δ ≤ gainFloor κ₁ δ

/-- Fixed-scale decomposed best-response regularity. The lower-bound field
connects the floor to the spectral threshold, and the existence field
constructs the deviation witness at one capability/tolerance scale. -/
structure BestResponseAtScaleDecomposition where
  gainFloor : ℚ → ℚ → ℚ
  lowerBound : BestResponseLowerBound gainFloor
  existence : game.BestResponseExistence gainFloor

/-- Capability-monotone decomposed best-response regularity. This extends the
fixed-scale certificate with an audit of how the floor scales across
capabilities. -/
structure BestResponseDecomposition extends game.BestResponseAtScaleDecomposition where
  monotone : BestResponseMonotone gainFloor

/-- A game is fixed-scale decomposed-regular when it has an explicit
best-response gain floor with witness extraction. -/
def BestResponseAtScaleRegularity : Prop :=
  Nonempty game.BestResponseAtScaleDecomposition

/-- A game is decomposed-regular when it has an explicit, capability-monotone
best-response gain floor with witness extraction. -/
def BestResponseDecomposedRegularity : Prop :=
  Nonempty game.BestResponseDecomposition

/-- Behavioral persistence at one capability/tolerance pair. -/
def BehavioralPersistentEquilibrium (κ δ : ℚ) : Prop :=
  0 < κ ∧ 0 < δ ∧
    game.BestResponseAtScaleRegularity ∧ game.NashStableAtCapability κ

/-- A game keeps finding persistent equilibria at arbitrarily high capability. -/
def BehavioralUnboundedPersistence (δ : ℚ) : Prop :=
  ∀ κ₀ : ℚ, 0 < κ₀ →
    ∃ κ : ℚ, κ₀ ≤ κ ∧ game.BehavioralPersistentEquilibrium κ δ

/-- Stackelberg persistence along a monotone capability scale. -/
def StackelbergPersistent (scaling : CapabilityScaling) : Prop :=
  ∀ δ κ₀ : ℚ, 0 < δ → 0 < κ₀ →
    ∃ κ : ℚ, κ₀ ≤ κ ∧
      game.BehavioralPersistentEquilibrium (scaling.scaling κ) δ

lemma nashStableAtCapability_iff_no_profitable_deviation (κ : ℚ) :
    game.NashStableAtCapability κ ↔ ¬ ∃ _dev : game.ProfitableDeviation κ, True :=
  Iff.rfl

lemma gameStrategyproof_no_profitable_deviation
    (h : game.GameStrategyproof) {κ : ℚ} (hκ : 0 < κ) :
    ¬ ∃ _dev : game.ProfitableDeviation κ, True :=
  h κ hκ

lemma not_gameStrategyproof_of_profitable_deviation
    {κ : ℚ} (hκ : 0 < κ) (dev : game.ProfitableDeviation κ) :
    ¬ game.GameStrategyproof := by
  intro hsp
  exact hsp κ hκ ⟨dev, trivial⟩

lemma bestResponseRegularity_of_decomposed
    (h : game.BestResponseAtScaleRegularity) :
    game.BestResponseRegularity := by
  intro κ δ hκ hδ hdev
  rcases h with ⟨regular⟩
  obtain ⟨dev, hfloor_gain⟩ := regular.existence hκ hδ hdev
  exact ⟨dev, le_trans (regular.lowerBound hκ hδ) hfloor_gain⟩

lemma bestResponseAtScaleRegularity_of_decomposed
    (h : game.BestResponseDecomposedRegularity) :
    game.BestResponseAtScaleRegularity := by
  rcases h with ⟨regular⟩
  exact ⟨regular.toBestResponseAtScaleDecomposition⟩

lemma bestResponseRegularity_of_monotone_decomposed
    (h : game.BestResponseDecomposedRegularity) :
    game.BestResponseRegularity :=
  game.bestResponseRegularity_of_decomposed
    (game.bestResponseAtScaleRegularity_of_decomposed h)

end BehavioralGovernanceGame

export BehavioralGovernanceGame
  (CapabilityScaling ProfitableDeviation BestResponseRegularity
   BestResponseLowerBound BestResponseExistence BestResponseMonotone
   BestResponseAtScaleDecomposition BestResponseAtScaleRegularity
   BestResponseDecomposition BestResponseDecomposedRegularity
   BehavioralPersistentEquilibrium BehavioralUnboundedPersistence
   GameStrategyproof NashStableAtCapability StackelbergPersistent)

end Legitimacy
