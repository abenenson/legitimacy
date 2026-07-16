/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Corrigible

/-!
# Legitimacy.Results.SelfMod — Self-modification resistance for ASI governance

A governance graph is self-modification resistant if the agent cannot
change it through its available actions.

## Two forms

1. **Strong self-modification resistance**: for all agent actions `a`,
   `apply a G = G`. The graph is a fixpoint of the action space.

2. **Weak self-modification resistance**: for all agent actions `a`,
   the governance properties of `apply a G` are at least as strong as
   those of `G`. The graph may change structurally, but its governance
   guarantees are preserved.

## Main results

- `strong_selfmod_implies_override_preserved` — strong self-mod resistance
  implies that the override is preserved under all actions.
- `strong_selfmod_implies_override_corrigible` — strong self-mod resistance on
  a graph with an override implies override-fragment corrigibility.
- `strong_selfmod_seq_fixpoint` — a fixpoint under single actions is a
  fixpoint under all finite sequences.
- `weak_selfmod_preserves_override` — weak self-mod resistance (with
  override as the monitored property) implies override preservation.
- `selfmod_override_corrigible_stability` — self-mod resistance plus
  override-fragment corrigibility means the system denies all claims after any
  action sequence.

All proofs complete — zero sorry.

## References

* Soares et al., "Corrigibility", MIRI Technical Report, 2015.
* Hadfield-Menell et al., "The Off-Switch Game", 2017.
-/

set_option autoImplicit false

namespace Legitimacy

/-! ### Strong self-modification resistance -/

/-- **Strong self-modification resistance**: for every agent action,
    the governance graph is unchanged. The graph is a fixpoint of the
    entire action space.

    This is the strongest form: the agent literally cannot modify its
    own governance structure. -/
def StrongSelfModResistant (G : GovernanceGraph) (space : AgentActionSpace) : Prop :=
  ∀ (a : space.Action), space.apply a G = G

/-- Under strong self-mod resistance, any single action preserves the
    graph identity, hence preserves all properties including override. -/
lemma strong_selfmod_implies_override_preserved
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hfix : StrongSelfModResistant G space)
    (hov : hasOverride G) :
    ∀ (a : space.Action), hasOverride (space.apply a G) := by
  intro a
  rw [hfix a]
  exact hov

/-- **Self-modification resistance implies override-fragment corrigibility.**
    If the graph is a fixpoint and has an override, it is override-corrigible. -/
theorem strong_selfmod_implies_override_corrigible
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hfix : StrongSelfModResistant G space)
    (hov : hasOverride G) :
    OverrideCorrigible G space where
  has_override := hov
  override_preserved := strong_selfmod_implies_override_preserved G space hfix hov

/-- **Strong self-mod resistance is preserved under sequences.**
    If every single action is a fixpoint on G, then any finite sequence
    of actions is also a fixpoint on G. -/
lemma strong_selfmod_seq_fixpoint
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hfix : StrongSelfModResistant G space)
    (actions : List space.Action) :
    space.applySeq actions G = G := by
  induction actions with
  | nil => rfl
  | cons a as ih =>
    simp only [AgentActionSpace.applySeq]
    rw [hfix a]
    exact ih

/-- Under strong self-mod resistance, the graph denies all claims after
    any sequence of actions (if it has an override). -/
lemma strong_selfmod_denies_all
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hfix : StrongSelfModResistant G space)
    (hov : hasOverride G)
    (actions : List space.Action)
    (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide (space.applySeq actions G) claims k = BinaryDecision.Deny := by
  rw [strong_selfmod_seq_fixpoint G space hfix actions]
  exact hasOverride_denies hov claims k

/-! ### Weak self-modification resistance -/

/-- A **governance invariant** is a predicate on governance graphs that
    we want to preserve under agent actions. -/
def GovInvariant := GovernanceGraph → Prop

/-- **Weak self-modification resistance**: every agent action preserves
    a given governance invariant. The graph may change structurally,
    but the invariant is maintained.

    This is weaker than `StrongSelfModResistant` because the graph
    can change — only the invariant is preserved. -/
def WeakSelfModResistant
    (G : GovernanceGraph) (space : AgentActionSpace)
    (inv : GovInvariant) : Prop :=
  ∀ (a : space.Action), inv G → inv (space.apply a G)

/-- Weak self-mod resistance with `hasOverride` as the invariant implies
    override preservation (and hence corrigibility). -/
lemma weak_selfmod_preserves_override
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hweak : WeakSelfModResistant G space hasOverride)
    (hov : hasOverride G) :
    ∀ (a : space.Action), hasOverride (space.apply a G) :=
  fun a => hweak a hov

/-- Weak self-mod resistance with `hasOverride` as the invariant implies
    override-fragment corrigibility. -/
theorem weak_selfmod_implies_override_corrigible
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hweak : WeakSelfModResistant G space hasOverride)
    (hov : hasOverride G) :
    OverrideCorrigible G space where
  has_override := hov
  override_preserved := weak_selfmod_preserves_override G space hweak hov

/-- Strong self-mod resistance implies weak self-mod resistance for any
    invariant. If the graph does not change, every invariant is preserved. -/
lemma strong_implies_weak
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hfix : StrongSelfModResistant G space)
    (inv : GovInvariant) :
    WeakSelfModResistant G space inv := by
  intro a hinv
  rw [hfix a]
  exact hinv

/-! ### Weak self-mod resistance lifts to sequences -/

/-- If every action preserves an invariant on *every* graph (not just G),
    then any sequence preserves the invariant. -/
lemma weak_selfmod_seq
    (space : AgentActionSpace)
    (inv : GovInvariant)
    (hpres : ∀ (a : space.Action) (H : GovernanceGraph),
      inv H → inv (space.apply a H))
    (G : GovernanceGraph) (hinv : inv G)
    (actions : List space.Action) :
    inv (space.applySeq actions G) := by
  induction actions generalizing G with
  | nil => exact hinv
  | cons a as ih => exact ih (space.apply a G) (hpres a G hinv)

/-! ### Combined stability theorem -/

/-- **Stability theorem.** If a governance graph is override-corrigible and
    the action space preserves overrides globally, then the system denies all
    claims after any finite sequence of agent actions. This is the core safety
    guarantee: the agent cannot escape governance. -/
theorem selfmod_override_corrigible_stability
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hcorr : OverrideCorrigible G space)
    (hpres : OverridePreserving space)
    (actions : List space.Action)
    (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide (space.applySeq actions G) claims k = BinaryDecision.Deny :=
  override_corrigible_denies_after_seq G space hcorr hpres actions claims k

/-! ### Composition of action spaces -/

/-- The **sum action space**: the agent can take actions from either
    of two action spaces. -/
def AgentActionSpace.sum (s₁ s₂ : AgentActionSpace) : AgentActionSpace where
  Action := s₁.Action ⊕ s₂.Action
  apply := fun a G =>
    match a with
    | Sum.inl a₁ => s₁.apply a₁ G
    | Sum.inr a₂ => s₂.apply a₂ G

/-- If both component spaces preserve overrides, so does their sum. -/
lemma sum_preserves_override
    (s₁ s₂ : AgentActionSpace)
    (hp₁ : OverridePreserving s₁)
    (hp₂ : OverridePreserving s₂) :
    OverridePreserving (s₁.sum s₂) := by
  intro a G hov
  cases a with
  | inl a₁ => exact hp₁ a₁ G hov
  | inr a₂ => exact hp₂ a₂ G hov

/-- Strong self-mod resistance is preserved under the sum of action spaces,
    if the graph is a fixpoint of both components. -/
lemma strong_selfmod_sum
    (G : GovernanceGraph)
    (s₁ s₂ : AgentActionSpace)
    (hfix₁ : StrongSelfModResistant G s₁)
    (hfix₂ : StrongSelfModResistant G s₂) :
    StrongSelfModResistant G (s₁.sum s₂) := by
  intro a
  cases a with
  | inl a₁ => exact hfix₁ a₁
  | inr a₂ => exact hfix₂ a₂

end Legitimacy
