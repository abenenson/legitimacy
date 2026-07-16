/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.SelfMod

/-!
# Self-modification boundary theorems

These theorems isolate the exact obstruction behind self-modification escape.
An override graph can only produce a later permit if some action in the finite
self-modification trajectory removes the override from an intermediate graph.
-/

set_option autoImplicit false

namespace Legitimacy

/-- For a graph that initially has an override, failure of override
corrigibility is exactly the existence of a single action that removes that
override. -/
theorem not_overrideCorrigible_of_override_decomposition
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hov : hasOverride G) :
    ¬ OverrideCorrigible G space ↔
      ∃ a : space.Action, ¬ hasOverride (space.apply a G) := by
  constructor
  · intro hncorr
    have hchar := not_override_corrigible_characterization G space hncorr
    rcases hchar with hno | hrem
    · exact False.elim (hno hov)
    · exact hrem.2
  · intro hrem hcorr
    obtain ⟨a, hremove⟩ := hrem
    exact hremove (hcorr.override_preserved a)

/-- Global override preservation rules out self-modification escape along every
finite trajectory: every claim is denied after every action sequence. -/
theorem no_selfmod_permit_under_override_preservation
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hov : hasOverride G)
    (hpres : OverridePreserving space)
    (actions : List space.Action)
    (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide (space.applySeq actions G) claims k = BinaryDecision.Deny := by
  exact hasOverride_denies
    (override_preserved_seq space hpres G hov actions) claims k

/-- If a self-modification trajectory starting from an override graph ever
permits a claim, then the action space was not globally override-preserving. -/
theorem selfmod_permit_refutes_override_preservation
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hov : hasOverride G)
    (actions : List space.Action)
    (claims : List ClaimQ) (k : ClaimantId)
    (hpermit :
      graphDecide (space.applySeq actions G) claims k =
        BinaryDecision.Permit) :
    ¬ OverridePreserving space := by
  intro hpres
  have hdeny := no_selfmod_permit_under_override_preservation
    G space hov hpres actions claims k
  rw [hdeny] at hpermit
  exact BinaryDecision.noConfusion hpermit

/-- Indexed finite-trajectory self-modification boundary: any successful escape
from an initial override graph has a concrete removal step at index `i`. The
pre-removal graph is exactly the state reached by applying the prefix
`actions.take i`, and the removing action is exactly `actions[i]?`. -/
theorem selfmod_escape_requires_indexed_override_removal_step
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hov : hasOverride G)
    (actions : List space.Action)
    (claims : List ClaimQ) (k : ClaimantId)
    (hpermit :
      graphDecide (space.applySeq actions G) claims k =
        BinaryDecision.Permit) :
    ∃ (i : Nat) (a : space.Action) (H : GovernanceGraph),
      H = space.applySeq (actions.take i) G ∧
        actions[i]? = some a ∧
        hasOverride H ∧
        ¬ hasOverride (space.apply a H) := by
  induction actions generalizing G with
  | nil =>
      have hdeny := hasOverride_denies hov claims k
      rw [AgentActionSpace.applySeq_nil, hdeny] at hpermit
      exact BinaryDecision.noConfusion hpermit
  | cons a rest ih =>
      by_cases hnext : hasOverride (space.apply a G)
      · obtain ⟨i, b, H, hH, hget, hHov, hremove⟩ :=
          ih (space.apply a G) hnext hpermit
        refine ⟨i + 1, b, H, ?_, ?_, hHov, hremove⟩
        · simpa [Nat.succ_eq_add_one] using hH
        · simpa [Nat.succ_eq_add_one] using hget
      · refine ⟨0, a, G, ?_, ?_, hov, hnext⟩
        · rfl
        · rfl

/-- Finite-trajectory self-modification impossibility boundary: any successful
escape from an initial override graph has a concrete removal step. The witness
is an action and the intermediate graph on which that action destroys the
override. -/
theorem selfmod_escape_requires_override_removal_step
    (G : GovernanceGraph) (space : AgentActionSpace)
    (hov : hasOverride G)
    (actions : List space.Action)
    (claims : List ClaimQ) (k : ClaimantId)
    (hpermit :
      graphDecide (space.applySeq actions G) claims k =
        BinaryDecision.Permit) :
    ∃ (a : space.Action) (H : GovernanceGraph),
      hasOverride H ∧ ¬ hasOverride (space.apply a H) := by
  obtain ⟨_i, a, H, _hH, _hget, hHov, hremove⟩ :=
    selfmod_escape_requires_indexed_override_removal_step
      G space hov actions claims k hpermit
  exact ⟨a, H, hHov, hremove⟩

end Legitimacy
