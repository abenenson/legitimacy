/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.PeerRelativeClass
import Legitimacy.Spectral.Core.ConcreteGraphs
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality
import Mathlib.Tactic.NormNum

/-!
# Claimant Interaction Encoding

Weighted-graph substrate induced by the binary first-effective
peer-relative surface.
-/

set_option autoImplicit false

namespace Legitimacy

/-- The uniform complete claimant-interaction graph on `n` claimants. -/
def uniformCompleteGraph (n : Nat) : GovGraph ℚ n where
  weights i j := if i = j then 0 else 1
  weight_symm := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  weight_nonneg := by
    intro i j
    by_cases hij : i = j <;> simp [hij]
  weight_self_zero := by
    intro i
    simp

/-- The empty certified-interaction graph used when a binary pipeline has no
first-effective peer-relative surface certificate. -/
def nullInteractionGraph (n : Nat) : GovGraph ℚ n where
  weights _ _ := 0
  weight_symm := by
    intro _ _
    rfl
  weight_nonneg := by
    intro _ _
    rfl
  weight_self_zero := by
    intro _
    rfl

/-- The constructed complete peer-relative claimant-interaction carrier. At
arity five this is definitionally the already-discharged `uniK5` spectral
archetype; at other arities it is the same uniform complete-graph construction
over the corresponding finite claimant type. This is a construction choice, not
a theorem deriving complete support from an arbitrary aggregator predicate. -/
def constructedPeerRelativeInteractionGraph : (n : Nat) → GovGraph ℚ n
  | 5 => uniK5
  | n => uniformCompleteGraph n

/-- Natural weighted-graph encoding of a binary peer-relative pipeline `G`
over `n` claimants. When `G` is certified as a complete first-effective
peer-relative surface, the first decision-relevant gate is the median-style
`peerRelativeNode`; every claimant's strength can affect every other
claimant's median comparison, so the induced interaction carrier is the
uniform complete graph. Outside that certified class, this encoding returns the
zero graph to make the missing semantic certificate explicit. -/
noncomputable def claimantInteractionGraph
    (G : GovernanceGraph) (n : Nat) [NeZero n] : GovGraph ℚ n :=
  by
    classical
    exact
      if ∃ pref tail, CompleteFirstEffectivePeerRelativeSurfaceClass G pref tail then
        constructedPeerRelativeInteractionGraph n
      else
        nullInteractionGraph n

/-- Certified complete first-effective peer-relative surfaces induce the
constructed complete claimant-interaction carrier by definition of
`claimantInteractionGraph`. This is a carrier-equality lemma for the chosen
encoding, not a structural derivation of the carrier from arbitrary aggregator
witnesses. -/
theorem claimantInteractionGraph_eq_constructedPeerRelativeCarrier_of_completeSurface
    {G : GovernanceGraph} {n : Nat} [NeZero n]
    (h : ∃ pref tail, CompleteFirstEffectivePeerRelativeSurfaceClass G pref tail) :
    claimantInteractionGraph G n = constructedPeerRelativeInteractionGraph n := by
  classical
  simp [claimantInteractionGraph, h]

/-- The singleton median peer-relative pipeline is a complete first-effective
peer-relative surface. -/
theorem peerRelativeNode_singleton_completeFirstEffectivePeerRelativeSurfaceClass :
    CompleteFirstEffectivePeerRelativeSurfaceClass [peerRelativeNode] [] [] := by
  constructor
  · constructor
    · rfl
    · intro node hmem
      cases hmem
  · intro claims k hpermit
    simp [graphDecide]

/-- For the median-rule peer-relative gate over five claimants, the claimant
interaction graph is exactly the uniform complete graph `K_5` already used in
the spectral section. -/
theorem peerRelativeNode_claimantInteractionGraph_eq_uniK5 :
    claimantInteractionGraph [peerRelativeNode] 5 = uniK5 := by
  rw [claimantInteractionGraph_eq_constructedPeerRelativeCarrier_of_completeSurface
    (G := [peerRelativeNode]) (n := 5)
    ⟨[], [], peerRelativeNode_singleton_completeFirstEffectivePeerRelativeSurfaceClass⟩]
  rfl

/-- For the median-rule peer-relative gate over five claimants, the induced
claimant-interaction graph inherits the discharged complete-graph spectral gap
of `5`. -/
theorem peerRelativeNode_claimantInteractionGraph_spectralGap_eq_five :
    (claimantInteractionGraph [peerRelativeNode] 5).spectralGap
      (by norm_num : 2 ≤ 5) = (5 : ℝ) := by
  rw [peerRelativeNode_claimantInteractionGraph_eq_uniK5]
  simpa [fiveNodeCompleteSpectralGapCertificate] using
    uniK5_spectralGap_eq_certificate

/-- Positive consistency vulnerability on the median-rule claimant-interaction
carrier gives a concrete `SpectralWellConnectedAt` witness at threshold `0`.
The nonzero spectral factor is the complete-graph gap inherited from `uniK5`. -/
theorem peerRelativeNode_claimantInteractionGraph_spectralWellConnectedAt_zero
    (s : Fin 5 → ℚ)
    (hs : 0 < (claimantInteractionGraph [peerRelativeNode] 5).cv s) :
    SpectralWellConnectedAt (claimantInteractionGraph [peerRelativeNode] 5)
      s 0 (by norm_num : 2 ≤ 5) := by
  unfold SpectralWellConnectedAt
  constructor
  · unfold SpectralConnected
    rw [peerRelativeNode_claimantInteractionGraph_spectralGap_eq_five]
    norm_num
  · unfold PositiveGovernanceVulnerabilityAt
    rw [peerRelativeNode_claimantInteractionGraph_spectralGap_eq_five]
    have hcv_nonneg :
        0 ≤ ((claimantInteractionGraph [peerRelativeNode] 5).cv s : ℝ) := by
      exact_mod_cast le_of_lt hs
    simpa only [ge_iff_le, Rat.cast_zero] using
      (mul_nonneg (show (0 : ℝ) ≤ 5 by norm_num) hcv_nonneg)

/-- Median-rule construction theorem: the binary singleton peer-relative surface
induces the `uniK5` spectral substrate and therefore admits an explicit
parameterized spectral-connectivity witness whenever the induced CV is
positive. -/
theorem peerRelativeNode_claimantInteractionGraph_spectralGap_bound
    (s : Fin 5 → ℚ)
    (hs : 0 < (claimantInteractionGraph [peerRelativeNode] 5).cv s) :
    ∃ θ_min : ℚ,
      θ_min ≤ (17 / 20 : ℚ) ∧
      SpectralWellConnectedAt (claimantInteractionGraph [peerRelativeNode] 5)
        s θ_min (by norm_num : 2 ≤ 5) := by
  refine ⟨0, by norm_num, ?_⟩
  exact peerRelativeNode_claimantInteractionGraph_spectralWellConnectedAt_zero s hs

end Legitimacy
