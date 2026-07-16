/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Channels.CStarChannelBridge
import Legitimacy.Spectral.Core.SpectralWellConnected

/-!
# Capability response and spectral threshold compatibility

This module packages the common `C_star` reading shared by the deterministic
capability-response channel and the `SpectralWellConnected` product cone.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset

/-- On the `SpectralWellConnected` product cone, the deterministic capability
response permits exactly when capability clears the exact critical threshold,
and the same `C_star` is bounded above by the spectral-gap witness supplied by
the product-cone classification. -/
theorem SpectralWellConnected_capabilityResponse_threshold_via_spectralGap
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (hn : 2 ≤ n)
    (s : Fin n → ℚ) (δ C : ℚ)
    (hδ : 0 < δ) (hC : 0 < C)
    (hG : SpectralWellConnected G s hn) :
    G.capabilityResponse s δ C = BinaryDecision.Permit ↔
      (C_star G s δ : ℝ) ≤ (C : ℝ) ∧
        SpectralWellConnected G s hn ∧
          (C_star G s δ : ℝ) ≤
            (20 : ℝ) / 17 * (δ : ℝ) * G.spectralGap hn := by
  have hcv : 0 < G.cv s :=
    SpectralWellConnected_cv_pos G s hn hG
  have hresponse :=
    G.capabilityResponse_eq_permit_iff_C_star_le s δ C hδ hcv hC
  have hupper :=
    SpectralWellConnected_C_star_le_spectralGap G s hn δ hδ.le hG
  constructor
  · intro hpermit
    have hthreshold : C_star G s δ ≤ C := hresponse.mp hpermit
    have hthresholdR : (C_star G s δ : ℝ) ≤ (C : ℝ) := by
      exact_mod_cast hthreshold
    exact ⟨hthresholdR, hG, hupper⟩
  · intro h
    have hthreshold : C_star G s δ ≤ C := by
      exact_mod_cast h.1
    exact hresponse.mpr hthreshold

/-- Spectral sandwich form of the compatibility result. The lower
expander-style bound is not a consequence of `SpectralWellConnected` alone; it
also needs the existing degree hypotheses from the `C_star` spectral theorem.
Under those hypotheses, the capability response, the exact threshold, and both
spectral bounds are one transitive package. -/
theorem SpectralWellConnected_capabilityResponse_C_star_sandwich
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (hn : 2 ≤ n)
    (s : Fin n → ℚ) (δ C : ℚ)
    (hδ : 0 < δ) (hC : 0 < C)
    (hmin : 0 < G.minRemovedDeg)
    (hsg_le : ∀ i : Fin n, G.spectralGap hn ≤ Rat.cast (G.deg i))
    (hG : SpectralWellConnected G s hn) :
    (δ : ℝ) * G.spectralGap hn /
        (((signalRange s : ℚ) : ℝ) * (G.maxDeg : ℝ)) ≤
      (C_star G s δ : ℝ) ∧
    (G.capabilityResponse s δ C = BinaryDecision.Permit ↔
      (C_star G s δ : ℝ) ≤ (C : ℝ)) ∧
    (C_star G s δ : ℝ) ≤
      (20 : ℝ) / 17 * (δ : ℝ) * G.spectralGap hn := by
  have hcv : 0 < G.cv s :=
    SpectralWellConnected_cv_pos G s hn hG
  have hsg : 0 < G.spectralGap hn :=
    (SpectralWellConnected_positive_factors G s hn hG).1
  have hlower :=
    governance_graph_C_star_expander_bound G hn s δ hδ hcv hmin hsg hsg_le
  have hupper :=
    SpectralWellConnected_C_star_le_spectralGap G s hn δ hδ.le hG
  refine ⟨hlower, ?_, hupper⟩
  have hresponse :=
    G.capabilityResponse_eq_permit_iff_C_star_le s δ C hδ hcv hC
  constructor
  · intro hpermit
    have hthreshold : C_star G s δ ≤ C := hresponse.mp hpermit
    exact_mod_cast hthreshold
  · intro hthresholdR
    have hthreshold : C_star G s δ ≤ C := by
      exact_mod_cast hthresholdR
    exact hresponse.mpr hthreshold

end Legitimacy
