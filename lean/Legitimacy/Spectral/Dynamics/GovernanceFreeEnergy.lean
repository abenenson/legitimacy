/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Channels.CStarChannelBridge
import Mathlib.Tactic.Linarith

/-!
# Governance free energy

This module gives the exact critical-capability threshold a free-energy
reading.  The scalar

`C * cv(G, s) - δ`

is the capability budget after paying the graph-local sensitivity cost.  Its
zero set is exactly the deterministic capability-response transition.
-/

set_option autoImplicit false

namespace Legitimacy

namespace GovGraph

variable {n : Nat}

/-- Governance free energy at capability `C`: capability times graph-wide
consistency vulnerability, minus the target perturbation tolerance. -/
def governanceFreeEnergy
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ C : ℚ) : ℚ :=
  C * G.cv s - δ

/-- The reciprocal critical capability is exactly the zero level set of
governance free energy. -/
theorem C_star_le_iff_governanceFreeEnergy_nonneg
    (G : GovGraph ℚ n) [NeZero n]
    (s : Fin n → ℚ) (δ C : ℚ)
    (hcv : 0 < G.cv s) :
    C_star G s δ ≤ C ↔ 0 ≤ G.governanceFreeEnergy s δ C := by
  constructor
  · intro hle
    have hbudget : δ ≤ C * G.cv s := by
      exact (div_le_iff₀ hcv).mp (by simpa [C_star] using hle)
    simp [governanceFreeEnergy]
    linarith
  · intro henergy
    have hbudget : δ ≤ C * G.cv s := by
      simpa [governanceFreeEnergy] using henergy
    exact (div_le_iff₀ hcv).mpr (by simpa [C_star] using hbudget)

/-- Free-energy form of the deterministic capability-response transition:
positive capability permits exactly when the governance free energy is
nonnegative. -/
theorem capabilityResponse_eq_permit_iff_governanceFreeEnergy_nonneg
    (G : GovGraph ℚ n) [NeZero n]
    (s : Fin n → ℚ) (δ C : ℚ)
    (hδ : 0 < δ) (hcv : 0 < G.cv s) (hC : 0 < C) :
    G.capabilityResponse s δ C = BinaryDecision.Permit ↔
      0 ≤ G.governanceFreeEnergy s δ C :=
  (G.capabilityResponse_eq_permit_iff_C_star_le s δ C hδ hcv hC).trans
    (G.C_star_le_iff_governanceFreeEnergy_nonneg s δ C hcv)

/-- Signed phase-transition packaging: negative governance free energy forces
denial, while nonnegative governance free energy forces permit. -/
theorem capabilityResponse_governanceFreeEnergy_sign_dichotomy
    (G : GovGraph ℚ n) [NeZero n]
    (s : Fin n → ℚ) (δ C : ℚ)
    (hδ : 0 < δ) (hcv : 0 < G.cv s) (hC : 0 < C) :
    (G.governanceFreeEnergy s δ C < 0 →
      G.capabilityResponse s δ C = BinaryDecision.Deny) ∧
    (0 ≤ G.governanceFreeEnergy s δ C →
      G.capabilityResponse s δ C = BinaryDecision.Permit) := by
  have hiff :=
    G.capabilityResponse_eq_permit_iff_governanceFreeEnergy_nonneg
      s δ C hδ hcv hC
  constructor
  · intro hneg
    have hnotPermit : G.capabilityResponse s δ C ≠ BinaryDecision.Permit := by
      intro hpermit
      exact not_le_of_gt hneg (hiff.mp hpermit)
    cases hresp : G.capabilityResponse s δ C with
    | Permit =>
        exact False.elim (hnotPermit hresp)
    | Deny =>
        rfl
  · intro hnonneg
    exact hiff.mpr hnonneg

end GovGraph

end Legitimacy
