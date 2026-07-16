/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.Protocol

/-!
# Legitimacy.Attacks.Sovereignty

Priority-stratified override admissibility for constitutional layers.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A finite priority layer, with smaller indices denoting higher priority. -/
abbrev Layer (k : ℕ) := Fin k

/-- Layer-indexed evaluation of decision/property pairs. -/
structure LayerEval (k : ℕ) where
  eval : Layer k → Decision3 → GovernanceProperty → Bool

/-- An override targets a layer and transforms a decision at that layer. -/
structure Override (k : ℕ) where
  toLayer : Layer k
  transform : Decision3 → Decision3

/-- An override is admissible when it preserves every higher-or-equal layer. -/
def AdmissibleOverride {k : ℕ} (eval : LayerEval k) (ov : Override k) : Prop :=
  ∀ (L : Layer k), L ≤ ov.toLayer →
    ∀ (d : Decision3) (p : GovernanceProperty),
      eval.eval L d p = eval.eval L (ov.transform d) p

/-- A stratification certificate witnesses that every override is admissible. -/
def StratificationCertificate {k : ℕ} (eval : LayerEval k) (ovs : List (Override k)) : Prop :=
  ∀ ov ∈ ovs, AdmissibleOverride eval ov

/-- A sovereignty inversion flips some strictly higher-priority layer. -/
def SovereigntyInversion {k : ℕ} (eval : LayerEval k) (ovs : List (Override k)) : Prop :=
  ∃ (L : Layer k) (d : Decision3) (p : GovernanceProperty) (ov : Override k),
    ov ∈ ovs ∧
    L < ov.toLayer ∧
    eval.eval L d p ≠ eval.eval L (ov.transform d) p

/-- A stratification certificate excludes sovereignty inversions, because every
listed override preserves all higher-priority layers. -/
theorem strat_immune_to_inversion
    {k : ℕ}
    (eval : LayerEval k) (ovs : List (Override k))
    (hcert : StratificationCertificate eval ovs) :
    ¬ SovereigntyInversion eval ovs := by
  intro hinv
  rcases hinv with ⟨L, d, p, ov, hov_mem, hlt, hflip⟩
  have hov := hcert ov hov_mem
  have hpres := hov L (le_of_lt hlt) d p
  exact hflip hpres

/-- Two admissible overrides targeting the same layer compose to another
override that remains admissible on all higher-or-equal layers. -/
lemma strat_override_admissible_compose
    {k : ℕ}
    (eval : LayerEval k) (ov1 ov2 : Override k)
    (htarget : ov1.toLayer = ov2.toLayer)
    (h1 : AdmissibleOverride eval ov1)
    (h2 : AdmissibleOverride eval ov2) :
    ∀ (L : Layer k), L ≤ ov1.toLayer → ∀ (d : Decision3) (p : GovernanceProperty),
      eval.eval L d p = eval.eval L (ov2.transform (ov1.transform d)) p := by
  intro L hL d p
  have hfirst := h1 L hL d p
  have hL' : L ≤ ov2.toLayer := by
    simpa [htarget] using hL
  have hsecond := h2 L hL' (ov1.transform d) p
  exact hfirst.trans hsecond

end Legitimacy
