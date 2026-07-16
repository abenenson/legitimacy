/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.RGFlow

/-!
  ASI-safe universality packaging for the `n = 5` spectral RG witnesses.

  The computational content lives in `RGFlow`; this module exists to provide a
  stable import surface for the `δ`-parametric ASI spectral signature and its
  concrete depth-3 witness.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Re-export of the concrete positive-`δ` ASI-safe spectral witness on the
depth-3 `n = 5` RG lattice. -/
theorem concrete_iterated_RG_n5_universality
    (δ : ℚ) (hδ : 0 < δ) :
    ASISpectralSignature δ (GovGraph.rgTrajectory uniK5 sig5 δ 3) ∧
    ASISpectralSignature δ (GovGraph.rgTrajectory asymK5 sig5 δ 3) ∧
    ASISpectralSignature δ (GovGraph.rgTrajectory nearPath5 sig5 δ 3) ∧
    ¬ ASISpectralSignature δ (GovGraph.rgTrajectory bottleneck5 sig5 δ 3) ∧
    ASISpectralSignature δ (GovGraph.rgTrajectory wheel5 sig5 δ 3) :=
  concrete_iterated_RG_n5_parametric_signature δ hδ

end Legitimacy
