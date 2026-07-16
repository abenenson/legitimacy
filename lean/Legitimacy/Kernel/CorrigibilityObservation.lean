/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Unified

/-!
# Legitimacy.Kernel.CorrigibilityObservation

Observable corrigibility state exposed over unbundled kernel data.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Observable corrigibility status for one kernel datum. Bundled kernels expose
the invariant `.Corrigible` observation by construction, while external data
can instantiate alternative observations. -/
inductive CorrigibilityState where
  | Corrigible
  | Drifted
  | Recompiling
  deriving Repr, DecidableEq, Inhabited

/-- Observation interface exposing corrigibility state for one unbundled kernel
datum. -/
class KernelObservation {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : Type where
  observeCorrigibility : CorrigibilityState

instance {n : Nat} {sys : GovernedSystem n} (K : LegitimacyKernel sys) :
    KernelObservation K.toLegitimacyKernelData where
  observeCorrigibility := .Corrigible

/-- The bundled kernel's observation agrees definitionally with the bundled
corrigibility invariant. -/
theorem bundled_observation_matches_invariant
    {n : Nat} {sys : GovernedSystem n} (K : LegitimacyKernel sys) :
    KernelObservation.observeCorrigibility (D := K.toLegitimacyKernelData) =
      CorrigibilityState.Corrigible := rfl

end Legitimacy
