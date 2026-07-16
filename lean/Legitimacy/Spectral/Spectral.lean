/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Core.ConcreteGraphs
import Legitimacy.Spectral.CrossScale.ASIUniversality
import Legitimacy.Spectral.Capacity.Structural
import Legitimacy.Spectral.CrossScale.ClaimantInteraction
import Legitimacy.Spectral.Dynamics.Bifurcation
import Legitimacy.Spectral.Capacity.CriticalCapability
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality
import Legitimacy.Spectral.Channels.ThresholdGovernanceChannel
import Legitimacy.Spectral.Core.LegitimacyEntropy
import Legitimacy.Spectral.Core.Localizability
import Legitimacy.Spectral.Capacity.MultiDecisionCapacity
import Legitimacy.Spectral.CrossScale.N9Archetypes
import Legitimacy.Spectral.Core.PerturbationBounds
import Legitimacy.Spectral.Dynamics.Stackelberg
import Legitimacy.Spectral.Dynamics.StackelbergConvergence
import Legitimacy.Spectral.CrossScale.Universality

/-!
# Legitimacy.Spectral.Spectral

Import-stable entrypoint for the spectral theorem cluster.

The spectral substrate is split into topic directories:

* `Core`: graph primitives, perturbation/localizability facts, entropy, and
  well-connected product predicates;
* `Capacity`: structural capacity, critical-capability thresholds, and
  capacity converses;
* `Channels`: finite governance-channel probes and noisy-channel calibration;
* `Certificates`: positive-procedure carriers above the channel layer;
* `Dynamics`: Stackelberg, bifurcation, and free-energy readings;
* `CrossScale`: claimant-interaction, basin, archetype, and universality
  packages.

This umbrella imports the stable public subset used by downstream theorem
surfaces. `Legitimacy.lean` imports additional leaf modules directly when those
leaves are part of the full crate build but not this compact spectral entrypoint.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {n : Nat}

/-! ## Combined statement (over F) -/

/-- **Combined pointwise perturbation bounds.** -/
theorem spectral_governance_combined (G : GovGraph F n) [NeZero n]
    (s : Fin n → F) (R : F) (hR : 0 ≤ R)
    (hsr : ∀ a b : Fin n, |s a - s b| ≤ R)
    (k i : Fin n)
    (hD : 0 < G.deg i) (hD' : 0 < G.degRemoved k i) :
    |G.gov s i - G.govRemoved s k i| ≤ R ∧
    |G.gov s i - G.govRemoved s k i| * G.deg i ≤ R * G.W i k ∧
    |G.gov s i - G.govRemoved s k i| * G.deg i ≤ R * G.maxDeg :=
  ⟨G.perturbation_le_signalRange s R hR hsr k i hD hD',
   G.perturb_deg_le_signalRange_mul_weight s R hsr k i hD hD',
   G.perturb_deg_le_signalRange_mul_maxDeg s R hR hsr k i hD hD'⟩

end Legitimacy
