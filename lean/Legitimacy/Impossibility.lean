/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.AxiomIndependence
import Legitimacy.Impossibility.AxiomLattice
import Legitimacy.Impossibility.ConstructiveCompanion
import Legitimacy.Impossibility.PeerRelativeClass
import Legitimacy.Impossibility.PeerRelativeReachable

/-!
# Legitimacy.Impossibility

Import-stable umbrella for impossibility-theorem support modules.

This file intentionally contains no proof content. It preserves the
`Legitimacy.Impossibility` import surface while the implementation is organized
by responsibility:

* `Impossibility.AxiomIndependence` owns independence witnesses for the
  diagnostic axioms.
* `Impossibility.AxiomLattice` owns lattice structure over axiom bundles.
* `Impossibility.PeerRelativeClass` owns peer-relative class counterexamples.
* `Impossibility.PeerRelativeReachable` owns reachable-stage generalization.
* `Impossibility.ConstructiveCompanion` owns constructive companion examples.

New declarations should live in the module that owns their responsibility; this
umbrella should remain a re-export surface for downstream import compatibility.
-/
