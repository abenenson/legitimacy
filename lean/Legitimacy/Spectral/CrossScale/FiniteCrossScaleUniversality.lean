/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.Core
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.FiveNode
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.SevenNode
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.NineNode
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.Universality

/-!
# Finite Cross-Scale Spectral Universality

# Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality

Import-stable umbrella for the finite cross-scale spectral universality modules
in the cross-scale spectral partition.

This umbrella imports every finite cross-scale spectral universality child
explicitly:

* `FiniteCrossScaleUniversality.Core` owns the shared spectral-window
  vocabulary and cross-scale predicates.
* `FiniteCrossScaleUniversality.FiveNode` owns the n=5 certificate family.
* `FiniteCrossScaleUniversality.SevenNode` owns the n=7 certificate family.
* `FiniteCrossScaleUniversality.NineNode` owns the n=9 certificate family.
* `FiniteCrossScaleUniversality.Universality` packages the finite-family
  theorem surface over those children.
-/
