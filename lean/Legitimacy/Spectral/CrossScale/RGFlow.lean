/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.RGFlow.Core
import Legitimacy.Spectral.CrossScale.RGFlow.N5
import Legitimacy.Spectral.CrossScale.RGFlow.N7
import Legitimacy.Spectral.CrossScale.RGFlow.Robustness

/-!
# Legitimacy.Spectral.CrossScale.RGFlow

Import-stable umbrella for renormalization-group coarse-graining modules in
the cross-scale spectral partition.

This module imports the focused child modules:

* `RGFlow.Core` owns pairwise and partition-family coarse-graining, selector
  definitions, RG states, trajectory APIs, and fixed-point/preservation facts.
* `RGFlow.N5` owns the concrete n=5 iterated-RG table and positive-δ spectral
  signature package.
* `RGFlow.Robustness` owns the three-family n=5 universality theorems for
  Cheeger, modularity, and signal-preserving partition families.
* `RGFlow.N7` owns the n=7 extension table and depth-3 inequality frontier.
-/
