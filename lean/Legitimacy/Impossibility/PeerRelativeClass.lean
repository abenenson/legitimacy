/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.PeerRelativeClass.Predicates
import Legitimacy.Impossibility.PeerRelativeClass.Witnesses
import Legitimacy.Impossibility.PeerRelativeClass.Countermodel
import Legitimacy.Impossibility.PeerRelativeClass.Obstructions

/-!
# Quantified peer-relative class impossibility

# Legitimacy.Impossibility.PeerRelativeClass

Import-stable umbrella for the peer-relative class impossibility development.

The public API is split across:

* `PeerRelativeClass.Predicates`: class predicates and transparent-prefix
  infrastructure;
* `PeerRelativeClass.Witnesses`: concrete peer-relative and route-separation
  witnesses;
* `PeerRelativeClass.Obstructions`: complete-surface obstruction theorems;
* `PeerRelativeClass.Countermodel`: the deny-all countermodel for the weak
  syntactic class.
-/
