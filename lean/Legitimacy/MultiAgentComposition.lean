/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.MultiAgentComposition.Core
import Legitimacy.MultiAgentComposition.Certificates
import Legitimacy.MultiAgentComposition.Fixtures

/-!
# Legitimacy.MultiAgentComposition

Import-stable umbrella for cross-agent composition modules.

The implementation is organized by responsibility:

* `MultiAgentComposition.Core` owns the shared cross-agent substrate,
  compatibility witnesses, and anchored-representative realization theorem.
* `MultiAgentComposition.Certificates` owns failure certificates and
  kernel-aware failure extraction.
* `MultiAgentComposition.Fixtures` owns worked two-agent fixtures and
  per-condition independence witnesses.

New declarations should live in the module that owns their responsibility; this
umbrella should remain a re-export surface for downstream import compatibility.
-/
