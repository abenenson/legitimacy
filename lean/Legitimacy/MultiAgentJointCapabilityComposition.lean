/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.MultiAgentJointCapabilityComposition.Core
import Legitimacy.MultiAgentJointCapabilityComposition.CanonicalFixtures
import Legitimacy.MultiAgentJointCapabilityComposition.BoolFixtures
import Legitimacy.MultiAgentJointCapabilityComposition.IndependenceFixtures

/-!
# Legitimacy.MultiAgentJointCapabilityComposition

Import-stable umbrella for joint-capability composition modules.

The implementation is organized by responsibility:

* `MultiAgentJointCapabilityComposition.Core` owns the shared joint-capability
  substrate and preservation theorems.
* `MultiAgentJointCapabilityComposition.CanonicalFixtures` owns the Unit-action
  Spera tightness fixtures.
* `MultiAgentJointCapabilityComposition.BoolFixtures` owns the nontrivial
  Bool-action Spera fixtures.
* `MultiAgentJointCapabilityComposition.IndependenceFixtures` owns the
  hypothesis-independence and drop-test witnesses.

New declarations should live in the module that owns their responsibility; this
umbrella should remain a re-export surface for downstream import compatibility.
-/
