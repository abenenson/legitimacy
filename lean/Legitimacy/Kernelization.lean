/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernelization.Core
import Legitimacy.Kernelization.Fixtures
import Legitimacy.Kernelization.StructuralExamples
import Legitimacy.Kernelization.SemanticFailure
import Legitimacy.Kernelization.EndToEnd
import Legitimacy.Kernelization.Tightness

/-!
# Legitimacy.Kernelization

Import-stable umbrella for kernelization-honesty modules.

The implementation is organized by responsibility:

* `Kernelization.Core` owns authority-surface vocabulary, certificates, and the
  extractor honesty theorem.
* `Kernelization.Fixtures` owns concrete compiled artifacts shared by examples.
* `Kernelization.StructuralExamples` owns clean and structural certificate
  examples.
* `Kernelization.SemanticFailure` owns semantic-bridge failure certificates.
* `Kernelization.EndToEnd` owns extractor-contract worked examples.
* `Kernelization.Tightness` owns nonvacuity, independence, and minimality
  tightness witnesses.

New declarations should live in the module that owns their responsibility; this
umbrella should remain a re-export surface for downstream import compatibility.
-/
