/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.GovernanceAdmissibilityAudit.Core -- direct sub-module import: umbrella re-export
import Legitimacy.Results.GovernanceAdmissibilityAudit.Traversal -- direct sub-module import: umbrella re-export
import Legitimacy.Results.GovernanceAdmissibilityAudit.Cycles -- direct sub-module import: umbrella re-export
import Legitimacy.Results.GovernanceAdmissibilityAudit.Evaluation -- direct sub-module import: umbrella re-export
import Legitimacy.Results.GovernanceAdmissibilityAudit.Checks -- direct sub-module import: umbrella re-export
import Legitimacy.Results.GovernanceAdmissibilityAudit.Fixtures -- direct sub-module import: umbrella re-export

/-!
# Legitimacy.Results.GovernanceAdmissibilityAudit

Import-stable umbrella for governance admissibility audit modules.

This file intentionally contains no proof content. It preserves the historical
`Legitimacy.Results.GovernanceAdmissibilityAudit` import while the implementation
is organized by responsibility:

* `GovernanceAdmissibilityAudit.Core` owns audit graph data, canonicalization,
  and synthetic claim generation.
* `GovernanceAdmissibilityAudit.Traversal` owns acyclic traversal state, queue
  propagation, topological orders, and traversal determinism helpers.
* `GovernanceAdmissibilityAudit.Cycles` owns cycle discovery, fixed-point cycle
  iteration, and nonvacuity diagnostics.
* `GovernanceAdmissibilityAudit.Evaluation` owns concrete node evaluation,
  perturbation helpers, graph projections, and traversal-determinism diagnostics.
* `GovernanceAdmissibilityAudit.Checks` owns audit check cores, status
  dispatchers, summaries, and verdict projections.
* `GovernanceAdmissibilityAudit.Fixtures` owns tightness fixtures, the compiler
  audit fixture, and theorem-facing certificates.

New declarations should live in the module that owns their responsibility; this
umbrella should remain a re-export surface for downstream import compatibility.
-/
