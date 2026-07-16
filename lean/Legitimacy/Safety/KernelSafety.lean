/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.Core
import Legitimacy.Safety.KernelSafety.Sacrifice
import Legitimacy.Safety.KernelSafety.Trajectory
import Legitimacy.Safety.KernelSafety.BinaryDecisionPipeline
import Legitimacy.Safety.KernelSafety.ReachabilityStack
import Legitimacy.Safety.KernelSafety.GovernanceExamples
import Legitimacy.Safety.KernelSafety.StatefulExamples

/-!
# Legitimacy.Safety.KernelSafety

Import-stable umbrella for kernel-relative safety theorems.

This file intentionally contains no proof content. It preserves the historical
`Legitimacy.Safety.KernelSafety` import while the implementation is organized
by responsibility:

* `KernelSafety.Core` owns the semantic invariant, governed graph projection,
  certified kernel transitions, and direct transition preservation.
* `KernelSafety.Sacrifice` owns sacrificed obligations, monitored sacrifice
  obligations, stateful critical-capability violations, and certificate
  constructors.
* `KernelSafety.Trajectory` owns finite kernel-governed trajectories and the
  invariant-only trajectory fragment.
* `KernelSafety.BinaryDecisionPipeline` owns no-undeclared-sacrifice theorems
  for binary-pipeline live surfaces, bounded stateful preservation,
  aggregator-witnessed sacrifice predicates, and the stateful
  bounded-corrigibility-or-sacrifice disjunction.
* `KernelSafety.ReachabilityStack` owns reachable-state safety and the
  extracted-kernel theorem that composes reachability, stateful sidecars, and
  empirical parity.
* `KernelSafety.GovernanceExamples` owns base governance fixtures: the
  five-node semantic kernel datum, widened-signal mutation, action-driven
  mutation, and simple trajectories.
* `KernelSafety.StatefulExamples` owns concrete stateful adversaries,
  supercritical sacrifice-route examples, extractor artifacts, and worked
  stack instantiations.

The dependency order is `Core -> Sacrifice -> Trajectory`, with
`BinaryDecisionPipeline` depending on `Sacrifice`, `ReachabilityStack`
depending on `Trajectory` and `BinaryDecisionPipeline`, and examples layered
after the generic theorem modules. New declarations should be added to the
module that owns their responsibility; this umbrella should remain a re-export
surface for downstream import compatibility.
-/
