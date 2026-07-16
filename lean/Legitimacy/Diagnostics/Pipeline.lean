/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.DecisionSystem
import Legitimacy.Impossibility.PeerRelativeClass

/-!
# Binary pipeline diagnostic bridges

This module relates pipeline-level predicates from `BinaryDecisionPipeline` to
the concrete governance-graph predicates used by the existing impossibility
stack.
-/

set_option autoImplicit false

namespace Legitimacy

/-- The pipeline-level peer-relative aggregator predicate specializes to the
existing concrete node-level predicate for governance graph nodes. -/
lemma pipelinePeerRelativeAggregator_eq_graphPeerRelativeAggregator
    (node : GovernanceNodeFn) :
    BinaryDecisionPipeline.IsPeerRelativeAggregator (P := GovernanceGraph) node ↔
      IsPeerRelativeAggregator node := by
  rfl

end Legitimacy
