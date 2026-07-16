/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.PythonHookCore.Soundness

set_option autoImplicit false

namespace Legitimacy
namespace PythonHookCore
namespace Corpus

def langGraphCheckpointInterruptGuard : CallbackDecl where
  name := "checkpoint_interrupt_guard"
  body :=
    .ifThenElse (.fieldEq "state" "missing_checkpoint")
      (.returnDecision .deny)
      (.ifThenElse (.fieldEq "state" "requires_human_resume")
        (.returnDecision .ask)
        (.returnDecision .allow))

def langGraphInterruptRegistration : Registration where
  hook := "InterruptBeforeTool"
  callback := "checkpoint_interrupt_guard"

def langGraphProgram : Program :=
  .mk [] [] [langGraphCheckpointInterruptGuard] [langGraphInterruptRegistration]

theorem langgraph_python_hook_core_graph_equivalent
    (graph : GovernanceGraph)
    (hextract : extractPythonHookCore langGraphProgram = .ok graph) :
    DecisionSystem.Equivalent
      (sourceGovernanceGraphSemantics langGraphProgram)
      graph :=
  extractPythonHookCore_decision_equivalent langGraphProgram graph hextract

end Corpus
end PythonHookCore
end Legitimacy
