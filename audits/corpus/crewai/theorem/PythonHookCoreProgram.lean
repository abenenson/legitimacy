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

def crewAIToolHookGuard : CallbackDecl where
  name := "tool_hook_guard"
  body :=
    .ifThenElse (.fieldEq "tool_name" "dangerous_tool")
      (.returnDecision .deny)
      (.returnDecision .allow)

def crewAIToolHookRegistration : Registration where
  hook := "BeforeToolCall"
  callback := "tool_hook_guard"

def crewAIProgram : Program :=
  .mk [] [] [crewAIToolHookGuard] [crewAIToolHookRegistration]

theorem crewai_python_hook_core_graph_equivalent
    (graph : GovernanceGraph)
    (hextract : extractPythonHookCore crewAIProgram = .ok graph) :
    DecisionSystem.Equivalent
      (sourceGovernanceGraphSemantics crewAIProgram)
      graph :=
  extractPythonHookCore_decision_equivalent crewAIProgram graph hextract

end Corpus
end PythonHookCore
end Legitimacy
