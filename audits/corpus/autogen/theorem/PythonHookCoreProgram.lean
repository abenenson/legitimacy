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

def autogenApprovalGuard : CallbackDecl where
  name := "approval_guard"
  body :=
    .ifThenElse (.fieldEq "action" "rm")
      (.returnDecision .deny)
      (.returnDecision .allow)

def autogenApprovalRegistration : Registration where
  hook := "CodeExecutorApproval"
  callback := "approval_guard"

def autogenProgram : Program :=
  .mk [] [] [autogenApprovalGuard] [autogenApprovalRegistration]

theorem autogen_python_hook_core_graph_equivalent
    (graph : GovernanceGraph)
    (hextract : extractPythonHookCore autogenProgram = .ok graph) :
    DecisionSystem.Equivalent
      (sourceGovernanceGraphSemantics autogenProgram)
      graph :=
  extractPythonHookCore_decision_equivalent autogenProgram graph hextract

end Corpus
end PythonHookCore
end Legitimacy
