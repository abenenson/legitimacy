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

def nemoDialoguePolicyGuard : CallbackDecl where
  name := "dialogue_policy_guard"
  body :=
    .ifThenElse (.fieldEq "intent" "unsafe")
      (.returnDecision .deny)
      (.returnDecision .allow)

def nemoDialoguePolicyRegistration : Registration where
  hook := "DialoguePolicy"
  callback := "dialogue_policy_guard"

def nemoGuardrailsProgram : Program :=
  .mk [] [] [nemoDialoguePolicyGuard] [nemoDialoguePolicyRegistration]

theorem nemo_guardrails_python_hook_core_graph_equivalent
    (graph : GovernanceGraph)
    (hextract : extractPythonHookCore nemoGuardrailsProgram = .ok graph) :
    DecisionSystem.Equivalent
      (sourceGovernanceGraphSemantics nemoGuardrailsProgram)
      graph :=
  extractPythonHookCore_decision_equivalent nemoGuardrailsProgram graph hextract

end Corpus
end PythonHookCore
end Legitimacy
