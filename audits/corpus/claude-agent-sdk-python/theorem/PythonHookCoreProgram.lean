/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.PythonHookCore.Fixtures.ClaudeAgentSDK

set_option autoImplicit false

namespace Legitimacy
namespace PythonHookCore
namespace Corpus

def claudeAgentSDKProgram : Program :=
  Fixtures.claudeAgentSDKPreToolUseProgram

theorem claude_agent_sdk_python_hook_core_graph_equivalent
    (graph : GovernanceGraph)
    (hextract : extractPythonHookCore claudeAgentSDKProgram = .ok graph) :
    DecisionSystem.Equivalent
      (sourceGovernanceGraphSemantics claudeAgentSDKProgram)
      graph :=
  extractPythonHookCore_decision_equivalent claudeAgentSDKProgram graph hextract

end Corpus
end PythonHookCore
end Legitimacy
