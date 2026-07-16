/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.PythonHookCore.Soundness

/-!
# Claude Agent SDK PythonHookCore fixture

Lean binding for the Claude Agent SDK Python `types.py` PreToolUse hook-output
surface covered by theorem-backed extraction.
-/

set_option autoImplicit false

namespace Legitimacy
namespace PythonHookCore
namespace Fixtures

def claudeAgentSDKPreToolUseOutputSchema : SchemaDecl where
  name := "PreToolUseHookSpecificOutput"
  kind := .typedDict
  fields := [
    { name := "hookEventName", typeName := "Literal[PreToolUse]",
      typedDecision := false },
    { name := "permissionDecision",
      typeName := "NotRequired[Literal[allow, deny, ask]]",
      typedDecision := true },
    { name := "permissionDecisionReason", typeName := "NotRequired[str]",
      typedDecision := false },
    { name := "updatedInput", typeName := "NotRequired[dict[str, Any]]",
      typedDecision := false },
    { name := "additionalContext", typeName := "NotRequired[str]",
      typedDecision := false }
  ]

def claudeAgentSDKHookEventDispatch : DispatchEnum where
  name := "HookEvent"
  cases := [
    "PreToolUse", "PostToolUse", "PostToolUseFailure", "UserPromptSubmit",
    "Stop", "SubagentStop", "PreCompact", "Notification", "SubagentStart",
    "PermissionRequest"
  ]

def claudeAgentSDKPreToolUseDecisionCallback : CallbackDecl where
  name := "pre_tool_use_permission_decision"
  body :=
    .ifThenElse (.fieldEq "permissionDecision" "deny")
      (.returnDecision .deny)
      (.ifThenElse (.fieldEq "permissionDecision" "ask")
        (.returnDecision .ask)
        (.returnDecision .allow))

def claudeAgentSDKPreToolUseRegistration : Registration where
  hook := "PreToolUse"
  callback := "pre_tool_use_permission_decision"

def claudeAgentSDKPreToolUseProgram : Program :=
  .mk
    [claudeAgentSDKPreToolUseOutputSchema]
    [claudeAgentSDKHookEventDispatch]
    [claudeAgentSDKPreToolUseDecisionCallback]
    [claudeAgentSDKPreToolUseRegistration]

def claudeAgentSDKPreToolUseDenyClaim : ClaimQ :=
  ⟨0, 1, by norm_num, [("permissionDecision", "deny")]⟩

def claudeAgentSDKPreToolUseAskClaim : ClaimQ :=
  ⟨0, 1, by norm_num, [("permissionDecision", "ask")]⟩

def claudeAgentSDKPreToolUseAllowClaim : ClaimQ :=
  ⟨0, 1, by norm_num, [("permissionDecision", "allow")]⟩

theorem claudeAgentSDKPreToolUse_deny_metadata_fires :
    evalPythonHookCore claudeAgentSDKPreToolUseProgram
      [claudeAgentSDKPreToolUseDenyClaim] 0 = BinaryDecision.Deny := by
  native_decide

theorem claudeAgentSDKPreToolUse_ask_metadata_fires :
    evalPythonHookCore claudeAgentSDKPreToolUseProgram
      [claudeAgentSDKPreToolUseAskClaim] 0 = BinaryDecision.Deny := by
  native_decide

theorem claudeAgentSDKPreToolUse_allow_metadata_permits :
    evalPythonHookCore claudeAgentSDKPreToolUseProgram
      [claudeAgentSDKPreToolUseAllowClaim] 0 = BinaryDecision.Permit := by
  native_decide

lemma claude_agent_sdk_pre_tool_use_source_graph_equivalent
    (graph : GovernanceGraph)
    (hextract :
      extractPythonHookCore claudeAgentSDKPreToolUseProgram = .ok graph) :
    DecisionSystem.Equivalent
      (sourceGovernanceGraphSemantics claudeAgentSDKPreToolUseProgram)
      graph :=
  extractPythonHookCore_decision_equivalent
    claudeAgentSDKPreToolUseProgram graph hextract

lemma claude_agent_sdk_ask_maps_to_non_permit :
    HookResult.toDecision HookResult.ask = BinaryDecision.Deny := by
  rfl

end Fixtures
end PythonHookCore
end Legitimacy
