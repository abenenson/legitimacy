/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.RustHookCore.Soundness

/-!
# Codex RustHookCore fixture

Lean binding for the restricted RustHookCore `UserPromptSubmit` verdict surface
modeled from the codex-rs hook fixture.
-/

set_option autoImplicit false

namespace Legitimacy
namespace RustHookCore
namespace Fixtures

def codexHookResultEnum : DecisionEnumDecl where
  name := "HookResult"
  variants := ["Allow", "Deny", "Ask", "Block"]

def codexUserPromptSubmitHook : HookFnDecl where
  name := "on_UserPromptSubmit"
  event := "UserPromptSubmit"
  inputType := "HookInput"
  resultType := "HookResult"
  body :=
    .matchEvent
      [("UserPromptSubmit", .returnDecision .block)]
      (.returnDecision .allow)

def codexUserPromptSubmitRegistration : Registration where
  event := "UserPromptSubmit"
  callback := "on_UserPromptSubmit"
  kind := .macro

def codexUserPromptSubmitProgram : Program :=
  .mk
    [codexHookResultEnum]
    [codexUserPromptSubmitHook]
    [codexUserPromptSubmitRegistration]

lemma codex_user_prompt_submit_source_graph_equivalent
    (graph : GovernanceGraph)
    (hextract :
      extractRustHookCore codexUserPromptSubmitProgram = .ok graph) :
    DecisionSystem.Equivalent
      (sourceGovernanceGraphSemantics codexUserPromptSubmitProgram)
      graph :=
  extractRustHookCore_decision_equivalent
    codexUserPromptSubmitProgram graph hextract

lemma codex_user_prompt_submit_block_maps_to_deny :
    HookResult.toDecision HookResult.block = BinaryDecision.Deny := by
  rfl

end Fixtures
end RustHookCore
end Legitimacy
