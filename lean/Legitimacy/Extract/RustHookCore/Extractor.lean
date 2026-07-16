/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.RustHookCore.Semantics

/-!
# RustHookCore verified extractor

The extractor is intentionally fail-closed: no formal Rust hook registration is
invented, and every registered hook callback must resolve inside the restricted
modeled source core.
-/

set_option autoImplicit false

namespace Legitimacy
namespace RustHookCore

inductive ExtractError where
  | noFormalRegistration
  | missingHook : String → ExtractError
  deriving DecidableEq, Repr

def hookNode (event : String) (hook : HookFnDecl) : GovernanceNodeFn :=
  fun profile subject => hook.body.evalDecision event profile subject

def extractRegistrationNode
    (program : Program) (registration : Registration) :
    Except ExtractError GovernanceNodeFn :=
  match findHook? program.hooks registration.callback with
  | some hook => .ok (hookNode registration.event hook)
  | none => .error (.missingHook registration.callback)

def extractRegistrationNodes
    (program : Program) : List Registration → Except ExtractError GovernanceGraph
  | [] => .ok []
  | registration :: rest =>
      match extractRegistrationNode program registration with
      | .error error => .error error
      | .ok node =>
          match extractRegistrationNodes program rest with
          | .error error => .error error
          | .ok nodes => .ok (node :: nodes)

def extractRustHookCore (program : Program) :
    Except ExtractError GovernanceGraph :=
  match program.registrations with
  | [] => .error .noFormalRegistration
  | registrations => extractRegistrationNodes program registrations

end RustHookCore
end Legitimacy
