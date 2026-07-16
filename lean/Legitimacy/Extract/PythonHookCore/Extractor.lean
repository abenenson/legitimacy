/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.PythonHookCore.Semantics

/-!
# PythonHookCore verified extractor

The extractor is intentionally fail-closed: no registration table means no
synthetic hook registration is invented, and every registered callback must
resolve inside the restricted core.
-/

set_option autoImplicit false

namespace Legitimacy
namespace PythonHookCore

inductive ExtractError where
  | noFormalRegistration
  | missingCallback : String → ExtractError
  deriving DecidableEq, Repr

def callbackNode (callback : CallbackDecl) : GovernanceNodeFn :=
  fun profile subject => callback.body.evalDecision profile subject

def extractRegistrationNode
    (program : Program) (registration : Registration) :
    Except ExtractError GovernanceNodeFn :=
  match findCallback? program.callbacks registration.callback with
  | some callback => .ok (callbackNode callback)
  | none => .error (.missingCallback registration.callback)

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

def extractPythonHookCore (program : Program) :
    Except ExtractError GovernanceGraph :=
  match program.registrations with
  | [] => .error .noFormalRegistration
  | registrations => extractRegistrationNodes program registrations

end PythonHookCore
end Legitimacy
