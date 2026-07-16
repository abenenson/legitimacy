/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.TypeScriptApprovalCore.Semantics

/-!
# TypeScriptApprovalCore verified extractor

The extractor is fail-closed: it does not synthesize registration surfaces, and
every registered handler must resolve inside the modeled TypeScript core.
-/

set_option autoImplicit false

namespace Legitimacy
namespace TypeScriptApprovalCore

inductive ExtractError where
  | noFormalRegistration
  | missingHandler : String → ExtractError
  deriving DecidableEq, Repr

def handlerNode (handler : HandlerDecl) : GovernanceNodeFn :=
  fun profile subject => handler.body.evalDecision profile subject

def extractRegistrationNode
    (program : Program) (registration : Registration) :
    Except ExtractError GovernanceNodeFn :=
  match findHandler? program.handlers registration.handler with
  | some handler => .ok (handlerNode handler)
  | none => .error (.missingHandler registration.handler)

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

def extractTypeScriptApprovalCore (program : Program) :
    Except ExtractError GovernanceGraph :=
  match program.registrations with
  | [] => .error .noFormalRegistration
  | registrations => extractRegistrationNodes program registrations

end TypeScriptApprovalCore
end Legitimacy
