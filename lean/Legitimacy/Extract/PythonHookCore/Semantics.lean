/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.PythonHookCore.Syntax
import Legitimacy.Foundations.DecisionSystem

/-!
# PythonHookCore source semantics

Executable semantics for the restricted Python hook source core. `allow` is the
only local permit. `ask` requires higher-authority review; this binary Lean
model collapses that non-permit escalation outcome to `Deny`, while the Rust
graph extractor preserves it as `Decision::Escalate`.
-/

set_option autoImplicit false

namespace Legitimacy
namespace PythonHookCore

abbrev ClaimProfile := List ClaimQ
abbrev Decision := BinaryDecision

def HookResult.toDecision : HookResult → Decision
  | .allow => .Permit
  | .ask => .Deny
  | .deny => .Deny
  | .block => .Deny

def Expr.eval (expr : Expr) (profile : ClaimProfile) (subject : ClaimantId) : Bool :=
  match expr with
  | .bool value => value
  | .fieldEq field value =>
      (ClaimProfile.lookup profile subject field == some value : Bool)
  | .decision result => result.toDecision == BinaryDecision.Permit
  | .callback _name => true

def Stmt.evalHookResult
    (stmt : Stmt) (profile : ClaimProfile) (subject : ClaimantId) : HookResult :=
  match stmt with
  | .returnDecision result => result
  | .ifThenElse condition yes no =>
      if condition.eval profile subject then
        yes.evalHookResult profile subject
      else
        no.evalHookResult profile subject
  | .call _callback => .allow
  | .dead live => live.evalHookResult profile subject

def Stmt.evalDecision
    (stmt : Stmt) (profile : ClaimProfile) (subject : ClaimantId) : Decision :=
  (stmt.evalHookResult profile subject).toDecision

def findCallback? (callbacks : List CallbackDecl) (name : String) :
    Option CallbackDecl :=
  callbacks.find? (fun callback => callback.name == name)

def evalRegistration
    (program : Program) (registration : Registration)
    (profile : ClaimProfile) (subject : ClaimantId) : Decision :=
  match findCallback? program.callbacks registration.callback with
  | some callback => callback.body.evalDecision profile subject
  | none => BinaryDecision.Deny

def registrationNode (program : Program) (registration : Registration) :
    GovernanceNodeFn :=
  fun profile subject => evalRegistration program registration profile subject

def evalRegistrations
    (program : Program) (registrations : List Registration)
    (profile : ClaimProfile) (subject : ClaimantId) : Decision :=
  match registrations with
  | [] => BinaryDecision.Permit
  | registration :: rest =>
      match evalRegistration program registration profile subject with
      | BinaryDecision.Deny => BinaryDecision.Deny
      | BinaryDecision.Permit =>
          evalRegistrations program rest
            (filterPermitted (registrationNode program registration) profile)
            subject

def evalPythonHookCore
    (program : Program) (profile : ClaimProfile) (subject : ClaimantId) : Decision :=
  evalRegistrations program program.registrations profile subject

/-- Wrapper object carrying a PythonHookCore program as a decision system. -/
structure SourceGovernanceGraphSemantics where
  program : Program

def sourceGovernanceGraphSemantics (program : Program) :
    SourceGovernanceGraphSemantics :=
  ⟨program⟩

instance : DecisionSystem SourceGovernanceGraphSemantics ClaimProfile ClaimantId Decision where
  decide system := evalPythonHookCore system.program

end PythonHookCore
end Legitimacy
