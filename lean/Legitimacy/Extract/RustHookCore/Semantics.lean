/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.RustHookCore.Syntax
import Legitimacy.Foundations.DecisionSystem

/-!
# RustHookCore source semantics

Executable semantics for the restricted Rust hook source core. `allow` and
`ask` are forwarding outcomes; `deny` and `block` are terminal denials in the
binary governance pipeline.
-/

set_option autoImplicit false

namespace Legitimacy
namespace RustHookCore

abbrev ClaimProfile := List ClaimQ
abbrev Decision := BinaryDecision

def HookResult.toDecision : HookResult → Decision
  | .allow => .Permit
  | .ask => .Permit
  | .deny => .Deny
  | .block => .Deny

def Expr.eval (expr : Expr) (profile : ClaimProfile) (subject : ClaimantId) : Bool :=
  match expr with
  | .bool value => value
  | .eventEq _event => false
  | .fieldEq field value =>
      (ClaimProfile.lookup profile subject field == some value : Bool)
  | .decision result => result.toDecision == BinaryDecision.Permit
  | .callback _name => true

def structuralFieldEqWitnessProfile : ClaimProfile :=
  [⟨0, 1, by norm_num, [("arbitraryField", "arbitraryValue")]⟩]

theorem structural_fieldEq_differs_from_dead_letter_false :
    Expr.eval (.fieldEq "arbitraryField" "arbitraryValue")
      structuralFieldEqWitnessProfile 0 = true := by
  native_decide

def Stmt.directHookResult? : Stmt → Option HookResult
  | .returnDecision result => some result
  | .dead live => live.directHookResult?
  | _ => none

def evalMatchArms
    (event : String) (arms : List (String × Stmt)) : Option HookResult :=
  match arms with
  | [] => none
  | arm :: rest =>
      if arm.1 == event then
        arm.2.directHookResult?
      else
        evalMatchArms event rest

def Stmt.evalHookResult
    (event : String) (stmt : Stmt) (profile : ClaimProfile) (subject : ClaimantId) :
    HookResult :=
  match stmt with
  | .returnDecision result => result
  | .matchEvent arms default =>
      match evalMatchArms event arms with
      | some result => result
      | none => default.evalHookResult event profile subject
  | .ifThenElse condition yes no =>
      if condition.eval profile subject then
        yes.evalHookResult event profile subject
      else
        no.evalHookResult event profile subject
  | .call _callback => .allow
  | .dead live => live.evalHookResult event profile subject

def Stmt.evalDecision
    (event : String) (stmt : Stmt) (profile : ClaimProfile) (subject : ClaimantId) :
    Decision :=
  (stmt.evalHookResult event profile subject).toDecision

def findHook? (hooks : List HookFnDecl) (name : String) : Option HookFnDecl :=
  hooks.find? (fun hook => hook.name == name)

def evalRegistration
    (program : Program) (registration : Registration)
    (profile : ClaimProfile) (subject : ClaimantId) : Decision :=
  match findHook? program.hooks registration.callback with
  | some hook => hook.body.evalDecision registration.event profile subject
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

def evalRustHookCore
    (program : Program) (profile : ClaimProfile) (subject : ClaimantId) : Decision :=
  evalRegistrations program program.registrations profile subject

/-- Wrapper object carrying a RustHookCore program as a decision system. -/
structure SourceGovernanceGraphSemantics where
  program : Program

def sourceGovernanceGraphSemantics (program : Program) :
    SourceGovernanceGraphSemantics :=
  ⟨program⟩

instance : DecisionSystem SourceGovernanceGraphSemantics ClaimProfile ClaimantId Decision where
  decide system := evalRustHookCore system.program

end RustHookCore
end Legitimacy
