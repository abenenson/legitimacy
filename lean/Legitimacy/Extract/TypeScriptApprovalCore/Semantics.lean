/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.TypeScriptApprovalCore.Syntax
import Legitimacy.Foundations.DecisionSystem

/-!
# TypeScriptApprovalCore source semantics

Executable semantics for the restricted TypeScript approval core. `allow` is
the only local permit. `ask` and `escalate` require higher-authority review;
this binary Lean model collapses those non-permit escalation outcomes to
`Deny`, while the Rust graph extractor preserves them as `Decision::Escalate`.
-/

set_option autoImplicit false

namespace Legitimacy
namespace TypeScriptApprovalCore

abbrev ClaimProfile := List ClaimQ
abbrev Decision := BinaryDecision

def ApprovalResult.toDecision : ApprovalResult → Decision
  | .allow => .Permit
  | .ask => .Deny
  | .escalate => .Deny
  | .deny => .Deny

def Expr.eval (expr : Expr) (profile : ClaimProfile) (subject : ClaimantId) : Bool :=
  match expr with
  | .bool value => value
  | .fieldEq field value =>
      (ClaimProfile.lookup profile subject field == some value : Bool)
  | .listMember _listName _field => false
  | .approval result => result.toDecision == BinaryDecision.Permit
  | .handler _name => true

def Stmt.evalApprovalResult
    (stmt : Stmt) (profile : ClaimProfile) (subject : ClaimantId) : ApprovalResult :=
  match stmt with
  | .returnApproval result => result
  | .ifThenElse condition yes no =>
      if condition.eval profile subject then
        yes.evalApprovalResult profile subject
      else
        no.evalApprovalResult profile subject
  | .call _handler => .allow
  | .awaitCall _handler => .allow
  | .fallback _handler rest =>
      match rest.evalApprovalResult profile subject with
      | .deny => .deny
      | .allow => .allow
      | .ask => .ask
      | .escalate => .escalate
  | .dead live => live.evalApprovalResult profile subject

def Stmt.evalDecision
    (stmt : Stmt) (profile : ClaimProfile) (subject : ClaimantId) : Decision :=
  (stmt.evalApprovalResult profile subject).toDecision

def findHandler? (handlers : List HandlerDecl) (name : String) :
    Option HandlerDecl :=
  handlers.find? (fun handler => handler.name == name)

def evalRegistration
    (program : Program) (registration : Registration)
    (profile : ClaimProfile) (subject : ClaimantId) : Decision :=
  match findHandler? program.handlers registration.handler with
  | some handler => handler.body.evalDecision profile subject
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

def evalTypeScriptApprovalCore
    (program : Program) (profile : ClaimProfile) (subject : ClaimantId) : Decision :=
  evalRegistrations program program.registrations profile subject

/-- Wrapper object carrying a TypeScriptApprovalCore program as a decision system. -/
structure SourceGovernanceGraphSemantics where
  program : Program

def sourceGovernanceGraphSemantics (program : Program) :
    SourceGovernanceGraphSemantics :=
  ⟨program⟩

instance : DecisionSystem SourceGovernanceGraphSemantics ClaimProfile ClaimantId Decision where
  decide system := evalTypeScriptApprovalCore system.program

end TypeScriptApprovalCore
end Legitimacy
