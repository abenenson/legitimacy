/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Types

/-!
# RustHookCore syntax

Restricted source core for Rust hook extraction. The core keeps only hook
result enum declarations, direct hook functions, event dispatch via `match`,
direct decision returns, callback calls, and formal macro/attribute
registrations. Unsupported Rust constructs remain outside this modeled
language and are refused by the Rust parser before theorem-backed extraction.
-/

set_option autoImplicit false

namespace Legitimacy
namespace RustHookCore

/-- Literal hook outcomes accepted in typed Rust hook decision positions. -/
inductive HookResult where
  | allow
  | deny
  | ask
  | block
  deriving DecidableEq, Repr

/-- Expression fragment for simple hook matches and returns. -/
inductive Expr where
  | bool : Bool → Expr
  | eventEq : String → Expr
  | fieldEq : String → String → Expr
  | decision : HookResult → Expr
  | callback : String → Expr
  deriving DecidableEq, Repr

/-- Statement fragment accepted by the theorem-backed Rust extractor. -/
inductive Stmt where
  | returnDecision : HookResult → Stmt
  | matchEvent : List (String × Stmt) → Stmt → Stmt
  | ifThenElse : Expr → Stmt → Stmt → Stmt
  | call : String → Stmt
  | dead : Stmt → Stmt

noncomputable instance : DecidableEq Stmt := Classical.decEq Stmt

instance : Repr Stmt where
  reprPrec _ _ := "Stmt"

/-- Supported hook registration mechanisms. -/
inductive RegistrationKind where
  | inventory
  | linkme
  | macro
  deriving DecidableEq, Repr

/-- `enum HookResult { Allow, Deny, Ask, Block }`-style declaration. -/
structure DecisionEnumDecl where
  name : String
  variants : List String
  deriving DecidableEq, Repr

/-- Hook function declaration in the restricted Rust core. -/
structure HookFnDecl where
  name : String
  event : String
  inputType : String
  resultType : String
  body : Stmt
  deriving Repr

noncomputable instance : DecidableEq HookFnDecl := Classical.decEq HookFnDecl

/-- Formal hook registration entry. -/
structure Registration where
  event : String
  callback : String
  kind : RegistrationKind
  deriving DecidableEq, Repr

/-- Complete restricted Rust hook program. -/
inductive Program where
  | mk :
      List DecisionEnumDecl →
      List HookFnDecl →
      List Registration →
      Program
  deriving Repr

noncomputable instance : DecidableEq Program := Classical.decEq Program

namespace Program

def decisionEnums : Program → List DecisionEnumDecl
  | mk decisionEnums _ _ => decisionEnums

def hooks : Program → List HookFnDecl
  | mk _ hooks _ => hooks

def registrations : Program → List Registration
  | mk _ _ registrations => registrations

end Program

end RustHookCore
end Legitimacy
