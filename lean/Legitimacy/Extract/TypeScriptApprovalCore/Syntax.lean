/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Types

/-!
# TypeScriptApprovalCore syntax

Restricted source core for TypeScript approval-surface extraction. The core
models typed approval unions, allow/block policy declarations, approval
handlers, async/failover handler shapes, and explicit/decorator registration
surfaces without binding to a full TypeScript AST.
-/

set_option autoImplicit false

namespace Legitimacy
namespace TypeScriptApprovalCore

/-- Canonical approval outcomes accepted by the restricted TypeScript core. -/
inductive ApprovalResult where
  | allow
  | deny
  | ask
  | escalate
  deriving DecidableEq, Repr

/-- Expression fragment for simple policy checks and handler returns. -/
inductive Expr where
  | bool : Bool → Expr
  | fieldEq : String → String → Expr
  | listMember : String → String → Expr
  | approval : ApprovalResult → Expr
  | handler : String → Expr
  deriving DecidableEq, Repr

/-- Statement fragment accepted by the theorem-backed extractor. -/
inductive Stmt where
  | returnApproval : ApprovalResult → Stmt
  | ifThenElse : Expr → Stmt → Stmt → Stmt
  | call : String → Stmt
  | awaitCall : String → Stmt
  | fallback : String → Stmt → Stmt
  | dead : Stmt → Stmt
  deriving DecidableEq, Repr

/-- Supported TypeScript policy declaration shapes. -/
inductive PolicyKind where
  | allowlist
  | blocklist
  deriving DecidableEq, Repr

/-- Typed approval result union declaration. -/
structure ApprovalUnionDecl where
  name : String
  literals : List String
  deriving DecidableEq, Repr

/-- Request/payload field declaration in the modeled source core. -/
structure RequestField where
  name : String
  typeName : String
  approvalPosition : Bool
  deriving DecidableEq, Repr

/-- Type/interface request declaration. -/
structure RequestDecl where
  name : String
  fields : List RequestField
  deriving DecidableEq, Repr

/-- Allowlist or blocklist policy declaration. -/
structure PolicyDecl where
  name : String
  kind : PolicyKind
  entries : List String
  deriving DecidableEq, Repr

/-- Approval handler body in the restricted core. -/
structure HandlerDecl where
  name : String
  isAsync : Bool
  body : Stmt
  fallbackHandlers : List String
  deriving DecidableEq, Repr

/-- Registration entry from an approval surface to a concrete handler. -/
structure Registration where
  surface : String
  handler : String
  viaDecorator : Bool
  deriving DecidableEq, Repr

/-- Complete restricted TypeScript approval program. -/
inductive Program where
  | mk :
      List ApprovalUnionDecl →
      List RequestDecl →
      List PolicyDecl →
      List HandlerDecl →
      List Registration →
      Program
  deriving DecidableEq, Repr

namespace Program

def approvalUnions : Program → List ApprovalUnionDecl
  | mk approvalUnions _ _ _ _ => approvalUnions

def requests : Program → List RequestDecl
  | mk _ requests _ _ _ => requests

def policies : Program → List PolicyDecl
  | mk _ _ policies _ _ => policies

def handlers : Program → List HandlerDecl
  | mk _ _ _ handlers _ => handlers

def registrations : Program → List Registration
  | mk _ _ _ _ registrations => registrations

end Program

end TypeScriptApprovalCore
end Legitimacy
