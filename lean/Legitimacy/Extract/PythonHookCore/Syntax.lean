/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Types

/-!
# PythonHookCore syntax

Restricted source core for Python hook extraction. The core deliberately keeps
only typed decision positions, schema declarations, dispatch declarations,
registration tables, simple conditional returns, and direct callback edges.
-/

set_option autoImplicit false

namespace Legitimacy
namespace PythonHookCore

/-- Literal hook outcomes accepted in typed decision positions. -/
inductive HookResult where
  | allow
  | deny
  | ask
  | block
  deriving DecidableEq, Repr

/-- Expression fragment for simple hook conditions and returns. -/
inductive Expr where
  | bool : Bool → Expr
  | fieldEq : String → String → Expr
  | decision : HookResult → Expr
  | callback : String → Expr
  deriving DecidableEq, Repr

/-- Statement fragment accepted by the theorem-backed extractor. -/
inductive Stmt where
  | returnDecision : HookResult → Stmt
  | ifThenElse : Expr → Stmt → Stmt → Stmt
  | call : String → Stmt
  | dead : Stmt → Stmt
  deriving DecidableEq, Repr

/-- Supported Python schema declaration shapes. -/
inductive SchemaKind where
  | dataclass
  | typedDict
  | pydanticLike
  deriving DecidableEq, Repr

/-- A typed schema field. `typedDecision = true` marks decision positions. -/
structure SchemaField where
  name : String
  typeName : String
  typedDecision : Bool
  deriving DecidableEq, Repr

/-- Dataclass, TypedDict, or Pydantic-like schema declaration. -/
structure SchemaDecl where
  name : String
  kind : SchemaKind
  fields : List SchemaField
  deriving DecidableEq, Repr

/-- Hook dispatch enum declaration. -/
structure DispatchEnum where
  name : String
  cases : List String
  deriving DecidableEq, Repr

/-- Callback body in the restricted core. -/
structure CallbackDecl where
  name : String
  body : Stmt
  deriving DecidableEq, Repr

/-- Formal hook registration entry: hook kind wired to a callback. -/
structure Registration where
  hook : String
  callback : String
  deriving DecidableEq, Repr

/-- Complete restricted Python hook program. -/
inductive Program where
  | mk :
      List SchemaDecl →
      List DispatchEnum →
      List CallbackDecl →
      List Registration →
      Program
  deriving DecidableEq, Repr

namespace Program

def schemas : Program → List SchemaDecl
  | mk schemas _ _ _ => schemas

def dispatchEnums : Program → List DispatchEnum
  | mk _ dispatchEnums _ _ => dispatchEnums

def callbacks : Program → List CallbackDecl
  | mk _ _ callbacks _ => callbacks

def registrations : Program → List Registration
  | mk _ _ _ registrations => registrations

end Program

end PythonHookCore
end Legitimacy
