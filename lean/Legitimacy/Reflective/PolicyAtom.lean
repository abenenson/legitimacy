/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# Reflective policy atoms

Atomic propositions for the Phase B reflective-governance modal encoding.
Each atom carries the governance state it speaks about; there is no general
encoder from arbitrary state predicates to modal syntax.
-/

namespace Legitimacy
namespace Reflective

universe u

/-- The three load-bearing reflective-governance predicates as modal atoms. -/
inductive PolicyAtom (State : Type u) : Type u where
  | agentActs : State → PolicyAtom State
  | auditCertifies : State → PolicyAtom State
  | selfModelAgrees : State → PolicyAtom State
  deriving DecidableEq

instance {State : Type u} [Inhabited State] : Inhabited (PolicyAtom State) :=
  ⟨PolicyAtom.agentActs default⟩

end Reflective
end Legitimacy
