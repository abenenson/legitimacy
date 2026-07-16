/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Data.Fin.Basic
import GodelLoeb
import Legitimacy.Reflective.PolicyAtom

/-!
# Reflective modal encoding

The encoder is intentionally per-predicate. Phase B does not claim a canonical
translation from arbitrary `State → Prop` predicates into modal syntax.
-/

namespace Legitimacy
namespace Reflective

open ModalLogic.GoedelLoeb

universe u

/-- Encode the agent-action predicate at a specific state. -/
def encodeAgentActs {State : Type u} (s : State) :
    ModalFormula (PolicyAtom State) :=
  ModalFormula.atom (PolicyAtom.agentActs s)

/-- Encode the external-audit predicate at a specific state. -/
def encodeAuditCertifies {State : Type u} (s : State) :
    ModalFormula (PolicyAtom State) :=
  ModalFormula.atom (PolicyAtom.auditCertifies s)

/--
Encode audit certification over a finite powerset-lattice support.

The base atom still names the whole state, while the folded conjuncts name the
singleton generators that are present in the state. This is the additive Phase C
structural variant: modal syntax now changes with the state's lattice support,
not only with an opaque atom payload.
-/
noncomputable def encodeAuditCertifiesLatticeSupport {ι : Type u} [DecidableEq ι]
    (support : List ι) (s : Set ι) : ModalFormula (PolicyAtom (Set ι)) := by
  classical
  exact support.foldr
    (fun i tail =>
      if i ∈ s then
        ModalFormula.and (encodeAuditCertifies ({i} : Set ι)) tail
      else
        tail)
    (encodeAuditCertifies s)

/--
Finite powerset-lattice audit encoder.

For `Set (Fin n)` states, the structural support is the canonical list of
singleton lattice generators. Existing Phase B code continues to use
`encodeAuditCertifies`; this variant is for consumers that need audit modal
content to inspect lattice shape.
-/
noncomputable def encodeAuditCertifiesLattice {n : Nat}
    (s : Set (Fin n)) : ModalFormula (PolicyAtom (Set (Fin n))) :=
  encodeAuditCertifiesLatticeSupport (List.finRange n) s

/-- Encode the self-model agreement predicate at a specific state. -/
def encodeSelfModelAgrees {State : Type u} (s : State) :
    ModalFormula (PolicyAtom State) :=
  ModalFormula.atom (PolicyAtom.selfModelAgrees s)

/--
Kripke valuation bridge for the three policy atoms.

The world parameter is intentionally separate from the state carried by the
atom. Current Phase B atoms carry their own state context, so the valuation
ignores the world when reducing an atom to a governance predicate.
-/
def policyValuation {State : Type u}
    (agentActs auditCertifies selfModelAgrees : State → Prop) :
    PolicyAtom State → State → Prop
  | PolicyAtom.agentActs t, _ => agentActs t
  | PolicyAtom.auditCertifies t, _ => auditCertifies t
  | PolicyAtom.selfModelAgrees t, _ => selfModelAgrees t

/-- The canonical godel-loeb diagonal interface for policy atoms. -/
instance policyAtomDiagonalisable {State : Type u} [DecidableEq State] [Inhabited State] :
    Diagonalisable (PolicyAtom State) :=
  inferInstance

end Reflective
end Legitimacy
