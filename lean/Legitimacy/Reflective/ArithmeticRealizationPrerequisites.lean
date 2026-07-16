/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.Arithmetic.Presburger.Basic
import Mathlib.ModelTheory.Complexity
import Legitimacy.Reflective.BoxedSoundnessRealization

/-!
# Current-target reflection prerequisites

This module isolates the narrow reflection shape that the current boxed
internal-soundness target can actually rule out.

## Main results

* `depth2Core_latticeAuditFormula_contains_core_atom` and
  `depth2Core_latticeAuditFormula_contains_singleton_zero_atom`: the concrete
  audit formula still contains opaque Lean state-indexed policy atoms, so an
  arithmetic realization needs a nontrivial atom-to-first-order-sentence layer.
-/

set_option autoImplicit false

namespace Legitimacy
namespace Reflective
namespace ReflectiveGovernanceFixedPointSystem

open FirstOrder
open ModalLogic.GoedelLoeb

universe u

/-- Syntactic occurrence of an atom inside a modal formula. -/
def modalFormulaContainsAtom {α : Type u} (needle : α) : ModalFormula α → Prop
  | @ModalFormula.atom _ atom => atom = needle
  | @ModalFormula.bot _ => False
  | @ModalFormula.impl _ phi psi =>
      modalFormulaContainsAtom needle phi ∨ modalFormulaContainsAtom needle psi
  | @ModalFormula.iff _ phi psi =>
      modalFormulaContainsAtom needle phi ∨ modalFormulaContainsAtom needle psi
  | @ModalFormula.box _ phi => modalFormulaContainsAtom needle phi
  | @ModalFormula.quote _ phi => modalFormulaContainsAtom needle phi
  | @ModalFormula.kreiselFixed _ phi => modalFormulaContainsAtom needle phi

@[simp]
theorem modalFormulaContainsAtom_atom_self {α : Type u} (atom : α) :
    modalFormulaContainsAtom atom (ModalFormula.atom atom) := by
  rfl

@[simp]
theorem modalFormulaContainsAtom_impl_left {α : Type u} {needle : α}
    {phi psi : ModalFormula α} (h : modalFormulaContainsAtom needle phi) :
    modalFormulaContainsAtom needle (phi ⟶ psi) :=
  Or.inl h

@[simp]
theorem modalFormulaContainsAtom_impl_right {α : Type u} {needle : α}
    {phi psi : ModalFormula α} (h : modalFormulaContainsAtom needle psi) :
    modalFormulaContainsAtom needle (phi ⟶ psi) :=
  Or.inr h

@[simp]
theorem modalFormulaContainsAtom_box {α : Type u} {needle : α} {phi : ModalFormula α}
    (h : modalFormulaContainsAtom needle phi) :
    modalFormulaContainsAtom needle (□ₛphi) :=
  h

/--
Mathlib currently supplies first-order sentence syntax for ring-language
arithmetic, but this is only syntax: it is not a PA theory or a PA provability
predicate.
-/
abbrev RingArithmeticSentence : Type :=
  FirstOrder.Language.ring.Sentence

/--
Mathlib currently supplies Presburger-language sentence syntax. Presburger
arithmetic is too weak for Solovay realization because it omits multiplication,
and the pinned Mathlib also does not define a PA provability predicate here.
-/
abbrev PresburgerArithmeticSentence : Type :=
  FirstOrder.Language.presburger.Sentence

/-- The concrete depth-2 audit formula contains its state-level core audit atom. -/
theorem depth2Core_latticeAuditFormula_contains_core_atom :
    modalFormulaContainsAtom (PolicyAtom.auditCertifies depth2Core)
      (depth2LatticeAuditFormulaAt depth2Core) := by
  change modalFormulaContainsAtom (PolicyAtom.auditCertifies depth2Core)
    (encodeAuditCertifiesLattice depth2Core)
  simp [encodeAuditCertifiesLattice, encodeAuditCertifiesLatticeSupport, List.finRange,
    depth2Core, encodeAuditCertifies, modalFormulaContainsAtom, ModalFormula.and,
    ModalFormula.neg]

/--
The concrete depth-2 audit formula also contains singleton-generator atoms.
These are governance atoms, not first-order arithmetic sentences, until an
explicit atom interpretation is supplied.
-/
theorem depth2Core_latticeAuditFormula_contains_singleton_zero_atom :
    modalFormulaContainsAtom
      (PolicyAtom.auditCertifies ({(0 : Fin 4)} : Depth2State))
      (depth2LatticeAuditFormulaAt depth2Core) := by
  change modalFormulaContainsAtom
    (PolicyAtom.auditCertifies ({(0 : Fin 4)} : Depth2State))
    (encodeAuditCertifiesLattice depth2Core)
  simp [encodeAuditCertifiesLattice, encodeAuditCertifiesLatticeSupport, List.finRange,
    depth2Core, encodeAuditCertifies, modalFormulaContainsAtom, ModalFormula.and,
    ModalFormula.neg]

end ReflectiveGovernanceFixedPointSystem
end Reflective
end Legitimacy
