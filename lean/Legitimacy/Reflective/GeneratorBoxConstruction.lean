/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Legitimacy.Reflective.Depth2

/-!
# Generator boxed-atom construction probe

This module is the Path gamma probe for the depth-2 lattice. It tests the
single-generator `{0}` construction against the existing godel-loeb
`Provable` substrate.

The projection itself works: from the boxed lattice audit formula produced by
the depth-2 audit predicate at `{0}`, K plus necessitation project the boxed
singleton-generator atom. The probe also records the remaining premise
honestly: the current substrate does not construct the `{0}` audit certificate
from the abstract fixed-point agreement fields alone.
-/

set_option autoImplicit false

namespace Legitimacy
namespace Reflective
namespace ReflectiveGovernanceFixedPointSystem

open ModalLogic.GoedelLoeb
open ModalLogic.GoedelLoeb.ModalFormula

universe u

/-- The singleton generator `{0}` in the depth-2 powerset lattice. -/
def depth2GeneratorZeroState : Depth2State :=
  {(0 : Fin 4)}

/-- The depth-2 transition sends the `{0}` generator to the core fixed state. -/
theorem depth2Step_generator_zero :
    depth2Step depth2GeneratorZeroState = depth2Core := by
  ext i
  fin_cases i <;> simp [depth2Step, depth2StepSet, depth2GeneratorZeroState,
    depth2Core]

/-- Object-language conjunction projects to its left conjunct in `Provable`. -/
theorem provable_and_left {α : Type u} (phi psi : ModalFormula α) :
    Provable (ModalFormula.and phi psi ⟶ phi) := by
  refine Provable.of_prop_taut ?_
  intro val hand
  by_contra hphi
  exact False.elim (hand fun hphi' _hpsi => hphi hphi')

/-- K lifts a left-conjunct projection through the object-language box. -/
theorem provable_box_and_left {α : Type u} {phi psi : ModalFormula α}
    (hbox : Provable (□ₛ(ModalFormula.and phi psi))) :
    Provable (□ₛphi) :=
  Provable.mp (Provable.box_imp (provable_and_left phi psi)) hbox

/--
The core lattice audit formula propositionally implies the singleton `{0}`
audit atom.

This is the local content needed by the probe: the structural lattice encoder
really does put the `{0}` generator atom at the left edge of the depth-2 core
formula.
-/
theorem depth2Core_latticeAuditFormula_implies_generator_zero :
    Provable
      (depth2LatticeAuditFormulaAt depth2Core ⟶
        encodeAuditCertifies depth2GeneratorZeroState) := by
  simpa [depth2LatticeAuditFormulaAt, encodeAuditCertifiesLattice,
    encodeAuditCertifiesLatticeSupport, List.finRange, depth2Core,
    depth2GeneratorZeroState] using
      (provable_and_left (encodeAuditCertifies depth2GeneratorZeroState)
        (ModalFormula.and
          (encodeAuditCertifies ({(1 : Fin 4)} : Depth2State))
          (encodeAuditCertifies depth2Core)))

/--
If the depth-2 core lattice audit is already boxed, K projects the boxed `{0}`
generator atom.

This is the positive part of the Path gamma probe: no Kripke lift and no new
object-level postulate is needed for the per-generator projection once the
boxed lattice audit certificate is available.
-/
theorem depth2GeneratorZero_boxed_atom_of_core_lattice_box
    (hboxCore : Provable (□ₛ(depth2LatticeAuditFormulaAt depth2Core))) :
    Provable (□ₛ(encodeAuditCertifies depth2GeneratorZeroState)) :=
  Provable.mp
    (Provable.box_imp depth2Core_latticeAuditFormula_implies_generator_zero)
    hboxCore

/--
The lattice audit predicate at `{0}` is exactly a boxed audit of the core
lattice formula, because the transition installs the missing core generator
`1`.
-/
theorem depth2GeneratorZero_auditCertifies_iff_core_lattice_box :
    depth2ReflectiveSystemLattice.auditCertifies depth2GeneratorZeroState ↔
      Provable (□ₛ(depth2LatticeAuditFormulaAt depth2Core)) := by
  constructor
  · intro haudit
    simpa [depth2ReflectiveSystemLattice, depth2ReflectiveAuditCertifiesLattice,
      reflectiveBox, reflectiveBoxOf, modalAxiomaticReflectiveBox,
      depth2LatticeAuditFormulaAt, depth2Step_generator_zero] using haudit
  · intro hbox
    simpa [depth2ReflectiveSystemLattice, depth2ReflectiveAuditCertifiesLattice,
      reflectiveBox, reflectiveBoxOf, modalAxiomaticReflectiveBox,
      depth2LatticeAuditFormulaAt, depth2Step_generator_zero] using hbox

/--
Conditional single-generator boxed-atom construction for `{0}`.

This is as far as the current depth-2 substrate goes constructively. The
modal projection from the audit predicate to `Provable □encodeAuditCertifies`
lands, but the premise is still the modal audit certificate itself.
-/
theorem depth2GeneratorZero_boxed_atom_of_auditCertifies
    (haudit :
      depth2ReflectiveSystemLattice.auditCertifies depth2GeneratorZeroState) :
    Provable (□ₛ(encodeAuditCertifies depth2GeneratorZeroState)) :=
  depth2GeneratorZero_boxed_atom_of_core_lattice_box
    (depth2GeneratorZero_auditCertifies_iff_core_lattice_box.mp haudit)

end ReflectiveGovernanceFixedPointSystem
end Reflective
end Legitimacy
