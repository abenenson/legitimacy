/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Legitimacy.Reflective.CriticalCapabilityComposition

/-!
# Boxed internal-soundness realization

This module records the realization probe against the boxed internal-soundness
premise used by the reflective substrate.

## Main result

* `depth2Core_lattice_hinternal_countermodel`: a concrete transitive Kripke
  countermodel where the boxed internal-soundness formula for
  `depth2Core` fails.
* `depth2BoxedSoundness_propTautSound_refuted`: the concrete frame and
  valuation do not satisfy godel-loeb's `PropTautSound` bridge.
* `depth2Core_lattice_hinternal_refuted_if_propTautSound`: the countermodel
  refutes any attempt to obtain the premise from the exported K4 soundness
  bridge under the exact `PropTautSound` precondition required by godel-loeb.
* `propTautSound_forces_every_box`: any frame satisfying the exported
  `PropTautSound` bridge forces all boxed formulas vacuously.
* `no_currentTargetReflection_if_propTautSound`: the reduced current-target
  reflection package is impossible under the boxed-soundness bridge.
-/

set_option autoImplicit false

namespace Legitimacy
namespace Reflective
namespace ReflectiveGovernanceFixedPointSystem

open ModalLogic.GoedelLoeb
open ModalLogic.GoedelLoeb.ModalFormula

universe u

/-- Two-world K4 frame used for the boxed internal-soundness realization countermodel. World `0`
sees world `1`; world `1` sees no worlds. -/
def depth2BoxedSoundnessFrame : KripkeFrame where
  World := Fin 2
  accessible w v := w = 0 ∧ v = 1

/-- The countermodel frame is transitive, hence a K4 frame. -/
theorem depth2BoxedSoundnessFrame_transitive :
    ∀ w₁ w₂ w₃ : depth2BoxedSoundnessFrame.World,
      depth2BoxedSoundnessFrame.accessible w₁ w₂ →
        depth2BoxedSoundnessFrame.accessible w₂ w₃ →
          depth2BoxedSoundnessFrame.accessible w₁ w₃ := by
  intro w₁ w₂ w₃ h₁₂ h₂₃
  exact False.elim (by
    have h₂_zero : w₂ = (0 : Fin 2) := h₂₃.1
    have h₂_one : w₂ = (1 : Fin 2) := h₁₂.2
    exact Fin.zero_ne_one (h₂_zero.symm.trans h₂_one))

/-- The countermodel frame is irreflexive, so it has the standard finite GL-frame shape. -/
theorem depth2BoxedSoundnessFrame_irreflexive :
    ∀ w : depth2BoxedSoundnessFrame.World,
      ¬ depth2BoxedSoundnessFrame.accessible w w := by
  intro w h
  have hzero : w = (0 : Fin 2) := h.1
  have hone : w = (1 : Fin 2) := h.2
  exact Fin.zero_ne_one (hzero.symm.trans hone)

/-- Countermodel valuation: no policy atom holds at either world. -/
def depth2BoxedSoundnessValuation :
    PolicyAtom Depth2State → depth2BoxedSoundnessFrame.World → Prop :=
  fun _atom _world => False

/-- Atom used to expose that `PropTautSound` is not inhabited on the countermodel. -/
def depth2BoxedSoundnessPropTautCounterexampleAtom : PolicyAtom Depth2State :=
  PolicyAtom.auditCertifies depth2Core

/--
A propositional-tautology formula that is not forced at the root of the
two-world boxed-soundness countermodel.

The formula is `□K(a) ∨ K(a)`, where `K` is the godel-loeb `kreiselFixed`
constructor. In the propositional evaluator this is tautological because it
has shape `p ∨ (p → q)`. In the non-reflexive countermodel both disjuncts fail
at the root for the all-false atom valuation.
-/
def depth2BoxedSoundnessPropTautCounterexample :
    ModalFormula (PolicyAtom Depth2State) :=
  ModalFormula.or
    (□ₛ(ModalFormula.kreiselFixed
      (ModalFormula.atom depth2BoxedSoundnessPropTautCounterexampleAtom)))
    (ModalFormula.kreiselFixed
      (ModalFormula.atom depth2BoxedSoundnessPropTautCounterexampleAtom))

/-- The boxed-soundness bridge counterexample is a godel-loeb `PropTaut`. -/
theorem depth2BoxedSoundness_propTautCounterexample_taut :
    depth2BoxedSoundnessPropTautCounterexample.PropTaut := by
  intro val
  simp only [depth2BoxedSoundnessPropTautCounterexample, ModalFormula.or,
    ModalFormula.neg, ModalFormula.propEval]
  intro hnot hp
  exact False.elim (hnot hp)

/-- The boxed-soundness bridge counterexample is not forced at the root world. -/
theorem depth2BoxedSoundness_propTautCounterexample_not_forced_at_root :
    ¬ KripkeFrame.Forces (F := depth2BoxedSoundnessFrame) depth2BoxedSoundnessValuation
      (0 : Fin 2) depth2BoxedSoundnessPropTautCounterexample := by
  simp only [depth2BoxedSoundnessPropTautCounterexample, ModalFormula.or,
    ModalFormula.neg, KripkeFrame.Forces, depth2BoxedSoundnessValuation]
  intro h
  exact h (fun hbox => hbox (1 : Fin 2) ⟨rfl, rfl⟩)

/--
The concrete two-world countermodel does not satisfy godel-loeb's
`PropTautSound` bridge.

This blocks the previously proposed route of discharging the bridge for this
frame: the bridge is formally refutable, not merely missing.
-/
theorem depth2BoxedSoundness_propTautSound_refuted :
    ¬ KripkeFrame.PropTautSound
      (F := depth2BoxedSoundnessFrame) depth2BoxedSoundnessValuation := by
  intro hSound
  exact depth2BoxedSoundness_propTautCounterexample_not_forced_at_root
    (hSound depth2BoxedSoundness_propTautCounterexample_taut)

/--
Kreisel-bottom tautology used to expose the strength of `PropTautSound`.

Propositionally it is `p ∨ ¬p`, with `p` the boxed Kreisel-bottom sentence.
Kripke-semantically it becomes `□⊥ ∨ ⊥`, so any `PropTautSound` valuation can
only live on frames with no accessible successors.
-/
def kreiselBottomAccessibilityTautology (α : Type u) : ModalFormula α :=
  ModalFormula.or (□ₛ(ModalFormula.kreiselFixed (⊥ₛ : ModalFormula α)))
    (ModalFormula.kreiselFixed (⊥ₛ : ModalFormula α))

/-- `kreiselBottomAccessibilityTautology` is propositionally tautological. -/
theorem kreiselBottomAccessibilityTautology_propTaut (α : Type u) :
    (kreiselBottomAccessibilityTautology α).PropTaut := by
  intro val
  simp [kreiselBottomAccessibilityTautology, ModalFormula.or, ModalFormula.neg,
    ModalFormula.propEval]

/--
The `PropTautSound` bridge forces every accessibility relation to be empty.

This is the formal obstruction to the tempting boxed-target countermodel route:
any frame/valuation pair satisfying the bridge validates every boxed formula
vacuously.
-/
theorem no_accessible_of_propTautSound {α : Type u} {F : KripkeFrame}
    {val : α → F.World → Prop}
    (hProp : KripkeFrame.PropTautSound (F := F) val)
    (w v : F.World) :
    ¬ F.accessible w v := by
  intro hacc
  have hforced :
      KripkeFrame.Forces (F := F) val w (kreiselBottomAccessibilityTautology α) :=
    hProp (kreiselBottomAccessibilityTautology_propTaut α)
  simp [kreiselBottomAccessibilityTautology, ModalFormula.or, ModalFormula.neg,
    KripkeFrame.Forces] at hforced
  exact hforced v hacc

/-- Under `PropTautSound`, every boxed formula is forced at every world. -/
theorem propTautSound_forces_every_box {α : Type u} {F : KripkeFrame}
    {val : α → F.World → Prop}
    (hProp : KripkeFrame.PropTautSound (F := F) val)
    (w : F.World) (phi : ModalFormula α) :
    KripkeFrame.Forces (F := F) val w (□ₛphi) := by
  intro v hacc
  exact False.elim (no_accessible_of_propTautSound hProp w v hacc)

/--
No `PropTautSound`-compatible Kripke countermodel can refute the boxed depth-2
internal-soundness target.
-/
theorem propTautSound_forces_depth2Core_lattice_hinternal {F : KripkeFrame}
    {val : PolicyAtom Depth2State → F.World → Prop}
    (hProp : KripkeFrame.PropTautSound (F := F) val)
    (w : F.World) :
    KripkeFrame.Forces (F := F) val w
      (□ₛ(depth2LatticeAuditSoundFormulaAt depth2Core)) :=
  propTautSound_forces_every_box hProp w
    (depth2LatticeAuditSoundFormulaAt depth2Core)

/-- The dead-end world has no successors. -/
theorem depth2BoxedSoundnessFrame_deadEnd_no_successor
    (v : depth2BoxedSoundnessFrame.World) :
    ¬ depth2BoxedSoundnessFrame.accessible (1 : Fin 2) v := by
  intro h
  have hzero : (1 : Fin 2) = 0 := h.1
  exact (by decide : (1 : Fin 2) ≠ 0) hzero

/-- At the dead-end world, every boxed formula is vacuously forced. -/
theorem depth2BoxedSoundnessFrame_deadEnd_forces_box
    (phi : ModalFormula (PolicyAtom Depth2State)) :
    KripkeFrame.Forces (F := depth2BoxedSoundnessFrame) depth2BoxedSoundnessValuation
      (1 : Fin 2) (□ₛphi) := by
  intro v hacc
  exact False.elim (depth2BoxedSoundnessFrame_deadEnd_no_successor v hacc)

/-- The structural audit formula for `depth2Core` is false at the dead-end
world under the countermodel valuation. -/
theorem depth2Core_lattice_audit_fails_at_deadEnd :
    ¬ KripkeFrame.Forces (F := depth2BoxedSoundnessFrame) depth2BoxedSoundnessValuation
      (1 : Fin 2) (depth2LatticeAuditFormulaAt depth2Core) := by
  change ¬ KripkeFrame.Forces (F := depth2BoxedSoundnessFrame) depth2BoxedSoundnessValuation
    (1 : Fin 2) (encodeAuditCertifiesLattice depth2Core)
  simp [encodeAuditCertifiesLattice, encodeAuditCertifiesLatticeSupport,
    List.finRange, depth2Core, encodeAuditCertifies, depth2BoxedSoundnessValuation,
    ModalFormula.and, ModalFormula.neg, KripkeFrame.Forces]

/-- The unboxed internal-soundness formula fails at the dead-end world:
`□A` is vacuous there while `A` is false. -/
theorem depth2Core_lattice_sound_formula_fails_at_deadEnd :
    ¬ KripkeFrame.Forces (F := depth2BoxedSoundnessFrame) depth2BoxedSoundnessValuation
      (1 : Fin 2) (depth2LatticeAuditSoundFormulaAt depth2Core) := by
  intro hsound
  exact depth2Core_lattice_audit_fails_at_deadEnd
    (hsound (depth2BoxedSoundnessFrame_deadEnd_forces_box
      (depth2LatticeAuditFormulaAt depth2Core)))

/-- Concrete Kripke countermodel for the boxed internal-soundness premise at
the depth-2 core. -/
theorem depth2Core_lattice_hinternal_countermodel :
    ¬ KripkeFrame.Forces (F := depth2BoxedSoundnessFrame) depth2BoxedSoundnessValuation
      (0 : Fin 2) (□ₛ(depth2LatticeAuditSoundFormulaAt depth2Core)) := by
  intro hbox
  exact depth2Core_lattice_sound_formula_fails_at_deadEnd
    (hbox (1 : Fin 2) ⟨rfl, rfl⟩)

/--
The countermodel refutes any derivation of the concrete `hinternal` premise
that is justified by godel-loeb's exported K4 soundness theorem.

The `PropTautSound` hypothesis is not smuggled: it is exactly the extra
precondition required by `KripkeFrame.provable_forces` because the modal
substrate includes the `kreiselFixed` propositional-tautology primitive.
-/
theorem depth2Core_lattice_hinternal_refuted_if_propTautSound
    (hProp :
      KripkeFrame.PropTautSound (F := depth2BoxedSoundnessFrame) depth2BoxedSoundnessValuation) :
    ¬ reflectiveBox (depth2LatticeAuditSoundFormulaAt depth2Core) := by
  intro hprov
  exact depth2Core_lattice_hinternal_countermodel
    (KripkeFrame.provable_forces depth2BoxedSoundnessFrame_transitive hProp hprov (0 : Fin 2))

/--
Minimal data for the specific current-target reflection shape ruled out by the
boxed-soundness countermodel.

This is deliberately not named as an arithmetic realization. The theorem below
only consumes a source proposition, a witness of it, and a bridge from that
witness to the current godel-loeb `reflectiveBox` premise.
-/
structure Depth2CurrentTargetReflection where
  /-- Source proposition whose witness is intended to justify the boxed premise. -/
  SourceProof : Prop
  /-- A concrete witness of the source proposition. -/
  sourceProof : SourceProof
  /--
  Bridge from the source proof back to the existing godel-loeb premise consumed
  by downstream reflective theorems.
  -/
  reflectsSourceProof :
    SourceProof →
      reflectiveBox (depth2LatticeAuditSoundFormulaAt depth2Core)

/--
Under the `PropTautSound` bridge, current-target reflection packages are
impossible for the concrete depth-2 boxed internal-soundness target.

This is the exact target-shape obstruction: the proof consumes only a source
proof and a bridge from that source proof into `reflectiveBox`. It does not
consume arithmetic interpretation, Σ₁-completeness, or Solovay-realization
data.
-/
theorem no_currentTargetReflection_if_propTautSound
    (hProp :
      KripkeFrame.PropTautSound (F := depth2BoxedSoundnessFrame)
        depth2BoxedSoundnessValuation) :
    IsEmpty Depth2CurrentTargetReflection := by
  constructor
  intro candidate
  exact depth2Core_lattice_hinternal_refuted_if_propTautSound hProp
    (candidate.reflectsSourceProof candidate.sourceProof)

/--
There is no current-target reflection package paired with the concrete
countermodel's `PropTautSound` bridge.

This corollary is driven by the formal refutation of `PropTautSound` for the
countermodel, not by arithmetic content.
-/
theorem no_propTautSoundCompatibleCurrentTargetReflection :
    IsEmpty
      {_R : Depth2CurrentTargetReflection //
        KripkeFrame.PropTautSound
          (F := depth2BoxedSoundnessFrame) depth2BoxedSoundnessValuation} := by
  constructor
  intro candidate
  exact depth2BoxedSoundness_propTautSound_refuted candidate.2

/-- Route A semantic sanity check: a reflexive one-world valuation can make the
same boxed internal-soundness formula true, but godel-loeb exports no
completeness theorem turning that semantic fact into `reflectiveBox`. -/
theorem depth2Core_lattice_hinternal_forces_on_trivial_true_valuation :
    KripkeFrame.Forces (F := KripkeFrame.trivialK4Frame)
      (fun _atom _world => True)
      () (□ₛ(depth2LatticeAuditSoundFormulaAt depth2Core)) := by
  intro v _hacc hbox
  simp [depth2LatticeAuditFormulaAt, encodeAuditCertifiesLattice,
    encodeAuditCertifiesLatticeSupport, List.finRange, depth2Core, encodeAuditCertifies,
    ModalFormula.and, ModalFormula.neg, KripkeFrame.Forces]

end ReflectiveGovernanceFixedPointSystem
end Reflective
end Legitimacy
