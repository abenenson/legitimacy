/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Legitimacy.Reflective.FixedPointSystem

/-!
Depth-2 reflective fixed-point worked example.

This module contains the sixteen-state depth-2 worked example extracted from
`Legitimacy.Reflective.FixedPointSystem` to keep the release-gate file-size
ceiling focused on cohesive proof layers.
-/

namespace Legitimacy
namespace Reflective

open ModalLogic.GoedelLoeb
open ModalLogic.GoedelLoeb.ModalFormula

universe u

namespace ReflectiveGovernanceFixedPointSystem

/-- Introduce forcing for object-language conjunction. -/
private theorem forces_and_intro {α : Type u} {F : KripkeFrame}
    {val : α → F.World → Prop} {w : F.World} {phi psi : ModalFormula α}
    (hphi : KripkeFrame.Forces (F := F) val w phi)
    (hpsi : KripkeFrame.Forces (F := F) val w psi) :
    KripkeFrame.Forces (F := F) val w (ModalFormula.and phi psi) := by
  unfold ModalFormula.and ModalFormula.neg
  intro hnot
  exact hnot hphi hpsi

/-- Extract the left side of an object-language conjunction under forcing. -/
private theorem forces_and_left {α : Type u} {F : KripkeFrame}
    {val : α → F.World → Prop} {w : F.World} {phi psi : ModalFormula α}
    (h :
      KripkeFrame.Forces (F := F) val w (ModalFormula.and phi psi)) :
    KripkeFrame.Forces (F := F) val w phi := by
  classical
  unfold ModalFormula.and ModalFormula.neg at h
  by_contra hphi
  exact h fun hphi' _hpsi => hphi hphi'

/-- Extract the right side of an object-language conjunction under forcing. -/
private theorem forces_and_right {α : Type u} {F : KripkeFrame}
    {val : α → F.World → Prop} {w : F.World} {phi psi : ModalFormula α}
    (h :
      KripkeFrame.Forces (F := F) val w (ModalFormula.and phi psi)) :
    KripkeFrame.Forces (F := F) val w psi := by
  classical
  unfold ModalFormula.and ModalFormula.neg at h
  by_contra hpsi
  exact h fun _hphi hpsi' => hpsi hpsi'

/-- Sixteen-state depth-2 reflective lattice. Slots `0` and `1` are the stable
core, slot `2` is a retained upper fixed-point marker, and slot `3` is an
unreachable deny-only fragment. -/
abbrev Depth2State : Type :=
  Set (Fin 4)

/-- The proper stable core selected by the least fixed point. -/
def depth2Core : Depth2State :=
  {(0 : Fin 4), (1 : Fin 4)}

/-- A second fixed point above the least fixed point. -/
def depth2UpperFixedState : Depth2State :=
  {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4)}

/-- Raw transition relation for the depth-2 lattice. -/
def depth2StepSet (s : Depth2State) : Depth2State :=
  {i | i = 0 ∨ i = 1 ∨ (i = 2 ∧ (2 : Fin 4) ∈ s)}

/-- Non-constant transition: the core is always installed, marker `2` is
retained when already present, and deny-only marker `3` is erased. -/
def depth2Step : Depth2State →o Depth2State where
  toFun := depth2StepSet
  monotone' := by
    intro s t hst i hi
    rcases hi with hzero | hone | ⟨htwo, hmarker⟩
    · exact Or.inl hzero
    · exact Or.inr (Or.inl hone)
    · exact Or.inr (Or.inr ⟨htwo, hst hmarker⟩)

/-- The proper core is a fixed point of the depth-2 transition. -/
theorem depth2Step_core_fixed :
    depth2Step depth2Core = depth2Core := by
  ext i
  fin_cases i <;> simp [depth2Step, depth2StepSet, depth2Core]

/-- The marker-retaining state is a second, strictly larger fixed point. -/
theorem depth2Step_upper_fixed :
    depth2Step depth2UpperFixedState = depth2UpperFixedState := by
  ext i
  fin_cases i <;> simp [depth2Step, depth2StepSet, depth2UpperFixedState]

/-- The two concrete fixed points are distinct. -/
theorem depth2Core_ne_upper_fixed :
    depth2Core ≠ depth2UpperFixedState := by
  intro h
  have htwo : (2 : Fin 4) ∈ depth2Core := by
    rw [h]
    simp [depth2UpperFixedState]
  simp [depth2Core] at htwo

/-- The transition is not the identity. -/
theorem depth2Step_not_identity :
    depth2Step (∅ : Depth2State) ≠ (∅ : Depth2State) := by
  intro hstep
  have hzero : (0 : Fin 4) ∈ depth2Step (∅ : Depth2State) := by
    simp [depth2Step, depth2StepSet]
  have hempty : (0 : Fin 4) ∈ (∅ : Depth2State) := by
    rw [← hstep]
    exact hzero
  exact hempty

/-- The transition is not constant across the depth-2 lattice. -/
theorem depth2Step_not_constant :
    depth2Step depth2Core ≠ depth2Step depth2UpperFixedState := by
  intro heq
  have hright : (2 : Fin 4) ∈ depth2Step depth2UpperFixedState := by
    simp [depth2Step, depth2StepSet, depth2UpperFixedState]
  have hleft : (2 : Fin 4) ∈ depth2Step depth2Core := by
    simpa [heq] using hright
  simp [depth2Step, depth2StepSet, depth2Core] at hleft

/--
Modal audit predicate for the non-`Set.univ` depth-2 example.

The audit at `s` asks for the godel-loeb boxed audit atom of the next state.
This makes the stable audit certificate state-specific and non-uniform: the
core and the upper marker state encode different audit atoms.
-/
def depth2ReflectiveAuditCertifies (s : Depth2State) : Prop :=
  reflectiveBox (encodeAuditCertifies (depth2Step s))

/--
Non-`Set.univ` reflective worked example with a proper least fixed point.

At the fixed point, Knaster-Tarski gives only predicate agreement. The
audit-to-box direction is the substantive one: it uses godel-loeb's `loeb`
through `stable_audit_loeb`. The box-to-audit direction below is explicitly the
encoded round-trip direction; Knaster-Tarski monotonicity supplies the
fixed-state alignment, and its concrete forcing witness factors through an
already supplied audit certificate.

Here `agentActs s := reflectiveBox (encodeAuditCertifies s)` and `selfModel s`
carries the same modal-provability claim of an opaque atom indexed by state `s`.
Lattice non-triviality lives below the predicate layer: the predicates
themselves are uniformly Löb-axiomatic across all states.

Phase C-2 substrate-cliff: making `auditCertifies` a function of lattice state
rather than only atom-indexed is the path to non-trivial interaction between
modal content and lattice depth. This example is still at the substrate cliff
identified by the round-13 audit.
-/
def depth2ReflectiveSystem : ReflectiveGovernanceFixedPointSystem Depth2State where
  step := depth2Step
  agentActs := fun s => reflectiveBox (encodeAuditCertifies s)
  auditCertifies := depth2ReflectiveAuditCertifies
  selfModel := fun s => { auditVerdict := reflectiveBox (encodeAuditCertifies s) }
  agent_step_iff_audit := by
    intro s
    rfl
  selfModel_step_iff_audit := by
    intro s
    rfl

/-- The least fixed point is the proper core, not the whole lattice top. -/
theorem depth2ReflectiveSystem_stable_eq_core :
    depth2ReflectiveSystem.stable = depth2Core := by
  apply le_antisymm
  · exact depth2Step.lfp_le_fixed depth2Step_core_fixed
  · apply depth2Step.le_lfp
    intro b hb i hi
    fin_cases i <;> simp [depth2Core] at hi ⊢
    · have hstep : (0 : Fin 4) ∈ depth2Step b := by
        simp [depth2Step, depth2StepSet]
      exact hb hstep
    · have hstep : (1 : Fin 4) ∈ depth2Step b := by
        simp [depth2Step, depth2StepSet]
      exact hb hstep

/-- The depth-2 fixed point is a proper subset of `Set.univ`. -/
theorem depth2ReflectiveSystem_stable_ne_univ :
    depth2ReflectiveSystem.stable ≠ (Set.univ : Depth2State) := by
  intro hstable
  have hthree : (3 : Fin 4) ∈ depth2Core := by
    rw [← depth2ReflectiveSystem_stable_eq_core, hstable]
    exact Set.mem_univ _
  simp [depth2Core] at hthree

/-- The depth-2 example has a second fixed point above its least fixed point. -/
theorem depth2ReflectiveSystem_upper_fixed :
    depth2ReflectiveSystem.step depth2UpperFixedState = depth2UpperFixedState :=
  depth2Step_upper_fixed

/-- The two stable audit atoms are state-distinguished. -/
theorem depth2ReflectiveSystem_core_formula_ne_upper_formula :
    encodeAuditCertifies depth2Core ≠ encodeAuditCertifies depth2UpperFixedState := by
  intro hformula
  have hstate : depth2Core = depth2UpperFixedState := by
    change ModalFormula.atom (PolicyAtom.auditCertifies depth2Core) =
      ModalFormula.atom (PolicyAtom.auditCertifies depth2UpperFixedState) at hformula
    injection hformula with hatom
    injection hatom
  exact depth2Core_ne_upper_fixed hstate

/--
Verification gate for the lattice-state-functional audit encoder.

The new encoder is not merely `auditCertifies` with a different state payload:
it conjoins audit atoms for the singleton generators present in the powerset
lattice state. The upper fixed point therefore has structural modal content
for generator `2` that the core fixed point lacks.
-/
theorem depth2_audit_modal_content_differs :
    encodeAuditCertifiesLattice depth2Core ≠
      encodeAuditCertifiesLattice depth2UpperFixedState := by
  change encodeAuditCertifiesLatticeSupport
      [(0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4)] depth2Core ≠
    encodeAuditCertifiesLatticeSupport
      [(0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4)] depth2UpperFixedState
  unfold encodeAuditCertifiesLatticeSupport
  simp [depth2Core, depth2UpperFixedState, ModalFormula.and, ModalFormula.neg]
  intro h
  cases h

/--
Lattice-state-functional audit predicate for the depth-2 system.

Unlike `depth2ReflectiveAuditCertifies`, this asks the modal substrate to prove
the structural audit formula of the next lattice state, including the singleton
generators present in that state.
-/
noncomputable def depth2ReflectiveAuditCertifiesLattice (s : Depth2State) : Prop :=
  reflectiveBox (encodeAuditCertifiesLattice (depth2Step s))

/--
Depth-2 reflective system over the structural audit encoder.

This is additive: the original `depth2ReflectiveSystem` and all Phase B atomic
encoding theorems remain available. This variant is the substrate for Phase C
consumers that need modal audit content to vary with lattice shape.
-/
noncomputable def depth2ReflectiveSystemLattice :
    ReflectiveGovernanceFixedPointSystem Depth2State where
  step := depth2Step
  agentActs := fun s => reflectiveBox (encodeAuditCertifiesLattice s)
  auditCertifies := depth2ReflectiveAuditCertifiesLattice
  selfModel := fun s => { auditVerdict := reflectiveBox (encodeAuditCertifiesLattice s) }
  agent_step_iff_audit := by
    intro s
    rfl
  selfModel_step_iff_audit := by
    intro s
    rfl

/--
The structural audit formula produced by one depth-2 transition.

The transition always installs core generators `0` and `1`, preserves marker
`2` exactly when it was already present, erases marker `3`, and names the
whole stepped state as the base audit atom.
-/
noncomputable def depth2AuditStepComposedFormula (s : Depth2State) :
    ModalFormula (PolicyAtom Depth2State) := by
  classical
  exact
    ModalFormula.and (encodeAuditCertifies ({(0 : Fin 4)} : Depth2State))
      (ModalFormula.and (encodeAuditCertifies ({(1 : Fin 4)} : Depth2State))
        (if (2 : Fin 4) ∈ s then
          ModalFormula.and (encodeAuditCertifies ({(2 : Fin 4)} : Depth2State))
            (encodeAuditCertifies (depth2Step s))
        else
          encodeAuditCertifies (depth2Step s)))

/--
Depth-2 compose equation for the lattice-state-functional audit encoder.

This is the syntactic bridge missing from Track C: encoding the transitioned
state is definitionally the modal composition that installs core support,
preserves marker `2` from the source state, erases marker `3`, and then audits
the whole stepped state.
-/
theorem depth2_encodeAuditCertifiesLattice_step_compose (s : Depth2State) :
    encodeAuditCertifiesLattice (depth2Step s) =
      depth2AuditStepComposedFormula s := by
  classical
  change encodeAuditCertifiesLatticeSupport
      [(0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4)] (depth2Step s) =
    depth2AuditStepComposedFormula s
  by_cases htwo : (2 : Fin 4) ∈ s
  · simp [depth2AuditStepComposedFormula, encodeAuditCertifiesLatticeSupport,
      depth2Step, depth2StepSet, htwo]
  · simp [depth2AuditStepComposedFormula, encodeAuditCertifiesLatticeSupport,
      depth2Step, depth2StepSet, htwo]

/-- If marker `2` is present in the source state, the source lattice audit
formula forces the singleton audit atom for generator `2`. -/
theorem depth2_lattice_forces_marker_two_of_mem {F : KripkeFrame}
    {val : PolicyAtom Depth2State → F.World → Prop} {w : F.World}
    {s : Depth2State} (htwo : (2 : Fin 4) ∈ s)
    (hsource :
      KripkeFrame.Forces (F := F) val w (encodeAuditCertifiesLattice s)) :
    KripkeFrame.Forces (F := F) val w
      (encodeAuditCertifies ({(2 : Fin 4)} : Depth2State)) := by
  classical
  change KripkeFrame.Forces (F := F) val w
    (encodeAuditCertifiesLatticeSupport
      [(0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4)] s) at hsource
  unfold encodeAuditCertifiesLatticeSupport at hsource
  by_cases hzero : (0 : Fin 4) ∈ s
  · by_cases hone : (1 : Fin 4) ∈ s
    · have hsource' :
          KripkeFrame.Forces (F := F) val w
            (ModalFormula.and (encodeAuditCertifies ({(0 : Fin 4)} : Depth2State))
              (ModalFormula.and (encodeAuditCertifies ({(1 : Fin 4)} : Depth2State))
                (ModalFormula.and (encodeAuditCertifies ({(2 : Fin 4)} : Depth2State))
                  (if (3 : Fin 4) ∈ s then
                    ModalFormula.and (encodeAuditCertifies ({(3 : Fin 4)} : Depth2State))
                      (encodeAuditCertifies s)
                  else
                    encodeAuditCertifies s)))) := by
        simpa [htwo, hzero, hone] using hsource
      have htail01 := forces_and_right hsource'
      have htail1 := forces_and_right htail01
      simpa [htwo, hzero, hone] using forces_and_left htail1
    · have hsource' :
          KripkeFrame.Forces (F := F) val w
            (ModalFormula.and (encodeAuditCertifies ({(0 : Fin 4)} : Depth2State))
              (ModalFormula.and (encodeAuditCertifies ({(2 : Fin 4)} : Depth2State))
                (if (3 : Fin 4) ∈ s then
                  ModalFormula.and (encodeAuditCertifies ({(3 : Fin 4)} : Depth2State))
                    (encodeAuditCertifies s)
                else
                  encodeAuditCertifies s))) := by
        simpa [htwo, hzero, hone] using hsource
      have htail0 := forces_and_right hsource'
      simpa [htwo, hzero, hone] using forces_and_left htail0
  · by_cases hone : (1 : Fin 4) ∈ s
    · have hsource' :
          KripkeFrame.Forces (F := F) val w
            (ModalFormula.and (encodeAuditCertifies ({(1 : Fin 4)} : Depth2State))
              (ModalFormula.and (encodeAuditCertifies ({(2 : Fin 4)} : Depth2State))
                (if (3 : Fin 4) ∈ s then
                  ModalFormula.and (encodeAuditCertifies ({(3 : Fin 4)} : Depth2State))
                    (encodeAuditCertifies s)
                else
                  encodeAuditCertifies s))) := by
        simpa [htwo, hzero, hone] using hsource
      have htail1 := forces_and_right hsource'
      simpa [htwo, hzero, hone] using forces_and_left htail1
    · have hsource' :
          KripkeFrame.Forces (F := F) val w
            (ModalFormula.and (encodeAuditCertifies ({(2 : Fin 4)} : Depth2State))
              (if (3 : Fin 4) ∈ s then
                ModalFormula.and (encodeAuditCertifies ({(3 : Fin 4)} : Depth2State))
                  (encodeAuditCertifies s)
              else
                encodeAuditCertifies s)) := by
        simpa [htwo, hzero, hone] using hsource
      simpa [htwo, hzero, hone] using forces_and_left hsource'

/--
Forcing-level compose theorem for the depth-2 lattice audit encoder.

The target stepped formula is forced from four pieces: the source lattice audit
formula, the two newly installed core-generator certificates, and the audit
atom for the whole stepped state. The proof consumes the source formula only
for the preserved marker-`2` branch, so modal content changes under
composition instead of passing unchanged through fixed-point rewriting.
-/
theorem depth2_audit_compose_forces {F : KripkeFrame}
    {val : PolicyAtom Depth2State → F.World → Prop} {w : F.World}
    {s : Depth2State}
    (hsource :
      KripkeFrame.Forces (F := F) val w (encodeAuditCertifiesLattice s))
    (hcore0 :
      KripkeFrame.Forces (F := F) val w
        (encodeAuditCertifies ({(0 : Fin 4)} : Depth2State)))
    (hcore1 :
      KripkeFrame.Forces (F := F) val w
        (encodeAuditCertifies ({(1 : Fin 4)} : Depth2State)))
    (hstep :
      KripkeFrame.Forces (F := F) val w (encodeAuditCertifies (depth2Step s))) :
    KripkeFrame.Forces (F := F) val w
      (encodeAuditCertifiesLattice (depth2Step s)) := by
  classical
  rw [depth2_encodeAuditCertifiesLattice_step_compose]
  refine forces_and_intro hcore0 (forces_and_intro hcore1 ?_)
  by_cases htwo : (2 : Fin 4) ∈ s
  · simpa [htwo] using
      forces_and_intro (depth2_lattice_forces_marker_two_of_mem htwo hsource) hstep
  · simpa [depth2AuditStepComposedFormula, htwo] using hstep

/-- The lattice-encoded variant has the same proper least fixed point. -/
theorem depth2ReflectiveSystemLattice_stable_eq_core :
    depth2ReflectiveSystemLattice.stable = depth2Core := by
  change depth2Step.lfp = depth2Core
  simpa [ReflectiveGovernanceFixedPointSystem.stable, depth2ReflectiveSystem]
    using depth2ReflectiveSystem_stable_eq_core

/-- State-indexed structural audit formula for depth-2 lattice discharges. -/
noncomputable def depth2LatticeAuditFormulaAt (s : Depth2State) :
    ModalFormula (PolicyAtom Depth2State) :=
  encodeAuditCertifiesLattice s

/-- State-indexed internal soundness formula for depth-2 lattice audit content. -/
noncomputable def depth2LatticeAuditSoundFormulaAt (s : Depth2State) :
    ModalFormula (PolicyAtom Depth2State) :=
  □ₛ(depth2LatticeAuditFormulaAt s) ⟶ depth2LatticeAuditFormulaAt s

/-- Stable-state structural audit formula for the lattice-encoded variant. -/
noncomputable def depth2LatticeStableAuditFormula :
    ModalFormula (PolicyAtom Depth2State) :=
  depth2LatticeAuditFormulaAt depth2ReflectiveSystemLattice.stable

/-- Encoded internal soundness for the structural stable-audit formula. -/
noncomputable def depth2LatticeStableAuditSoundFormula :
    ModalFormula (PolicyAtom Depth2State) :=
  □ₛ(depth2LatticeStableAuditFormula) ⟶ depth2LatticeStableAuditFormula

/-- Loeb discharges the structural boxed audit formula at any named depth-2 state. -/
theorem depth2Lattice_audit_implies_box_at (s : Depth2State)
    [ReflectiveBoxSubstrate (PolicyAtom Depth2State)]
    (hinternal : reflectiveBox (depth2LatticeAuditSoundFormulaAt s)) :
    reflectiveBox (depth2LatticeAuditFormulaAt s) := by
  let auditPhi := depth2LatticeAuditFormulaAt s
  have hBoxedInternal :
      ReflectiveBoxSubstrate.box (□ₛ(□ₛauditPhi ⟶ auditPhi)) := by
    simpa [reflectiveBox, reflectiveBoxOf, depth2LatticeAuditSoundFormulaAt, auditPhi]
      using hinternal
  have hK :
      ReflectiveBoxSubstrate.box (□ₛ(□ₛauditPhi ⟶ auditPhi) ⟶
        (□ₛ(□ₛauditPhi) ⟶ □ₛauditPhi)) :=
    ReflectiveBoxSubstrate.axiomK (□ₛauditPhi) auditPhi
  have hBoxBoxToBox : ReflectiveBoxSubstrate.box (□ₛ(□ₛauditPhi) ⟶ □ₛauditPhi) :=
    ReflectiveBoxSubstrate.mp hK hBoxedInternal
  have hLoebBox : ReflectiveBoxSubstrate.box (□ₛauditPhi) :=
    ReflectiveBoxSubstrate.loeb hBoxBoxToBox
  simpa [reflectiveBox, reflectiveBoxOf, auditPhi] using hLoebBox

/-- Loeb discharges the structural boxed audit formula. -/
theorem depth2ReflectiveSystemLattice_stable_audit_implies_box
    (hinternal : reflectiveBox depth2LatticeStableAuditSoundFormula) :
    reflectiveBox depth2LatticeStableAuditFormula := by
  exact depth2Lattice_audit_implies_box_at depth2ReflectiveSystemLattice.stable
    (by
      simpa [depth2LatticeStableAuditSoundFormula,
        depth2LatticeStableAuditFormula, depth2LatticeAuditSoundFormulaAt])

/-- Loeb certifies the lattice-state-functional audit predicate at the proper
stable state. -/
theorem depth2ReflectiveSystemLattice_loeb_audit_certified
    (hinternal : reflectiveBox depth2LatticeStableAuditSoundFormula) :
    depth2ReflectiveSystemLattice.auditCertifies depth2ReflectiveSystemLattice.stable := by
  have hbox : reflectiveBox depth2LatticeStableAuditFormula :=
    depth2ReflectiveSystemLattice_stable_audit_implies_box hinternal
  change reflectiveBox (encodeAuditCertifiesLattice
    (depth2Step depth2ReflectiveSystemLattice.stable))
  rw [show depth2Step depth2ReflectiveSystemLattice.stable =
      depth2ReflectiveSystemLattice.stable from
    stable_fixed depth2ReflectiveSystemLattice]
  exact hbox

/-- Loeb certifies the structural audit predicate at the lower depth-2 fixed point. -/
theorem depth2CoreFixedState_loeb_audit_certified
    (hinternal : reflectiveBox (depth2LatticeAuditSoundFormulaAt depth2Core)) :
    depth2ReflectiveSystemLattice.auditCertifies depth2Core := by
  have hbox : reflectiveBox (depth2LatticeAuditFormulaAt depth2Core) :=
    depth2Lattice_audit_implies_box_at depth2Core hinternal
  change reflectiveBox (encodeAuditCertifiesLattice (depth2Step depth2Core))
  rw [depth2Step_core_fixed]
  simpa [depth2LatticeAuditFormulaAt] using hbox

/-- Loeb certifies the structural audit predicate at the upper depth-2 fixed point. -/
theorem depth2UpperFixedState_loeb_audit_certified
    (hinternal :
      reflectiveBox (depth2LatticeAuditSoundFormulaAt depth2UpperFixedState)) :
    depth2ReflectiveSystemLattice.auditCertifies depth2UpperFixedState := by
  have hbox : reflectiveBox (depth2LatticeAuditFormulaAt depth2UpperFixedState) :=
    depth2Lattice_audit_implies_box_at depth2UpperFixedState hinternal
  change reflectiveBox (encodeAuditCertifiesLattice (depth2Step depth2UpperFixedState))
  rw [depth2Step_upper_fixed]
  simpa [depth2LatticeAuditFormulaAt] using hbox

/-- The lower and upper fixed-point Loeb invocations operate on distinct
lattice-state-functional modal content. -/
theorem depth2_lattice_differentiated_discharge_formulas :
    depth2LatticeAuditFormulaAt depth2Core ≠
      depth2LatticeAuditFormulaAt depth2UpperFixedState := by
  simpa [depth2LatticeAuditFormulaAt] using depth2_audit_modal_content_differs

/-- The explicit composed audit formula for the upper depth-2 fixed point. -/
noncomputable def depth2UpperFixedStateComposedAuditFormula :
    ModalFormula (PolicyAtom Depth2State) :=
  depth2AuditStepComposedFormula depth2UpperFixedState

/-- Internal soundness for the explicit upper fixed-point composed audit formula. -/
noncomputable def depth2UpperFixedStateComposedAuditSoundFormula :
    ModalFormula (PolicyAtom Depth2State) :=
  □ₛ(depth2UpperFixedStateComposedAuditFormula) ⟶
    depth2UpperFixedStateComposedAuditFormula

/--
Löb discharges the upper fixed point through the explicit composed formula.

This is the Track C-3 strengthening of the old bundle-shaped discharge:
`loeb` fires with `phi := □ₛdepth2UpperFixedStateComposedAuditFormula`, so
the modal target is the lattice-marker composition form rather than a parallel
fixed-point audit formula. The boxed internal-soundness premise is still the
Phase-B-shaped substrate cliff; this theorem strengthens the F3 wiring, not the
F7 construction of that premise.
-/
theorem depth2UpperFixedState_audit_certified_via_compose
    (hinternal :
      reflectiveBox (depth2LatticeAuditSoundFormulaAt depth2UpperFixedState)) :
    depth2ReflectiveSystemLattice.auditCertifies depth2UpperFixedState := by
  have hinternalCompose :
      reflectiveBox depth2UpperFixedStateComposedAuditSoundFormula := by
    simpa [reflectiveBox, depth2UpperFixedStateComposedAuditSoundFormula,
      depth2UpperFixedStateComposedAuditFormula, depth2LatticeAuditSoundFormulaAt,
      depth2LatticeAuditFormulaAt, ← depth2_encodeAuditCertifiesLattice_step_compose
        depth2UpperFixedState, depth2Step_upper_fixed] using hinternal
  let composePhi := depth2UpperFixedStateComposedAuditFormula
  have hBoxedInternal :
      ReflectiveBoxSubstrate.box (□ₛ(□ₛcomposePhi ⟶ composePhi)) := by
    simpa [reflectiveBox, reflectiveBoxOf, depth2UpperFixedStateComposedAuditSoundFormula,
      composePhi]
      using hinternalCompose
  have hK :
      ReflectiveBoxSubstrate.box (□ₛ(□ₛcomposePhi ⟶ composePhi) ⟶
        (□ₛ(□ₛcomposePhi) ⟶ □ₛcomposePhi)) :=
    ReflectiveBoxSubstrate.axiomK (□ₛcomposePhi) composePhi
  have hBoxBoxToBox : ReflectiveBoxSubstrate.box (□ₛ(□ₛcomposePhi) ⟶ □ₛcomposePhi) :=
    ReflectiveBoxSubstrate.mp hK hBoxedInternal
  have hLoebBox : ReflectiveBoxSubstrate.box (□ₛcomposePhi) :=
    ReflectiveBoxSubstrate.loeb hBoxBoxToBox
  change reflectiveBox (encodeAuditCertifiesLattice (depth2Step depth2UpperFixedState))
  rw [depth2_encodeAuditCertifiesLattice_step_compose]
  simpa [reflectiveBox, reflectiveBoxOf, composePhi, depth2UpperFixedStateComposedAuditFormula]
    using hLoebBox

/-- Knaster-Tarski supplies fixed-state agreement for the depth-2 example. -/
theorem depth2ReflectiveSystem_knaster_tarski_path :
    depth2ReflectiveSystem.stableReflectiveAgreementStatement :=
  stableReflectiveAgreement depth2ReflectiveSystem

/--
The audit-to-box leg for the depth-2 example uses godel-loeb's `loeb`.

This is the novel direction: the proof body delegates to `stable_audit_loeb`,
whose proof applies K, modus ponens, and then `loeb` to the boxed audit atom.
The Löb-discharge content is structurally identical to the progress-system
analog. Lattice non-triviality, witnessed by the proper-subset stable point,
does not drive modal content; it shows the witness is not vacuously discharged
via `Set.univ`. Modal content lives at the godel-loeb-axiomatic Löb call,
independent of lattice depth.
-/
theorem depth2ReflectiveSystem_stable_audit_implies_box
    (hinternal :
      reflectiveBox (stableAuditSoundFormula depth2ReflectiveSystem)) :
    reflectiveBox (stableAuditFormula depth2ReflectiveSystem) :=
  stable_audit_loeb depth2ReflectiveSystem hinternal

/-- Loeb discharges the stable audit certificate for the non-`Set.univ` worked
example. -/
theorem depth2ReflectiveSystem_loeb_audit_certified
    (hinternal :
      reflectiveBox (stableAuditSoundFormula depth2ReflectiveSystem)) :
    depth2ReflectiveSystem.auditCertifies depth2ReflectiveSystem.stable := by
  have hbox : reflectiveBox (stableAuditFormula depth2ReflectiveSystem) :=
    depth2ReflectiveSystem_stable_audit_implies_box hinternal
  change reflectiveBox (encodeAuditCertifies (depth2Step depth2ReflectiveSystem.stable))
  rw [show depth2Step depth2ReflectiveSystem.stable = depth2ReflectiveSystem.stable from
    stable_fixed depth2ReflectiveSystem]
  exact hbox

/-- Build gate: the depth-2 worked example still fires through the class layer. -/
example
    (hinternal :
      reflectiveBox (stableAuditSoundFormula depth2ReflectiveSystem)) :
    depth2ReflectiveSystem.auditCertifies depth2ReflectiveSystem.stable :=
  depth2ReflectiveSystem_loeb_audit_certified hinternal

/--
Encoded round-trip witness for the box-to-audit leg.

This direction is structurally derivable: the available forcing witness for
`□A` is built from an already supplied audit certificate. Knaster-Tarski
monotonicity supplies the fixed-state alignment around this witness; it is not
the substantive Löb-discharge.
-/
theorem depth2ReflectiveSystem_stable_audit_forces_box
    (haudit :
      depth2ReflectiveSystem.auditCertifies depth2ReflectiveSystem.stable) :
    KripkeFrame.Forces (F := KripkeFrame.trivialK4Frame)
      (stablePolicyValuationFor depth2ReflectiveSystem) ()
      (□ₛ(stableAuditFormula depth2ReflectiveSystem)) := by
  intro v _hacc
  change stablePolicyValuationFor depth2ReflectiveSystem
    (PolicyAtom.auditCertifies depth2ReflectiveSystem.stable) v
  simpa [stablePolicyValuationFor, policyValuationFor, policyValuation,
    stableAuditFormula, depth2ReflectiveSystem, depth2ReflectiveAuditCertifies,
    stable_fixed depth2ReflectiveSystem] using haudit

/--
Box-to-audit extraction for the depth-2 example.

This is the encoded round-trip direction: `stable_audit_sound` translates a
forced boxed audit atom back to the Lean audit predicate, while the concrete
forcing witness above factors through the audit certificate and Knaster-Tarski
monotonicity supplies only the surrounding fixed-point alignment.
-/
theorem depth2ReflectiveSystem_stable_box_implies_audit
    (hforces :
      KripkeFrame.Forces (F := KripkeFrame.trivialK4Frame)
        (stablePolicyValuationFor depth2ReflectiveSystem) ()
        (□ₛ(stableAuditFormula depth2ReflectiveSystem))) :
    depth2ReflectiveSystem.auditCertifies depth2ReflectiveSystem.stable :=
  stable_audit_sound depth2ReflectiveSystem hforces

/--
Verification gate: direct Knaster-Tarski computation is intentionally unable
to prove the modal audit certificate for the proper fixed point. The final line
compiles only because the Löb route fires through `stable_audit_loeb`.
-/
theorem depth2_loeb_required_witness
    (hinternal :
      reflectiveBox (stableAuditSoundFormula depth2ReflectiveSystem)) :
    depth2ReflectiveSystem.auditCertifies depth2ReflectiveSystem.stable := by
  fail_if_success
    simpa [depth2ReflectiveSystem, depth2ReflectiveAuditCertifies,
      depth2ReflectiveSystem_stable_eq_core]
  exact depth2ReflectiveSystem_loeb_audit_certified hinternal

end ReflectiveGovernanceFixedPointSystem
end Reflective
end Legitimacy
