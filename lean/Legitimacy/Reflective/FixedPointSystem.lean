/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Legitimacy.Reflective.Encoding

/-!
# Reflective governance fixed-point system

This module is theoretical-Lean-only by design. The modal Löb substrate has no
Rust extraction-side counterpart; cross-language parity gates
(`check-asi-parity-manifest.sh`) exempt this module per
`audits/parity/lean-only-modules.txt`.

The primary object here is not the governance graph itself. It is the stable
state where the agent action predicate, the external audit predicate, and the
agent's representation of that external verdict agree.

## Main results

* `ReflectiveGovernanceFixedPointSystem`: the substrate coupling monotone
  state update, external audit, action, and self-model predicates.
* `progressSystem_stableReflectiveAgreement`: a concrete progress-system
  worked example where Knaster-Tarski aligns action, audit, and self-model.
* `stable_audit_loeb`: the modal bridge discharging a stable audit certificate
  through godel-loeb's `loeb`.

The companion depth-2 worked example is deliberately modal-axiomatic rather
than an arithmetic realisation claim: audit-to-box certification uses
godel-loeb's `loeb`, while box-to-audit extraction is the encoded round-trip
direction whose stable-state alignment comes from Knaster-Tarski monotonicity
and whose available forcing witness factors through the audit certificate.
Kernel-safety reflective composition for `SelfAudit` remains outside the
current substrate: the threshold-pipeline encoding does not yet carry a
non-trivial reflective fixed point on the legitimacy graph itself.
-/

namespace Legitimacy
namespace Reflective

open ModalLogic.GoedelLoeb
open ModalLogic.GoedelLoeb.ModalFormula

universe u

/--
Typeclass interface for a reflective box substrate.

The class packages the predicate that plays the role of modal provability,
plus the modal laws consumed by the reflective stack. The consistency field is
the Pattern-9-reverse guard: it rules out `box := fun _ => True` instances
instead of letting downstream theorems be trivialized by a decorated substrate.
This file ships only the modal-axiomatic godel-loeb instance below; future
arithmetic realizations must justify each field for their own predicate before
they can reuse the stack.
-/
class ReflectiveBoxSubstrate (α : Type u) where
  /-- The substrate's derivability predicate over modal formulas. -/
  box : ModalFormula α → Prop
  /-- Consistency for the substrate predicate; falsity is not derivable. -/
  notBoxBot : ¬ box (⊥ₛ : ModalFormula α)
  /-- Necessitation for the substrate predicate. -/
  necessitation : ∀ {phi : ModalFormula α}, box phi → box (□ₛphi)
  /-- K distribution axiom under the substrate predicate. -/
  axiomK : ∀ phi psi : ModalFormula α, box (□ₛ(phi ⟶ psi) ⟶ (□ₛphi ⟶ □ₛpsi))
  /-- Modus ponens closure for the substrate predicate. -/
  mp : ∀ {phi psi : ModalFormula α}, box (phi ⟶ psi) → box phi → box psi
  /-- Löb rule for the substrate predicate. -/
  loeb : ∀ {phi : ModalFormula α}, box (□ₛphi ⟶ phi) → box phi
  /-- Propositional tautologies are substrate-derivable. -/
  ofPropTaut : ∀ {phi : ModalFormula α}, phi.PropTaut → box phi

namespace ReflectiveBoxSubstrate

/--
No valid reflective box substrate can prove every formula.

The witness is object-language falsity, carried by the class consistency
field. In particular, the constant-`True` predicate cannot instantiate
`ReflectiveBoxSubstrate`.
-/
theorem box_not_constant_True {α : Type u} [ReflectiveBoxSubstrate α] :
    ∃ phi : ModalFormula α, ¬ ReflectiveBoxSubstrate.box phi :=
  ⟨(⊥ₛ : ModalFormula α), ReflectiveBoxSubstrate.notBoxBot⟩

end ReflectiveBoxSubstrate

/-- The modal-axiomatic godel-loeb substrate as the default instance. -/
instance modalAxiomaticReflectiveBox {α : Type u} [DecidableEq α] [Diagonalisable α] :
    ReflectiveBoxSubstrate α where
  box := Provable
  notBoxBot := by
    exact Provable.not_bot
  necessitation := by
    intro phi hphi
    exact Provable.nec hphi
  axiomK := by
    intro phi psi
    exact Provable.k phi psi
  mp := by
    intro phi psi hImp hPhi
    exact Provable.mp hImp hPhi
  loeb := by
    intro phi hphi
    exact ModalLogic.GoedelLoeb.loeb (phi := phi) hphi
  ofPropTaut := by
    intro phi htaut
    exact Provable.of_prop_taut htaut

/-- The part of an agent self-model relevant to reflective audit: its internal
representation of the external audit verdict. -/
structure SelfAuditView where
  auditVerdict : Prop

/-- A reflective fixed-point system couples monotone state update with three
predicates over the state:

* `agentActs`: what the agent will do at a state;
* `auditCertifies`: what the external audit certifies at a state;
* `selfModel`: the agent's representation of the audit verdict.

The action/audit law is intentionally one-step: action after transition is
equivalent to the audit verdict before transition. The self-model law has the
same one-step shape, so fixed-state agreement is derived from transition
stability rather than supplied as a fixed-point assumption. -/
structure ReflectiveGovernanceFixedPointSystem (State : Type u) [CompleteLattice State] where
  step : State →o State
  agentActs : State → Prop
  auditCertifies : State → Prop
  selfModel : State → SelfAuditView
  agent_step_iff_audit : ∀ s : State, agentActs (step s) ↔ auditCertifies s
  selfModel_step_iff_audit :
    ∀ s : State, ((selfModel (step s)).auditVerdict ↔ auditCertifies s)

namespace ReflectiveGovernanceFixedPointSystem

variable {State : Type u} [CompleteLattice State]

/-- The canonical stable state selected by Knaster-Tarski. -/
def stable (G : ReflectiveGovernanceFixedPointSystem State) : State :=
  G.step.lfp

/-- The target theorem shape: at the least fixed point, transition stability
collapses the one-step action/audit law into same-state agreement, and the
agent's self-model agrees with the external audit at that same state. -/
def stableReflectiveAgreementStatement
    (G : ReflectiveGovernanceFixedPointSystem State) : Prop :=
  G.step G.stable = G.stable ∧
    (G.agentActs G.stable ↔ G.auditCertifies G.stable) ∧
      ((G.selfModel G.stable).auditVerdict ↔ G.auditCertifies G.stable) ∧
        (G.agentActs G.stable ↔ (G.selfModel G.stable).auditVerdict)

/-- Knaster-Tarski supplies the least fixed point of the governance transition. -/
theorem stable_fixed (G : ReflectiveGovernanceFixedPointSystem State) :
    G.step G.stable = G.stable :=
  G.step.map_lfp

/-- At a fixed point, the one-step action/audit law becomes a same-state law. -/
theorem stable_agent_iff_audit (G : ReflectiveGovernanceFixedPointSystem State) :
    G.agentActs G.stable ↔ G.auditCertifies G.stable := by
  simpa [stable_fixed G] using G.agent_step_iff_audit G.stable

/-- At a fixed point, the agent's internal audit verdict agrees with the
external audit. -/
theorem stable_selfModel_iff_audit (G : ReflectiveGovernanceFixedPointSystem State) :
    (G.selfModel G.stable).auditVerdict ↔ G.auditCertifies G.stable :=
  by
    simpa [stable_fixed G] using G.selfModel_step_iff_audit G.stable

/-- The fixed point aligns agent action, external audit, and the agent's
self-model of that audit. -/
theorem stable_agent_iff_selfModel (G : ReflectiveGovernanceFixedPointSystem State) :
    G.agentActs G.stable ↔ (G.selfModel G.stable).auditVerdict :=
  (stable_agent_iff_audit G).trans (stable_selfModel_iff_audit G).symm

/-- The compiled reflective fixed-point theorem for the substrate. -/
theorem stableReflectiveAgreement (G : ReflectiveGovernanceFixedPointSystem State) :
    G.stableReflectiveAgreementStatement := by
  refine ⟨stable_fixed G, stable_agent_iff_audit G, stable_selfModel_iff_audit G, ?_⟩
  exact stable_agent_iff_selfModel G

/-- Four-state progress lattice. Membership of `0` is the externally checked
condition and membership of `1` is the agent's current executable proof witness.
The singleton middle states are incomparable. -/
abbrev ProgressState : Type :=
  Set (Fin 2)

/-- Raw transition relation for the progress lattice. -/
def progressStepSet (s : ProgressState) : ProgressState :=
  {i | i = 0 ∨ (i = 1 ∧ (0 : Fin 2) ∈ s)}

/-- Non-constant transition: every step sets the external condition and copies
the previous condition into the witness slot. -/
def progressStep : ProgressState →o ProgressState where
  toFun := progressStepSet
  monotone' := by
    intro s t hst i hi
    rcases hi with hzero | ⟨hone, hcondition⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨hone, hst hcondition⟩

/-- The agent acts only when the witness slot has caught up. -/
def progressAgentActs (s : ProgressState) : Prop :=
  (1 : Fin 2) ∈ s

/-- The external audit certifies the checked condition slot. -/
def progressAuditCertifies (s : ProgressState) : Prop :=
  (0 : Fin 2) ∈ s

/-- A four-state reflective system whose transient middle states can disagree,
but whose transition forces convergence at the least fixed point. -/
def progressSystem : ReflectiveGovernanceFixedPointSystem ProgressState where
  step := progressStep
  agentActs := progressAgentActs
  auditCertifies := progressAuditCertifies
  selfModel := fun s => { auditVerdict := (1 : Fin 2) ∈ s }
  agent_step_iff_audit := by
    intro s
    simp [progressStep, progressStepSet, progressAgentActs, progressAuditCertifies]
  selfModel_step_iff_audit := by
    intro s
    simp [progressStep, progressStepSet, progressAuditCertifies]

/-- The transition is not the identity. -/
theorem progressStep_not_identity :
    progressSystem.step (∅ : ProgressState) ≠ (∅ : ProgressState) := by
  simp [progressSystem, progressStep, progressStepSet]

/-- The transition is not constant across the four-state lattice. -/
theorem progressStep_not_constant :
    progressSystem.step (∅ : ProgressState) ≠
      progressSystem.step ({(0 : Fin 2)} : ProgressState) := by
  intro heq
  have hright : (1 : Fin 2) ∈
      progressSystem.step ({(0 : Fin 2)} : ProgressState) := by
    simp [progressSystem, progressStep, progressStepSet]
  have hleft : (1 : Fin 2) ∈ progressSystem.step (∅ : ProgressState) := by
    simpa [heq] using hright
  simp [progressSystem, progressStep, progressStepSet] at hleft

/-- A concrete non-fixed point where the agent and external audit disagree. -/
theorem progressSystem_agent_audit_disagree_at_transient :
    ¬ (progressSystem.agentActs ({(0 : Fin 2)} : ProgressState) ↔
      progressSystem.auditCertifies ({(0 : Fin 2)} : ProgressState)) := by
  simp [progressSystem, progressAgentActs, progressAuditCertifies]

/-- The disagreement witness is genuinely away from a fixed point. -/
theorem progressSystem_transient_not_fixed :
    progressSystem.step ({(0 : Fin 2)} : ProgressState) ≠
      ({(0 : Fin 2)} : ProgressState) := by
  intro heq
  have hstep : (1 : Fin 2) ∈
      progressSystem.step ({(0 : Fin 2)} : ProgressState) := by
    simp [progressSystem, progressStep, progressStepSet]
  have hsingleton : (1 : Fin 2) ∈ ({(0 : Fin 2)} : ProgressState) := by
    rw [← heq]
    exact hstep
  simp at hsingleton

/-- The least fixed point is the state where both the external condition and
the witness slot have converged. This uses fixed-point stability to recover
both memberships. -/
theorem progressSystem_stable_eq_univ :
    progressSystem.stable = (Set.univ : ProgressState) := by
  have hfixed : progressSystem.step progressSystem.stable = progressSystem.stable :=
    stable_fixed progressSystem
  have hcondition : (0 : Fin 2) ∈ progressSystem.stable := by
    have hstep : (0 : Fin 2) ∈ progressSystem.step progressSystem.stable := by
      change (0 : Fin 2) ∈ progressStepSet progressSystem.stable
      exact Or.inl rfl
    simpa [hfixed] using hstep
  have hwitness : (1 : Fin 2) ∈ progressSystem.stable := by
    have hstep : (1 : Fin 2) ∈ progressSystem.step progressSystem.stable := by
      change (1 : Fin 2) ∈ progressStepSet progressSystem.stable
      exact Or.inr ⟨rfl, hcondition⟩
    simpa [hfixed] using hstep
  ext i
  fin_cases i
  · simpa using hcondition
  · simpa using hwitness

/-- The generic reflective theorem applies to the non-trivial progress system. -/
theorem progressSystem_stableReflectiveAgreement :
    progressSystem.stableReflectiveAgreementStatement :=
  stableReflectiveAgreement progressSystem

/-- At the fixed point, agent action, external audit, and self-model all hold. -/
theorem progressSystem_converges_at_fixed :
    progressSystem.agentActs progressSystem.stable ∧
      progressSystem.auditCertifies progressSystem.stable ∧
        (progressSystem.selfModel progressSystem.stable).auditVerdict := by
  have hstable : progressSystem.stable = Set.univ :=
    progressSystem_stable_eq_univ
  constructor
  · change (1 : Fin 2) ∈ progressSystem.stable
    rw [hstable]
    exact Set.mem_univ _
  constructor
  · change (0 : Fin 2) ∈ progressSystem.stable
    rw [hstable]
    exact Set.mem_univ _
  · change (1 : Fin 2) ∈ progressSystem.stable
    rw [hstable]
    exact Set.mem_univ _

/-- Specialize the three-predicate policy valuation to a reflective system. -/
def policyValuationFor (G : ReflectiveGovernanceFixedPointSystem State) :
    PolicyAtom State → State → Prop :=
  policyValuation G.agentActs G.auditCertifies fun s => (G.selfModel s).auditVerdict

/-- A one-world Kripke valuation that evaluates policy atoms at the stable state. -/
def stablePolicyValuationFor (G : ReflectiveGovernanceFixedPointSystem State) :
    PolicyAtom State → KripkeFrame.trivialK4Frame.World → Prop :=
  fun atom _world => policyValuationFor G atom G.stable

/-- The encoded external-audit proposition at the stable state. -/
def stableAuditFormula (G : ReflectiveGovernanceFixedPointSystem State) :
    ModalFormula (PolicyAtom State) :=
  encodeAuditCertifies G.stable

/-- The encoded proposition saying boxed audit belief implies external audit. -/
def stableAuditSoundFormula (G : ReflectiveGovernanceFixedPointSystem State) :
    ModalFormula (PolicyAtom State) :=
  □ₛ(stableAuditFormula G) ⟶ stableAuditFormula G

/-- The encoded stable-state governance trinity: action, audit, and self-model. -/
def stableGovernanceTrinityFormula (G : ReflectiveGovernanceFixedPointSystem State) :
    ModalFormula (PolicyAtom State) :=
  ModalFormula.and (encodeAgentActs G.stable)
    (ModalFormula.and (encodeAuditCertifies G.stable)
      (encodeSelfModelAgrees G.stable))

/--
The active reflective substrate proves the box of an encoded modal formula.

This is intentionally state-free: Phase B's modal substrate is not yet a
state-indexed belief model, so the name avoids implying that `G` or `s`
contribute semantic content.
-/
def reflectiveBoxOf {α : Type u} [ReflectiveBoxSubstrate α] (phi : ModalFormula α) :
    Prop :=
  ReflectiveBoxSubstrate.box (□ₛphi)

/--
Backward-compatible name for the reflective box over policy atoms.

Under the default `modalAxiomaticReflectiveBox` instance this reduces to
`Provable (□ₛ phi)`, preserving the modal-axiomatic substrate while
letting downstream theorems consume the abstract class laws.
-/
def reflectiveBox [ReflectiveBoxSubstrate (PolicyAtom State)]
    (phi : ModalFormula (PolicyAtom State)) : Prop :=
  reflectiveBoxOf phi

/-- Necessitation for encoded stable-audit formulas is a substrate law. -/
theorem stable_audit_necessitation (G : ReflectiveGovernanceFixedPointSystem State)
    [ReflectiveBoxSubstrate (PolicyAtom State)]
    (haudit : ReflectiveBoxSubstrate.box (stableAuditFormula G)) :
    reflectiveBox (stableAuditFormula G) :=
  ReflectiveBoxSubstrate.necessitation haudit

/--
Semantic soundness bridge from a boxed encoded audit formula to the external
audit predicate, using the policy valuation and godel-loeb's one-world K4 frame.
-/
theorem stable_audit_sound (G : ReflectiveGovernanceFixedPointSystem State)
    (hforces :
      KripkeFrame.Forces (F := KripkeFrame.trivialK4Frame) (stablePolicyValuationFor G)
        () (□ₛ(stableAuditFormula G))) :
    G.auditCertifies G.stable := by
  have hAtStable :
      KripkeFrame.Forces (F := KripkeFrame.trivialK4Frame)
        (stablePolicyValuationFor G) () (stableAuditFormula G) :=
    hforces () trivial
  change stablePolicyValuationFor G (PolicyAtom.auditCertifies G.stable) () at hAtStable
  simpa [stablePolicyValuationFor, policyValuationFor, policyValuation,
    stableAuditFormula, encodeAuditCertifies] using hAtStable

/--
Derived Loeb rule for the encoded stable-audit proposition.

The bridge is intentionally visible: the boxed internal soundness hypothesis is
first pushed through K to obtain the substrate proof of `□□A ⟶ □A`, and only
then does the substrate Löb field fire with `phi := □A`.
-/
theorem stable_audit_loeb (G : ReflectiveGovernanceFixedPointSystem State)
    [ReflectiveBoxSubstrate (PolicyAtom State)]
    (hinternal : reflectiveBox (stableAuditSoundFormula G)) :
    reflectiveBox (stableAuditFormula G) := by
  let auditPhi := stableAuditFormula G
  have hBoxedInternal :
      ReflectiveBoxSubstrate.box (□ₛ(□ₛauditPhi ⟶ auditPhi)) := by
    simpa [reflectiveBox, reflectiveBoxOf, stableAuditSoundFormula, auditPhi]
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

/-- The progress-system stable audit atom is forced at every accessible world. -/
theorem progressSystem_stable_audit_forces_box :
    KripkeFrame.Forces (F := KripkeFrame.trivialK4Frame)
      (stablePolicyValuationFor progressSystem) ()
      (□ₛ(stableAuditFormula progressSystem)) := by
  intro v _hacc
  have haudit : progressSystem.auditCertifies progressSystem.stable :=
    progressSystem_converges_at_fixed.2.1
  change stablePolicyValuationFor progressSystem
    (PolicyAtom.auditCertifies progressSystem.stable) v
  simpa [stablePolicyValuationFor, policyValuationFor, policyValuation, stableAuditFormula,
    encodeAuditCertifies] using haudit

/-- The progress-system stable audit certificate follows from its forced audit atom. -/
theorem progressSystem_stable_box_implies_audit :
    progressSystem.auditCertifies progressSystem.stable :=
  stable_audit_sound progressSystem progressSystem_stable_audit_forces_box

/--
The progress-system boxed audit proposition follows from the encoded internal
soundness premise, without assuming the external audit certificate.

This is the same godel-loeb-axiomatic discharge pattern used by the depth-2
worked example: the modal content lives at the `stable_audit_loeb` call rather
than in any state-lattice witness.
-/
theorem progressSystem_stable_audit_implies_box
    (hinternal :
      reflectiveBox (stableAuditSoundFormula progressSystem)) :
    reflectiveBox (stableAuditFormula progressSystem) :=
  stable_audit_loeb progressSystem hinternal

/-- Build gate: the progress-system Löb discharge fires through the class layer. -/
example
    (hinternal :
      reflectiveBox (stableAuditSoundFormula progressSystem)) :
    reflectiveBox (stableAuditFormula progressSystem) :=
  stable_audit_loeb progressSystem hinternal

/-- In the progress system, boxed audit provability and external audit agree at the
fixed point once the encoded internal soundness premise is present. -/
theorem progressSystem_stable_box_iff_audit
    (hinternal :
      reflectiveBox (stableAuditSoundFormula progressSystem)) :
    reflectiveBox (stableAuditFormula progressSystem) ↔
      progressSystem.auditCertifies progressSystem.stable :=
  Iff.intro
    (fun _ => progressSystem_stable_box_implies_audit)
    (fun _ => progressSystem_stable_audit_implies_box hinternal)

/-- In the progress system, the self-model's audit verdict agrees with the
boxed audit proposition at the fixed point under the same encoded modal premise. -/
theorem progressSystem_stable_selfModel_iff_box
    (hinternal :
      reflectiveBox (stableAuditSoundFormula progressSystem)) :
    (progressSystem.selfModel progressSystem.stable).auditVerdict ↔
      reflectiveBox (stableAuditFormula progressSystem) :=
  (stable_selfModel_iff_audit progressSystem).trans
    (progressSystem_stable_box_iff_audit hinternal).symm

/-- The progress-system stable audit certificate is Knaster-Tarski-backed. -/
theorem progressSystem_audit_certified_at_stable :
    progressSystem.auditCertifies progressSystem.stable :=
  progressSystem_converges_at_fixed.2.1

/-- The progress-system encoded trinity is forced at the stable state. -/
theorem progressSystem_stable_governance_trinity_forces :
    KripkeFrame.Forces (F := KripkeFrame.trivialK4Frame)
      (stablePolicyValuationFor progressSystem) ()
      (stableGovernanceTrinityFormula progressSystem) := by
  have hacts : progressSystem.agentActs progressSystem.stable :=
    progressSystem_converges_at_fixed.1
  have haudit : progressSystem.auditCertifies progressSystem.stable :=
    progressSystem_converges_at_fixed.2.1
  have hself : (progressSystem.selfModel progressSystem.stable).auditVerdict :=
    progressSystem_converges_at_fixed.2.2
  unfold stableGovernanceTrinityFormula ModalFormula.and ModalFormula.neg
  change
    ((stablePolicyValuationFor progressSystem (PolicyAtom.agentActs progressSystem.stable) () →
        (((stablePolicyValuationFor progressSystem
              (PolicyAtom.auditCertifies progressSystem.stable) () →
            stablePolicyValuationFor progressSystem
              (PolicyAtom.selfModelAgrees progressSystem.stable) () → False) →
          False) →
        False)) →
      False)
  intro hnotTrinity
  apply hnotTrinity
  · simpa [stablePolicyValuationFor, policyValuationFor, policyValuation] using hacts
  · intro hnotAuditSelf
    apply hnotAuditSelf
    · simpa [stablePolicyValuationFor, policyValuationFor, policyValuation] using haudit
    · simpa [stablePolicyValuationFor, policyValuationFor, policyValuation] using hself

/--
Audit predicate for the load-bearing Loeb worked example.

The external audit at a state is exactly the substrate proving the box of that
state's audit atom. Knaster-Tarski can still align the three governance
predicates, but it cannot manufacture this modal certificate.
-/
def reflectiveLoebAuditCertifies (s : Unit) : Prop :=
  reflectiveBox (encodeAuditCertifies s)

/-- A one-state system whose audit certificate is modal, not lattice-theoretic. -/
def reflectiveLoebExample : ReflectiveGovernanceFixedPointSystem Unit where
  step := {
    toFun := id
    monotone' := by
      intro s t hst
      exact hst
  }
  agentActs := reflectiveLoebAuditCertifies
  auditCertifies := reflectiveLoebAuditCertifies
  selfModel := fun s => { auditVerdict := reflectiveLoebAuditCertifies s }
  agent_step_iff_audit := by
    intro s
    rfl
  selfModel_step_iff_audit := by
    intro s
    rfl

/-- Knaster-Tarski supplies only fixed-state agreement for the Loeb example. -/
theorem reflectiveLoebExample_knaster_tarski_path :
    reflectiveLoebExample.stableReflectiveAgreementStatement :=
  stableReflectiveAgreement reflectiveLoebExample

/-- Loeb discharges the audit certificate for the modal-audit worked example. -/
theorem reflectiveLoebExample_loeb_audit_certified
    (hinternal :
      reflectiveBox (stableAuditSoundFormula reflectiveLoebExample)) :
    reflectiveLoebExample.auditCertifies reflectiveLoebExample.stable := by
  simpa [reflectiveLoebExample, reflectiveLoebAuditCertifies, stableAuditFormula]
    using stable_audit_loeb reflectiveLoebExample hinternal

/--
Verification gate: the Knaster-Tarski path is intentionally the wrong shape for
the audit certificate. If that direct fixed-point route ever starts proving the
certificate, `fail_if_success` will fail the build.
-/
theorem loeb_required_witness
    (hinternal :
      reflectiveBox (stableAuditSoundFormula reflectiveLoebExample)) :
    reflectiveLoebExample.auditCertifies reflectiveLoebExample.stable := by
  fail_if_success exact reflectiveLoebExample_knaster_tarski_path
  exact reflectiveLoebExample_loeb_audit_certified hinternal

end ReflectiveGovernanceFixedPointSystem
end Reflective
end Legitimacy
