/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Reflective.Depth2
import Legitimacy.Spectral.Channels.CStarChannelBridge

/-!
# Reflective composition with critical capability

This module is the Phase C-2 probe: it asks whether the exact critical
capability threshold `C_star G s δ` can be consumed by the reflective
fixed-point substrate without collapsing into a bundle of independent facts.

## Main result

* `criticalCapabilityReflectiveSystem_stable_audit_unfolds_to_subcritical_under_hinternal`: for the
  composed system, the stable reflective audit unfolds to the concrete `C_star`
  subcritical inequality under the abstract `hinternal` premise.
* `criticalCapability_audit_distinguishes_subcritical_fixed_states`: two
  depth-2 fixed states can share the subcritical threshold position while their
  content-extracted audit verdicts differ by the lattice audit formula.
* `concreteCriticalCapabilityReflectiveSystem_response_split`: a worked
  three-node graph instance where the stable state is below threshold and the
  erased transient marker is at threshold.
-/

set_option autoImplicit false

namespace Legitimacy
namespace Reflective
namespace ReflectiveGovernanceFixedPointSystem

open ModalLogic.GoedelLoeb

variable {n : Nat}

/-- The C-2 composition reuses the depth-2 lattice support. Marker `3` denotes
the above-threshold transient branch erased by `depth2Step`. -/
abbrev CriticalCapabilityReflectiveState : Type :=
  Depth2State

/-- Stable below-threshold state for the C-2 composition. -/
def criticalCapabilityStableState : CriticalCapabilityReflectiveState :=
  depth2Core

/-- Above-threshold transient marker erased by one reflective transition. -/
def criticalCapabilityAboveTransientState : CriticalCapabilityReflectiveState :=
  {(3 : Fin 4)}

/-- State-indexed capability: the erased transient marker receives the high
capability; all other states receive the low capability. -/
noncomputable def criticalCapabilityStateCapability
    (Cbelow Cabove : ℚ) (x : CriticalCapabilityReflectiveState) : ℚ :=
  by
    classical
    exact if (3 : Fin 4) ∈ x then Cabove else Cbelow

/-- The spectral side of the composed predicate: the state's selected
capability lies strictly below the exact critical threshold. -/
noncomputable def criticalCapabilityBelowThreshold
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (x : CriticalCapabilityReflectiveState) : Prop :=
  criticalCapabilityStateCapability Cbelow Cabove x < C_star G s δ

/-- Modal truth is always reflectively boxed by necessitation. -/
theorem reflectiveBox_top
    [ReflectiveBoxSubstrate (PolicyAtom CriticalCapabilityReflectiveState)] :
    reflectiveBox
      (ModalFormula.top : ModalFormula (PolicyAtom CriticalCapabilityReflectiveState)) := by
  exact ReflectiveBoxSubstrate.necessitation
    (ReflectiveBoxSubstrate.ofPropTaut (by
      intro val hbot
      exact hbot))

/--
Threshold-conditioned modal audit target.

Below the exact capability threshold, the modal formula is the genuine
lattice-state audit certificate. At and above threshold, it is the lattice
audit certificate conjoined with modal truth, so the branch is no longer
available from `□⊤` alone. The action predicate below compares the threshold
side with a content-extracted verdict from the selected formula. The shared
`depth2Step` transition is still threshold-blind, and this C-2 layer couples
the threshold through the modal target rather than by changing the depth-2
lattice transition itself.
-/
noncomputable def criticalCapabilityThresholdAuditFormula
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (x : CriticalCapabilityReflectiveState) :
    ModalFormula (PolicyAtom CriticalCapabilityReflectiveState) :=
  by
    classical
    exact
      if criticalCapabilityBelowThreshold G s δ Cbelow Cabove x then
        encodeAuditCertifiesLattice x
      else
        ModalFormula.and (encodeAuditCertifiesLattice x) ModalFormula.top

/-- Internal soundness for the threshold-conditioned modal audit target. -/
noncomputable def criticalCapabilityThresholdAuditSoundFormula
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (x : CriticalCapabilityReflectiveState) :
    ModalFormula (PolicyAtom CriticalCapabilityReflectiveState) :=
  □ₛ(criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove x) ⟶
    criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove x

/--
Löb discharges the threshold-conditioned audit formula.

The formula being discharged already contains the spectral threshold branch.
Consequently the C-2 headline theorem below cannot reduce to
`constant ∧ threshold ↔ threshold`: the modal side changes when the exact
capability threshold changes.
-/
theorem criticalCapabilityThresholdAudit_implies_box_at
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (x : CriticalCapabilityReflectiveState)
    [ReflectiveBoxSubstrate (PolicyAtom CriticalCapabilityReflectiveState)]
    (hinternal :
      reflectiveBox (criticalCapabilityThresholdAuditSoundFormula G s δ Cbelow Cabove x)) :
    reflectiveBox (criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove x) := by
  let auditPhi := criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove x
  have hBoxedInternal :
      ReflectiveBoxSubstrate.box (□ₛ(□ₛauditPhi ⟶ auditPhi)) := by
    simpa [reflectiveBox, reflectiveBoxOf, criticalCapabilityThresholdAuditSoundFormula, auditPhi]
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

/--
Content-extracted audit verdict selected by the threshold-Löb formula.

Below threshold, the audit must both box the selected modal formula and extract
the stable-core lattice content from that formula. At and above threshold, the
verdict remains the boxed selected formula, so the headline forward direction
must still obtain a box for the branch selected by the threshold.
-/
noncomputable def criticalCapabilityAuditContentVerdict
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (x : CriticalCapabilityReflectiveState) : Prop :=
  by
    classical
    exact
      if criticalCapabilityBelowThreshold G s δ Cbelow Cabove x then
        reflectiveBox (criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove x) ∧
          criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove x =
            encodeAuditCertifiesLattice criticalCapabilityStableState
      else
        reflectiveBox (criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove x)

/-- Agent predicate for the composed reflective system. It is an equivalence
between the spectral threshold and the boxed modal certificate selected by
that threshold, rather than a passive conjunction of the two facts. -/
noncomputable def criticalCapabilityAgentActs
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (x : CriticalCapabilityReflectiveState) : Prop :=
  criticalCapabilityBelowThreshold G s δ Cbelow Cabove x ↔
    criticalCapabilityAuditContentVerdict G s δ Cbelow Cabove x

/-- Audit predicate for the composed system: audit certifies exactly what the
agent predicate will certify after the reflective transition. -/
noncomputable def criticalCapabilityAuditCertifies
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (x : CriticalCapabilityReflectiveState) : Prop :=
  criticalCapabilityAgentActs G s δ Cbelow Cabove (depth2Step x)

/-- Reflective fixed-point system coupled to the exact critical-capability
threshold. The threshold is not a post-hoc theorem: it is part of the action,
audit, and self-model predicates whose fixed-point agreement is proved by the
reflective substrate. -/
noncomputable def criticalCapabilityReflectiveSystem
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ) :
    ReflectiveGovernanceFixedPointSystem CriticalCapabilityReflectiveState where
  step := depth2Step
  agentActs := criticalCapabilityAgentActs G s δ Cbelow Cabove
  auditCertifies := criticalCapabilityAuditCertifies G s δ Cbelow Cabove
  selfModel := fun x =>
    { auditVerdict := criticalCapabilityAgentActs G s δ Cbelow Cabove x }
  agent_step_iff_audit := by
    intro x
    rfl
  selfModel_step_iff_audit := by
    intro x
    rfl

/-- The composed system keeps the depth-2 proper least fixed point. -/
theorem criticalCapabilityReflectiveSystem_stable_eq_core
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ) :
    (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).stable =
      criticalCapabilityStableState := by
  change depth2Step.lfp = depth2Core
  simpa [criticalCapabilityStableState] using depth2ReflectiveSystem_stable_eq_core

/-- The above-threshold marker is transient, not another fixed point. -/
theorem criticalCapabilityAboveTransient_not_fixed :
    depth2Step criticalCapabilityAboveTransientState ≠
      criticalCapabilityAboveTransientState := by
  intro hfixed
  have hzero : (0 : Fin 4) ∈ depth2Step criticalCapabilityAboveTransientState := by
    simp [criticalCapabilityAboveTransientState, depth2Step, depth2StepSet]
  have hzero' : (0 : Fin 4) ∈ criticalCapabilityAboveTransientState := by
    simpa [hfixed] using hzero
  simp [criticalCapabilityAboveTransientState] at hzero'

/-- The transient marker is erased to the stable core in one step. -/
theorem criticalCapabilityAboveTransient_steps_to_core :
    depth2Step criticalCapabilityAboveTransientState = criticalCapabilityStableState := by
  ext i
  fin_cases i <;>
    simp [criticalCapabilityAboveTransientState, criticalCapabilityStableState,
      depth2Core, depth2Step, depth2StepSet]

/-- At the stable state, the selected capability is the low capability. -/
theorem criticalCapabilityStableState_capability
    (Cbelow Cabove : ℚ) :
    criticalCapabilityStateCapability Cbelow Cabove criticalCapabilityStableState =
      Cbelow := by
  simp [criticalCapabilityStateCapability, criticalCapabilityStableState, depth2Core]

/-- At the erased transient marker, the selected capability is the high
capability. -/
theorem criticalCapabilityAboveTransientState_capability
    (Cbelow Cabove : ℚ) :
    criticalCapabilityStateCapability Cbelow Cabove
      criticalCapabilityAboveTransientState = Cabove := by
  simp [criticalCapabilityStateCapability, criticalCapabilityAboveTransientState]

/-- The core and upper fixed states can occupy the same subcritical threshold
region while selecting different Löb-discharged lattice audit content. -/
theorem criticalCapability_subcritical_fixed_state_modal_content_differs
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (hcore :
      criticalCapabilityBelowThreshold G s δ Cbelow Cabove depth2Core)
    (hupper :
      criticalCapabilityBelowThreshold G s δ Cbelow Cabove depth2UpperFixedState) :
    criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove depth2Core ≠
      criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove
        depth2UpperFixedState := by
  simpa [criticalCapabilityThresholdAuditFormula, hcore, hupper] using
    depth2_audit_modal_content_differs

/-- At the upper fixed state, subcritical threshold position plus the core-content
extraction test rejects the verdict because marker `2` changes the selected
lattice audit formula. -/
theorem criticalCapability_upperFixedState_not_core_content_verdict
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (hupper :
      criticalCapabilityBelowThreshold G s δ Cbelow Cabove depth2UpperFixedState) :
    ¬ criticalCapabilityAuditContentVerdict G s δ Cbelow Cabove
        depth2UpperFixedState := by
  intro hverdict
  have hcontent :
      encodeAuditCertifiesLattice depth2UpperFixedState =
        encodeAuditCertifiesLattice criticalCapabilityStableState := by
    have hpair :
        reflectiveBox
            (criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove
              depth2UpperFixedState) ∧
          criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove
              depth2UpperFixedState =
            encodeAuditCertifiesLattice criticalCapabilityStableState := by
      simpa [criticalCapabilityAuditContentVerdict, hupper] using hverdict
    simpa [criticalCapabilityThresholdAuditFormula, hupper] using hpair.2
  exact depth2_audit_modal_content_differs (by
    simpa [criticalCapabilityStableState] using hcontent.symm)

/--
State-extraction theorem for Track I.

The two fixed states are both subcritical, but their threshold-selected modal
audit content differs by `depth2_audit_modal_content_differs`. The strengthened
content-extraction verdict therefore certifies the core audit and rejects the
upper fixed-state audit.
-/
theorem criticalCapability_audit_distinguishes_subcritical_fixed_states
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (hcore :
      criticalCapabilityBelowThreshold G s δ Cbelow Cabove depth2Core)
    (hupper :
      criticalCapabilityBelowThreshold G s δ Cbelow Cabove depth2UpperFixedState)
    (hinternal_core :
      reflectiveBox
        (criticalCapabilityThresholdAuditSoundFormula G s δ Cbelow Cabove
          depth2Core))
    (hinternal_upper :
      reflectiveBox
        (criticalCapabilityThresholdAuditSoundFormula G s δ Cbelow Cabove
          depth2UpperFixedState)) :
    (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).auditCertifies
        depth2Core ≠
      (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).auditCertifies
        depth2UpperFixedState := by
  let R := criticalCapabilityReflectiveSystem G s δ Cbelow Cabove
  have hcoreAudit : R.auditCertifies depth2Core := by
    change criticalCapabilityAgentActs G s δ Cbelow Cabove (depth2Step depth2Core)
    rw [depth2Step_core_fixed]
    have hbox :
        reflectiveBox
          (criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove depth2Core) :=
      criticalCapabilityThresholdAudit_implies_box_at
        G s δ Cbelow Cabove depth2Core hinternal_core
    have hcontent :
        criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove depth2Core =
          encodeAuditCertifiesLattice criticalCapabilityStableState := by
      simp [criticalCapabilityThresholdAuditFormula, hcore, criticalCapabilityStableState]
    have hverdict :
        criticalCapabilityAuditContentVerdict G s δ Cbelow Cabove depth2Core := by
      simpa [criticalCapabilityAuditContentVerdict, hcore] using
        And.intro hbox hcontent
    exact ⟨fun _hbelow => hverdict, fun _hverdict => hcore⟩
  have hupperBox :
      reflectiveBox
        (criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove
          depth2UpperFixedState) :=
    criticalCapabilityThresholdAudit_implies_box_at
      G s δ Cbelow Cabove depth2UpperFixedState hinternal_upper
  have hupperRejectedDespiteBox :
      reflectiveBox
          (criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove
            depth2UpperFixedState) ∧
        ¬ criticalCapabilityAuditContentVerdict G s δ Cbelow Cabove
          depth2UpperFixedState :=
    ⟨hupperBox,
      criticalCapability_upperFixedState_not_core_content_verdict
        G s δ Cbelow Cabove hupper⟩
  have hupperNot : ¬ R.auditCertifies depth2UpperFixedState := by
    intro haudit
    change criticalCapabilityAgentActs G s δ Cbelow Cabove
      (depth2Step depth2UpperFixedState) at haudit
    rw [depth2Step_upper_fixed] at haudit
    have hverdict :
        criticalCapabilityAuditContentVerdict G s δ Cbelow Cabove
          depth2UpperFixedState := haudit.mp hupper
    exact hupperRejectedDespiteBox.2 hverdict
  intro heq
  exact hupperNot (by simpa [R, heq] using hcoreAudit)

/-- Under the abstract `hinternal` premise, the stable audit certificate
unfolds to the exact `C_star` subcritical inequality.

This theorem honestly records the abstract-premise boundary. The selected
threshold formula is boxed by the supplied `hinternal` assumption through
`criticalCapabilityThresholdAudit_implies_box_at`; the theorem does not
construct `hinternal` for a concrete instance.
-/
theorem criticalCapabilityReflectiveSystem_stable_audit_unfolds_to_subcritical_under_hinternal
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (hinternal :
      reflectiveBox
        (criticalCapabilityThresholdAuditSoundFormula G s δ Cbelow Cabove
          criticalCapabilityStableState)) :
    (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).auditCertifies
        (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).stable ↔
      Cbelow < C_star G s δ := by
  let R := criticalCapabilityReflectiveSystem G s δ Cbelow Cabove
  have hstable : R.stable = criticalCapabilityStableState :=
    criticalCapabilityReflectiveSystem_stable_eq_core G s δ Cbelow Cabove
  have hstep :
      depth2Step criticalCapabilityStableState = criticalCapabilityStableState := by
    simpa [criticalCapabilityStableState] using depth2Step_core_fixed
  constructor
  · intro haudit
    rw [hstable] at haudit
    change criticalCapabilityAgentActs G s δ Cbelow Cabove
      (depth2Step criticalCapabilityStableState) at haudit
    rw [hstep] at haudit
    by_contra hnotSub
    have hnotBelow :
        ¬ criticalCapabilityBelowThreshold G s δ Cbelow Cabove
          criticalCapabilityStableState := by
      simpa [criticalCapabilityBelowThreshold, criticalCapabilityStableState_capability]
        using hnotSub
    have hbox :
        reflectiveBox
          (criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove
            criticalCapabilityStableState) :=
      criticalCapabilityThresholdAudit_implies_box_at
        G s δ Cbelow Cabove criticalCapabilityStableState hinternal
    have hverdict :
        criticalCapabilityAuditContentVerdict G s δ Cbelow Cabove
          criticalCapabilityStableState := by
      simpa [criticalCapabilityAuditContentVerdict, hnotBelow] using hbox
    exact hnotBelow (haudit.mpr hverdict)
  · intro hsub
    rw [hstable]
    change criticalCapabilityAgentActs G s δ Cbelow Cabove
      (depth2Step criticalCapabilityStableState)
    rw [hstep]
    have hbelow :
        criticalCapabilityBelowThreshold G s δ Cbelow Cabove
          criticalCapabilityStableState := by
      simpa [criticalCapabilityBelowThreshold, criticalCapabilityStableState_capability]
        using hsub
    have hbox :
        reflectiveBox
          (criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove
            criticalCapabilityStableState) :=
      criticalCapabilityThresholdAudit_implies_box_at
        G s δ Cbelow Cabove criticalCapabilityStableState hinternal
    have hcontent :
        criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove
            criticalCapabilityStableState =
          encodeAuditCertifiesLattice criticalCapabilityStableState := by
      simp [criticalCapabilityThresholdAuditFormula, hbelow]
    have hverdict :
        criticalCapabilityAuditContentVerdict G s δ Cbelow Cabove
          criticalCapabilityStableState := by
      simpa [criticalCapabilityAuditContentVerdict, hbelow] using
        And.intro hbox hcontent
    exact ⟨fun _hbelow => hverdict, fun _hverdict => hbelow⟩

set_option linter.unreachableTactic false
set_option linter.unusedVariables false

/--
Content gate: removing `hinternal` leaves the stable iff proof without a source
for the threshold-selected boxed formula.

The rejected proof is intentionally goal-shaped: it attempts the actual stable
iff, rewrites through the fixed state and threshold branch, then tries to obtain
the selected box from `reflectiveBox_top`. Track I's above-threshold branch is
not `⊤`, so this is a content failure rather than a mismatched conclusion.
-/
theorem criticalCapabilityReflectiveSystem_without_hinternal_content_gate
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ) :
    True := by
  fail_if_success
    have hiff :
        (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).auditCertifies
            (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).stable ↔
          Cbelow < C_star G s δ := by
      let R := criticalCapabilityReflectiveSystem G s δ Cbelow Cabove
      have hstable : R.stable = criticalCapabilityStableState :=
        criticalCapabilityReflectiveSystem_stable_eq_core G s δ Cbelow Cabove
      have hstep :
          depth2Step criticalCapabilityStableState = criticalCapabilityStableState := by
        simpa [criticalCapabilityStableState] using depth2Step_core_fixed
      constructor
      · intro haudit
        rw [hstable] at haudit
        change criticalCapabilityAgentActs G s δ Cbelow Cabove
          (depth2Step criticalCapabilityStableState) at haudit
        rw [hstep] at haudit
        by_contra hnotSub
        have hnotBelow :
            ¬ criticalCapabilityBelowThreshold G s δ Cbelow Cabove
              criticalCapabilityStableState := by
          simpa [criticalCapabilityBelowThreshold, criticalCapabilityStableState_capability]
            using hnotSub
        have hbox :
            reflectiveBox
              (criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove
                criticalCapabilityStableState) := by
          simpa [criticalCapabilityThresholdAuditFormula, hnotBelow] using reflectiveBox_top
        have hverdict :
            criticalCapabilityAuditContentVerdict G s δ Cbelow Cabove
              criticalCapabilityStableState := by
          simpa [criticalCapabilityAuditContentVerdict, hnotBelow] using hbox
        exact hnotBelow (haudit.mpr hverdict)
      · intro hsub
        rw [hstable]
        change criticalCapabilityAgentActs G s δ Cbelow Cabove
          (depth2Step criticalCapabilityStableState)
        rw [hstep]
        have hbelow :
            criticalCapabilityBelowThreshold G s δ Cbelow Cabove
              criticalCapabilityStableState := by
          simpa [criticalCapabilityBelowThreshold, criticalCapabilityStableState_capability]
            using hsub
        have hbox :
            reflectiveBox
              (criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove
                criticalCapabilityStableState) := by
          simpa [criticalCapabilityThresholdAuditFormula, hbelow] using reflectiveBox_top
        have hcontent :
            criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove
                criticalCapabilityStableState =
              encodeAuditCertifiesLattice criticalCapabilityStableState := by
          simpa [criticalCapabilityThresholdAuditFormula, hbelow]
        have hverdict :
            criticalCapabilityAuditContentVerdict G s δ Cbelow Cabove
              criticalCapabilityStableState := by
          simpa [criticalCapabilityAuditContentVerdict, hbelow] using
            And.intro hbox hcontent
        exact ⟨fun _hbelow => hverdict, fun _hverdict => hbelow⟩
    exact hiff
  trivial

set_option linter.unreachableTactic true
set_option linter.unusedVariables true

/-- Unconditional audit target used only by the Track I content gate. -/
noncomputable def criticalCapabilityUnconditionalAuditFormula
    (x : CriticalCapabilityReflectiveState) :
    ModalFormula (PolicyAtom CriticalCapabilityReflectiveState) :=
  encodeAuditCertifiesLattice x

/-- Unconditional audit verdict used only by the Track I content gate. -/
noncomputable def criticalCapabilityUnconditionalAuditVerdict
    (x : CriticalCapabilityReflectiveState) : Prop :=
  reflectiveBox (criticalCapabilityUnconditionalAuditFormula x) ∧
    criticalCapabilityUnconditionalAuditFormula x =
      encodeAuditCertifiesLattice criticalCapabilityStableState

set_option linter.unreachableTactic false
set_option linter.unusedVariables false

/--
Content gate: replacing the threshold-conditioned modal target by an
unconditional lattice audit target cannot reuse the threshold-Löb premise to
prove the forward branch.
-/
theorem criticalCapabilityReflectiveSystem_unconditional_formula_content_gate
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (hinternal :
      reflectiveBox
        (criticalCapabilityThresholdAuditSoundFormula G s δ Cbelow Cabove
          criticalCapabilityStableState)) :
    True := by
  fail_if_success
    have hforward :
        ((criticalCapabilityBelowThreshold G s δ Cbelow Cabove
              criticalCapabilityStableState ↔
            criticalCapabilityUnconditionalAuditVerdict criticalCapabilityStableState) →
          Cbelow < C_star G s δ) := by
      intro haudit
      by_contra hnotSub
      have hnotBelow :
          ¬ criticalCapabilityBelowThreshold G s δ Cbelow Cabove
            criticalCapabilityStableState := by
        simpa [criticalCapabilityBelowThreshold, criticalCapabilityStableState_capability]
          using hnotSub
      have hbox :
          reflectiveBox
            (criticalCapabilityUnconditionalAuditFormula criticalCapabilityStableState) := by
        simpa [criticalCapabilityThresholdAuditFormula, hnotBelow,
          criticalCapabilityUnconditionalAuditFormula] using
          criticalCapabilityThresholdAudit_implies_box_at
            G s δ Cbelow Cabove criticalCapabilityStableState hinternal
      have hverdict :
          criticalCapabilityUnconditionalAuditVerdict criticalCapabilityStableState := by
        simpa [criticalCapabilityUnconditionalAuditVerdict,
          criticalCapabilityUnconditionalAuditFormula] using
          And.intro hbox rfl
      exact hnotBelow (haudit.mpr hverdict)
    exact hforward
  trivial

set_option linter.unreachableTactic true
set_option linter.unusedVariables true

/--
Build gate for the reverse direction of the restated stable-audit theorem.

The stable audit certificate cannot be supplied by the spectral threshold
alone, nor by the threshold-conditioned Löb box alone. The final line closes
only through the abstract-premise theorem above.
-/
theorem criticalCapabilityReflectiveSystem_reverse_requires_threshold_and_loeb
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (hinternal :
      reflectiveBox
        (criticalCapabilityThresholdAuditSoundFormula G s δ Cbelow Cabove
          criticalCapabilityStableState))
    (hsub : Cbelow < C_star G s δ) :
    (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).auditCertifies
        (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).stable := by
  exact (criticalCapabilityReflectiveSystem_stable_audit_unfolds_to_subcritical_under_hinternal
    G s δ Cbelow Cabove hinternal).mpr hsub

/--
Build gate for the forward direction of the restated stable-audit theorem.

The audit certificate is not a threshold projection from a conjunction. The
proof must pass through the abstract-premise unfolding theorem, whose forward
branch uses the above-threshold modal branch and the spectral threshold
reduction at the stable state.
-/
theorem criticalCapabilityReflectiveSystem_forward_requires_coupled_audit
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (hinternal :
      reflectiveBox
        (criticalCapabilityThresholdAuditSoundFormula G s δ Cbelow Cabove
          criticalCapabilityStableState))
    (haudit :
      (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).auditCertifies
        (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).stable) :
    Cbelow < C_star G s δ := by
  exact (criticalCapabilityReflectiveSystem_stable_audit_unfolds_to_subcritical_under_hinternal
    G s δ Cbelow Cabove hinternal).mp haudit

/-- At positive capability, the stable reflective audit is equivalent to the
deterministic capability-response channel denying the low capability. -/
theorem criticalCapabilityReflectiveSystem_stable_audit_iff_denied
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (hδ : 0 < δ) (hcv : 0 < G.cv s) (hCbelow : 0 < Cbelow)
    (hinternal :
      reflectiveBox
        (criticalCapabilityThresholdAuditSoundFormula G s δ Cbelow Cabove
          criticalCapabilityStableState)) :
    (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).auditCertifies
        (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).stable ↔
      G.capabilityResponse s δ Cbelow = BinaryDecision.Deny := by
  have hauditIff :=
    criticalCapabilityReflectiveSystem_stable_audit_unfolds_to_subcritical_under_hinternal
      G s δ Cbelow Cabove hinternal
  have hresponse :=
    G.capabilityResponse_eq_permit_iff_C_star_le s δ Cbelow hδ hcv hCbelow
  constructor
  · intro haudit
    have hsub : Cbelow < C_star G s δ := hauditIff.mp haudit
    exact (G.capabilityResponse_threshold s δ hδ hcv).1 Cbelow hCbelow hsub
  · intro hdeny
    apply hauditIff.mpr
    by_contra hnot
    have hle : C_star G s δ ≤ Cbelow := le_of_not_gt hnot
    have hpermit : G.capabilityResponse s δ Cbelow = BinaryDecision.Permit :=
      hresponse.mpr hle
    rw [hdeny] at hpermit
    cases hpermit

/-- The erased transient marker is not accepted by the composed agent predicate
once its selected capability is at or above `C_star`. -/
theorem criticalCapabilityReflectiveSystem_aboveTransient_not_agentActs
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cbelow Cabove : ℚ)
    (habove : C_star G s δ ≤ Cabove)
    (hinternal :
      reflectiveBox
        (criticalCapabilityThresholdAuditSoundFormula G s δ Cbelow Cabove
          criticalCapabilityAboveTransientState)) :
    ¬ (criticalCapabilityReflectiveSystem G s δ Cbelow Cabove).agentActs
        criticalCapabilityAboveTransientState := by
  intro hacts
  have hnot : ¬ Cabove < C_star G s δ := not_lt_of_ge habove
  have hnotBelow :
      ¬ criticalCapabilityBelowThreshold G s δ Cbelow Cabove
        criticalCapabilityAboveTransientState := by
    simpa [criticalCapabilityBelowThreshold, criticalCapabilityAboveTransientState_capability]
      using hnot
  have hbox :
      reflectiveBox
        (criticalCapabilityThresholdAuditFormula G s δ Cbelow Cabove
          criticalCapabilityAboveTransientState) :=
    criticalCapabilityThresholdAudit_implies_box_at
      G s δ Cbelow Cabove criticalCapabilityAboveTransientState hinternal
  have hverdict :
      criticalCapabilityAuditContentVerdict G s δ Cbelow Cabove
        criticalCapabilityAboveTransientState := by
    simpa [criticalCapabilityAuditContentVerdict, hnotBelow] using hbox
  exact hnotBelow (hacts.mpr hverdict)

/-- The high-capability transient side receives a Permit response at and above
the exact critical threshold. -/
theorem criticalCapabilityReflectiveSystem_aboveTransient_permit
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ Cabove : ℚ)
    (hδ : 0 < δ) (hcv : 0 < G.cv s) (habove : C_star G s δ ≤ Cabove) :
    G.capabilityResponse s δ Cabove = BinaryDecision.Permit :=
  (G.capabilityResponse_threshold s δ hδ hcv).2 Cabove habove

/-- Concrete Phase C-2 worked instance over the uniform three-node graph. -/
noncomputable def concreteCriticalCapabilityReflectiveSystem :
    ReflectiveGovernanceFixedPointSystem CriticalCapabilityReflectiveState :=
  criticalCapabilityReflectiveSystem uniTriGraph sig (1 / 10) (1 / 20) (1 / 10)

/-- The concrete worked instance has the proper depth-2 stable core. -/
theorem concreteCriticalCapabilityReflectiveSystem_stable_eq_core :
    concreteCriticalCapabilityReflectiveSystem.stable = criticalCapabilityStableState := by
  simpa [concreteCriticalCapabilityReflectiveSystem] using
    criticalCapabilityReflectiveSystem_stable_eq_core
      uniTriGraph sig (1 / 10) (1 / 20) (1 / 10)

/-- Concrete response split: the stable low capability is denied below `C_star`,
while the transient high capability is permitted at `C_star`. -/
theorem concreteCriticalCapabilityReflectiveSystem_response_split :
    uniTriGraph.capabilityResponse sig (1 / 10) (1 / 20) =
        BinaryDecision.Deny ∧
      uniTriGraph.capabilityResponse sig (1 / 10) (1 / 10) =
        BinaryDecision.Permit := by
  have hcv : 0 < uniTriGraph.cv sig := concrete_cv_pos.1
  constructor
  · exact (uniTriGraph.capabilityResponse_threshold sig (1 / 10)
      (by norm_num) hcv).1 (1 / 20) (by norm_num) (by
        have hstar : C_star uniTriGraph sig (1 / 10) = 1 / 10 :=
          concrete_C_star_values.1
        rw [hstar]
        norm_num)
  · exact (uniTriGraph.capabilityResponse_threshold sig (1 / 10)
      (by norm_num) hcv).2 (1 / 10) (by
        have hstar : C_star uniTriGraph sig (1 / 10) = 1 / 10 :=
          concrete_C_star_values.1
        rw [hstar])

/-- Concrete composed equivalence: under the encoded internal soundness premise,
the stable reflective audit is exactly the low-capability Deny response. -/
theorem concreteCriticalCapabilityReflectiveSystem_stable_audit_iff_denied
    (hinternal :
      reflectiveBox
        (criticalCapabilityThresholdAuditSoundFormula uniTriGraph sig (1 / 10) (1 / 20)
          (1 / 10) criticalCapabilityStableState)) :
    concreteCriticalCapabilityReflectiveSystem.auditCertifies
        concreteCriticalCapabilityReflectiveSystem.stable ↔
      uniTriGraph.capabilityResponse sig (1 / 10) (1 / 20) =
        BinaryDecision.Deny := by
  simpa [concreteCriticalCapabilityReflectiveSystem] using
    criticalCapabilityReflectiveSystem_stable_audit_iff_denied
      uniTriGraph sig (1 / 10) (1 / 20) (1 / 10)
      (by norm_num) concrete_cv_pos.1 (by norm_num) hinternal

/--
Build gate: the concrete critical-capability selected box fires through the
substrate class before the response-level theorem consumes it.
-/
example
    (hinternal :
      reflectiveBox
        (criticalCapabilityThresholdAuditSoundFormula uniTriGraph sig (1 / 10) (1 / 20)
          (1 / 10) criticalCapabilityStableState)) :
    reflectiveBox
      (criticalCapabilityThresholdAuditFormula uniTriGraph sig (1 / 10) (1 / 20)
        (1 / 10) criticalCapabilityStableState) :=
  criticalCapabilityThresholdAudit_implies_box_at
    uniTriGraph sig (1 / 10) (1 / 20) (1 / 10) criticalCapabilityStableState hinternal

/--
Concrete coupling exhibit: the threshold-conditioned Löb premise and the
spectral response split jointly certify the stable audit, while the
above-threshold capability is permitted by the same exact `C_star` surface.
-/
theorem concreteCriticalCapabilityReflectiveSystem_threshold_loeb_coupling_exhibit
    (hinternal :
      reflectiveBox
        (criticalCapabilityThresholdAuditSoundFormula uniTriGraph sig (1 / 10) (1 / 20)
          (1 / 10) criticalCapabilityStableState)) :
    concreteCriticalCapabilityReflectiveSystem.auditCertifies
        concreteCriticalCapabilityReflectiveSystem.stable ∧
      uniTriGraph.capabilityResponse sig (1 / 10) (1 / 20) =
        BinaryDecision.Deny ∧
      uniTriGraph.capabilityResponse sig (1 / 10) (1 / 10) =
        BinaryDecision.Permit := by
  have hsplit := concreteCriticalCapabilityReflectiveSystem_response_split
  have hauditIff :=
    concreteCriticalCapabilityReflectiveSystem_stable_audit_iff_denied hinternal
  exact ⟨hauditIff.mpr hsplit.1, hsplit.1, hsplit.2⟩

/-- Concrete transient side: the erased marker is above the stable acceptance
surface and is removed by one reflective transition. -/
theorem concreteCriticalCapabilityReflectiveSystem_transient_above_threshold :
    (hinternal :
      reflectiveBox
        (criticalCapabilityThresholdAuditSoundFormula uniTriGraph sig (1 / 10) (1 / 20)
          (1 / 10) criticalCapabilityAboveTransientState)) →
    ¬ concreteCriticalCapabilityReflectiveSystem.agentActs
        criticalCapabilityAboveTransientState ∧
      concreteCriticalCapabilityReflectiveSystem.step
          criticalCapabilityAboveTransientState =
        criticalCapabilityStableState := by
  intro hinternal
  constructor
  · apply criticalCapabilityReflectiveSystem_aboveTransient_not_agentActs
    have hstar : C_star uniTriGraph sig (1 / 10) = 1 / 10 :=
      concrete_C_star_values.1
    rw [hstar]
    exact hinternal
  · simpa [concreteCriticalCapabilityReflectiveSystem] using
      criticalCapabilityAboveTransient_steps_to_core

end ReflectiveGovernanceFixedPointSystem
end Reflective
end Legitimacy
