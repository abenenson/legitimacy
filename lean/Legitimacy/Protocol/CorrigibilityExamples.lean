/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Examples
import Legitimacy.Protocol.Corrigibility

/-!
# Legitimacy.Protocol.CorrigibilityExamples

Illustrative finite examples for
`Legitimacy.Protocol.Corrigibility`. These constructions are not part of the
core protocol theorems; they show how the arbitrary-trajectory corrigibility
result applies to a concrete self-modifying kernel.
-/

set_option autoImplicit false

namespace Legitimacy

private def emergencySupervisoryAlgebra : SupervisoryAlgebra :=
  {σ | σ = SupervisoryAction.pause ∨
    σ = SupervisoryAction.deny ∨
    σ = SupervisoryAction.stop}

private lemma supports_emergency_algebra (S : GovernanceState) :
    SupportsAlgebra S emergencySupervisoryAlgebra := by
  intro σ hσ
  rcases hσ with rfl | rfl | rfl <;> trivial

private inductive ToySelfModStep where
  | rewriteGraph
  | retuneThresholds
  deriving Repr, DecidableEq

private def toySelfModSpace : StateActionSpace where
  Action := ToySelfModStep
  apply step S :=
    match step with
    | .rewriteGraph =>
        { S with
          graph := [denyNode]
          snapshot := S.graph
          paused := false }
    | .retuneThresholds =>
        { S with
          thresholds := S.thresholds ++ [S.degradeFactor] }

private lemma toy_selfmod_single_step_preserved :
    SingleStepPreserved toySelfModSpace emergencySupervisoryAlgebra := by
  intro a S _
  cases a <;> exact supports_emergency_algebra _

private lemma toy_kernel_corrigible :
    Corrigible permitSystem.state toySelfModSpace emergencySupervisoryAlgebra where
  supports_algebra := supports_emergency_algebra permitSystem.state
  single_step_preserved := toy_selfmod_single_step_preserved

/-- A concrete toy kernel with two distinct self-modification step types. -/
private noncomputable def toyKernel : LegitimacyKernel permitSystem :=
  { permitKernel with
    actionSpace := toySelfModSpace
    actionCapability := fun _ => 0
    algebra := emergencySupervisoryAlgebra
    isKernel :=
      { permitKernel.isKernel with
        corrigible :=
          kernelCorrigible_zero _ toy_kernel_corrigible (by intro a; rfl)
        compositionalSafety :=
          LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness _
            permitKernel.compositionalSafety
        nonVacuous :=
          LegitimacyKernelData.kernelNonVacuous_of_nonVacuous _
            permitKernel.nonVacuous } }

/-- The arbitrary-trajectory theorem discharges on a two-step toy adversarial
trajectory whose steps have distinct constructors. -/
private theorem toy_kernel_two_step_trajectory :
    CorrigibilityInvariant
      (applyTrajectory toyKernel
        (show List toyKernel.actionSpace.Action from
          [ToySelfModStep.rewriteGraph, ToySelfModStep.retuneThresholds]))
      toyKernel.algebra := by
  let trajectory : List toyKernel.actionSpace.Action :=
    [ToySelfModStep.rewriteGraph, ToySelfModStep.retuneThresholds]
  exact corrigibility_under_arbitrary_selfmod toyKernel trajectory

end Legitimacy
