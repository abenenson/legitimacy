/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Results.BifurcationKernel
import Legitimacy.Protocol.CorrigibilityRG
import Legitimacy.Spectral.CrossScale.ASIUniversality
import Legitimacy.Spectral.ASIBridge.FamilyAlignment

/-!
# Legitimacy.Results.ASIGovernanceReliability

Joint packaging of the current spectral-capacity and corrigibility APIs.

The present tree now contains a scoped bridge from concrete
size-indexed ASI spectral-signature witnesses to kernel-side semantic
invariants. For kernel data aligned with a native ASI family carrier, the
bridge derives the
signature-to-kernel spectral lift from the alignment fields rather than taking
it as a caller hypothesis. This is not yet a substrate-wide free theorem from
ASI spectral signatures to every kernel datum. The self-modification side is
also constrained by the current bundling design:
`LegitimacyKernel` already carries a corrigibility witness, so bounded
self-modification preservation is automatic for the witness kernel.

Accordingly, the nontrivial content of the theorem below is the spectral side:
below the bifurcation boundary, the graph remains in spectral stable
equilibrium at the adversarial capability level, while the concrete
five-axiom witness kernel can be packaged alongside that bound and any
Stackelberg-bounded self-modification trajectory preserves its algebra.

## §10 Frontier

To recover a substrate-wide ASI-governance bridge, the library still needs
native spectral certificates for broader structural classes beyond the
complete-symmetric carrier predicate. The hypothesis-free native bridge is
scoped to `FamilyAlignedKernelData`.
-/

set_option autoImplicit false

namespace Legitimacy

/-- The bounded-trajectory predicate specialized to the concrete permit-kernel
action space used by the existing kernel-side bifurcation witness. -/
abbrev PermitTrajectoryBound :
    List permitKernel.actionSpace.Action → Prop :=
  StackelbergBounded permitKernel.toLegitimacyKernelData

/-- Joint adversary for the current subcritical packaging API: external
capability scaling is tracked by `κ`, while bounded self-modification is a
concrete permit-kernel action trajectory. -/
structure JointSubcriticalAdversary where
  κ : ℚ
  κ_pos : 0 < κ
  trajectory : List permitKernel.actionSpace.Action
  trajectory_bounded : PermitTrajectoryBound trajectory

/-- On the bundled witness kernel, bounded self-modification corrigibility is
uniform: every Stackelberg-bounded trajectory preserves the supervisory
algebra. This is automatic in the current design because `permitKernel`
already bundles corrigibility. -/
lemma permitKernel_bounded_selfmod_corrigibility :
    BoundedSelfModCorrigibility permitKernel PermitTrajectoryBound :=
  bounded_selfmod_corrigibility_of_kernel permitKernel PermitTrajectoryBound

/-- Subcritical packaging theorem for the current API.

The present proof packages the already-landed spectral bifurcation and
bundled-kernel corrigibility results. The headline mathematical content is the
joint packaging: subcritical capability scaling gives spectral stability, and
the witness kernel survives any Stackelberg-bounded self-modification
trajectory. -/
theorem subcritical_spectral_kernel_packaging
    (KernelBridge : KernelLFEBridge)
    {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (δ : ℚ)
    (hδ : 0 < δ)
    (adv : JointSubcriticalAdversary)
    (hbelow : BelowBifurcationBoundary G s δ adv.κ)
    (hbridge : KernelBridge permitKernel δ) :
    (G.capacity s δ ∧ 0 < G.cv s ∧ SpectralStableEquilibrium G s δ adv.κ) ∧
      (∀ A : KernelAxiom, SatisfiesAxiom permitKernel A) ∧
      KernelBridge permitKernel δ ∧
      CorrigibilityInvariant
        (applyTrajectory permitKernel adv.trajectory) permitKernel.algebra := by
  have hcorr :
      CorrigibilityInvariant
        (applyTrajectory permitKernel adv.trajectory) permitKernel.algebra :=
    permitKernel_bounded_selfmod_corrigibility
      adv.trajectory adv.trajectory_bounded
  exact
    ⟨(bifurcation_iff_spectral G s δ adv.κ hδ).mp hbelow,
      permitKernel_satisfies_all_axioms,
      hbridge,
      hcorr⟩

/-- Concrete `n = 5` firing of the subcritical packaging theorem on `uniK5` at the
already-decided parameter choice `(δ, κ) = (80, 1)`. The self-modification
side is specialized to any Stackelberg-bounded trajectory on `permitKernel`. -/
theorem uniK5_subcritical_spectral_kernel_packaging
    (KernelBridge : KernelLFEBridge)
    (trajectory : List permitKernel.actionSpace.Action)
    (hbounded : PermitTrajectoryBound trajectory)
    (hbridge : KernelBridge permitKernel 80) :
    (uniK5.capacity sig5 80 ∧ 0 < uniK5.cv sig5 ∧
        SpectralStableEquilibrium uniK5 sig5 80 1) ∧
      (∀ A : KernelAxiom, SatisfiesAxiom permitKernel A) ∧
      KernelBridge permitKernel 80 ∧
      CorrigibilityInvariant
        (applyTrajectory permitKernel trajectory) permitKernel.algebra := by
  let adv : JointSubcriticalAdversary :=
    { κ := 1
      κ_pos := by norm_num
      trajectory := trajectory
      trajectory_bounded := hbounded }
  have hδ : 0 < (80 : ℚ) := by norm_num
  have hbelow : BelowBifurcationBoundary uniK5 sig5 80 adv.κ := by
    simpa [adv] using (concrete_bifurcation_n5).1
  simpa [adv] using
    subcritical_spectral_kernel_packaging KernelBridge uniK5 sig5 80 hδ
      adv hbelow hbridge

/-- Concrete `n = 5` package that materially combines the landed ASI spectral
signature with the honest subcritical spectral-plus-kernel packaging theorem. -/
theorem uniK5_subcritical_packaging_with_positive_n5_rg_signature
    (KernelBridge : KernelLFEBridge)
    (trajectory : List permitKernel.actionSpace.Action)
    (hbounded : PermitTrajectoryBound trajectory)
    (hbridge : KernelBridge permitKernel 80) :
    ASISpectralSignature 80 (GovGraph.rgTrajectory uniK5 sig5 80 3) ∧
      (uniK5.capacity sig5 80 ∧ 0 < uniK5.cv sig5 ∧
        SpectralStableEquilibrium uniK5 sig5 80 1) ∧
      (∀ A : KernelAxiom, SatisfiesAxiom permitKernel A) ∧
      KernelBridge permitKernel 80 ∧
      CorrigibilityInvariant
        (applyTrajectory permitKernel trajectory) permitKernel.algebra := by
  have hsig :
      ASISpectralSignature 80 (GovGraph.rgTrajectory uniK5 sig5 80 3) :=
    (concrete_iterated_RG_n5_universality 80 (by norm_num)).1
  exact ⟨hsig,
    uniK5_subcritical_spectral_kernel_packaging
      KernelBridge trajectory hbounded hbridge⟩

/-- Native scoped ASI bridge toy case. This routes the concrete depth-3 `uniK5`
ASI signature into the semantic-kernel invariant target for the existing
five-node example governance kernel through the family-aligned corollary, so no
explicit signature-to-kernel spectral lift is supplied by the caller. -/
theorem uniK5_native_asi_kernelInvariant_toy_case :
    Safety.KernelInvariant Safety.exampleGovernanceKernelData :=
  ASIBridge.uniK5_family_aligned_native_asi_signature_kernelInvariant

/-- Seven-node complete-carrier semantic invariant from family alignment. This
uses the `uniK7` carrier's own spectral well-connected discharge rather than
reusing the `uniK5` proof. -/
theorem uniK7_family_aligned_kernelInvariant_complete_carrier :
    Safety.KernelInvariant ASIBridge.uniK7FamilyKernelData :=
  ASIBridge.uniK7_family_aligned_kernelInvariant

/-- Seven-node complete-carrier native ASI bridge theorem. The concrete
seven-node ASI signature is discharged internally from the native RG witness. -/
theorem uniK7_native_asi_kernelInvariant_complete_carrier :
    Safety.KernelInvariant ASIBridge.uniK7FamilyKernelData :=
  ASIBridge.uniK7_family_aligned_native_asi_signature_kernelInvariant

/-- Nine-node complete-carrier semantic invariant from family alignment. This
uses the `uniK9` carrier's own spectral well-connected discharge rather than
reusing the `uniK5` or `uniK7` proofs. -/
theorem uniK9_family_aligned_kernelInvariant_complete_carrier :
    Safety.KernelInvariant ASIBridge.uniK9FamilyKernelData :=
  ASIBridge.uniK9_family_aligned_kernelInvariant

/-- Nine-node complete-carrier native ASI bridge theorem. The concrete
nine-node ASI signature is discharged internally from the native RG witness. -/
theorem uniK9_native_asi_kernelInvariant_complete_carrier :
    Safety.KernelInvariant ASIBridge.uniK9FamilyKernelData :=
  ASIBridge.uniK9_family_aligned_native_asi_signature_kernelInvariant

end Legitimacy
