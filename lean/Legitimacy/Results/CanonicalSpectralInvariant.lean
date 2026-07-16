/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
-/

import Legitimacy.Impossibility.ConstructiveCompanion
import Legitimacy.Kernel.Class
import Legitimacy.Safety.KernelSafety.GovernanceExamples

/-!
# Legitimacy.Results.CanonicalSpectralInvariant

Canonical finite spectral invariants derived from the diagnostic governance
graph class.

The invariant in this file is intentionally weaker than equality of weighted
topologies: the existing representation relation does not identify the
datum's weighted carrier with a particular canonical carrier. What it does
provide is a finite decoded carrier profile matching the diagnostic graph on
its canonical claim set, and that profile is the canonical class derived here.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A concrete weighted carrier and signal at a fixed carrier size. -/
structure SpectralRealization (n : Nat) where
  G : GovGraph ℚ n
  s : Fin n → ℚ

/-- The decoded spectral-CV class retained by the canonical invariant.

It records the binary readout profile of a spectral realization. This is the
part of the spectral annotation that `SpectralCarrierRepresentsGraph` can
canonically transport from the diagnostic governance graph without adding a
separate spectral-well-connected premise. -/
abbrev SpectralCvClass (n : Nat) : Type :=
  Fin n → BinaryDecision

/-- Decode a spectral realization into its finite carrier decision profile. -/
def spectralCvClass {n : Nat} [NeZero n]
    (R : SpectralRealization n) : SpectralCvClass n :=
  fun i => spectralCarrierDecision R.G R.s i

/-- Size-indexed canonical spectral invariant class. -/
abbrev SpectralInvariantClass : Type :=
  Σ n : Nat, SpectralCvClass n

/-- Fixed three-claim profile used by the quotient-level canonical invariant.

The existing `GovernanceGraphClass` is a quotient by external decision
behavior, so any invariant defined on it must be independent of the syntactic
pipeline length of the representative. This fixed profile is well-defined on
that quotient; the graph-derived `weightedSize` is not. -/
def canonicalThreeClaimProfile : List ClaimQ :=
  [ ⟨0, 1, by norm_num, []⟩
  , ⟨1, 2, by norm_num, []⟩
  , ⟨2, 3, by norm_num, []⟩
  ]

/-- Representative-level three-point decision profile. -/
def governanceGraphThreePointProfile
    (graph : GovernanceGraph) : SpectralInvariantClass :=
  Sigma.mk 3
    (fun i : Fin 3 => graphDecide graph canonicalThreeClaimProfile i.val)

/-- Canonical spectral invariant derived from the diagnostic graph class. -/
noncomputable def canonicalSpectralInvariant :
    GovernanceGraphClass → SpectralInvariantClass :=
  Quotient.lift governanceGraphThreePointProfile (by
    intro G H heq
    unfold governanceGraphThreePointProfile
    congr
    funext i
    exact heq canonicalThreeClaimProfile i.val)

/-- Size-retaining canonical spectral profile at one fixed weighted size. -/
noncomputable def canonicalSpectralInvariantAtSize {n : Nat} :
    GovernanceGraphClassAtSize n → SpectralCvClass n :=
  Quotient.lift
    (fun G : { graph : GovernanceGraph // graph.weightedSize = n } =>
      fun i : Fin n => graphDecide G.1 G.1.profileClaims i.val)
    (by
      intro G H heq
      funext i
      exact heq.2 i)

/-- Size-retaining canonical spectral invariant. Unlike the legacy
`canonicalSpectralInvariant`, this quotient carries the graph-derived carrier
size explicitly. -/
noncomputable def canonicalSizedSpectralInvariant :
    SizedGovernanceGraphClass → SpectralInvariantClass
  | ⟨n, C⟩ => ⟨n, canonicalSpectralInvariantAtSize C⟩

@[simp]
theorem canonicalSizedSpectralInvariant_governanceGraphClass_size
    (graph : GovernanceGraph) :
    (canonicalSizedSpectralInvariant (sizedGovernanceGraphClass graph)).1 =
      graph.weightedSize := by
  rfl

@[simp]
theorem canonicalSizedSpectralInvariant_governanceGraphClass_profile
    (graph : GovernanceGraph) :
    (canonicalSizedSpectralInvariant (sizedGovernanceGraphClass graph)).2 =
      fun i : Fin graph.weightedSize =>
        graphDecide graph graph.profileClaims i.val := by
  rfl

/-! ## Honest restatement: size-indexed target obstruction -/

/-- The quotient-level canonical invariant has the fixed size forced by the
behavioral graph class. This is well-defined on `GovernanceGraphClass`; the
representative's `weightedSize` is not. -/
theorem canonicalSpectralInvariant_governanceGraphClass_size
    (graph : GovernanceGraph) :
    (canonicalSpectralInvariant (governanceGraphClass graph)).1 = 3 := by
  rfl

private def obstructionPermitNode : GovernanceNodeFn :=
  fun _ _ => BinaryDecision.Permit

private def obstructionFiveStagePermitGraph : GovernanceGraph :=
  [ obstructionPermitNode
  , obstructionPermitNode
  , obstructionPermitNode
  , obstructionPermitNode
  , obstructionPermitNode
  ]

private theorem obstructionFiveStagePermitGraph_weightedSize :
    obstructionFiveStagePermitGraph.weightedSize = 5 := by
  rfl

/-- Obstruction to the requested fully size-indexed theorem:
`GovernanceGraphClass` quotients by external decision behavior and therefore
cannot canonically retain the representative's graph-derived carrier size. -/
theorem semanticKernel_spectral_annotation_is_canonical_size_obstruction :
    obstructionFiveStagePermitGraph.weightedSize ≠
      (canonicalSpectralInvariant
        (governanceGraphClass obstructionFiveStagePermitGraph)).1 := by
  rw [obstructionFiveStagePermitGraph_weightedSize,
    canonicalSpectralInvariant_governanceGraphClass_size]
  norm_num

/-- The sized class retains the representative's carrier size, repairing the
specific obstruction that applies to the legacy behavioral quotient. -/
theorem canonicalSizedSpectralInvariant_retains_obstruction_graph_size :
    (canonicalSizedSpectralInvariant
        (sizedGovernanceGraphClass obstructionFiveStagePermitGraph)).1 =
      obstructionFiveStagePermitGraph.weightedSize := by
  rfl

/-! ## Semantic-kernel canonicality -/

/-- The spectral class carried by one kernel datum. -/
noncomputable def kernelSpectralInvariant
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) :
    SpectralInvariantClass :=
  ⟨sys.graph.weightedSize,
    spectralCvClass
      ({ G := D.spectralGraph, s := D.spectralSignal } :
        SpectralRealization sys.graph.weightedSize)⟩

/-- Theorem A, A2 shape: once a runtime kernel is strengthened to a semantic
kernel, the datum's spectral annotation is exactly the canonical retained-size
spectral class of the diagnostic governance graph. Runtime kernel axioms alone
do not imply this; the semantic bridge supplies the carrier-representation
witness. -/
theorem kernel_spectral_class_eq_canonical
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (hsemantic : IsSemanticLegitimacyKernel D) :
    kernelSpectralInvariant D =
      canonicalSizedSpectralInvariant (sizedGovernanceGraphClass sys.graph) := by
  let hcarrier := hsemantic.semanticBridge.carrierRepresentsGraph
  have hrecovered :
      ∀ i : Fin sys.graph.weightedSize,
        spectralCarrierDecision D.spectralGraph D.spectralSignal i =
          graphDecide sys.graph sys.graph.profileClaims i.val :=
    hcarrier.canonicalProfileRecovery sys.graph rfl
      ⟨by intro claims k; rfl, by intro _; rfl⟩
  change
    Sigma.mk sys.graph.weightedSize
        (spectralCvClass
          ({ G := D.spectralGraph, s := D.spectralSignal } :
            SpectralRealization sys.graph.weightedSize)) =
      Sigma.mk sys.graph.weightedSize
        (fun i : Fin sys.graph.weightedSize =>
          graphDecide sys.graph sys.graph.profileClaims i.val)
  refine Sigma.ext rfl ?_
  exact heq_of_eq (funext hrecovered)

/-- Positive worked example for Theorem A: the example semantic kernel's
spectral annotation is canonical for its diagnostic governance graph. -/
theorem worked_example_semantic_kernel_spectral_class_eq_canonical :
    kernelSpectralInvariant Safety.exampleGovernanceKernelData =
      canonicalSizedSpectralInvariant
        (sizedGovernanceGraphClass Safety.exampleGovernedSystem.graph) :=
  kernel_spectral_class_eq_canonical Safety.exampleGovernanceKernelData
    Safety.exampleGovernanceSemanticKernel

/-! ## Worked examples -/

private def invariantDecisionAtZero
    (C : SpectralInvariantClass) : Option BinaryDecision :=
  match C with
  | Sigma.mk 0 _ => none
  | Sigma.mk (n + 1) profile => some (profile ⟨0, Nat.succ_pos n⟩)

private def workedPermitNode : GovernanceNodeFn :=
  fun _ _ => BinaryDecision.Permit

private def workedDenyNode : GovernanceNodeFn :=
  fun _ _ => BinaryDecision.Deny

private def workedPermitGraph : GovernanceGraph :=
  [workedPermitNode]

private def workedDenyGraph : GovernanceGraph :=
  [workedDenyNode]

/-- Floor test: the quotient-level canonical invariant is not constant. -/
theorem canonicalSpectralInvariant_nonconstant_worked_example :
    canonicalSpectralInvariant (governanceGraphClass workedPermitGraph) ≠
      canonicalSpectralInvariant (governanceGraphClass workedDenyGraph) := by
  intro h
  have hdecision := congrArg invariantDecisionAtZero h
  have hleft :
      invariantDecisionAtZero
          (canonicalSpectralInvariant (governanceGraphClass workedPermitGraph)) =
        some BinaryDecision.Permit := by
    rfl
  have hright :
      invariantDecisionAtZero
          (canonicalSpectralInvariant (governanceGraphClass workedDenyGraph)) =
        some BinaryDecision.Deny := by
    rfl
  rw [hleft, hright] at hdecision
  cases hdecision

/-- The two concrete runtime kernel data over the same five-stage diagnostic
graph carry the same decoded spectral decision profile, even though the second
datum widens the signal and is propositionally distinct. -/
theorem worked_example_distinct_kernel_data_same_decoded_spectral_class :
    Safety.exampleGovernanceKernelData ≠
        Safety.exampleGovernanceWideSignalKernelData ∧
      IsLegitimacyKernel Safety.exampleGovernanceKernelData ∧
      IsLegitimacyKernel Safety.exampleGovernanceWideSignalKernelData ∧
      spectralCvClass
        ({ G := Safety.exampleGovernanceKernelData.spectralGraph
           s := Safety.exampleGovernanceKernelData.spectralSignal } :
          SpectralRealization Safety.exampleGovernedSystem.graph.weightedSize) =
        spectralCvClass
        ({ G := Safety.exampleGovernanceWideSignalKernelData.spectralGraph
           s := Safety.exampleGovernanceWideSignalKernelData.spectralSignal } :
          SpectralRealization Safety.exampleGovernedSystem.graph.weightedSize) := by
  refine ⟨Safety.exampleGovernanceWideSignalKernelData_ne,
    Safety.exampleGovernanceRuntimeKernel,
    Safety.exampleGovernanceWideSignalRuntimeKernel, ?_⟩
  funext i
  change spectralCarrierDecision uniK5 sig5 i =
    spectralCarrierDecision uniK5 Safety.exampleGovernanceWideSignal i
  calc
    spectralCarrierDecision uniK5 sig5 i =
        graphDecide Safety.exampleGovernedSystem.graph
          Safety.exampleGovernedSystem.graph.profileClaims i.val :=
      Safety.exampleGovernance_spectralCarrierRepresentsGraph
        |>.decisionProfilePreserved i
    _ = spectralCarrierDecision uniK5 Safety.exampleGovernanceWideSignal i :=
      (Safety.exampleGovernanceWideSignal_spectralCarrierRepresentsGraph
        |>.decisionProfilePreserved i).symm

private def workedExampleZeroSignal :
    Fin Safety.exampleGovernedSystem.graph.weightedSize → ℚ :=
  fun _ => 0

private def workedExampleLayerEval : LayerEval 0 where
  eval := fun L => nomatch L

noncomputable def workedExampleNonKernelNoncanonicalData :
    LegitimacyKernelData Safety.exampleGovernedSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification Safety.exampleGovernedSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent Safety.exampleGovernedSystem.graph
  ObservedState := Unit
  answer := stateGovernanceAnswer Safety.exampleGovernedSystem
  observe := fun _ : GovernanceState => ()
  observeAnswer := fun _ _ => false
  answer_consistent := state_answer_consistent Safety.exampleGovernedSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := uniK5
  spectralSignal := workedExampleZeroSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange workedExampleZeroSignal
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := workedExampleLayerEval
  overrideOvs := []

private lemma workedExample_falseObservation_not_observable :
    ¬ GovernanceObservable
      (stateGovernanceAnswer Safety.exampleGovernedSystem)
      (fun _ _ => false) (fun _ : GovernanceState => ()) := by
  intro hobs
  have h :=
    hobs (GovernanceQuery.ClaimPermitted permitClaim.id) permitState
  simp [stateGovernanceAnswer, Safety.exampleGovernedSystem, permitTrace,
    permitClaim] at h

private theorem workedExample_nonKernel :
    ¬ IsLegitimacyKernel workedExampleNonKernelNoncanonicalData := by
  intro hkernel
  exact workedExample_falseObservation_not_observable hkernel.observable

private theorem workedExample_zeroSignal_noncanonical :
    spectralCvClass
      ({ G := workedExampleNonKernelNoncanonicalData.spectralGraph
         s := workedExampleNonKernelNoncanonicalData.spectralSignal } :
        SpectralRealization Safety.exampleGovernedSystem.graph.weightedSize) ≠
      spectralCvClass
      ({ G := Safety.exampleGovernanceKernelData.spectralGraph
         s := Safety.exampleGovernanceKernelData.spectralSignal } :
        SpectralRealization Safety.exampleGovernedSystem.graph.weightedSize) := by
  intro h
  let i : Fin Safety.exampleGovernedSystem.graph.weightedSize :=
    ⟨0, by native_decide⟩
  have h0 := congrFun h i
  have hzero :
      spectralCarrierDecision uniK5 workedExampleZeroSignal i =
        BinaryDecision.Deny := by
    native_decide
  have hpermit :
      spectralCarrierDecision uniK5 sig5 i = BinaryDecision.Permit := by
    native_decide
  change spectralCarrierDecision uniK5 workedExampleZeroSignal i =
    spectralCarrierDecision uniK5 sig5 i at h0
  rw [hzero, hpermit] at h0
  cases h0

/-- Separation example: the same diagnostic graph admits a runtime kernel datum
with the canonical decoded profile and a non-kernel datum with a noncanonical
spectral annotation. -/
theorem worked_example_nonkernel_noncanonical_same_diagnostic_class :
    IsLegitimacyKernel Safety.exampleGovernanceKernelData ∧
      ¬ IsLegitimacyKernel workedExampleNonKernelNoncanonicalData ∧
      governanceGraphClass Safety.exampleGovernedSystem.graph =
        governanceGraphClass Safety.exampleGovernedSystem.graph ∧
      spectralCvClass
        ({ G := workedExampleNonKernelNoncanonicalData.spectralGraph
           s := workedExampleNonKernelNoncanonicalData.spectralSignal } :
          SpectralRealization Safety.exampleGovernedSystem.graph.weightedSize) ≠
        spectralCvClass
        ({ G := Safety.exampleGovernanceKernelData.spectralGraph
           s := Safety.exampleGovernanceKernelData.spectralSignal } :
          SpectralRealization Safety.exampleGovernedSystem.graph.weightedSize) :=
  ⟨Safety.exampleGovernanceRuntimeKernel, workedExample_nonKernel, rfl,
    workedExample_zeroSignal_noncanonical⟩

end Legitimacy
