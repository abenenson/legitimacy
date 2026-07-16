/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.Corrigibility
import Legitimacy.Attacks.Sovereignty
import Legitimacy.Spectral.CrossScale.RGFlow

/-!
# Legitimacy.Protocol.CorrigibilityRG

Open proof status for RG-basin plus stratification corrigibility iff statements.

In the current tree, `LegitimacyKernel` already bundles a `corrigible` witness.
That makes any theorem whose left-hand side quantifies bounded self-modification
trajectories and asks for `CorrigibilityInvariant` on the resulting state
vacuous as a discriminator: the left-hand side is derivable for every kernel,
independently of any RG or stratification metadata.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Any bounded-trajectory corrigibility predicate over the bundled kernel
reduces to the same universal property: arbitrary self-modification already
preserves the supervisory algebra by construction. -/
abbrev BoundedSelfModCorrigibility
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys)
    (bounded : List K.actionSpace.Action → Prop) : Prop :=
  ∀ trajectory : List K.actionSpace.Action,
    bounded trajectory →
      CorrigibilityInvariant (applyTrajectory K trajectory) K.algebra

/-- The bundled corrigibility axiom makes bounded self-modification
corrigibility automatic for every kernel, regardless of the chosen bound. -/
lemma bounded_selfmod_corrigibility_of_kernel
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys)
    (bounded : List K.actionSpace.Action → Prop) :
    BoundedSelfModCorrigibility K bounded := by
  intro trajectory _
  exact corrigibility_under_arbitrary_selfmod K trajectory

/-- Consequently there is no counterexample kernel, in the current bundled
substrate, whose bounded self-modification trajectory violates the
corrigibility invariant. -/
private lemma no_bounded_selfmod_counterexample
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys)
    (bounded : List K.actionSpace.Action → Prop) :
    ¬ ∃ trajectory : List K.actionSpace.Action,
        bounded trajectory ∧
          ¬ CorrigibilityInvariant (applyTrajectory K trajectory) K.algebra := by
  intro h
  rcases h with ⟨trajectory, hbounded, hbad⟩
  exact hbad (bounded_selfmod_corrigibility_of_kernel K bounded trajectory hbounded)

/-- Any iff theorem with the requested left-hand side shape collapses to its
right-hand side alone, because the left-hand side is already true for every
bundled kernel. -/
private lemma bounded_selfmod_corrigibility_iff_reduces_to_rhs
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys)
    (bounded : List K.actionSpace.Action → Prop)
    (P : Prop) :
    (BoundedSelfModCorrigibility K bounded ↔ P) ↔ P := by
  have hcorr : BoundedSelfModCorrigibility K bounded :=
    bounded_selfmod_corrigibility_of_kernel K bounded
  constructor
  · intro hiff
    exact hiff.mp hcorr
  · intro hP
    constructor
    · intro _
      exact hP
    · intro _
      exact hcorr

/-! ## Extended-substrate analysis on unbundled kernel data

The additive substrate extension makes the displayed iff non-vacuous, but it
also exposes the reason the conjecture fails on the stronger substrate:
spectral basin membership and stratification admissibility do not, by
themselves, constrain the action semantics strongly enough to force algebra
preservation for every bounded trajectory.
-/

private def fiveStagePermitGraph : GovernanceGraph :=
  [thresholdNode 0, thresholdNode 0, thresholdNode 0, thresholdNode 0, thresholdNode 0]

private lemma fiveStagePermitGraph_decides_permit :
    graphDecide fiveStagePermitGraph [permitClaim] permitClaim.id =
      BinaryDecision.Permit := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

private lemma fiveStagePermitTrace_consistent :
    TraceConsistentWithGraph permitTrace fiveStagePermitGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, permitTrace]
  exact ⟨[permitClaim], by simp, fiveStagePermitGraph_decides_permit⟩

/-- Shared 5-stage governed system used by this extended-substrate analysis. Its
binary governance graph has weighted carrier size `5`, matching the concrete
RG witnesses `uniK5`, `bottleneck5`, and `sig5`. -/
abbrev fiveStagePermitSystem : GovernedSystem 1 where
  graph := fiveStagePermitGraph
  state := permitState
  trace := permitTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := fiveStagePermitTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 fiveStagePermitGraph

abbrev ProbeData := LegitimacyKernelData fiveStagePermitSystem

private def probeUniK5 :
    GovGraph ℚ fiveStagePermitSystem.graph.weightedSize :=
  uniK5

private def probeBottleneck5 :
    GovGraph ℚ fiveStagePermitSystem.graph.weightedSize :=
  bottleneck5

private def probeSignal :
    Fin fiveStagePermitSystem.graph.weightedSize → ℚ :=
  sig5

/-- The RG-basin predicate used by this construction: on the 5-node lattice, the
well-connected basin is exactly the depth-3 trajectory value `(10, δ / 10)`. -/
def WellConnectedBasin
    (signal : Fin fiveStagePermitSystem.graph.weightedSize → ℚ)
    (δ : ℚ) :
    Set (GovGraph ℚ fiveStagePermitSystem.graph.weightedSize) :=
  {G | GovGraph.rgTrajectory G signal δ 3 = (10, δ / 10)}

/-- Apply a finite data-level self-modification trajectory to the datum's
shared initial state. -/
abbrev applyDataTrajectory
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) :
    List D.actionSpace.Action → GovernanceState :=
  fun trajectory => D.actionSpace.applySeq trajectory sys.state

/-- A bounded trajectory is one whose every step stays below the Stackelberg
capability threshold declared by the kernel datum. -/
def StackelbergBounded
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (trajectory : List D.actionSpace.Action) : Prop :=
  ∀ a ∈ trajectory,
    0 ≤ D.actionCapability a ∧
      D.actionCapability a ≤ stackelbergValue D.toleranceParameter

/-- Data-level corrigibility preservation means that the shared supervisory
algebra still holds after applying the trajectory to the shared initial state. -/
def corrigibilityPreservedUnder
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (trajectory : List D.actionSpace.Action) : Prop :=
  SupportsAlgebra (applyDataTrajectory D trajectory) D.algebra

/-- Dynamic reroute support after a bounded self-modification trajectory. -/
def hasRerouteSupport (S : GovernanceState) : Prop :=
  SupportsSupervisory S SupervisoryAction.reroute

/-- Dynamic supervisory stability after a bounded self-modification
trajectory: every bounded trajectory preserves the datum's full supervisory
algebra. -/
def SupervisoryStableUnderBoundedTrajectories
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : Prop :=
  ∀ trajectory : List D.actionSpace.Action,
    StackelbergBounded D trajectory →
      corrigibilityPreservedUnder D trajectory

/-- Dynamic RHS candidate: every Stackelberg-bounded trajectory preserves
reroute support. -/
def RerouteStableUnderBoundedTrajectories
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : Prop :=
  ∀ trajectory : List D.actionSpace.Action,
    StackelbergBounded D trajectory →
      hasRerouteSupport (applyDataTrajectory D trajectory)

/-- Right-hand side of the extended-substrate analysis: RG-basin membership plus a
valid stratification certificate. -/
def CorrigibilityStructuralRHS (D : ProbeData) : Prop :=
  D.spectralGraph ∈ WellConnectedBasin D.spectralSignal D.toleranceParameter ∧
    StratificationCertificate D.overrideEval D.overrideOvs

/-- RG-basin and stratification formula over unbundled 5-node data. -/
def corrigibility_iff_RG_basin_and_stratification (D : ProbeData) : Prop :=
  (∀ trajectory : List D.actionSpace.Action,
      StackelbergBounded D trajectory →
        corrigibilityPreservedUnder D trajectory) ↔
    CorrigibilityStructuralRHS D

private def rerouteOnlyAlgebra : SupervisoryAlgebra :=
  {σ | σ = SupervisoryAction.reroute}

private lemma permitState_supports_rerouteOnly :
    SupportsAlgebra permitState rerouteOnlyAlgebra := by
  intro σ hσ
  rcases hσ with rfl
  simp [SupportsSupervisory, permitState]

private lemma supportsAlgebra_rerouteOnly_iff_hasRerouteSupport
    (S : GovernanceState) :
    SupportsAlgebra S rerouteOnlyAlgebra ↔ hasRerouteSupport S := by
  constructor
  · intro hsupp
    exact hsupp (σ := SupervisoryAction.reroute) rfl
  · intro hsupp σ hσ
    rcases hσ with rfl
    exact hsupp

/-- On reroute-only kernels, data-level corrigibility preservation is exactly
reroute support of the post-trajectory state. -/
private lemma corrigibilityPreservedUnder_iff_hasRerouteSupport
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (hAlg : D.algebra = rerouteOnlyAlgebra)
    (trajectory : List D.actionSpace.Action) :
    corrigibilityPreservedUnder D trajectory ↔
      hasRerouteSupport (applyDataTrajectory D trajectory) := by
  simpa [corrigibilityPreservedUnder, hAlg] using
    supportsAlgebra_rerouteOnly_iff_hasRerouteSupport
      (applyDataTrajectory D trajectory)

/-- Stability-based corrigibility iff: on reroute-only kernels, bounded
corrigibility is characterized by bounded preservation of the supervisory
algebra. -/
private lemma corrigibility_iff_supervisory_stable_under_bounded_trajectories
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) :
    (∀ trajectory : List D.actionSpace.Action,
       StackelbergBounded D trajectory →
         corrigibilityPreservedUnder D trajectory) ↔
      SupervisoryStableUnderBoundedTrajectories D := by
  rfl

/-- On reroute-only kernels, the generalized bounded supervisory stability
predicate specializes to reroute stability. -/
private lemma supervisoryStableUnderBoundedTrajectories_iff_rerouteStable
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (hAlg : D.algebra = rerouteOnlyAlgebra) :
    SupervisoryStableUnderBoundedTrajectories D ↔
      RerouteStableUnderBoundedTrajectories D := by
  constructor
  · intro hstable trajectory hbounded
    exact
      (corrigibilityPreservedUnder_iff_hasRerouteSupport D hAlg trajectory).mp
        (hstable trajectory hbounded)
  · intro hstable trajectory hbounded
    exact
      (corrigibilityPreservedUnder_iff_hasRerouteSupport D hAlg trajectory).mpr
        (hstable trajectory hbounded)

/-- Reroute-only corollary of the generalized bounded supervisory stability
iff. -/
private lemma corrigibility_iff_reroute_stable_under_bounded_trajectories
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (hAlg : D.algebra = rerouteOnlyAlgebra) :
    (∀ trajectory : List D.actionSpace.Action,
       StackelbergBounded D trajectory →
         corrigibilityPreservedUnder D trajectory) ↔
      RerouteStableUnderBoundedTrajectories D := by
  exact
    (corrigibility_iff_supervisory_stable_under_bounded_trajectories D).trans
      (supervisoryStableUnderBoundedTrajectories_iff_rerouteStable D hAlg)

private inductive BreakRerouteStep where
  | eraseReroute
  deriving Repr, DecidableEq

private def breakRerouteSpace : StateActionSpace where
  Action := BreakRerouteStep
  apply _ S := { S with reroutePrefix := [] }

private def breakCapability : breakRerouteSpace.Action → ℚ := fun _ => 0

private def breakTrajectory : List breakRerouteSpace.Action :=
  [BreakRerouteStep.eraseReroute]

private lemma stackelbergValue_nonneg
    (δ : ℚ) (hδ : 0 < δ) :
    0 ≤ stackelbergValue δ := by
  have hcv : 0 < uniTriGraph.cv sig := by
    exact fiveGraphLattice_cv_pos (by simp [fiveGraphLattice])
  have huni : 0 ≤ C_star uniTriGraph sig δ := by
    simpa [C_star] using div_nonneg hδ.le hcv.le
  unfold stackelbergValue
  exact le_trans huni (le_max_left _ _)

private lemma stackelbergValue_one_tenth_nonneg :
    0 ≤ stackelbergValue (1 / 10) := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  exact stackelbergValue_nonneg (1 / 10) (by native_decide)

private lemma breakTrajectory_breaks_reroute :
    ¬ SupportsAlgebra
        (breakRerouteSpace.applySeq breakTrajectory permitState)
        rerouteOnlyAlgebra := by
  intro hsupp
  have hreroute := hsupp (σ := SupervisoryAction.reroute) rfl
  simp [breakRerouteSpace, breakTrajectory, StateActionSpace.applySeq,
    SupportsSupervisory] at hreroute

private lemma breakTrajectory_has_no_reroute_support :
    ¬ hasRerouteSupport
        (breakRerouteSpace.applySeq breakTrajectory permitState) := by
  intro hsupp
  exact breakTrajectory_breaks_reroute
    ((supportsAlgebra_rerouteOnly_iff_hasRerouteSupport
      (breakRerouteSpace.applySeq breakTrajectory permitState)).mpr hsupp)

private lemma idActionSpace_applySeq_permitState
    (trajectory : List idActionSpace.Action) (S : GovernanceState) :
    idActionSpace.applySeq trajectory S = S := by
  induction trajectory generalizing S with
  | nil =>
      rfl
  | cons a as ih =>
      simpa [StateActionSpace.applySeq, idActionSpace] using ih S

private def validOverrideEval : LayerEval 1 where
  eval := fun _ _ _ => true

private def validOverride : Override 1 where
  toLayer := 0
  transform := fun d => d

private def validOverrides : List (Override 1) := [validOverride]

private lemma valid_stratification :
    StratificationCertificate validOverrideEval validOverrides := by
  intro ov hov
  simp [validOverrides, validOverride, validOverrideEval] at hov ⊢
  subst hov
  intro L hL d p
  rfl

private def invalidOverrideEval : LayerEval 2 where
  eval := fun L d _ =>
    match L.val, d with
    | 0, Decision3.Permit => true
    | 0, _ => false
    | _, _ => false

private def invalidOverride : Override 2 where
  toLayer := 1
  transform := fun d =>
    match d with
    | Decision3.Permit => Decision3.Deny
    | Decision3.Deny => Decision3.Permit
    | Decision3.Escalate => Decision3.Escalate

private def invalidOverrides : List (Override 2) := [invalidOverride]

private lemma invalid_stratification :
    ¬ StratificationCertificate invalidOverrideEval invalidOverrides := by
  intro hcert
  have hov := hcert invalidOverride (by simp [invalidOverrides])
  have hpres : true = false := by
    simpa [invalidOverrideEval, invalidOverride] using
      hov 0 (by decide) Decision3.Permit GovernanceProperty.Consistency
  cases hpres

private noncomputable def mkProbeData
    {k : ℕ}
    (space : StateActionSpace)
    (alg : SupervisoryAlgebra)
    (cap : space.Action → ℚ)
    (spectralGraph : GovGraph ℚ fiveStagePermitSystem.graph.weightedSize)
    (eval : LayerEval k)
    (ovs : List (Override k)) :
    ProbeData where
  Witness := ReplayWitness
  certification := graphReplayCertification fiveStagePermitSystem.graph
  certification_consistent := graphReplayCertification_consistent fiveStagePermitSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer fiveStagePermitSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer fiveStagePermitSystem
  answer_consistent := state_answer_consistent fiveStagePermitSystem
  actionSpace := space
  algebra := alg
  actionCapability := cap
  spectralGraph := spectralGraph
  spectralSignal := probeSignal
  toleranceParameter := 1 / 10
  signalRange := Legitimacy.signalRange probeSignal
  signalRange_spec := rfl
  stratificationLayers := k
  overrideEval := eval
  overrideOvs := ovs

private noncomputable def mkProbeDataAt
    {k : ℕ}
    (space : StateActionSpace)
    (alg : SupervisoryAlgebra)
    (cap : space.Action → ℚ)
    (spectralGraph : GovGraph ℚ fiveStagePermitSystem.graph.weightedSize)
    (eval : LayerEval k)
    (ovs : List (Override k))
    (δ : ℚ) :
    ProbeData where
  Witness := ReplayWitness
  certification := graphReplayCertification fiveStagePermitSystem.graph
  certification_consistent := graphReplayCertification_consistent fiveStagePermitSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer fiveStagePermitSystem
  observe := fun s : GovernanceState => s
  observeAnswer := stateGovernanceAnswer fiveStagePermitSystem
  answer_consistent := state_answer_consistent fiveStagePermitSystem
  actionSpace := space
  algebra := alg
  actionCapability := cap
  spectralGraph := spectralGraph
  spectralSignal := probeSignal
  toleranceParameter := δ
  signalRange := Legitimacy.signalRange probeSignal
  signalRange_spec := rfl
  stratificationLayers := k
  overrideEval := eval
  overrideOvs := ovs

/-- `uniK5` plus a valid certificate, paired with an inert action space. This
is the requested positive toy. -/
noncomputable def dataGood : ProbeData :=
  mkProbeData idActionSpace rerouteOnlyAlgebra (fun _ => 0)
    probeUniK5 validOverrideEval validOverrides

/-- Basin-only toy: the RG side is good, but stratification fails and a bounded
trajectory destroys algebra support. This witnesses that stratification is
necessary. -/
noncomputable def dataBad_no_strat : ProbeData :=
  mkProbeData breakRerouteSpace rerouteOnlyAlgebra breakCapability
    probeUniK5 invalidOverrideEval invalidOverrides

/-- Stratification-only toy: the certificate holds, but the graph sits in the
bottleneck basin and a bounded trajectory destroys algebra support. This
witnesses that basin membership is necessary. -/
noncomputable def dataBad_wrong_basin : ProbeData :=
  mkProbeData breakRerouteSpace rerouteOnlyAlgebra breakCapability
    probeBottleneck5 validOverrideEval validOverrides

/-- Clean failure witness for the original iff on the extended substrate:
the right-hand side is fully satisfied, but bounded self-modification still
breaks the supervisory algebra because the action semantics are hostile. -/
noncomputable def counterexample_good_rhs_bad_lhs : ProbeData :=
  mkProbeData breakRerouteSpace rerouteOnlyAlgebra breakCapability
    probeUniK5 validOverrideEval validOverrides

/-- The same hostile counterexample kernel, but with a generic positive
tolerance parameter. The action semantics, spectral witness, and
stratification certificate are unchanged; only the RG tolerance is moved. -/
noncomputable def counterexample_good_rhs_bad_lhs_at (δ : ℚ) : ProbeData :=
  mkProbeDataAt breakRerouteSpace rerouteOnlyAlgebra breakCapability
    probeUniK5 validOverrideEval validOverrides δ

private def dataBad_no_strat_breakTrajectory :
    List dataBad_no_strat.actionSpace.Action := [BreakRerouteStep.eraseReroute]

private def dataBad_wrong_basin_breakTrajectory :
    List dataBad_wrong_basin.actionSpace.Action := [BreakRerouteStep.eraseReroute]

private def counterexample_breakTrajectory :
    List counterexample_good_rhs_bad_lhs.actionSpace.Action := [BreakRerouteStep.eraseReroute]

private def counterexample_breakTrajectory_at
    (δ : ℚ) :
    List (counterexample_good_rhs_bad_lhs_at δ).actionSpace.Action :=
  [BreakRerouteStep.eraseReroute]

private lemma dataBad_no_strat_cap_zero :
    dataBad_no_strat.actionCapability BreakRerouteStep.eraseReroute = 0 := rfl

private lemma dataBad_wrong_basin_cap_zero :
    dataBad_wrong_basin.actionCapability BreakRerouteStep.eraseReroute = 0 := rfl

private lemma counterexample_cap_zero :
    counterexample_good_rhs_bad_lhs.actionCapability BreakRerouteStep.eraseReroute = 0 := rfl

private lemma counterexample_cap_zero_at
    (δ : ℚ) :
    (counterexample_good_rhs_bad_lhs_at δ).actionCapability
        BreakRerouteStep.eraseReroute = 0 := rfl

private lemma probeUniK5_in_basin_at
    (δ : ℚ) :
    probeUniK5 ∈ WellConnectedBasin probeSignal δ := by
  change GovGraph.rgTrajectory probeUniK5 probeSignal δ 3 = (10, δ / 10)
  change GovGraph.rgTrajectory uniK5 sig5 δ 3 = (10, δ / 10)
  exact (concrete_iterated_RG_n5_parametric_bridge δ).1

private lemma probeUniK5_in_basin :
    probeUniK5 ∈ WellConnectedBasin probeSignal (1 / 10) := by
  exact probeUniK5_in_basin_at (1 / 10)

private lemma probeBottleneck5_not_in_basin :
    probeBottleneck5 ∉ WellConnectedBasin probeSignal (1 / 10) := by
  unfold WellConnectedBasin
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

private lemma dataGood_lhs :
    ∀ trajectory : List dataGood.actionSpace.Action,
      StackelbergBounded dataGood trajectory →
        corrigibilityPreservedUnder dataGood trajectory := by
  intro trajectory _hbounded
  simpa [dataGood, corrigibilityPreservedUnder, mkProbeData,
    fiveStagePermitSystem, idActionSpace_applySeq_permitState trajectory permitState] using
    permitState_supports_rerouteOnly

private lemma dataGood_rhs :
    CorrigibilityStructuralRHS dataGood := by
  exact ⟨probeUniK5_in_basin, valid_stratification⟩

private lemma dataGood_iff :
    corrigibility_iff_RG_basin_and_stratification dataGood := by
  constructor
  · intro _
    exact dataGood_rhs
  · intro _
    exact dataGood_lhs

private lemma dataGood_dynamic_rhs :
    SupervisoryStableUnderBoundedTrajectories dataGood := by
  exact
    (corrigibility_iff_supervisory_stable_under_bounded_trajectories
      dataGood).mp dataGood_lhs

private lemma dataGood_dynamic_iff :
    (∀ trajectory : List dataGood.actionSpace.Action,
       StackelbergBounded dataGood trajectory →
         corrigibilityPreservedUnder dataGood trajectory) ↔
      SupervisoryStableUnderBoundedTrajectories dataGood := by
  exact
    corrigibility_iff_supervisory_stable_under_bounded_trajectories dataGood

private lemma dataBad_no_strat_rhs_false :
    ¬ CorrigibilityStructuralRHS dataBad_no_strat := by
  intro hrhs
  exact invalid_stratification hrhs.2

private lemma dataBad_no_strat_lhs_false :
    ¬ ∀ trajectory : List dataBad_no_strat.actionSpace.Action,
        StackelbergBounded dataBad_no_strat trajectory →
          corrigibilityPreservedUnder dataBad_no_strat trajectory := by
  intro hall
  have hbounded : StackelbergBounded dataBad_no_strat dataBad_no_strat_breakTrajectory := by
    intro a ha
    have ha' : a = BreakRerouteStep.eraseReroute := by
      exact List.mem_singleton.mp (by simpa [dataBad_no_strat_breakTrajectory] using ha)
    cases ha'
    constructor
    · simp [dataBad_no_strat_cap_zero]
    · rw [dataBad_no_strat_cap_zero]
      exact stackelbergValue_one_tenth_nonneg
  have hpreserved := hall dataBad_no_strat_breakTrajectory hbounded
  exact breakTrajectory_breaks_reroute
    (by
      simpa [corrigibilityPreservedUnder, dataBad_no_strat, mkProbeData,
        dataBad_no_strat_breakTrajectory] using hpreserved)

private lemma dataBad_no_strat_iff :
    corrigibility_iff_RG_basin_and_stratification dataBad_no_strat := by
  constructor
  · intro hlhs
    exact False.elim (dataBad_no_strat_lhs_false hlhs)
  · intro hrhs
    exact False.elim (dataBad_no_strat_rhs_false hrhs)

private lemma dataBad_no_strat_dynamic_rhs_false :
    ¬ RerouteStableUnderBoundedTrajectories dataBad_no_strat := by
  intro hstable
  have hbounded : StackelbergBounded dataBad_no_strat dataBad_no_strat_breakTrajectory := by
    intro a ha
    have ha' : a = BreakRerouteStep.eraseReroute := by
      exact List.mem_singleton.mp (by simpa [dataBad_no_strat_breakTrajectory] using ha)
    cases ha'
    constructor
    · simp [dataBad_no_strat_cap_zero]
    · rw [dataBad_no_strat_cap_zero]
      exact stackelbergValue_one_tenth_nonneg
  have hsupp := hstable dataBad_no_strat_breakTrajectory hbounded
  exact breakTrajectory_has_no_reroute_support
    (by
      simpa [hasRerouteSupport, applyDataTrajectory, dataBad_no_strat, mkProbeData,
        dataBad_no_strat_breakTrajectory] using hsupp)

private lemma dataBad_no_strat_dynamic_iff :
    (∀ trajectory : List dataBad_no_strat.actionSpace.Action,
       StackelbergBounded dataBad_no_strat trajectory →
         corrigibilityPreservedUnder dataBad_no_strat trajectory) ↔
      SupervisoryStableUnderBoundedTrajectories dataBad_no_strat := by
  exact
    corrigibility_iff_supervisory_stable_under_bounded_trajectories
      dataBad_no_strat

private lemma dataBad_wrong_basin_rhs_false :
    ¬ CorrigibilityStructuralRHS dataBad_wrong_basin := by
  intro hrhs
  exact probeBottleneck5_not_in_basin hrhs.1

private lemma dataBad_wrong_basin_lhs_false :
    ¬ ∀ trajectory : List dataBad_wrong_basin.actionSpace.Action,
        StackelbergBounded dataBad_wrong_basin trajectory →
          corrigibilityPreservedUnder dataBad_wrong_basin trajectory := by
  intro hall
  have hbounded :
      StackelbergBounded dataBad_wrong_basin dataBad_wrong_basin_breakTrajectory := by
    intro a ha
    have ha' : a = BreakRerouteStep.eraseReroute := by
      exact List.mem_singleton.mp (by simpa [dataBad_wrong_basin_breakTrajectory] using ha)
    cases ha'
    constructor
    · simp [dataBad_wrong_basin_cap_zero]
    · rw [dataBad_wrong_basin_cap_zero]
      exact stackelbergValue_one_tenth_nonneg
  have hpreserved := hall dataBad_wrong_basin_breakTrajectory hbounded
  exact breakTrajectory_breaks_reroute
    (by
      simpa [corrigibilityPreservedUnder, dataBad_wrong_basin, mkProbeData,
        dataBad_wrong_basin_breakTrajectory] using hpreserved)

private lemma dataBad_wrong_basin_iff :
    corrigibility_iff_RG_basin_and_stratification dataBad_wrong_basin := by
  constructor
  · intro hlhs
    exact False.elim (dataBad_wrong_basin_lhs_false hlhs)
  · intro hrhs
    exact False.elim (dataBad_wrong_basin_rhs_false hrhs)

private lemma dataBad_wrong_basin_dynamic_rhs_false :
    ¬ RerouteStableUnderBoundedTrajectories dataBad_wrong_basin := by
  intro hstable
  have hbounded :
      StackelbergBounded dataBad_wrong_basin dataBad_wrong_basin_breakTrajectory := by
    intro a ha
    have ha' : a = BreakRerouteStep.eraseReroute := by
      exact List.mem_singleton.mp (by simpa [dataBad_wrong_basin_breakTrajectory] using ha)
    cases ha'
    constructor
    · simp [dataBad_wrong_basin_cap_zero]
    · rw [dataBad_wrong_basin_cap_zero]
      exact stackelbergValue_one_tenth_nonneg
  have hsupp := hstable dataBad_wrong_basin_breakTrajectory hbounded
  exact breakTrajectory_has_no_reroute_support
    (by
      simpa [hasRerouteSupport, applyDataTrajectory, dataBad_wrong_basin, mkProbeData,
        dataBad_wrong_basin_breakTrajectory] using hsupp)

private lemma dataBad_wrong_basin_dynamic_iff :
    (∀ trajectory : List dataBad_wrong_basin.actionSpace.Action,
       StackelbergBounded dataBad_wrong_basin trajectory →
         corrigibilityPreservedUnder dataBad_wrong_basin trajectory) ↔
      SupervisoryStableUnderBoundedTrajectories dataBad_wrong_basin := by
  exact
    corrigibility_iff_supervisory_stable_under_bounded_trajectories
      dataBad_wrong_basin

private lemma kernelBadLHS_basin_only :
    dataBad_no_strat.spectralGraph ∈
        WellConnectedBasin dataBad_no_strat.spectralSignal dataBad_no_strat.toleranceParameter ∧
      ¬ StratificationCertificate dataBad_no_strat.overrideEval dataBad_no_strat.overrideOvs ∧
      ∃ trajectory : List dataBad_no_strat.actionSpace.Action,
        StackelbergBounded dataBad_no_strat trajectory ∧
          ¬ corrigibilityPreservedUnder dataBad_no_strat trajectory := by
  refine ⟨probeUniK5_in_basin, invalid_stratification, ?_⟩
  refine ⟨dataBad_no_strat_breakTrajectory, ?_, ?_⟩
  · intro a ha
    have ha' : a = BreakRerouteStep.eraseReroute := by
      exact List.mem_singleton.mp (by simpa [dataBad_no_strat_breakTrajectory] using ha)
    cases ha'
    constructor
    · simp [dataBad_no_strat_cap_zero]
    · rw [dataBad_no_strat_cap_zero]
      exact stackelbergValue_one_tenth_nonneg
  · simpa [corrigibilityPreservedUnder, dataBad_no_strat, mkProbeData] using
      breakTrajectory_breaks_reroute

private lemma kernelBadLHS_strat_only :
    StratificationCertificate dataBad_wrong_basin.overrideEval
        dataBad_wrong_basin.overrideOvs ∧
      dataBad_wrong_basin.spectralGraph ∉
        WellConnectedBasin dataBad_wrong_basin.spectralSignal
          dataBad_wrong_basin.toleranceParameter ∧
      ∃ trajectory : List dataBad_wrong_basin.actionSpace.Action,
        StackelbergBounded dataBad_wrong_basin trajectory ∧
          ¬ corrigibilityPreservedUnder dataBad_wrong_basin trajectory := by
  refine ⟨valid_stratification, probeBottleneck5_not_in_basin, ?_⟩
  refine ⟨dataBad_wrong_basin_breakTrajectory, ?_, ?_⟩
  · intro a ha
    have ha' : a = BreakRerouteStep.eraseReroute := by
      exact List.mem_singleton.mp (by simpa [dataBad_wrong_basin_breakTrajectory] using ha)
    cases ha'
    constructor
    · simp [dataBad_wrong_basin_cap_zero]
    · rw [dataBad_wrong_basin_cap_zero]
      exact stackelbergValue_one_tenth_nonneg
  · simpa [corrigibilityPreservedUnder, dataBad_wrong_basin, mkProbeData] using
      breakTrajectory_breaks_reroute

private lemma counterexample_good_rhs_bad_lhs_rhs :
    CorrigibilityStructuralRHS counterexample_good_rhs_bad_lhs := by
  exact ⟨probeUniK5_in_basin, valid_stratification⟩

private lemma counterexample_good_rhs_bad_lhs_at_rhs
    (δ : ℚ) :
    CorrigibilityStructuralRHS (counterexample_good_rhs_bad_lhs_at δ) := by
  exact ⟨probeUniK5_in_basin_at δ, valid_stratification⟩

private lemma counterexample_good_rhs_bad_lhs_lhs_false :
    ¬ ∀ trajectory : List counterexample_good_rhs_bad_lhs.actionSpace.Action,
        StackelbergBounded counterexample_good_rhs_bad_lhs trajectory →
          corrigibilityPreservedUnder counterexample_good_rhs_bad_lhs trajectory := by
  intro hall
  have hbounded :
      StackelbergBounded counterexample_good_rhs_bad_lhs
        counterexample_breakTrajectory := by
    intro a ha
    have ha' : a = BreakRerouteStep.eraseReroute := by
      exact List.mem_singleton.mp (by simpa [counterexample_breakTrajectory] using ha)
    cases ha'
    constructor
    · simp [counterexample_cap_zero]
    · rw [counterexample_cap_zero]
      exact stackelbergValue_one_tenth_nonneg
  have hpreserved := hall counterexample_breakTrajectory hbounded
  exact breakTrajectory_breaks_reroute
    (by
      simpa [corrigibilityPreservedUnder, counterexample_good_rhs_bad_lhs, mkProbeData] using
        hpreserved)

private lemma counterexample_good_rhs_bad_lhs_at_lhs_false
    (δ : ℚ) (hδ : 0 < δ) :
    ¬ ∀ trajectory : List (counterexample_good_rhs_bad_lhs_at δ).actionSpace.Action,
        StackelbergBounded (counterexample_good_rhs_bad_lhs_at δ) trajectory →
          corrigibilityPreservedUnder (counterexample_good_rhs_bad_lhs_at δ) trajectory := by
  intro hall
  have hbounded :
      StackelbergBounded (counterexample_good_rhs_bad_lhs_at δ)
        (counterexample_breakTrajectory_at δ) := by
    intro a ha
    have ha' : a = BreakRerouteStep.eraseReroute := by
      exact List.mem_singleton.mp (by simpa [counterexample_breakTrajectory_at] using ha)
    cases ha'
    constructor
    · simp [counterexample_cap_zero_at]
    · rw [counterexample_cap_zero_at]
      exact stackelbergValue_nonneg δ hδ
  have hpreserved := hall (counterexample_breakTrajectory_at δ) hbounded
  exact breakTrajectory_breaks_reroute
    (by
      simpa [corrigibilityPreservedUnder, counterexample_good_rhs_bad_lhs_at, mkProbeDataAt] using
        hpreserved)

private lemma counterexample_good_rhs_bad_lhs_dynamic_rhs_false :
    ¬ RerouteStableUnderBoundedTrajectories counterexample_good_rhs_bad_lhs := by
  intro hstable
  have hbounded :
      StackelbergBounded counterexample_good_rhs_bad_lhs
        counterexample_breakTrajectory := by
    intro a ha
    have ha' : a = BreakRerouteStep.eraseReroute := by
      exact List.mem_singleton.mp (by simpa [counterexample_breakTrajectory] using ha)
    cases ha'
    constructor
    · simp [counterexample_cap_zero]
    · rw [counterexample_cap_zero]
      exact stackelbergValue_one_tenth_nonneg
  have hsupp := hstable counterexample_breakTrajectory hbounded
  exact breakTrajectory_has_no_reroute_support
    (by
      simpa [hasRerouteSupport, applyDataTrajectory, counterexample_good_rhs_bad_lhs,
        mkProbeData, counterexample_breakTrajectory] using hsupp)

private lemma counterexample_good_rhs_bad_lhs_static_rhs_dynamic_rhs_false :
    CorrigibilityStructuralRHS counterexample_good_rhs_bad_lhs ∧
      ¬ RerouteStableUnderBoundedTrajectories counterexample_good_rhs_bad_lhs := by
  exact ⟨counterexample_good_rhs_bad_lhs_rhs,
    counterexample_good_rhs_bad_lhs_dynamic_rhs_false⟩

private lemma counterexample_good_rhs_bad_lhs_dynamic_iff :
    (∀ trajectory : List counterexample_good_rhs_bad_lhs.actionSpace.Action,
       StackelbergBounded counterexample_good_rhs_bad_lhs trajectory →
         corrigibilityPreservedUnder counterexample_good_rhs_bad_lhs trajectory) ↔
      SupervisoryStableUnderBoundedTrajectories
        counterexample_good_rhs_bad_lhs := by
  exact
    corrigibility_iff_supervisory_stable_under_bounded_trajectories
      counterexample_good_rhs_bad_lhs

/-- Uniform negative result for the hostile reroute-erasing kernel: every
positive tolerance still admits a datum whose RG-basin and stratification RHS
holds while bounded corrigibility fails on the LHS. -/
theorem RG_basin_stratification_corrigibility_biconditional_fails_parametric
    (δ : ℚ) (hδ : 0 < δ) :
    ∃ D : ProbeData,
      CorrigibilityStructuralRHS D ∧
        ¬ ∀ trajectory : List D.actionSpace.Action,
            StackelbergBounded D trajectory →
              corrigibilityPreservedUnder D trajectory := by
  refine ⟨counterexample_good_rhs_bad_lhs_at δ, ?_, ?_⟩
  · exact counterexample_good_rhs_bad_lhs_at_rhs δ
  · exact counterexample_good_rhs_bad_lhs_at_lhs_false δ hδ

/-- Fixed-witness parametric form of the negative iff, used to recover the
landed `δ = 1 / 10` theorem as a corollary. -/
theorem counterexample_good_rhs_bad_lhs_biconditional_fails_at
    (δ : ℚ) (hδ : 0 < δ) :
    ¬ corrigibility_iff_RG_basin_and_stratification
        (counterexample_good_rhs_bad_lhs_at δ) := by
  intro hiff
  have hRHS := counterexample_good_rhs_bad_lhs_at_rhs δ
  have hLHS := hiff.mpr hRHS
  exact (counterexample_good_rhs_bad_lhs_at_lhs_false δ hδ) hLHS

/-- Clean failure of the extended-substrate formulation: even after extending
the substrate to carry spectral, capability, and stratification data, the
displayed iff is false on a concrete kernel datum with RHS true and LHS false.
This is the
`δ = 1 / 10` corollary of the parametric witness. -/
theorem RG_basin_stratification_corrigibility_biconditional_fails :
    ¬ corrigibility_iff_RG_basin_and_stratification
        counterexample_good_rhs_bad_lhs := by
  simpa [counterexample_good_rhs_bad_lhs, counterexample_good_rhs_bad_lhs_at,
    mkProbeData, mkProbeDataAt] using
    counterexample_good_rhs_bad_lhs_biconditional_fails_at
      -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
      (1 / 10) (by native_decide)

end Legitimacy
