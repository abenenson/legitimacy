/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.Impossibility
import Legitimacy.Spectral.Spectral
import Legitimacy.Foundations.Supervision

/-!
# Legitimacy.Protocol.State

Foundational definitions for the spectral governance protocol.

This module defines:

* governance properties and sacrifice bookkeeping
* compilation artifacts and spectral risk witnesses
* the operational protocol state machine and transition relation
-/

set_option autoImplicit false

namespace Legitimacy

/-- The protocol tracks the four graph-diagnostic properties plus the
trace-based non-vacuity obligation from the semantic legitimacy kernel. -/
inductive GovernanceProperty where
  | Consistency       : GovernanceProperty
  | Solidarity        : GovernanceProperty
  | Monotonicity      : GovernanceProperty
  | Strategyproofness : GovernanceProperty
  | NonVacuous        : GovernanceProperty
  deriving Repr, DecidableEq

/-- Whether a governance property holds for a given graph. -/
def ProtocolNonVacuous (graph : GovernanceGraph) : Prop :=
  ∃ (τ : GovernanceTrace)
      (governedClaims permitEligibleClaims : List ClaimQ),
    TraceConsistentWithGraph τ graph ∧
      graph ≠ [] ∧
      governedClaims ≠ [] ∧
      BoundedDisposition τ governedClaims ∧
      permitEligibleClaims ≠ [] ∧
      (∀ c ∈ permitEligibleClaims, c ∈ governedClaims) ∧
      PermitEligible τ permitEligibleClaims ∧
      ¬ Refusal τ ∧
      ¬ PermanentEscalation τ ∧
      ¬ Deadlock τ

/-- Whether a governance property holds for a given graph. -/
def propertyHolds (p : GovernanceProperty) (graph : GovernanceGraph) : Prop :=
  match p with
  | GovernanceProperty.Consistency       => GraphConsistency graph
  | GovernanceProperty.Solidarity        => GraphSolidarity graph
  | GovernanceProperty.Monotonicity      => GraphMonotonicity graph
  | GovernanceProperty.Strategyproofness => GraphStrategyproofness graph
  | GovernanceProperty.NonVacuous        => ProtocolNonVacuous graph

/-- All properties not in the sacrifice list hold for the graph. -/
def NonSacrificedHold (graph : GovernanceGraph)
    (sacrifices : List GovernanceProperty) : Prop :=
  ∀ (p : GovernanceProperty), p ∉ sacrifices → propertyHolds p graph

/-- Every property in the sacrifice list is genuinely violated. -/
def SacrificesJustified (graph : GovernanceGraph)
    (sacrifices : List GovernanceProperty) : Prop :=
  ∀ (p : GovernanceProperty), p ∈ sacrifices → ¬ propertyHolds p graph

/-- A governance graph is well-formed if it has at least one node. -/
def WellFormed (graph : GovernanceGraph) : Prop := graph ≠ []

/-- A governance graph is non-trivial if the four graph-diagnostic properties
cannot all hold simultaneously. Non-vacuity is tracked separately as the fifth
constitutional obligation. -/
def NonTrivial (graph : GovernanceGraph) : Prop :=
  ¬ (GraphConsistency graph ∧ GraphSolidarity graph ∧
     GraphMonotonicity graph ∧ GraphStrategyproofness graph)

/-- The compiler either certifies a property or records it as sacrificed. -/
inductive CompilationVerdict where
  | certified : CompilationVerdict
  | sacrificed : CompilationVerdict
  deriving Repr, DecidableEq

/-- A compilation result records one verdict per governance property. -/
abbrev CompilationReport := GovernanceProperty → CompilationVerdict

/-- Monitoring configuration for a live deployment. -/
structure MonitoringPlan where
  watches : List GovernanceProperty
  deriving Repr

/-- Going live requires monitoring to watch every non-sacrificed property. -/
def MonitoringCovers (monitoring : MonitoringPlan)
    (sacrifices : List GovernanceProperty) : Prop :=
  ∀ (p : GovernanceProperty), p ∉ sacrifices → p ∈ monitoring.watches

/-- A compile step is accepted exactly when the report certifies every
non-sacrificed property and marks every sacrificed property as genuinely
violated. -/
def CompilationChecks (graph : GovernanceGraph)
    (sacrifices : List GovernanceProperty)
    (report : CompilationReport) : Prop :=
  (∀ (p : GovernanceProperty), p ∉ sacrifices →
      report p = CompilationVerdict.certified ∧ propertyHolds p graph) ∧
  (∀ (p : GovernanceProperty), p ∈ sacrifices →
      report p = CompilationVerdict.sacrificed ∧ ¬ propertyHolds p graph)

/-- A successful compilation produces a reusable certificate that the report
precisely refines the declared sacrifice boundary. -/
structure CompiledSacrificeCertificate (graph : GovernanceGraph)
    (sacrifices : List GovernanceProperty)
    (report : CompilationReport) where
  certified_of_nonSacrificed :
    ∀ (p : GovernanceProperty), p ∉ sacrifices →
      report p = CompilationVerdict.certified
  sacrificed_of_listed :
    ∀ (p : GovernanceProperty), p ∈ sacrifices →
      report p = CompilationVerdict.sacrificed
  nonSacrificed_sound : NonSacrificedHold graph sacrifices
  sacrifices_justified : SacrificesJustified graph sacrifices

/-- Deprecated compatibility name for the compiled sacrifice-boundary
certificate stored by `CompiledGovernance`. Use
`CompiledSacrificeCertificate` at new call sites. -/
abbrev CompilationWitness := CompiledSacrificeCertificate

/-- A compiled governance artifact packages the compiled rule together with the
compile-time witness it discharged. -/
structure CompiledGovernance where
  graph : GovernanceGraph
  sacrifices : List GovernanceProperty
  report : CompilationReport
  witness : CompiledSacrificeCertificate graph sacrifices report

/-- A drift report is anchored to the currently live compiled artifact while
pointing to the observed graph that violated one of its non-sacrificed
properties. The observed graph is stored explicitly; otherwise drift would be
inconsistent with `CompiledGovernance.witness`. -/
structure DriftReport (compiled : CompiledGovernance) where
  observed_graph : GovernanceGraph
  violated_property : GovernanceProperty
  not_sacrificed : violated_property ∉ compiled.sacrifices
  violation_proof : ¬ propertyHolds violated_property observed_graph

/-- Passing the compilation checks produces the witness stored by the compiled
artifact. -/
def compileGovernance
    (graph : GovernanceGraph)
    (sacrifices : List GovernanceProperty)
    (report : CompilationReport)
    (hchecks : CompilationChecks graph sacrifices report) :
    CompiledGovernance where
  graph := graph
  sacrifices := sacrifices
  report := report
  witness :=
    { certified_of_nonSacrificed := fun p hp => (hchecks.1 p hp).1
      sacrificed_of_listed := fun p hp => (hchecks.2 p hp).1
      nonSacrificed_sound := fun p hp => (hchecks.1 p hp).2
      sacrifices_justified := fun p hp => (hchecks.2 p hp).2 }

/-- A compiled governance artifact exposes both the report refinement and the
soundness obligations discharged at compile time. -/
theorem compilationChecks_sound
    {graph : GovernanceGraph}
    {sacrifices : List GovernanceProperty}
    {report : CompilationReport}
    (hchecks : CompilationChecks graph sacrifices report) :
    let compiled := compileGovernance graph sacrifices report hchecks
    (∀ (p : GovernanceProperty), p ∉ compiled.sacrifices →
        compiled.report p = CompilationVerdict.certified) ∧
    (∀ (p : GovernanceProperty), p ∈ compiled.sacrifices →
        compiled.report p = CompilationVerdict.sacrificed) ∧
    NonSacrificedHold compiled.graph compiled.sacrifices ∧
    SacrificesJustified compiled.graph compiled.sacrifices := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (hchecks.1 p hp).1
  · intro p hp
    exact (hchecks.2 p hp).1
  · intro p hp
    exact (hchecks.1 p hp).2
  · intro p hp
    exact (hchecks.2 p hp).2

/-- Factor-exposure summary mirroring the Rust protocol risk vector. -/
structure LegitimacyFactorExposure where
  consistency : ℝ
  solidarity : ℝ
  monotonicity : ℝ
  strategyproofness : ℝ
  nonvacuity : ℝ

/-- Rust-parity aliases for the four primary legitimacy-factor coordinates. -/
def LegitimacyFactorExposure.cv (exposure : LegitimacyFactorExposure) : ℝ :=
  exposure.consistency

/-- Rust-parity alias for solidarity exposure. -/
def LegitimacyFactorExposure.sv (exposure : LegitimacyFactorExposure) : ℝ :=
  exposure.solidarity

/-- Rust-parity alias for monotonicity exposure. -/
def LegitimacyFactorExposure.mv (exposure : LegitimacyFactorExposure) : ℝ :=
  exposure.monotonicity

/-- Rust-parity alias for strategyproofness exposure. -/
def LegitimacyFactorExposure.spv (exposure : LegitimacyFactorExposure) : ℝ :=
  exposure.strategyproofness

/-- Risk report produced after the measured phase, mirroring the Rust protocol
format while remaining rich enough for the Lean-side soundness argument. -/
structure GovernanceRiskReport where
  factor_exposure : LegitimacyFactorExposure
  spectral_gap : ℝ
  cv_bound : ℝ
  localizability_bound : ℝ

/-- Compatibility alias matching the research note's `localizability` name. -/
def GovernanceRiskReport.localizability (report : GovernanceRiskReport) : ℝ :=
  report.localizability_bound

/-- A measured report must at least dominate the factor-exposure CV component
and carry some spectral upper bound parameterised by a signal range. -/
structure GovernanceRiskWitness (_compiled : CompiledGovernance)
    (report : GovernanceRiskReport) where
  cv_le_cvBound : report.factor_exposure.cv ≤ report.cv_bound
  signal_range : ℝ
  cv_bound_le_spectral : report.cv_bound ≤ report.spectral_gap⁻¹ * signal_range

/-- The report's CV exposure is controlled by its explicit CV bound. -/
def RiskCalibrated (report : GovernanceRiskReport) : Prop :=
  report.factor_exposure.cv ≤ report.cv_bound

/-- The report's CV bound is certified by some spectral signal-range witness. -/
def SpectrallyBounded (report : GovernanceRiskReport) : Prop :=
  ∃ signal_range : ℝ, report.cv_bound ≤ report.spectral_gap⁻¹ * signal_range

/-- Binary governance pipelines are embedded into a canonical uniformly weighted
carrier of size at least three so the weighted spectral API always has a
non-degenerate removal semantics. -/
def GovernanceGraph.weightedSize (graph : GovernanceGraph) : Nat :=
  max graph.length 3

/-- The canonical weighted carrier associated to a governance graph always has
at least two nodes. -/
lemma GovernanceGraph.weightedSize_atLeastTwo (graph : GovernanceGraph) :
    2 ≤ graph.weightedSize := by
  unfold GovernanceGraph.weightedSize
  omega

/-- The canonical weighted carrier associated to a governance graph always has
at least three nodes. -/
lemma GovernanceGraph.weightedSize_atLeastThree (graph : GovernanceGraph) :
    3 ≤ graph.weightedSize := by
  unfold GovernanceGraph.weightedSize
  omega

instance (graph : GovernanceGraph) : NeZero graph.weightedSize where
  out := by
    unfold GovernanceGraph.weightedSize
    omega

/-- Canonical weighted embedding: a uniform complete graph over the padded
carrier supporting the spectral governance bounds. -/
def GovernanceGraph.toWeighted (graph : GovernanceGraph) :
    GovGraph ℚ graph.weightedSize where
  weights := fun i j => if i = j then 0 else 1
  weight_symm := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, eq_comm]
  weight_nonneg := by
    intro i j
    by_cases hij : i = j <;> simp [hij]
  weight_self_zero := by
    intro i
    simp

/-- Canonical finite claims used to profile a pipeline's stage behavior on a
carrier matching `weightedSize`. -/
def GovernanceGraph.profileClaims (graph : GovernanceGraph) :
    List ClaimQ :=
  (List.finRange graph.weightedSize).map fun i =>
    ⟨i.val, i.val + 1, by
      exact_mod_cast Nat.succ_pos i.val, []⟩

/-- Read stage `i` from the graph, padding with the deny-all node beyond the
concrete pipeline length so the profiled bridge remains total. -/
def GovernanceGraph.profileNode (graph : GovernanceGraph)
    (i : Fin graph.weightedSize) : GovernanceNodeFn :=
  if hi : i.val < graph.length then
    graph.get ⟨i.val, hi⟩
  else
    fun _ _ => BinaryDecision.Deny

/-- Stage-level decision profile over the canonical finite claim set. -/
def GovernanceGraph.profileDecision (graph : GovernanceGraph)
    (i k : Fin graph.weightedSize) : BinaryDecision :=
  graph.profileNode i graph.profileClaims k.val

/-- Agreement score between two profiled stages. Distinct stage behavior on the
canonical claim set therefore produces distinct weighted neighborhoods. -/
def GovernanceGraph.profileAgreementScore (graph : GovernanceGraph)
    (i j : Fin graph.weightedSize) : ℚ :=
  ∑ k : Fin graph.weightedSize,
    if graph.profileDecision i k = graph.profileDecision j k then 1 else 0

private def GovernanceGraph.profileWeight (graph : GovernanceGraph)
    (i j : Fin graph.weightedSize) : ℚ :=
  if _ : i = j then 0 else graph.profileAgreementScore i j

private lemma GovernanceGraph.profileWeight_symm (graph : GovernanceGraph)
    (i j : Fin graph.weightedSize) :
    graph.profileWeight i j = graph.profileWeight j i := by
  by_cases hij : i = j
  · subst hij
    simp [GovernanceGraph.profileWeight]
  · have hji : j ≠ i := by
      intro hji
      exact hij hji.symm
    simp [GovernanceGraph.profileWeight, hij, hji,
      GovernanceGraph.profileAgreementScore, eq_comm]

private lemma GovernanceGraph.profileWeight_nonneg (graph : GovernanceGraph)
    (i j : Fin graph.weightedSize) :
    0 ≤ graph.profileWeight i j := by
  by_cases hij : i = j
  · simp [GovernanceGraph.profileWeight, hij]
  · unfold GovernanceGraph.profileWeight
    simp [hij, GovernanceGraph.profileAgreementScore]

private lemma GovernanceGraph.profileWeight_self_zero (graph : GovernanceGraph)
    (i : Fin graph.weightedSize) :
    graph.profileWeight i i = 0 := by
  simp [GovernanceGraph.profileWeight]

/-- Behavioral weighted embedding for governance pipelines. Unlike the legacy
uniform bridge, this carrier depends on the stage-level decision profile of the
underlying graph on a canonical finite claim set. -/
def GovernanceGraph.toWeightedProfiled (graph : GovernanceGraph) :
    GovGraph ℚ graph.weightedSize where
  weights := graph.profileWeight
  weight_symm := by
    intro i j
    exact graph.profileWeight_symm i j
  weight_nonneg := by
    intro i j
    exact graph.profileWeight_nonneg i j
  weight_self_zero := by
    intro i
    exact graph.profileWeight_self_zero i

/-- The weighted embedding is canonical: every off-diagonal edge has unit
weight. -/
lemma GovernanceGraph.toWeighted_offDiag
    (graph : GovernanceGraph) {i j : Fin graph.weightedSize} (hij : i ≠ j) :
    graph.toWeighted.weights i j = 1 := by
  simp [GovernanceGraph.toWeighted, hij]

/-- The weighted embedding preserves the basic admissibility conditions needed
by the spectral API: a uniform complete graph on a carrier of size at least
three. -/
lemma GovernanceGraph.toWeighted_admissible (graph : GovernanceGraph) :
    3 ≤ graph.weightedSize ∧
      ∀ {i j : Fin graph.weightedSize}, i ≠ j →
        graph.toWeighted.weights i j = 1 := by
  exact ⟨graph.weightedSize_atLeastThree, fun hij => graph.toWeighted_offDiag hij⟩

/-- The spectral perturbation bound lifts verbatim to the binary protocol model
through the canonical weighted embedding. -/
theorem GovernanceGraph.toWeighted_cv_bound
    (graph : GovernanceGraph)
    (s : Fin graph.weightedSize → ℚ)
    (R : ℚ) (hR : 0 ≤ R)
    (hsr : ∀ a b : Fin graph.weightedSize, |s a - s b| ≤ R)
    (hsg : 0 < graph.toWeighted.spectralGap graph.weightedSize_atLeastTwo)
    (k i : Fin graph.weightedSize)
    (hD : 0 < graph.toWeighted.deg i)
    (hD' : 0 < graph.toWeighted.degRemoved k i)
    (hsg_le : graph.toWeighted.spectralGap graph.weightedSize_atLeastTwo ≤
      Rat.cast (graph.toWeighted.deg i)) :
    (Rat.cast |graph.toWeighted.gov s i - graph.toWeighted.govRemoved s k i| : ℝ) ≤
      Rat.cast R * Rat.cast graph.toWeighted.maxDeg /
        graph.toWeighted.spectralGap graph.weightedSize_atLeastTwo := by
  simpa using
    (graph.toWeighted.perturbation_spectral_bound_pointwise
      graph.weightedSize_atLeastTwo s R hR hsr hsg k i hD hD' hsg_le)

/-- The protocol state machine stores the abstract operational phases. It omits
Rust-side persistence metadata, but it does track supervisory interventions
through an explicit `Supervised` phase. -/
inductive ProtocolState where
  | Undeclared : ProtocolState
  | Declared (graph : GovernanceGraph) (sacrifices : List GovernanceProperty) :
      ProtocolState
  | Compiled (compiled : CompiledGovernance) : ProtocolState
  | Measured (compiled : CompiledGovernance) (report : GovernanceRiskReport) :
      ProtocolState
  | Live (compiled : CompiledGovernance) (report : GovernanceRiskReport)
      (monitoring : MonitoringPlan) :
      ProtocolState
  | Supervised (compiled : CompiledGovernance) (report : GovernanceRiskReport)
      (monitoring : MonitoringPlan) (action : SupervisoryAction) :
      ProtocolState
  | Drifted (compiled : CompiledGovernance) (report : DriftReport compiled) :
      ProtocolState
  | Recompiling (orig : CompiledGovernance)
      (orig_report : DriftReport orig) (revised : GovernanceGraph) :
      ProtocolState

/-- Valid protocol transitions. The proof work happens at compile time. -/
inductive ValidTransition : ProtocolState → ProtocolState → Prop where
  | declare
      {graph : GovernanceGraph}
      {sacrifices : List GovernanceProperty}
      (wf : WellFormed graph) :
      ValidTransition
        ProtocolState.Undeclared
        (ProtocolState.Declared graph sacrifices)
  | compile
      {graph : GovernanceGraph}
      {sacrifices : List GovernanceProperty}
      {report : CompilationReport}
      (hchecks : CompilationChecks graph sacrifices report) :
      ValidTransition
        (ProtocolState.Declared graph sacrifices)
        (ProtocolState.Compiled
          (compileGovernance graph sacrifices report hchecks))
  | measure
      {compiled : CompiledGovernance}
      {report : GovernanceRiskReport}
      (hrisk : GovernanceRiskWitness compiled report) :
      ValidTransition
        (ProtocolState.Compiled compiled)
        (ProtocolState.Measured compiled report)
  | go_live
      {compiled : CompiledGovernance}
      {report : GovernanceRiskReport}
      {monitoring : MonitoringPlan}
      (hmonitor : MonitoringCovers monitoring compiled.sacrifices) :
      ValidTransition
        (ProtocolState.Measured compiled report)
        (ProtocolState.Live compiled report monitoring)
  | supervise
      {compiled : CompiledGovernance}
      {report : GovernanceRiskReport}
      {monitoring : MonitoringPlan}
      {action : SupervisoryAction} :
      ValidTransition
        (ProtocolState.Live compiled report monitoring)
        (ProtocolState.Supervised compiled report monitoring action)
  | resupervise
      {compiled : CompiledGovernance}
      {report : GovernanceRiskReport}
      {monitoring : MonitoringPlan}
      {prior next : SupervisoryAction} :
      ValidTransition
        (ProtocolState.Supervised compiled report monitoring prior)
        (ProtocolState.Supervised compiled report monitoring next)
  | drift
      {compiled : CompiledGovernance}
      {report : GovernanceRiskReport}
      {monitoring : MonitoringPlan}
      {drift_report : DriftReport compiled}
      (hwatch : drift_report.violated_property ∈ monitoring.watches) :
      ValidTransition
        (ProtocolState.Live compiled report monitoring)
        (ProtocolState.Drifted compiled drift_report)
  | drift_supervised
      {compiled : CompiledGovernance}
      {report : GovernanceRiskReport}
      {monitoring : MonitoringPlan}
      {action : SupervisoryAction}
      {drift_report : DriftReport compiled}
      (hwatch : drift_report.violated_property ∈ monitoring.watches) :
      ValidTransition
        (ProtocolState.Supervised compiled report monitoring action)
        (ProtocolState.Drifted compiled drift_report)
  | recompile
      {orig : CompiledGovernance}
      {orig_report : DriftReport orig}
      {revised : GovernanceGraph} :
      ValidTransition
        (ProtocolState.Drifted orig orig_report)
        (ProtocolState.Recompiling orig orig_report revised)
  | replant
      {orig : CompiledGovernance}
      {orig_report : DriftReport orig}
      {revised : GovernanceGraph}
      {sacrifices : List GovernanceProperty}
      {report : CompilationReport}
      (hsacrifices : ∀ p : GovernanceProperty, p ∈ orig.sacrifices → p ∈ sacrifices)
      (hchecks : CompilationChecks revised sacrifices report) :
      ValidTransition
        (ProtocolState.Recompiling orig orig_report revised)
        (ProtocolState.Compiled
          (compileGovernance revised sacrifices report hchecks))

/-- Reflexive-transitive closure of valid protocol transitions. -/
inductive TransitionSequence : ProtocolState → ProtocolState → Prop where
  | refl (state : ProtocolState) : TransitionSequence state state
  | tail
      {start : ProtocolState}
      {middle : ProtocolState}
      {finish : ProtocolState}
      (path : TransitionSequence start middle)
      (step : ValidTransition middle finish) :
      TransitionSequence start finish

end Legitimacy
