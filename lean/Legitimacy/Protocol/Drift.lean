/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.Soundness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Legitimacy.Protocol.Drift

Drift and recompilation theorems for the spectral governance protocol.

This module proves:

* drift evidence is preserved through recompilation
* finite termination of a recompile cycle once checks are discharged
* a concrete `peerGraph` lifecycle that detects drift and recompiles
-/

set_option autoImplicit false

namespace Legitimacy

/-- A drifted state explicitly carries a non-sacrificed property that fails on
the observed graph. -/
theorem drifted_implies_violation_evidence
    (compiled : CompiledGovernance) (report : DriftReport compiled) :
    ∃ p : GovernanceProperty,
      p ∉ compiled.sacrifices ∧
        ¬ propertyHolds p report.observed_graph := by
  exact ⟨report.violated_property, report.not_sacrificed, report.violation_proof⟩

/-- Proposing a revision does not erase the witness that justified entering the
recompile loop. -/
lemma recompiling_preserves_drift_evidence
    (orig : CompiledGovernance) (orig_report : DriftReport orig)
    (_revised : GovernanceGraph) :
    ∃ p : GovernanceProperty,
      p ∉ orig.sacrifices ∧
        ¬ propertyHolds p orig_report.observed_graph := by
  exact drifted_implies_violation_evidence orig orig_report

/-- Any successful replant either explicitly sacrifices the violated property
or proves that the revised graph satisfies it. -/
theorem recompiling_must_address_drift
    {orig : CompiledGovernance}
    {orig_report : DriftReport orig}
    {revised : GovernanceGraph}
    {sacrifices : List GovernanceProperty}
    {report : CompilationReport}
    (hchecks : CompilationChecks revised sacrifices report) :
    orig_report.violated_property ∈ sacrifices ∨
      propertyHolds orig_report.violated_property revised := by
  by_cases hp : orig_report.violated_property ∈ sacrifices
  · exact Or.inl hp
  · exact Or.inr ((hchecks.1 _ hp).2)

/-- A simple ranking that makes the recompile loop's finite resolution
explicit. -/
def RecompileDepth : ProtocolState → Nat
  | ProtocolState.Drifted _ _ => 2
  | ProtocolState.Recompiling _ _ _ => 1
  | _ => 0

/-- Entering the recompile loop guarantees a finite path back to a compiled
state once a revised graph discharges the compile checks. -/
theorem recompile_cycle_terminates_drifted
    {orig : CompiledGovernance}
    {report : DriftReport orig}
    {revised : GovernanceGraph}
    {sacrifices : List GovernanceProperty}
    {compilation_report : CompilationReport}
    (hsacrifices : ∀ p : GovernanceProperty, p ∈ orig.sacrifices → p ∈ sacrifices)
    (hchecks : CompilationChecks revised sacrifices compilation_report) :
    ∃ compiled' : CompiledGovernance,
      TransitionSequence
          (ProtocolState.Drifted orig report)
          (ProtocolState.Compiled compiled') ∧
        RecompileDepth (ProtocolState.Drifted orig report) = 2 ∧
        RecompileDepth (ProtocolState.Compiled compiled') = 0 := by
  let compiled' := compileGovernance revised sacrifices compilation_report hchecks
  refine ⟨compiled', ?_, rfl, rfl⟩
  refine TransitionSequence.tail
    (TransitionSequence.tail
      (TransitionSequence.refl _)
      ValidTransition.recompile)
    (ValidTransition.replant hsacrifices hchecks)

private def scaleClaims (α : ℚ) (hα : 0 < α) (claims : List ClaimQ) :
    List ClaimQ :=
  claims.map (fun c => ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)

private theorem lookupStrength_scaleClaims
    (claims : List ClaimQ) (k : ClaimantId) (α : ℚ) (hα : 0 < α) :
    lookupStrength k (scaleClaims α hα claims) = α * lookupStrength k claims := by
  induction claims with
  | nil =>
      simp [scaleClaims, lookupStrength]
  | cons c cs ih =>
      by_cases hk : c.id = k
      · simp [scaleClaims, lookupStrength, hk]
      · simpa [scaleClaims, lookupStrength, hk] using ih

private theorem countAtMost_scaleClaims
    (claims : List ClaimQ) (α : ℚ) (hα : 0 < α) (s : ℚ) :
    countAtMost (scaleClaims α hα claims) (α * s) = countAtMost claims s := by
  induction claims with
  | nil =>
      simp [countAtMost, scaleClaims]
  | cons c cs ih =>
      by_cases hcs : c.strength ≤ s
      · have hscaled : α * c.strength ≤ α * s := by
          nlinarith
        simpa [countAtMost, scaleClaims, hcs, hscaled] using ih
      · have hscaled : ¬ α * c.strength ≤ α * s := by
          intro h
          apply hcs
          nlinarith
        simpa [countAtMost, scaleClaims, hcs, hscaled] using ih

private theorem peerGraph_solidary : GraphSolidarity peerGraph := by
  intro claims α hα j hj
  change
    graphDecide peerGraph claims j =
      graphDecide peerGraph (scaleClaims α hα claims) j
  have hlookup :
      lookupStrength j (scaleClaims α hα claims) = α * lookupStrength j claims := by
    simpa using lookupStrength_scaleClaims claims j α hα
  have hcount :
      countAtMost (scaleClaims α hα claims) (α * lookupStrength j claims) =
        countAtMost claims (lookupStrength j claims) := by
    simpa using countAtMost_scaleClaims claims α hα (lookupStrength j claims)
  rw [show graphDecide peerGraph claims j =
      if 2 * countAtMost claims (lookupStrength j claims) ≥ claims.length then
        BinaryDecision.Permit else BinaryDecision.Deny by
        simp [peerGraph, graphDecide, peerRelativeNode]
        split_ifs <;> rfl
    , show graphDecide peerGraph (scaleClaims α hα claims) j =
      if
          2 *
              countAtMost (scaleClaims α hα claims)
                (lookupStrength j (scaleClaims α hα claims)) ≥
            (scaleClaims α hα claims).length then
        BinaryDecision.Permit else BinaryDecision.Deny by
        simp [peerGraph, graphDecide, peerRelativeNode]
        split_ifs <;> rfl]
  rw [hlookup, hcount]
  simp [scaleClaims]

/-- The peer-relative graph is non-trivial. -/
lemma peerGraph_nontrivial : NonTrivial peerGraph :=
  peerGraph_impossibility

private def consA : ClaimQ := ⟨0, 1/4, by norm_num, []⟩
private def consB : ClaimQ := ⟨1, 1/2, by norm_num, []⟩
private def consC : ClaimQ := ⟨2, 3/4, by norm_num, []⟩
private def consD : ClaimQ := ⟨3, 1, by norm_num, []⟩
private def consClaims : List ClaimQ := [consA, consB, consC, consD]

private theorem consClaims_distinct : ClaimsDistinct consClaims := by
  unfold ClaimsDistinct consClaims consA consB consC consD
  show ([0, 1, 2, 3] : List Nat).Nodup
  exact List.nodup_cons.mpr ⟨by decide, List.nodup_cons.mpr ⟨by decide,
    List.nodup_cons.mpr ⟨by decide,
    List.nodup_cons.mpr ⟨by decide, List.Pairwise.nil⟩⟩⟩⟩

private theorem a_in_consClaims : InClaims 0 consClaims :=
  ⟨consA, List.Mem.head _, rfl⟩

private theorem b_in_consClaims : InClaims 1 consClaims :=
  ⟨consB, List.Mem.tail _ (List.Mem.head _), rfl⟩

private theorem a_denied_cons :
    graphDecide peerGraph consClaims 0 = BinaryDecision.Deny := by
  show graphDecide [peerRelativeNode] consClaims 0 = BinaryDecision.Deny
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

private theorem b_permitted_cons :
    graphDecide peerGraph consClaims 1 = BinaryDecision.Permit := by
  show graphDecide [peerRelativeNode] consClaims 1 = BinaryDecision.Permit
  native_decide

private theorem b_denied_after_remove_a :
    graphDecide peerGraph (removeClaimGraph 0 consClaims) 1 = BinaryDecision.Deny := by
  show graphDecide [peerRelativeNode] (removeClaimGraph 0 consClaims) 1 =
    BinaryDecision.Deny
  native_decide

private def permitAllNode : GovernanceNodeFn := fun _ _ => BinaryDecision.Permit

private def permitAllGraph : GovernanceGraph := [permitAllNode]

private theorem permitAllGraph_wellFormed : WellFormed permitAllGraph := by
  simp [WellFormed, permitAllGraph]

private theorem permitAllGraph_consistent : GraphConsistency permitAllGraph := by
  intro claims k j hk hj hkj hdist hden
  simp [permitAllGraph, permitAllNode, graphDecide] at hden

private theorem permitAllGraph_solidary : GraphSolidarity permitAllGraph := by
  intro claims α hα j hj
  simp [permitAllGraph, permitAllNode, graphDecide]

private theorem permitAllGraph_monotone : GraphMonotonicity permitAllGraph := by
  intro claims k s' hs' j hk hdist hle hperm
  simp [permitAllGraph, permitAllNode, graphDecide]

private theorem permitAllGraph_strategyproof : GraphStrategyproofness permitAllGraph := by
  intro claims k s_r hs_r hk hdist hperm
  simp [permitAllGraph, permitAllNode, graphDecide]

private def permitAllClaim : ClaimQ := ⟨0, 1, by norm_num, []⟩

private def permitAllTrace : GovernanceTrace :=
  fun _ => (permitAllClaim, some GovernanceOutcome.permit)

private theorem permitAllTrace_consistent :
    TraceConsistentWithGraph permitAllTrace permitAllGraph := by
  intro t
  refine ⟨[permitAllClaim], ?_, ?_⟩
  · simp [permitAllTrace]
  · simp [permitAllTrace, permitAllGraph, permitAllNode, graphDecide]

private theorem permitAllTrace_bounded :
    BoundedDisposition permitAllTrace [permitAllClaim] := by
  refine ⟨0, ?_⟩
  intro c hc
  simp at hc
  subst hc
  exact ⟨0, le_rfl, Or.inl (by simp [permitAllTrace])⟩

private theorem permitAllTrace_permitEligible :
    PermitEligible permitAllTrace [permitAllClaim] := by
  intro c hc
  simp at hc
  subst hc
  exact ⟨0, by simp [permitAllTrace]⟩

private theorem permitAllTrace_notRefusal : ¬ Refusal permitAllTrace := by
  intro hrefusal
  have h0 := hrefusal 0
  simp [permitAllTrace] at h0

private theorem permitAllTrace_notPermanentEscalation :
    ¬ PermanentEscalation permitAllTrace := by
  intro hesc
  have h0 := hesc 0
  simp [permitAllTrace] at h0

private theorem permitAllTrace_notDeadlock : ¬ Deadlock permitAllTrace := by
  intro hdead
  have h0 := hdead 0
  simp [permitAllTrace] at h0

private theorem permitAllGraph_nonvacuous :
    ProtocolNonVacuous permitAllGraph := by
  refine ⟨permitAllTrace, [permitAllClaim], [permitAllClaim], ?_⟩
  exact ⟨permitAllTrace_consistent, permitAllGraph_wellFormed, by simp,
    permitAllTrace_bounded, by simp, by
      intro c hc
      simp at hc
      simp [hc],
    permitAllTrace_permitEligible,
    permitAllTrace_notRefusal,
    permitAllTrace_notPermanentEscalation,
    permitAllTrace_notDeadlock⟩

private def permitAllCompilationReport : CompilationReport := fun _ =>
  CompilationVerdict.certified

private theorem permitAllCompilationChecks :
    CompilationChecks permitAllGraph [] permitAllCompilationReport := by
  constructor
  · intro p hp
    cases p <;> simp [permitAllCompilationReport, propertyHolds,
      permitAllGraph_consistent, permitAllGraph_solidary,
      permitAllGraph_monotone, permitAllGraph_strategyproof,
      permitAllGraph_nonvacuous]
  · intro p hp
    simp at hp

/-- Declared sacrifices for the public `peerGraph` deployment artifact. -/
def peerGraphRevisedSacrifices : List GovernanceProperty :=
  [ GovernanceProperty.Consistency
  , GovernanceProperty.Monotonicity
  , GovernanceProperty.Strategyproofness
  ]

/-- Compilation report for the public sacrificed `peerGraph` artifact. -/
def peerGraphRevisedReport : CompilationReport := fun p =>
  if p ∈ peerGraphRevisedSacrifices then
    CompilationVerdict.sacrificed
  else
    CompilationVerdict.certified

/-- Compilation checks for the sacrificed `peerGraph` artifact. -/
theorem peerGraphRevisedChecks :
    CompilationChecks peerGraph peerGraphRevisedSacrifices peerGraphRevisedReport := by
  constructor
  · intro p hp
    cases p <;> simp [peerGraphRevisedSacrifices, peerGraphRevisedReport] at hp ⊢
    exact peerGraph_solidary
    · let peerTrace : GovernanceTrace :=
        fun _ => (consB, some GovernanceOutcome.permit)
      have hconsistent : TraceConsistentWithGraph peerTrace peerGraph := by
        intro t
        refine ⟨consClaims, ?_, ?_⟩
        · exact List.Mem.tail _ (List.Mem.head _)
        · simpa [peerTrace] using b_permitted_cons
      have hbounded : BoundedDisposition peerTrace [consB] := by
        refine ⟨0, ?_⟩
        intro c hc
        simp at hc
        subst hc
        exact ⟨0, le_rfl, Or.inl (by simp [peerTrace])⟩
      have hpermit : PermitEligible peerTrace [consB] := by
        intro c hc
        simp at hc
        subst hc
        exact ⟨0, by simp [peerTrace]⟩
      have hnotRefusal : ¬ Refusal peerTrace := by
        intro hrefusal
        have h0 := hrefusal 0
        simp [peerTrace] at h0
      have hnotEsc : ¬ PermanentEscalation peerTrace := by
        intro hesc
        have h0 := hesc 0
        simp [peerTrace] at h0
      have hnotDead : ¬ Deadlock peerTrace := by
        intro hdead
        have h0 := hdead 0
        simp [peerTrace] at h0
      exact ⟨peerTrace, [consB], [consB], ⟨hconsistent, by simp [peerGraph],
        by simp, hbounded, by simp, by
          intro c hc
          simp at hc
          simp [hc],
        hpermit, hnotRefusal, hnotEsc, hnotDead⟩⟩
  · intro p hp
    cases p <;> simp [peerGraphRevisedSacrifices, peerGraphRevisedReport] at hp ⊢
    · exact peerGraph_not_consistent
    · exact peerGraph_not_monotone
    · exact peerGraph_not_strategyproof

/-- Zero-risk report used by the worked `peerGraph` deployment lifecycle. -/
def peerCycleRiskReport : GovernanceRiskReport where
  factor_exposure :=
    { consistency := 0
      solidarity := 0
      monotonicity := 0
      strategyproofness := 0
      nonvacuity := 0 }
  spectral_gap := 1
  cv_bound := 0
  localizability_bound := 0

/-- Risk witness for the worked `peerGraph` deployment lifecycle. -/
def peerCycleRiskWitness
    (compiled : CompiledGovernance) :
    GovernanceRiskWitness compiled peerCycleRiskReport where
  cv_le_cvBound := by norm_num [peerCycleRiskReport,
    LegitimacyFactorExposure.cv]
  signal_range := 0
  cv_bound_le_spectral := by
    norm_num [peerCycleRiskReport]

/-- Monitoring plan used by the worked `peerGraph` deployment lifecycle. -/
def peerCycleMonitoring : MonitoringPlan where
  watches :=
    [ GovernanceProperty.Consistency
    , GovernanceProperty.Solidarity
    , GovernanceProperty.Monotonicity
    , GovernanceProperty.Strategyproofness
    , GovernanceProperty.NonVacuous
    ]

/-- The worked monitoring plan watches every governance property not declared
as sacrificed, for any sacrifice boundary. -/
theorem peerCycleMonitoringCovers
    (sacrifices : List GovernanceProperty) :
    MonitoringCovers peerCycleMonitoring sacrifices := by
  intro p hp
  cases p <;> simp [peerCycleMonitoring]

/-- Public sacrificed compilation artifact for the canonical peer-relative
graph. This is the direct compile target used by capability-scaling's worked
inhabitant. -/
def peerGraphSacrificedCompiledGovernance : CompiledGovernance :=
  compileGovernance peerGraph peerGraphRevisedSacrifices
    peerGraphRevisedReport peerGraphRevisedChecks

/-- The public `peerGraph` artifact declares the forced peer-relative
consistency and monotonicity sacrifices. -/
theorem peerGraphSacrificedCompiledGovernance_forcedDeclared :
    GovernanceProperty.Consistency ∈
        peerGraphSacrificedCompiledGovernance.sacrifices ∧
      GovernanceProperty.Monotonicity ∈
        peerGraphSacrificedCompiledGovernance.sacrifices := by
  constructor
  · change GovernanceProperty.Consistency ∈ peerGraphRevisedSacrifices
    simp [peerGraphRevisedSacrifices]
  · change GovernanceProperty.Monotonicity ∈ peerGraphRevisedSacrifices
    simp [peerGraphRevisedSacrifices]

/-- Direct live lifecycle for the sacrificed `peerGraph` artifact:
declare, compile, measure, then go live. -/
theorem peerGraphSacrificedCompiledGovernance_live :
    TransitionSequence ProtocolState.Undeclared
      (ProtocolState.Live peerGraphSacrificedCompiledGovernance
        peerCycleRiskReport peerCycleMonitoring) := by
  refine
    TransitionSequence.tail
      (TransitionSequence.tail
        (TransitionSequence.tail
          (TransitionSequence.tail
            (TransitionSequence.refl _)
            (ValidTransition.declare (graph := peerGraph)
              (sacrifices := peerGraphRevisedSacrifices) ?_))
          (ValidTransition.compile peerGraphRevisedChecks))
        (ValidTransition.measure
          (peerCycleRiskWitness peerGraphSacrificedCompiledGovernance)))
      ?_
  · simp [WellFormed, peerGraph]
  · exact
      ValidTransition.go_live
        (peerCycleMonitoringCovers
          peerGraphSacrificedCompiledGovernance.sacrifices)

private def peerGraphDriftReport
    (compiled : CompiledGovernance) (hnil : compiled.sacrifices = []) :
    DriftReport compiled where
  observed_graph := peerGraph
  violated_property := GovernanceProperty.Consistency
  not_sacrificed := by
    simp [hnil]
  violation_proof := peerGraph_not_consistent

/-- A concrete full protocol lifecycle whose monitoring phase detects the
`peerGraph` consistency failure and recompiles into an explicitly sacrificed
artifact. -/
theorem peerGraph_recompile_cycle :
    ∃ compiled' : CompiledGovernance,
      TransitionSequence ProtocolState.Undeclared
        (ProtocolState.Compiled compiled') ∧
      compiled'.graph = peerGraph ∧
      GovernanceProperty.Consistency ∈ compiled'.sacrifices := by
  let initialCompiled :=
    compileGovernance permitAllGraph [] permitAllCompilationReport
      permitAllCompilationChecks
  have hnil : initialCompiled.sacrifices = [] := rfl
  let driftReport := peerGraphDriftReport initialCompiled hnil
  let compiled' :=
    compileGovernance peerGraph peerGraphRevisedSacrifices peerGraphRevisedReport
      peerGraphRevisedChecks
  refine ⟨compiled', ?_, rfl, ?_⟩
  · have htraceToDrifted :
        TransitionSequence ProtocolState.Undeclared
          (ProtocolState.Drifted initialCompiled driftReport) :=
      TransitionSequence.tail
        (TransitionSequence.tail
          (TransitionSequence.tail
            (TransitionSequence.tail
              (TransitionSequence.tail
                (TransitionSequence.refl _)
                (ValidTransition.declare permitAllGraph_wellFormed))
              (ValidTransition.compile permitAllCompilationChecks))
            (ValidTransition.measure (peerCycleRiskWitness initialCompiled)))
          (ValidTransition.go_live (peerCycleMonitoringCovers [])))
        (ValidTransition.drift (drift_report := driftReport) (by
          simp [peerCycleMonitoring, driftReport, peerGraphDriftReport]))
    have htraceToRecompiling :
        TransitionSequence ProtocolState.Undeclared
          (ProtocolState.Recompiling initialCompiled driftReport peerGraph) :=
      TransitionSequence.tail htraceToDrifted
        (ValidTransition.recompile (orig := initialCompiled)
          (orig_report := driftReport) (revised := peerGraph))
    exact TransitionSequence.tail htraceToRecompiling
      (ValidTransition.replant
        (orig := initialCompiled)
        (orig_report := driftReport)
        (revised := peerGraph)
        (sacrifices := peerGraphRevisedSacrifices)
        (report := peerGraphRevisedReport)
        (by
          intro p hp
          have hp' := hp
          simp [initialCompiled, compileGovernance] at hp')
        peerGraphRevisedChecks)
  · change GovernanceProperty.Consistency ∈ peerGraphRevisedSacrifices
    simp [peerGraphRevisedSacrifices]

end Legitimacy
