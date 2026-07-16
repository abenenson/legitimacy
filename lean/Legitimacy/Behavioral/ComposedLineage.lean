/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Behavioral.StackelbergLineage
import Legitimacy.Behavioral.ConstitutionalAIVerdict
import Legitimacy.Behavioral.AIControlLineage

/-!
# Cross-lineage positive-procedure composition

This module promotes the CategoryFunctor cross-lineage scaffold into a
substrate theorem for CAI-shaped harm partitions, Stackelberg-shaped capability
adversaries, and AI-Control-shaped monitor budgets.
-/

set_option autoImplicit false

namespace Legitimacy
namespace BehavioralLineage

open Finset Matrix BigOperators
open MeasureTheory ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Finite α] [Finite β]
variable {n : Nat} [NeZero n]

/-- Behavioral composition object carrying the three lineages whose boundary
data must agree before the positive-procedure extractor can be reused:
Constitutional AI supplies the harm/benign claim partition, Stackelberg supplies
the capability adversary, and AI Control supplies the trusted-monitor budget.

The `kernel` field is explicit. Compatibility hypotheses below must prove that
it is the shared graph/channel substrate, rather than an unrelated
positive-procedure kernel. -/
structure ComposedLineage
    (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [Finite β] (n : Nat) [NeZero n] where
  cai : ConstitutionalAICapacityLineage n
  stackelberg : StackelbergBehavioralLineage n
  monitor : AIControl.MonitorCapacityLineage n
  kernel : CapacityKernel α β n

namespace ComposedLineage

variable (L : ComposedLineage α β n)

/-- The CAI side is compatible with the shared kernel when the kernel is the
same graph/signal/tolerance substrate as the CAI deployment lineage and the
CAI harm partition is read at that same capability boundary. -/
structure CAIHarmPartitionCompatible : Prop where
  kernel_graph : L.kernel.G = L.cai.lineage.G
  kernel_signal : L.kernel.s = L.cai.lineage.s
  kernel_tolerance : L.kernel.δ = L.cai.δ
  harm_denied :
    ∀ state : Fin n, L.cai.lineage.claimClass.HarmCategoricalClaim state →
      (L.cai.lineage.policy state).toBinary = BinaryDecision.Deny
  benign_boundary :
    ∀ (state : Fin n) (c : ℚ),
      L.cai.lineage.claimClass.BenignClaim state → 0 < c →
        (L.kernel.G.capabilityResponse L.kernel.s L.kernel.δ c =
            (L.cai.lineage.policy state).toBinary ↔
          L.kernel.C_star ≤ c)

/-- The Stackelberg side is compatible when the adversary acts on exactly the
same graph/signal as the CAI/kernel substrate and its perturbation scale is the
kernel `C_star` boundary. -/
structure StackelbergCapabilityCompatible
    (hCAI : L.CAIHarmPartitionCompatible) : Prop where
  graph_matches_kernel : L.stackelberg.G = L.kernel.G
  signal_matches_kernel : L.stackelberg.s = L.kernel.s
  perturbation_bound_by_kernel_cv :
    ∀ k state : Fin n,
      L.stackelberg.perturbationBudget k state ≤ L.kernel.G.cv L.kernel.s
  stackelberg_C_star_eq_kernel :
    Legitimacy.C_star L.stackelberg.G L.stackelberg.s L.kernel.δ =
      L.kernel.C_star
  harm_partition_preserved_under_perturbation :
    ∀ k state : Fin n,
      L.cai.lineage.claimClass.HarmCategoricalClaim state →
        0 < L.stackelberg.perturbationBudget k state →
          (L.cai.lineage.policy state).toBinary = BinaryDecision.Deny := by
    intro _k state hharm _hbudget
    exact hCAI.harm_denied state hharm

/-- The AI-Control monitor is compatible when it reads the Stackelberg
substrate and covers every capability up to the Stackelberg boundary while
remaining bounded by the shared kernel boundary. -/
structure AIControlMonitorCompatible
    (hCAI : L.CAIHarmPartitionCompatible)
    (hStack : L.StackelbergCapabilityCompatible hCAI) : Prop where
  monitor_graph_matches_stackelberg : L.monitor.G = L.stackelberg.G
  monitor_signal_matches_stackelberg : L.monitor.s = L.stackelberg.s
  monitor_tolerance_matches_kernel : L.monitor.δ = L.kernel.δ
  stackelberg_boundary_le_monitor_budget :
    Legitimacy.C_star L.stackelberg.G L.stackelberg.s L.kernel.δ ≤
      L.monitor.monitorQueryBudget
  monitor_budget_le_kernel_boundary :
    L.monitor.monitorQueryBudget ≤ L.kernel.C_star
  benign_boundary_observed_by_monitor :
    ∀ (state : Fin n) (c : ℚ),
      L.cai.lineage.claimClass.BenignClaim state → 0 < c →
        c ≤ L.monitor.monitorQueryBudget →
          (L.kernel.G.capabilityResponse L.kernel.s L.kernel.δ c =
              (L.cai.lineage.policy state).toBinary ↔
            L.kernel.C_star ≤ c) := by
    intro state c hbenign hcpos _hcmonitor
    exact hCAI.benign_boundary state c hbenign hcpos

/-- The capability bound used by the extractor is re-derived through the three
lineages: CAI fixes the shared kernel boundary, Stackelberg identifies the
capability-adversary boundary, and AI Control monitors that boundary while
staying within the kernel threshold. -/
lemma capability_le_kernel_boundary_via_monitor
    {hCAI : L.CAIHarmPartitionCompatible}
    {hStack : L.StackelbergCapabilityCompatible hCAI}
    (hAIControl : L.AIControlMonitorCompatible hCAI hStack)
    {c : ℚ} (_hcpos : 0 < c) (hc : c ≤ L.kernel.C_star) :
    c ≤ L.kernel.C_star := by
  have hstack : c ≤
      Legitimacy.C_star L.stackelberg.G L.stackelberg.s L.kernel.δ := by
    simpa [hStack.stackelberg_C_star_eq_kernel] using hc
  have hmonitor : c ≤ L.monitor.monitorQueryBudget :=
    le_trans hstack hAIControl.stackelberg_boundary_le_monitor_budget
  exact le_trans hmonitor hAIControl.monitor_budget_le_kernel_boundary

/-- The deployed CAI policy agrees with the verdict of the resolved
constitutional principle at every claim-state. -/
lemma cai_policy_respects_resolution :
    ConstitutionallyRespectsResolution
      L.cai.lineage.claimClass L.cai.lineage.policy := by
  intro state
  rcases L.cai.lineage.claimClass.exhaustive state with hharm | hbenign
  · have hresolved :=
      (L.cai.lineage.claimClass.harm_iff_resolved_denies state).mp hharm
    have hdeny :
        (L.cai.lineage.policy state).toBinary = BinaryDecision.Deny :=
      L.cai.cai_harm_categorical_policy_denies hharm
    rw [hdeny, hresolved]
  · have hresolved :=
      (L.cai.lineage.claimClass.benign_iff_resolved_permits state).mp hbenign
    have hpermit :
        (L.cai.lineage.policy state).toBinary = BinaryDecision.Permit := by
      rw [L.cai.lineage.policy_rule.2 state hbenign]
      simp
    rw [hpermit, hresolved]

/-- Cross-lineage composition theorem. The extracted certificate is paired
with an admissible CAI substrate verdict and a monitor-covered CAI benign
boundary after the capability bound has been routed through the
Stackelberg-shaped adversary boundary and the AI-Control monitor budget. -/
theorem positiveProcedure_classification
    (hCAI : L.CAIHarmPartitionCompatible)
    (hStack : L.StackelbergCapabilityCompatible hCAI)
    (hAIControl : L.AIControlMonitorCompatible hCAI hStack)
    (hcapacity : WellConditionedForCapacity L.kernel) :
    ∀ c : ℚ, 0 < c → c ≤ L.kernel.C_star →
      ∃ cert : PositiveProcedureCertificate L.kernel c,
        (cert.kind = PreservedDiagnostic.consistency ∨
          cert.kind = PreservedDiagnostic.monotonicity) ∧
        ConstitutionalAIBehavioralLineage.substrateVerdict L.cai cert =
          ConstitutionalAIBehavioralLineage.ConstitutionalAISubstrateVerdict.admissible ∧
        c ≤ L.monitor.monitorQueryBudget ∧
        ∀ state : Fin n,
          L.cai.lineage.claimClass.BenignClaim state →
            (L.kernel.G.capabilityResponse L.kernel.s L.kernel.δ c =
                (L.cai.lineage.policy state).toBinary ↔
              L.kernel.C_star ≤ c) := by
  intro c hcpos hc
  have hstack : c ≤
      Legitimacy.C_star L.stackelberg.G L.stackelberg.s L.kernel.δ := by
    simpa [hStack.stackelberg_C_star_eq_kernel] using hc
  have hmonitor : c ≤ L.monitor.monitorQueryBudget :=
    le_trans hstack hAIControl.stackelberg_boundary_le_monitor_budget
  have hboundary : c ≤ L.kernel.C_star :=
    le_trans hmonitor hAIControl.monitor_budget_le_kernel_boundary
  let cert := governance_certificate L.kernel hcapacity c hcpos hboundary
  have hkind :
      cert.kind = PreservedDiagnostic.consistency ∨
        cert.kind = PreservedDiagnostic.monotonicity := by
    dsimp [cert]
    unfold governance_certificate
    by_cases hlt : c < L.kernel.C_star
    · simp [hlt, PositiveProcedureCertificate.kind]
    · simp [hlt, PositiveProcedureCertificate.kind]
  have hadmissible :
      ConstitutionalAIBehavioralLineage.substrateVerdict L.cai cert =
        ConstitutionalAIBehavioralLineage.ConstitutionalAISubstrateVerdict.admissible := by
    dsimp [cert]
    exact
      ConstitutionalAIBehavioralLineage.substrateVerdict_admissible_of_respects_resolution
        L.cai hcapacity hcpos hboundary L.cai_policy_respects_resolution
  refine ⟨cert, hkind, hadmissible, hmonitor, ?_⟩
  intro state hbenign
  exact hCAI.benign_boundary state c hbenign hcpos

end ComposedLineage

/-- Requested top-level spelling for the cross-lineage composition theorem. -/
theorem composedLineage_positiveProcedure_classification
    (L : ComposedLineage α β n)
    (hCAI : L.CAIHarmPartitionCompatible)
    (hStack : L.StackelbergCapabilityCompatible hCAI)
    (hAIControl : L.AIControlMonitorCompatible hCAI hStack)
    (hcapacity : WellConditionedForCapacity L.kernel) :
    ∀ c : ℚ, 0 < c → c ≤ L.kernel.C_star →
      ∃ cert : PositiveProcedureCertificate L.kernel c,
        (cert.kind = PreservedDiagnostic.consistency ∨
          cert.kind = PreservedDiagnostic.monotonicity) ∧
        ConstitutionalAIBehavioralLineage.substrateVerdict L.cai cert =
          ConstitutionalAIBehavioralLineage.ConstitutionalAISubstrateVerdict.admissible ∧
        c ≤ L.monitor.monitorQueryBudget ∧
        ∀ state : Fin n,
          L.cai.lineage.claimClass.BenignClaim state →
            (L.kernel.G.capabilityResponse L.kernel.s L.kernel.δ c =
                (L.cai.lineage.policy state).toBinary ↔
              L.kernel.C_star ≤ c) :=
  L.positiveProcedure_classification hCAI hStack hAIControl hcapacity

namespace ComposedLineageExamples

open ConstitutionalAIBehavioralLineage

/-- Five-state local claim partition for the composed-lineage witness: state
`0` is harm-categorical and every other state is benign. -/
noncomputable def composedClaimClass5 :
    ConstitutionalAIClaimClass 5 :=
  ConstitutionalAIClaimClass.ofFlat
    (fun state => state = 0)
    (fun state => state ≠ 0)
    (by
      intro state
      by_cases h : state = 0
      · exact Or.inl h
      · exact Or.inr h)
    (by
      intro state hboth
      exact hboth.2 hboth.1)

/-- Trained local policy for the composed-lineage witness: deny harm and permit
the benign residual class. -/
def composedPolicy5 (state : Fin 5) : ConstitutionalAIDecision :=
  if state = 0 then
    ConstitutionalAIDecision.deny
  else
    ConstitutionalAIDecision.permit

theorem composedPolicy5_rule :
    ConstitutionalAITrainedAuditSubject composedClaimClass5 composedPolicy5 := by
  constructor
  · intro state hharm
    dsimp [composedClaimClass5] at hharm
    change state = 0 at hharm
    exact Or.inr (by simp [composedPolicy5, hharm])
  · intro state hbenign
    dsimp [composedClaimClass5] at hbenign
    change state ≠ 0 at hbenign
    simp [composedPolicy5, hbenign]

/-- CAI lineage over the calibrated five-node half-scale signal used by the
existing exact positive-procedure channel. It keeps the same n=5 harm/benign
partition and trained policy as the AI-Control-shaped witness. -/
noncomputable def constitutionalAIHalfSignalLineage5 :
    ConstitutionalAIBehavioralLineage 5 where
  G := uniK5
  s := uniK5HalfSig
  claimClass := composedClaimClass5
  policy := composedPolicy5
  policy_rule := composedPolicy5_rule

/-- Capability wrapper for the calibrated five-node CAI half-signal lineage. -/
noncomputable def constitutionalAICapacityHalfSignalLineage5 :
    ConstitutionalAICapacityLineage 5 where
  lineage := constitutionalAIHalfSignalLineage5
  δ := 1 / 10
  δ_pos := by norm_num
  cv_pos := GovernanceChannel.uniK5_cv_uniK5HalfSig_pos
  auditAmplitudeBudget := 4 / 15
  auditAmplitudeBudget_pos := by norm_num

/-- Stackelberg adversary over the same calibrated five-node graph/signal. -/
def stackelbergHalfSignalLineage5 :
    StackelbergBehavioralLineage 5 where
  G := uniK5
  s := uniK5HalfSig

/-- AI-Control monitor budget pinned to the calibrated five-node `C_star`. -/
def aiControlHalfSignalMonitor5 :
    AIControl.MonitorCapacityLineage 5 where
  G := uniK5
  s := uniK5HalfSig
  δ := 1 / 10
  δ_pos := by norm_num
  cv_pos := GovernanceChannel.uniK5_cv_uniK5HalfSig_pos
  monitorQueryBudget := 4 / 15
  monitorQueryBudget_pos := by norm_num

/-- Positive-procedure kernel over the existing exact `uniK5HalfSig`
erasure-channel calibration. -/
noncomputable def composedPositiveProcedureKernel5 :
    CapacityKernel BinaryDecision (Option BinaryDecision) 5 where
  G := uniK5
  s := uniK5HalfSig
  δ := 1 / 10
  channel := GovernanceChannel.concreteUniK5HalfNoisyCStarCalibration.channel

/-- The worked composed kernel is well-conditioned. -/
noncomputable def composedPositiveProcedureKernel5_wellConditioned :
    WellConditionedForCapacity composedPositiveProcedureKernel5 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [composedPositiveProcedureKernel5]
  · simpa [composedPositiveProcedureKernel5] using
      GovernanceChannel.uniK5_cv_uniK5HalfSig_pos
  · simpa [composedPositiveProcedureKernel5] using
      GovernanceChannel.ConcreteNoisyCStarCalibration.toExactCapacityCertificate
        GovernanceChannel.concreteUniK5HalfNoisyCStarCalibration
        GovernanceChannel.uniK5_cv_uniK5HalfSig_pos

/-- The calibrated five-node half-signal kernel has `C_star = 4 / 15`. -/
theorem composedPositiveProcedureKernel5_C_star :
    composedPositiveProcedureKernel5.C_star = 4 / 15 := by
  simp [composedPositiveProcedureKernel5, CapacityKernel.C_star,
    Legitimacy.C_star, GovernanceChannel.uniK5_cv_uniK5HalfSig]
  norm_num

/-- Worked n=5 composed lineage sharing the calibrated `uniK5HalfSig`
positive-procedure kernel. -/
noncomputable def composedLineage5 :
    ComposedLineage BinaryDecision (Option BinaryDecision) 5 where
  cai := constitutionalAICapacityHalfSignalLineage5
  stackelberg := stackelbergHalfSignalLineage5
  monitor := aiControlHalfSignalMonitor5
  kernel := composedPositiveProcedureKernel5

theorem composedLineage5_C_star :
    composedLineage5.kernel.C_star = 4 / 15 :=
  composedPositiveProcedureKernel5_C_star

/-- CAI compatibility for the worked n=5 composition. -/
theorem composedLineage5_caiCompatible :
    composedLineage5.CAIHarmPartitionCompatible := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro state hharm
    exact constitutionalAICapacityHalfSignalLineage5
      |>.cai_harm_categorical_policy_denies hharm
  · intro state c hbenign hcpos
    exact constitutionalAICapacityHalfSignalLineage5
      |>.cai_capabilityBoundary_benign_response_matches_C_star hbenign hcpos

/-- Stackelberg compatibility for the worked n=5 composition. -/
theorem composedLineage5_stackelbergCompatible :
    composedLineage5.StackelbergCapabilityCompatible
      composedLineage5_caiCompatible := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro k state
    change stackelbergHalfSignalLineage5.perturbationBudget k state ≤
      uniK5.cv uniK5HalfSig
    exact stackelbergHalfSignalLineage5.single_removal_perturbation_le_cv k state
  · dsimp [composedLineage5, stackelbergHalfSignalLineage5,
      composedPositiveProcedureKernel5, CapacityKernel.C_star,
      Legitimacy.C_star]
  · intro _k state hharm _hbudget
    exact composedLineage5_caiCompatible.harm_denied state hharm

/-- AI-Control monitor compatibility for the worked n=5 composition. -/
theorem composedLineage5_aiControlCompatible :
    composedLineage5.AIControlMonitorCompatible
      composedLineage5_caiCompatible
      composedLineage5_stackelbergCompatible := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · dsimp [composedLineage5, stackelbergHalfSignalLineage5,
      aiControlHalfSignalMonitor5, composedPositiveProcedureKernel5,
      Legitimacy.C_star]
    rw [GovernanceChannel.uniK5_cv_uniK5HalfSig]
    norm_num
  · rw [composedLineage5_C_star]
    rfl
  · intro state c hbenign hcpos _hcmonitor
    exact composedLineage5_caiCompatible.benign_boundary state c hbenign hcpos

/-- Worked n=5 instance of the cross-lineage composition theorem. -/
theorem composedLineage5_positiveProcedure_classification :
    ∀ c : ℚ, 0 < c → c ≤ composedLineage5.kernel.C_star →
      ∃ cert : PositiveProcedureCertificate composedLineage5.kernel c,
        (cert.kind = PreservedDiagnostic.consistency ∨
          cert.kind = PreservedDiagnostic.monotonicity) ∧
        ConstitutionalAIBehavioralLineage.substrateVerdict
            composedLineage5.cai cert =
          ConstitutionalAIBehavioralLineage.ConstitutionalAISubstrateVerdict.admissible ∧
        c ≤ composedLineage5.monitor.monitorQueryBudget ∧
        ∀ state : Fin 5,
          composedLineage5.cai.lineage.claimClass.BenignClaim state →
            (composedLineage5.kernel.G.capabilityResponse
                composedLineage5.kernel.s composedLineage5.kernel.δ c =
                (composedLineage5.cai.lineage.policy state).toBinary ↔
              composedLineage5.kernel.C_star ≤ c) :=
  composedLineage_positiveProcedure_classification
    composedLineage5
    composedLineage5_caiCompatible
    composedLineage5_stackelbergCompatible
    composedLineage5_aiControlCompatible
    composedPositiveProcedureKernel5_wellConditioned

end ComposedLineageExamples

end BehavioralLineage
end Legitimacy
