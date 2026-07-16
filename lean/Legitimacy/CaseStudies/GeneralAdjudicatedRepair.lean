/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Bridges.AuditSpectralProjection
import Legitimacy.Results.GovernanceAdmissibilityAudit
import Legitimacy.Spectral.Dynamics.StackelbergConvergence
import Legitimacy.CaseStudies.CodexHarness
import Legitimacy.CaseStudies.ClaudeAgentSdkHarness
import Legitimacy.CaseStudies.ClaudeCodeHarness
import Legitimacy.Results.CrewAIAdmissibilityAudit
import Legitimacy.Results.OpenClawAdmissibilityAudit

/-!
# Legitimacy.CaseStudies.GeneralAdjudicatedRepair

General threshold-adjudication repair surface for extracted governance audit
graphs.

The primitive class predicate below is intentionally separated from the repair
conclusion. It records the graph-side feature that makes a threshold gate act
as a terminal monotonicity rejection surface: a threshold match returns a
decision strictly below `.permit` in the production rank lattice.
-/

set_option autoImplicit false

namespace Legitimacy

/-!
## Stage 1: primitive threshold-rejection class witness
-/

/-- Synthetic one-node class-C witness: strengthening `audit_signal` can move
the synthetic baseline claim from default `.permit` to terminal `.escalate`. -/
def syntheticThresholdEscalationGraph : AuditGovernanceGraph where
  nodes :=
    [ .binary "threshold-escalation"
        "synthetic threshold escalation"
        [ .thresholdGate "audit_signal" 1 .escalate ]
        .permit
        .firstMatch
    ]
  edges := []

/-- Audit subject for `syntheticThresholdEscalationGraph`. -/
def syntheticThresholdEscalationSubject : AuditSubject where
  graph := syntheticThresholdEscalationGraph
  evalNode := auditEvaluateNode

/-- The synthetic witness is structurally inside class C. -/
theorem syntheticThresholdEscalation_contains_threshold_rejection :
    ContainsThresholdMonotonicityRejection
      syntheticThresholdEscalationGraph = true := by
  native_decide

/-- The synthetic witness has the production monotonicity rejection expected
for the class-C audit-subject predicate. -/
theorem syntheticThresholdEscalation_monotonicity_rejected :
    auditCheckStatus syntheticThresholdEscalationSubject
        AuditCheck.monotonicity = .ok .failed := by
  native_decide

/-- Non-vacuity witness for the class-C subject predicate independent of the
Codex harness. -/
theorem syntheticThresholdEscalation_in_class_C :
    ThresholdGateMonotonicityRejectionSubject
      syntheticThresholdEscalationSubject := by
  exact
    ⟨syntheticThresholdEscalation_contains_threshold_rejection,
      syntheticThresholdEscalation_monotonicity_rejected⟩

/-!
## Stage 2: general adjudicated repair theorem
-/

/-- General theorem: adjudicated repair satisfies the graph predicate and its
scoped spectral vulnerability is no greater than the audit-derived pre-repair
spectral vulnerability. -/
theorem general_adjudicated_repair_removes_spectral_vulnerability
    {n : Nat} [NeZero n]
    (spectralGraph : GovGraph ℚ n)
    (graph : AuditGovernanceGraph) :
    graph_threshold_adjudicated
        (adjudicateThresholdGraph graph) = true ∧
      spectralGraph.cv
          (auditGraphThresholdSignal
            (adjudicateThresholdGraph graph)) ≤
        spectralGraph.cv (auditGraphThresholdSignal graph) := by
  constructor
  · exact graph_threshold_adjudicated_adjudicateThresholdGraph graph
  · rw [adjudicateThresholdGraph_cv_zero]
    exact spectralGraph.cv_nonneg (auditGraphThresholdSignal graph)

/-- Strict version over the load-bearing positive pre-repair spectral
vulnerability premise. Class-C membership remains the structural repair-family
predicate, but it is not part of this strict inequality because the supplied
spectral topology is arbitrary. -/
theorem general_adjudicated_repair_strictly_removes_spectral_vulnerability
    {n : Nat} [NeZero n]
    (spectralGraph : GovGraph ℚ n)
    (graph : AuditGovernanceGraph)
    (hwitness :
      ThresholdRepairStrictSpectralWitness spectralGraph graph) :
    graph_threshold_adjudicated
        (adjudicateThresholdGraph graph) = true ∧
      spectralGraph.cv
          (auditGraphThresholdSignal
            (adjudicateThresholdGraph graph)) <
        spectralGraph.cv (auditGraphThresholdSignal graph) := by
  constructor
  · exact graph_threshold_adjudicated_adjudicateThresholdGraph graph
  · rw [adjudicateThresholdGraph_cv_zero]
    exact hwitness

/-!
## Stage 4: concrete harness instances
-/

/-- Appending the explicit compositional permit suffix preserves generic
threshold adjudication because the suffix node has no threshold gates. -/
theorem graph_threshold_adjudicated_appendCompositionalPermitSuffix
    (graph : AuditGovernanceGraph)
    (hgraph : graph_threshold_adjudicated graph = true) :
    graph_threshold_adjudicated
      (appendCompositionalPermitSuffix graph) = true := by
  cases graph
  simpa [appendCompositionalPermitSuffix, graph_threshold_adjudicated,
    nodeThresholdAdjudicated] using hgraph

/-- The Codex graph contains the primitive threshold-rejection feature. -/
theorem codexHooks_contains_threshold_monotonicity_rejection :
    ContainsThresholdMonotonicityRejection
      codexHooksExtractedGovernanceGraph = true := by
  native_decide

/-- The Codex extracted audit subject is in class C. -/
theorem codexHooks_in_class_C :
    ThresholdGateMonotonicityRejectionSubject
      codexHooksExtractedGraph := by
  constructor
  · exact codexHooks_contains_threshold_monotonicity_rejection
  · native_decide

/-- The Codex case-study repair is the generic threshold adjudication repair
followed by the existing explicit permit suffix. -/
theorem codexHarnessRepairedGovernanceGraph_eq_general_adjudicated_suffix :
    codexHarnessRepairedGovernanceGraph =
      appendCompositionalPermitSuffix
        (adjudicateThresholdGraph codexHooksExtractedGovernanceGraph) := by
  native_decide

/-- Generic threshold adjudication proves the repaired Codex graph satisfies
the generic graph predicate. -/
theorem codexHarness_repaired_graph_threshold_adjudicated_from_general :
    graph_threshold_adjudicated
      codexHarnessRepairedGovernanceGraph = true := by
  rw [codexHarnessRepairedGovernanceGraph_eq_general_adjudicated_suffix]
  exact graph_threshold_adjudicated_appendCompositionalPermitSuffix
    (adjudicateThresholdGraph codexHooksExtractedGovernanceGraph)
    (graph_threshold_adjudicated_adjudicateThresholdGraph
      codexHooksExtractedGovernanceGraph)

/-- The Codex-specific threshold predicate agrees with the generic predicate on
the repaired graph; the original case-study theorem is therefore a corollary of
the generic repair surface. -/
theorem codexHarness_repaired_codex_predicate_from_general :
    codexHarnessGraphThresholdAdjudicated
      codexHarnessRepairedGovernanceGraph = true := by
  simpa [codexHarnessGraphThresholdAdjudicated,
    codexHarnessNodeThresholdAdjudicated,
    codexHarnessGateThresholdAdjudicated,
    graph_threshold_adjudicated,
    nodeThresholdAdjudicated,
    thresholdGateAdjudicated] using
      codexHarness_repaired_graph_threshold_adjudicated_from_general

/-- The Codex spectral projection supplies a positive pre-repair threshold
witness for the strict general theorem. -/
theorem codexHarness_threshold_repair_spectral_witness :
    ThresholdRepairSpectralWitness
      codexHarnessSpectralGraph
      codexHooksExtractedGovernanceGraph := by
  constructor
  · exact codexHooks_contains_threshold_monotonicity_rejection
  · native_decide

/-- Codex instance of the strict general spectral theorem. -/
theorem codexHarness_general_adjudicated_repair_strict_spectral :
    graph_threshold_adjudicated
        (adjudicateThresholdGraph
          codexHooksExtractedGovernanceGraph) = true ∧
      codexHarnessSpectralGraph.cv
          (auditGraphThresholdSignal
            (adjudicateThresholdGraph
              codexHooksExtractedGovernanceGraph)) <
        codexHarnessSpectralGraph.cv
          (auditGraphThresholdSignal
            codexHooksExtractedGovernanceGraph) :=
  general_adjudicated_repair_strictly_removes_spectral_vulnerability
    codexHarnessSpectralGraph
      codexHooksExtractedGovernanceGraph
      codexHarness_threshold_repair_spectral_witness.strict

/-- The derived Codex spectral projection supplies a positive pre-repair
threshold witness for the strict general theorem. -/
theorem codexHarnessDerived_threshold_repair_spectral_witness :
    ThresholdRepairSpectralWitness
      codexHarnessDerivedSpectralGraph
      codexHooksExtractedGovernanceGraph := by
  constructor
  · exact codexHooks_contains_threshold_monotonicity_rejection
  · native_decide

/-- Derived-carrier Codex instance of the strict general spectral theorem. -/
theorem codexHarnessDerived_general_adjudicated_repair_strict_spectral :
    graph_threshold_adjudicated
        (adjudicateThresholdGraph
          codexHooksExtractedGovernanceGraph) = true ∧
      codexHarnessDerivedSpectralGraph.cv
          (auditGraphThresholdSignal
            (adjudicateThresholdGraph
              codexHooksExtractedGovernanceGraph)) <
        codexHarnessDerivedSpectralGraph.cv
          (auditGraphThresholdSignal
            codexHooksExtractedGovernanceGraph) :=
  general_adjudicated_repair_strictly_removes_spectral_vulnerability
    codexHarnessDerivedSpectralGraph
    codexHooksExtractedGovernanceGraph
    codexHarnessDerived_threshold_repair_spectral_witness.strict

/-- The repaired Codex graph has zero audit-derived threshold CV under the
generic graph-indexed spectral repair surface for the committed
`hook_registration` signal. -/
theorem codexHarness_repaired_audit_threshold_signal_cv_zero_from_general :
    codexHarnessRepairedSpectralGraph.cv
      (auditGraphThresholdSignal codexHarnessRepairedGovernanceGraph) = 0 := by
  exact
    auditGraphThresholdSignal_cv_zero_of_graph_threshold_adjudicated
      codexHarnessRepairedSpectralGraph
      codexHarnessRepairedGovernanceGraph
      codexHarness_repaired_graph_threshold_adjudicated_from_general

/-- Claude Agent SDK hooks are in the subject-level class C. -/
theorem claudeAgentSDKHooks_in_class_C :
    ThresholdGateMonotonicityRejectionSubject
      claudeAgentSDKHooksExtractedGraph := by
  constructor <;> native_decide

/-- The derived Claude Agent SDK spectral projection supplies a positive
pre-repair threshold witness for the strict general theorem. -/
theorem claudeAgentSdkHarnessDerived_threshold_repair_spectral_witness :
    ThresholdRepairSpectralWitness
      claudeAgentSdkHarnessDerivedSpectralGraph
      claudeAgentSDKHooksExtractedGovernanceGraph := by
  constructor
  · native_decide
  · native_decide

/-- Derived-carrier Claude Agent SDK instance of the strict general spectral
theorem. -/
theorem claudeAgentSdkHarnessDerived_general_adjudicated_repair_strict_spectral :
    graph_threshold_adjudicated
        (adjudicateThresholdGraph
          claudeAgentSDKHooksExtractedGovernanceGraph) = true ∧
      claudeAgentSdkHarnessDerivedSpectralGraph.cv
          (auditGraphThresholdSignal
            (adjudicateThresholdGraph
              claudeAgentSDKHooksExtractedGovernanceGraph)) <
        claudeAgentSdkHarnessDerivedSpectralGraph.cv
          (auditGraphThresholdSignal
            claudeAgentSDKHooksExtractedGovernanceGraph) :=
  general_adjudicated_repair_strictly_removes_spectral_vulnerability
    claudeAgentSdkHarnessDerivedSpectralGraph
    claudeAgentSDKHooksExtractedGovernanceGraph
    claudeAgentSdkHarnessDerived_threshold_repair_spectral_witness.strict

/-- Claude Code hooks are in the subject-level class C. -/
theorem claudeCodeHooks_in_class_C :
    ThresholdGateMonotonicityRejectionSubject
      claudeCodeHooksExtractedGraph := by
  constructor <;> native_decide

/-- The derived Claude Code spectral projection supplies a positive pre-repair
threshold witness for the strict general theorem. -/
theorem claudeCodeHarnessDerived_threshold_repair_spectral_witness :
    ThresholdRepairSpectralWitness
      claudeCodeHarnessDerivedSpectralGraph
      claudeCodeHooksExtractedGovernanceGraph := by
  constructor
  · native_decide
  · native_decide

/-- Derived-carrier Claude Code instance of the strict general spectral
theorem. -/
theorem claudeCodeHarnessDerived_general_adjudicated_repair_strict_spectral :
    graph_threshold_adjudicated
        (adjudicateThresholdGraph
          claudeCodeHooksExtractedGovernanceGraph) = true ∧
      claudeCodeHarnessDerivedSpectralGraph.cv
          (auditGraphThresholdSignal
            (adjudicateThresholdGraph
              claudeCodeHooksExtractedGovernanceGraph)) <
        claudeCodeHarnessDerivedSpectralGraph.cv
          (auditGraphThresholdSignal
            claudeCodeHooksExtractedGovernanceGraph) :=
  general_adjudicated_repair_strictly_removes_spectral_vulnerability
    claudeCodeHarnessDerivedSpectralGraph
    claudeCodeHooksExtractedGovernanceGraph
    claudeCodeHarnessDerived_threshold_repair_spectral_witness.strict

/-- CrewAI hooks are in the subject-level class C. -/
theorem crewAIHooks_in_class_C :
    ThresholdGateMonotonicityRejectionSubject
      crewAIExtractedGraph := by
  constructor <;> native_decide

/-- OpenClaw has non-permit threshold gates structurally, so it is inside the
primitive graph-side repair surface. -/
theorem openClawInfra_contains_threshold_monotonicity_rejection :
    ContainsThresholdMonotonicityRejection
      openClawInfraExtractedGovernanceGraph = true := by
  native_decide

/-- OpenClaw's current theorem-facing rejection is nonvacuity, not the
subject-level monotonicity class used for Codex/Claude/CrewAI above. We keep
this as a residual characterization rather than forcing an expensive
monotonicity-pass recomputation over the large OpenClaw literal here. -/
theorem openClawInfra_nonvacuity_rejection_characterization :
    auditCheckStatus openClawInfraExtractedGraph
      AuditCheck.nonvacuous = .ok .failed :=
  openClawInfraNonvacuityCheckFails

/-- Five current non-vacuity witnesses for the subject-level class C: Codex,
the synthetic one-node graph, Claude Agent SDK hooks, Claude Code hooks, and
CrewAI hooks. -/
theorem class_C_nonvacuous_witnesses :
    ThresholdGateMonotonicityRejectionSubject
        codexHooksExtractedGraph ∧
      ThresholdGateMonotonicityRejectionSubject
        syntheticThresholdEscalationSubject ∧
      ThresholdGateMonotonicityRejectionSubject
        claudeAgentSDKHooksExtractedGraph ∧
      ThresholdGateMonotonicityRejectionSubject
        claudeCodeHooksExtractedGraph ∧
      ThresholdGateMonotonicityRejectionSubject
        crewAIExtractedGraph :=
  ⟨codexHooks_in_class_C,
    syntheticThresholdEscalation_in_class_C,
    claudeAgentSDKHooks_in_class_C,
    claudeCodeHooks_in_class_C,
    crewAIHooks_in_class_C⟩

end Legitimacy
