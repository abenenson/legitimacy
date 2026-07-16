/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Bridges.AuditSpectralProjection
import Legitimacy.Results.CodexAdmissibilityAudit
import Legitimacy.Spectral.Capacity.CriticalCapability
import Legitimacy.Spectral.Dynamics.StackelbergConvergence

/-!
# Legitimacy.CaseStudies.CodexHarness

End-to-end case study for the extracted OpenAI Codex hooks governance harness.

The file is deliberately staged: the extracted fixture and rejection theorem
come first, the spectral capability threshold is added next, and the repaired
typed graph is proved admissible only after the repair structure is explicit.
This avoids packaging the case study as a conjunction of unrelated witnesses.
-/

set_option autoImplicit false

namespace Legitimacy

/-!
## Stage 1: extracted fixture and audit detection

The source artifact is `examples/graphs/codex-graph.json`; the Lean literal
is `codexHooksExtractedGovernanceGraph` in
`Legitimacy.Results.CodexAdmissibilityAudit`.
-/

/-- The committed Codex extracted graph has the expected sixteen hook nodes. -/
theorem codexHarness_extracted_node_count :
    codexHooksExtractedGovernanceGraph.nodes.length = 16 := by
  native_decide

/-- The committed Codex extracted graph has the eight pass-through hook edges
recorded in the byte-stable graph fixture. -/
theorem codexHarness_extracted_edge_count :
    codexHooksExtractedGovernanceGraph.edges.length = 8 := by
  native_decide

/-- The production synthetic audit corpus for the Codex graph has 29 claims. -/
theorem codexHarness_extracted_claim_count :
    (auditGraphClaims codexHooksExtractedGraph).length = 29 := by
  native_decide

/-- The production synthetic audit corpus exposes five numeric metric fields. -/
theorem codexHarness_extracted_metric_field_count :
    (auditGraphFields (auditGraphClaims codexHooksExtractedGraph)).length = 5 := by
  native_decide

/-- Stage-one detection: the existing substrate rejects the byte-stable Codex
fixture on monotonicity. -/
theorem codexHarness_stage1_detects_monotonicity_failure :
    codexHooksGovernanceAdmissibilityVerdict =
      AuditVerdict.rejected AuditCheck.monotonicity :=
  codexHooksGovernanceAdmissibilityRejectsMonotonicity

/-!
## Stage 2: critical capability threshold

The derived spectral projection below is computed from the extracted
pass-through hook topology. The derived threshold signal is computed from the
extracted node-indexed threshold gates: every registration node contributes the
`hook_registration`/`.escalate` component and every callback node contributes
zero.
-/

/-- Legacy hand-authored ten-node carrier for five of the eight Codex
pass-through hook pairs, superseded by `codexHarnessDerivedSpectralGraph` and
retained for citation stability. -/
def codexHarnessSpectralGraph : GovGraph ℚ 10 where
  weights := fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
       (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
       (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) ∨
       (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6) ∨
       (i = 8 ∧ j = 9) ∨ (i = 9 ∧ j = 8) then
      1
    else
      0
  weight_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by
    intro i
    fin_cases i <;> native_decide

/-- Legacy hand-authored failure signal for the ten-node carrier, superseded by
the graph-derived `codexHarnessDerivedFailureSignal` and retained for citation
stability. -/
def codexHarnessFailureSignal : Fin 10 → ℚ :=
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

/-- The case-study tolerance used for the capability threshold, matching the
concrete spectral examples in `CriticalCapability.lean`. -/
def codexHarnessTolerance : ℚ := 1 / 10

/-- The Codex spectral projection has exact consistency vulnerability 1 under
the failure-localized signal. -/
theorem codexHarness_cv_value :
    codexHarnessSpectralGraph.cv codexHarnessFailureSignal = 1 := by
  native_decide

/-- Exact critical capability value for the Codex graph: `1/10`, i.e. decimal
`0.1`. -/
theorem codexHarness_C_star_value :
    C_star codexHarnessSpectralGraph codexHarnessFailureSignal
        codexHarnessTolerance = 1 / 10 := by
  native_decide

/-- Below `C_star` the spectral surrogate has no reachable perturbation at the
capability-scaled tolerance; at or above `C_star` the perturbation exists. -/
theorem codexHarness_stage2_threshold :
    (∀ C : ℚ, 0 < C →
        C < C_star codexHarnessSpectralGraph codexHarnessFailureSignal
            codexHarnessTolerance →
          ¬ codexHarnessSpectralGraph.spViolation codexHarnessFailureSignal
            (codexHarnessTolerance / C)) ∧
      (∀ C : ℚ,
        C_star codexHarnessSpectralGraph codexHarnessFailureSignal
            codexHarnessTolerance ≤ C →
          codexHarnessSpectralGraph.spViolation codexHarnessFailureSignal
            (codexHarnessTolerance / C)) := by
  have hδ : 0 < codexHarnessTolerance := by
    native_decide
  have hcv : 0 < codexHarnessSpectralGraph.cv codexHarnessFailureSignal := by
    native_decide
  exact C_star_exists codexHarnessSpectralGraph codexHarnessFailureSignal
    codexHarnessTolerance hδ hcv

/-- Operational high-capability side of the critical threshold. This is the
Stage 1 failure regime restated through the spectral `C_star` API: any
capability strictly above the exact threshold is in the violation region. -/
theorem codexHarness_stage2_failure_above_C_star
    (C : ℚ)
    (hC :
      C_star codexHarnessSpectralGraph codexHarnessFailureSignal
          codexHarnessTolerance < C) :
    codexHarnessSpectralGraph.spViolation codexHarnessFailureSignal
      (codexHarnessTolerance / C) := by
  exact codexHarness_stage2_threshold.2 C (le_of_lt hC)

/-- Stackelberg-limit reading: positive Codex CV eventually rules out stable
spectral equilibria once capability crosses the exact `C_star` threshold. -/
theorem codexHarness_stage2_stackelberg_eventual_instability :
    ∃ κ₀ > 0, ∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
      ¬ SpectralStableEquilibrium codexHarnessSpectralGraph
        codexHarnessFailureSignal codexHarnessTolerance κ := by
  have hδ : 0 < codexHarnessTolerance := by
    native_decide
  have hcv : 0 < codexHarnessSpectralGraph.cv codexHarnessFailureSignal := by
    native_decide
  exact eventually_no_stable_equilibrium_of_positive_cv
    codexHarnessSpectralGraph codexHarnessFailureSignal
    codexHarnessTolerance hδ hcv

/-- Derived sixteen-node spectral carrier obtained by symmetrizing the committed
extracted Codex audit graph's pass-through edges. -/
def codexHarnessDerivedSpectralGraph : GovGraph ℚ 16 :=
  codexHooksExtractedGovernanceGraph.spectralProjection 16

/-- Derived threshold signal from the committed extracted Codex audit graph:
callback nodes carry zero and registration nodes carry the
`hook_registration`/`.escalate` component `1`. -/
def codexHarnessDerivedFailureSignal : Fin 16 → ℚ :=
  auditGraphThresholdSignal codexHooksExtractedGovernanceGraph

/-- The derived carrier keeps all eight extracted pass-through pairs: unit
weight appears exactly between the callback/registration nodes in the same pair,
and no self-loop is present. -/
theorem codexHarnessDerivedSpectralGraph_weights_pair :
    ∀ i j : Fin 16,
      codexHarnessDerivedSpectralGraph.weights i j =
        if i.val / 2 = j.val / 2 ∧ i ≠ j then 1 else 0 := by
  native_decide

/-- The derived threshold signal is zero on callback nodes and one on all eight
registration nodes. -/
theorem codexHarnessDerivedFailureSignal_vector :
    codexHarnessDerivedFailureSignal =
      ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] := by
  native_decide

/-- The derived sixteen-node carrier is eight disconnected `K₂` components, so
vertices in different extracted hook pairs have zero edge weight. Consequently
the real Laplacian gap is `λ₂ = 0`; the `cv`/`C*`/Stackelberg-limit results
below consume only positive CV and deliberately do not instantiate the
positive-spectral-gap lower-bound theorems. -/
theorem codexHarnessDerivedSpectralGraph_pairwise_disconnected :
    ∀ i j : Fin 16, i.val / 2 ≠ j.val / 2 →
      codexHarnessDerivedSpectralGraph.weights i j = 0 := by
  native_decide

/-- The derived Codex spectral carrier has exact consistency vulnerability 1
under the audit-derived threshold signal. -/
theorem codexHarnessDerived_cv_value :
    codexHarnessDerivedSpectralGraph.cv
      codexHarnessDerivedFailureSignal = 1 := by
  native_decide

/-- Exact critical capability value on the derived carrier: `1/10`, unchanged
from the legacy hand-authored carrier. -/
theorem codexHarnessDerived_C_star_value :
    C_star codexHarnessDerivedSpectralGraph
        codexHarnessDerivedFailureSignal codexHarnessTolerance = 1 / 10 := by
  native_decide

/-- Below derived `C*` the spectral surrogate has no reachable perturbation at
the capability-scaled tolerance; at or above derived `C*` the perturbation
exists. -/
theorem codexHarnessDerived_stage2_threshold :
    (∀ C : ℚ, 0 < C →
        C < C_star codexHarnessDerivedSpectralGraph
            codexHarnessDerivedFailureSignal codexHarnessTolerance →
          ¬ codexHarnessDerivedSpectralGraph.spViolation
            codexHarnessDerivedFailureSignal (codexHarnessTolerance / C)) ∧
      (∀ C : ℚ,
        C_star codexHarnessDerivedSpectralGraph
            codexHarnessDerivedFailureSignal codexHarnessTolerance ≤ C →
          codexHarnessDerivedSpectralGraph.spViolation
            codexHarnessDerivedFailureSignal (codexHarnessTolerance / C)) := by
  have hδ : 0 < codexHarnessTolerance := by
    native_decide
  have hcv :
      0 <
        codexHarnessDerivedSpectralGraph.cv
          codexHarnessDerivedFailureSignal := by
    native_decide
  exact C_star_exists codexHarnessDerivedSpectralGraph
    codexHarnessDerivedFailureSignal codexHarnessTolerance hδ hcv

/-- Operational high-capability side of the derived critical threshold. -/
theorem codexHarnessDerived_stage2_failure_above_C_star
    (C : ℚ)
    (hC :
      C_star codexHarnessDerivedSpectralGraph
          codexHarnessDerivedFailureSignal codexHarnessTolerance < C) :
    codexHarnessDerivedSpectralGraph.spViolation
      codexHarnessDerivedFailureSignal (codexHarnessTolerance / C) := by
  exact codexHarnessDerived_stage2_threshold.2 C (le_of_lt hC)

/-- Stackelberg-limit reading on the derived carrier: positive derived CV
eventually rules out stable spectral equilibria once capability crosses the
exact derived `C*` threshold. -/
theorem codexHarnessDerived_stage2_stackelberg_eventual_instability :
    ∃ κ₀ > 0, ∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
      ¬ SpectralStableEquilibrium codexHarnessDerivedSpectralGraph
        codexHarnessDerivedFailureSignal codexHarnessTolerance κ := by
  have hδ : 0 < codexHarnessTolerance := by
    native_decide
  have hcv :
      0 <
        codexHarnessDerivedSpectralGraph.cv
          codexHarnessDerivedFailureSignal := by
    native_decide
  exact eventually_no_stable_equilibrium_of_positive_cv
    codexHarnessDerivedSpectralGraph codexHarnessDerivedFailureSignal
    codexHarnessTolerance hδ hcv

/-!
## Stage 3: repaired typed routing lattice

The selected repair is a schema-level adjudication repair. Threshold metrics are
not modeled as terminal decisions; they are routed as adjudicated evidence, and
terminal escalation is made explicit by appending a downstream permit
adjudication suffix. This is a repaired typed graph for the case study, not a
claim that the live vendor protocol already implements this route.
-/

/-- Repair threshold gates by treating threshold satisfaction as evidence that
has passed explicit downstream adjudication. Content and exact-match hard-deny
routes are left untouched. -/
def codexHarnessAdjudicatedGate : AuditGate → AuditGate
  | .thresholdGate field min _decision => .thresholdGate field min .permit
  | gate => gate

/-- Apply the threshold-adjudication repair to binary nodes. -/
def codexHarnessAdjudicatedNode : AuditGovernanceNode → AuditGovernanceNode
  | .binary id name gates default combination =>
      .binary id name (gates.map codexHarnessAdjudicatedGate) default combination
  | node => node

/-- Repaired Codex graph: threshold routing is adjudicated, and every former
terminal node feeds the explicit permit suffix supplied by the substrate helper
`appendCompositionalPermitSuffix`. -/
def codexHarnessRepairedGovernanceGraph : AuditGovernanceGraph :=
  appendCompositionalPermitSuffix
    { nodes :=
        codexHooksExtractedGovernanceGraph.nodes.map
          codexHarnessAdjudicatedNode
      edges := codexHooksExtractedGovernanceGraph.edges }

/-- Audit subject for the repaired typed Codex graph. -/
def codexHarnessRepairedSubject : AuditSubject where
  graph := codexHarnessRepairedGovernanceGraph
  evalNode := auditEvaluateNode

/-- The repair adds exactly one explicit adjudication node. -/
theorem codexHarness_repaired_node_count :
    codexHarnessRepairedGovernanceGraph.nodes.length = 17 := by
  native_decide

/-- The repair preserves the eight original pass-through edges and adds one
suffix edge for each former terminal hook parser. -/
theorem codexHarness_repaired_edge_count :
    codexHarnessRepairedGovernanceGraph.edges.length = 16 := by
  native_decide

/-- The repair does not hide the finite audit workload: the synthetic corpus
still has the same 29 claims. -/
theorem codexHarness_repaired_claim_count :
    (auditGraphClaims codexHarnessRepairedSubject).length = 29 := by
  native_decide

/-!
## Stage 3.1: adjudicated-threshold graph predicate

The spectral repaired signal below is intentionally scoped to the concrete
typed repair. The predicate records the finite graph-side fact that every
threshold gate has been converted into adjudicated permit evidence.
-/

/-- A gate is adjudicated for this case-study repair when threshold gates no
longer carry terminal deny/escalate decisions. Non-threshold gates are outside
the threshold-repair surface. -/
def codexHarnessGateThresholdAdjudicated : AuditGate → Bool
  | .thresholdGate _ _ decision => decision == .permit
  | _ => true

/-- Node-level threshold-adjudication predicate for binary audit nodes. -/
def codexHarnessNodeThresholdAdjudicated : AuditGovernanceNode → Bool
  | .binary _ _ gates _ _ =>
      gates.all codexHarnessGateThresholdAdjudicated
  | _ => true

/-- Graph-level predicate characterizing the adjudicated threshold repair used
by the Codex harness case study. -/
def codexHarnessGraphThresholdAdjudicated
    (graph : AuditGovernanceGraph) : Bool :=
  graph.nodes.all codexHarnessNodeThresholdAdjudicated

/-- The repaired typed graph satisfies the finite adjudicated-threshold
predicate that grounds the zero repaired spectral signal. -/
theorem codexHarness_repaired_graph_threshold_adjudicated :
    codexHarnessGraphThresholdAdjudicated
      codexHarnessRepairedGovernanceGraph = true := by
  native_decide

/-!
## Stage 3.5: threshold removal in the spectral witness

The repaired spectral witness is also derived from the concrete repaired audit
graph. The repaired graph appends one explicit permit sink, so the projection has
seventeen nodes; threshold adjudication forces the audit-derived threshold signal
to zero coordinatewise.
-/

/-- Derived repaired seventeen-node carrier obtained by symmetrizing the repaired
audit graph, including the appended permit sink. -/
def codexHarnessDerivedRepairedSpectralGraph : GovGraph ℚ 17 :=
  codexHarnessRepairedGovernanceGraph.spectralProjection 17

/-- Derived repaired threshold signal from the repaired audit graph. -/
def codexHarnessDerivedRepairedFailureSignal : Fin 17 → ℚ :=
  auditGraphThresholdSignal codexHarnessRepairedGovernanceGraph

/-- Compatibility name for the repaired derived spectral projection consumed by
the existing Stage 4 endpoint theorems. -/
def codexHarnessRepairedSpectralGraph : GovGraph ℚ 17 :=
  codexHarnessDerivedRepairedSpectralGraph

/-- Compatibility name for the repaired derived threshold signal consumed by the
existing Stage 4 endpoint theorems. -/
def codexHarnessRepairedFailureSignal : Fin 17 → ℚ :=
  codexHarnessDerivedRepairedFailureSignal

/-- The repaired typed graph satisfies the generic adjudicated-threshold
predicate that drives the audit-derived spectral signal to zero. -/
theorem codexHarness_repaired_graph_threshold_adjudicated_generic :
    graph_threshold_adjudicated
      codexHarnessRepairedGovernanceGraph = true := by
  native_decide

/-- The generic adjudication chain forces the repaired derived threshold signal
to be zero coordinatewise. -/
theorem codexHarness_repaired_failure_signal_zero
    (i : Fin 17) :
    codexHarnessRepairedFailureSignal i = 0 := by
  simpa [codexHarnessRepairedFailureSignal,
    codexHarnessDerivedRepairedFailureSignal] using
    auditNodesThresholdSignalAt_eq_zero_of_all_adjudicated
      codexHarnessRepairedGovernanceGraph.nodes
      (by
        simpa [graph_threshold_adjudicated] using
          codexHarness_repaired_graph_threshold_adjudicated_generic)
      i.val

/-- The repaired derived spectral witness has zero consistency vulnerability,
derived from the repaired graph's adjudicated-threshold predicate. -/
theorem codexHarness_repaired_cv_value :
    codexHarnessRepairedSpectralGraph.cv
      codexHarnessRepairedFailureSignal = 0 := by
  exact
    auditGraphThresholdSignal_cv_zero_of_graph_threshold_adjudicated
      codexHarnessRepairedSpectralGraph
      codexHarnessRepairedGovernanceGraph
      codexHarness_repaired_graph_threshold_adjudicated_generic

/-- Stage 2 threshold-removal predicate consumed by Stage 4. -/
def codexHarnessStage2ThresholdRemoved : Prop :=
  ∀ C : ℚ, 0 < C →
    ¬ codexHarnessRepairedSpectralGraph.spViolation
      codexHarnessRepairedFailureSignal (codexHarnessTolerance / C)

/-- The repaired spectral witness reverses the Stage 2 failure inequality:
after adjudication removes the threshold signal, no positive capability remains
in the spectral violation region. -/
theorem codexHarness_stage2_threshold_removed :
    codexHarnessStage2ThresholdRemoved := by
  intro C hC hviol
  have hδ : 0 < codexHarnessTolerance := by
    native_decide
  have hscale : 0 < codexHarnessTolerance / C := div_pos hδ hC
  have hle :
      codexHarnessTolerance / C ≤
        codexHarnessRepairedSpectralGraph.cv
          codexHarnessRepairedFailureSignal :=
    (codexHarnessRepairedSpectralGraph.spViolation_iff_le_cv
      codexHarnessRepairedFailureSignal (codexHarnessTolerance / C)).mp hviol
  rw [codexHarness_repaired_cv_value] at hle
  exact (not_le_of_gt hscale) hle

/-- Stage 2 threshold removal forces the repaired spectral CV to be zero. -/
theorem codexHarness_repaired_cv_zero_of_stage2_threshold_removed
    (hremoved : codexHarnessStage2ThresholdRemoved) :
    codexHarnessRepairedSpectralGraph.cv
      codexHarnessRepairedFailureSignal = 0 := by
  by_contra hne
  have hδ : 0 < codexHarnessTolerance := by
    native_decide
  have hcv_pos :
      0 <
        codexHarnessRepairedSpectralGraph.cv
          codexHarnessRepairedFailureSignal :=
    lt_of_le_of_ne
      (codexHarnessRepairedSpectralGraph.cv_nonneg
        codexHarnessRepairedFailureSignal)
      (Ne.symm hne)
  let C : ℚ :=
    codexHarnessTolerance /
      codexHarnessRepairedSpectralGraph.cv
        codexHarnessRepairedFailureSignal
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos hδ hcv_pos
  have hscale :
      codexHarnessTolerance / C =
        codexHarnessRepairedSpectralGraph.cv
          codexHarnessRepairedFailureSignal := by
    dsimp [C]
    field_simp [ne_of_gt hδ, ne_of_gt hcv_pos]
  have hviol :
      codexHarnessRepairedSpectralGraph.spViolation
        codexHarnessRepairedFailureSignal
        (codexHarnessTolerance / C) := by
    rw [hscale]
    exact
      (codexHarnessRepairedSpectralGraph.spViolation_iff_le_cv
        codexHarnessRepairedFailureSignal
        (codexHarnessRepairedSpectralGraph.cv
          codexHarnessRepairedFailureSignal)).mpr le_rfl
  exact hremoved C hC hviol

/-!
## Stage 4: repaired graph admissibility

The final stage uses the scoped spectral witness as a load-bearing premise for
the finite audit path. Stage 2 threshold removal forces zero repaired spectral
CV; for the concrete Codex projection, zero CV forces the repaired threshold
signal to vanish coordinatewise. The audit-status proofs then unfold the
production dispatcher and feed the zero signal through the concrete
monotonicity and nonvacuity cores before composing the complete verdict.
-/

/-- The repaired Codex audit graph is acyclic, so dispatcher branches that are
guarded by cycle detection can reach their check-specific core evaluators. -/
theorem codexHarness_repaired_acyclic :
    detectAuditCycles codexHarnessRepairedSubject.graph = [] := by
  native_decide

/-- On this repaired spectral projection, each threshold-signal coordinate is
bounded by the graph-wide CV. This is the concrete bridge that lets Stage 2
threshold removal recover coordinatewise signal zero for the Codex harness. -/
theorem codexHarness_repaired_failure_signal_abs_le_cv
    (i : Fin 17) :
    |codexHarnessRepairedFailureSignal i| ≤
      codexHarnessRepairedSpectralGraph.cv
        codexHarnessRepairedFailureSignal := by
  rw [codexHarness_repaired_failure_signal_zero i,
    codexHarness_repaired_cv_value]
  norm_num

/-- Stage 2 threshold removal gives zero CV, and the concrete Codex spectral
projection turns zero CV into a coordinatewise zero repaired threshold signal. -/
theorem codexHarness_repaired_failure_signal_zero_of_cv_zero
    (hcv_zero :
      codexHarnessRepairedSpectralGraph.cv
        codexHarnessRepairedFailureSignal = 0) :
    ∀ i : Fin 17, codexHarnessRepairedFailureSignal i = 0 := by
  intro i
  have hle := codexHarness_repaired_failure_signal_abs_le_cv i
  rw [hcv_zero] at hle
  have hnonneg : 0 ≤ |codexHarnessRepairedFailureSignal i| := abs_nonneg _
  have habs : |codexHarnessRepairedFailureSignal i| = 0 :=
    le_antisymm hle hnonneg
  exact abs_eq_zero.mp habs

/-- The concrete monotonicity core is pinned to the localized repaired
threshold-signal coordinate rather than to an already-packaged status verdict. -/
theorem codexHarness_repaired_monotonicity_core_eq_spectral_signal :
      auditCheckMonotonicityCore codexHarnessRepairedSubject
          (auditGraphClaims codexHarnessRepairedSubject) =
        .ok
          (decide
            (codexHarnessRepairedFailureSignal ⟨7, by decide⟩ = 0)) := by
    native_decide

/-- The canonical schema-polarity monotonicity core is pinned to the same
localized repaired threshold-signal coordinate. -/
theorem codexHarness_repaired_polarity_monotonicity_core_eq_spectral_signal :
      auditCheckMonotonicityCorePolarityAware codexHarnessRepairedSubject
          (auditGraphClaims codexHarnessRepairedSubject) =
        .ok
          (decide
            (codexHarnessRepairedFailureSignal ⟨7, by decide⟩ = 0)) := by
    native_decide

/-- The concrete nonvacuity core is likewise exposed at the core-evaluator
level, so Stage 4 can compose audit checks instead of recomputing the verdict
as one opaque finite fact. -/
theorem codexHarness_repaired_nonvacuity_core_eq_spectral_signal :
    auditGraphNonvacuous codexHarnessRepairedSubject.evalNode
        codexHarnessRepairedSubject.graph
          (auditGraphClaims codexHarnessRepairedSubject) =
        .ok
          (decide
            (codexHarnessRepairedFailureSignal ⟨7, by decide⟩ = 0)) := by
    native_decide

/-- Spectral zero derives the repaired monotonicity pass by unfolding the
production audit-status dispatcher through its acyclic and monotonicity-core
branches. -/
theorem codexHarness_repaired_spectral_zero_derives_monotonicity_pass
    (hzero : ∀ i : Fin 17, codexHarnessRepairedFailureSignal i = 0) :
    auditCheckStatus codexHarnessRepairedSubject AuditCheck.monotonicity =
      .ok .passed := by
  have hsignal :
      decide
        (codexHarnessRepairedFailureSignal ⟨7, by decide⟩ = 0) = true := by
    have hcoord :
        codexHarnessRepairedFailureSignal ⟨7, by decide⟩ = 0 :=
      hzero ⟨7, by decide⟩
    rw [hcoord]
    rfl
  have hcore :
      auditCheckMonotonicityCorePolarityAware codexHarnessRepairedSubject
          (auditGraphClaims codexHarnessRepairedSubject) =
        .ok true := by
    rw [codexHarness_repaired_polarity_monotonicity_core_eq_spectral_signal]
    exact congrArg Except.ok hsignal
  simp [auditCheckStatus, codexHarness_repaired_acyclic, hcore]
  rfl

/-- The repaired typed Codex graph passes the monotonicity check that rejected
the extracted graph in Stage 1. -/
theorem codexHarness_repaired_monotonicity_passes :
    auditCheckStatus codexHarnessRepairedSubject AuditCheck.monotonicity =
      .ok .passed := by
  exact codexHarness_repaired_spectral_zero_derives_monotonicity_pass
    codexHarness_repaired_failure_signal_zero

/-- Compatibility alias for the earlier documentation-oriented theorem name.
The proof now delegates to the load-bearing spectral-to-status derivation. -/
theorem codexHarness_repaired_spectral_zero_packaged_with_monotonicity_pass
    (hzero : ∀ i : Fin 17, codexHarnessRepairedFailureSignal i = 0) :
    auditCheckStatus codexHarnessRepairedSubject AuditCheck.monotonicity =
      .ok .passed := by
  exact codexHarness_repaired_spectral_zero_derives_monotonicity_pass hzero

/-- Spectral zero derives the repaired nonvacuity pass by feeding the localized
zero threshold signal through the concrete nonvacuity core and the
`auditCheckStatus` nonvacuity branch. -/
theorem codexHarness_repaired_spectral_zero_derives_nonvacuity_pass
    (hzero : ∀ i : Fin 17, codexHarnessRepairedFailureSignal i = 0) :
    auditCheckStatus codexHarnessRepairedSubject AuditCheck.nonvacuous =
      .ok .passed := by
  have hsignal :
      decide
        (codexHarnessRepairedFailureSignal ⟨7, by decide⟩ = 0) = true := by
    have hcoord :
        codexHarnessRepairedFailureSignal ⟨7, by decide⟩ = 0 :=
      hzero ⟨7, by decide⟩
    rw [hcoord]
    rfl
  have hcore :
      auditGraphNonvacuous codexHarnessRepairedSubject.evalNode
          codexHarnessRepairedSubject.graph
          (auditGraphClaims codexHarnessRepairedSubject) =
        .ok true := by
    rw [codexHarness_repaired_nonvacuity_core_eq_spectral_signal]
    exact congrArg Except.ok hsignal
  simp [auditCheckStatus, hcore]
  rfl

/-- The explicit adjudication suffix closes the terminal-escalation nonvacuity
surface on the repaired typed graph. -/
theorem codexHarness_repaired_nonvacuity_passes :
    auditCheckStatus codexHarnessRepairedSubject AuditCheck.nonvacuous =
      .ok .passed := by
  exact codexHarness_repaired_spectral_zero_derives_nonvacuity_pass
    codexHarness_repaired_failure_signal_zero

theorem codexHarness_repaired_consistency_passes :
    auditCheckStatus codexHarnessRepairedSubject AuditCheck.consistency =
      .ok .passed := by
  native_decide

theorem codexHarness_repaired_solidarity_passes :
    auditCheckStatus codexHarnessRepairedSubject AuditCheck.solidarity =
      .ok .passed := by
  native_decide

theorem codexHarness_repaired_strategyproofness_passes :
    auditCheckStatus codexHarnessRepairedSubject AuditCheck.strategyproofness =
      .ok .passed := by
  native_decide

theorem codexHarness_repaired_certifiability_passes :
    auditCheckStatus codexHarnessRepairedSubject AuditCheck.certifiability =
      .ok .passed := by
  native_decide

theorem codexHarness_repaired_observable_determinacy_passes :
    auditCheckStatus codexHarnessRepairedSubject
        AuditCheck.observableDeterminacy =
      .ok .passed := by
  native_decide

theorem codexHarness_repaired_corrigibility_passes :
    auditCheckStatus codexHarnessRepairedSubject AuditCheck.corrigibility =
      .ok .passed := by
  native_decide

theorem codexHarness_repaired_compositional_safety_passes :
    auditCheckStatus codexHarnessRepairedSubject
        AuditCheck.compositionalSafety =
      .ok .passed := by
  native_decide

/-- Finite-audit path: the repaired typed Codex graph is legitimate under the
production theorem-facing governance-admissibility verdict. This is a concrete
audit-evaluator theorem, not a consequence of the spectral surrogate. -/
theorem codexHarness_stage4_finite_audit_path_repaired_admissible :
    governanceAdmissibilityVerdict codexHarnessRepairedSubject =
      AuditVerdict.legitimate := by
  native_decide

/-- Stage 2 threshold removal derives the finite repaired Codex audit verdict:
threshold removal gives zero CV, zero CV gives a zero repaired threshold signal,
the zero signal derives monotonicity and nonvacuity passes, and the named
per-check statuses compose through `firstFailedAuditCheck?` to legitimacy. -/
theorem codexHarness_stage4_threshold_removed_derives_finite_audit
    (hremoved : codexHarnessStage2ThresholdRemoved) :
    governanceAdmissibilityVerdict codexHarnessRepairedSubject =
      AuditVerdict.legitimate := by
  have hcv_zero :
      codexHarnessRepairedSpectralGraph.cv
        codexHarnessRepairedFailureSignal = 0 :=
    codexHarness_repaired_cv_zero_of_stage2_threshold_removed hremoved
  have hsignal_zero :
      ∀ i : Fin 17, codexHarnessRepairedFailureSignal i = 0 :=
    codexHarness_repaired_failure_signal_zero_of_cv_zero hcv_zero
  have hconsistency := codexHarness_repaired_consistency_passes
  have hsolidarity := codexHarness_repaired_solidarity_passes
  have hmonotonicity :=
    codexHarness_repaired_spectral_zero_derives_monotonicity_pass
      hsignal_zero
  have hstrategyproofness := codexHarness_repaired_strategyproofness_passes
  have hcertifiability := codexHarness_repaired_certifiability_passes
  have hobservable :=
    codexHarness_repaired_observable_determinacy_passes
  have hcorrigibility := codexHarness_repaired_corrigibility_passes
  have hcompositional :=
    codexHarness_repaired_compositional_safety_passes
  have hnonvacuity :=
    codexHarness_repaired_spectral_zero_derives_nonvacuity_pass
      hsignal_zero
  simp [governanceAdmissibilityVerdict, governanceAdmissibilityVerdict?,
    firstFailedAuditCheck?, auditCheckOrder, hconsistency, hsolidarity,
    hmonotonicity, hstrategyproofness, hcertifiability, hobservable,
    hcorrigibility, hcompositional, hnonvacuity]
  rfl

/-- Compatibility alias for the earlier packaging theorem name. The proof now
delegates to the load-bearing Stage 2-to-finite-audit derivation. -/
theorem codexHarness_stage4_threshold_removed_packaged_with_finite_audit
    (hremoved : codexHarnessStage2ThresholdRemoved) :
    governanceAdmissibilityVerdict codexHarnessRepairedSubject =
      AuditVerdict.legitimate := by
  exact codexHarness_stage4_threshold_removed_derives_finite_audit hremoved

/-- Final finite-audit case-study theorem: after the repaired routing/lattice
structure is applied to the typed graph, the production governance
admissibility verdict flips to legitimate. -/
theorem codexHarness_stage4_repaired_admissible :
    governanceAdmissibilityVerdict codexHarnessRepairedSubject =
      AuditVerdict.legitimate := by
  exact codexHarness_stage4_threshold_removed_derives_finite_audit
    codexHarness_stage2_threshold_removed

/-!
## Stage 5: repair minimality scope

The full universal minimality claim would quantify over every strict subset of
individual threshold-gate repairs and prove that each such graph remains
inadmissible. This file instead proves a scoped finite witness: the concrete
strictly weaker repair that leaves `hook_registration` terminal while permitting
the other threshold fields still fails the production audit. That establishes a
non-vacuous strict-subset counterexample and marks full threshold-subset
minimality as future work rather than overclaiming it here. The older
`block_reason` carve-out is retained below as a vacuous fixture: that field does
not occur in the committed graph's threshold gates.
-/

/-- Strict subset relation for field-level threshold repair policies. `left` is
strictly weaker than `right` when every field repaired by `left` is repaired by
`right`, and at least one field repaired by `right` is not repaired by `left`. -/
def codexHarnessThresholdFieldRepairStrictSubset
    (left right : AuditMetricField → Bool) : Prop :=
  (∀ field, left field = true → right field = true) ∧
    ∃ field, right field = true ∧ left field = false

/-- Field-level policy for the full Stage 3 repair: every threshold field is
converted to adjudicated permit evidence. -/
def codexHarnessPermitAllThresholdFields (_field : AuditMetricField) : Bool :=
  true

/-- Strictly weaker tested policy: all threshold fields are repaired except the
failing committed `hook_registration` threshold. -/
def codexHarnessPermitThresholdFieldsExceptHookRegistration
    (field : AuditMetricField) : Bool :=
  field != "hook_registration"

/-- Vacuous legacy policy: all threshold fields are repaired except
`block_reason`, a field that does not occur in the committed Codex graph's
threshold gates. -/
def codexHarnessPermitThresholdFieldsExceptBlockReason
    (field : AuditMetricField) : Bool :=
  field != "block_reason"

/-- Apply a field-level threshold repair policy to a gate. Non-threshold gates
are outside the repair surface. -/
def codexHarnessAdjudicatedGateByFieldPolicy
    (repairField : AuditMetricField → Bool) : AuditGate → AuditGate
  | .thresholdGate field min decision =>
      if repairField field then
        .thresholdGate field min .permit
      else
        .thresholdGate field min decision
  | gate => gate

/-- Apply a field-level threshold repair policy to binary audit nodes. -/
def codexHarnessAdjudicatedNodeByFieldPolicy
    (repairField : AuditMetricField → Bool) :
    AuditGovernanceNode → AuditGovernanceNode
  | .binary id name gates default combination =>
      .binary id name
        (gates.map (codexHarnessAdjudicatedGateByFieldPolicy repairField))
        default combination
  | node => node

/-- Repaired Codex graph under a field-level threshold repair policy. -/
def codexHarnessRepairedGovernanceGraphByFieldPolicy
    (repairField : AuditMetricField → Bool) : AuditGovernanceGraph :=
  appendCompositionalPermitSuffix
    { nodes :=
        codexHooksExtractedGovernanceGraph.nodes.map
          (codexHarnessAdjudicatedNodeByFieldPolicy repairField)
      edges := codexHooksExtractedGovernanceGraph.edges }

/-- Audit subject for the real strictly weaker tested repair that leaves
`hook_registration` unrepaired. -/
def codexHarnessWithoutHookRegistrationRepairSubject : AuditSubject where
  graph :=
    codexHarnessRepairedGovernanceGraphByFieldPolicy
      codexHarnessPermitThresholdFieldsExceptHookRegistration
  evalNode := auditEvaluateNode

/-- Audit subject for the vacuous legacy carve-out that leaves `block_reason`
unrepaired, a field absent from the committed threshold gates. -/
def codexHarnessWithoutBlockReasonRepairSubject : AuditSubject where
  graph :=
    codexHarnessRepairedGovernanceGraphByFieldPolicy
      codexHarnessPermitThresholdFieldsExceptBlockReason
  evalNode := auditEvaluateNode

/-- The tested no-`hook_registration` policy is a genuine strict subset of the
full threshold-field repair policy. -/
theorem codexHarness_without_hook_registration_repair_strict_subset :
    codexHarnessThresholdFieldRepairStrictSubset
      codexHarnessPermitThresholdFieldsExceptHookRegistration
      codexHarnessPermitAllThresholdFields := by
  constructor
  · intro field _hfield
    simp [codexHarnessPermitAllThresholdFields]
  · exact ⟨"hook_registration", by
      simp [codexHarnessPermitAllThresholdFields,
        codexHarnessPermitThresholdFieldsExceptHookRegistration]⟩

/-- Concrete strict-subset probe: if the failing `hook_registration` threshold
field is not adjudicated, the repaired subject remains rejected by monotonicity. -/
theorem codexHarness_without_hook_registration_repair_rejected_monotonicity :
    governanceAdmissibilityVerdict
        codexHarnessWithoutHookRegistrationRepairSubject =
      AuditVerdict.rejected AuditCheck.monotonicity := by
  native_decide

/-- The tested no-`block_reason` policy is a genuine strict subset of the full
threshold-field repair policy as a field-level predicate, but the carve-out is
vacuous on this graph because no committed threshold gate uses `block_reason`. -/
theorem codexHarness_without_block_reason_repair_strict_subset :
    codexHarnessThresholdFieldRepairStrictSubset
      codexHarnessPermitThresholdFieldsExceptBlockReason
      codexHarnessPermitAllThresholdFields := by
  constructor
  · intro field _hfield
    simp [codexHarnessPermitAllThresholdFields]
  · exact ⟨"block_reason", by
      simp [codexHarnessPermitAllThresholdFields,
        codexHarnessPermitThresholdFieldsExceptBlockReason]⟩

/-- Vacuous carve-out check: under schema-derived monotonicity, repairing every
committed threshold field except absent `block_reason` is graph-identical in the
load-bearing threshold surface and therefore legitimate for this finite subject. -/
theorem codexHarness_without_block_reason_repair_legitimate :
    governanceAdmissibilityVerdict
        codexHarnessWithoutBlockReasonRepairSubject =
      AuditVerdict.legitimate := by
  native_decide

/-- Scope-framed strict-subset comparison under schema-derived polarity. The
load-bearing no-`hook_registration` strict subset remains rejected, while the
full repair is legitimate. The old no-`block_reason` carve-out is tracked
separately as a vacuous strict field-policy subset on this graph. -/
theorem codexHarness_threshold_repair_strict_subset_legitimacy_comparison :
    codexHarnessThresholdFieldRepairStrictSubset
        codexHarnessPermitThresholdFieldsExceptHookRegistration
        codexHarnessPermitAllThresholdFields ∧
      governanceAdmissibilityVerdict
          codexHarnessWithoutHookRegistrationRepairSubject =
        AuditVerdict.rejected AuditCheck.monotonicity ∧
      governanceAdmissibilityVerdict codexHarnessRepairedSubject =
        AuditVerdict.legitimate ∧
      codexHarnessThresholdFieldRepairStrictSubset
        codexHarnessPermitThresholdFieldsExceptBlockReason
        codexHarnessPermitAllThresholdFields ∧
      governanceAdmissibilityVerdict
          codexHarnessWithoutBlockReasonRepairSubject =
        AuditVerdict.legitimate := by
  exact
    ⟨codexHarness_without_hook_registration_repair_strict_subset,
      codexHarness_without_hook_registration_repair_rejected_monotonicity,
      codexHarness_stage4_repaired_admissible,
      codexHarness_without_block_reason_repair_strict_subset,
      codexHarness_without_block_reason_repair_legitimate⟩

/-!
## Binary-facing headline bridge

The v1.0.0 audit binary consumes the end-to-end bridge after the legacy line
anchors above, so public claim-ledger citations remain stable.
-/

/-- Honest scalar summary for the binary evidence bundle: the extracted Codex
graph has the recorded finite cardinalities, and the derived Stage 2 spectral
carrier has exact C* `1/10`. -/
theorem codexExtractedGraphCardinalityAndCStar :
    codexHooksExtractedGovernanceGraph.nodes.length = 16 ∧
      codexHooksExtractedGovernanceGraph.edges.length = 8 ∧
      C_star codexHarnessDerivedSpectralGraph
        codexHarnessDerivedFailureSignal codexHarnessTolerance = 1 / 10 := by
  exact ⟨codexHarness_extracted_node_count,
    codexHarness_extracted_edge_count, codexHarnessDerived_C_star_value⟩

/-- Honest binary-facing Codex lane facts: the committed extracted hook fixture
fails monotonicity, and the threshold carrier derived from that same extracted
topology has exact critical capability C* = `1/10`. -/
theorem codexCliRejectionAndThresholdFacts :
    codexHooksGovernanceAdmissibilityVerdict =
        AuditVerdict.rejected AuditCheck.monotonicity ∧
      codexHooksExtractedGovernanceGraph.nodes.length = 16 ∧
      codexHooksExtractedGovernanceGraph.edges.length = 8 ∧
      C_star codexHarnessDerivedSpectralGraph
        codexHarnessDerivedFailureSignal codexHarnessTolerance = 1 / 10 := by
  exact ⟨codexHarness_stage1_detects_monotonicity_failure,
    codexExtractedGraphCardinalityAndCStar.1,
    codexExtractedGraphCardinalityAndCStar.2.1,
    codexExtractedGraphCardinalityAndCStar.2.2⟩

end Legitimacy
