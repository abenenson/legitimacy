/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Bridges.AuditSpectralProjection
import Legitimacy.Results.ClaudeAgentSDKAdmissibilityAudit
import Legitimacy.Spectral.Capacity.CriticalCapability
import Legitimacy.Spectral.Dynamics.StackelbergConvergence

/-!
# Legitimacy.CaseStudies.ClaudeAgentSdkHarness

Derived spectral case study for the extracted Claude Agent SDK hooks governance
harness.

The Stage 2 carrier below is computed from the committed extracted graph by
symmetrizing its pass-through registration-to-handler topology. The threshold
signal is computed from the extracted node-indexed threshold gates.
-/

set_option autoImplicit false

namespace Legitimacy

/-!
## Stage 1: extracted fixture and audit detection
-/

/-!
## Stage 2: critical capability threshold
-/

/-- Derived twenty-two-node spectral carrier obtained by symmetrizing the
committed extracted Claude Agent SDK audit graph's pass-through edges. -/
def claudeAgentSdkHarnessDerivedSpectralGraph : GovGraph ℚ 22 :=
  claudeAgentSDKHooksExtractedGovernanceGraph.spectralProjection 22

/-- Derived threshold signal from the committed extracted Claude Agent SDK
audit graph: handler and schema nodes carry zero, while registration nodes
carry the `hook_registration`/`.escalate` component `1`. -/
def claudeAgentSdkHarnessDerivedFailureSignal : Fin 22 → ℚ :=
  auditGraphThresholdSignal claudeAgentSDKHooksExtractedGovernanceGraph

/-- Symmetric edge indicator for the eight extracted registration/handler
pass-through pairs. -/
def claudeAgentSdkHarnessDerivedPair (i j : Fin 22) : Bool :=
  (i.val == 6 && j.val == 1) || (i.val == 1 && j.val == 6) ||
  (i.val == 7 && j.val == 2) || (i.val == 2 && j.val == 7) ||
  (i.val == 8 && j.val == 4) || (i.val == 4 && j.val == 8) ||
  (i.val == 9 && j.val == 3) || (i.val == 3 && j.val == 9) ||
  (i.val == 10 && j.val == 5) || (i.val == 5 && j.val == 10) ||
  (i.val == 11 && j.val == 14) || (i.val == 14 && j.val == 11) ||
  (i.val == 12 && j.val == 15) || (i.val == 15 && j.val == 12) ||
  (i.val == 13 && j.val == 16) || (i.val == 16 && j.val == 13)

/-- The derived carrier keeps all eight extracted pass-through pairs and no
self-loop is present. -/
theorem claudeAgentSdkHarnessDerivedSpectralGraph_weights_pair :
    ∀ i j : Fin 22,
      claudeAgentSdkHarnessDerivedSpectralGraph.weights i j =
        if claudeAgentSdkHarnessDerivedPair i j = true then 1 else 0 := by
  native_decide

/-- The derived threshold signal is zero off registration nodes and one on the
eight registration nodes. -/
theorem claudeAgentSdkHarnessDerivedFailureSignal_vector :
    claudeAgentSdkHarnessDerivedFailureSignal =
      ![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  native_decide

/-- The derived twenty-two-node carrier is eight disconnected `K₂` components
plus six isolated vertices, so vertices outside the extracted hook pairs have
zero edge weight. Consequently the real Laplacian gap is `λ₂ = 0`; the
`cv`/`C*`/Stackelberg-limit results below consume only positive CV and
deliberately do not instantiate the positive-spectral-gap lower-bound theorems.
-/
theorem claudeAgentSdkHarnessDerivedSpectralGraph_pairwise_disconnected :
    ∀ i j : Fin 22, claudeAgentSdkHarnessDerivedPair i j = false →
      claudeAgentSdkHarnessDerivedSpectralGraph.weights i j = 0 := by
  native_decide

/-- The derived Claude Agent SDK spectral carrier has exact consistency
vulnerability 1 under the audit-derived threshold signal. -/
theorem claudeAgentSdkHarnessDerived_cv_value :
    claudeAgentSdkHarnessDerivedSpectralGraph.cv
      claudeAgentSdkHarnessDerivedFailureSignal = 1 := by
  native_decide

/-- Exact critical capability value on the derived carrier: `1/10`, unchanged
from the legacy hand-authored carrier. -/
theorem claudeAgentSdkHarnessDerived_C_star_value :
    C_star claudeAgentSdkHarnessDerivedSpectralGraph
        claudeAgentSdkHarnessDerivedFailureSignal
        claudeAgentSdkHarnessTolerance = 1 / 10 := by
  native_decide

/-- Below derived `C*` the spectral surrogate has no reachable perturbation at
the capability-scaled tolerance; at or above derived `C*` the perturbation
exists. -/
theorem claudeAgentSdkHarnessDerived_stage2_threshold :
    (∀ C : ℚ, 0 < C →
        C < C_star claudeAgentSdkHarnessDerivedSpectralGraph
            claudeAgentSdkHarnessDerivedFailureSignal
            claudeAgentSdkHarnessTolerance →
          ¬ claudeAgentSdkHarnessDerivedSpectralGraph.spViolation
            claudeAgentSdkHarnessDerivedFailureSignal
            (claudeAgentSdkHarnessTolerance / C)) ∧
      (∀ C : ℚ,
        C_star claudeAgentSdkHarnessDerivedSpectralGraph
            claudeAgentSdkHarnessDerivedFailureSignal
            claudeAgentSdkHarnessTolerance ≤ C →
          claudeAgentSdkHarnessDerivedSpectralGraph.spViolation
            claudeAgentSdkHarnessDerivedFailureSignal
            (claudeAgentSdkHarnessTolerance / C)) := by
  have hδ : 0 < claudeAgentSdkHarnessTolerance := by
    native_decide
  have hcv :
      0 <
        claudeAgentSdkHarnessDerivedSpectralGraph.cv
          claudeAgentSdkHarnessDerivedFailureSignal := by
    native_decide
  exact C_star_exists claudeAgentSdkHarnessDerivedSpectralGraph
    claudeAgentSdkHarnessDerivedFailureSignal
    claudeAgentSdkHarnessTolerance hδ hcv

/-- Operational high-capability side of the derived phase transition. -/
theorem claudeAgentSdkHarnessDerived_stage2_failure_above_C_star
    (C : ℚ)
    (hC :
      C_star claudeAgentSdkHarnessDerivedSpectralGraph
          claudeAgentSdkHarnessDerivedFailureSignal
          claudeAgentSdkHarnessTolerance < C) :
    claudeAgentSdkHarnessDerivedSpectralGraph.spViolation
      claudeAgentSdkHarnessDerivedFailureSignal
      (claudeAgentSdkHarnessTolerance / C) := by
  exact claudeAgentSdkHarnessDerived_stage2_threshold.2 C (le_of_lt hC)

/-- Stackelberg-limit reading on the derived carrier: positive derived CV
eventually rules out stable spectral equilibria once capability crosses the
exact derived `C*` threshold. -/
theorem claudeAgentSdkHarnessDerived_stage2_stackelberg_eventual_instability :
    ∃ κ₀ > 0, ∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
      ¬ SpectralStableEquilibrium claudeAgentSdkHarnessDerivedSpectralGraph
        claudeAgentSdkHarnessDerivedFailureSignal
        claudeAgentSdkHarnessTolerance κ := by
  have hδ : 0 < claudeAgentSdkHarnessTolerance := by
    native_decide
  have hcv :
      0 <
        claudeAgentSdkHarnessDerivedSpectralGraph.cv
          claudeAgentSdkHarnessDerivedFailureSignal := by
    native_decide
  exact eventually_no_stable_equilibrium_of_positive_cv
    claudeAgentSdkHarnessDerivedSpectralGraph
    claudeAgentSdkHarnessDerivedFailureSignal
    claudeAgentSdkHarnessTolerance hδ hcv

/-- The adjudicated threshold repair has zero audit-derived threshold CV on the
derived Claude Agent SDK carrier. -/
theorem claudeAgentSdkHarnessDerived_repaired_cv_zero :
    claudeAgentSdkHarnessDerivedSpectralGraph.cv
      (auditGraphThresholdSignal
        (adjudicateThresholdGraph
          claudeAgentSDKHooksExtractedGovernanceGraph)) = 0 := by
  exact
    adjudicateThresholdGraph_cv_zero
      claudeAgentSdkHarnessDerivedSpectralGraph
      claudeAgentSDKHooksExtractedGovernanceGraph

/-!
## Binary-facing headline bridge
-/

/-- Honest scalar summary for the binary evidence bundle: the extracted Claude
Agent SDK graph has the recorded finite cardinalities, and the derived Stage 2
spectral carrier has exact C* `1/10`. -/
theorem claudeAgentSdkExtractedGraphCardinalityAndCStar :
    claudeAgentSDKHooksExtractedGovernanceGraph.nodes.length = 22 ∧
      claudeAgentSDKHooksExtractedGovernanceGraph.edges.length = 8 ∧
      C_star claudeAgentSdkHarnessDerivedSpectralGraph
        claudeAgentSdkHarnessDerivedFailureSignal
        claudeAgentSdkHarnessTolerance = 1 / 10 := by
  exact ⟨claudeAgentSdkHarness_extracted_node_count,
    claudeAgentSdkHarness_extracted_edge_count,
    claudeAgentSdkHarnessDerived_C_star_value⟩

/-- Honest binary-facing Claude Agent SDK lane facts: the committed extracted
hook fixture fails monotonicity, and the threshold carrier derived from that
same extracted topology has exact critical capability C* = `1/10`. -/
theorem claudeAgentSdkRejectionAndThresholdFacts :
    claudeAgentSDKHooksGovernanceAdmissibilityVerdict =
        AuditVerdict.rejected AuditCheck.monotonicity ∧
      claudeAgentSDKHooksExtractedGovernanceGraph.nodes.length = 22 ∧
      claudeAgentSDKHooksExtractedGovernanceGraph.edges.length = 8 ∧
      C_star claudeAgentSdkHarnessDerivedSpectralGraph
        claudeAgentSdkHarnessDerivedFailureSignal
        claudeAgentSdkHarnessTolerance = 1 / 10 := by
  exact ⟨claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity,
    claudeAgentSdkExtractedGraphCardinalityAndCStar.1,
    claudeAgentSdkExtractedGraphCardinalityAndCStar.2.1,
    claudeAgentSdkExtractedGraphCardinalityAndCStar.2.2⟩

end Legitimacy
