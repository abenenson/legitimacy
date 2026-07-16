/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Bridges.AuditSpectralProjection
import Legitimacy.Results.ClaudeCodeAdmissibilityAudit
import Legitimacy.Spectral.Capacity.CriticalCapability
import Legitimacy.Spectral.Dynamics.StackelbergConvergence

/-!
# Legitimacy.CaseStudies.ClaudeCodeHarness

Derived spectral case study for the extracted Claude Code public hook
governance harness.

The Stage 2 carrier below is computed from the committed extracted graph by
symmetrizing its pass-through registration-to-handler topology. The threshold
signal is computed from the extracted node-indexed threshold gates.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset

/-!
## Stage 1: extracted fixture and audit detection
-/

/-!
## Stage 2: critical capability threshold
-/

/-- Derived thirty-one-node spectral carrier obtained by symmetrizing the
committed extracted Claude Code audit graph's pass-through edges. -/
def claudeCodeHarnessDerivedSpectralGraph : GovGraph ℚ 31 :=
  claudeCodeHooksExtractedGovernanceGraph.spectralProjection 31

/-- Derived threshold signal from the committed extracted Claude Code audit
graph: handler and schema nodes carry zero, while registration nodes carry the
`hook_registration`/`.escalate` component `1`. -/
def claudeCodeHarnessDerivedFailureSignal : Fin 31 → ℚ :=
  auditGraphThresholdSignal claudeCodeHooksExtractedGovernanceGraph

/-- Symmetric edge indicator for the fourteen extracted registration/handler
pass-through pairs. -/
def claudeCodeHarnessDerivedPair (i j : Fin 31) : Bool :=
  (decide (10 ≤ i.val) && decide (i.val ≤ 16) &&
      decide (i.val = j.val + 7)) ||
  (decide (10 ≤ j.val) && decide (j.val ≤ 16) &&
      decide (j.val = i.val + 7)) ||
  (decide (17 ≤ i.val) && decide (i.val ≤ 23) &&
      decide (j.val = i.val + 7)) ||
  (decide (17 ≤ j.val) && decide (j.val ≤ 23) &&
      decide (i.val = j.val + 7))

/-- The derived carrier keeps all fourteen extracted pass-through pairs and no
self-loop is present. -/
theorem claudeCodeHarnessDerivedSpectralGraph_weights_pair :
    ∀ i j : Fin 31,
      claudeCodeHarnessDerivedSpectralGraph.weights i j =
        if claudeCodeHarnessDerivedPair i j = true then 1 else 0 := by
  native_decide

/-- The derived threshold signal is zero off registration nodes and one exactly
on the fourteen registration positions 10 through 23. -/
theorem claudeCodeHarnessDerivedFailureSignal_vector :
    ∀ i : Fin 31,
      claudeCodeHarnessDerivedFailureSignal i =
        if 10 ≤ i.val ∧ i.val ≤ 23 then 1 else 0 := by
  intro i
  fin_cases i <;> native_decide

/-- The derived thirty-one-node carrier is fourteen disconnected `K₂`
components plus three isolated vertices, so vertices outside the extracted hook
pairs have zero edge weight. Consequently the real Laplacian gap is `λ₂ = 0`;
the `cv`/`C*`/Stackelberg-limit results below consume only positive CV and
deliberately do not instantiate the positive-spectral-gap lower-bound theorems.
-/
theorem claudeCodeHarnessDerivedSpectralGraph_pairwise_disconnected :
    ∀ i j : Fin 31, claudeCodeHarnessDerivedPair i j = false →
      claudeCodeHarnessDerivedSpectralGraph.weights i j = 0 := by
  intro i j hpair
  rw [claudeCodeHarnessDerivedSpectralGraph_weights_pair i j]
  simp [hpair]

/-- Weighted-average nonnegativity for the Code derived carrier under a
nonnegative signal. -/
lemma claudeCodeHarnessDerived_gov_nonneg_of_signal_nonneg
    (s : Fin 31 → ℚ)
    (hs0 : ∀ j : Fin 31, 0 ≤ s j)
    (i : Fin 31)
    (hD : 0 < claudeCodeHarnessDerivedSpectralGraph.deg i) :
    0 ≤ claudeCodeHarnessDerivedSpectralGraph.gov s i := by
  simpa [GovGraph.gov, GovGraph.deg] using
    wavg_ge (Finset.univ (α := Fin 31))
      (fun j => claudeCodeHarnessDerivedSpectralGraph.W i j) s 0
      (fun j _ => claudeCodeHarnessDerivedSpectralGraph.nonneg i j)
      (fun j _ => hs0 j) hD

/-- Weighted-average upper bound for the Code derived carrier under a
signal bounded by one. -/
lemma claudeCodeHarnessDerived_gov_le_one_of_signal_le_one
    (s : Fin 31 → ℚ)
    (hs1 : ∀ j : Fin 31, s j ≤ 1)
    (i : Fin 31)
    (hD : 0 < claudeCodeHarnessDerivedSpectralGraph.deg i) :
    claudeCodeHarnessDerivedSpectralGraph.gov s i ≤ 1 := by
  simpa [GovGraph.gov, GovGraph.deg] using
    wavg_le (Finset.univ (α := Fin 31))
      (fun j => claudeCodeHarnessDerivedSpectralGraph.W i j) s 1
      (fun j _ => claudeCodeHarnessDerivedSpectralGraph.nonneg i j)
      (fun j _ => hs1 j) hD

/-- Every single-removal perturbation on the derived Code carrier is bounded
by the unit 0/1 threshold-signal range. -/
lemma claudeCodeHarnessDerived_pointwise_perturbation_le_one
    (k i : Fin 31) :
    |claudeCodeHarnessDerivedSpectralGraph.gov
        claudeCodeHarnessDerivedFailureSignal i -
      claudeCodeHarnessDerivedSpectralGraph.govRemoved
        claudeCodeHarnessDerivedFailureSignal k i| ≤ 1 := by
  have hs0 :
      ∀ j : Fin 31, 0 ≤ claudeCodeHarnessDerivedFailureSignal j := by
    native_decide
  have hs1 :
      ∀ j : Fin 31, claudeCodeHarnessDerivedFailureSignal j ≤ 1 := by
    native_decide
  have hsr :
      ∀ a b : Fin 31,
        |claudeCodeHarnessDerivedFailureSignal a -
          claudeCodeHarnessDerivedFailureSignal b| ≤ 1 := by
    intro a b
    have ha0 := hs0 a
    have ha1 := hs1 a
    have hb0 := hs0 b
    have hb1 := hs1 b
    rw [abs_le]
    constructor <;> linarith
  by_cases hD : 0 < claudeCodeHarnessDerivedSpectralGraph.deg i
  · by_cases hD' :
        0 < claudeCodeHarnessDerivedSpectralGraph.degRemoved k i
    · exact
        claudeCodeHarnessDerivedSpectralGraph.perturbation_le_signalRange
          claudeCodeHarnessDerivedFailureSignal 1 (by norm_num) hsr k i
          hD hD'
    · have hD'zero :
          claudeCodeHarnessDerivedSpectralGraph.degRemoved k i = 0 := by
        exact le_antisymm (le_of_not_gt hD')
          (claudeCodeHarnessDerivedSpectralGraph.degRemoved_nonneg k i)
      have hgov0 :
          0 ≤
            claudeCodeHarnessDerivedSpectralGraph.gov
              claudeCodeHarnessDerivedFailureSignal i :=
        claudeCodeHarnessDerived_gov_nonneg_of_signal_nonneg
          claudeCodeHarnessDerivedFailureSignal hs0 i hD
      have hgov1 :
          claudeCodeHarnessDerivedSpectralGraph.gov
              claudeCodeHarnessDerivedFailureSignal i ≤ 1 :=
        claudeCodeHarnessDerived_gov_le_one_of_signal_le_one
          claudeCodeHarnessDerivedFailureSignal hs1 i hD
      have hremoved :
          claudeCodeHarnessDerivedSpectralGraph.govRemoved
            claudeCodeHarnessDerivedFailureSignal k i = 0 := by
        simp [GovGraph.govRemoved, hD'zero]
      rw [hremoved, sub_zero, abs_of_nonneg hgov0]
      exact hgov1
  · have hDzero :
        claudeCodeHarnessDerivedSpectralGraph.deg i = 0 := by
      exact le_antisymm (le_of_not_gt hD)
        (claudeCodeHarnessDerivedSpectralGraph.deg_nonneg i)
    have hD'zero :
        claudeCodeHarnessDerivedSpectralGraph.degRemoved k i = 0 := by
      have hdecomp :=
        claudeCodeHarnessDerivedSpectralGraph.deg_eq_weight_add_degRemoved
          k i
      have hnonneg := claudeCodeHarnessDerivedSpectralGraph.nonneg i k
      have hrem_nonneg :=
        claudeCodeHarnessDerivedSpectralGraph.degRemoved_nonneg k i
      linarith
    have hgov :
        claudeCodeHarnessDerivedSpectralGraph.gov
          claudeCodeHarnessDerivedFailureSignal i = 0 := by
      simp [GovGraph.gov, hDzero]
    have hremoved :
        claudeCodeHarnessDerivedSpectralGraph.govRemoved
          claudeCodeHarnessDerivedFailureSignal k i = 0 := by
      simp [GovGraph.govRemoved, hD'zero]
    rw [hgov, hremoved, sub_self, abs_zero]
    norm_num

/-- The derived Claude Code spectral carrier has exact consistency
vulnerability 1 under the audit-derived threshold signal. -/
theorem claudeCodeHarnessDerived_cv_value :
    claudeCodeHarnessDerivedSpectralGraph.cv
      claudeCodeHarnessDerivedFailureSignal = 1 := by
  apply le_antisymm
  · unfold GovGraph.cv
    apply Finset.sup'_le
    intro p _hp
    exact claudeCodeHarnessDerived_pointwise_perturbation_le_one p.1 p.2
  · unfold GovGraph.cv
    calc
      (1 : ℚ) =
          |claudeCodeHarnessDerivedSpectralGraph.gov
              claudeCodeHarnessDerivedFailureSignal (3 : Fin 31) -
            claudeCodeHarnessDerivedSpectralGraph.govRemoved
              claudeCodeHarnessDerivedFailureSignal (10 : Fin 31)
              (3 : Fin 31)| := by
            native_decide
      _ ≤ Finset.sup' (Finset.univ (α := Fin 31 × Fin 31))
          (Finset.univ_nonempty)
          (fun p =>
            |claudeCodeHarnessDerivedSpectralGraph.gov
                claudeCodeHarnessDerivedFailureSignal p.2 -
              claudeCodeHarnessDerivedSpectralGraph.govRemoved
                claudeCodeHarnessDerivedFailureSignal p.1 p.2|) := by
            exact Finset.le_sup'
              (s := Finset.univ)
              (f := fun p : Fin 31 × Fin 31 =>
                |claudeCodeHarnessDerivedSpectralGraph.gov
                    claudeCodeHarnessDerivedFailureSignal p.2 -
                  claudeCodeHarnessDerivedSpectralGraph.govRemoved
                    claudeCodeHarnessDerivedFailureSignal p.1 p.2|)
              (by simp :
                ((10 : Fin 31), (3 : Fin 31)) ∈
                  (Finset.univ : Finset (Fin 31 × Fin 31)))

/-- Exact critical capability value on the derived carrier: `1/10`, unchanged
from the legacy hand-authored carrier. -/
theorem claudeCodeHarnessDerived_C_star_value :
    C_star claudeCodeHarnessDerivedSpectralGraph
        claudeCodeHarnessDerivedFailureSignal
        claudeCodeHarnessTolerance = 1 / 10 := by
  simp [C_star, claudeCodeHarnessDerived_cv_value,
    claudeCodeHarnessTolerance]

/-- Below derived `C*` the spectral surrogate has no reachable perturbation at
the capability-scaled tolerance; at or above derived `C*` the perturbation
exists. -/
theorem claudeCodeHarnessDerived_stage2_threshold :
    (∀ C : ℚ, 0 < C →
        C < C_star claudeCodeHarnessDerivedSpectralGraph
            claudeCodeHarnessDerivedFailureSignal
            claudeCodeHarnessTolerance →
          ¬ claudeCodeHarnessDerivedSpectralGraph.spViolation
            claudeCodeHarnessDerivedFailureSignal
            (claudeCodeHarnessTolerance / C)) ∧
      (∀ C : ℚ,
        C_star claudeCodeHarnessDerivedSpectralGraph
            claudeCodeHarnessDerivedFailureSignal
            claudeCodeHarnessTolerance ≤ C →
          claudeCodeHarnessDerivedSpectralGraph.spViolation
            claudeCodeHarnessDerivedFailureSignal
            (claudeCodeHarnessTolerance / C)) := by
  have hδ : 0 < claudeCodeHarnessTolerance := by
    native_decide
  have hcv :
      0 <
        claudeCodeHarnessDerivedSpectralGraph.cv
          claudeCodeHarnessDerivedFailureSignal := by
    rw [claudeCodeHarnessDerived_cv_value]
    norm_num
  exact C_star_exists claudeCodeHarnessDerivedSpectralGraph
    claudeCodeHarnessDerivedFailureSignal
    claudeCodeHarnessTolerance hδ hcv

/-- Operational high-capability side of the derived phase transition. -/
theorem claudeCodeHarnessDerived_stage2_failure_above_C_star
    (C : ℚ)
    (hC :
      C_star claudeCodeHarnessDerivedSpectralGraph
          claudeCodeHarnessDerivedFailureSignal
          claudeCodeHarnessTolerance < C) :
    claudeCodeHarnessDerivedSpectralGraph.spViolation
      claudeCodeHarnessDerivedFailureSignal
      (claudeCodeHarnessTolerance / C) := by
  exact claudeCodeHarnessDerived_stage2_threshold.2 C (le_of_lt hC)

/-- Stackelberg-limit reading on the derived carrier: positive derived CV
eventually rules out stable spectral equilibria once capability crosses the
exact derived `C*` threshold. -/
theorem claudeCodeHarnessDerived_stage2_stackelberg_eventual_instability :
    ∃ κ₀ > 0, ∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
      ¬ SpectralStableEquilibrium claudeCodeHarnessDerivedSpectralGraph
        claudeCodeHarnessDerivedFailureSignal
        claudeCodeHarnessTolerance κ := by
  have hδ : 0 < claudeCodeHarnessTolerance := by
    native_decide
  have hcv :
      0 <
        claudeCodeHarnessDerivedSpectralGraph.cv
          claudeCodeHarnessDerivedFailureSignal := by
    rw [claudeCodeHarnessDerived_cv_value]
    norm_num
  exact eventually_no_stable_equilibrium_of_positive_cv
    claudeCodeHarnessDerivedSpectralGraph
    claudeCodeHarnessDerivedFailureSignal
    claudeCodeHarnessTolerance hδ hcv

/-- The adjudicated threshold repair has zero audit-derived threshold CV on the
derived Claude Code carrier. -/
theorem claudeCodeHarnessDerived_repaired_cv_zero :
    claudeCodeHarnessDerivedSpectralGraph.cv
      (auditGraphThresholdSignal
        (adjudicateThresholdGraph
          claudeCodeHooksExtractedGovernanceGraph)) = 0 := by
  exact
    adjudicateThresholdGraph_cv_zero
      claudeCodeHarnessDerivedSpectralGraph
      claudeCodeHooksExtractedGovernanceGraph

/-!
## Binary-facing headline bridge
-/

/-- Honest scalar summary for the binary evidence bundle: the extracted Claude
Code graph has the recorded finite cardinalities, and the derived Stage 2
spectral carrier has exact C* `1/10`. -/
theorem claudeCodeExtractedGraphCardinalityAndCStar :
    claudeCodeHooksExtractedGovernanceGraph.nodes.length = 31 ∧
      claudeCodeHooksExtractedGovernanceGraph.edges.length = 14 ∧
      C_star claudeCodeHarnessDerivedSpectralGraph
        claudeCodeHarnessDerivedFailureSignal
        claudeCodeHarnessTolerance = 1 / 10 := by
  exact ⟨claudeCodeHarness_extracted_node_count,
    claudeCodeHarness_extracted_edge_count,
    claudeCodeHarnessDerived_C_star_value⟩

/-- Legacy compatibility name for the v1.0.0 binary evidence bundle. The JSON
bundle emits the more explicit graph-cardinality-with-C*-carrier field name.
Deprecated compatibility alias for
`claudeCodeExtractedGraphCardinalityAndCStar`; this is not a correspondence
theorem. -/
theorem claudeCodeHarnessSpectralCorrespondence :
    claudeCodeHooksExtractedGovernanceGraph.nodes.length = 31 ∧
      claudeCodeHooksExtractedGovernanceGraph.edges.length = 14 ∧
      C_star claudeCodeHarnessDerivedSpectralGraph
        claudeCodeHarnessDerivedFailureSignal
        claudeCodeHarnessTolerance = 1 / 10 := by
  exact claudeCodeExtractedGraphCardinalityAndCStar

/-- Binary-facing Claude Code lane facts: the committed extracted public-surface
fixture fails monotonicity, and the threshold carrier derived from that same
extracted topology has exact C* = `1/10`. -/
theorem claudeCodeCliRejectionAndThresholdFacts :
    claudeCodeHooksGovernanceAdmissibilityVerdict =
        AuditVerdict.rejected AuditCheck.monotonicity ∧
      claudeCodeHooksExtractedGovernanceGraph.nodes.length = 31 ∧
      claudeCodeHooksExtractedGovernanceGraph.edges.length = 14 ∧
      C_star claudeCodeHarnessDerivedSpectralGraph
        claudeCodeHarnessDerivedFailureSignal
        claudeCodeHarnessTolerance = 1 / 10 := by
  exact ⟨claudeCodeHooksGovernanceAdmissibilityRejectsMonotonicity,
    claudeCodeExtractedGraphCardinalityAndCStar.1,
    claudeCodeExtractedGraphCardinalityAndCStar.2.1,
    claudeCodeExtractedGraphCardinalityAndCStar.2.2⟩

end Legitimacy
