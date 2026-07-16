/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Core.Basic

/-!
  Concrete weighted governance graphs used throughout the spectral section.

  This module packages the five explicit 3-node graph witnesses, their degree
  computations, the shared signal `sig`, and the concrete CV evaluations used
  by later localizability, capacity, and capability results.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

-- native_decide: finite rational matrix and degree checks over literal
-- concrete graph witnesses.

/-- The uniform triangle: all edge weights = 1.
    Laplacian eigenvalues: 0, 3, 3. Spectral gap = 3. -/
def uniTriGraph : GovGraph ℚ 3 where
  weights := !![0, 1, 1; 1, 0, 1; 1, 1, 0]
  weight_symm := by decide
  weight_nonneg := by decide
  weight_self_zero := by decide

/-- Degree of every node in the uniform triangle is 2. -/
lemma uniTriGraph_deg (i : Fin 3) : uniTriGraph.deg i = 2 := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  fin_cases i <;> native_decide

/-- The asymmetric triangle: w01 = 1, w12 = 2, w02 = 1.
    Laplacian eigenvalues: 0, 3, 5. Spectral gap = 3. -/
def asymTriGraph : GovGraph ℚ 3 where
  weights := !![0, 1, 1; 1, 0, 2; 1, 2, 0]
  weight_symm := by decide
  weight_nonneg := by decide
  weight_self_zero := by decide

/-- Degree of the left node in the asymmetric triangle is 2. -/
lemma asymTriGraph_deg_0 : asymTriGraph.deg 0 = 2 := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  native_decide

/-- Degree of the center node in the asymmetric triangle is 3. -/
lemma asymTriGraph_deg_1 : asymTriGraph.deg 1 = 3 := by
  native_decide

/-- Degree of the right node in the asymmetric triangle is 3. -/
lemma asymTriGraph_deg_2 : asymTriGraph.deg 2 = 3 := by
  native_decide

/-- A near-path triangle with one weak edge of weight 1/50. -/
def nearPathGraph : GovGraph ℚ 3 where
  weights := !![0, 1, 1/50; 1, 0, 1; 1/50, 1, 0]
  weight_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by decide

/-- Node 0 in the near-path graph has degree 51/50. -/
lemma nearPathGraph_deg_0 : nearPathGraph.deg 0 = 51 / 50 := by
  native_decide

/-- Node 1 in the near-path graph has degree 2. -/
lemma nearPathGraph_deg_1 : nearPathGraph.deg 1 = 2 := by
  native_decide

/-- Node 2 in the near-path graph has degree 51/50. -/
lemma nearPathGraph_deg_2 : nearPathGraph.deg 2 = 51 / 50 := by
  native_decide

/-- A strongly connected triangle with all edge weights equal to 10. -/
def stronglyConnectedGraph : GovGraph ℚ 3 where
  weights := !![0, 10, 10; 10, 0, 10; 10, 10, 0]
  weight_symm := by decide
  weight_nonneg := by decide
  weight_self_zero := by decide

/-- Every node in the strongly connected graph has degree 20. -/
lemma stronglyConnectedGraph_deg (i : Fin 3) :
    stronglyConnectedGraph.deg i = 20 := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  fin_cases i <;> native_decide

/-- A near-path triangle with an extreme bottleneck edge of weight 1/10000. -/
def bottleneckGraph : GovGraph ℚ 3 where
  weights := !![0, 1, 1/10000; 1, 0, 1; 1/10000, 1, 0]
  weight_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by decide

/-- Node 0 in the bottleneck graph has degree 10001/10000. -/
lemma bottleneckGraph_deg_0 : bottleneckGraph.deg 0 = 10001 / 10000 := by
  native_decide

/-- Node 1 in the bottleneck graph has degree 2. -/
lemma bottleneckGraph_deg_1 : bottleneckGraph.deg 1 = 2 := by
  native_decide

/-- Node 2 in the bottleneck graph has degree 10001/10000. -/
lemma bottleneckGraph_deg_2 : bottleneckGraph.deg 2 = 10001 / 10000 := by
  native_decide

/-- Standard concrete signal used for the five-graph verification. -/
def sig : Fin 3 → ℚ := ![1, 2, 3]

/-- Half-scale triangle signal used by the concrete noisy-channel calibration. -/
def halfSig : Fin 3 → ℚ := ![1 / 2, 1, 3 / 2]

/-- Half-scale signal for the asymmetric-triangle noisy-channel calibration. -/
def asymTriHalfSig : Fin 3 → ℚ := ![1 / 2, 1, 3 / 2]

/-- Half-scale signal for the near-path noisy-channel calibration. -/
def nearPathHalfSig : Fin 3 → ℚ := ![1 / 2, 1, 3 / 2]

/-- Half-scale signal for the bottleneck noisy-channel calibration. -/
def bottleneckHalfSig : Fin 3 → ℚ := ![1 / 2, 1, 3 / 2]

/-- The signal range of `sig` is exactly 2. -/
lemma sig_signalRange : signalRange sig = 2 := by
  native_decide

/-- The signal range of `halfSig` is exactly 1. -/
lemma halfSig_signalRange : signalRange halfSig = 1 := by
  native_decide

/-- Experimental 5-node lattice witness: the uniform complete graph `K₅`. -/
def uniK5 : GovGraph ℚ 5 where
  weights := !![
    0, 1, 1, 1, 1;
    1, 0, 1, 1, 1;
    1, 1, 0, 1, 1;
    1, 1, 1, 0, 1;
    1, 1, 1, 1, 0
  ]
  weight_symm := by decide
  weight_nonneg := by decide
  weight_self_zero := by decide

/-- Experimental 5-node lattice witness: `K₅` with one heavier edge
`w₀₁ = 2`. -/
def asymK5 : GovGraph ℚ 5 where
  weights := !![
    0, 2, 1, 1, 1;
    2, 0, 1, 1, 1;
    1, 1, 0, 1, 1;
    1, 1, 1, 0, 1;
    1, 1, 1, 1, 0
  ]
  weight_symm := by decide
  weight_nonneg := by decide
  weight_self_zero := by decide

/-- Experimental 5-node lattice witness: a path with weak off-path leakage
of weight `1/50`. -/
def nearPath5 : GovGraph ℚ 5 where
  weights := !![
    0, 1, 1/50, 1/50, 1/50;
    1, 0, 1, 1/50, 1/50;
    1/50, 1, 0, 1, 1/50;
    1/50, 1/50, 1, 0, 1;
    1/50, 1/50, 1/50, 1, 0
  ]
  weight_symm := by
    intro i j
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by decide

/-- Experimental 5-node lattice witness: two strong flanks joined only
through an extremely weak bridge at node `2`. -/
def bottleneck5 : GovGraph ℚ 5 where
  weights := !![
    0, 1, 1/10000, 0, 0;
    1, 0, 1/10000, 0, 0;
    1/10000, 1/10000, 0, 1/10000, 1/10000;
    0, 0, 1/10000, 0, 1;
    0, 0, 1/10000, 1, 0
  ]
  weight_symm := by
    intro i j
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by decide

/-- Experimental 5-node lattice witness: a wheel with hub `0`, unit spokes,
and rim edges of weight `1/10`. -/
def wheel5 : GovGraph ℚ 5 where
  weights := !![
    0, 1, 1, 1, 1;
    1, 0, 1/10, 0, 1/10;
    1, 1/10, 0, 1/10, 0;
    1, 0, 1/10, 0, 1/10;
    1, 1/10, 0, 1/10, 0
  ]
  weight_symm := by
    intro i j
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by decide

/-- Standard 5-node concrete signal used for the iterated RG experiment. -/
def sig5 : Fin 5 → ℚ := ![1, 2, 3, 4, 5]

/-- Half-scale `K₅` signal used by the concrete noisy-channel calibration. -/
def uniK5HalfSig : Fin 5 → ℚ := ![1 / 2, 1, 3 / 2, 2, 5 / 2]

/-- The signal range of `sig5` is exactly 4. -/
lemma sig5_signalRange : signalRange sig5 = 4 := by
  native_decide

/-- Experimental 7-node lattice witness: the uniform complete graph `K₇`. -/
def uniK7 : GovGraph ℚ 7 where
  weights := !![
    0, 1, 1, 1, 1, 1, 1;
    1, 0, 1, 1, 1, 1, 1;
    1, 1, 0, 1, 1, 1, 1;
    1, 1, 1, 0, 1, 1, 1;
    1, 1, 1, 1, 0, 1, 1;
    1, 1, 1, 1, 1, 0, 1;
    1, 1, 1, 1, 1, 1, 0
  ]
  weight_symm := by decide
  weight_nonneg := by decide
  weight_self_zero := by decide

/-- Experimental 7-node lattice witness: `K₇` with one heavier edge
`w₀₁ = 2`. -/
def asymK7 : GovGraph ℚ 7 where
  weights := !![
    0, 2, 1, 1, 1, 1, 1;
    2, 0, 1, 1, 1, 1, 1;
    1, 1, 0, 1, 1, 1, 1;
    1, 1, 1, 0, 1, 1, 1;
    1, 1, 1, 1, 0, 1, 1;
    1, 1, 1, 1, 1, 0, 1;
    1, 1, 1, 1, 1, 1, 0
  ]
  weight_symm := by decide
  weight_nonneg := by decide
  weight_self_zero := by decide

/-- Experimental 7-node lattice witness: a path with weak long-range leakage
of weight `1/50`. -/
def nearPath7 : GovGraph ℚ 7 where
  weights := !![
    0, 1, 1/50, 1/50, 1/50, 1/50, 1/50;
    1, 0, 1, 1/50, 1/50, 1/50, 1/50;
    1/50, 1, 0, 1, 1/50, 1/50, 1/50;
    1/50, 1/50, 1, 0, 1, 1/50, 1/50;
    1/50, 1/50, 1/50, 1, 0, 1, 1/50;
    1/50, 1/50, 1/50, 1/50, 1, 0, 1;
    1/50, 1/50, 1/50, 1/50, 1/50, 1, 0
  ]
  weight_symm := by
    intro i j
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by decide

/-- Experimental 7-node lattice witness: two disjoint dense communities
`{0,1,2}` and `{3,4,5,6}` connected only by weak cross-community leakage of
weight `1/70000`. -/
def bottleneck7_bi : GovGraph ℚ 7 where
  weights := !![
    0, 1, 1, 1/70000, 1/70000, 1/70000, 1/70000;
    1, 0, 1, 1/70000, 1/70000, 1/70000, 1/70000;
    1, 1, 0, 1/70000, 1/70000, 1/70000, 1/70000;
    1/70000, 1/70000, 1/70000, 0, 1, 1, 1;
    1/70000, 1/70000, 1/70000, 1, 0, 1, 1;
    1/70000, 1/70000, 1/70000, 1, 1, 0, 1;
    1/70000, 1/70000, 1/70000, 1, 1, 1, 0
  ]
  weight_symm := by
    intro i j
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by decide

/-- Experimental 7-node lattice witness: three nonoverlapping dense clusters
`{0,1,2}`, `{3,4}`, and `{5,6}` connected only by weak inter-cluster leakage
of weight `1/70000`. -/
def bottleneck7_tri : GovGraph ℚ 7 where
  weights := !![
    0, 1, 1, 1/70000, 1/70000, 1/70000, 1/70000;
    1, 0, 1, 1/70000, 1/70000, 1/70000, 1/70000;
    1, 1, 0, 1/70000, 1/70000, 1/70000, 1/70000;
    1/70000, 1/70000, 1/70000, 0, 1, 1/70000, 1/70000;
    1/70000, 1/70000, 1/70000, 1, 0, 1/70000, 1/70000;
    1/70000, 1/70000, 1/70000, 1/70000, 1/70000, 0, 1;
    1/70000, 1/70000, 1/70000, 1/70000, 1/70000, 1, 0
  ]
  weight_symm := by
    intro i j
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by decide

/-- Experimental 7-node lattice witness: a hub-and-spoke hierarchy with hub
`0`, spoke leaves `{1,2,3,4}`, and a secondary weak branch `{5,6}` attached
through spoke `1`. -/
def hubSpokeHierarchy7 : GovGraph ℚ 7 where
  weights := !![
    0, 1, 1, 1, 1, 0, 0;
    1, 0, 0, 0, 0, 1/10, 1/10;
    1, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0;
    0, 1/10, 0, 0, 0, 0, 0;
    0, 1/10, 0, 0, 0, 0, 0
  ]
  weight_symm := by
    intro i j
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by decide

/-- Experimental 7-node lattice witness: a nested three-level hierarchy with
inner triangle `{0,1,2}`, middle pair `{3,4}`, and outer leaves `{5,6}`. -/
def nestedHierarchy7 : GovGraph ℚ 7 where
  weights := !![
    0, 1, 1, 1/5, 1/5, 0, 0;
    1, 0, 1, 1/5, 1/5, 0, 0;
    1, 1, 0, 1/5, 1/5, 0, 0;
    1/5, 1/5, 1/5, 0, 1/2, 1/20, 1/20;
    1/5, 1/5, 1/5, 1/2, 0, 1/20, 1/20;
    0, 0, 0, 1/20, 1/20, 0, 0;
    0, 0, 0, 1/20, 1/20, 0, 0
  ]
  weight_symm := by
    intro i j
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    fin_cases i <;> fin_cases j <;> native_decide
  weight_nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> native_decide
  weight_self_zero := by decide

/-- Standard 7-node concrete signal used for the iterated RG experiment. -/
def sig7 : Fin 7 → ℚ := ![1, 2, 3, 4, 5, 6, 7]

/-- The signal range of `sig7` is exactly 6. -/
lemma sig7_signalRange : signalRange sig7 = 6 := by
  native_decide

end Legitimacy
