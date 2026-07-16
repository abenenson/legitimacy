/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.RGFlow.Core

/-!
# Legitimacy.Spectral.CrossScale.RGFlow.N7

Seven-node concrete RG trajectory certificates.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Legitimacy

section Concrete

/-- **Experimental `n = 7` iterated-RG verification.** This computes the
deterministic maximum-weight-merge proxy trajectory for the seven 7-node
archetypes for the seven-graph lattice, using the same greedy partition rule as the
`n = 5` lattice. -/
lemma concrete_iterated_RG_n7 :
    GovGraph.rgTrajectory uniK7 sig7 (1 / 10) 0 = (2 / 3, 3 / 20) ∧
    GovGraph.rgTrajectory uniK7 sig7 (1 / 10) 1 = (5 / 6, 3 / 25) ∧
    GovGraph.rgTrajectory uniK7 sig7 (1 / 10) 2 = (1 / 2, 1 / 5) ∧
    GovGraph.rgTrajectory uniK7 sig7 (1 / 10) 3 = (3, 1 / 30) ∧
    GovGraph.rgTrajectory uniK7 sig7 (1 / 10) 4 = (15 / 2, 1 / 75) ∧
    GovGraph.rgTrajectory uniK7 sig7 (1 / 10) 5 = (21, 1 / 210) ∧
    GovGraph.rgTrajectory asymK7 sig7 (1 / 10) 0 = (8 / 7, 7 / 80) ∧
    GovGraph.rgTrajectory asymK7 sig7 (1 / 10) 1 = (5 / 6, 3 / 25) ∧
    GovGraph.rgTrajectory asymK7 sig7 (1 / 10) 2 = (1 / 2, 1 / 5) ∧
    GovGraph.rgTrajectory asymK7 sig7 (1 / 10) 3 = (3, 1 / 30) ∧
    GovGraph.rgTrajectory asymK7 sig7 (1 / 10) 4 = (15 / 2, 1 / 75) ∧
    GovGraph.rgTrajectory asymK7 sig7 (1 / 10) 5 = (21, 1 / 210) ∧
    GovGraph.rgTrajectory nearPath7 sig7 (1 / 10) 0 = (30 / 11, 11 / 300) ∧
    GovGraph.rgTrajectory nearPath7 sig7 (1 / 10) 1 = (24 / 11, 11 / 240) ∧
    GovGraph.rgTrajectory nearPath7 sig7 (1 / 10) 2 = (104 / 61, 61 / 1040) ∧
    GovGraph.rgTrajectory nearPath7 sig7 (1 / 10) 3 = (30 / 11, 11 / 300) ∧
    GovGraph.rgTrajectory nearPath7 sig7 (1 / 10) 4 = (90 / 11, 11 / 900) ∧
    GovGraph.rgTrajectory nearPath7 sig7 (1 / 10) 5 = (21, 1 / 210) ∧
    GovGraph.rgTrajectory bottleneck7_bi sig7 (1 / 10) 0 =
      (612578750 / 612552501, 612552501 / 6125787500) ∧
    GovGraph.rgTrajectory bottleneck7_bi sig7 (1 / 10) 1 =
      (87500 / 35001, 35001 / 875000) ∧
    GovGraph.rgTrajectory bottleneck7_bi sig7 (1 / 10) 2 =
      (24500420000 / 29401050009, 29401050009 / 245004200000) ∧
    GovGraph.rgTrajectory bottleneck7_bi sig7 (1 / 10) 3 =
      (140000 / 70001, 70001 / 1400000) ∧
    GovGraph.rgTrajectory bottleneck7_bi sig7 (1 / 10) 4 =
      (630000 / 70001, 70001 / 6300000) ∧
    GovGraph.rgTrajectory bottleneck7_bi sig7 (1 / 10) 5 = (22, 1 / 220) ∧
    GovGraph.rgTrajectory bottleneck7_tri sig7 (1 / 10) 0 =
      (56000 / 14001, 14001 / 560000) ∧
    GovGraph.rgTrajectory bottleneck7_tri sig7 (1 / 10) 1 =
      (47600 / 14001, 14001 / 476000) ∧
    GovGraph.rgTrajectory bottleneck7_tri sig7 (1 / 10) 2 =
      (30800 / 14001, 14001 / 308000) ∧
    GovGraph.rgTrajectory bottleneck7_tri sig7 (1 / 10) 3 =
      (5 / 4, 2 / 25) ∧
    GovGraph.rgTrajectory bottleneck7_tri sig7 (1 / 10) 4 =
      (21 / 5, 1 / 42) ∧
    GovGraph.rgTrajectory bottleneck7_tri sig7 (1 / 10) 5 = (15, 1 / 150) ∧
    GovGraph.rgTrajectory hubSpokeHierarchy7 sig7 (1 / 10) 0 =
      (55 / 12, 6 / 275) ∧
    GovGraph.rgTrajectory hubSpokeHierarchy7 sig7 (1 / 10) 1 = (3, 1 / 30) ∧
    GovGraph.rgTrajectory hubSpokeHierarchy7 sig7 (1 / 10) 2 = (6, 1 / 60) ∧
    GovGraph.rgTrajectory hubSpokeHierarchy7 sig7 (1 / 10) 3 = (10, 1 / 100) ∧
    GovGraph.rgTrajectory hubSpokeHierarchy7 sig7 (1 / 10) 4 = (15, 1 / 150) ∧
    GovGraph.rgTrajectory hubSpokeHierarchy7 sig7 (1 / 10) 5 = (21, 1 / 210) ∧
    GovGraph.rgTrajectory nestedHierarchy7 sig7 (1 / 10) 0 = (85 / 84, 42 / 425) ∧
    GovGraph.rgTrajectory nestedHierarchy7 sig7 (1 / 10) 1 = (5 / 4, 2 / 25) ∧
    GovGraph.rgTrajectory nestedHierarchy7 sig7 (1 / 10) 2 = (145 / 168, 84 / 725) ∧
    GovGraph.rgTrajectory nestedHierarchy7 sig7 (1 / 10) 3 = (77 / 24, 12 / 385) ∧
    GovGraph.rgTrajectory nestedHierarchy7 sig7 (1 / 10) 4 = (15, 1 / 150) ∧
    GovGraph.rgTrajectory nestedHierarchy7 sig7 (1 / 10) 5 = (21, 1 / 210) := by
  set_option maxRecDepth 4096 in
    repeat' constructor
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    all_goals native_decide

end Concrete

end Legitimacy
