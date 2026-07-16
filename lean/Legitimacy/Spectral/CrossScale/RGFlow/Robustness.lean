/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.RGFlow.Core

/-!
# Legitimacy.Spectral.CrossScale.RGFlow.Robustness

Five-node robustness tables for alternate RG partition families.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Legitimacy

section Concrete

/-- **`n = 5` robustness table, Family A.** The true minimum-conductance
partition family preserves the bottleneck split at depth `k = 3`. -/
lemma robustness_cheeger_n5 :
    GovGraph.rgTrajectoryCheeger uniK5 sig5 (1 / 10) 0 = (3 / 4, 2 / 15) ∧
    GovGraph.rgTrajectoryCheeger uniK5 sig5 (1 / 10) 1 = (3 / 4, 2 / 15) ∧
    GovGraph.rgTrajectoryCheeger uniK5 sig5 (1 / 10) 2 = (3 / 2, 1 / 15) ∧
    GovGraph.rgTrajectoryCheeger uniK5 sig5 (1 / 10) 3 = (3 / 2, 1 / 15) ∧
    GovGraph.rgTrajectoryCheeger uniK5 sig5 (1 / 10) 4 = (3 / 2, 1 / 15) ∧
    GovGraph.rgTrajectoryCheeger asymK5 sig5 (1 / 10) 0 = (6 / 5, 1 / 12) ∧
    GovGraph.rgTrajectoryCheeger asymK5 sig5 (1 / 10) 1 = (3 / 4, 2 / 15) ∧
    GovGraph.rgTrajectoryCheeger asymK5 sig5 (1 / 10) 2 = (3 / 2, 1 / 15) ∧
    GovGraph.rgTrajectoryCheeger asymK5 sig5 (1 / 10) 3 = (3 / 2, 1 / 15) ∧
    GovGraph.rgTrajectoryCheeger asymK5 sig5 (1 / 10) 4 = (3 / 2, 1 / 15) ∧
    GovGraph.rgTrajectoryCheeger nearPath5 sig5 (1 / 10) 0 = (100 / 53, 53 / 1000) ∧
    GovGraph.rgTrajectoryCheeger nearPath5 sig5 (1 / 10) 1 = (153 / 110, 11 / 153) ∧
    GovGraph.rgTrajectoryCheeger nearPath5 sig5 (1 / 10) 2 = (100 / 53, 53 / 1000) ∧
    GovGraph.rgTrajectoryCheeger nearPath5 sig5 (1 / 10) 3 = (100 / 53, 53 / 1000) ∧
    GovGraph.rgTrajectoryCheeger nearPath5 sig5 (1 / 10) 4 = (100 / 53, 53 / 1000) ∧
    GovGraph.rgTrajectoryCheeger bottleneck5 sig5 (1 / 10) 0 = (20000 / 10001, 10001 / 200000) ∧
    GovGraph.rgTrajectoryCheeger bottleneck5 sig5 (1 / 10) 1 = (3, 1 / 30) ∧
    GovGraph.rgTrajectoryCheeger bottleneck5 sig5 (1 / 10) 2 = (20000 / 10001, 10001 / 200000) ∧
    GovGraph.rgTrajectoryCheeger bottleneck5 sig5 (1 / 10) 3 = (20000 / 10001, 10001 / 200000) ∧
    GovGraph.rgTrajectoryCheeger bottleneck5 sig5 (1 / 10) 4 = (20000 / 10001, 10001 / 200000) ∧
    GovGraph.rgTrajectoryCheeger wheel5 sig5 (1 / 10) 0 = (5 / 2, 1 / 25) ∧
    GovGraph.rgTrajectoryCheeger wheel5 sig5 (1 / 10) 1 = (11 / 12, 6 / 55) ∧
    GovGraph.rgTrajectoryCheeger wheel5 sig5 (1 / 10) 2 = (11 / 6, 3 / 55) ∧
    GovGraph.rgTrajectoryCheeger wheel5 sig5 (1 / 10) 3 = (11 / 6, 3 / 55) ∧
    GovGraph.rgTrajectoryCheeger wheel5 sig5 (1 / 10) 4 = (11 / 6, 3 / 55) := by
  set_option maxRecDepth 2048 in
    repeat' constructor
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    all_goals native_decide

/-- **`n = 5` robustness table, Family B.** The modularity-maximizing partition
family also preserves the bottleneck split at depth `k = 3`. -/
lemma robustness_modularity_n5 :
    GovGraph.rgTrajectoryModularity uniK5 sig5 (1 / 10) 0 = (3 / 4, 2 / 15) ∧
    GovGraph.rgTrajectoryModularity uniK5 sig5 (1 / 10) 1 = (3 / 4, 2 / 15) ∧
    GovGraph.rgTrajectoryModularity uniK5 sig5 (1 / 10) 2 = (3 / 4, 2 / 15) ∧
    GovGraph.rgTrajectoryModularity uniK5 sig5 (1 / 10) 3 = (3 / 4, 2 / 15) ∧
    GovGraph.rgTrajectoryModularity uniK5 sig5 (1 / 10) 4 = (3 / 4, 2 / 15) ∧
    GovGraph.rgTrajectoryModularity asymK5 sig5 (1 / 10) 0 = (6 / 5, 1 / 12) ∧
    GovGraph.rgTrajectoryModularity asymK5 sig5 (1 / 10) 1 = (6 / 5, 1 / 12) ∧
    GovGraph.rgTrajectoryModularity asymK5 sig5 (1 / 10) 2 = (6 / 5, 1 / 12) ∧
    GovGraph.rgTrajectoryModularity asymK5 sig5 (1 / 10) 3 = (6 / 5, 1 / 12) ∧
    GovGraph.rgTrajectoryModularity asymK5 sig5 (1 / 10) 4 = (6 / 5, 1 / 12) ∧
    GovGraph.rgTrajectoryModularity nearPath5 sig5 (1 / 10) 0 = (100 / 53, 53 / 1000) ∧
    GovGraph.rgTrajectoryModularity nearPath5 sig5 (1 / 10) 1 = (153 / 110, 11 / 153) ∧
    GovGraph.rgTrajectoryModularity nearPath5 sig5 (1 / 10) 2 = (100 / 53, 53 / 1000) ∧
    GovGraph.rgTrajectoryModularity nearPath5 sig5 (1 / 10) 3 = (100 / 53, 53 / 1000) ∧
    GovGraph.rgTrajectoryModularity nearPath5 sig5 (1 / 10) 4 = (100 / 53, 53 / 1000) ∧
    GovGraph.rgTrajectoryModularity bottleneck5 sig5 (1 / 10) 0 = (20000 / 10001, 10001 / 200000) ∧
    GovGraph.rgTrajectoryModularity bottleneck5 sig5 (1 / 10) 1 = (3, 1 / 30) ∧
    GovGraph.rgTrajectoryModularity bottleneck5 sig5 (1 / 10) 2 = (20000 / 10001, 10001 / 200000) ∧
    GovGraph.rgTrajectoryModularity bottleneck5 sig5 (1 / 10) 3 = (20000 / 10001, 10001 / 200000) ∧
    GovGraph.rgTrajectoryModularity bottleneck5 sig5 (1 / 10) 4 = (20000 / 10001, 10001 / 200000) ∧
    GovGraph.rgTrajectoryModularity wheel5 sig5 (1 / 10) 0 = (5 / 2, 1 / 25) ∧
    GovGraph.rgTrajectoryModularity wheel5 sig5 (1 / 10) 1 = (5 / 2, 1 / 25) ∧
    GovGraph.rgTrajectoryModularity wheel5 sig5 (1 / 10) 2 = (5 / 2, 1 / 25) ∧
    GovGraph.rgTrajectoryModularity wheel5 sig5 (1 / 10) 3 = (5 / 2, 1 / 25) ∧
    GovGraph.rgTrajectoryModularity wheel5 sig5 (1 / 10) 4 = (5 / 2, 1 / 25) := by
  set_option maxRecDepth 2048 in
    repeat' constructor
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    all_goals native_decide

/-- **`n = 5` robustness table, Family C.** The signal-preserving partition
family collapses every archetype to the same terminal value by depth `k = 3`. -/
lemma robustness_signal_preserving_n5 :
    GovGraph.rgTrajectorySignalPreserving uniK5 sig5 (1 / 10) 0 = (3 / 4, 2 / 15) ∧
    GovGraph.rgTrajectorySignalPreserving uniK5 sig5 (1 / 10) 1 = (2, 1 / 20) ∧
    GovGraph.rgTrajectorySignalPreserving uniK5 sig5 (1 / 10) 2 = (8, 1 / 80) ∧
    GovGraph.rgTrajectorySignalPreserving uniK5 sig5 (1 / 10) 3 = (0, 0) ∧
    GovGraph.rgTrajectorySignalPreserving uniK5 sig5 (1 / 10) 4 = (0, 0) ∧
    GovGraph.rgTrajectorySignalPreserving asymK5 sig5 (1 / 10) 0 = (6 / 5, 1 / 12) ∧
    GovGraph.rgTrajectorySignalPreserving asymK5 sig5 (1 / 10) 1 = (2, 1 / 20) ∧
    GovGraph.rgTrajectorySignalPreserving asymK5 sig5 (1 / 10) 2 = (8, 1 / 80) ∧
    GovGraph.rgTrajectorySignalPreserving asymK5 sig5 (1 / 10) 3 = (0, 0) ∧
    GovGraph.rgTrajectorySignalPreserving asymK5 sig5 (1 / 10) 4 = (0, 0) ∧
    GovGraph.rgTrajectorySignalPreserving nearPath5 sig5 (1 / 10) 0 = (100 / 53, 53 / 1000) ∧
    GovGraph.rgTrajectorySignalPreserving nearPath5 sig5 (1 / 10) 1 = (204 / 53, 53 / 2040) ∧
    GovGraph.rgTrajectorySignalPreserving nearPath5 sig5 (1 / 10) 2 = (8, 1 / 80) ∧
    GovGraph.rgTrajectorySignalPreserving nearPath5 sig5 (1 / 10) 3 = (0, 0) ∧
    GovGraph.rgTrajectorySignalPreserving nearPath5 sig5 (1 / 10) 4 = (0, 0) ∧
    GovGraph.rgTrajectorySignalPreserving bottleneck5 sig5 (1 / 10) 0 =
      (20000 / 10001, 10001 / 200000) ∧
    GovGraph.rgTrajectorySignalPreserving bottleneck5 sig5 (1 / 10) 1 = (7, 1 / 70) ∧
    GovGraph.rgTrajectorySignalPreserving bottleneck5 sig5 (1 / 10) 2 = (8, 1 / 80) ∧
    GovGraph.rgTrajectorySignalPreserving bottleneck5 sig5 (1 / 10) 3 = (0, 0) ∧
    GovGraph.rgTrajectorySignalPreserving bottleneck5 sig5 (1 / 10) 4 = (0, 0) ∧
    GovGraph.rgTrajectorySignalPreserving wheel5 sig5 (1 / 10) 0 = (5 / 2, 1 / 25) ∧
    GovGraph.rgTrajectorySignalPreserving wheel5 sig5 (1 / 10) 1 = (11 / 3, 3 / 110) ∧
    GovGraph.rgTrajectorySignalPreserving wheel5 sig5 (1 / 10) 2 = (8, 1 / 80) ∧
    GovGraph.rgTrajectorySignalPreserving wheel5 sig5 (1 / 10) 3 = (0, 0) ∧
    GovGraph.rgTrajectorySignalPreserving wheel5 sig5 (1 / 10) 4 = (0, 0) := by
  set_option maxRecDepth 2048 in
    repeat' constructor
    -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
    all_goals native_decide

end Concrete

end Legitimacy
