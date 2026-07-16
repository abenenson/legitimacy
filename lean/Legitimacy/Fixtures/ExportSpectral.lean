/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.CrossScale.RGFlow
import Legitimacy.Spectral.Dynamics.Stackelberg
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality

/-!
# Legitimacy.Fixtures.ExportSpectral

Emit the canonical concrete spectral expectations consumed by the Rust test
suite. The output format is TOML so it can be checked into the repository and
diffed cleanly.
-/

set_option autoImplicit false

namespace Legitimacy

private def quote (s : String) : String :=
  "\"" ++ s ++ "\""

private def ratString (q : ℚ) : String :=
  s!"{q.num}/{q.den}"

private def ratToml (q : ℚ) : String :=
  quote (ratString q)

private def kv (key value : String) : String :=
  s!"{key} = {value}"

private def boolToml (value : Bool) : String :=
  if value then "true" else "false"

private def ratListToml (values : List ℚ) : String :=
  "[" ++ String.intercalate ", " (values.map ratToml) ++ "]"

private def pairToml (value : ℚ × ℚ) : String :=
  "[" ++ String.intercalate ", " [ratToml value.1, ratToml value.2] ++ "]"

private def pairListToml (values : List (ℚ × ℚ)) : String :=
  "[" ++ String.intercalate ", " (values.map pairToml) ++ "]"

private def wellConnectedToml (sDelta : ℚ) : String :=
  boolToml (decide (ProbeSpectralWellConnected sDelta))

private def emitSection (name : String) (lines : List String) : String :=
  "[" ++ name ++ "]\n" ++ String.intercalate "\n" lines ++ "\n"

private def rgSeries
    {n : ℕ}
    (f : GovGraph ℚ (n + 1) → (Fin (n + 1) → ℚ) → ℚ → ℕ → ℚ × ℚ)
    (G : GovGraph ℚ (n + 1))
    (s : Fin (n + 1) → ℚ)
    (steps : ℕ) : List (ℚ × ℚ) :=
  (List.range steps).map fun k => f G s (1 / 10) k

private def coarseSignal01 : Fin 2 → ℚ :=
  GovGraph.coarseSignal sig 0 1 (by decide)

private def coarseGraph01 : GovGraph ℚ 2 :=
  GovGraph.coarseGrain uniTriGraph 0 1 (by decide)

private def threeNodeUniformSDeltaCertificate : ℚ := 3

private def threeNodeAsymmetricSDeltaCertificate : ℚ := 4

private def threeNodeNearPathSDeltaCertificate : ℚ := 26 / 25

private def threeNodeStronglyConnectedSDeltaCertificate : ℚ := 30

private def threeNodeBottleneckSDeltaCertificate : ℚ := 5001 / 5000

def payload : String :=
  let header :=
    [ kv "delta" (ratToml (1 / 10 : ℚ))
    , ""
    ]
  let capacity :=
    emitSection "capacity_bounds"
      [ kv "uni_tri" (ratToml (uniTriGraph.capacityBound sig))
      , kv "asym_tri" (ratToml (asymTriGraph.capacityBound sig))
      , kv "near_path" (ratToml (nearPathGraph.capacityBound sig))
      , kv "strongly_connected" (ratToml (stronglyConnectedGraph.capacityBound sig))
      , kv "bottleneck" (ratToml (bottleneckGraph.capacityBound sig))
      ]
  let cvValues :=
    emitSection "cv_values"
      [ kv "uni_tri" (ratToml (uniTriGraph.cv sig))
      , kv "asym_tri" (ratToml (asymTriGraph.cv sig))
      , kv "near_path" (ratToml (nearPathGraph.cv sig))
      , kv "strongly_connected" (ratToml (stronglyConnectedGraph.cv sig))
      , kv "bottleneck" (ratToml (bottleneckGraph.cv sig))
      ]
  let critical :=
    emitSection "critical_capability"
      [ kv "uni_tri" (ratToml (C_star uniTriGraph sig (1 / 10)))
      , kv "asym_tri" (ratToml (C_star asymTriGraph sig (1 / 10)))
      , kv "near_path" (ratToml (C_star nearPathGraph sig (1 / 10)))
      , kv "strongly_connected" (ratToml (C_star stronglyConnectedGraph sig (1 / 10)))
      , kv "bottleneck" (ratToml (C_star bottleneckGraph sig (1 / 10)))
      ]
  let stackelberg :=
    emitSection "stackelberg"
      [ kv "value" (ratToml (stackelbergValue (1 / 10))) ]
  let coarse :=
    emitSection "coarse_grain"
      [ kv "signal" (ratListToml [coarseSignal01 0, coarseSignal01 1])
      , kv "cv" (ratToml (coarseGraph01.cv coarseSignal01))
      , kv "c_star" (ratToml (C_star coarseGraph01 coarseSignal01 (1 / 10)))
      ]
  let spectralWellConnectedN3 :=
    emitSection "spectral_well_connected_n3"
      [ kv "uni_tri" (wellConnectedToml threeNodeUniformSDeltaCertificate)
      , kv "asym_tri" (wellConnectedToml threeNodeAsymmetricSDeltaCertificate)
      , kv "near_path" (wellConnectedToml threeNodeNearPathSDeltaCertificate)
      , kv "strongly_connected"
          (wellConnectedToml threeNodeStronglyConnectedSDeltaCertificate)
      , kv "bottleneck" (wellConnectedToml threeNodeBottleneckSDeltaCertificate)
      ]
  let spectralWellConnectedN5 :=
    emitSection "spectral_well_connected_n5"
      [ kv "uni_k5" (wellConnectedToml fiveNodeCompleteSDeltaCertificate)
      , kv "asym_k5" (wellConnectedToml fiveNodeAsymmetricSDeltaCertificate)
      , kv "near_path5" (wellConnectedToml fiveNodeNearPathSDeltaCertificate)
      , kv "bottleneck5" (wellConnectedToml fiveNodeBottleneckSDeltaCertificate)
      , kv "wheel5" (wellConnectedToml fiveNodeWheelSDeltaCertificate)
      ]
  let rgN5 :=
    emitSection "rg_n5"
      [ kv "uni_k5" (pairListToml (rgSeries GovGraph.rgTrajectory uniK5 sig5 4))
      , kv "asym_k5" (pairListToml (rgSeries GovGraph.rgTrajectory asymK5 sig5 4))
      , kv "near_path5" (pairListToml (rgSeries GovGraph.rgTrajectory nearPath5 sig5 4))
      , kv "bottleneck5" (pairListToml (rgSeries GovGraph.rgTrajectory bottleneck5 sig5 4))
      , kv "wheel5" (pairListToml (rgSeries GovGraph.rgTrajectory wheel5 sig5 4))
      ]
  let rgN7 :=
    emitSection "rg_n7"
      [ kv "uni_k7" (pairListToml (rgSeries GovGraph.rgTrajectory uniK7 sig7 6))
      , kv "asym_k7" (pairListToml (rgSeries GovGraph.rgTrajectory asymK7 sig7 6))
      , kv "near_path7" (pairListToml (rgSeries GovGraph.rgTrajectory nearPath7 sig7 6))
      , "# bottleneck7_* values reflect the weak-bridge definitions in ConcreteGraphs."
      , kv "bottleneck7_bi"
          (pairListToml (rgSeries GovGraph.rgTrajectory bottleneck7_bi sig7 6))
      , kv "bottleneck7_tri"
          (pairListToml (rgSeries GovGraph.rgTrajectory bottleneck7_tri sig7 6))
      , kv "hub_spoke_hierarchy7"
          (pairListToml (rgSeries GovGraph.rgTrajectory hubSpokeHierarchy7 sig7 6))
      , kv "nested_hierarchy7"
          (pairListToml (rgSeries GovGraph.rgTrajectory nestedHierarchy7 sig7 6))
      ]
  let rgCheeger :=
    emitSection "rg_cheeger_n5"
      [ kv "uni_k5" (pairListToml (rgSeries GovGraph.rgTrajectoryCheeger uniK5 sig5 5))
      , kv "asym_k5" (pairListToml (rgSeries GovGraph.rgTrajectoryCheeger asymK5 sig5 5))
      , kv "near_path5"
          (pairListToml (rgSeries GovGraph.rgTrajectoryCheeger nearPath5 sig5 5))
      , kv "bottleneck5"
          (pairListToml (rgSeries GovGraph.rgTrajectoryCheeger bottleneck5 sig5 5))
      , kv "wheel5" (pairListToml (rgSeries GovGraph.rgTrajectoryCheeger wheel5 sig5 5))
      ]
  let rgModularity :=
    emitSection "rg_modularity_n5"
      [ kv "uni_k5"
          (pairListToml (rgSeries GovGraph.rgTrajectoryModularity uniK5 sig5 5))
      , kv "asym_k5"
          (pairListToml (rgSeries GovGraph.rgTrajectoryModularity asymK5 sig5 5))
      , kv "near_path5"
          (pairListToml (rgSeries GovGraph.rgTrajectoryModularity nearPath5 sig5 5))
      , kv "bottleneck5"
          (pairListToml (rgSeries GovGraph.rgTrajectoryModularity bottleneck5 sig5 5))
      , kv "wheel5"
          (pairListToml (rgSeries GovGraph.rgTrajectoryModularity wheel5 sig5 5))
      ]
  let rgSignalPreserving :=
    emitSection "rg_signal_preserving_n5"
      [ kv "uni_k5"
          (pairListToml (rgSeries GovGraph.rgTrajectorySignalPreserving uniK5 sig5 5))
      , kv "asym_k5"
          (pairListToml (rgSeries GovGraph.rgTrajectorySignalPreserving asymK5 sig5 5))
      , kv "near_path5"
          (pairListToml (rgSeries GovGraph.rgTrajectorySignalPreserving nearPath5 sig5 5))
      , kv "bottleneck5"
          (pairListToml (rgSeries GovGraph.rgTrajectorySignalPreserving bottleneck5 sig5 5))
      , kv "wheel5"
          (pairListToml (rgSeries GovGraph.rgTrajectorySignalPreserving wheel5 sig5 5))
      ]
  String.intercalate "\n"
    (header ++ [capacity, cvValues, critical, stackelberg, coarse,
      spectralWellConnectedN3, spectralWellConnectedN5, rgN5, rgN7, rgCheeger,
      rgModularity, rgSignalPreserving])

end Legitimacy

def main : IO Unit := IO.print Legitimacy.payload
