/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Kernelization

/-!
# ASI parity fixture exporter

This executable emits the pinned JSON fixture consumed by
`tests/asi_parity.rs`. The field names are the Rust serde mirror of the Lean
worked example `safetySpecReductionExampleArtifact`.
-/

namespace Legitimacy

namespace Fixtures

def safetySpecReductionExampleArtifactJson : String :=
  "{\n" ++
  "  \"extract\": \"exampleGovernanceKernelExtractor\",\n" ++
  "  \"src\": {\n" ++
  "    \"sourceId\": \"audits/fixtures/sources/leaderboard/autogen\",\n" ++
  "    \"byteSize\": 23978,\n" ++
  "    \"sizeBound\": 23978,\n" ++
  "    \"coverageComplete\": true,\n" ++
  "    \"parserErrors\": 0\n" ++
  "  },\n" ++
  "  \"reachedData\": \"exampleGovernanceKernelData\",\n" ++
  "  \"trajectory\": \"KernelGovernedTrajectory.refl exampleGovernanceKernelData\",\n" ++
  "  \"compiled\": \"reductionExampleCompiledGovernance\",\n" ++
  "  \"report\": \"reductionExampleRiskReport\",\n" ++
  "  \"monitoring\": \"reductionExampleMonitoring\",\n" ++
  "  \"runtimeKernel\": true,\n" ++
  "  \"semanticBridge\": true,\n" ++
  "  \"semanticKernel\": true,\n" ++
  "  \"reachableStateSafe\": true,\n" ++
  "  \"forcedSacrificesDeclared\": true\n" ++
  "}"

end Fixtures

end Legitimacy

def main : IO Unit := do
  IO.println Legitimacy.Fixtures.safetySpecReductionExampleArtifactJson
