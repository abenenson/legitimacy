/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

/-!
# Legitimacy.Extract.CanonicalInputs

Shared canonical extractor-parity input records.

This module is intentionally data-only. Lean consumes the records directly, and
Rust fixture tests parse the restricted record syntax from this same file.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Bounded source package presented to an extractor model. The fields mirror
the stable facts the Rust boundary can report without importing Rust semantics
into Lean: source identity, bounded byte size, complete coverage, and parser
failure count. -/
structure ExtractorInput where
  /-- Stable identifier for the source package or fixture. -/
  sourceId : String
  /-- Number of source bytes considered by the extractor. -/
  byteSize : Nat
  /-- Declared maximum source size for the bounded extraction claim. -/
  sizeBound : Nat
  /-- Whether the extractor reported complete coverage for discovered files. -/
  coverageComplete : Bool
  /-- Number of parser failures reported at the extractor boundary. -/
  parserErrors : Nat
  deriving Repr, DecidableEq

namespace ExtractorInput

/-- Well-formed bounded inputs are exactly the inputs for which the extractor
boundary is allowed to make a soundness claim. Partial parses and over-bound
sources remain empirical tooling outputs, not formal kernel witnesses. -/
def WellFormed (src : ExtractorInput) : Prop :=
  src.byteSize ≤ src.sizeBound ∧
    src.coverageComplete = true ∧
    src.parserErrors = 0

end ExtractorInput

/-- One canonical extractor parity record shared by Lean and Rust tests. -/
structure CanonicalExtractorParityRecord where
  /-- Stable short fixture name for diagnostics. -/
  name : String
  /-- Repository-relative source fixture path. -/
  source : String
  /-- Whether the Rust extractor must opt into partial parse tolerance. -/
  allowPartial : Bool
  /-- Repository-relative canonical extracted graph snapshot path. -/
  canonicalGraph : String
  /-- Expected deterministic source-tree byte count. -/
  sourceByteSize : Nat
  /-- Expected deterministic source-tree hash. -/
  sourceTreeHash : String
  deriving Repr, DecidableEq

namespace CanonicalExtractorParityRecord

/-- Convert a shared fixture record into the bounded extractor input consumed by
the Lean soundness and parity certificate surfaces. -/
def input (record : CanonicalExtractorParityRecord) : ExtractorInput where
  sourceId := record.source
  byteSize := record.sourceByteSize
  sizeBound := record.sourceByteSize
  coverageComplete := true
  parserErrors := 0

end CanonicalExtractorParityRecord

/-- Canonical input descriptor for the AutoGen leaderboard graph fixture. -/
def autogenExtractorInput : ExtractorInput where
  sourceId := "audits/fixtures/sources/leaderboard/autogen"
  byteSize := 23978
  sizeBound := 23978
  coverageComplete := true
  parserErrors := 0

/-- Canonical input descriptor for the Codex hooks leaderboard graph fixture. -/
def codexHooksExtractorInput : ExtractorInput where
  sourceId := "audits/fixtures/sources/leaderboard/codex-hooks"
  byteSize := 89739
  sizeBound := 89739
  coverageComplete := true
  parserErrors := 0

/-- Canonical input descriptor for the CrewAI hooks leaderboard graph fixture. -/
def crewaiExtractorInput : ExtractorInput where
  sourceId := "audits/fixtures/sources/leaderboard/crewai"
  byteSize := 28085
  sizeBound := 28085
  coverageComplete := true
  parserErrors := 0

/-- Canonical input descriptor for the OpenClaw infrastructure leaderboard graph
fixture. -/
def openclawInfraExtractorInput : ExtractorInput where
  sourceId := "audits/fixtures/sources/leaderboard/openclaw-infra"
  byteSize := 276060
  sizeBound := 276060
  coverageComplete := true
  parserErrors := 0

/-- Canonical input descriptor for the Claude Agent SDK hooks leaderboard graph
fixture. -/
def claudeAgentSDKHooksExtractorInput : ExtractorInput where
  sourceId := "audits/fixtures/sources/leaderboard/claude-agent-sdk-hooks"
  byteSize := 123885
  sizeBound := 123885
  coverageComplete := true
  parserErrors := 0

/-- Shared canonical extractor parity records. This restricted record syntax is
also parsed by Rust fixture tests. -/
def canonicalExtractorParityRecords : List CanonicalExtractorParityRecord :=
  [ { name := "autogen"
      source := "audits/fixtures/sources/leaderboard/autogen"
      allowPartial := false
      canonicalGraph := "audits/leaderboard/autogen-graph.json"
      sourceByteSize := 23978
      sourceTreeHash :=
        "sha256:1e70af30480b142a397360250b7c370cb0e4f447ba238a371d79e3a7374a0d45" }
  , { name := "codex"
      source := "audits/fixtures/sources/leaderboard/codex-hooks"
      allowPartial := false
      canonicalGraph := "audits/leaderboard/codex-graph.json" -- archived heuristic fixture: 10 nodes / 5 edges
      sourceByteSize := 89739
      sourceTreeHash :=
        "sha256:120fe31d3e12be227b379b6a12e199d9dbca5fcdb4bcfcd70c79896a372f4741" }
  , { name := "claude-agent-sdk"
      source := "audits/fixtures/sources/leaderboard/claude-agent-sdk-hooks"
      allowPartial := false
      canonicalGraph := "audits/leaderboard/claude-agent-sdk-graph.json" -- archived heuristic fixture: 15 nodes / 0 edges
      sourceByteSize := 123885
      sourceTreeHash :=
        "sha256:5b3e32a718c1d2655cda0c495317e51a9ae913e50299ea40320b56930e892ec0" }
  , { name := "crewai"
      source := "audits/fixtures/sources/leaderboard/crewai"
      allowPartial := true
      canonicalGraph := "audits/leaderboard/crewai-graph.json"
      sourceByteSize := 28085
      sourceTreeHash :=
        "sha256:7a5f4c405fed72613344841554dd71723708e79284a6bb11b9a2d1b4146cbd64" }
  , { name := "openclaw"
      source := "audits/fixtures/sources/leaderboard/openclaw-infra"
      allowPartial := false
      canonicalGraph := "audits/leaderboard/openclaw-graph.json"
      sourceByteSize := 276060
      sourceTreeHash :=
        "sha256:c76fe02ed7513e4bdb793146c60fde21d461836ec4e6e8af7b5fcff0783553b9" }
  ]

/-- The canonical finite input set shared by Lean and Rust extractor parity. -/
def canonicalExtractorParityInputs : List ExtractorInput :=
  canonicalExtractorParityRecords.map CanonicalExtractorParityRecord.input

/-- Codex hooks is a concrete leaderboard fixture promoted into the shared
Lean/Rust canonical input set. -/
theorem codexHooksExtractorInput_mem_canonicalExtractorParityInputs :
    codexHooksExtractorInput ∈ canonicalExtractorParityInputs := by
  -- native_decide: finite canonical extractor input and byte-fixture equality checks.
  native_decide

/-- Claude Agent SDK hooks is a concrete leaderboard fixture promoted into the shared
Lean/Rust canonical input set. -/
theorem claudeAgentSDKHooksExtractorInput_mem_canonicalExtractorParityInputs :
    claudeAgentSDKHooksExtractorInput ∈ canonicalExtractorParityInputs := by
  -- native_decide: finite canonical extractor input and byte-fixture equality checks.
  native_decide

end Legitimacy
