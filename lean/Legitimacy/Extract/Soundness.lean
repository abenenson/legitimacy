/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.CanonicalInputs
import Legitimacy.Results.AutoGenAdmissibilityAudit
import Legitimacy.Results.ClaudeAgentSDKAdmissibilityAudit
import Legitimacy.Results.GovernanceAdmissibilityAudit
import Legitimacy.Results.LeaderboardAdmissibilityAudits

/-!
# Legitimacy.Extract.Soundness

Bounded extractor contract for connecting empirical extraction artifacts to the
Lean kernel target.

The Rust extractor is an empirical parser and serializer. This module does not
model Rust execution. Instead it states the Lean-side contract an extracted
artifact must satisfy after parsing succeeds within a declared bound. Under that
contract, the extracted kernel artifact is a semantic legitimacy kernel.

Existing byte-stability and fixture round-trip tests are the empirical evidence
that Rust emits the committed artifacts; the theorems here are the formal
obligation those artifacts must discharge in Lean.
-/

set_option autoImplicit false

namespace Legitimacy

/-- One extracted kernel artifact, existentially packaging the finite governed
system index together with the unbundled kernel data over that system. -/
structure ExtractedKernelArtifact where
  n : Nat
  sys : GovernedSystem n
  data : LegitimacyKernelData sys

namespace ExtractedKernelArtifact

/-- Runtime kernel obligation for an extracted artifact. -/
def IsRuntimeKernel (artifact : ExtractedKernelArtifact) : Prop :=
  IsLegitimacyKernel artifact.data

/-- Semantic kernel obligation for an extracted artifact. -/
def IsSemanticKernel (artifact : ExtractedKernelArtifact) : Prop :=
  IsSemanticLegitimacyKernel artifact.data

/-- Graph-diagnostic and spectral bridge obligation for an extracted artifact. -/
def HasSemanticBridge (artifact : ExtractedKernelArtifact) : Prop :=
  KernelSemanticBridge artifact.data

end ExtractedKernelArtifact

/-- Lean model of an extractor from bounded source inputs to kernel artifacts.
The production Rust implementation is related to such a model empirically by
byte-stable fixture tests, not by a theorem over Rust operational semantics. -/
abbrev KernelExtractor := ExtractorInput → ExtractedKernelArtifact

/-- Concrete boundary evidence for one bounded extractor source package.

The bounded byte count is carried as a `Fin` witness, so contract users retain
the concrete byte bound rather than only an opaque well-formedness proposition.
Coverage and parser cleanliness mirror the other extractor-boundary facts that
authorize a soundness claim. -/
structure BoundedExtractorSourceEvidence (src : ExtractorInput) where
  /-- The source byte count as an inhabitant of the declared finite bound. -/
  boundedBytes : Fin (src.sizeBound + 1)
  /-- The finite byte witness is exactly the source byte count. -/
  boundedBytes_eq : boundedBytes.val = src.byteSize
  /-- The extractor reported complete source coverage. -/
  coverageComplete : src.coverageComplete = true
  /-- The extractor reported no parser failures. -/
  parserClean : src.parserErrors = 0

namespace BoundedExtractorSourceEvidence

/-- Concrete boundary evidence implies the input's well-formedness predicate. -/
def wellFormed
    {src : ExtractorInput}
    (evidence : BoundedExtractorSourceEvidence src) :
    src.WellFormed := by
  refine ⟨?_, evidence.coverageComplete, evidence.parserClean⟩
  rw [← evidence.boundedBytes_eq]
  exact Nat.lt_succ_iff.mp evidence.boundedBytes.isLt

/-- Materialize concrete boundary evidence from a well-formed source package. -/
def ofWellFormed
    (src : ExtractorInput)
    (hwellFormed : src.WellFormed) :
    BoundedExtractorSourceEvidence src where
  boundedBytes := ⟨src.byteSize, Nat.lt_succ_of_le hwellFormed.1⟩
  boundedBytes_eq := rfl
  coverageComplete := hwellFormed.2.1
  parserClean := hwellFormed.2.2

end BoundedExtractorSourceEvidence

/-- Bounded extractor contract. For every well-formed bounded input, the
contract first materializes concrete byte-bound, coverage, and parser-clean
evidence. Against that evidence, the extractor output must satisfy the five
runtime kernel axioms and the explicit semantic bridge tying the artifact to
graph diagnostics and spectral well-connectedness. -/
structure BoundedExtractorContract (extract : KernelExtractor) where
  /-- Concrete source-boundary evidence for well-formed source packages. -/
  sourceEvidence :
    ∀ src : ExtractorInput,
      src.WellFormed → BoundedExtractorSourceEvidence src
  /-- The extracted artifact satisfies the five runtime kernel axioms. -/
  runtimeSound :
    ∀ src : ExtractorInput,
      BoundedExtractorSourceEvidence src → (extract src).IsRuntimeKernel
  /-- The extracted artifact satisfies the diagnostic/spectral semantic bridge. -/
  semanticBridgeSound :
    ∀ src : ExtractorInput,
      BoundedExtractorSourceEvidence src → (extract src).HasSemanticBridge

/-- Main bounded extraction-soundness theorem: a contracted extractor maps any
well-formed bounded source package to a semantic legitimacy kernel. -/
lemma bounded_extractor_contract_sound
    (extract : KernelExtractor)
    (hcontract : BoundedExtractorContract extract)
    (src : ExtractorInput)
    (hwellFormed : src.WellFormed) :
    (extract src).IsSemanticKernel := by
  let evidence := hcontract.sourceEvidence src hwellFormed
  exact
    { runtimeKernel := hcontract.runtimeSound src evidence
      semanticBridge := hcontract.semanticBridgeSound src evidence }

/-- Runtime-only projection of the bounded extraction contract. -/
lemma bounded_extractor_contract_runtime_sound
    (extract : KernelExtractor)
    (hcontract : BoundedExtractorContract extract)
    (src : ExtractorInput)
    (hwellFormed : src.WellFormed) :
    (extract src).IsRuntimeKernel :=
  (bounded_extractor_contract_sound extract hcontract src hwellFormed).runtimeKernel

/-- Named formal subset currently covered by the extracted-graph admissibility audit:
the committed Lean artifact evaluates to a legitimate audit verdict under the
Lean port of the Rust extracted-graph audit semantics. -/
def ExtractedGraphAdmissibilityContract (subject : AuditSubject) : Prop :=
  governanceAdmissibilityVerdict subject = AuditVerdict.legitimate

/-- Byte strings emitted by the external extractor and represented in Lean.

This type is deliberately just bytes: the theorem below records equality of
finite fixture outputs, not a parser or serializer semantics for Rust. -/
abbrev FixtureBytes := List UInt8

/-- External byte-match evidence relating a Rust extractor run to Lean-modeled
bytes for one bounded source input.

This proposition is intentionally just byte equality. It is supplied by the
empirical fixture tests for canonical inputs, not derived here from Rust
operational semantics, parser correctness, or serializer correctness. -/
def ExternalExtractorByteMatch
    (_src : ExtractorInput)
    (rustOutputBytes leanModeledBytes : FixtureBytes) : Prop :=
  rustOutputBytes = leanModeledBytes

/-- Explicit empirical/formal extractor boundary.

Given a bounded extractor contract, Lean proves the runtime kernel obligation,
the semantic bridge obligation, and therefore semantic kernel soundness for a
well-formed source package. The byte-match premise is returned unchanged to make
the boundary visible: the theorem consumes external evidence that a Rust run's
output bytes match the Lean-modeled bytes for this input; it does not verify
Rust execution, parser correctness for arbitrary inputs, serializer semantics,
or runtime-kernel behavior outside the contracted artifact. -/
lemma extractor_byte_stable_soundness_boundary
    (extract : KernelExtractor)
    (hcontract : BoundedExtractorContract extract)
    (src : ExtractorInput)
    (rustOutputBytes leanModeledBytes : FixtureBytes)
    (hbyteMatch :
      ExternalExtractorByteMatch src rustOutputBytes leanModeledBytes)
    (hwellFormed : src.WellFormed) :
    (extract src).IsRuntimeKernel ∧
      (extract src).HasSemanticBridge ∧
      (extract src).IsSemanticKernel ∧
      ExternalExtractorByteMatch src rustOutputBytes leanModeledBytes := by
  let evidence := hcontract.sourceEvidence src hwellFormed
  exact
    ⟨hcontract.runtimeSound src evidence,
      hcontract.semanticBridgeSound src evidence,
      bounded_extractor_contract_sound extract hcontract src hwellFormed,
      hbyteMatch⟩

/-- One finite extractor-parity fixture. The `rustOutputBytes` field is the byte
string emitted by the production Rust extractor in an external fixture run; the
`leanFixtureBytes` field is the committed/canonical byte string represented on
the Lean side. -/
structure EmpiricalParityFixture where
  /-- Bounded-source descriptor naming the fixture. -/
  input : ExtractorInput
  /-- Lean audit graph subject represented by the canonical fixture bytes. -/
  subject : AuditSubject
  /-- Output bytes reported by the Rust fixture run. -/
  rustOutputBytes : FixtureBytes
  /-- Canonical bytes represented by the Lean fixture. -/
  leanFixtureBytes : FixtureBytes

namespace EmpiricalParityFixture

/-- The finite fixture has byte parity between Rust output and Lean fixture. -/
def ByteParity (fixture : EmpiricalParityFixture) : Prop :=
  fixture.rustOutputBytes = fixture.leanFixtureBytes

/-- The finite fixture's Lean graph artifact satisfies the governance
admissibility audit contract. -/
def LeanContract (fixture : EmpiricalParityFixture) : Prop :=
  ExtractedGraphAdmissibilityContract fixture.subject

end EmpiricalParityFixture

/-- Finite empirical parity certificate for canonical extractor fixtures.

The certificate says exactly two things:

* each canonical bounded input has a listed fixture, and every listed fixture is
  one of the canonical inputs;
* each listed fixture carries byte equality between the external Rust output and
  the Lean canonical bytes, plus the Lean extracted-graph admissibility contract.

It does not claim Rust operational soundness for all well-formed inputs. -/
def EmpiricalParityCertificate
    (canonicalInputs : List ExtractorInput)
    (fixtures : List EmpiricalParityFixture) : Prop :=
  (∀ src : ExtractorInput,
      src ∈ canonicalInputs →
        ∃ fixture : EmpiricalParityFixture,
          fixture ∈ fixtures ∧ fixture.input = src) ∧
    (∀ fixture : EmpiricalParityFixture,
      fixture ∈ fixtures →
        fixture.input ∈ canonicalInputs ∧
          fixture.ByteParity ∧
          fixture.LeanContract)

/-- Canonical input descriptor for the compiler audit graph fixture. The source
bytes themselves remain external to Lean; this descriptor records the bounded
fixture identity used by the empirical parity certificate. -/
def compilerAuditExtractorInput : ExtractorInput where
  sourceId := "compiler-audit"
  byteSize := 0
  sizeBound := 0
  coverageComplete := true
  parserErrors := 0

/-- Compiler-audit empirical parity fixture, parameterized by the external Rust
bytes and the Lean canonical bytes. -/
def compilerAuditEmpiricalParityFixture
    (rustBytes leanBytes : FixtureBytes) : EmpiricalParityFixture where
  input := compilerAuditExtractorInput
  subject := compilerAuditGraph
  rustOutputBytes := rustBytes
  leanFixtureBytes := leanBytes

/-- AutoGen empirical parity fixture, parameterized by the external Rust bytes
and the Lean canonical bytes. -/
def autogenEmpiricalParityFixture
    (rustBytes leanBytes : FixtureBytes) : EmpiricalParityFixture where
  input := autogenExtractorInput
  subject := autoGenExtractedGraph
  rustOutputBytes := rustBytes
  leanFixtureBytes := leanBytes

/-- Codex hooks empirical parity fixture, parameterized by external Rust bytes
and committed canonical bytes. -/
def codexHooksEmpiricalParityFixture
    (rustBytes leanBytes : FixtureBytes) : EmpiricalParityFixture where
  input := codexHooksExtractorInput
  subject := codexHooksExtractedGraph
  rustOutputBytes := rustBytes
  leanFixtureBytes := leanBytes

/-- Claude Agent SDK hooks empirical parity fixture, parameterized by external Rust
bytes and committed canonical bytes. -/
def claudeAgentSDKHooksEmpiricalParityFixture
    (rustBytes leanBytes : FixtureBytes) : EmpiricalParityFixture where
  input := claudeAgentSDKHooksExtractorInput
  subject := claudeAgentSDKHooksExtractedGraph
  rustOutputBytes := rustBytes
  leanFixtureBytes := leanBytes

/-- CrewAI empirical parity fixture, parameterized by external Rust bytes and
committed canonical bytes. -/
def crewaiEmpiricalParityFixture
    (rustBytes leanBytes : FixtureBytes) : EmpiricalParityFixture where
  input := crewaiExtractorInput
  subject := crewAIExtractedGraph
  rustOutputBytes := rustBytes
  leanFixtureBytes := leanBytes

/-- OpenClaw infrastructure empirical parity fixture, parameterized by external
Rust bytes and committed canonical bytes. -/
def openclawInfraEmpiricalParityFixture
    (rustBytes leanBytes : FixtureBytes) : EmpiricalParityFixture where
  input := openclawInfraExtractorInput
  subject := openClawInfraExtractedGraph
  rustOutputBytes := rustBytes
  leanFixtureBytes := leanBytes

/-- The compiler audit fixture satisfies the extracted-graph admissibility contract. -/
lemma compiler_audit_satisfies_extracted_graph_admissibility_contract :
    ExtractedGraphAdmissibilityContract compilerAuditGraph :=
  compiler_audit_is_self_legitimate

/-- The AutoGen leaderboard fixture satisfies the extracted-graph admissibility
contract. Rust parity tests separately check that the emitted JSON bytes match
the canonical fixture represented by `autoGenExtractedGraph`. -/
lemma autogen_satisfies_extracted_graph_admissibility_contract :
    ExtractedGraphAdmissibilityContract autoGenExtractedGraph :=
  autoGen_extracted_graph_is_self_legitimate

/-- Finite byte-parity certificate for canonical extractor fixtures.

Unlike `EmpiricalParityCertificate`, this certificate makes no Lean
audit claim about each graph. It is the honest surface for large generated
leaderboard graphs whose committed bytes are pinned by Rust fixture tests but
whose full Lean governance-admissibility audit proof has not yet been discharged
in the release gate. -/
def EmpiricalByteParityCertificate
    (canonicalInputs : List ExtractorInput)
    (fixtures : List EmpiricalParityFixture) : Prop :=
  (∀ src : ExtractorInput,
      src ∈ canonicalInputs →
        ∃ fixture : EmpiricalParityFixture,
          fixture ∈ fixtures ∧ fixture.input = src) ∧
    (∀ fixture : EmpiricalParityFixture,
      fixture ∈ fixtures →
        fixture.input ∈ canonicalInputs ∧ fixture.ByteParity)

/-- The shared canonical leaderboard fixtures form a byte-parity certificate
once the external byte-parity facts are supplied. The byte-parity hypotheses
are exactly the facts checked by the Rust fixture tests; only AutoGen currently
has a separately discharged Lean governance-admissibility audit contract. -/
lemma canonical_leaderboard_fixtures_byte_parity_certificate
    (autogenRustBytes autogenLeanBytes codexRustBytes codexLeanBytes
      claudeAgentSDKRustBytes claudeAgentSDKLeanBytes crewaiRustBytes crewaiLeanBytes
      openclawRustBytes openclawLeanBytes : FixtureBytes)
    (hautogenBytes : autogenRustBytes = autogenLeanBytes)
    (hcodexBytes : codexRustBytes = codexLeanBytes)
    (hclaudeAgentSDKBytes : claudeAgentSDKRustBytes = claudeAgentSDKLeanBytes)
    (hcrewaiBytes : crewaiRustBytes = crewaiLeanBytes)
    (hopenclawBytes : openclawRustBytes = openclawLeanBytes) :
    EmpiricalByteParityCertificate
      canonicalExtractorParityInputs
      [ autogenEmpiricalParityFixture autogenRustBytes autogenLeanBytes
      , codexHooksEmpiricalParityFixture codexRustBytes codexLeanBytes
      , claudeAgentSDKHooksEmpiricalParityFixture claudeAgentSDKRustBytes claudeAgentSDKLeanBytes
      , crewaiEmpiricalParityFixture crewaiRustBytes crewaiLeanBytes
      , openclawInfraEmpiricalParityFixture openclawRustBytes openclawLeanBytes ] := by
  constructor
  · intro src hsrc
    simp [canonicalExtractorParityInputs, canonicalExtractorParityRecords,
      CanonicalExtractorParityRecord.input] at hsrc
    rcases hsrc with rfl | rfl | rfl | rfl | rfl
    · refine ⟨autogenEmpiricalParityFixture autogenRustBytes autogenLeanBytes, ?_, rfl⟩
      exact List.Mem.head _
    · refine ⟨codexHooksEmpiricalParityFixture codexRustBytes codexLeanBytes, ?_, rfl⟩
      exact List.Mem.tail _ (List.Mem.head _)
    · refine
        ⟨claudeAgentSDKHooksEmpiricalParityFixture claudeAgentSDKRustBytes claudeAgentSDKLeanBytes,
          ?_, rfl⟩
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · refine ⟨crewaiEmpiricalParityFixture crewaiRustBytes crewaiLeanBytes, ?_, rfl⟩
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    · refine
        ⟨openclawInfraEmpiricalParityFixture openclawRustBytes openclawLeanBytes,
          ?_, rfl⟩
      exact
        List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  · intro fixture hfixture
    simp at hfixture
    rcases hfixture with rfl | rfl | rfl | rfl | rfl
    · exact ⟨List.Mem.head _, hautogenBytes⟩
    · exact ⟨List.Mem.tail _ (List.Mem.head _), hcodexBytes⟩
    · exact
        ⟨List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), hclaudeAgentSDKBytes⟩
    · exact
        ⟨List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
          hcrewaiBytes⟩
    · exact
        ⟨List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
          hopenclawBytes⟩

/-- AutoGen is the currently discharged extracted-graph admissibility leaderboard
fixture: its Lean literal mirrors the committed JSON and satisfies the governance
admissibility audit contract. -/
lemma autogen_leaderboard_fixture_empirical_parity_certificate
    (autogenRustBytes autogenLeanBytes : FixtureBytes)
    (hautogenBytes : autogenRustBytes = autogenLeanBytes) :
    EmpiricalParityCertificate
      [autogenExtractorInput]
      [autogenEmpiricalParityFixture autogenRustBytes autogenLeanBytes] := by
  constructor
  · intro src hsrc
    simp at hsrc
    subst hsrc
    exact ⟨autogenEmpiricalParityFixture autogenRustBytes autogenLeanBytes,
      List.Mem.head _, rfl⟩
  · intro fixture hfixture
    simp at hfixture
    subst hfixture
    exact ⟨List.Mem.head _, hautogenBytes,
      autogen_satisfies_extracted_graph_admissibility_contract⟩

end Legitimacy
