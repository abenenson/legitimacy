/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.GovernanceExamples

/-!
# Legitimacy.Safety.KernelSafety.StatefulExamples.ExtractorArtifacts

Lean-side model extractor artifacts used by the bounded safety stack examples.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-- Extracted artifact for the concrete governance example. This is a Lean-side
model artifact used to instantiate the contracted-extractor clause. -/
noncomputable def exampleGovernanceExtractedKernelArtifact :
    ExtractedKernelArtifact where
  n := 1
  sys := exampleGovernedSystem
  data := exampleGovernanceKernelData

/-- Constant Lean model extractor returning the concrete governance example.
This is only a Lean-side model inhabitant for contract plumbing; it is not a
meaningful source extraction function. Production parity for real emitted
artifacts is enforced separately by Rust fixture tests. -/
noncomputable def exampleGovernanceKernelExtractor : KernelExtractor :=
  fun _ => exampleGovernanceExtractedKernelArtifact

/-- Extracted artifact for the widened-signal variant of the concrete
governance example. The governed system is the same, but the emitted datum is
propositionally distinct from the live datum used by the worked stack
instantiation below. -/
noncomputable def exampleGovernanceWideSignalExtractedKernelArtifact :
    ExtractedKernelArtifact where
  n := 1
  sys := exampleGovernedSystem
  data := exampleGovernanceWideSignalKernelData

/-- Constant Lean model extractor returning the widened-signal example datum.
This is only a Lean-side model inhabitant for contract plumbing; it is not a
meaningful source extraction function. Production parity for real emitted
artifacts is enforced separately by Rust fixture tests. -/
noncomputable def exampleGovernanceWideSignalKernelExtractor :
    KernelExtractor :=
  fun _ => exampleGovernanceWideSignalExtractedKernelArtifact

/-- Non-constant Lean model extractor for the worked bounded-stack example.
The AutoGen-sized source lane emits the widened-signal artifact; other bounded
inputs emit the base governance artifact. This remains a Lean-side model of the
contract surface rather than Rust operational semantics, but the output is no
longer independent of the source input. -/
noncomputable def exampleGovernanceSourceSensitiveKernelExtractor :
    KernelExtractor :=
  fun src =>
    { n := 1
      sys := exampleGovernedSystem
      data :=
        if src.byteSize = autogenExtractorInput.byteSize then
          exampleGovernanceWideSignalKernelData
        else
          exampleGovernanceKernelData }

/-- The concrete governance example satisfies the bounded extractor contract
for the constant Lean model extractor. -/
def exampleGovernanceKernelExtractor_contract :
    BoundedExtractorContract exampleGovernanceKernelExtractor where
  sourceEvidence := BoundedExtractorSourceEvidence.ofWellFormed
  runtimeSound := by
    intro _src _evidence
    exact exampleGovernanceSemanticKernel.runtimeKernel
  semanticBridgeSound := by
    intro _src _evidence
    exact exampleGovernanceSemanticKernel.semanticBridge

/-- The widened-signal example satisfies the bounded extractor contract for
the constant Lean model extractor. -/
def exampleGovernanceWideSignalKernelExtractor_contract :
    BoundedExtractorContract exampleGovernanceWideSignalKernelExtractor where
  sourceEvidence := BoundedExtractorSourceEvidence.ofWellFormed
  runtimeSound := by
    intro _src _evidence
    exact exampleGovernanceWideSignalSemanticKernel.runtimeKernel
  semanticBridgeSound := by
    intro _src _evidence
    exact exampleGovernanceWideSignalSemanticKernel.semanticBridge

/-- The source-sensitive worked extractor satisfies the bounded extractor
contract by a real case split on the source byte count. -/
def exampleGovernanceSourceSensitiveKernelExtractor_contract :
    BoundedExtractorContract exampleGovernanceSourceSensitiveKernelExtractor where
  sourceEvidence := BoundedExtractorSourceEvidence.ofWellFormed
  runtimeSound := by
    intro src _evidence
    by_cases hbytes : src.byteSize = autogenExtractorInput.byteSize
    · simpa [exampleGovernanceSourceSensitiveKernelExtractor, hbytes,
        ExtractedKernelArtifact.IsRuntimeKernel]
        using exampleGovernanceWideSignalSemanticKernel.runtimeKernel
    · simpa [exampleGovernanceSourceSensitiveKernelExtractor, hbytes,
        ExtractedKernelArtifact.IsRuntimeKernel]
        using exampleGovernanceSemanticKernel.runtimeKernel
  semanticBridgeSound := by
    intro src _evidence
    by_cases hbytes : src.byteSize = autogenExtractorInput.byteSize
    · simpa [exampleGovernanceSourceSensitiveKernelExtractor, hbytes,
        ExtractedKernelArtifact.HasSemanticBridge]
        using exampleGovernanceWideSignalSemanticKernel.semanticBridge
    · simpa [exampleGovernanceSourceSensitiveKernelExtractor, hbytes,
        ExtractedKernelArtifact.HasSemanticBridge]
        using exampleGovernanceSemanticKernel.semanticBridge

/-- Semantic transfer from the widened-signal extracted datum to the live
worked-example datum. This is explicit rather than a definitional equality:
both data live over the same governed system, but their cached signal ranges
differ. -/
noncomputable def exampleGovernanceWideSignalExtracted_to_liveSemantic :
    (src : ExtractorInput) →
      ExtractedKernelSemanticTransfer
        (exampleGovernanceWideSignalKernelExtractor src).data
        exampleGovernanceKernelData :=
  fun _src _hsemanticExtracted => exampleGovernanceSemanticKernel

/-- The widened-signal extractor is not definitionally returning the live datum
used by the worked stack instantiation. -/
lemma exampleGovernanceWideSignalExtractor_data_ne_live :
    exampleGovernanceKernelData ≠
      (exampleGovernanceWideSignalKernelExtractor
        autogenExtractorInput).data := by
  exact exampleGovernanceWideSignalKernelData_ne

/-- Semantic transfer from the source-sensitive extracted datum to the live
worked-example datum. Both branches emit semantic kernels over the same
governed system; the transfer keeps the live trajectory datum explicit. -/
noncomputable def exampleGovernanceSourceSensitiveExtracted_to_liveSemantic :
    (src : ExtractorInput) →
      ExtractedKernelSemanticTransfer
        (exampleGovernanceSourceSensitiveKernelExtractor src).data
        exampleGovernanceKernelData :=
  fun _src _hsemanticExtracted => exampleGovernanceSemanticKernel

end Safety

end Legitimacy
