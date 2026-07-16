/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Graph

/-!
# Legitimacy.Extract.ASTWitness

Lean-side interface for binding an extracted `GovernanceGraph` derivation step
to the canonical source-shape-and-token hash emitted by the Rust extractor.

Lean does not compute SHA-256 or model tree-sitter execution here. The Rust
verifier recomputes the canonical parsed-source shape plus lexical-token hash
and graph hash; this module records the exact strings that a generated theorem
witness must carry and threads them into the governance-graph derivation object.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Hash metadata emitted by the Rust AST theorem-witness protocol. -/
structure ASTTheoremWitnessBinding where
  /-- Source package or directory identifier. -/
  sourceId : String
  /-- Lean theorem name claimed by the generated witness. -/
  theoremName : String
  /-- Canonical source-shape-and-token hash, including file paths and language tags. -/
  sourceAstHash : String
  /-- Canonical pretty-JSON hash of the extracted governance graph. -/
  governanceGraphHash : String
  deriving Repr, DecidableEq

namespace ASTTheoremWitnessBinding

/-- The externally recomputed hashes and theorem name match this binding. -/
def Matches
    (binding : ASTTheoremWitnessBinding)
    (sourceId theoremName sourceAstHash governanceGraphHash : String) : Prop :=
  binding.sourceId = sourceId ∧
    binding.theoremName = theoremName ∧
    binding.sourceAstHash = sourceAstHash ∧
    binding.governanceGraphHash = governanceGraphHash

end ASTTheoremWitnessBinding

/-- A governance-graph derivation step carrying the AST/theorem witness binding
that generated it. -/
structure HashedGovernanceGraphDerivation where
  graph : GovernanceGraph
  binding : ASTTheoremWitnessBinding

namespace HashedGovernanceGraphDerivation

/-- The derivation step verifies against the externally recomputed witness
strings. -/
def VerifiesWitness
    (step : HashedGovernanceGraphDerivation)
    (sourceId theoremName sourceAstHash governanceGraphHash : String) : Prop :=
  step.binding.Matches sourceId theoremName sourceAstHash governanceGraphHash

end HashedGovernanceGraphDerivation

/-- If the Rust verifier recomputes the same source-shape-and-token hash, graph
hash, theorem name, and source id carried by the Lean binding, the
governance-graph derivation step is bound to that exact witness. -/
lemma ast_theorem_witness_binding_verified
    (step : HashedGovernanceGraphDerivation)
    (sourceId theoremName sourceAstHash governanceGraphHash : String)
    (hmatch :
      step.binding.Matches sourceId theoremName sourceAstHash governanceGraphHash) :
    step.VerifiesWitness sourceId theoremName sourceAstHash governanceGraphHash := by
  exact hmatch

/-- The graph exposed by a verified hashed derivation is the graph packaged in
that derivation step; hash verification constrains provenance, not graph
semantics. -/
lemma ast_theorem_witness_binding_preserves_graph
    (step : HashedGovernanceGraphDerivation)
    (sourceId theoremName sourceAstHash governanceGraphHash : String)
    (_hverified :
      step.VerifiesWitness sourceId theoremName sourceAstHash governanceGraphHash) :
    step.graph = step.graph := by
  rfl

end Legitimacy
