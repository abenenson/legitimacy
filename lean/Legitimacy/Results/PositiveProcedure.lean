/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Certificates.PositiveProcedureCertificate

/-!
# Downstream use of positive-procedure certificates

This module roots the spectral positive procedure in the graph-diagnostic
results layer. Consistency now uses the profile-uniform spectral reflection
that sends every all-profile binary consistency counterexample into the
certificate's lower-scale no-violation range.
-/

set_option autoImplicit false

namespace Legitimacy

open MeasureTheory ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Finite α] [Finite β]
variable {n : Nat} [NeZero n]

/-- Downstream graph classification obtained by composing the exact
positive-procedure extractor with the graph-diagnostic bridges.

In the current exact substrate the extractor returns either consistency for a
strict subcritical scale or monotonicity at the boundary. Consistency consumes
the profile-uniform spectral reflection; monotonicity still consumes the
boundary graph-diagnostic carrier. -/
theorem positiveProcedure_graphDiagnostic_classification
    (K : CapacityKernel α β n) (hK : WellConditionedForCapacity K)
    (c : ℚ) (hcpos : 0 < c) (hc : c ≤ K.C_star)
    (graph : GovernanceGraph)
    (hreflection :
      PositiveProcedureCertificate.GraphConsistencySpectralReflection
        K c graph)
    (hcarrier : PositiveProcedureCertificate.GraphDiagnosticCarrier K c graph) :
    ∃ cert : PositiveProcedureCertificate K c,
      (cert.kind = PreservedDiagnostic.consistency ∧ GraphConsistency graph) ∨
        (cert.kind = PreservedDiagnostic.monotonicity ∧ GraphMonotonicity graph) := by
  rcases governance_certificate_constructible K hK c hcpos hc with
    ⟨cert, hkind | hkind⟩
  · exact ⟨cert, Or.inl ⟨hkind,
      PositiveProcedureCertificate.kind_consistency_to_GraphConsistency
        hreflection hkind⟩⟩
  · exact ⟨cert, Or.inr ⟨hkind,
      PositiveProcedureCertificate.kind_monotonicity_to_GraphMonotonicity
        hK hcarrier hkind⟩⟩

end Legitimacy
