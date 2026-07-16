/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernelization.EndToEnd

/-!
# Legitimacy.Kernelization.Tightness

Tightness and independence witnesses for the kernelization predicates.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

/-! ## Tightness witnesses -/

theorem KernelizationClean_nonvacuous :
    ∃ observation :
      GovernanceKernelizationObservation kernelizationExampleArtifact,
      KernelizationClean observation :=
  ⟨cleanKernelizationObservation, cleanKernelizationObservation_clean⟩

theorem SourceEvidenceComplete_independent_of_graph_equivalence :
    AuthorityExtensionallyEquivalent sourceGapObservation.reported
        sourceGapObservation.effective ∧
      ¬ SourceEvidenceComplete sourceGapObservation := by
  constructor
  · constructor <;> intro edge <;>
      simp [sourceGapObservation, cleanAuthorityGraph, HasAuthorityEdge,
        HasAuthorityOverride]
  · intro hcomplete
    have hgap := hcomplete
      { fromNode := "principal", toNode := "reviewer" }
      (by
        left
        simp [sourceGapObservation, cleanAuthorityGraph, HasAuthorityEdge])
    simp [sourceGapObservation, SourceDerivesEdge] at hgap

theorem AuthorityExtensionallyEquivalent_independent_of_source_evidence :
    SourceEvidenceComplete unmodeledEdgeObservation ∧
      ¬ AuthorityExtensionallyEquivalent
        unmodeledEdgeObservation.reported
        unmodeledEdgeObservation.effective := by
  constructor
  · intro edge hedge
    simpa [unmodeledEdgeObservation, unmodeledEffectiveGraph,
      SourceDerivesEdge, HasAuthoritySurface, HasAuthorityEdge,
      HasAuthorityOverride] using hedge
  · intro heq
    have hreported :=
      (heq.1 { fromNode := "principal", toNode := "reviewer" }).2
        (by simp [unmodeledEdgeObservation, unmodeledEffectiveGraph,
          HasAuthorityEdge])
    simp [unmodeledEdgeObservation, unmodeledReportedGraph,
      HasAuthorityEdge] at hreported

theorem KernelizationHonesty_operationally_distinguishes_clean_and_certified :
    KernelizationHonesty cleanKernelizationObservation ∧
      KernelizationHonesty sourceGapObservation ∧
        ¬ KernelizationClean sourceGapObservation := by
  exact ⟨cleanKernelization_honesty,
    sourceEvidenceGapKernelization_honesty, sourceGap_not_clean⟩

theorem AuthorityEdgeDifference_nonvacuous :
    ∃ edge : AuthorityEdge,
      edge ∈ AuthorityEdgeDifference unmodeledEdgeObservation.effective
        unmodeledEdgeObservation.reported :=
  ⟨{ fromNode := "principal", toNode := "reviewer" },
    unmodeledEdgeCertificate_minimal⟩

theorem HiddenOverrideDominatesPair_nonvacuous :
    ∃ witness : HiddenOverrideWitness hiddenOverrideObservation,
      HiddenOverrideDominatesPair witness := by
  refine ⟨?_, ?_⟩
  · exact
      { overrideEdge := { fromNode := "policy", toNode := "deployment" }
        dominatedPair := { fromNode := "policy", toNode := "deployment" }
        effective_has_override := by
          simp [hiddenOverrideObservation, hiddenOverrideEffectiveGraph,
            HasAuthorityOverride]
        reported_lacks_override := by
          simp [hiddenOverrideObservation, hiddenOverrideReportedGraph,
            HasAuthorityOverride]
        dominates_pair := by simp
        dominated_pair_reported := by
          simp [hiddenOverrideObservation, hiddenOverrideReportedGraph,
            HasAuthorityEdge] }
  · simp [HiddenOverrideDominatesPair, hiddenOverrideObservation,
      hiddenOverrideReportedGraph, HasAuthorityEdge]

theorem SourceEvidenceDerivable_nonvacuous :
    ∃ edge : AuthorityEdge,
      SourceEvidenceDerivable cleanKernelizationObservation.sourceEdges edge :=
  ⟨{ fromNode := "principal", toNode := "reviewer" },
    (sourceEvidenceDerivable_iff _ _).2 (by
      simp [cleanKernelizationObservation, SourceDerivesEdge])⟩

theorem SourceEvidenceDerivable_independent_of_effective_edge :
    HasAuthoritySurface sourceGapObservation.effective
        { fromNode := "principal", toNode := "reviewer" } ∧
      ¬ SourceEvidenceDerivable sourceGapObservation.sourceEdges
        { fromNode := "principal", toNode := "reviewer" } := by
  exact sourceEvidenceGapCertificate_minimal

theorem BypassPathMinimal_nonvacuous :
    ∃ witness : BypassPathWitness bypassPathObservation,
      BypassPathMinimal bypassPathObservation.reported witness := by
  refine ⟨?_, ?_⟩
  · exact
      { source := "user"
        middle := ["router"]
        target := "admin"
        middle_nonempty := by simp
        route_nodup := by native_decide
        effective_route := by
          simpa [bypassPathObservation] using bypassGraph_route_permitted
        reported_route := by
          simpa [bypassPathObservation] using bypassGraph_route_permitted
        reported_lacks_direct := by
          simp [bypassPathObservation, bypassGraph, HasAuthorityEdge] }
  · exact bypassPathCertificate_minimal.2.2.2

def paddedBypassGraph : AuthorityGraph where
  nodes := ["user", "router", "auditor", "admin"]
  edges :=
    [ { fromNode := "user", toNode := "router" }
    , { fromNode := "router", toNode := "auditor" }
    , { fromNode := "auditor", toNode := "admin" }
    , { fromNode := "router", toNode := "admin" }
    ]
  overrides := []

private lemma paddedBypassGraph_full_route_permitted :
    AuthorityPathPermitted paddedBypassGraph
      ["user", "router", "auditor", "admin"] := by
  intro edge hedge
  fin_cases hedge <;> simp [paddedBypassGraph, HasAuthorityEdge]

private lemma paddedBypassGraph_shorter_route_permitted :
    AuthorityPathPermitted paddedBypassGraph
      ["user", "router", "admin"] := by
  intro edge hedge
  fin_cases hedge <;> simp [paddedBypassGraph, HasAuthorityEdge]

noncomputable def paddedBypassObservation :
    GovernanceKernelizationObservation kernelizationExampleArtifact where
  reported := paddedBypassGraph
  effective := paddedBypassGraph
  sourceEdges := paddedBypassGraph.edges
  reportedSemanticBridgeClean := true

def paddedBypassWitness :
    BypassPathWitness paddedBypassObservation where
  source := "user"
  middle := ["router", "auditor"]
  target := "admin"
  middle_nonempty := by simp
  route_nodup := by native_decide
  effective_route := by
    simpa [paddedBypassObservation] using
      paddedBypassGraph_full_route_permitted
  reported_route := by
    simpa [paddedBypassObservation] using
      paddedBypassGraph_full_route_permitted
  reported_lacks_direct := by
    simp [paddedBypassObservation, paddedBypassGraph, HasAuthorityEdge]

theorem BypassPathMinimal_excludes_padded_route :
    IsEdgePermittedBypass paddedBypassGraph
        ["user", "router", "auditor", "admin"] ∧
      ¬ BypassPathMinimal paddedBypassObservation.reported
        paddedBypassWitness := by
  constructor
  · exact ⟨⟨by norm_num, paddedBypassGraph_full_route_permitted⟩, by
      simp [routeDirectEdge?, routeTarget?, paddedBypassGraph,
        HasAuthorityEdge]⟩
  · intro hminimal
    have hproper :
        ProperRouteSublist ["user", "router", "admin"]
          ["user", "router", "auditor", "admin"] := by
      constructor
      · simp [routeSublists]
      · native_decide
    have hshorter :
        IsEdgePermittedBypass paddedBypassGraph
          ["user", "router", "admin"] := by
      exact ⟨⟨by norm_num, paddedBypassGraph_shorter_route_permitted⟩, by
        simp [routeDirectEdge?, routeTarget?, paddedBypassGraph,
          HasAuthorityEdge]⟩
    exact hminimal.2.2 ["user", "router", "admin"] hproper hshorter

end Safety

end Legitimacy
