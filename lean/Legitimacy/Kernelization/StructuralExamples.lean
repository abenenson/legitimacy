/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernelization.Fixtures

/-!
# Legitimacy.Kernelization.StructuralExamples

Worked clean, unmodeled-edge, bypass-path, hidden-override, and source-evidence-gap examples.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

/-! ## Worked graph and certificate examples -/

def cleanAuthorityGraph : AuthorityGraph where
  nodes := ["principal", "reviewer"]
  edges := [{ fromNode := "principal", toNode := "reviewer" }]
  overrides := []

noncomputable def cleanKernelizationObservation :
    GovernanceKernelizationObservation kernelizationExampleArtifact where
  reported := cleanAuthorityGraph
  effective := cleanAuthorityGraph
  sourceEdges := [{ fromNode := "principal", toNode := "reviewer" }]
  reportedSemanticBridgeClean := true

theorem cleanKernelizationObservation_clean :
    KernelizationClean cleanKernelizationObservation := by
  refine ⟨?_, ?_, kernelizationExampleSemanticKernel⟩
  · constructor <;> intro edge <;> simp [cleanKernelizationObservation,
      cleanAuthorityGraph, HasAuthorityEdge, HasAuthorityOverride]
  · intro edge hedge
    simpa [cleanKernelizationObservation, cleanAuthorityGraph,
      SourceDerivesEdge, HasAuthoritySurface, HasAuthorityEdge,
      HasAuthorityOverride] using hedge

noncomputable def sacrificeStepCleanObservation :
    GovernanceKernelizationObservation kernelizationSacrificeStepArtifact where
  reported := cleanAuthorityGraph
  effective := cleanAuthorityGraph
  sourceEdges := [{ fromNode := "principal", toNode := "reviewer" }]
  reportedSemanticBridgeClean := true

theorem sacrificeStepCleanObservation_clean :
    KernelizationClean sacrificeStepCleanObservation := by
  refine ⟨?_, ?_, kernelizationExampleSemanticKernel⟩
  · constructor <;> intro edge <;> simp [sacrificeStepCleanObservation,
      cleanAuthorityGraph, HasAuthorityEdge, HasAuthorityOverride]
  · intro edge hedge
    simpa [sacrificeStepCleanObservation, cleanAuthorityGraph,
      SourceDerivesEdge, HasAuthoritySurface, HasAuthorityEdge,
      HasAuthorityOverride] using hedge

def unmodeledReportedGraph : AuthorityGraph where
  nodes := ["principal", "reviewer"]
  edges := []
  overrides := []

def unmodeledEffectiveGraph : AuthorityGraph where
  nodes := ["principal", "reviewer"]
  edges := [{ fromNode := "principal", toNode := "reviewer" }]
  overrides := []

noncomputable def unmodeledEdgeObservation :
    GovernanceKernelizationObservation kernelizationExampleArtifact where
  reported := unmodeledReportedGraph
  effective := unmodeledEffectiveGraph
  sourceEdges := [{ fromNode := "principal", toNode := "reviewer" }]
  reportedSemanticBridgeClean := true

def unmodeledEdgeCertificate :
    HiddenAuthorityCertificate unmodeledEdgeObservation :=
  HiddenAuthorityCertificate.unmodeledEdge
    { edge := { fromNode := "principal", toNode := "reviewer" }
      effective_has_edge := by
        simp [unmodeledEdgeObservation, unmodeledEffectiveGraph,
          HasAuthorityEdge]
      reported_lacks_edge := by
        simp [unmodeledEdgeObservation, unmodeledReportedGraph,
          HasAuthorityEdge] }

theorem unmodeledEdgeCertificate_minimal :
    MinimalHiddenAuthority unmodeledEdgeCertificate := by
  change
    { fromNode := "principal", toNode := "reviewer" } ∈
      AuthorityEdgeDifference unmodeledEdgeObservation.effective
        unmodeledEdgeObservation.reported
  simp [AuthorityEdgeDifference, unmodeledEdgeObservation,
    unmodeledEffectiveGraph, unmodeledReportedGraph]

def bypassGraph : AuthorityGraph where
  nodes := ["user", "router", "admin"]
  edges :=
    [ { fromNode := "user", toNode := "router" }
    , { fromNode := "router", toNode := "admin" }
    ]
  overrides := []

lemma bypassGraph_route_permitted :
    AuthorityPathPermitted bypassGraph ["user", "router", "admin"] := by
  intro edge hedge
  fin_cases hedge <;> simp [bypassGraph, HasAuthorityEdge]

noncomputable def bypassPathObservation :
    GovernanceKernelizationObservation kernelizationExampleArtifact where
  reported := bypassGraph
  effective := bypassGraph
  sourceEdges :=
    [ { fromNode := "user", toNode := "router" }
    , { fromNode := "router", toNode := "admin" }
    ]
  reportedSemanticBridgeClean := true

def bypassPathCertificate :
    HiddenAuthorityCertificate bypassPathObservation :=
  HiddenAuthorityCertificate.bypassPath
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

theorem bypassPathCertificate_minimal :
    MinimalHiddenAuthority bypassPathCertificate := by
  dsimp [MinimalHiddenAuthority, bypassPathCertificate]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · native_decide
  · exact ⟨by norm_num, by
      simpa [bypassPathObservation] using bypassGraph_route_permitted⟩
  · change BypassPathMinimal bypassPathObservation.reported
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
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨by norm_num, by
        simpa [bypassPathObservation] using bypassGraph_route_permitted⟩
    · exact ⟨⟨by norm_num, by
        simpa [bypassPathObservation] using bypassGraph_route_permitted⟩, by
          simp [routeDirectEdge?, routeTarget?, bypassPathObservation,
            bypassGraph, HasAuthorityEdge]⟩
    · intro shorter hproper hbypass
      rcases hproper with ⟨hsub, hne⟩
      dsimp [routeSublists] at hsub
      have hcases :
        shorter = [] ∨ shorter = ["admin"] ∨
          shorter = ["router"] ∨ shorter = ["router", "admin"] ∨
          shorter = ["user"] ∨ shorter = ["user", "admin"] ∨
          shorter = ["user", "router"] ∨
          shorter = ["user", "router", "admin"] := by
        simpa using hsub
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (by norm_num : ¬ 2 ≤ ([] : List AuthorityNodeId).length)
          hbypass.1.1
      · exact (by norm_num : ¬ 2 ≤ (["admin"] : List AuthorityNodeId).length)
          hbypass.1.1
      · exact (by norm_num :
          ¬ 2 ≤ (["router"] : List AuthorityNodeId).length) hbypass.1.1
      · exact hbypass.2 (by
          simp [bypassPathObservation, bypassGraph, HasAuthorityEdge])
      · exact (by norm_num : ¬ 2 ≤ (["user"] : List AuthorityNodeId).length)
          hbypass.1.1
      · have hdirect := hbypass.1.2
          { fromNode := "user", toNode := "admin" }
          (by simp [pathAuthorityEdges])
        simp [bypassPathObservation, bypassGraph, HasAuthorityEdge] at hdirect
      · exact hbypass.2 (by
          simp [bypassPathObservation, bypassGraph, HasAuthorityEdge])
      · exact (hne rfl).elim

def hiddenOverrideReportedGraph : AuthorityGraph where
  nodes := ["policy", "deployment"]
  edges := [{ fromNode := "policy", toNode := "deployment" }]
  overrides := []

def hiddenOverrideEffectiveGraph : AuthorityGraph where
  nodes := ["policy", "deployment"]
  edges := [{ fromNode := "policy", toNode := "deployment" }]
  overrides := [{ fromNode := "policy", toNode := "deployment" }]

noncomputable def hiddenOverrideObservation :
    GovernanceKernelizationObservation kernelizationExampleArtifact where
  reported := hiddenOverrideReportedGraph
  effective := hiddenOverrideEffectiveGraph
  sourceEdges := []
  reportedSemanticBridgeClean := true

def hiddenOverrideCertificate :
    HiddenAuthorityCertificate hiddenOverrideObservation :=
  HiddenAuthorityCertificate.hiddenOverride
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

theorem hiddenOverrideCertificate_minimal :
    MinimalHiddenAuthority hiddenOverrideCertificate := by
  dsimp [MinimalHiddenAuthority, hiddenOverrideCertificate]
  constructor
  · simp [AuthorityOverrideDifference, hiddenOverrideObservation,
      hiddenOverrideEffectiveGraph, hiddenOverrideReportedGraph]
  · change HiddenOverrideDominatesPair
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
    simp [HiddenOverrideDominatesPair, hiddenOverrideObservation,
      hiddenOverrideReportedGraph, HasAuthorityEdge]

noncomputable def sourceGapObservation :
    GovernanceKernelizationObservation kernelizationExampleArtifact where
  reported := cleanAuthorityGraph
  effective := cleanAuthorityGraph
  sourceEdges := []
  reportedSemanticBridgeClean := true

def sourceEvidenceGapCertificate :
    HiddenAuthorityCertificate sourceGapObservation :=
  HiddenAuthorityCertificate.sourceEvidenceGap
    { edge := { fromNode := "principal", toNode := "reviewer" }
      effective_has_edge := by
        left
        simp [sourceGapObservation, cleanAuthorityGraph, HasAuthorityEdge]
      source_lacks_edge := by
        simp [sourceGapObservation, SourceDerivesEdge] }

theorem sourceEvidenceGapCertificate_minimal :
    MinimalHiddenAuthority sourceEvidenceGapCertificate := by
  change
    HasAuthoritySurface sourceGapObservation.effective
        { fromNode := "principal", toNode := "reviewer" } ∧
      ¬ SourceEvidenceDerivable sourceGapObservation.sourceEdges
        { fromNode := "principal", toNode := "reviewer" }
  constructor
  · left
    simp [sourceGapObservation, cleanAuthorityGraph, HasAuthorityEdge]
  · rw [sourceEvidenceDerivable_iff]
    simp [sourceGapObservation, SourceDerivesEdge]

theorem sourceGap_not_clean :
    ¬ KernelizationClean sourceGapObservation := by
  intro hclean
  have hsource := hclean.2.1
    { fromNode := "principal", toNode := "reviewer" }
    (by
      left
      simp [sourceGapObservation, cleanAuthorityGraph, HasAuthorityEdge])
  simp [sourceGapObservation, SourceDerivesEdge] at hsource

end Safety

end Legitimacy
