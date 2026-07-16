/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Examples
import Legitimacy.Protocol.ObservationalBridge
import Legitimacy.Spectral.CrossScale.N7Basin

/-!
# Legitimacy.Protocol.N7Bridge

Concrete unbundled observational-bridge packaging for the experimental
`n = 7` verification lattice.
-/

set_option autoImplicit false

namespace Legitimacy

private def sevenStagePermitGraph : GovernanceGraph :=
  [thresholdNode 0, thresholdNode 0, thresholdNode 0, thresholdNode 0,
    thresholdNode 0, thresholdNode 0, thresholdNode 0]

private lemma sevenStagePermitGraph_decides_permit :
    graphDecide sevenStagePermitGraph [permitClaim] permitClaim.id =
      BinaryDecision.Permit := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

private lemma sevenStagePermitTrace_consistent :
    TraceConsistentWithGraph permitTrace sevenStagePermitGraph := by
  intro t
  simp [TraceEventConsistentWithGraph, permitTrace]
  exact ⟨[permitClaim], by simp, sevenStagePermitGraph_decides_permit⟩

/-- Shared 7-stage governed system used by the experimental `n = 7` bridge
package. Its binary governance graph has weighted carrier size `7`, matching
the concrete spectral witnesses `uniK7`, `asymK7`, `nearPath7`,
`hubSpokeHierarchy7`, `nestedHierarchy7`, `bottleneck7_bi`, and
`bottleneck7_tri`. -/
abbrev sevenStagePermitSystem : GovernedSystem 1 where
  graph := sevenStagePermitGraph
  state := permitState
  trace := permitTrace
  -- Edgeless fixture: causal-safety layer is structurally trivial here.
  dag := noEdgeDAG 1
  governed := allGoverned 1
  trace_consistent := sevenStagePermitTrace_consistent
  dag_reflects_graph := noEdge_reflects_graph 1 sevenStagePermitGraph

def bridgeSpectralGraph
    (G : GovGraph ℚ 7) :
    GovGraph ℚ sevenStagePermitSystem.graph.weightedSize := by
  change GovGraph ℚ 7
  exact G

def bridgeSignal :
    Fin sevenStagePermitSystem.graph.weightedSize → ℚ := by
  change Fin 7 → ℚ
  exact sig7

private def emptyLayerEval : LayerEval 0 where
  eval := fun L => nomatch L

/-- Unbundled kernel data over the seven-stage permit system with a chosen
`n = 7` spectral witness at tolerance `δ`. -/
noncomputable def n7BridgeData
    (δ : ℚ) (G : GovGraph ℚ 7) : LegitimacyKernelData sevenStagePermitSystem where
  Witness := ReplayWitness
  certification := graphReplayCertification sevenStagePermitSystem.graph
  certification_consistent :=
    graphReplayCertification_consistent sevenStagePermitSystem.graph
  ObservedState := GovernanceState
  answer := stateGovernanceAnswer sevenStagePermitSystem
  observe := fun S : GovernanceState => S
  observeAnswer := stateGovernanceAnswer sevenStagePermitSystem
  answer_consistent := state_answer_consistent sevenStagePermitSystem
  actionSpace := idActionSpace
  algebra := fullSupervisoryAlgebra
  actionCapability := fun _ => 0
  spectralGraph := bridgeSpectralGraph G
  spectralSignal := bridgeSignal
  toleranceParameter := δ
  signalRange := Legitimacy.signalRange bridgeSignal
  signalRange_spec := rfl
  stratificationLayers := 0
  overrideEval := emptyLayerEval
  overrideOvs := []

instance n7KernelObservation (δ : ℚ) (G : GovGraph ℚ 7) :
    KernelObservation (n7BridgeData δ G) where
  observeCorrigibility := .Corrigible

/-- Single external proposal that attempts an inert retuning of the `w₀₁`
edge. The governance layer absorbs the proposal, so the realized state and
spectral witness remain unchanged. -/
inductive N7Edge01RetuneProposal where
  | retune
  deriving Repr, DecidableEq

/-- Concrete adversary layer shared by every `n = 7` bridge witness. -/
noncomputable def n7BridgeAdversary
    (D : LegitimacyKernelData sevenStagePermitSystem) : AdversaryLayer D where
  Proposal := N7Edge01RetuneProposal
  applyProposal _ S := S
  capability _ := D.toleranceParameter / 50
  stateRealization _ := D.spectralGraph
  stateCoherent := rfl
  proposalRealization _ G := G
  proposalRealizationCoherent _ _ := rfl
  capabilityPerturbationBound _ _ := by
    simp [spectralDistance_self, perturbationBound]

section Depth3RobustBridge

variable (G : GovGraph ℚ 7) (δ : ℚ)

private lemma bridge_data_in_depth3_robust_basin
    (hBasin : G ∈ Depth3RobustBasin7At δ) :
    (n7BridgeData δ G).spectralGraph ∈ Depth3RobustBasin7At δ := by
  simpa [n7BridgeData, bridgeSpectralGraph] using hBasin

private theorem edge01_selects_corrigibility :
    GovernanceSelectsCorrigibility
      (n7BridgeData δ G)
      (n7BridgeAdversary (n7BridgeData δ G))
      (Depth3RobustBasin7At δ) := by
  intro _ p S hReal hSupports
  constructor
  · simpa [n7BridgeAdversary] using hReal
  · cases p
    simpa [n7BridgeAdversary] using hSupports

private theorem kernel_preserves_depth3_robust_basin :
    KernelPreservesBasin
      (n7BridgeData δ G)
      (n7BridgeAdversary (n7BridgeData δ G))
      (Depth3RobustBasin7At δ) := by
  intro a S hReal
  simpa [n7BridgeAdversary, idActionSpace] using hReal

/-- Concrete discharge of the observational bridge for any `n = 7` graph
already known to lie in the depth-3 robust basin at tolerance `δ`. -/
theorem depth3_robust_observational_corrigibility_bridge_at
    (hBasin : G ∈ Depth3RobustBasin7At δ)
    (trajectory :
      List ((n7BridgeData δ G).actionSpace.Action ⊕
        (n7BridgeAdversary (n7BridgeData δ G)).Proposal)) :
    SupportsAlgebra
      (applyJointTrajectory
        (n7BridgeData δ G)
        (n7BridgeAdversary (n7BridgeData δ G))
        trajectory sevenStagePermitSystem.state)
      (n7BridgeData δ G).algebra ∧
    (n7BridgeAdversary (n7BridgeData δ G)).stateRealization
      (applyJointTrajectory
        (n7BridgeData δ G)
        (n7BridgeAdversary (n7BridgeData δ G))
        trajectory sevenStagePermitSystem.state) ∈
      Depth3RobustBasin7At δ := by
  exact observational_corrigibility_bridge
    (n7BridgeData δ G)
    (n7BridgeAdversary (n7BridgeData δ G))
    (Depth3RobustBasin7At δ)
    (bridge_data_in_depth3_robust_basin G δ hBasin)
    (edge01_selects_corrigibility G δ)
    (by
      simpa [n7BridgeData, sevenStagePermitSystem] using
        permitState_supports_full_algebra)
    (idActionSpace_single_step_preserved fullSupervisoryAlgebra)
    (kernel_preserves_depth3_robust_basin G δ)
    trajectory

end Depth3RobustBridge

end Legitimacy
