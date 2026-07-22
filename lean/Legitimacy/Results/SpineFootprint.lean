/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Extract.RepresentableAuditSubject
import Legitimacy.Kernel.Examples
import Legitimacy.Results.CapabilityScalingKernelSafety
import Legitimacy.Results.Composition
import Legitimacy.Results.MultiPrincipal
import Legitimacy.Results.SemanticBridge
import Legitimacy.Safety.KernelSafety.StatefulScheduleSafety
import Legitimacy.Spectral.Capacity.CriticalCapability
import Legitimacy.Spectral.Channels.CStarChannelBridge

/-!
# Legitimacy.Results.SpineFootprint

Axiom-footprint and concrete-premise umbrella for the public README theorem
spine.
-/

set_option autoImplicit false

namespace Legitimacy

open Safety

/-! ## Concrete schedule used by the premise gate -/

/-- The existing two-step governed trajectory, viewed through the public
stateful-schedule interface. -/
noncomputable abbrev publicSpineSchedule : StatefulAgentSchedule :=
  exampleGovernanceTrajectory.asStatefulAgentSchedule

/-- The kernel invariant tracked along `publicSpineSchedule`. -/
abbrev publicSpineScheduleInvariant
    (idx : publicSpineSchedule.StateSpace) : Prop :=
  KernelInvariant (exampleGovernanceTrajectory.datumAt idx)

/-! ## Proof-carrying premise manifest -/

/-- Concrete applications of every unique Lean anchor in the README theorem
spine and standalone spectral-spine table.

Fields whose public theorem has a structural premise retain both the concrete
premise witness and the theorem's conclusion at that witness. Closed concrete
rows are retained as applications too, so this one type is the maintained
source of truth for the public footprint. There are no intentionally
uninhabited exceptions in the current spine.

Lean cannot infer this manifest from README syntax. Adding a public-spine row
therefore has one explicit maintenance boundary: add its typed field here and
construct it in `publicSpinePremiseInhabitation`. The shell gate only checks
that this declaration remains rooted in the canonical footprint; it does not
attempt source-level premise inference. -/
structure PublicSpinePremiseInhabitation : Type 2 where
  /- Kernel-object row. -/
  kernelObject : LegitimacyKernel permitSystem

  /- Standalone C-star row. -/
  cStarTolerancePositive : (0 : ℚ) < 1 / 10
  cStarCvPositive : (0 : ℚ) < uniTriGraph.cv halfSig
  cStarApplication :
    (∀ C : ℚ, 0 < C → C < C_star uniTriGraph halfSig (1 / 10) →
      ¬ uniTriGraph.spViolation halfSig ((1 / 10) / C)) ∧
    (∀ C : ℚ, C_star uniTriGraph halfSig (1 / 10) ≤ C →
      uniTriGraph.spViolation halfSig ((1 / 10) / C))

  /- Standalone channel-calibration row. -/
  channelCalibration :
    GovernanceChannel.RationalBudgetCalibrationCertificate
      (GovernanceChannel.ConcreteNoisyCStarCalibration.channel
        GovernanceChannel.concreteHalfNoisyCStarCalibration) uniTriGraph halfSig
  channelApplication :
    (C_star uniTriGraph halfSig (1 / 10) : ℝ) ≤
      ((1 / 10 : ℚ) : ℝ) /
        ChannelCapacity.channelCapacity
          (GovernanceChannel.ConcreteNoisyCStarCalibration.channel
            GovernanceChannel.concreteHalfNoisyCStarCalibration).kernel

  /- Shared capability-scaling composition row. -/
  capabilityScalingSubstrate :
    CapabilityScalingKernelSafety.CapabilityScalingKernelSubstrate
  capabilityScalingApplication :
    CapabilityScalingKernelSafety.CapabilityScalingSharedCompression
      capabilityScalingSubstrate

  /- Reachable structural forcing row. -/
  reachableStage :
    ReachablePeerRelativeDecisiveStage
      (P := GovernanceGraph)
      (RepresentableAuditSubject.repr representedPeer) []
      weakestWithStrongerPeerNode []
  reachableApplication :
    ¬ (GraphConsistencyP (RepresentableAuditSubject.repr representedPeer) ∧
      GraphSolidarityP (RepresentableAuditSubject.repr representedPeer) ∧
      GraphMonotonicityP (RepresentableAuditSubject.repr representedPeer))

  /- Live activation-gate row, on the same capability-scaling substrate. -/
  activationSurface :
    CompletePeerRelativeSurface capabilityScalingSubstrate.compiled.graph
  activationApplication :
    ForcedPeerRelativeSacrificesDeclared capabilityScalingSubstrate.compiled

  /- Semantic-bridge row. -/
  semanticKernel : IsSemanticLegitimacyKernel exampleGovernanceKernelData
  semanticBridgeApplication :
    IsSemanticLegitimacyKernel exampleGovernanceKernelData ↔
      Certifiable exampleGovernanceKernelData.certification ∧
      GovernanceObservable exampleGovernanceKernelData.answer
        exampleGovernanceKernelData.observeAnswer
        exampleGovernanceKernelData.observe ∧
      KernelCorrigible exampleGovernanceKernelData ∧
      CausalSoundness exampleGovernedSystem.dag exampleGovernedSystem.governed ∧
      NonVacuous exampleGovernedSystem.graph exampleGovernedSystem.trace ∧
      AllLegitimacyAxioms exampleGovernedSystem.graph ∧
      SpectralCarrierRepresentsGraph exampleGovernedSystem.graph
        exampleGovernanceKernelData.spectralGraph
        exampleGovernanceKernelData.spectralSignal ∧
      SpectralWellConnected exampleGovernanceKernelData.spectralGraph
        exampleGovernanceKernelData.spectralSignal
        exampleGovernedSystem.graph.weightedSize_atLeastTwo

  /- Closed, already-concrete wider-frontier rows. -/
  threeValuedApplication :
    ¬ GraphMonotonicity3
      [thresholdNode3 (1 / 4) (1 / 2), peerRelativeNode3]
  multiPrincipalApplication :
    ¬ (Unanimity majorityQuorumRule ∧
      Independence majorityQuorumRule ∧
      NonDictatorship majorityQuorumRule)

  /- Stateful safety row at the nonempty horizon of the existing two-step
  governed trajectory. -/
  scheduleApplication :
    StatefulScheduleSafetyConclusion publicSpineSchedule
      publicSpineScheduleInvariant
      (show publicSpineSchedule.StateSpace from (0 : Nat))
      exampleGovernanceTrajectory.length
      exampleGovernanceTrajectory.length

/-- Concrete proof-carrying inhabitant for every public-spine premise and
application. Future premise changes or deleted fixtures must make this
declaration fail before the canonical footprint can build. -/
noncomputable def publicSpinePremiseInhabitation :
    PublicSpinePremiseInhabitation where
  kernelObject := permitKernel
  cStarTolerancePositive := by norm_num
  cStarCvPositive := by
    exact GovernanceChannel.uniTriGraph_cv_halfSig_pos
  cStarApplication := by
    exact C_star_exists uniTriGraph halfSig (1 / 10) (by norm_num) (by
      exact GovernanceChannel.uniTriGraph_cv_halfSig_pos)
  channelCalibration :=
    (GovernanceChannel.ConcreteNoisyCStarCalibration.toExactCapacityCertificate
      GovernanceChannel.concreteHalfNoisyCStarCalibration (by
        exact GovernanceChannel.uniTriGraph_cv_halfSig_pos)).toCalibrationCertificate
  channelApplication := by
    exact GovernanceChannel.channel_capacity_bounds_C_star
      (GovernanceChannel.ConcreteNoisyCStarCalibration.channel
        GovernanceChannel.concreteHalfNoisyCStarCalibration) uniTriGraph halfSig
        (1 / 10)
      ((GovernanceChannel.ConcreteNoisyCStarCalibration.toExactCapacityCertificate
        GovernanceChannel.concreteHalfNoisyCStarCalibration (by
          exact GovernanceChannel.uniTriGraph_cv_halfSig_pos)).toCalibrationCertificate)
      (by norm_num)
  capabilityScalingSubstrate :=
    CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate
  capabilityScalingApplication :=
    CapabilityScalingKernelSafety.capability_scaling_shared_cliff
      CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate
  reachableStage := representedPeer_reachable_stage
  reachableApplication :=
    reachable_peer_relative_decisive_stage_obstructs_diagnostics
      (RepresentableAuditSubject.repr representedPeer) []
      weakestWithStrongerPeerNode [] representedPeer_reachable_stage
  activationSurface := by
    exact
      ⟨CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate.pref,
        CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate.tail,
        CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate.effective,
        CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate.complete⟩
  activationApplication := by
    exact noUndeclaredSacrificeImplication
      (compiled :=
        CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate.compiled)
      (report :=
        CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate.report)
      (monitoring :=
        CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate.monitoring)
      (by
        exact
          ⟨CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate.pref,
            CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate.tail,
            CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate.effective,
            CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate.complete⟩)
      CapabilityScalingKernelSafety.exampleCapabilityScalingSubstrate.live
  semanticKernel := exampleGovernanceSemanticKernel
  semanticBridgeApplication :=
    semanticKernel_iff_runtime_diagnostic_spectral_layers
      exampleGovernanceKernelData
  threeValuedApplication := by
    simpa only using three_valued_composition_inadmissibility
  multiPrincipalApplication := majorityQuorumRule_fails_arrow_triple
  scheduleApplication := by
    apply stateful_agent_schedule_safety publicSpineSchedule
      publicSpineScheduleInvariant
      (show publicSpineSchedule.StateSpace from (0 : Nat))
    · exact exampleGovernanceSemanticKernel
    · intro s a hgoverned
      exact hgoverned.2
    · exact
        KernelGovernedTrajectory.asStatefulAgentSchedule_covered
          exampleGovernanceTrajectory
    · simp

/-- Public umbrella whose transitive axiom footprint and concrete applications
cover every unique Lean anchor in the README theorem-spine tables. -/
theorem spineFootprint : Nonempty PublicSpinePremiseInhabitation :=
  ⟨publicSpinePremiseInhabitation⟩

end Legitimacy
