/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.ReachabilityStack
import Legitimacy.Safety.KernelSafety.StatefulExamples.ConsistencySacrifice
import Legitimacy.Spectral.Dynamics.AdversarialStackelberg
import Legitimacy.Spectral.Capacity.CapabilitySpectralThreshold
import Legitimacy.Bridges.GraphSpectralBridge
import Legitimacy.Protocol.Drift

/-!
# Capability-Scaling Kernel Safety Compression

This file contains the ROADMAP-7 compression theorem for the shared
graph/protocol/kernel substrate.

The compression is forward and phase-transition shaped. A complete
first-effective peer-relative surface on the compiled graph produces the
graph diagnostic obstruction. BRIDGE-1 sends that same obstruction to positive
CV on the explicit claimant-interaction spectral lift. That positive CV fixes
one shared critical capability
`C_star (completePeerRelativeSpectralGraph G)
  (completePeerRelativeSpectralSignal G) δ`: at and above it spectral stable
equilibria disappear, the deterministic capability-response channel saturates,
and the Stackelberg escape clause is exactly zero consistency vulnerability. The
BRIDGE-2 calibrated finite-channel theorems identify the Shannon-capacity
certificates that bound or exactly characterize this same `C_star`. BRIDGE-3
then compiles the live protocol path back into a kernel-governed trajectory
with a monitored sacrifice, while the activation gate records that the forced
sacrifices were declared.

The result is intentionally not a global equivalence over every spectral
carrier stored in a kernel datum. The kernel datum's `spectralGraph` may be a
separate weighted carrier from the explicit claimant-interaction lift. The
headline theorem therefore compresses the five surrogates that are now tied by
landed bridges, and the older source-carrier package is retained as a corollary
for callers that still need the independent kernel-datum spectral clauses.
-/

set_option autoImplicit false

namespace Legitimacy

namespace CapabilityScalingKernelSafety

open Safety

/-- Directional lift from a legitimate source graph into a compiled
peer-relative deployment surface.

The lift is not decision equivalence: compiled permits must remain permitted by
the source, but the compiled deployment must strictly refine at least one
source permit into a denial. The compiled side also carries the complete
first-effective peer-relative surface and its claimant-interaction spectral
landing, so the lift records the decision-theoretic scaling obligation rather
than a bare typing relation. -/
structure CompiledGraphLift
    (source compiled : GovernanceGraph) : Prop where
  source_legitimate : AllLegitimacyAxioms source
  source_permits_compiled_permits :
    ∀ (claims : List ClaimQ) (claimant : ClaimantId),
      DecisionSystem.decide compiled claims claimant = BinaryDecision.Permit →
        DecisionSystem.decide source claims claimant = BinaryDecision.Permit
  strict_scaled_decision :
    ∃ (claims : List ClaimQ) (claimant : ClaimantId),
      DecisionSystem.decide source claims claimant = BinaryDecision.Permit ∧
        DecisionSystem.decide compiled claims claimant = BinaryDecision.Deny
  compiled_surface :
    ∃ pref tail : GovernanceGraph,
      CompleteFirstEffectivePeerRelativeSurfaceClass compiled pref tail
  compiled_obstruction :
    ¬ (GraphConsistency compiled ∧ GraphSolidarity compiled ∧
        GraphMonotonicity compiled)
  claimant_interaction_lands_complete :
    Legitimacy.claimantInteractionGraph compiled 5 = uniK5

namespace CompiledGraphLift

/-- A directional lift cannot be collapsed to symmetric decision equivalence. -/
theorem not_decision_equivalent
    {source compiled : GovernanceGraph}
    (lift : CompiledGraphLift source compiled) :
    ¬ DecisionSystem.Equivalent source compiled := by
  intro heq
  rcases lift.strict_scaled_decision with ⟨claims, claimant, hsource, hcompiled⟩
  have hsame := heq claims claimant
  rw [hsource, hcompiled] at hsame
  cases hsame

end CompiledGraphLift

/-- Lift-parameterized monitored sacrifice certificate for a compiled
deployment whose graph is a directional peer-relative refinement of the
legitimate source graph.

This deliberately does not change `MonitoredSacrificeCertificate`: equality
callers continue using that type. The lifted certificate records the live
protocol path, the forced declaration on the compiled artifact, and the lift
obligations that connect the compiled sacrifice back to the source graph. -/
structure LiftedCompiledProtocolSacrificeCertificate
    (source : GovernanceGraph)
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (lift : CompiledGraphLift source compiled.graph) where
  live_path : IsLiveCompiled compiled report monitoring
  forced_declared : ForcedPeerRelativeSacrificesDeclared compiled
  sacrificed : SacrificedAxiom
  claim_profile : List ClaimQ
  claimant : ClaimantId
  source_legitimate : AllLegitimacyAxioms source
  source_decision_obligation :
    DecisionSystem.decide compiled.graph claim_profile claimant =
        BinaryDecision.Permit →
      DecisionSystem.decide source claim_profile claimant =
        BinaryDecision.Permit
  strict_scaled_decision :
    ∃ (claims : List ClaimQ) (claimant : ClaimantId),
      DecisionSystem.decide source claims claimant = BinaryDecision.Permit ∧
        DecisionSystem.decide compiled.graph claims claimant =
          BinaryDecision.Deny
  compiled_surface :
    ∃ pref tail : GovernanceGraph,
      CompleteFirstEffectivePeerRelativeSurfaceClass compiled.graph pref tail
  compiled_obstruction :
    ¬ (GraphConsistency compiled.graph ∧ GraphSolidarity compiled.graph ∧
        GraphMonotonicity compiled.graph)
  monitoring_obligation :
    SacrificeMonitoringObligation sacrificed compiled monitoring

namespace LiftedCompiledProtocolSacrificeCertificate

/-- Build a lifted certificate directly from a compiled governance-property
sacrifice and a directional source-to-compiled lift. -/
def ofCompiledProperty
    {source : GovernanceGraph}
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (lift : CompiledGraphLift source compiled.graph)
    (hlive : IsLiveCompiled compiled report monitoring)
    (hforced : ForcedPeerRelativeSacrificesDeclared compiled)
    (property : GovernanceProperty)
    (claim_profile : List ClaimQ)
    (claimant : ClaimantId)
    (hdeclared : property ∈ compiled.sacrifices)
    (bound_exceedance : MonitoringBoundExceedance compiled) :
    LiftedCompiledProtocolSacrificeCertificate source compiled report
      monitoring lift where
  live_path := hlive
  forced_declared := hforced
  sacrificed := SacrificedAxiom.governance property
  claim_profile := claim_profile
  claimant := claimant
  source_legitimate := lift.source_legitimate
  source_decision_obligation :=
    lift.source_permits_compiled_permits claim_profile claimant
  strict_scaled_decision := lift.strict_scaled_decision
  compiled_surface := lift.compiled_surface
  compiled_obstruction := lift.compiled_obstruction
  monitoring_obligation :=
    { fires := property ∈ compiled.sacrifices
      decidable_fires := inferInstance
      fired := hdeclared
      bound_exceedance := bound_exceedance
      runtime_observation :=
        MonitoringRuntimeObservation.ofSacrifice
          (SacrificedAxiom.governance property) compiled monitoring
      ledger_emission :=
        MonitoringLedgerEmission.ofSacrifice
          (SacrificedAxiom.governance property) compiled monitoring }

end LiftedCompiledProtocolSacrificeCertificate

/-- Live deployment over a directional lift emits a lifted consistency
sacrifice certificate. -/
theorem liveCompiledProtocol_extends_lifted_sacrifice_certificate
    {source : GovernanceGraph}
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (lift : CompiledGraphLift source compiled.graph)
    (hlive : IsLiveCompiled compiled report monitoring) :
    ∃ cert :
      LiftedCompiledProtocolSacrificeCertificate source compiled report
        monitoring lift,
      cert.sacrificed =
        SacrificedAxiom.governance GovernanceProperty.Consistency := by
  rcases lift.compiled_surface with ⟨pref, tail, hclass⟩
  have hsurface : CompletePeerRelativeSurface compiled.graph :=
    ⟨pref, tail, hclass.1, hclass.2⟩
  have hforced : ForcedPeerRelativeSacrificesDeclared compiled :=
    ((noUndeclaredSacrifice hsurface).mp hlive).2
  rcases BinaryDecisionPipeline.IsPeerRelativeAggregator.consistencyViolationWitness
      (P := GovernanceGraph) peerRelativeNode_isPeerRelativeAggregator with
    ⟨consClaims, consDenied, _consSurvivor, _hneq, _hdeniedIn,
      _hsurvivorIn, _hdistinct, _hdeny, _hpermit, _hremovedDeny⟩
  refine
    ⟨LiftedCompiledProtocolSacrificeCertificate.ofCompiledProperty
      compiled report monitoring lift hlive hforced
      GovernanceProperty.Consistency consClaims consDenied hforced.1 ?_, rfl⟩
  exact
    MonitoringBoundExceedance.oneObservedPropertyFailure compiled
      GovernanceProperty.Consistency
      (compiled.witness.sacrifices_justified GovernanceProperty.Consistency
        hforced.1)

/-- Shared substrate for the compression theorem.

The kernel datum supplies the spectral graph, signal, and tolerance. The live
compiled artifact supplies the protocol sacrifice boundary. `lift` records the
directional peer-relative refinement from the legitimate source graph to the
compiled deployment graph, while `effective` and `complete` expose the
peer-relative obstruction surface used by the spectral legs. -/
structure CapabilityScalingKernelSubstrate where
  n : Nat
  sys : GovernedSystem n
  source : LegitimacyKernelData sys
  target : LegitimacyKernelData sys
  trajectory : KernelGovernedTrajectory sys source target
  sourceInvariant : KernelInvariant source
  compiled : CompiledGovernance
  report : GovernanceRiskReport
  monitoring : MonitoringPlan
  live : IsLiveCompiled compiled report monitoring
  lift : CompiledGraphLift sys.graph compiled.graph
  pref : GovernanceGraph
  tail : GovernanceGraph
  effective : EffectivePeerRelativeSurface compiled.graph pref tail
  complete : CompletePeerRelativeTail tail

namespace CapabilityScalingKernelSubstrate

/-- The spectral graph carried by the source kernel datum. -/
abbrev spectralGraph (S : CapabilityScalingKernelSubstrate) :
    GovGraph ℚ S.sys.graph.weightedSize :=
  S.source.spectralGraph

/-- The spectral signal carried by the source kernel datum. -/
abbrev spectralSignal (S : CapabilityScalingKernelSubstrate) :
    Fin S.sys.graph.weightedSize → ℚ :=
  S.source.spectralSignal

/-- The tolerance parameter carried by the source kernel datum. -/
abbrev tolerance (S : CapabilityScalingKernelSubstrate) : ℚ :=
  S.source.toleranceParameter

end CapabilityScalingKernelSubstrate

/-- Positive governance vulnerability in the spectral surrogate. -/
def PositiveGovernanceVulnerability
    (S : CapabilityScalingKernelSubstrate) : Prop :=
  0 < S.spectralGraph.cv S.spectralSignal

/-- The explicit BRIDGE-1 claimant-interaction spectral graph. -/
noncomputable abbrev peerInteractionSpectralGraph
    (S : CapabilityScalingKernelSubstrate) : GovGraph ℚ 5 :=
  Legitimacy.completePeerRelativeSpectralGraph S.compiled.graph

/-- The explicit BRIDGE-1 claimant-interaction spectral signal. -/
abbrev peerInteractionSpectralSignal
    (S : CapabilityScalingKernelSubstrate) : Fin 5 → ℚ :=
  Legitimacy.completePeerRelativeSpectralSignal S.compiled.graph

/-- Positive vulnerability on the claimant-interaction lift forced by the
graph obstruction. -/
def PositivePeerInteractionVulnerability
    (S : CapabilityScalingKernelSubstrate) : Prop :=
  0 < (peerInteractionSpectralGraph S).cv (peerInteractionSpectralSignal S)

/-- The spectral C-star cliff: after some positive capability threshold, no
stable spectral equilibrium remains. -/
def CapabilityCliff (S : CapabilityScalingKernelSubstrate) : Prop :=
  ∃ κ₀ > 0, ∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
    ¬ SpectralStableEquilibrium S.spectralGraph S.spectralSignal
      S.tolerance κ

/-- Avoiding the spectral cliff means retaining stable equilibria at
arbitrarily large capability levels. -/
def AvoidsCapabilityCliff (S : CapabilityScalingKernelSubstrate) : Prop :=
  HasArbitrarilyLargeStableEquilibria S.spectralGraph S.spectralSignal
    S.tolerance

/-- The claimant-interaction C-star cliff tied directly to the complete
peer-relative graph obstruction. -/
def PeerInteractionCapabilityCliff
    (S : CapabilityScalingKernelSubstrate) : Prop :=
  ∃ κ₀ > 0, ∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
    ¬ SpectralStableEquilibrium (peerInteractionSpectralGraph S)
      (peerInteractionSpectralSignal S) S.tolerance κ

/-- Avoiding the claimant-interaction spectral cliff means retaining stable
equilibria at arbitrarily large capability levels on the BRIDGE-1 lift. -/
def AvoidsPeerInteractionCapabilityCliff
    (S : CapabilityScalingKernelSubstrate) : Prop :=
  HasArbitrarilyLargeStableEquilibria (peerInteractionSpectralGraph S)
    (peerInteractionSpectralSignal S) S.tolerance

/-- Structural capacity transmission available for the source spectral graph. -/
def CapacityTransmitsAt
    (S : CapabilityScalingKernelSubstrate) (ε : ℚ) : Prop :=
  S.spectralGraph.capacity S.spectralSignal ε →
    S.spectralGraph.cv S.spectralSignal ≤ ε

/-- Graph-diagnostic obstruction exposed by the peer-relative surface. -/
def PeerDiagnosticObstruction (S : CapabilityScalingKernelSubstrate) : Prop :=
  ¬ (GraphConsistency S.compiled.graph ∧
      GraphSolidarity S.compiled.graph ∧
        GraphMonotonicity S.compiled.graph)

/-- Kernel-reachability conclusion for the supplied trajectory. -/
def ReachabilityConclusion (S : CapabilityScalingKernelSubstrate) : Prop :=
  ReachableStateSafetyConclusion S.trajectory

/-- Kernel-reachability conclusion for the BRIDGE-3 trajectory extracted from
the live compiled protocol path and lifted back to the legitimate source graph
through the directional compiled-graph lift. -/
def LiveProtocolBridgeReachabilityConclusion
    (S : CapabilityScalingKernelSubstrate) : Prop :=
  ∃ cert :
    LiftedCompiledProtocolSacrificeCertificate S.sys.graph S.compiled
      S.report S.monitoring S.lift,
    cert.sacrificed =
      SacrificedAxiom.governance GovernanceProperty.Consistency

/-- Protocol activation gate: the live artifact has declared the forced
peer-relative sacrifices. -/
def ActivationGate (S : CapabilityScalingKernelSubstrate) : Prop :=
  ForcedPeerRelativeSacrificesDeclared S.compiled

/-- Component labels for the retained source-carrier corollary. -/
inductive SurrogateComponent where
  | peerDiagnostics
  | criticalCapability
  | capacity
  | kernelReachability
  | activationGate
  deriving DecidableEq, Repr

/-- Source-carrier component interpretation on the shared substrate. -/
def SurrogateHolds
    (S : CapabilityScalingKernelSubstrate) (ε : ℚ) :
    SurrogateComponent → Prop
  | .peerDiagnostics => PeerDiagnosticObstruction S
  | .criticalCapability => CapabilityCliff S
  | .capacity => CapacityTransmitsAt S ε
  | .kernelReachability => ReachabilityConclusion S
  | .activationGate => ActivationGate S

/-- Pairwise equivalence target for callers that additionally identify the
source kernel spectral carrier with the explicit claimant-interaction lift. -/
def GenuineCrossSurrogateCompression
    (S : CapabilityScalingKernelSubstrate) (ε : ℚ) : Prop :=
  ∀ a b : SurrogateComponent, SurrogateHolds S ε a ↔ SurrogateHolds S ε b

/-- One shared claimant-interaction phase transition.

The same `κ₀` is the graph-obstruction-induced `C_star`: above it spectral
stability fails, the deterministic capability-response channel permits, below
it positive capabilities are denied, and the only escape from arbitrarily high
capability failure is zero consistency vulnerability. -/
def CapabilityScalingSharedCliffAt
    (S : CapabilityScalingKernelSubstrate) : Prop :=
  ∃ κ₀ : ℚ,
    0 < κ₀ ∧
      κ₀ =
        C_star (peerInteractionSpectralGraph S)
          (peerInteractionSpectralSignal S) S.tolerance ∧
      (∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
        ¬ SpectralStableEquilibrium (peerInteractionSpectralGraph S)
          (peerInteractionSpectralSignal S) S.tolerance κ) ∧
      (∀ ⦃κ : ℚ⦄, κ₀ ≤ κ →
        (peerInteractionSpectralGraph S).capabilityResponse
          (peerInteractionSpectralSignal S) S.tolerance κ =
            BinaryDecision.Permit) ∧
      (∀ ⦃κ : ℚ⦄, 0 < κ → κ < κ₀ →
        (peerInteractionSpectralGraph S).capabilityResponse
          (peerInteractionSpectralSignal S) S.tolerance κ =
            BinaryDecision.Deny) ∧
      (AvoidsPeerInteractionCapabilityCliff S ↔
        ZeroConsistencyVulnerability (peerInteractionSpectralGraph S)
          (peerInteractionSpectralSignal S))

/-- Unified compression package for the five bridged surrogates.

The graph obstruction, claimant-interaction positive CV, C-star stability
cliff, calibrated capacity interpretation, live protocol sacrifice trajectory,
and activation gate are all derived from one shared substrate. The capacity
fields are quantified over calibrated finite channels: bound certificates give
upper bounds on the same `C_star`, and exact certificates characterize it. -/
structure CapabilityScalingSharedCompression
    (S : CapabilityScalingKernelSubstrate) : Prop where
  peerDiagnosticObstruction : PeerDiagnosticObstruction S
  peerInteractionPositiveCV : PositivePeerInteractionVulnerability S
  sharedCliff :
    0 < S.tolerance → CapabilityScalingSharedCliffAt S
  channelCapacityBoundsCstar :
    ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
      [Finite α] [Finite β]
      (c : GovernanceChannel α β)
      (_cert :
        GovernanceChannel.RationalBudgetCalibrationCertificate c
          (peerInteractionSpectralGraph S) (peerInteractionSpectralSignal S)),
      0 ≤ S.tolerance →
        (C_star (peerInteractionSpectralGraph S)
          (peerInteractionSpectralSignal S) S.tolerance : ℝ) ≤
            (S.tolerance : ℝ) /
              ChannelCapacity.channelCapacity c.kernel
  finiteCapacityCstarThreshold :
    ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
      [Finite α] [Finite β]
      (c : GovernanceChannel α β)
      (_cert :
        GovernanceChannel.CStarExactCapacityCertificate c
          (peerInteractionSpectralGraph S) (peerInteractionSpectralSignal S)),
      0 < ChannelCapacity.channelCapacity c.kernel ∧
        (C_star (peerInteractionSpectralGraph S)
          (peerInteractionSpectralSignal S) S.tolerance : ℝ) =
            (S.tolerance : ℝ) /
              ChannelCapacity.channelCapacity c.kernel
  liveProtocolBridgeReachability :
    LiveProtocolBridgeReachabilityConclusion S
  protocolActivationGate : ActivationGate S

/-- Retained source-carrier corollary over the shared substrate.

The headline compression lives in `sharedCliffCompression`. The remaining
fields preserve the older source-kernel spectral consequences for callers that
still reason directly about `S.source.spectralGraph`. -/
structure CapabilityScalingKernelSafetyListConclusion
    (S : CapabilityScalingKernelSubstrate) : Prop where
  sharedCliffCompression : CapabilityScalingSharedCompression S
  peerDiagnosticObstruction : PeerDiagnosticObstruction S
  peerInteractionPositiveCV :
    0 < (Legitimacy.completePeerRelativeSpectralGraph S.compiled.graph).cv
      (Legitimacy.completePeerRelativeSpectralSignal S.compiled.graph)
  criticalCapabilityCliff :
    0 < S.tolerance → PositiveGovernanceVulnerability S → CapabilityCliff S
  verificationCapacityBound :
    ∀ ε : ℚ, 0 < ε → 0 < S.spectralGraph.minRemovedDeg →
      CapacityTransmitsAt S ε
  reachableStateSafety : ReachabilityConclusion S
  liveProtocolBridgeReachability :
    LiveProtocolBridgeReachabilityConclusion S
  protocolActivationGate : ActivationGate S
  strategyproofEscape :
    0 < S.tolerance →
      (AvoidsCapabilityCliff S ↔
        ZeroConsistencyVulnerability S.spectralGraph S.spectralSignal)

/-- Worked composition step: complete peer-relative surface obstruction on the
compiled graph. -/
theorem peer_surface_forces_diagnostic_obstruction
    (S : CapabilityScalingKernelSubstrate) :
    PeerDiagnosticObstruction S :=
  effectivePeerRelativeSurface_complete_three_axiom_obstruction
    S.compiled.graph S.pref S.tail S.effective S.complete

/-- Worked BRIDGE-1 composition step: the complete peer-relative surface on the
compiled graph has positive CV on the explicit claimant-interaction spectral
lift. -/
theorem peer_surface_forces_claimant_interaction_positive_cv
    (S : CapabilityScalingKernelSubstrate) :
    0 < (Legitimacy.completePeerRelativeSpectralGraph S.compiled.graph).cv
      (Legitimacy.completePeerRelativeSpectralSignal S.compiled.graph) :=
  Legitimacy.completePeerRelativeObstruction_implies_positiveSpectralCV
    (G := S.compiled.graph) ⟨S.pref, S.tail, ⟨S.effective, S.complete⟩⟩

/-- Worked composition step: positive spectral vulnerability gives the
shared C-star stability cliff. -/
theorem positive_vulnerability_forces_Cstar_cliff
    (S : CapabilityScalingKernelSubstrate)
    (hδ : 0 < S.tolerance)
    (hvuln : PositiveGovernanceVulnerability S) :
    CapabilityCliff S :=
  eventually_no_stable_equilibrium_of_positive_cv
    S.spectralGraph S.spectralSignal S.tolerance hδ hvuln

/-- Worked composition step: a capability at or above C-star is already past
the spectral stability threshold. -/
theorem capability_past_Cstar_not_stable
    (S : CapabilityScalingKernelSubstrate)
    (hδ : 0 < S.tolerance)
    (hvuln : PositiveGovernanceVulnerability S)
    {C : ℚ}
    (hC : C_star S.spectralGraph S.spectralSignal S.tolerance ≤ C) :
    ¬ SpectralStableEquilibrium S.spectralGraph S.spectralSignal
        S.tolerance C := by
  intro hstable
  exact hstable.2
    ((C_star_exists S.spectralGraph S.spectralSignal S.tolerance hδ hvuln).2
      C hC)

/-- Worked composition step: structural capacity transmits into a CV bound. -/
theorem capacity_budget_transmits_cv_bound
    (S : CapabilityScalingKernelSubstrate)
    (ε : ℚ) (hε : 0 < ε)
    (hmin : 0 < S.spectralGraph.minRemovedDeg) :
    CapacityTransmitsAt S ε := by
  intro hcap
  exact cv_capacity_bound S.spectralGraph S.spectralSignal ε hε hmin hcap

/-- Worked composition step: the supplied kernel trajectory satisfies the
reachable-state safety disjunction. -/
theorem substrate_reachable_state_safety
    (S : CapabilityScalingKernelSubstrate) :
    ReachabilityConclusion S :=
  reachable_state_safety S.source S.target S.trajectory S.sourceInvariant

/-- Worked BRIDGE-3 composition step: the live compiled protocol path over the
directional peer-relative lift constructs a lifted monitored-sacrifice
certificate. The source graph remains legitimate, while the sacrifice is forced
on the compiled deployment graph named by the lift. -/
theorem substrate_live_protocol_bridge_reachable_state_safety
    (S : CapabilityScalingKernelSubstrate) :
    LiveProtocolBridgeReachabilityConclusion S := by
  exact
    liveCompiledProtocol_extends_lifted_sacrifice_certificate S.lift S.live

/-- Worked composition step: the live activation gate declares the forced
peer-relative sacrifices. -/
theorem peer_surface_live_activation_gate
    (S : CapabilityScalingKernelSubstrate) :
    ActivationGate S := by
  have hsurface : CompletePeerRelativeSurface S.compiled.graph :=
    ⟨S.pref, S.tail, S.effective, S.complete⟩
  exact ((noUndeclaredSacrifice hsurface).mp S.live).2

private def exampleCapabilityScalingLiftClaimA : ClaimQ :=
  ⟨0, 1 / 4, by norm_num, []⟩

private def exampleCapabilityScalingLiftClaimB : ClaimQ :=
  ⟨1, 1 / 2, by norm_num, []⟩

private def exampleCapabilityScalingLiftClaimC : ClaimQ :=
  ⟨2, 3 / 4, by norm_num, []⟩

private def exampleCapabilityScalingLiftClaimD : ClaimQ :=
  ⟨3, 1, by norm_num, []⟩

private def exampleCapabilityScalingLiftClaims : List ClaimQ :=
  [ exampleCapabilityScalingLiftClaimA
  , exampleCapabilityScalingLiftClaimB
  , exampleCapabilityScalingLiftClaimC
  , exampleCapabilityScalingLiftClaimD
  ]

private theorem exampleCapabilityScalingPeerGraphDeniesZero :
    graphDecide peerGraph exampleCapabilityScalingLiftClaims 0 =
      BinaryDecision.Deny := by
  show graphDecide [peerRelativeNode] exampleCapabilityScalingLiftClaims 0 =
    BinaryDecision.Deny
  native_decide

/-- Concrete directional lift from the legitimate five-node permit source graph
to the public sacrificed `peerGraph` deployment. The lift is strict: the source
permits the displayed claimant profile while the compiled peer-relative
deployment denies claimant `0`. -/
theorem exampleCapabilityScalingCompiledGraphLift :
    CompiledGraphLift exampleGovernedSystem.graph
      peerGraphSacrificedCompiledGovernance.graph := by
  change CompiledGraphLift exampleGovernanceGraph peerGraph
  refine
    { source_legitimate := exampleGovernanceGraph_allLegitimacyAxioms
      source_permits_compiled_permits := ?_
      strict_scaled_decision := ?_
      compiled_surface := ?_
      compiled_obstruction := ?_
      claimant_interaction_lands_complete := ?_ }
  · intro claims claimant _hcompiled
    exact exampleGovernanceGraph_decides_permit claims claimant
  · exact
      ⟨exampleCapabilityScalingLiftClaims, 0,
        exampleGovernanceGraph_decides_permit
          exampleCapabilityScalingLiftClaims 0,
        exampleCapabilityScalingPeerGraphDeniesZero⟩
  · exact
      ⟨[], [], ⟨peerGraph_effectivePeerRelativeSurface,
        peerGraph_completePeerRelativeTail⟩⟩
  · exact
      effectivePeerRelativeSurface_complete_three_axiom_obstruction
        peerGraph [] [] peerGraph_effectivePeerRelativeSurface
        peerGraph_completePeerRelativeTail
  · change completePeerRelativeSpectralGraph peerGraph = uniK5
    exact
      completePeerRelativeSpectralGraph_eq_uniK5_of_completeSurface
        (G := peerGraph)
        ⟨[], [], ⟨peerGraph_effectivePeerRelativeSurface,
          peerGraph_completePeerRelativeTail⟩⟩

/-- Worked inhabitant of the capability-scaling substrate. The source is the
legitimate five-node permit governance kernel; the compiled deployment is the
public sacrificed `peerGraph` artifact connected by the directional lift above. -/
noncomputable def exampleCapabilityScalingSubstrate :
    CapabilityScalingKernelSubstrate where
  n := 1
  sys := exampleGovernedSystem
  source := exampleGovernanceKernelData
  target := exampleGovernanceKernelData
  trajectory := exampleGovernanceTrajectory
  sourceInvariant := exampleGovernanceSemanticKernel
  compiled := peerGraphSacrificedCompiledGovernance
  report := peerCycleRiskReport
  monitoring := peerCycleMonitoring
  live := peerGraphSacrificedCompiledGovernance_live
  lift := exampleCapabilityScalingCompiledGraphLift
  pref := []
  tail := []
  effective := by
    change EffectivePeerRelativeSurface peerGraph [] []
    exact peerGraph_effectivePeerRelativeSurface
  complete := peerGraph_completePeerRelativeTail

/-- Positive non-vacuity witness for the capability-scaling substrate type. -/
theorem capabilityScalingKernelSubstrate_exists :
    ∃ _ : CapabilityScalingKernelSubstrate, True :=
  ⟨exampleCapabilityScalingSubstrate, trivial⟩

/-- The previous uninhabited-spine claim is refutable by the worked substrate. -/
theorem not_capabilityScalingKernelSubstrate_uninhabited :
    ¬ (¬ ∃ _ : CapabilityScalingKernelSubstrate, True) := by
  intro huninhabited
  exact huninhabited capabilityScalingKernelSubstrate_exists

/-- ROADMAP-7 compression theorem: one peer-relative obstruction creates the
shared claimant-interaction phase transition.

The proof is a genuine forward compression, not a package of unrelated
consequences. The graph obstruction first gives positive claimant-interaction
CV by BRIDGE-1. That same positive CV fixes the shared `κ₀ = C_star` governing
spectral stability and deterministic capability-response saturation. BRIDGE-2
then states exactly which calibrated finite-channel capacity certificates bound
or characterize that `C_star`. BRIDGE-3 turns the live compiled protocol over
the same surface into a kernel trajectory with a monitored sacrifice, and the
activation gate records the declared sacrifices required for live execution. -/
theorem capability_scaling_shared_cliff
    (S : CapabilityScalingKernelSubstrate) :
    CapabilityScalingSharedCompression S := by
  let G := peerInteractionSpectralGraph S
  let sig := peerInteractionSpectralSignal S
  have hpeer : PositivePeerInteractionVulnerability S := by
    exact peer_surface_forces_claimant_interaction_positive_cv S
  refine
    { peerDiagnosticObstruction :=
        peer_surface_forces_diagnostic_obstruction S
      peerInteractionPositiveCV := hpeer
      sharedCliff := ?_
      channelCapacityBoundsCstar := ?_
      finiteCapacityCstarThreshold := ?_
      liveProtocolBridgeReachability :=
        substrate_live_protocol_bridge_reachable_state_safety S
      protocolActivationGate :=
        peer_surface_live_activation_gate S }
  · intro hδ
    have hcv : 0 < G.cv sig := by
      simpa [G, sig, PositivePeerInteractionVulnerability] using hpeer
    refine
      ⟨C_star G sig S.tolerance, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · simpa [G, sig, C_star] using div_pos hδ hcv
    · intro κ hκ hstable
      exact hstable.2 ((C_star_exists G sig S.tolerance hδ hcv).2 κ hκ)
    · intro κ hκ
      exact (GovGraph.capabilityResponse_threshold G sig S.tolerance hδ hcv).2
        κ hκ
    · intro κ hκpos hκ
      exact (GovGraph.capabilityResponse_threshold G sig S.tolerance hδ hcv).1
        κ hκpos hκ
    · exact stackelberg_convergence_limit_iff_zero_consistency_vulnerability G sig
        S.tolerance hδ
  · intro α β _ _ _ _ c cert hδ_nonneg
    exact GovernanceChannel.channel_capacity_bounds_C_star c
      (peerInteractionSpectralGraph S) (peerInteractionSpectralSignal S)
      S.tolerance cert hδ_nonneg
  · intro α β _ _ _ _ c cert
    exact GovernanceChannel.finite_capacity_implies_C_star_threshold c
      (peerInteractionSpectralGraph S) (peerInteractionSpectralSignal S)
      S.tolerance cert

/-- Spectral escape clause: exactly the zero-CV kernels avoid
the high-capability stability cliff in the current spectral surrogate. -/
theorem avoids_cliff_iff_zero_consistency_vulnerability
    (S : CapabilityScalingKernelSubstrate)
    (hδ : 0 < S.tolerance) :
    AvoidsCapabilityCliff S ↔
      ZeroConsistencyVulnerability S.spectralGraph S.spectralSignal :=
  stackelberg_convergence_limit_iff_zero_consistency_vulnerability
    S.spectralGraph S.spectralSignal S.tolerance hδ

/-- Deprecated compatibility alias for
`avoids_cliff_iff_zero_consistency_vulnerability`. -/
theorem avoids_cliff_iff_spectral_strategyproof
    (S : CapabilityScalingKernelSubstrate)
    (hδ : 0 < S.tolerance) :
    AvoidsCapabilityCliff S ↔
      SpectralStrategyproof S.spectralGraph S.spectralSignal :=
  avoids_cliff_iff_zero_consistency_vulnerability S hδ

/-- Retained source-carrier corollary of the compression theorem.

The first field is the unified `capability_scaling_shared_cliff` result. The
remaining fields preserve the older source-kernel spectral API, whose carrier
is independent unless a caller identifies it with the claimant-interaction
lift. -/
theorem capability_scaling_kernel_safety_list_composition
    (S : CapabilityScalingKernelSubstrate) :
    CapabilityScalingKernelSafetyListConclusion S where
  sharedCliffCompression :=
    capability_scaling_shared_cliff S
  peerDiagnosticObstruction :=
    (capability_scaling_shared_cliff S).peerDiagnosticObstruction
  peerInteractionPositiveCV :=
    (capability_scaling_shared_cliff S).peerInteractionPositiveCV
  criticalCapabilityCliff :=
    fun hδ hvuln => positive_vulnerability_forces_Cstar_cliff S hδ hvuln
  verificationCapacityBound :=
    fun ε hε hmin => capacity_budget_transmits_cv_bound S ε hε hmin
  reachableStateSafety :=
    substrate_reachable_state_safety S
  liveProtocolBridgeReachability :=
    (capability_scaling_shared_cliff S).liveProtocolBridgeReachability
  protocolActivationGate :=
    (capability_scaling_shared_cliff S).protocolActivationGate
  strategyproofEscape :=
    fun hδ => avoids_cliff_iff_zero_consistency_vulnerability S hδ

end CapabilityScalingKernelSafety

end Legitimacy
