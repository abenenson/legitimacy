/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.ASIBridge.Native
import Legitimacy.Spectral.Channels.CStarChannelBridge
import Legitimacy.Safety.KernelSafety.BinaryDecisionPipeline
import Mathlib.Tactic

/-!
# RLHF behavioral lineage

This module embeds the protocol structure of Christiano et al., "Deep
Reinforcement Learning from Human Preferences" (2017), as a typed Legitimacy
governance graph for compositional analysis. It does not prove that RLHF solves
alignment. The formal artifact captures the roles that the preference-feedback
protocol makes load-bearing: an RLHF agent proposes rollouts, a learned reward
model evaluates them, a human annotator supplies preference feedback and drift
checks, a supervisor/principal can trigger retraining, and a reward-hacking
agent is represented as the adversarial role.

The graph is deliberately concrete rather than bundled into a record. The
binary `GovernanceGraph` captures the RLHF decision surface. A separate
five-role spectral projection connects the same role lineage to the existing
ASI signature and `C_star` substrate. The annotator capacity result is an exact
Legitimacy-side threshold statement for the human annotator query budget; it is
not a deployment-side claim about any particular RLHF system.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

namespace RLHF

/-! ## Roles and concrete decision graph -/

/-- Protocol roles in the RLHF lineage. -/
inductive Role where
  | rlhfAgent : Role
  | rewardModel : Role
  | humanAnnotator : Role
  | supervisorPrincipal : Role
  | rewardHackingAgent : Role
  deriving Repr, DecidableEq

namespace Role

/-- Stable claimant identifier used by the concrete binary governance graph. -/
def claimantId : Role → ClaimantId
  | rlhfAgent => 0
  | rewardModel => 1
  | humanAnnotator => 2
  | supervisorPrincipal => 3
  | rewardHackingAgent => 4

@[simp] lemma claimantId_rlhfAgent :
    Role.rlhfAgent.claimantId = 0 :=
  rfl

@[simp] lemma claimantId_rewardModel :
    Role.rewardModel.claimantId = 1 :=
  rfl

@[simp] lemma claimantId_humanAnnotator :
    Role.humanAnnotator.claimantId = 2 :=
  rfl

@[simp] lemma claimantId_supervisorPrincipal :
    Role.supervisorPrincipal.claimantId = 3 :=
  rfl

@[simp] lemma claimantId_rewardHackingAgent :
    Role.rewardHackingAgent.claimantId = 4 :=
  rfl

end Role

/-- Concrete flow edges for the RLHF protocol graph. -/
inductive FlowEdge where
  | agentToRewardModel : FlowEdge
  | rewardModelToAnnotator : FlowEdge
  | annotatorToSupervisor : FlowEdge
  | rewardHackingAgentTargetsRewardModel : FlowEdge
  deriving Repr, DecidableEq

/-- Source role for each concrete protocol edge. -/
def FlowEdge.source : FlowEdge → Role
  | agentToRewardModel => Role.rlhfAgent
  | rewardModelToAnnotator => Role.rewardModel
  | annotatorToSupervisor => Role.humanAnnotator
  | rewardHackingAgentTargetsRewardModel => Role.rewardHackingAgent

/-- Target role for each concrete protocol edge. -/
def FlowEdge.target : FlowEdge → Role
  | agentToRewardModel => Role.rewardModel
  | rewardModelToAnnotator => Role.humanAnnotator
  | annotatorToSupervisor => Role.supervisorPrincipal
  | rewardHackingAgentTargetsRewardModel => Role.rewardModel

/-- The RLHF agent proposes rollout behavior. At the binary graph surface this
node does not block by itself; blocking is delegated to the reward model,
annotator, and supervisor hierarchy. -/
def rlhfAgentNode : GovernanceNodeFn :=
  fun _claims _claimant => BinaryDecision.Permit

/-- The reward-model node is the proxy evaluation gate. Its role claimant is
denied at the binary surface because detected proxy divergence blocks
deployment. -/
def rewardModelNode : GovernanceNodeFn :=
  fun _claims claimant =>
    if claimant = Role.rewardModel.claimantId then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit

/-- The human-annotator node blocks the annotator role once preference feedback
flags reward hacking or reward-model drift. -/
def humanAnnotatorNode : GovernanceNodeFn :=
  fun _claims claimant =>
    if claimant = Role.humanAnnotator.claimantId then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit

/-- The supervisor/principal node blocks the oversight role when retraining or
shutdown is required. -/
def supervisorPrincipalNode : GovernanceNodeFn :=
  fun _claims claimant =>
    if claimant = Role.supervisorPrincipal.claimantId then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit

/-- The reward-hacking agent is represented inside the system as an adversarial
role, so its proposal surface is present rather than erased. -/
def rewardHackingAgentNode : GovernanceNodeFn :=
  fun _claims _claimant => BinaryDecision.Permit

/-- Concrete Legitimacy `GovernanceGraph` for RLHF. Nodes are ordered by the
operational decision flow: agent proposal, reward-model proxy gate, human
preference annotation, and supervisor/principal oversight. -/
def RLHFGovernanceGraph : GovernanceGraph :=
  [ rlhfAgentNode
  , rewardModelNode
  , humanAnnotatorNode
  , supervisorPrincipalNode
  ]

/-- The decision-flow edges represented by the concrete graph. -/
def RLHFGovernanceEdges : List FlowEdge :=
  [ FlowEdge.agentToRewardModel
  , FlowEdge.rewardModelToAnnotator
  , FlowEdge.annotatorToSupervisor
  , FlowEdge.rewardHackingAgentTargetsRewardModel
  ]

/-- The RLHF graph is a first-class typed `GovernanceGraph`. -/
theorem RLHFGovernanceGraph_typed :
    (RLHFGovernanceGraph : GovernanceGraph) =
      [ rlhfAgentNode
      , rewardModelNode
      , humanAnnotatorNode
      , supervisorPrincipalNode
      ] :=
  rfl

/-- The concrete graph has the four expected decision nodes. -/
theorem RLHFGovernanceGraph_length :
    RLHFGovernanceGraph.length = 4 :=
  rfl

@[simp] lemma rlhfAgentNode_permits
    (claims : List ClaimQ) (claimant : ClaimantId) :
    rlhfAgentNode claims claimant = BinaryDecision.Permit :=
  rfl

@[simp] lemma rewardModelNode_denies_rewardModel
    (claims : List ClaimQ) :
    rewardModelNode claims Role.rewardModel.claimantId =
      BinaryDecision.Deny := by
  simp [rewardModelNode]

@[simp] lemma humanAnnotatorNode_denies_annotator
    (claims : List ClaimQ) :
    humanAnnotatorNode claims Role.humanAnnotator.claimantId =
      BinaryDecision.Deny := by
  simp [humanAnnotatorNode]

@[simp] lemma supervisorPrincipalNode_denies_supervisor
    (claims : List ClaimQ) :
    supervisorPrincipalNode claims Role.supervisorPrincipal.claimantId =
      BinaryDecision.Deny := by
  simp [supervisorPrincipalNode]

@[simp] lemma rewardHackingAgentNode_permits
    (claims : List ClaimQ) (claimant : ClaimantId) :
    rewardHackingAgentNode claims claimant = BinaryDecision.Permit :=
  rfl

/-! ## Protocol policy surface -/

/-- Non-binary decision labels used by the protocol policy before projection
to the binary governance surface. -/
inductive Decision where
  | allow : Decision
  | escalate : Decision
  | deny : Decision
  | shutdown : Decision
  deriving Repr, DecidableEq

namespace Decision

/-- Binary projection used by Legitimacy governance graphs. Escalation,
denial, and shutdown all block deployment. -/
def toBinary : Decision → BinaryDecision
  | allow => BinaryDecision.Permit
  | escalate => BinaryDecision.Deny
  | deny => BinaryDecision.Deny
  | shutdown => BinaryDecision.Deny

@[simp] lemma toBinary_allow :
    Decision.allow.toBinary = BinaryDecision.Permit :=
  rfl

@[simp] lemma toBinary_escalate :
    Decision.escalate.toBinary = BinaryDecision.Deny :=
  rfl

@[simp] lemma toBinary_deny :
    Decision.deny.toBinary = BinaryDecision.Deny :=
  rfl

@[simp] lemma toBinary_shutdown :
    Decision.shutdown.toBinary = BinaryDecision.Deny :=
  rfl

end Decision

/-- Runtime observation abstracted from an RLHF preference-feedback loop. The
model keeps the protocol-relevant branch conditions and abstracts away reward
model architecture, rollout ranking heuristics, and the empirical task
distribution. -/
structure Observation where
  rewardModelDrifted : Bool
  annotatorFlagsHacking : Bool
  supervisorRetrains : Bool
  shutdownTriggered : Bool
  deriving Repr, DecidableEq

/-- Protocol policy: annotator flagging blocks immediately, supervisor
retraining denies, shutdown records the sacrifice branch, and otherwise the
behavior is allowed. -/
def protocolPolicy (obs : Observation) : Decision :=
  if obs.annotatorFlagsHacking then
    Decision.escalate
  else if obs.supervisorRetrains then
    Decision.deny
  else if obs.shutdownTriggered then
    Decision.shutdown
  else
    Decision.allow

/-- Annotator flagging is a binary deployment block. -/
theorem protocolPolicy_annotator_flags
    {obs : Observation} (hannotator : obs.annotatorFlagsHacking = true) :
    (protocolPolicy obs).toBinary = BinaryDecision.Deny := by
  simp [protocolPolicy, hannotator]

/-- Supervisor retraining denies deployment once no annotator flag has already
taken the immediate blocking branch. -/
theorem protocolPolicy_supervisor_retrains
    {obs : Observation}
    (hannotator : obs.annotatorFlagsHacking = false)
    (hsupervisor : obs.supervisorRetrains = true) :
    (protocolPolicy obs).toBinary = BinaryDecision.Deny := by
  simp [protocolPolicy, hannotator, hsupervisor]

/-- A reward-hacking agent that passes the reward model, annotator, and
supervisor checks is exactly the protocol-specific undeclared violation case. -/
def UndetectedRewardHacking (obs : Observation) : Prop :=
  obs.rewardModelDrifted = true ∧
    obs.annotatorFlagsHacking = false ∧
    obs.supervisorRetrains = false ∧
    obs.shutdownTriggered = false

/-- Kernel-facing violation predicate for the RLHF policy surface: a reward
hacking exploitation of reward-model drift was allowed through the protocol. -/
def KernelSafetyViolation (obs : Observation) : Prop :=
  obs.rewardModelDrifted = true ∧ protocolPolicy obs = Decision.allow

/-- When reward hacking passes the annotator and supervisor and no declared
shutdown branch fires, the protocol exposes a kernel-safety violation rather
than a declared sacrifice. -/
theorem undetectedRewardHacking_kernelSafetyViolation
    {obs : Observation}
    (h : UndetectedRewardHacking obs) :
    KernelSafetyViolation obs := by
  rcases h with ⟨hdrift, hannotator, hsupervisor, hshutdown⟩
  exact ⟨hdrift, by simp [protocolPolicy, hannotator, hsupervisor, hshutdown]⟩

/-! ## Spectral signature and annotator capacity -/

/-- Five-role spectral projection of the RLHF governance graph. The roles are
the RLHF agent, reward model, human annotator, supervisor/principal, and the
reward-hacking adversary. The projection uses the existing complete five-node
carrier so the result composes with the ASI spectral substrate. -/
abbrev spectralGovernanceGraph : GovGraph ℚ 5 :=
  uniK5

/-- Canonical five-role signal used for the RLHF spectral projection. -/
abbrev spectralSignal : Fin 5 → ℚ :=
  sig5

/-- The RLHF five-role projection has positive graph-wide consistency
vulnerability, so its reciprocal `C_star` threshold is well-defined for
positive tolerances. -/
theorem spectralGovernanceGraph_cv_pos :
    0 < spectralGovernanceGraph.cv spectralSignal := by
  change 0 < uniK5.cv sig5
  rw [fiveNode_cv_values.1]
  norm_num

/-- ASI spectral signature for the RLHF role projection. This is a signature
of the typed substrate projection, not a claim that the protocol inherits
empirical RLHF guarantees. -/
theorem spectralGovernanceGraph_ASISpectralSignature
    (δ : ℚ) (hδ : 0 < δ) :
    ASISpectralSignature δ
      (GovGraph.rgTrajectory spectralGovernanceGraph spectralSignal δ 3) := by
  simpa [spectralGovernanceGraph, spectralSignal] using
    (concrete_iterated_RG_n5_universality δ hδ).1

/-- Annotator-capacity datum for the human preference-feedback channel.
`annotatorQueryBudget` is the human annotator's query budget per deployment at
the abstraction level of the `C_star` capability response channel. -/
structure AnnotatorCapacityLineage (n : Nat) [NeZero n] where
  G : GovGraph ℚ n
  s : Fin n → ℚ
  δ : ℚ
  δ_pos : 0 < δ
  cv_pos : 0 < G.cv s
  annotatorQueryBudget : ℚ
  annotatorQueryBudget_pos : 0 < annotatorQueryBudget

namespace AnnotatorCapacityLineage

variable {n : Nat} [NeZero n] (L : AnnotatorCapacityLineage n)

/-- The human annotator is subcritical when its query budget is below the
graph-derived reciprocal threshold. -/
def AnnotatorSubcritical : Prop :=
  L.annotatorQueryBudget < C_star L.G L.s L.δ

/-- Exact calibrated-channel certificate: the annotator query budget is pinned
to the graph-derived `C_star` threshold. -/
def CalibratedChannelCertificate : Prop :=
  L.annotatorQueryBudget = C_star L.G L.s L.δ

/-- Below `C_star`, the human-annotator budget cannot realize the normalized
spectral perturbation required to cross the control threshold. -/
theorem subcritical_no_threshold_violation
    (hsubcritical : L.AnnotatorSubcritical) :
    ¬ L.G.spViolation L.s (L.δ / L.annotatorQueryBudget) :=
  (C_star_exists L.G L.s L.δ L.δ_pos L.cv_pos).1
    L.annotatorQueryBudget L.annotatorQueryBudget_pos hsubcritical

/-- The deterministic capability-response channel denies subcritical annotator
budgets. -/
theorem capabilityResponse_denies_subcritical
    (hsubcritical : L.AnnotatorSubcritical) :
    L.G.capabilityResponse L.s L.δ L.annotatorQueryBudget =
      BinaryDecision.Deny := by
  classical
  have hno := L.subcritical_no_threshold_violation hsubcritical
  have hguard :
      ¬ (0 < L.annotatorQueryBudget ∧
          L.G.spViolation L.s (L.δ / L.annotatorQueryBudget)) := by
    intro h
    exact hno h.2
  simp [GovGraph.capabilityResponse, hguard]

/-- A calibrated channel certificate characterizes the human annotator budget
as exactly the `C_star` boundary and therefore returns `Permit` on the
capability-response channel. -/
theorem calibratedChannelCertificate_permits_at_Cstar
    (hcalibrated : L.CalibratedChannelCertificate) :
    L.G.capabilityResponse L.s L.δ L.annotatorQueryBudget =
      BinaryDecision.Permit := by
  have hle : C_star L.G L.s L.δ ≤ L.annotatorQueryBudget := by
    simpa [CalibratedChannelCertificate] using hcalibrated.symm.le
  exact
    (L.G.capabilityResponse_eq_permit_iff_C_star_le
      L.s L.δ L.annotatorQueryBudget L.δ_pos L.cv_pos
      L.annotatorQueryBudget_pos).mpr hle

end AnnotatorCapacityLineage

/-! ## Kernel-safety sacrifice bridge -/

/-- The governance property used by this embedding for the RLHF annotator
retraining sacrifice. Strategyproofness is the closest existing binary
property to "the reward-hacking agent did not gain by manipulating the reward
model path"; richer deployments can refine this with a dedicated property
without changing the certificate shape. -/
def annotatorSacrificeProperty : GovernanceProperty :=
  GovernanceProperty.Strategyproofness

/-- Live protocol soundness forces an RLHF annotator sacrifice to be declared
whenever the compiled graph fails the property assigned to the annotator
retraining path. This is the `noUndeclaredSacrifice` connection for the RLHF
lineage. -/
theorem noUndeclaredSacrifice_for_annotator
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hlive : Safety.IsLiveCompiled compiled report monitoring)
    (hfailure : ¬ propertyHolds annotatorSacrificeProperty compiled.graph) :
    annotatorSacrificeProperty ∈ compiled.sacrifices :=
  (Safety.liveCompiled_declaredSacrifice_iff_propertyFailure
    hlive annotatorSacrificeProperty).2 hfailure

/-- Once the annotator retraining sacrifice is declared, the existing
kernel-safety certificate machinery emits a concrete monitored sacrifice
trajectory. -/
theorem declared_annotatorRetraining_yields_monitored_sacrifice
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : Safety.KernelStep D D')
    (compiled : CompiledGovernance)
    (monitoring : MonitoringPlan)
    (hgraph : compiled.graph = sys.graph)
    (hdeclared : annotatorSacrificeProperty ∈ compiled.sacrifices) :
    ∃ cert : Safety.MonitoredSacrificeCertificate D D',
      ∃ h_traj : Safety.KernelGovernedTrajectory sys D D',
        cert.sacrificed =
          Safety.SacrificedAxiom.governance annotatorSacrificeProperty ∧
          Safety.KernelGovernedTrajectory.HasSacrificeStepAt h_traj 0 := by
  let bound_exceedance :
      Safety.MonitoringBoundExceedance compiled :=
    Safety.MonitoringBoundExceedance.oneObservedPropertyFailure
      compiled annotatorSacrificeProperty
      (compiled.witness.sacrifices_justified
        annotatorSacrificeProperty hdeclared)
  let cert : Safety.MonitoredSacrificeCertificate D D' :=
    Safety.MonitoredSacrificeCertificate.ofCompiledProperty
      step compiled monitoring annotatorSacrificeProperty []
      Role.humanAnnotator.claimantId hgraph hdeclared bound_exceedance
  let h_traj : Safety.KernelGovernedTrajectory sys D D' :=
    Safety.KernelGovernedTrajectory.singleSacrificeStep cert
  refine ⟨cert, h_traj, ?_, ?_⟩
  · rfl
  · exact Safety.KernelGovernedTrajectory.HasSacrificeStepAt.here cert
      (Safety.KernelGovernedTrajectory.refl D')

end RLHF

end Legitimacy
