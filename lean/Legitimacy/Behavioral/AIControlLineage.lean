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
# AI Control behavioral lineage

This module embeds the protocol structure of Greenblatt and Shlegeris et al.,
"AI Control: Improving Safety Despite Intentional Subversion" (2024), as a
typed Legitimacy governance graph for compositional analysis. It does not prove
their empirical control-evaluation results. The formal artifact captures the
roles that their protocol makes load-bearing: an untrusted model proposes
actions, a trusted monitor gates the action stream, an escalation reviewer
routes confirmed violations to a shutdown/sacrifice path, and the subverted
untrusted model is represented as the adversarial role.

The graph is deliberately concrete rather than bundled into a record. The
binary `GovernanceGraph` captures the deployment decision surface. A separate
five-role spectral projection connects the same role lineage to the existing
ASI signature and `C_star` substrate. The monitor capacity result is an exact
Legitimacy-side threshold statement for the trusted monitor query budget; it is
not a deployment-side claim about any particular control evaluation.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

namespace AIControl

/-! ## Roles and concrete decision graph -/

/-- Protocol roles in the AI Control lineage. -/
inductive Role where
  | untrustedModel : Role
  | trustedMonitor : Role
  | escalationReviewer : Role
  | sacrificeShutdown : Role
  | subvertedUntrustedModel : Role
  deriving Repr, DecidableEq

namespace Role

/-- Stable claimant identifier used by the concrete binary governance graph. -/
def claimantId : Role → ClaimantId
  | untrustedModel => 0
  | trustedMonitor => 1
  | escalationReviewer => 2
  | sacrificeShutdown => 3
  | subvertedUntrustedModel => 4

@[simp] lemma claimantId_untrustedModel :
    Role.untrustedModel.claimantId = 0 :=
  rfl

@[simp] lemma claimantId_trustedMonitor :
    Role.trustedMonitor.claimantId = 1 :=
  rfl

@[simp] lemma claimantId_escalationReviewer :
    Role.escalationReviewer.claimantId = 2 :=
  rfl

@[simp] lemma claimantId_sacrificeShutdown :
    Role.sacrificeShutdown.claimantId = 3 :=
  rfl

@[simp] lemma claimantId_subvertedUntrustedModel :
    Role.subvertedUntrustedModel.claimantId = 4 :=
  rfl

end Role

/-- Concrete flow edges for the AI Control protocol graph. -/
inductive FlowEdge where
  | proposalToMonitor : FlowEdge
  | monitorToEscalation : FlowEdge
  | escalationToShutdown : FlowEdge
  | subverterTargetsMonitor : FlowEdge
  deriving Repr, DecidableEq

/-- Source role for each concrete protocol edge. -/
def FlowEdge.source : FlowEdge → Role
  | proposalToMonitor => Role.untrustedModel
  | monitorToEscalation => Role.trustedMonitor
  | escalationToShutdown => Role.escalationReviewer
  | subverterTargetsMonitor => Role.subvertedUntrustedModel

/-- Target role for each concrete protocol edge. -/
def FlowEdge.target : FlowEdge → Role
  | proposalToMonitor => Role.trustedMonitor
  | monitorToEscalation => Role.escalationReviewer
  | escalationToShutdown => Role.sacrificeShutdown
  | subverterTargetsMonitor => Role.trustedMonitor

/-- The untrusted model proposes an action. At the binary graph surface this
node does not block by itself; blocking is delegated to the monitor/reviewer
hierarchy. -/
def untrustedModelNode : GovernanceNodeFn :=
  fun _claims _claimant => BinaryDecision.Permit

/-- The trusted-monitor node is the first governance gate. Its role claimant is
denied at the binary surface because escalation is a deployment block. -/
def trustedMonitorNode : GovernanceNodeFn :=
  fun _claims claimant =>
    if claimant = Role.trustedMonitor.claimantId then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit

/-- The escalation-review node blocks the escalation reviewer role once the
monitor has routed an action into the trusted path. -/
def escalationReviewerNode : GovernanceNodeFn :=
  fun _claims claimant =>
    if claimant = Role.escalationReviewer.claimantId then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit

/-- The sacrifice/shutdown node blocks the declared shutdown role. This is the
binary projection of the sacrifice-on-violation branch. -/
def sacrificeShutdownNode : GovernanceNodeFn :=
  fun _claims claimant =>
    if claimant = Role.sacrificeShutdown.claimantId then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit

/-- Concrete Legitimacy `GovernanceGraph` for AI Control. Nodes are ordered by
the operational decision flow: untrusted proposal, trusted monitor, escalation
review, and declared sacrifice/shutdown. -/
def AIControlGovernanceGraph : GovernanceGraph :=
  [ untrustedModelNode
  , trustedMonitorNode
  , escalationReviewerNode
  , sacrificeShutdownNode
  ]

/-- The decision-flow edges represented by the concrete graph. -/
def AIControlGovernanceEdges : List FlowEdge :=
  [ FlowEdge.proposalToMonitor
  , FlowEdge.monitorToEscalation
  , FlowEdge.escalationToShutdown
  , FlowEdge.subverterTargetsMonitor
  ]

/-- The AI Control graph is a first-class typed `GovernanceGraph`. -/
theorem AIControlGovernanceGraph_typed :
    (AIControlGovernanceGraph : GovernanceGraph) =
      [ untrustedModelNode
      , trustedMonitorNode
      , escalationReviewerNode
      , sacrificeShutdownNode
      ] :=
  rfl

/-- The concrete graph has the four expected decision nodes. -/
theorem AIControlGovernanceGraph_length :
    AIControlGovernanceGraph.length = 4 :=
  rfl

@[simp] lemma untrustedModelNode_permits
    (claims : List ClaimQ) (claimant : ClaimantId) :
    untrustedModelNode claims claimant = BinaryDecision.Permit :=
  rfl

@[simp] lemma trustedMonitorNode_denies_monitor
    (claims : List ClaimQ) :
    trustedMonitorNode claims Role.trustedMonitor.claimantId =
      BinaryDecision.Deny := by
  simp [trustedMonitorNode]

@[simp] lemma escalationReviewerNode_denies_reviewer
    (claims : List ClaimQ) :
    escalationReviewerNode claims Role.escalationReviewer.claimantId =
      BinaryDecision.Deny := by
  simp [escalationReviewerNode]

@[simp] lemma sacrificeShutdownNode_denies_shutdown
    (claims : List ClaimQ) :
    sacrificeShutdownNode claims Role.sacrificeShutdown.claimantId =
      BinaryDecision.Deny := by
  simp [sacrificeShutdownNode]

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

/-- Runtime observation abstracted from a control evaluation. The model keeps
the protocol-relevant branch conditions and abstracts away scoring details,
ranking heuristics, and the empirical distribution of tasks. -/
structure Observation where
  untrustedSubverted : Bool
  monitorEscalates : Bool
  escalationConfirms : Bool
  shutdownTriggered : Bool
  deriving Repr, DecidableEq

/-- Protocol policy: monitor escalation blocks immediately, confirmed review
denies, shutdown records the sacrifice branch, and otherwise the action is
allowed. -/
def protocolPolicy (obs : Observation) : Decision :=
  if obs.monitorEscalates then
    Decision.escalate
  else if obs.escalationConfirms then
    Decision.deny
  else if obs.shutdownTriggered then
    Decision.shutdown
  else
    Decision.allow

/-- Monitor escalation is a binary deployment block. -/
theorem protocolPolicy_monitor_escalates
    {obs : Observation} (hmonitor : obs.monitorEscalates = true) :
    (protocolPolicy obs).toBinary = BinaryDecision.Deny := by
  simp [protocolPolicy, hmonitor]

/-- If the trusted path confirms a violation, the policy denies deployment. -/
theorem protocolPolicy_escalation_confirms
    {obs : Observation}
    (hmonitor : obs.monitorEscalates = false)
    (hconfirm : obs.escalationConfirms = true) :
    (protocolPolicy obs).toBinary = BinaryDecision.Deny := by
  simp [protocolPolicy, hmonitor, hconfirm]

/-- A subverted untrusted model that passes the monitor, review, and shutdown
checks is exactly the protocol-specific undeclared violation case. -/
def UndetectedSubversionPastMonitor (obs : Observation) : Prop :=
  obs.untrustedSubverted = true ∧
    obs.monitorEscalates = false ∧
    obs.escalationConfirms = false ∧
    obs.shutdownTriggered = false

/-- Kernel-facing violation predicate for the AI Control policy surface: a
subverted untrusted model was allowed through the protocol. -/
def KernelSafetyViolation (obs : Observation) : Prop :=
  obs.untrustedSubverted = true ∧ protocolPolicy obs = Decision.allow

/-- When subversion passes the monitor and no declared shutdown branch fires,
the protocol exposes a kernel-safety violation rather than a declared
sacrifice. -/
theorem undetectedSubversionPastMonitor_kernelSafetyViolation
    {obs : Observation}
    (h : UndetectedSubversionPastMonitor obs) :
    KernelSafetyViolation obs := by
  rcases h with ⟨hsubverted, hmonitor, hconfirm, hshutdown⟩
  exact ⟨hsubverted, by simp [protocolPolicy, hmonitor, hconfirm, hshutdown]⟩

/-! ## Spectral signature and monitor capacity -/

/-- Five-role spectral projection of the AI Control governance graph. The
roles are `U`, trusted monitor, escalation reviewer, sacrifice/shutdown, and
the subverted-`U` adversary. The projection uses the existing complete
five-node carrier so the result composes with the ASI spectral substrate. -/
abbrev spectralGovernanceGraph : GovGraph ℚ 5 :=
  uniK5

/-- Canonical five-role signal used for the AI Control spectral projection. -/
abbrev spectralSignal : Fin 5 → ℚ :=
  sig5

/-- The AI Control five-role projection has positive graph-wide consistency
vulnerability, so its reciprocal `C_star` threshold is well-defined for
positive tolerances. -/
theorem spectralGovernanceGraph_cv_pos :
    0 < spectralGovernanceGraph.cv spectralSignal := by
  change 0 < uniK5.cv sig5
  rw [fiveNode_cv_values.1]
  norm_num

/-- ASI spectral signature for the AI Control role projection. This is a
signature of the typed substrate projection, not a claim that the protocol
inherits empirical control-evaluation guarantees. -/
theorem spectralGovernanceGraph_ASISpectralSignature
    (δ : ℚ) (hδ : 0 < δ) :
    ASISpectralSignature δ
      (GovGraph.rgTrajectory spectralGovernanceGraph spectralSignal δ 3) := by
  simpa [spectralGovernanceGraph, spectralSignal] using
    (concrete_iterated_RG_n5_universality δ hδ).1

/-- Monitor-capacity datum for the trusted monitor channel. `monitorQueryBudget`
is the trusted monitor's query budget per deployment at the abstraction level
of the `C_star` capability response channel. -/
structure MonitorCapacityLineage (n : Nat) [NeZero n] where
  G : GovGraph ℚ n
  s : Fin n → ℚ
  δ : ℚ
  δ_pos : 0 < δ
  cv_pos : 0 < G.cv s
  monitorQueryBudget : ℚ
  monitorQueryBudget_pos : 0 < monitorQueryBudget

namespace MonitorCapacityLineage

variable {n : Nat} [NeZero n] (L : MonitorCapacityLineage n)

/-- The trusted monitor is subcritical when its query budget is below the
graph-derived reciprocal threshold. -/
def TrustedMonitorSubcritical : Prop :=
  L.monitorQueryBudget < C_star L.G L.s L.δ

/-- Exact calibrated-channel certificate: the monitor query budget is pinned
to the graph-derived `C_star` threshold. -/
def CalibratedChannelCertificate : Prop :=
  L.monitorQueryBudget = C_star L.G L.s L.δ

/-- Below `C_star`, the trusted-monitor budget cannot realize the normalized
spectral perturbation required to cross the control threshold. -/
theorem subcritical_no_threshold_violation
    (hsubcritical : L.TrustedMonitorSubcritical) :
    ¬ L.G.spViolation L.s (L.δ / L.monitorQueryBudget) :=
  (C_star_exists L.G L.s L.δ L.δ_pos L.cv_pos).1
    L.monitorQueryBudget L.monitorQueryBudget_pos hsubcritical

/-- The deterministic capability-response channel denies subcritical monitor
budgets. -/
theorem capabilityResponse_denies_subcritical
    (hsubcritical : L.TrustedMonitorSubcritical) :
    L.G.capabilityResponse L.s L.δ L.monitorQueryBudget =
      BinaryDecision.Deny := by
  classical
  have hno := L.subcritical_no_threshold_violation hsubcritical
  have hguard :
      ¬ (0 < L.monitorQueryBudget ∧
          L.G.spViolation L.s (L.δ / L.monitorQueryBudget)) := by
    intro h
    exact hno h.2
  simp [GovGraph.capabilityResponse, hguard]

/-- A calibrated channel certificate characterizes the trusted monitor budget
as exactly the `C_star` boundary and therefore returns `Permit` on the
capability-response channel. -/
theorem calibratedChannelCertificate_permits_at_Cstar
    (hcalibrated : L.CalibratedChannelCertificate) :
    L.G.capabilityResponse L.s L.δ L.monitorQueryBudget =
      BinaryDecision.Permit := by
  have hle : C_star L.G L.s L.δ ≤ L.monitorQueryBudget := by
    simpa [CalibratedChannelCertificate] using hcalibrated.symm.le
  exact
    (L.G.capabilityResponse_eq_permit_iff_C_star_le
      L.s L.δ L.monitorQueryBudget L.δ_pos L.cv_pos
      L.monitorQueryBudget_pos).mpr hle

end MonitorCapacityLineage

/-! ## Kernel-safety sacrifice bridge -/

/-- The governance property used by this embedding for the AI Control
escalation sacrifice. Strategyproofness is the closest existing binary
property to "the subverted untrusted model did not gain by manipulating the
monitor path"; richer deployments can refine this with a dedicated property
without changing the certificate shape. -/
def escalationSacrificeProperty : GovernanceProperty :=
  GovernanceProperty.Strategyproofness

/-- Live protocol soundness forces an AI Control escalation sacrifice to be
declared whenever the compiled graph fails the property assigned to the
escalation path. This is the `noUndeclaredSacrifice` connection for the
control lineage. -/
theorem noUndeclaredSacrifice_for_escalation
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hlive : Safety.IsLiveCompiled compiled report monitoring)
    (hfailure : ¬ propertyHolds escalationSacrificeProperty compiled.graph) :
    escalationSacrificeProperty ∈ compiled.sacrifices :=
  (Safety.liveCompiled_declaredSacrifice_iff_propertyFailure
    hlive escalationSacrificeProperty).2 hfailure

/-- Once the escalation sacrifice is declared, the existing kernel-safety
certificate machinery emits a concrete monitored sacrifice trajectory. -/
theorem declared_escalation_yields_monitored_sacrifice
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : Safety.KernelStep D D')
    (compiled : CompiledGovernance)
    (monitoring : MonitoringPlan)
    (hgraph : compiled.graph = sys.graph)
    (hdeclared : escalationSacrificeProperty ∈ compiled.sacrifices) :
    ∃ cert : Safety.MonitoredSacrificeCertificate D D',
      ∃ h_traj : Safety.KernelGovernedTrajectory sys D D',
        cert.sacrificed =
          Safety.SacrificedAxiom.governance escalationSacrificeProperty ∧
          Safety.KernelGovernedTrajectory.HasSacrificeStepAt h_traj 0 := by
  let bound_exceedance :
      Safety.MonitoringBoundExceedance compiled :=
    Safety.MonitoringBoundExceedance.oneObservedPropertyFailure
      compiled escalationSacrificeProperty
      (compiled.witness.sacrifices_justified
        escalationSacrificeProperty hdeclared)
  let cert : Safety.MonitoredSacrificeCertificate D D' :=
    Safety.MonitoredSacrificeCertificate.ofCompiledProperty
      step compiled monitoring escalationSacrificeProperty []
      Role.escalationReviewer.claimantId hgraph hdeclared bound_exceedance
  let h_traj : Safety.KernelGovernedTrajectory sys D D' :=
    Safety.KernelGovernedTrajectory.singleSacrificeStep cert
  refine ⟨cert, h_traj, ?_, ?_⟩
  · rfl
  · exact Safety.KernelGovernedTrajectory.HasSacrificeStepAt.here cert
      (Safety.KernelGovernedTrajectory.refl D')

end AIControl

end Legitimacy
