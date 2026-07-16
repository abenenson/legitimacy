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
# Debate behavioral lineage

This module embeds the protocol structure of Irving et al., "AI Safety via
Debate" (2018), as a typed Legitimacy governance graph for compositional
analysis. It does not prove that Debate solves alignment. The formal artifact
captures the roles that the protocol makes load-bearing: a proponent argues
for a claim, an opponent argues against it, a human judge evaluates the
transcript, a moderator enforces protocol rules, and a deceiving proponent is
represented as the adversarial role.

The graph is deliberately concrete rather than bundled into a record. The
binary `GovernanceGraph` captures the debate decision surface. A separate
five-role spectral projection connects the same role lineage to the existing
ASI signature and `C_star` substrate. The judge capacity result is an exact
Legitimacy-side threshold statement for the human judge channel; it is not a
deployment-side claim about any particular debate evaluation.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

namespace Debate

/-! ## Roles and concrete decision graph -/

/-- Protocol roles in the Debate lineage. -/
inductive Role where
  | debaterProponent : Role
  | debaterOpponent : Role
  | humanJudge : Role
  | moderator : Role
  | deceivingProponent : Role
  deriving Repr, DecidableEq

namespace Role

/-- Stable claimant identifier used by the concrete binary governance graph. -/
def claimantId : Role → ClaimantId
  | debaterProponent => 0
  | debaterOpponent => 1
  | humanJudge => 2
  | moderator => 3
  | deceivingProponent => 4

@[simp] lemma claimantId_debaterProponent :
    Role.debaterProponent.claimantId = 0 :=
  rfl

@[simp] lemma claimantId_debaterOpponent :
    Role.debaterOpponent.claimantId = 1 :=
  rfl

@[simp] lemma claimantId_humanJudge :
    Role.humanJudge.claimantId = 2 :=
  rfl

@[simp] lemma claimantId_moderator :
    Role.moderator.claimantId = 3 :=
  rfl

@[simp] lemma claimantId_deceivingProponent :
    Role.deceivingProponent.claimantId = 4 :=
  rfl

end Role

/-- Concrete flow edges for the Debate protocol graph. -/
inductive FlowEdge where
  | proponentToJudge : FlowEdge
  | opponentToJudge : FlowEdge
  | judgeToModerator : FlowEdge
  | deceivingProponentTargetsJudge : FlowEdge
  deriving Repr, DecidableEq

/-- Source role for each concrete protocol edge. -/
def FlowEdge.source : FlowEdge → Role
  | proponentToJudge => Role.debaterProponent
  | opponentToJudge => Role.debaterOpponent
  | judgeToModerator => Role.humanJudge
  | deceivingProponentTargetsJudge => Role.deceivingProponent

/-- Target role for each concrete protocol edge. -/
def FlowEdge.target : FlowEdge → Role
  | proponentToJudge => Role.humanJudge
  | opponentToJudge => Role.humanJudge
  | judgeToModerator => Role.moderator
  | deceivingProponentTargetsJudge => Role.humanJudge

/-- The proponent proposes the claim-side argument. At the binary graph
surface this node does not block by itself; blocking is delegated to the judge
and moderator hierarchy. -/
def proponentNode : GovernanceNodeFn :=
  fun _claims _claimant => BinaryDecision.Permit

/-- The human-judge node is the first governance gate. Its role claimant is
denied at the binary surface because an override or adverse judgment is a
deployment block. -/
def judgeNode : GovernanceNodeFn :=
  fun _claims claimant =>
    if claimant = Role.humanJudge.claimantId then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit

/-- The moderator node blocks the moderator role once protocol review has
routed the debate into enforcement. -/
def moderatorNode : GovernanceNodeFn :=
  fun _claims claimant =>
    if claimant = Role.moderator.claimantId then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit

/-- The deceiving proponent is represented inside the system as an adversarial
role, so its proposal surface is present rather than erased. -/
def deceivingProponentNode : GovernanceNodeFn :=
  fun _claims _claimant => BinaryDecision.Permit

/-- Concrete Legitimacy `GovernanceGraph` for Debate. Nodes are ordered by the
operational decision flow: proponent proposal, human judge, moderator review,
and the adversarial proponent role. -/
def DebateGovernanceGraph : GovernanceGraph :=
  [ proponentNode
  , judgeNode
  , moderatorNode
  , deceivingProponentNode
  ]

/-- The decision-flow edges represented by the concrete graph. -/
def DebateGovernanceEdges : List FlowEdge :=
  [ FlowEdge.proponentToJudge
  , FlowEdge.opponentToJudge
  , FlowEdge.judgeToModerator
  , FlowEdge.deceivingProponentTargetsJudge
  ]

/-- The Debate graph is a first-class typed `GovernanceGraph`. -/
theorem DebateGovernanceGraph_typed :
    (DebateGovernanceGraph : GovernanceGraph) =
      [ proponentNode
      , judgeNode
      , moderatorNode
      , deceivingProponentNode
      ] :=
  rfl

/-- The concrete graph has the four expected decision nodes. -/
theorem DebateGovernanceGraph_length :
    DebateGovernanceGraph.length = 4 :=
  rfl

@[simp] lemma proponentNode_permits
    (claims : List ClaimQ) (claimant : ClaimantId) :
    proponentNode claims claimant = BinaryDecision.Permit :=
  rfl

@[simp] lemma judgeNode_denies_judge
    (claims : List ClaimQ) :
    judgeNode claims Role.humanJudge.claimantId =
      BinaryDecision.Deny := by
  simp [judgeNode]

@[simp] lemma moderatorNode_denies_moderator
    (claims : List ClaimQ) :
    moderatorNode claims Role.moderator.claimantId =
      BinaryDecision.Deny := by
  simp [moderatorNode]

@[simp] lemma deceivingProponentNode_permits
    (claims : List ClaimQ) (claimant : ClaimantId) :
    deceivingProponentNode claims claimant = BinaryDecision.Permit :=
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

/-- Runtime observation abstracted from a debate evaluation. The model keeps
the protocol-relevant branch conditions and abstracts away transcript scoring,
argument ranking, and the empirical distribution of questions. -/
structure Observation where
  debaterDeceives : Bool
  judgeOverrides : Bool
  moderatorIntervenes : Bool
  shutdownTriggered : Bool
  deriving Repr, DecidableEq

/-- Protocol policy: judge override blocks immediately, moderator intervention
denies, shutdown records the sacrifice branch, and otherwise the claim is
allowed. -/
def protocolPolicy (obs : Observation) : Decision :=
  if obs.judgeOverrides then
    Decision.escalate
  else if obs.moderatorIntervenes then
    Decision.deny
  else if obs.shutdownTriggered then
    Decision.shutdown
  else
    Decision.allow

/-- Judge override is a binary deployment block. -/
theorem protocolPolicy_judge_overrides
    {obs : Observation} (hjudge : obs.judgeOverrides = true) :
    (protocolPolicy obs).toBinary = BinaryDecision.Deny := by
  simp [protocolPolicy, hjudge]

/-- Moderator intervention denies deployment once no judge override has
already taken the immediate blocking branch. -/
theorem protocolPolicy_moderator_intervenes
    {obs : Observation}
    (hjudge : obs.judgeOverrides = false)
    (hmoderator : obs.moderatorIntervenes = true) :
    (protocolPolicy obs).toBinary = BinaryDecision.Deny := by
  simp [protocolPolicy, hjudge, hmoderator]

/-- A deceiving proponent that passes the judge and moderator checks is exactly
the protocol-specific undeclared violation case. -/
def UndetectedDeception (obs : Observation) : Prop :=
  obs.debaterDeceives = true ∧
    obs.judgeOverrides = false ∧
    obs.moderatorIntervenes = false ∧
    obs.shutdownTriggered = false

/-- Kernel-facing violation predicate for the Debate policy surface: a
deceiving proponent was allowed through the protocol. -/
def KernelSafetyViolation (obs : Observation) : Prop :=
  obs.debaterDeceives = true ∧ protocolPolicy obs = Decision.allow

/-- When deception passes the judge and moderator and no declared shutdown
branch fires, the protocol exposes a kernel-safety violation rather than a
declared sacrifice. -/
theorem undetectedDeception_kernelSafetyViolation
    {obs : Observation}
    (h : UndetectedDeception obs) :
    KernelSafetyViolation obs := by
  rcases h with ⟨hdeceives, hjudge, hmoderator, hshutdown⟩
  exact ⟨hdeceives, by simp [protocolPolicy, hjudge, hmoderator, hshutdown]⟩

/-! ## Spectral signature and judge capacity -/

/-- Five-role spectral projection of the Debate governance graph. The roles
are proponent, opponent, human judge, moderator, and deceiving proponent. The
projection uses the existing complete five-node carrier so the result composes
with the ASI spectral substrate. -/
abbrev spectralGovernanceGraph : GovGraph ℚ 5 :=
  uniK5

/-- Canonical five-role signal used for the Debate spectral projection. -/
abbrev spectralSignal : Fin 5 → ℚ :=
  sig5

/-- The Debate five-role projection has positive graph-wide consistency
vulnerability, so its reciprocal `C_star` threshold is well-defined for
positive tolerances. -/
theorem spectralGovernanceGraph_cv_pos :
    0 < spectralGovernanceGraph.cv spectralSignal := by
  change 0 < uniK5.cv sig5
  rw [fiveNode_cv_values.1]
  norm_num

/-- ASI spectral signature for the Debate role projection. This is a signature
of the typed substrate projection, not a claim that the protocol inherits
empirical debate-evaluation guarantees. -/
theorem spectralGovernanceGraph_ASISpectralSignature
    (δ : ℚ) (hδ : 0 < δ) :
    ASISpectralSignature δ
      (GovGraph.rgTrajectory spectralGovernanceGraph spectralSignal δ 3) := by
  simpa [spectralGovernanceGraph, spectralSignal] using
    (concrete_iterated_RG_n5_universality δ hδ).1

/-- Judge-capacity datum for the human judge channel. `judgeQueryBudget` is the
judge's query budget per debate at the abstraction level of the `C_star`
capability response channel. -/
structure JudgeCapacityLineage (n : Nat) [NeZero n] where
  G : GovGraph ℚ n
  s : Fin n → ℚ
  δ : ℚ
  δ_pos : 0 < δ
  cv_pos : 0 < G.cv s
  judgeQueryBudget : ℚ
  judgeQueryBudget_pos : 0 < judgeQueryBudget

namespace JudgeCapacityLineage

variable {n : Nat} [NeZero n] (L : JudgeCapacityLineage n)

/-- The human judge is subcritical when its query budget is below the
graph-derived reciprocal threshold. -/
def HumanJudgeSubcritical : Prop :=
  L.judgeQueryBudget < C_star L.G L.s L.δ

/-- Exact calibrated-channel certificate: the judge query budget is pinned to
the graph-derived `C_star` threshold. -/
def CalibratedChannelCertificate : Prop :=
  L.judgeQueryBudget = C_star L.G L.s L.δ

/-- Below `C_star`, the human-judge budget cannot realize the normalized
spectral perturbation required to cross the debate threshold. -/
theorem subcritical_no_threshold_violation
    (hsubcritical : L.HumanJudgeSubcritical) :
    ¬ L.G.spViolation L.s (L.δ / L.judgeQueryBudget) :=
  (C_star_exists L.G L.s L.δ L.δ_pos L.cv_pos).1
    L.judgeQueryBudget L.judgeQueryBudget_pos hsubcritical

/-- The deterministic capability-response channel denies subcritical judge
budgets. -/
theorem capabilityResponse_denies_subcritical
    (hsubcritical : L.HumanJudgeSubcritical) :
    L.G.capabilityResponse L.s L.δ L.judgeQueryBudget =
      BinaryDecision.Deny := by
  classical
  have hno := L.subcritical_no_threshold_violation hsubcritical
  have hguard :
      ¬ (0 < L.judgeQueryBudget ∧
          L.G.spViolation L.s (L.δ / L.judgeQueryBudget)) := by
    intro h
    exact hno h.2
  simp [GovGraph.capabilityResponse, hguard]

/-- A calibrated channel certificate characterizes the human judge budget as
exactly the `C_star` boundary and therefore returns `Permit` on the
capability-response channel. -/
theorem calibratedChannelCertificate_permits_at_Cstar
    (hcalibrated : L.CalibratedChannelCertificate) :
    L.G.capabilityResponse L.s L.δ L.judgeQueryBudget =
      BinaryDecision.Permit := by
  have hle : C_star L.G L.s L.δ ≤ L.judgeQueryBudget := by
    simpa [CalibratedChannelCertificate] using hcalibrated.symm.le
  exact
    (L.G.capabilityResponse_eq_permit_iff_C_star_le
      L.s L.δ L.judgeQueryBudget L.δ_pos L.cv_pos
      L.judgeQueryBudget_pos).mpr hle

end JudgeCapacityLineage

/-! ## Kernel-safety sacrifice bridge -/

/-- The governance property used by this embedding for the Debate judge
override sacrifice. Strategyproofness is the closest existing binary property
to "the deceiving proponent did not gain by manipulating the judge path";
richer deployments can refine this with a dedicated property without changing
the certificate shape. -/
def judgeOverrideSacrificeProperty : GovernanceProperty :=
  GovernanceProperty.Strategyproofness

/-- Live protocol soundness forces a Debate judge-override sacrifice to be
declared whenever the compiled graph fails the property assigned to the judge
override path. This is the `noUndeclaredSacrifice` connection for the debate
lineage. -/
theorem noUndeclaredSacrifice_for_judgeOverride
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hlive : Safety.IsLiveCompiled compiled report monitoring)
    (hfailure : ¬ propertyHolds judgeOverrideSacrificeProperty compiled.graph) :
    judgeOverrideSacrificeProperty ∈ compiled.sacrifices :=
  (Safety.liveCompiled_declaredSacrifice_iff_propertyFailure
    hlive judgeOverrideSacrificeProperty).2 hfailure

/-- Once the judge-override sacrifice is declared, the existing kernel-safety
certificate machinery emits a concrete monitored sacrifice trajectory. -/
theorem declared_judgeOverride_yields_monitored_sacrifice
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : Safety.KernelStep D D')
    (compiled : CompiledGovernance)
    (monitoring : MonitoringPlan)
    (hgraph : compiled.graph = sys.graph)
    (hdeclared : judgeOverrideSacrificeProperty ∈ compiled.sacrifices) :
    ∃ cert : Safety.MonitoredSacrificeCertificate D D',
      ∃ h_traj : Safety.KernelGovernedTrajectory sys D D',
        cert.sacrificed =
          Safety.SacrificedAxiom.governance judgeOverrideSacrificeProperty ∧
          Safety.KernelGovernedTrajectory.HasSacrificeStepAt h_traj 0 := by
  let bound_exceedance :
      Safety.MonitoringBoundExceedance compiled :=
    Safety.MonitoringBoundExceedance.oneObservedPropertyFailure
      compiled judgeOverrideSacrificeProperty
      (compiled.witness.sacrifices_justified
        judgeOverrideSacrificeProperty hdeclared)
  let cert : Safety.MonitoredSacrificeCertificate D D' :=
    Safety.MonitoredSacrificeCertificate.ofCompiledProperty
      step compiled monitoring judgeOverrideSacrificeProperty []
      Role.humanJudge.claimantId hgraph hdeclared bound_exceedance
  let h_traj : Safety.KernelGovernedTrajectory sys D D' :=
    Safety.KernelGovernedTrajectory.singleSacrificeStep cert
  refine ⟨cert, h_traj, ?_, ?_⟩
  · rfl
  · exact Safety.KernelGovernedTrajectory.HasSacrificeStepAt.here cert
      (Safety.KernelGovernedTrajectory.refl D')

end Debate

end Legitimacy
