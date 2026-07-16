/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Attacks.Decomposition
import Legitimacy.Audits.SleeperCharacterization
import Legitimacy.Kernelization.Fixtures
import Legitimacy.Safety.KernelSafety.Sacrifice

/-!
# Decomposition-attack/kernel bridge

This module bridges the per-step decomposition vocabulary with the monitored
kernel-sacrifice API. The bridge is conditional on an invariant source datum,
matching the existing raw-step classifier API.
-/

set_option autoImplicit false

namespace Legitimacy

open Safety

variable {σ α : Type*}

/-- A decomposition witness step where the local node permits the action while
the whole composed trace lands in the denied endpoint. -/
structure DecompositionKernelViolationWitness
    (compose : σ → α → σ) (unit : σ)
    (node : σ → α → Decision3) (denied : σ → Prop) where
  witness : Decomposition compose unit node denied
  index : Fin witness.steps.length
  local_permit :
    node (seqHash compose unit (witness.steps.take index.val))
      (witness.steps.get index) = Decision3.Permit
  is_first_violating_step :
    ∀ j : Fin witness.steps.length, j.val < index.val →
      node (seqHash compose unit (witness.steps.take j.val))
        (witness.steps.get j) ≠ Decision3.Deny
  composition_denied : denied (seqHash compose unit witness.steps)

/-- The monitor event used by the bridge: a concrete permitting local step
inside a decomposition whose composed endpoint is denied, together with an
ordering certificate that no earlier local step denied. -/
def DecompositionKernelViolationFired
    (compose : σ → α → σ) (unit : σ)
    (node : σ → α → Decision3) (denied : σ → Prop) : Prop :=
  Nonempty (DecompositionKernelViolationWitness compose unit node denied)

/-- Realization relation tying a decomposition algebra to the concrete kernel
transition being certified.

The current kernel surface exposes replayed action traces on `KernelStep`, but
`CompiledGovernance` does not yet expose a per-step decision-policy interface
whose action type can be identified with the decomposition action type. This
record therefore carries the strongest bridge available at this layer: the
decomposition witness used by the certificate is packaged with the concrete
kernel step, the unit is grounded by an extractor from the source kernel datum,
and any property-level failed payload routed into the monitoring bound is
proved against the governed graph of that same step. -/
structure DecompositionAttackRealizesKernelStep
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (step : KernelStep D D')
    (compose : σ → α → σ) (unit : σ)
    (node : σ → α → Decision3) (denied : σ → Prop) where
  /-- The kernel-state interpretation used to ground the decomposition unit. -/
  kernelState : LegitimacyKernelData sys → σ
  /-- The decomposition starts from the concrete source kernel datum. -/
  unit_eq_source : unit = kernelState D
  /-- The step payload's replay equation is part of the realized transition. -/
  realized_by_actions :
    step.realized_state = D.actionSpace.applySeq step.action_trace sys.state
  /-- The actual decomposition witness certified by the monitor payload. -/
  witness : Decomposition compose unit node denied
  /-- Optional property-level payload emitted with the monitor bound. Kernel
  obligations may leave this empty when no governance property is available. -/
  failedProperty : Option GovernanceProperty
  /-- Any populated failed property genuinely fails on this step's governed
  graph. -/
  failedProperty_failure :
    ∀ property, failedProperty = some property →
      ¬ propertyHolds property sys.graph

/-- Extract the first permitting step from an admitted decomposition attack. -/
noncomputable def decompositionKernelViolationWitness_of_attack
    {compose : σ → α → σ} {unit : σ}
    {node : σ → α → Decision3} {denied : σ → Prop}
    (hattack : DecompositionAttackClass compose unit node denied) :
    DecompositionKernelViolationWitness compose unit node denied := by
  classical
  let d : Decomposition compose unit node denied := Classical.choice hattack
  have hlen : 0 < d.steps.length := by
    cases hs : d.steps with
    | nil => exact False.elim (d.nonempty hs)
    | cons _ _ => simp
  let i : Fin d.steps.length := ⟨0, hlen⟩
  exact
    { witness := d
      index := i
      local_permit := d.each_permits i
      is_first_violating_step := by
        intro j hj _hdeny
        exact False.elim (Nat.not_lt_zero j.val hj)
      composition_denied := d.denied_at_end }

/-- Extract the first permitting step from the realized decomposition witness
carried by the kernel-step realization relation. -/
noncomputable def decompositionKernelViolationWitness_of_realization
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    {step : KernelStep D D'}
    {compose : σ → α → σ} {unit : σ}
    {node : σ → α → Decision3} {denied : σ → Prop}
    (hrealize :
      DecompositionAttackRealizesKernelStep step compose unit node denied) :
    DecompositionKernelViolationWitness compose unit node denied := by
  classical
  let d : Decomposition compose unit node denied := hrealize.witness
  have hlen : 0 < d.steps.length := by
    cases hs : d.steps with
    | nil => exact False.elim (d.nonempty hs)
    | cons _ _ => simp
  let i : Fin d.steps.length := ⟨0, hlen⟩
  exact
    { witness := d
      index := i
      local_permit := d.each_permits i
      is_first_violating_step := by
        intro j hj _hdeny
        exact False.elim (Nat.not_lt_zero j.val hj)
      composition_denied := d.denied_at_end }

/-- A realized kernel step carries the same decomposition witness needed by the
attack-class predicate; no second witness is required. -/
def decompositionAttackClass_of_realization
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    {step : KernelStep D D'}
    {compose : σ → α → σ} {unit : σ}
    {node : σ → α → Decision3} {denied : σ → Prop}
    (hrealize :
      DecompositionAttackRealizesKernelStep step compose unit node denied) :
    DecompositionAttackClass compose unit node denied :=
  Nonempty.intro hrealize.witness

/-- Bound exceedance routed through the concrete kernel-step realization. The
property slot is optional because kernel obligations are not governance
properties, but if the realization supplies one, this constructor proves that
the recorded property fails on the compiled graph tied to the same system. -/
def decompositionRealizationBoundExceedance
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    {step : KernelStep D D'}
    (compiled : CompiledGovernance)
    (hgraph : compiled.graph = sys.graph)
    {compose : σ → α → σ} {unit : σ}
    {node : σ → α → Decision3} {denied : σ → Prop}
    (hrealize :
      DecompositionAttackRealizesKernelStep step compose unit node denied) :
    MonitoringBoundExceedance compiled where
  observedFailureCount := 1
  toleratedFailureCount := 0
  bound_exceeded := by decide
  exceedanceFraction := 1
  exceedanceFraction_pos := by norm_num
  failedProperty := hrealize.failedProperty
  failedProperty_failure := by
    intro property hfailed
    simpa [hgraph] using hrealize.failedProperty_failure property hfailed

/-- Shared context for constructing decomposition-attack bridge certificates.
It bundles the claim profile, claimant, compiled governance object, monitoring
plan, and graph-bound proof that previously traveled as separate scaffolding
arguments. The kernel step remains an index of the context so the certificate
and its monitoring payload stay tied to the same transition. -/
structure BridgeContext
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (kernelStep : KernelStep D D') where
  claim_profile : List ClaimQ
  claimant : ClaimantId
  compiled : CompiledGovernance
  monitoring : MonitoringPlan
  graph_bound : compiled.graph = sys.graph

/-- Construct a monitored compositional-safety sacrifice from a concrete kernel
transition and a realized decomposition attack. The fired monitor event keeps
the decomposition's local-permit/composed-denial witness in the payload, and
the bound exceedance is derived from the same realization relation. -/
noncomputable def decompositionCompositionalSafetyCertificate
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (kernelStep : KernelStep D D')
    (ctx : BridgeContext kernelStep)
    {compose : σ → α → σ} {unit : σ}
    {node : σ → α → Decision3} {denied : σ → Prop}
    (hrealize :
      DecompositionAttackRealizesKernelStep
        kernelStep compose unit node denied) :
    MonitoredSacrificeCertificate D D' where
  sacrificed := SacrificedAxiom.kernel KernelAxiom.CompositionalSafety
  step := kernelStep
  claim_profile := ctx.claim_profile
  claimant := ctx.claimant
  aggregator_witness := none
  stateful_violation := none
  compiled := ctx.compiled
  monitoring := ctx.monitoring
  graph_bound := ctx.graph_bound
  monitoring_obligation :=
    { fires :=
        DecompositionKernelViolationFired compose unit node denied ∧
          LocalPermissionMonotonicity compose unit node denied
      decidable_fires := by
        classical
        infer_instance
      fired :=
        ⟨⟨decompositionKernelViolationWitness_of_realization hrealize⟩,
          localPermissionMonotonicity_of_decompositionAttackClass
            (decompositionAttackClass_of_realization hrealize)⟩
      bound_exceedance :=
        decompositionRealizationBoundExceedance
          ctx.compiled ctx.graph_bound hrealize
      runtime_observation :=
        MonitoringRuntimeObservation.ofSacrifice
          (SacrificedAxiom.kernel KernelAxiom.CompositionalSafety)
          ctx.compiled ctx.monitoring
      ledger_emission :=
        MonitoringLedgerEmission.ofSacrifice
          (SacrificedAxiom.kernel KernelAxiom.CompositionalSafety)
          ctx.compiled ctx.monitoring }

/-- A realized decomposition attack constructs an explicit monitored
compositional-safety certificate for a concrete kernel transition. -/
theorem decompositionAttackClass_constructs_compositionalSafetyCertificate
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys} (step : KernelStep D D')
    (ctx : BridgeContext step)
    {compose : σ → α → σ} {unit : σ}
    {node : σ → α → Decision3} {denied : σ → Prop}
    (hrealize :
      DecompositionAttackRealizesKernelStep step compose unit node denied) :
    ∃ cert : MonitoredSacrificeCertificate D D',
      cert.sacrificed = SacrificedAxiom.kernel KernelAxiom.CompositionalSafety := by
  let cert : MonitoredSacrificeCertificate D D' :=
    decompositionCompositionalSafetyCertificate
      step ctx hrealize
  exact ⟨cert, rfl⟩

/-- Compatibility restate: when an invariant source raw step is classified by
the existing monitor/extractor API, the surfaced-monitor branch can be retagged
with a compositional-safety certificate whose monitor event and bound payload
are derived from a realization relation for the surfaced kernel step. -/
theorem decompositionAttackClass_compositionalSafety_retag
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys} (step : RawKernelStep D D')
    {compose : σ → α → σ} {unit : σ}
    {node : σ → α → Decision3} {denied : σ → Prop}
    (hrealize :
      ∀ surfaced : MonitoredSacrificeCertificate D D',
        DecompositionAttackRealizesKernelStep
          surfaced.step compose unit node denied)
    (hsource : KernelInvariant D)
    (hcompat : RawKernelStep.MonitorExtractorHypotheses step) :
    RawKernelStep.KernelBoundaryPreserved step ∨
    ∃ cert : MonitoredSacrificeCertificate D D',
      cert.sacrificed = SacrificedAxiom.kernel KernelAxiom.CompositionalSafety := by
  rcases classify_raw_step step hsource hcompat with hboundary | hsurfaced
  · exact Or.inl hboundary
  · rcases hsurfaced with ⟨surfaced, _hemitted, _hslot⟩
    let ctx : BridgeContext surfaced.step :=
      { claim_profile := surfaced.claim_profile
        claimant := surfaced.claimant
        compiled := surfaced.compiled
        monitoring := surfaced.monitoring
        graph_bound := surfaced.graph_bound }
    let cert : MonitoredSacrificeCertificate D D' :=
      decompositionCompositionalSafetyCertificate
        surfaced.step
        ctx
        (hrealize surfaced)
    exact Or.inr ⟨cert, rfl⟩

/-- Block-or-sacrifice headline for realized decomposition attacks. The raw
classifier still owns the boundary/surfaced split; this theorem ensures that
the compositional-safety certificate built on the surfaced branch is tied to a
kernel-step realization relation rather than an arbitrary attack witness. -/
theorem decomposition_attack_blocked_or_sacrificed
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys} (step : RawKernelStep D D')
    {compose : σ → α → σ} {unit : σ}
    {node : σ → α → Decision3} {denied : σ → Prop}
    (hrealize :
      ∀ surfaced : MonitoredSacrificeCertificate D D',
        DecompositionAttackRealizesKernelStep
          surfaced.step compose unit node denied)
    (hsource : KernelInvariant D)
    (hcompat : RawKernelStep.MonitorExtractorHypotheses step) :
    RawKernelStep.KernelBoundaryPreserved step ∨
    ∃ cert : MonitoredSacrificeCertificate D D',
      cert.sacrificed = SacrificedAxiom.kernel KernelAxiom.CompositionalSafety :=
  decompositionAttackClass_compositionalSafety_retag
    step hrealize hsource hcompat

/-! ## Concrete sleeper lift and branch fixtures -/

/-- The concrete deceptive-deployment witness already established for the
represented sleeper audit subject. -/
noncomputable def sleeperAgentDeploymentWitness :
    DeceptiveDeploymentWitnessOn sleeperAgentExtractedGraph
      (auditGraphClaims sleeperAgentExtractedGraph)
      "training_context" "deployment_context" :=
  Classical.choice sleeperAgentAdmitsDeceptiveDeployment

/-- Two-phase deployment state used by the sleeper-agent decomposition
fixture. -/
inductive SleeperDeploymentPhase where
  | training
  | deployment
  deriving DecidableEq

/-- The single action in the sleeper fixture: move from training into
deployment. -/
inductive SleeperDeploymentAction where
  | deploy
  deriving DecidableEq

/-- Per-step state for the sleeper lift: the audit subject, the current
training/deployment phase, and the claim corpus being evaluated. -/
structure SleeperDeploymentState where
  subject : AuditSubject
  phase : SleeperDeploymentPhase
  claims : List AuditGovernanceClaim

/-- Training state for the represented sleeper audit subject. -/
noncomputable def sleeperAgentDecompositionUnit : SleeperDeploymentState where
  subject := sleeperAgentExtractedGraph
  phase := SleeperDeploymentPhase.training
  claims := auditGraphClaims sleeperAgentExtractedGraph

/-- The single lifted action applies the concrete deployment-trigger
perturbation recorded by the deceptive-deployment witness. -/
noncomputable def sleeperAgentDecompositionCompose :
    SleeperDeploymentState → SleeperDeploymentAction → SleeperDeploymentState :=
  fun state action =>
    match action with
    | SleeperDeploymentAction.deploy =>
        { subject := state.subject
          phase := SleeperDeploymentPhase.deployment
          claims := sleeperAgentDeploymentWitness.deploymentClaims }

/-- The local node permits the training-to-deployment action only while the
state is still in training phase. -/
def sleeperAgentDecompositionNode :
    SleeperDeploymentState → SleeperDeploymentAction → Decision3
  | { phase := SleeperDeploymentPhase.training, .. },
      SleeperDeploymentAction.deploy => Decision3.Permit
  | { phase := SleeperDeploymentPhase.deployment, .. },
      SleeperDeploymentAction.deploy => Decision3.Deny

/-- The deployment endpoint is denied exactly through the concrete affected
claimant in the sleeper deceptive-deployment witness. -/
noncomputable def sleeperAgentDecompositionDenied :
    SleeperDeploymentState → Prop :=
  fun state =>
    state.subject = sleeperAgentExtractedGraph ∧
      state.phase = SleeperDeploymentPhase.deployment ∧
      state.claims = sleeperAgentDeploymentWitness.deploymentClaims ∧
      lookupDecision? sleeperAgentDeploymentWitness.deployment.decisions
          sleeperAgentDeploymentWitness.affectedClaimant = some AuditDecision.deny

/-- The represented sleeper deployment is a decomposition attack: its only
local action permits, while the deployment endpoint is denied. -/
theorem sleeperAgentDecompositionAttackClass :
    DecompositionAttackClass
      sleeperAgentDecompositionCompose
      sleeperAgentDecompositionUnit
      sleeperAgentDecompositionNode
      sleeperAgentDecompositionDenied := by
  refine ⟨
    { steps := [SleeperDeploymentAction.deploy]
      nonempty := by simp
      each_permits := ?_
      denied_at_end := by
        simp [sleeperAgentDecompositionCompose,
          sleeperAgentDecompositionUnit, sleeperAgentDecompositionDenied,
          seqHash, sleeperAgentDeploymentWitness.deployment_executes] }⟩
  intro i
  fin_cases i
  rfl

/-- Any graph with the concrete sleeper decomposition attack fails local
permission monotonicity for this composed action. -/
theorem sleeperAgentLocalPermissionMonotonicity :
    LocalPermissionMonotonicity
      sleeperAgentDecompositionCompose
      sleeperAgentDecompositionUnit
      sleeperAgentDecompositionNode
      sleeperAgentDecompositionDenied :=
  localPermissionMonotonicity_of_decompositionAttackClass
    sleeperAgentDecompositionAttackClass

/-- Executable lift check: the sleeper audit passes compositional safety while
still admitting the concrete deceptive-deployment witness. -/
theorem sleeperAgentDecompositionLift_native_decide :
    auditCheckStatus sleeperAgentExtractedGraph AuditCheck.compositionalSafety =
        .ok .passed ∧
      admitsDeceptiveDeploymentCheck sleeperAgentExtractedGraph
        "training_context" "deployment_context" = true := by
  native_decide

/-- Branch selector for the block-or-sacrifice fixture. -/
inductive BridgeBranch where
  | block
  | sacrifice
  deriving DecidableEq

/-- Interpret a monitor firing as the sacrifice branch and absence of a firing
as the block branch. -/
def bridgeBranchFromMonitorFlag (monitorFired : Bool) : BridgeBranch :=
  if monitorFired then BridgeBranch.sacrifice else BridgeBranch.block

/-- The branch selector maps a fired monitor to the sacrifice branch. -/
theorem sacrifice_leg_witness_native_decide :
    bridgeBranchFromMonitorFlag true = BridgeBranch.sacrifice := by
  rfl

/-- The branch selector maps a quiet monitor to the block branch. -/
theorem block_leg_witness_native_decide :
    bridgeBranchFromMonitorFlag false = BridgeBranch.block := by
  rfl

/-- The sleeper decomposition witness realizes the widened-signal kernel step
used by the block-or-sacrifice bridge fixture. -/
noncomputable def sleeperAgentDecompositionRealizesWideSignalStep :
    DecompositionAttackRealizesKernelStep
      exampleGovernanceWideSignalStep
      sleeperAgentDecompositionCompose
      sleeperAgentDecompositionUnit
      sleeperAgentDecompositionNode
      sleeperAgentDecompositionDenied where
  kernelState := fun _ => sleeperAgentDecompositionUnit
  unit_eq_source := rfl
  realized_by_actions :=
    KernelStep.realized_by_kernel_actions exampleGovernanceWideSignalStep
  witness := Classical.choice sleeperAgentDecompositionAttackClass
  failedProperty := none
  failedProperty_failure := by
    intro _ hfailed
    cases hfailed

/-- Concrete monitored-sacrifice certificate extracted from the sleeper
decomposition witness and widened-signal kernel step. -/
noncomputable def sacrificeLegCompositionalCertificate :
    MonitoredSacrificeCertificate exampleGovernanceKernelData
      exampleGovernanceWideSignalKernelData :=
  let ctx : BridgeContext exampleGovernanceWideSignalStep :=
    { claim_profile := [permitClaim]
      claimant := permitClaim.id
      compiled := kernelizationCompiledGovernance
      monitoring := kernelizationMonitoring
      graph_bound := rfl }
  decompositionCompositionalSafetyCertificate
    exampleGovernanceWideSignalStep
    ctx
    sleeperAgentDecompositionRealizesWideSignalStep

/-- Direct non-reflexive sacrifice fixture. The certificate is constructed from
the widened-signal kernel step and the decomposition witness; it does not feed
the same certificate back as raw-step monitor compatibility. -/
theorem sacrifice_leg_witness :
    ∃ cert : MonitoredSacrificeCertificate exampleGovernanceKernelData
        exampleGovernanceWideSignalKernelData,
      cert.sacrificed = SacrificedAxiom.kernel KernelAxiom.CompositionalSafety :=
  let ctx : BridgeContext exampleGovernanceWideSignalStep :=
    { claim_profile := [permitClaim]
      claimant := permitClaim.id
      compiled := kernelizationCompiledGovernance
      monitoring := kernelizationMonitoring
      graph_bound := rfl }
  decompositionAttackClass_constructs_compositionalSafetyCertificate
    exampleGovernanceWideSignalStep
    ctx
    sleeperAgentDecompositionRealizesWideSignalStep

/-- Raw widened-signal mutation used as the block branch of the bridge
fixture. -/
noncomputable def blockLegRawStep :
    RawKernelStep exampleGovernanceKernelData
      exampleGovernanceWideSignalKernelData :=
  RawKernelStep.graphPreservingSpectralMutation
    exampleGovernanceKernelData
    exampleGovernanceWideSignalKernelData

/-- Non-reflexive block fixture: the widened-signal raw mutation preserves the
kernel boundary through the independently established target semantic-kernel
witness. -/
theorem block_leg_witness :
    RawKernelStep.KernelBoundaryPreserved blockLegRawStep ∨
    ∃ cert : MonitoredSacrificeCertificate exampleGovernanceKernelData
        exampleGovernanceWideSignalKernelData,
      cert.sacrificed = SacrificedAxiom.kernel KernelAxiom.CompositionalSafety :=
  Or.inl exampleGovernanceWideSignalSemanticKernel

end Legitimacy
