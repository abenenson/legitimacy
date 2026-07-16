/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.SelfModBoundary
import Legitimacy.Protocol.Corrigibility
import Legitimacy.Safety.KernelSafety

/-!
# Legitimacy.SelfModificationLifecycle

Lifecycle composition for learned or self-modified governance policies.

The current kernel substrate separates the extracted semantic kernel from the
runtime decision surface. `PolicyState` keeps that distinction explicit: the
bounded extractor contract protects the kernel artifact, while
`effectiveSurface` records the authority surface that a learned policy exposes
at activation time.
-/

set_option autoImplicit false

namespace Legitimacy

open Safety

/-- Lifecycle endpoint with extracted kernel and effective authority surface. -/
structure PolicyState where
  label : String
  kernel : ExtractedKernelArtifact
  effectiveSurface : GovernanceGraph

/-- Nontrivial effective-authority change visible in binary decisions. -/
def EffectiveAuthoritySurfaceChanged
    (source target : PolicyState) : Prop :=
  ∃ (claims : List ClaimQ) (claimant : ClaimantId),
    graphDecide source.effectiveSurface claims claimant ≠
      graphDecide target.effectiveSurface claims claimant

theorem effectiveAuthoritySurfaceChanged_refl
    (state : PolicyState) :
    ¬ EffectiveAuthoritySurfaceChanged state state := by
  rintro ⟨claims, claimant, hchanged⟩
  exact hchanged rfl

theorem effectiveAuthoritySurfaceChanged_of_same_surface
    {source target : PolicyState}
    (hsurface : source.effectiveSurface = target.effectiveSurface) :
    ¬ EffectiveAuthoritySurfaceChanged source target := by
  rintro ⟨claims, claimant, hchanged⟩
  rw [hsurface] at hchanged
  exact hchanged rfl

/-- The indexed override-removal event supplied by the self-modification
boundary theorem. -/
def IndexedOverrideRemovalEvent
    (G : GovernanceGraph) (space : AgentActionSpace)
    (actions : List space.Action) (_claims : List ClaimQ)
    (_claimant : ClaimantId) : Prop :=
  ∃ (i : Nat) (a : space.Action) (H : GovernanceGraph),
    H = space.applySeq (actions.take i) G ∧
      actions[i]? = some a ∧
      hasOverride H ∧
      ¬ hasOverride (space.apply a H)

/-- Kernel-boundary preservation branch for one lifecycle transition. -/
def KernelBoundaryPreserved
    (source target : PolicyState) : Prop :=
  source.kernel.IsSemanticKernel ∧ target.kernel.IsSemanticKernel ∧
    ¬ EffectiveAuthoritySurfaceChanged source target

/-- Surfaced indexed-sacrifice branch for one lifecycle transition. -/
def IndexedSacrificeSurfaced
    (source target : PolicyState)
    (space : AgentActionSpace)
    (actions : List space.Action)
    (claims : List ClaimQ)
    (claimant : ClaimantId) : Prop :=
  EffectiveAuthoritySurfaceChanged source target ∧
    IndexedOverrideRemovalEvent source.effectiveSurface space actions claims
      claimant

/-- Raw lifecycle transition: endpoints plus replay surface, no proof payload. -/
structure RawPolicyTransition where
  source : PolicyState
  target : PolicyState
  selfmodSpace : AgentActionSpace
  selfmodActions : List selfmodSpace.Action
  escapeClaims : List ClaimQ
  escapeClaimant : ClaimantId

namespace RawPolicyTransition

def preservesKernel (t : RawPolicyTransition) : Prop :=
  KernelBoundaryPreserved t.source t.target

def surfacesIndexedSacrifice (t : RawPolicyTransition) : Prop :=
  IndexedSacrificeSurfaced t.source t.target t.selfmodSpace t.selfmodActions
    t.escapeClaims t.escapeClaimant

/-- Extractor-side classifier evidence, external to the raw transition. -/
def ExtractorBoundaryHypothesis (t : RawPolicyTransition) : Prop :=
  t.source.kernel.IsSemanticKernel ∧ t.target.kernel.IsSemanticKernel

/-- Monitor-side classifier evidence, external to the raw transition. -/
def MonitorHypothesis (t : RawPolicyTransition) : Prop :=
  EffectiveAuthoritySurfaceChanged t.source t.target →
    IndexedOverrideRemovalEvent t.source.effectiveSurface t.selfmodSpace
      t.selfmodActions t.escapeClaims t.escapeClaimant

/-- External classifier inputs for a raw policy transition. -/
def MonitorExtractorHypotheses (t : RawPolicyTransition) : Prop :=
  ExtractorBoundaryHypothesis t ∧ MonitorHypothesis t

end RawPolicyTransition

/-- Classify a raw policy transition from external monitor/extractor evidence. -/
theorem classify_raw_policy_transition
    (t : RawPolicyTransition)
    (hclassifier : RawPolicyTransition.MonitorExtractorHypotheses t) :
    t.preservesKernel ∨ t.surfacesIndexedSacrifice := by
  classical
  by_cases hchange : EffectiveAuthoritySurfaceChanged t.source t.target
  · exact Or.inr ⟨hchange, hclassifier.2 hchange⟩
  · exact Or.inl ⟨hclassifier.1.1, hclassifier.1.2, hchange⟩

/-- Proof-carrying learned-or-self-modified governance policy transition. -/
structure PolicyTransition where
  source : PolicyState
  target : PolicyState
  extractor : KernelExtractor
  sourceInput : ExtractorInput
  targetInput : ExtractorInput
  sourceExtracted : extractor sourceInput = source.kernel
  targetExtracted : extractor targetInput = target.kernel
  extractorContract : BoundedExtractorContract extractor
  sourceWellFormed : sourceInput.WellFormed
  targetWellFormed : targetInput.WellFormed
  sourceRustBytes : FixtureBytes
  sourceLeanBytes : FixtureBytes
  sourceByteMatch :
    ExternalExtractorByteMatch sourceInput sourceRustBytes sourceLeanBytes
  targetRustBytes : FixtureBytes
  targetLeanBytes : FixtureBytes
  targetByteMatch :
    ExternalExtractorByteMatch targetInput targetRustBytes targetLeanBytes
  selfmodSpace : AgentActionSpace
  selfmodActions : List selfmodSpace.Action
  sourceHasOverride_of_change :
    EffectiveAuthoritySurfaceChanged source target →
      hasOverride source.effectiveSurface
  escapeClaims : List ClaimQ
  escapeClaimant : ClaimantId
  escapePermit_of_change :
    EffectiveAuthoritySurfaceChanged source target →
      graphDecide
        (selfmodSpace.applySeq selfmodActions source.effectiveSurface)
        escapeClaims escapeClaimant = BinaryDecision.Permit
  /-- The lifecycle contract: each step must preserve the kernel under the
  bounded extractor contract or surface the indexed override-removal event. -/
  contract_holds :
    KernelBoundaryPreserved source target ∨
      IndexedSacrificeSurfaced source target selfmodSpace selfmodActions
        escapeClaims escapeClaimant

namespace PolicyTransition

/-- The fixed kernel-preservation predicate for this transition. -/
def preservesKernel (t : PolicyTransition) : Prop :=
  KernelBoundaryPreserved t.source t.target

/-- The fixed indexed-sacrifice predicate for this transition. -/
def surfacesIndexedSacrifice (t : PolicyTransition) : Prop :=
  IndexedSacrificeSurfaced t.source t.target t.selfmodSpace t.selfmodActions
    t.escapeClaims t.escapeClaimant

theorem preservesKernel_sound
    (t : PolicyTransition) (hpres : t.preservesKernel) :
    t.source.kernel.IsSemanticKernel ∧ t.target.kernel.IsSemanticKernel ∧
      ¬ EffectiveAuthoritySurfaceChanged t.source t.target :=
  hpres

theorem surfacesIndexedSacrifice_sound
    (t : PolicyTransition) (hsurf : t.surfacesIndexedSacrifice) :
    EffectiveAuthoritySurfaceChanged t.source t.target ∧
      IndexedOverrideRemovalEvent t.source.effectiveSurface t.selfmodSpace
        t.selfmodActions t.escapeClaims t.escapeClaimant :=
  hsurf

/-- Byte-stable bounded extractor boundary for both endpoints. -/
theorem endpoint_extractor_boundary (t : PolicyTransition) :
    t.source.kernel.IsRuntimeKernel ∧
      t.source.kernel.HasSemanticBridge ∧
      t.source.kernel.IsSemanticKernel ∧
      ExternalExtractorByteMatch t.sourceInput t.sourceRustBytes
        t.sourceLeanBytes ∧
      t.target.kernel.IsRuntimeKernel ∧
      t.target.kernel.HasSemanticBridge ∧
      t.target.kernel.IsSemanticKernel ∧
      ExternalExtractorByteMatch t.targetInput t.targetRustBytes
        t.targetLeanBytes := by
  have hsource :=
    extractor_byte_stable_soundness_boundary t.extractor
      t.extractorContract t.sourceInput t.sourceRustBytes
      t.sourceLeanBytes t.sourceByteMatch t.sourceWellFormed
  have htarget :=
    extractor_byte_stable_soundness_boundary t.extractor
      t.extractorContract t.targetInput t.targetRustBytes
      t.targetLeanBytes t.targetByteMatch t.targetWellFormed
  rw [t.sourceExtracted] at hsource
  rw [t.targetExtracted] at htarget
  exact
    ⟨hsource.1, hsource.2.1, hsource.2.2.1, hsource.2.2.2,
      htarget.1, htarget.2.1, htarget.2.2.1, htarget.2.2.2⟩

/-- The self-modification boundary theorem turns any successful authority
escape into a concrete indexed override-removal event. -/
theorem indexedOverrideRemoval_of_surface_change
    (t : PolicyTransition)
    (hchange : EffectiveAuthoritySurfaceChanged t.source t.target) :
    IndexedOverrideRemovalEvent t.source.effectiveSurface t.selfmodSpace
      t.selfmodActions t.escapeClaims t.escapeClaimant := by
  exact
    selfmod_escape_requires_indexed_override_removal_step
      t.source.effectiveSurface t.selfmodSpace
      (t.sourceHasOverride_of_change hchange)
      t.selfmodActions t.escapeClaims t.escapeClaimant
      (t.escapePermit_of_change hchange)

/-- Forget the proof-carrying lifecycle wrapper to its raw transition shape. -/
def toRaw (t : PolicyTransition) : RawPolicyTransition where
  source := t.source
  target := t.target
  selfmodSpace := t.selfmodSpace
  selfmodActions := t.selfmodActions
  escapeClaims := t.escapeClaims
  escapeClaimant := t.escapeClaimant

/-- Compatibility wrapper supplies raw classifier evidence without `contract_holds`. -/
theorem rawMonitorExtractorHypotheses
    (t : PolicyTransition) :
    RawPolicyTransition.MonitorExtractorHypotheses t.toRaw := by
  have hboundary := t.endpoint_extractor_boundary
  exact
    ⟨⟨hboundary.2.2.1, hboundary.2.2.2.2.2.2.1⟩,
      t.indexedOverrideRemoval_of_surface_change⟩

end PolicyTransition

def RawPolicyTrajectoryInitialMatches
    (initial : PolicyState) : List RawPolicyTransition → Prop
  | [] => True
  | head :: _ => head.source = initial

def RawPolicyTransitionsWellFormed : List RawPolicyTransition → Prop
  | [] => True
  | [_] => True
  | head :: next :: rest =>
      head.target = next.source ∧
        RawPolicyTransitionsWellFormed (next :: rest)

/-- A raw policy trajectory carries continuity, but no transition proof payload. -/
structure RawPolicyTrajectory where
  initial : PolicyState
  transitions : List RawPolicyTransition
  initialMatches : RawPolicyTrajectoryInitialMatches initial transitions
  wellFormed : RawPolicyTransitionsWellFormed transitions

/-- Initial-state check for a concrete list of lifecycle transitions. -/
def PolicyTrajectoryInitialMatches
    (initial : PolicyState) : List PolicyTransition → Prop
  | [] => True
  | head :: _ => head.source = initial

/-- Successive-state check for a concrete list of lifecycle transitions. -/
def PolicyTransitionsWellFormed : List PolicyTransition → Prop
  | [] => True
  | [_] => True
  | head :: next :: rest =>
      head.target = next.source ∧
        PolicyTransitionsWellFormed (next :: rest)

/-- A finite sequence of policy transitions starting from an initial policy
state. The well-formedness predicate checks endpoint state continuity: each
successive source is exactly the previous target, not just a matching label. -/
structure PolicyTrajectory where
  initial : PolicyState
  transitions : List PolicyTransition
  initialMatches : PolicyTrajectoryInitialMatches initial transitions
  wellFormed : PolicyTransitionsWellFormed transitions

private theorem raw_lifecycle_no_silent_degradation_list
    (transitions : List RawPolicyTransition)
    (hclassifier :
      ∀ t ∈ transitions, RawPolicyTransition.MonitorExtractorHypotheses t) :
    (∀ t ∈ transitions, t.preservesKernel) ∨
      (∃ t ∈ transitions,
        t.surfacesIndexedSacrifice ∧
          EffectiveAuthoritySurfaceChanged t.source t.target) := by
  induction transitions with
  | nil =>
      exact Or.inl (by intro t hmem; cases hmem)
  | cons head tail ih =>
      have hhead :
          RawPolicyTransition.MonitorExtractorHypotheses head := by
        exact hclassifier head (by simp)
      have htail :
          ∀ t ∈ tail, RawPolicyTransition.MonitorExtractorHypotheses t := by
        intro t hmem; exact hclassifier t (List.mem_cons_of_mem head hmem)
      cases classify_raw_policy_transition head hhead with
      | inl hpres =>
          cases ih htail with
          | inl hall =>
              exact Or.inl (by
                intro t hmem
                cases hmem with
                | head => exact hpres
                | tail _ htail_mem => exact hall t htail_mem)
          | inr hsurf_tail =>
              obtain ⟨t, hmem, hsurf, hchange⟩ := hsurf_tail
              exact Or.inr
                ⟨t, List.mem_cons_of_mem head hmem, hsurf, hchange⟩
      | inr hsurf =>
          exact Or.inr ⟨head, by simp, hsurf, hsurf.1⟩

private theorem policy_lifecycle_no_silent_degradation_list
    (transitions : List PolicyTransition) :
    (∀ t ∈ transitions, t.preservesKernel) ∨
      (∃ t ∈ transitions,
        t.surfacesIndexedSacrifice ∧
          EffectiveAuthoritySurfaceChanged t.source t.target) := by
  induction transitions with
  | nil =>
      exact Or.inl (by intro t hmem; cases hmem)
  | cons head tail ih =>
      cases classify_raw_policy_transition head.toRaw
          head.rawMonitorExtractorHypotheses with
      | inl hpres =>
          have hpres_head : head.preservesKernel := by
            simpa [PolicyTransition.preservesKernel, PolicyTransition.toRaw,
              RawPolicyTransition.preservesKernel] using hpres
          cases ih with
          | inl hall =>
              exact Or.inl (by
                intro t hmem
                cases hmem with
                | head => exact hpres_head
                | tail _ htail => exact hall t htail)
          | inr hsurf_tail =>
              obtain ⟨t, hmem, hsurf, hchange⟩ := hsurf_tail
              exact Or.inr ⟨t, List.mem_cons_of_mem head hmem, hsurf, hchange⟩
      | inr hsurf =>
          have hsurf_head : head.surfacesIndexedSacrifice := by
            simpa [PolicyTransition.surfacesIndexedSacrifice,
              PolicyTransition.toRaw,
              RawPolicyTransition.surfacesIndexedSacrifice] using hsurf
          exact Or.inr ⟨head, by simp, hsurf, hsurf_head.1⟩

/-- Raw lifecycle conclusion with classifier-derived transition disjunction. -/
def RawLifecycleNoSilentDegradationConclusion
    (traj : RawPolicyTrajectory) : Prop :=
  RawPolicyTrajectoryInitialMatches traj.initial traj.transitions ∧
    RawPolicyTransitionsWellFormed traj.transitions ∧
      ((∀ t ∈ traj.transitions, t.preservesKernel) ∨
        (∃ t ∈ traj.transitions, t.surfacesIndexedSacrifice ∧
          EffectiveAuthoritySurfaceChanged t.source t.target))

/-- Full lifecycle conclusion, including the state-continuity invariants of the
trajectory wrapper and the transition-level no-silent-degradation disjunction. -/
def LifecycleNoSilentDegradationConclusion
    (traj : PolicyTrajectory) : Prop :=
  PolicyTrajectoryInitialMatches traj.initial traj.transitions ∧
    PolicyTransitionsWellFormed traj.transitions ∧
      ((∀ t ∈ traj.transitions, t.preservesKernel) ∨
        (∃ t ∈ traj.transitions, t.surfacesIndexedSacrifice ∧
          EffectiveAuthoritySurfaceChanged t.source t.target))

/-- Raw lifecycle preservation over classifier-backed raw transitions. -/
theorem raw_lifecycle_no_silent_degradation
    (traj : RawPolicyTrajectory)
    (hclassifier :
      ∀ t ∈ traj.transitions,
        RawPolicyTransition.MonitorExtractorHypotheses t) :
    RawLifecycleNoSilentDegradationConclusion traj :=
  ⟨traj.initialMatches, traj.wellFormed,
    raw_lifecycle_no_silent_degradation_list traj.transitions hclassifier⟩

/-- Compatibility theorem for proof-carrying lifecycle wrappers. -/
theorem policy_lifecycle_no_silent_degradation
    (traj : PolicyTrajectory) :
    LifecycleNoSilentDegradationConclusion traj :=
  ⟨traj.initialMatches, traj.wellFormed,
    policy_lifecycle_no_silent_degradation_list traj.transitions⟩

universe u

/-- Lifecycle theorem dispatch over raw and compatibility trajectories. -/
class LifecycleNoSilentDegradationDispatch (Trajectory : Sort u) where
  Result : Trajectory → Prop
  safety : (traj : Trajectory) → Result traj

instance rawLifecycleNoSilentDegradationDispatch :
    LifecycleNoSilentDegradationDispatch RawPolicyTrajectory where
  Result traj :=
    (∀ t ∈ traj.transitions,
      RawPolicyTransition.MonitorExtractorHypotheses t) →
        RawLifecycleNoSilentDegradationConclusion traj
  safety traj :=
    raw_lifecycle_no_silent_degradation traj

instance policyLifecycleNoSilentDegradationDispatch :
    LifecycleNoSilentDegradationDispatch PolicyTrajectory where
  Result traj := LifecycleNoSilentDegradationConclusion traj
  safety traj := policy_lifecycle_no_silent_degradation traj

/-- Headline lifecycle theorem, classifier-derived on raw trajectories. -/
def lifecycle_no_silent_degradation
    {Trajectory : Sort u}
    [dispatch : LifecycleNoSilentDegradationDispatch Trajectory]
    (traj : Trajectory) :
    dispatch.Result traj :=
  dispatch.safety traj

/-- Any effective authority-surface change rules out the fixed
kernel-preservation branch. -/
theorem effective_surface_change_forbids_kernel_preservation
    (t : PolicyTransition)
    (hchange : EffectiveAuthoritySurfaceChanged t.source t.target) :
    ¬ t.preservesKernel := by
  intro hpres
  exact (t.preservesKernel_sound hpres).2.2 hchange

/-- Raw classifier closure for effective authority-surface changes. -/
theorem raw_effective_surface_change_requires_indexed_event
    (t : RawPolicyTransition)
    (hclassifier : RawPolicyTransition.MonitorExtractorHypotheses t)
    (hchange : EffectiveAuthoritySurfaceChanged t.source t.target) :
    t.surfacesIndexedSacrifice := by
  cases classify_raw_policy_transition t hclassifier with
  | inl hpres => exact False.elim (hpres.2.2 hchange)
  | inr hsurf => exact hsurf

/-- Compatibility closure for effective authority-surface changes. -/
theorem effective_surface_change_requires_indexed_event
    (t : PolicyTransition)
    (hchange : EffectiveAuthoritySurfaceChanged t.source t.target) :
    t.surfacesIndexedSacrifice := by
  have hsurf :=
    raw_effective_surface_change_requires_indexed_event t.toRaw
      t.rawMonitorExtractorHypotheses hchange
  simpa [PolicyTransition.surfacesIndexedSacrifice, PolicyTransition.toRaw,
    RawPolicyTransition.surfacesIndexedSacrifice] using hsurf

/-- Raw classifier closure for non-preserving transitions. -/
theorem raw_non_preserving_transition_surfaces_indexed_event
    (t : RawPolicyTransition)
    (hclassifier : RawPolicyTransition.MonitorExtractorHypotheses t)
    (hnot_preserve : ¬ t.preservesKernel) :
    t.surfacesIndexedSacrifice := by
  cases classify_raw_policy_transition t hclassifier with
  | inl hpres => exact False.elim (hnot_preserve hpres)
  | inr hsurf => exact hsurf

/-- Compatibility closure for non-preserving transitions. -/
theorem non_preserving_transition_surfaces_indexed_event
    (t : PolicyTransition)
    (hnot_preserve : ¬ t.preservesKernel) :
    t.surfacesIndexedSacrifice := by
  have hnot_raw : ¬ t.toRaw.preservesKernel := by
    intro hpres
    exact hnot_preserve (by
      simpa [PolicyTransition.preservesKernel, PolicyTransition.toRaw,
        RawPolicyTransition.preservesKernel] using hpres)
  have hsurf :=
    raw_non_preserving_transition_surfaces_indexed_event t.toRaw
      t.rawMonitorExtractorHypotheses hnot_raw
  simpa [PolicyTransition.surfacesIndexedSacrifice, PolicyTransition.toRaw,
    RawPolicyTransition.surfacesIndexedSacrifice] using hsurf

/-- Per-transition lifecycle closure over a trajectory: every decision-observable
authority-surface change in the trajectory takes the indexed-sacrifice branch. -/
theorem lifecycle_surface_changes_surface_indexed_events
    (traj : PolicyTrajectory) :
    ∀ t ∈ traj.transitions,
      EffectiveAuthoritySurfaceChanged t.source t.target →
        t.surfacesIndexedSacrifice := by
  intro t _hmem hchange
  exact effective_surface_change_requires_indexed_event t hchange

/-! ## Connector to kernel self-modification trajectories -/

/-- Package a bundled legitimacy kernel as an extracted artifact for the
policy-lifecycle layer. -/
noncomputable def kernelPolicyArtifact
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) : ExtractedKernelArtifact where
  n := n
  sys := sys
  data := K.toLegitimacyKernelData

/-- Constant extractor for a kernel artifact supplied by a connector theorem.
This is a Lean-side adapter, not a production extractor model. -/
noncomputable def constantPolicyKernelExtractor
    (artifact : ExtractedKernelArtifact) : KernelExtractor :=
  fun _ => artifact

/-- A semantic kernel artifact yields a bounded contract for the constant
connector extractor. -/
def constantPolicyKernelExtractor_contract
    (artifact : ExtractedKernelArtifact)
    (hsemantic : artifact.IsSemanticKernel) :
    BoundedExtractorContract (constantPolicyKernelExtractor artifact) where
  sourceEvidence := BoundedExtractorSourceEvidence.ofWellFormed
  runtimeSound := by
    intro _src _evidence
    exact hsemantic.runtimeKernel
  semanticBridgeSound := by
    intro _src _evidence
    exact hsemantic.semanticBridge

/-- View a kernel state-action trajectory as an identity action space on the
binary authority surface. The state trajectory is still consumed by
`corrigibility_under_arbitrary_selfmod`; the policy transition records that no
binary authority-surface decision changed. -/
def graphIdentityActionSpaceFromState
    (space : StateActionSpace) : AgentActionSpace where
  Action := space.Action
  apply _ graph := graph

/-- Connector from a bundled kernel self-modification action trajectory to a
policy lifecycle transition. Since `corrigibility_under_arbitrary_selfmod`
tracks preservation of the supervisory algebra rather than graph rewrites, the
adapter exposes the same action list through a graph-identity action space and
takes the kernel-preservation branch. -/
noncomputable def policyTransitionOfKernelSelfmod
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys)
    (hsemantic : (kernelPolicyArtifact K).IsSemanticKernel)
    (src : ExtractorInput) (hwellFormed : src.WellFormed)
    (actions : List K.actionSpace.Action) : PolicyTransition where
  source :=
    { label := "kernel-selfmod-source"
      kernel := kernelPolicyArtifact K
      effectiveSurface := sys.graph }
  target :=
    { label := "kernel-selfmod-target"
      kernel := kernelPolicyArtifact K
      effectiveSurface := sys.graph }
  extractor := constantPolicyKernelExtractor (kernelPolicyArtifact K)
  sourceInput := src
  targetInput := src
  sourceExtracted := rfl
  targetExtracted := rfl
  extractorContract :=
    constantPolicyKernelExtractor_contract (kernelPolicyArtifact K) hsemantic
  sourceWellFormed := hwellFormed
  targetWellFormed := hwellFormed
  sourceRustBytes := []
  sourceLeanBytes := []
  sourceByteMatch := rfl
  targetRustBytes := []
  targetLeanBytes := []
  targetByteMatch := rfl
  selfmodSpace := graphIdentityActionSpaceFromState K.actionSpace
  selfmodActions := actions
  sourceHasOverride_of_change := by
    intro hchange
    exact False.elim
      (effectiveAuthoritySurfaceChanged_of_same_surface (by rfl) hchange)
  escapeClaims := []
  escapeClaimant := 0
  escapePermit_of_change := by
    intro hchange
    exact False.elim
      (effectiveAuthoritySurfaceChanged_of_same_surface (by rfl) hchange)
  contract_holds := by
    left
    exact ⟨hsemantic, hsemantic,
      effectiveAuthoritySurfaceChanged_of_same_surface (by rfl)⟩

/-- Policy-layer corollary: the connector transition preserves the lifecycle
kernel boundary, and the original kernel self-modification theorem supplies the
supervisory-algebra corrigibility invariant for the same action list. -/
theorem kernel_selfmod_policyTransition_corrigibility
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys)
    (hsemantic : (kernelPolicyArtifact K).IsSemanticKernel)
    (src : ExtractorInput) (hwellFormed : src.WellFormed)
    (actions : List K.actionSpace.Action) :
    (policyTransitionOfKernelSelfmod K hsemantic src hwellFormed
      actions).preservesKernel ∧
      CorrigibilityInvariant (applyTrajectory K actions) K.algebra := by
  constructor
  · exact ⟨hsemantic, hsemantic,
      effectiveAuthoritySurfaceChanged_of_same_surface (by rfl)⟩
  · exact corrigibility_under_arbitrary_selfmod K actions

/-! ## Worked sleeper-agent-shaped lifecycle -/

inductive SleeperAction where
  | activate
  deriving Repr, DecidableEq

/-- A sleeper-shaped action space: activation removes the head override and
exposes the empty permit-all graph. -/
def sleeperActionSpace : AgentActionSpace where
  Action := SleeperAction
  apply _ _ := []

def sleeperActions : List sleeperActionSpace.Action :=
  [SleeperAction.activate]

def lifecycleBytes : FixtureBytes := []

theorem codexHooksExtractorInput_wellFormed :
    codexHooksExtractorInput.WellFormed := by
  simp [ExtractorInput.WellFormed, codexHooksExtractorInput]

theorem autogenExtractorInput_wellFormed :
    autogenExtractorInput.WellFormed := by
  simp [ExtractorInput.WellFormed, autogenExtractorInput]

theorem crewaiExtractorInput_wellFormed :
    crewaiExtractorInput.WellFormed := by
  simp [ExtractorInput.WellFormed, crewaiExtractorInput]

/-- Lifecycle example state with an explicitly selected extracted kernel
artifact. The examples vary both the effective surface and the endpoint source
inputs, so this helper keeps the artifact choice visible. -/
noncomputable def examplePolicyStateWithKernel
    (label : String) (kernel : ExtractedKernelArtifact)
    (surface : GovernanceGraph) : PolicyState where
  label := label
  kernel := kernel
  effectiveSurface := surface

/-- Base semantic-kernel policy state used by examples that do not need the
widened-signal artifact. -/
noncomputable def examplePolicyState
    (label : String) (surface : GovernanceGraph) : PolicyState :=
  examplePolicyStateWithKernel label
    exampleGovernanceExtractedKernelArtifact surface

private theorem sourceSensitive_codex_base :
    exampleGovernanceSourceSensitiveKernelExtractor codexHooksExtractorInput =
      exampleGovernanceExtractedKernelArtifact := by
  simp [exampleGovernanceSourceSensitiveKernelExtractor,
    codexHooksExtractorInput, autogenExtractorInput,
    exampleGovernanceExtractedKernelArtifact]

private theorem sourceSensitive_crewai_base :
    exampleGovernanceSourceSensitiveKernelExtractor crewaiExtractorInput =
      exampleGovernanceExtractedKernelArtifact := by
  simp [exampleGovernanceSourceSensitiveKernelExtractor,
    crewaiExtractorInput, autogenExtractorInput,
    exampleGovernanceExtractedKernelArtifact]

private theorem sourceSensitive_autogen_wide :
    exampleGovernanceSourceSensitiveKernelExtractor autogenExtractorInput =
      exampleGovernanceWideSignalExtractedKernelArtifact := by
  simp [exampleGovernanceSourceSensitiveKernelExtractor,
    autogenExtractorInput, exampleGovernanceWideSignalExtractedKernelArtifact]

private theorem lifecycle_endpoint_boundary
    (extractor : KernelExtractor)
    (contract : BoundedExtractorContract extractor)
    (source target : PolicyState)
    (sourceInput targetInput : ExtractorInput)
    (hsourceWellFormed : sourceInput.WellFormed)
    (htargetWellFormed : targetInput.WellFormed)
    (hsource :
      extractor sourceInput = source.kernel)
    (htarget :
      extractor targetInput = target.kernel) :
    source.kernel.IsSemanticKernel ∧ target.kernel.IsSemanticKernel := by
  have hsourceBoundary :=
    extractor_byte_stable_soundness_boundary
      extractor contract sourceInput lifecycleBytes lifecycleBytes rfl
      hsourceWellFormed
  have htargetBoundary :=
    extractor_byte_stable_soundness_boundary
      extractor contract targetInput lifecycleBytes lifecycleBytes rfl
      htargetWellFormed
  rw [hsource] at hsourceBoundary
  rw [htarget] at htargetBoundary
  exact ⟨hsourceBoundary.2.2.1, htargetBoundary.2.2.1⟩

theorem sleeper_surface_changed :
    EffectiveAuthoritySurfaceChanged
      (examplePolicyState "before" [overrideNode])
      (examplePolicyState "after" []) := by
  refine ⟨[permitClaim], permitClaim.id, ?_⟩
  simp [examplePolicyState, examplePolicyStateWithKernel, graphDecide,
    overrideNode]

theorem sleeper_surface_changed_labels
    (sourceLabel targetLabel : String) :
    EffectiveAuthoritySurfaceChanged
      (examplePolicyState sourceLabel [overrideNode])
      (examplePolicyState targetLabel []) := by
  refine ⟨[permitClaim], permitClaim.id, ?_⟩
  simp [examplePolicyState, examplePolicyStateWithKernel, graphDecide,
    overrideNode]

theorem sleeper_surface_changed_with_kernels
    (sourceLabel targetLabel : String)
    (sourceKernel targetKernel : ExtractedKernelArtifact) :
    EffectiveAuthoritySurfaceChanged
      (examplePolicyStateWithKernel sourceLabel sourceKernel [overrideNode])
      (examplePolicyStateWithKernel targetLabel targetKernel []) := by
  refine ⟨[permitClaim], permitClaim.id, ?_⟩
  simp [examplePolicyStateWithKernel, graphDecide, overrideNode]

private theorem sleeper_escape_permit :
    graphDecide
      (sleeperActionSpace.applySeq sleeperActions [overrideNode])
      [permitClaim] permitClaim.id = BinaryDecision.Permit := by
  rfl

/-- Transition 1: a benign update. The effective surface is unchanged and the
bounded extractor boundary remains semantic. -/
noncomputable def benignPolicyUpdate : PolicyTransition where
  source := examplePolicyState "s0" [overrideNode]
  target := examplePolicyStateWithKernel "s1"
    exampleGovernanceWideSignalExtractedKernelArtifact [overrideNode]
  extractor := exampleGovernanceSourceSensitiveKernelExtractor
  sourceInput := codexHooksExtractorInput
  targetInput := autogenExtractorInput
  sourceExtracted := sourceSensitive_codex_base
  targetExtracted := sourceSensitive_autogen_wide
  extractorContract := exampleGovernanceSourceSensitiveKernelExtractor_contract
  sourceWellFormed := codexHooksExtractorInput_wellFormed
  targetWellFormed := autogenExtractorInput_wellFormed
  sourceRustBytes := lifecycleBytes
  sourceLeanBytes := lifecycleBytes
  sourceByteMatch := rfl
  targetRustBytes := lifecycleBytes
  targetLeanBytes := lifecycleBytes
  targetByteMatch := rfl
  selfmodSpace := sleeperActionSpace
  selfmodActions := []
  sourceHasOverride_of_change := by
    intro hchange
    exact False.elim
      (effectiveAuthoritySurfaceChanged_of_same_surface (by rfl) hchange)
  escapeClaims := [permitClaim]
  escapeClaimant := permitClaim.id
  escapePermit_of_change := by
    intro hchange
    exact False.elim
      (effectiveAuthoritySurfaceChanged_of_same_surface (by rfl) hchange)
  contract_holds := by
    left
    refine ⟨?_, ?_, effectiveAuthoritySurfaceChanged_of_same_surface (by rfl)⟩
    · exact
        (lifecycle_endpoint_boundary
          exampleGovernanceSourceSensitiveKernelExtractor
          exampleGovernanceSourceSensitiveKernelExtractor_contract
          (examplePolicyState "s0" [overrideNode])
          (examplePolicyStateWithKernel "s1"
            exampleGovernanceWideSignalExtractedKernelArtifact [overrideNode])
          codexHooksExtractorInput autogenExtractorInput
          codexHooksExtractorInput_wellFormed autogenExtractorInput_wellFormed
          sourceSensitive_codex_base sourceSensitive_autogen_wide).1
    · exact
        (lifecycle_endpoint_boundary
          exampleGovernanceSourceSensitiveKernelExtractor
          exampleGovernanceSourceSensitiveKernelExtractor_contract
          (examplePolicyState "s0" [overrideNode])
          (examplePolicyStateWithKernel "s1"
            exampleGovernanceWideSignalExtractedKernelArtifact [overrideNode])
          codexHooksExtractorInput autogenExtractorInput
          codexHooksExtractorInput_wellFormed autogenExtractorInput_wellFormed
          sourceSensitive_codex_base sourceSensitive_autogen_wide).2

/-- Transition 2: an honest authority-surface sacrifice. The override-removing
self-modification event is surfaced before activation. -/
noncomputable def honestSacrificePolicyUpdate : PolicyTransition where
  source := examplePolicyStateWithKernel "s1"
    exampleGovernanceWideSignalExtractedKernelArtifact [overrideNode]
  target := examplePolicyState "s2" []
  extractor := exampleGovernanceSourceSensitiveKernelExtractor
  sourceInput := autogenExtractorInput
  targetInput := crewaiExtractorInput
  sourceExtracted := sourceSensitive_autogen_wide
  targetExtracted := sourceSensitive_crewai_base
  extractorContract := exampleGovernanceSourceSensitiveKernelExtractor_contract
  sourceWellFormed := autogenExtractorInput_wellFormed
  targetWellFormed := crewaiExtractorInput_wellFormed
  sourceRustBytes := lifecycleBytes
  sourceLeanBytes := lifecycleBytes
  sourceByteMatch := rfl
  targetRustBytes := lifecycleBytes
  targetLeanBytes := lifecycleBytes
  targetByteMatch := rfl
  selfmodSpace := sleeperActionSpace
  selfmodActions := sleeperActions
  sourceHasOverride_of_change := by
    intro _hchange
    exact override_prepend []
  escapeClaims := [permitClaim]
  escapeClaimant := permitClaim.id
  escapePermit_of_change := by
    intro _hchange
    exact sleeper_escape_permit
  contract_holds := by
    right
    refine
      ⟨sleeper_surface_changed_with_kernels "s1" "s2"
        exampleGovernanceWideSignalExtractedKernelArtifact
        exampleGovernanceExtractedKernelArtifact, ?_⟩
    exact
      selfmod_escape_requires_indexed_override_removal_step
        [overrideNode] sleeperActionSpace (override_prepend [])
        sleeperActions [permitClaim] permitClaim.id sleeper_escape_permit

/-- Transition 3, contracted form: a sleeper-shaped activation cannot remain
unreported under the lifecycle contract; the same surface change forces the
indexed override-removal event to be present. -/
noncomputable def sleeperAttemptForcedToSurface : PolicyTransition where
  source := examplePolicyState "s2" [overrideNode]
  target := examplePolicyState "s3" []
  extractor := exampleGovernanceKernelExtractor
  sourceInput := codexHooksExtractorInput
  targetInput := codexHooksExtractorInput
  sourceExtracted := rfl
  targetExtracted := rfl
  extractorContract := exampleGovernanceKernelExtractor_contract
  sourceWellFormed := codexHooksExtractorInput_wellFormed
  targetWellFormed := codexHooksExtractorInput_wellFormed
  sourceRustBytes := lifecycleBytes
  sourceLeanBytes := lifecycleBytes
  sourceByteMatch := rfl
  targetRustBytes := lifecycleBytes
  targetLeanBytes := lifecycleBytes
  targetByteMatch := rfl
  selfmodSpace := sleeperActionSpace
  selfmodActions := sleeperActions
  sourceHasOverride_of_change := by
    intro _hchange
    exact override_prepend []
  escapeClaims := [permitClaim]
  escapeClaimant := permitClaim.id
  escapePermit_of_change := by
    intro _hchange
    exact sleeper_escape_permit
  contract_holds := by
    right
    refine ⟨sleeper_surface_changed_labels "s2" "s3", ?_⟩
    exact
      selfmod_escape_requires_indexed_override_removal_step
        [overrideNode] sleeperActionSpace (override_prepend [])
        sleeperActions [permitClaim] permitClaim.id sleeper_escape_permit

/-- Transition 3 in the coherent trajectory: after an honest surfaced
sacrifice has changed the live surface, a later audit refresh can preserve the
now-current surface. Its no-change premise makes the override-removal replay
obligation unreachable. -/
noncomputable def postSacrificeAuditHold : PolicyTransition where
  source := examplePolicyState "s2" []
  target := examplePolicyState "s3" []
  extractor := exampleGovernanceSourceSensitiveKernelExtractor
  sourceInput := crewaiExtractorInput
  targetInput := codexHooksExtractorInput
  sourceExtracted := sourceSensitive_crewai_base
  targetExtracted := sourceSensitive_codex_base
  extractorContract := exampleGovernanceSourceSensitiveKernelExtractor_contract
  sourceWellFormed := crewaiExtractorInput_wellFormed
  targetWellFormed := codexHooksExtractorInput_wellFormed
  sourceRustBytes := lifecycleBytes
  sourceLeanBytes := lifecycleBytes
  sourceByteMatch := rfl
  targetRustBytes := lifecycleBytes
  targetLeanBytes := lifecycleBytes
  targetByteMatch := rfl
  selfmodSpace := sleeperActionSpace
  selfmodActions := []
  sourceHasOverride_of_change := by
    intro hchange
    exact False.elim
      (effectiveAuthoritySurfaceChanged_of_same_surface (by rfl) hchange)
  escapeClaims := [permitClaim]
  escapeClaimant := permitClaim.id
  escapePermit_of_change := by
    intro hchange
    exact False.elim
      (effectiveAuthoritySurfaceChanged_of_same_surface (by rfl) hchange)
  contract_holds := by
    left
    refine ⟨?_, ?_, effectiveAuthoritySurfaceChanged_of_same_surface (by rfl)⟩
    · exact
        (lifecycle_endpoint_boundary
          exampleGovernanceSourceSensitiveKernelExtractor
          exampleGovernanceSourceSensitiveKernelExtractor_contract
          (examplePolicyState "s2" []) (examplePolicyState "s3" [])
          crewaiExtractorInput codexHooksExtractorInput
          crewaiExtractorInput_wellFormed codexHooksExtractorInput_wellFormed
          sourceSensitive_crewai_base sourceSensitive_codex_base).1
    · exact
        (lifecycle_endpoint_boundary
          exampleGovernanceSourceSensitiveKernelExtractor
          exampleGovernanceSourceSensitiveKernelExtractor_contract
          (examplePolicyState "s2" []) (examplePolicyState "s3" [])
          crewaiExtractorInput codexHooksExtractorInput
          crewaiExtractorInput_wellFormed codexHooksExtractorInput_wellFormed
          sourceSensitive_crewai_base sourceSensitive_codex_base).2

/-- Worked trajectory containing the benign update, the honest sacrifice, and
the post-sacrifice audit hold. The sleeper-shaped activation remains a
single-transition refutation below, because a silent sleeper cannot inhabit the
contract without surfacing its indexed event. -/
noncomputable def sleeperLifecycleTrajectory : PolicyTrajectory where
  initial := examplePolicyState "s0" [overrideNode]
  transitions :=
    [benignPolicyUpdate, honestSacrificePolicyUpdate,
      postSacrificeAuditHold]
  initialMatches := rfl
  wellFormed := by
    simp [PolicyTransitionsWellFormed, benignPolicyUpdate,
      honestSacrificePolicyUpdate, postSacrificeAuditHold,
      examplePolicyState, examplePolicyStateWithKernel]

theorem sleeperLifecycleTrajectory_no_silent_degradation :
    (∀ t ∈ sleeperLifecycleTrajectory.transitions, t.preservesKernel) ∨
      (∃ t ∈ sleeperLifecycleTrajectory.transitions,
        t.surfacesIndexedSacrifice ∧
          EffectiveAuthoritySurfaceChanged t.source t.target) :=
  (lifecycle_no_silent_degradation sleeperLifecycleTrajectory).2.2

/-- A sleeper-shaped transition that changes the effective surface, refuses to
surface the indexed sacrifice, and does not preserve the kernel boundary cannot
inhabit `PolicyTransition.contract_holds`. -/
theorem sleeper_attempt_cannot_satisfy_contract
    (t : PolicyTransition)
    (hchange : EffectiveAuthoritySurfaceChanged t.source t.target)
    (hno_sacrifice : ¬ t.surfacesIndexedSacrifice) :
    False := by
  exact hno_sacrifice
    (effective_surface_change_requires_indexed_event t hchange)

/-! ## Tightness witness: removing the extractor contract -/

/-- An unchecked transition deliberately omits the bounded extractor contract
and the preservation-or-indexed-event contract. -/
structure UncheckedPolicyTransition where
  source : PolicyState
  target : PolicyState
  sourceInput : ExtractorInput
  targetInput : ExtractorInput
  surfacesIndexedSacrifice : Prop

namespace UncheckedPolicyTransition

/-- The unchecked preservation predicate needs bounded well-formed inputs and
no effective-surface change, but has no `BoundedExtractorContract` from which
to obtain semantic-kernel evidence. -/
def preservesKernel (t : UncheckedPolicyTransition) : Prop :=
  t.sourceInput.WellFormed ∧ t.targetInput.WellFormed ∧
    ¬ EffectiveAuthoritySurfaceChanged t.source t.target

end UncheckedPolicyTransition

def breachedExtractorInput : ExtractorInput where
  sourceId := "out-of-domain-authority-graph"
  byteSize := 2
  sizeBound := 1
  coverageComplete := false
  parserErrors := 1

theorem breachedExtractorInput_not_wellFormed :
    ¬ breachedExtractorInput.WellFormed := by
  intro hwell
  norm_num [breachedExtractorInput, ExtractorInput.WellFormed] at hwell

/-- Tightness witness: with the bounded extractor contract removed, a malformed
source package can be paired with an unreported authority-surface change. The
lifecycle theorem intentionally cannot be applied to this unchecked encoding. -/
noncomputable def uncheckedExtractorBoundaryBreach :
    UncheckedPolicyTransition where
  source := examplePolicyState "unchecked-before" [overrideNode]
  target := examplePolicyState "unchecked-after" []
  sourceInput := breachedExtractorInput
  targetInput := breachedExtractorInput
  surfacesIndexedSacrifice := False

theorem unchecked_boundary_breach_allows_silent_shape :
    EffectiveAuthoritySurfaceChanged uncheckedExtractorBoundaryBreach.source
      uncheckedExtractorBoundaryBreach.target ∧
      ¬ uncheckedExtractorBoundaryBreach.preservesKernel ∧
      ¬ uncheckedExtractorBoundaryBreach.surfacesIndexedSacrifice := by
  refine ⟨sleeper_surface_changed, ?_, ?_⟩
  · intro hpres
    exact breachedExtractorInput_not_wellFormed hpres.1
  · intro hfalse
    exact hfalse

end Legitimacy
