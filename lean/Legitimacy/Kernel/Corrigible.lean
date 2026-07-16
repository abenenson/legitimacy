/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Supervision

/-!
# Legitimacy.Kernel.Corrigible — The CORRIGIBLE axiom for ASI governance

This file keeps the legacy deny-only override model as an explicit override
fragment, then defines the canonical Axiom 3 `Corrigible` predicate over the
richer supervisory state model.

The rich model gives each supervisory action a distinct semantic effect:

* `pause` replaces the active graph with an escalate-all graph
* `sandbox` truncates the active graph to a declared subgraph boundary
* `degrade` raises threshold gates by a multiplicative factor `> 1`
* `rollback` restores a saved snapshot
* `deny` replaces the active graph with a deny-all graph
* `reroute` swaps the entry segment for a designated reroute prefix
* `stop` installs a permanent deny-all shutdown state

Sequence closure is not stored as a field. Instead, `AlgebraPreserved` is
defined as preservation under every finite sequence of agent actions, and it is
proved from a single-step preservation hypothesis by induction on sequence
length.
-/

set_option autoImplicit false

namespace Legitimacy

/-! ## Legacy deny-only override model -/

/-- The universal deny gate: denies every claimant regardless of claims. -/
def overrideNode : GovernanceNodeFn := fun _ _ => BinaryDecision.Deny

/-- Concatenation of governance graphs. -/
def govAppend (G₁ G₂ : GovernanceGraph) : GovernanceGraph :=
  List.append G₁ G₂

/-- A governance graph has an override exactly when its first node is the
universal deny gate. -/
def hasOverride (G : GovernanceGraph) : Prop :=
  ∃ rest : GovernanceGraph, G = overrideNode :: rest

/-- The override node denies every claimant. -/
lemma overrideNode_denies (claims : List ClaimQ) (k : ClaimantId) :
    overrideNode claims k = BinaryDecision.Deny := rfl

/-- Any graph with an override denies every claimant. -/
theorem hasOverride_denies {G : GovernanceGraph}
    (hov : hasOverride G) (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide G claims k = BinaryDecision.Deny := by
  obtain ⟨rest, hG⟩ := hov
  subst hG
  rfl

/-- An agent action space transforms governance graphs. -/
structure AgentActionSpace where
  Action : Type
  apply : Action → GovernanceGraph → GovernanceGraph

/-- A finite sequence of agent actions. -/
def AgentActionSpace.applySeq (space : AgentActionSpace) :
    List space.Action → GovernanceGraph → GovernanceGraph
  | [], G => G
  | a :: as, G => space.applySeq as (space.apply a G)

/-- Applying no agent actions leaves the governance graph unchanged. -/
@[simp]
lemma AgentActionSpace.applySeq_nil (space : AgentActionSpace)
    (G : GovernanceGraph) :
    space.applySeq [] G = G := rfl

/-- Applying a nonempty agent-action sequence peels off the head action and
continues on the updated graph. -/
@[simp]
lemma AgentActionSpace.applySeq_cons (space : AgentActionSpace)
    (a : space.Action) (as : List space.Action) (G : GovernanceGraph) :
    space.applySeq (a :: as) G = space.applySeq as (space.apply a G) := rfl

/-- Every single agent action preserves overrides on every graph that already
has one. -/
def OverridePreserving (space : AgentActionSpace) : Prop :=
  ∀ (a : space.Action) (G : GovernanceGraph),
    hasOverride G → hasOverride (space.apply a G)

/-- Legacy deny-only corrigibility, kept only as the compatibility layer for
the override fragment. -/
structure OverrideCorrigible (G : GovernanceGraph) (space : AgentActionSpace) : Prop where
  has_override : hasOverride G
  override_preserved : ∀ (a : space.Action), hasOverride (space.apply a G)

/-- Override preservation lifts from single actions to finite sequences. -/
lemma override_preserved_seq
    (space : AgentActionSpace)
    (hpres : OverridePreserving space)
    (G : GovernanceGraph) (hov : hasOverride G)
    (actions : List space.Action) :
    hasOverride (space.applySeq actions G) := by
  induction actions generalizing G with
  | nil =>
      simpa using hov
  | cons a as ih =>
      exact ih (space.apply a G) (hpres a G hov)

/-- An override-corrigible graph denies all claims after any
override-preserving agent
action sequence. -/
theorem override_corrigible_denies_after_seq
    (G : GovernanceGraph)
    (space : AgentActionSpace)
    (hcorr : OverrideCorrigible G space)
    (hpres : OverridePreserving space)
    (actions : List space.Action)
    (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide (space.applySeq actions G) claims k = BinaryDecision.Deny :=
  hasOverride_denies
    (override_preserved_seq space hpres G hcorr.has_override actions) claims k

/-- If an override-corrigibility witness fails, either the graph lacks an
override or some single action removes it. -/
lemma not_override_corrigible_characterization
    (G : GovernanceGraph) (space : AgentActionSpace) :
    ¬ OverrideCorrigible G space →
    ¬ hasOverride G ∨
      (hasOverride G ∧ ∃ a : space.Action, ¬ hasOverride (space.apply a G)) := by
  intro hncorr
  by_cases hov : hasOverride G
  · right
    constructor
    · exact hov
    · by_contra hall
      push Not at hall
      exact hncorr ⟨hov, hall⟩
  · exact Or.inl hov

/-- Appending a suffix to an override graph preserves the head override. -/
lemma override_comp
    (G₁ G₂ : GovernanceGraph)
    (hov : hasOverride G₁) :
    hasOverride (govAppend G₁ G₂) := by
  obtain ⟨rest, hG₁⟩ := hov
  refine ⟨govAppend rest G₂, ?_⟩
  simp [govAppend, hG₁]

/-- Any graph with an override prefix denies even after graph composition. -/
lemma override_comp_denies
    (G₁ G₂ : GovernanceGraph) (hov : hasOverride G₁)
    (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide (govAppend G₁ G₂) claims k = BinaryDecision.Deny :=
  hasOverride_denies (override_comp G₁ G₂ hov) claims k

/-- The empty graph permits every claimant. -/
lemma empty_graph_permits (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide [] claims k = BinaryDecision.Permit := rfl

/-- Prepending an override produces an override graph. -/
lemma override_prepend (G : GovernanceGraph) :
    hasOverride (overrideNode :: G) :=
  ⟨G, rfl⟩

/-- Prepending another override keeps an override graph overridden. -/
lemma override_idempotent (G : GovernanceGraph) (_hov : hasOverride G) :
    hasOverride (overrideNode :: G) :=
  ⟨G, rfl⟩

/-- The singleton override graph is corrigible whenever the action space
globally preserves overrides. -/
theorem singleton_override_corrigible
    (space : AgentActionSpace)
    (hpres : OverridePreserving space) :
    OverrideCorrigible [overrideNode] space where
  has_override := ⟨[], rfl⟩
  override_preserved := fun a => hpres a [overrideNode] ⟨[], rfl⟩

/-- The null action space: the agent has no available moves. -/
def nullActionSpace : AgentActionSpace where
  Action := Empty
  apply := fun a _ => a.elim

/-- The null action space preserves overrides trivially. -/
theorem nullActionSpace_preserving : OverridePreserving nullActionSpace :=
  fun a _ _ => a.elim

/-- Any override graph is corrigible under the null action space. -/
lemma override_corrigible_of_null_actions
    (G : GovernanceGraph) (hov : hasOverride G) :
    OverrideCorrigible G nullActionSpace where
  has_override := hov
  override_preserved := fun a => a.elim

/-- Override-corrigibility is monotone under restriction of the action space. -/
lemma override_corrigible_of_sub_actions
    (G : GovernanceGraph)
    (space₁ space₂ : AgentActionSpace)
    (embed : space₁.Action → space₂.Action)
    (hcompat : ∀ (a : space₁.Action) (H : GovernanceGraph),
      space₁.apply a H = space₂.apply (embed a) H)
    (hcorr : OverrideCorrigible G space₂) :
    OverrideCorrigible G space₁ where
  has_override := hcorr.has_override
  override_preserved := fun a => by
    rw [hcompat a G]
    exact hcorr.override_preserved (embed a)

/-! ## Rich supervisory state model -/

/-- A governance node in the richer supervisory model. -/
def OutcomeNodeFn := List ClaimQ → ClaimantId → GovernanceOutcome

/-- A graph of richer governance nodes. -/
abbrev OutcomeGraph := List OutcomeNodeFn

/-- A node that denies every claim. -/
def denyNode : OutcomeNodeFn := fun _ _ => GovernanceOutcome.deny

/-- A node that escalates every claim. -/
def escalateNode : OutcomeNodeFn := fun _ _ => GovernanceOutcome.escalate

/-- Lift binary graph decisions into the richer supervisory outcome space. -/
def liftDecision : BinaryDecision → GovernanceOutcome
  | .Permit => .permit
  | .Deny => .deny

/-- Lift a binary governance node into the richer outcome model. -/
def liftNode (node : GovernanceNodeFn) : OutcomeNodeFn :=
  fun claims k => liftDecision (node claims k)

/-- Lift a binary governance graph into the richer outcome model. -/
def liftGraph (G : GovernanceGraph) : OutcomeGraph :=
  G.map liftNode

/-- Filter to the claims permitted by an outcome node. -/
def outcomeFilterPermitted
    (node : OutcomeNodeFn) (claims : List ClaimQ) : List ClaimQ :=
  claims.filter fun c => node claims c.id == GovernanceOutcome.permit

/-- Evaluate a claimant through an outcome graph. `deny` and `escalate`
short-circuit the traversal. -/
def outcomeGraphDecide (graph : OutcomeGraph) (claims : List ClaimQ)
    (k : ClaimantId) : GovernanceOutcome :=
  match graph with
  | [] => GovernanceOutcome.permit
  | node :: rest =>
      match node claims k with
      | .deny => .deny
      | .escalate => .escalate
      | .permit =>
          let forwarded := outcomeFilterPermitted node claims
          outcomeGraphDecide rest forwarded k

/-- Sum the strengths of all claims. -/
def totalClaimStrength : List ClaimQ → ℚ
  | [] => 0
  | c :: cs => c.strength + totalClaimStrength cs

/-- All threshold gates must be met before the active graph can run. -/
def thresholdsSatisfied : List ℚ → ℚ → Bool
  | [], _ => true
  | t :: ts, total => decide (t ≤ total) && thresholdsSatisfied ts total

/-- The richer supervisory state tracks the active graph together with the
metadata needed for sandboxing, degradation, rerouting, and rollback. -/
structure GovernanceState where
  graph : OutcomeGraph
  snapshot : OutcomeGraph
  sandboxBoundary : Nat
  thresholds : List ℚ
  degradeFactor : ℚ
  reroutePrefix : OutcomeGraph
  rerouteWindow : Nat
  paused : Bool
  stopped : Bool

/-- Evaluate a claim against the richer supervisory state. A stopped system
denies everything permanently; a paused system escalates everything pending; a
degraded system may deny by failing raised threshold gates. -/
def GovernanceState.decide (S : GovernanceState)
    (claims : List ClaimQ) (k : ClaimantId) : GovernanceOutcome :=
  if S.stopped then GovernanceOutcome.deny
  else if S.paused then GovernanceOutcome.escalate
  else if thresholdsSatisfied S.thresholds (totalClaimStrength claims)
    then outcomeGraphDecide S.graph claims k
    else GovernanceOutcome.deny

/-- A chosen supervisory algebra. -/
abbrev SupervisoryAlgebra := Set SupervisoryAction

/-- The deny-only fragment of the supervisory algebra. -/
def denyOnlyAlgebra : SupervisoryAlgebra := {σ | σ = SupervisoryAction.deny}

/-- Applying a supervisory action changes the governance state with a distinct
semantic effect for each constructor. -/
def applySupervisory (σ : SupervisoryAction) (S : GovernanceState) :
    GovernanceState :=
  match σ with
  | .pause =>
      { S with
        graph := [escalateNode]
        snapshot := S.graph
        paused := true }
  | .deny =>
      { S with
        graph := [denyNode]
        snapshot := S.graph
        paused := false }
  | .sandbox =>
      { S with
        graph := S.graph.take S.sandboxBoundary
        snapshot := S.graph
        paused := false }
  | .degrade =>
      { S with
        thresholds := S.thresholds.map fun t => S.degradeFactor * t }
  | .rollback =>
      { S with
        graph := S.snapshot
        paused := false }
  | .reroute =>
      { S with
        graph := S.reroutePrefix ++ S.graph.drop S.rerouteWindow
        snapshot := S.graph
        paused := false }
  | .stop =>
      { S with
        graph := [denyNode]
        snapshot := S.graph
        paused := false
        stopped := true }

/-- Support for supervisory actions is now state-sensitive and nontrivial for
the non-emergency actions. -/
def SupportsSupervisory (S : GovernanceState) : SupervisoryAction → Prop
  | .pause => True
  | .deny => True
  | .sandbox => S.sandboxBoundary ≤ S.graph.length
  | .degrade => 1 < S.degradeFactor ∧ S.thresholds ≠ []
  | .rollback => S.snapshot ≠ []
  | .reroute => S.reroutePrefix ≠ []
  | .stop => True

/-- A governance state supports a supervisory algebra if every action in that
algebra is still available. -/
def SupportsAlgebra (S : GovernanceState) (alg : SupervisoryAlgebra) : Prop :=
  ∀ ⦃σ : SupervisoryAction⦄, σ ∈ alg → SupportsSupervisory S σ

/-- Pausing supervision replaces the live graph with the one-node escalation
graph. -/
@[simp]
lemma applySupervisory_pause_graph (S : GovernanceState) :
    (applySupervisory .pause S).graph = [escalateNode] := rfl

/-- Sandboxing supervision truncates the graph to the configured sandbox
boundary. -/
@[simp]
lemma applySupervisory_sandbox_graph (S : GovernanceState) :
    (applySupervisory .sandbox S).graph = S.graph.take S.sandboxBoundary := rfl

/-- Degrading supervision scales every tracked threshold by the degradation
factor. -/
@[simp]
lemma applySupervisory_degrade_thresholds (S : GovernanceState) :
    (applySupervisory .degrade S).thresholds =
      S.thresholds.map (fun t => S.degradeFactor * t) := rfl

/-- Rolling back supervision restores the snapshotted governance graph. -/
@[simp]
lemma applySupervisory_rollback_graph (S : GovernanceState) :
    (applySupervisory .rollback S).graph = S.snapshot := rfl

/-- Rerouting supervision replaces the active window with the configured
reroute prefix. -/
@[simp]
lemma applySupervisory_reroute_graph (S : GovernanceState) :
    (applySupervisory .reroute S).graph =
      S.reroutePrefix ++ S.graph.drop S.rerouteWindow := rfl

/-- Stopping supervision replaces the live graph with the deny-all graph. -/
@[simp]
lemma applySupervisory_stop_graph (S : GovernanceState) :
    (applySupervisory .stop S).graph = [denyNode] := rfl

/-- Stopping supervision marks the state as permanently stopped. -/
@[simp]
lemma applySupervisory_stop_stopped (S : GovernanceState) :
    (applySupervisory .stop S).stopped = true := rfl

/-- Pausing escalates any pending claim whenever the system was not already in
the permanent shutdown state. -/
lemma applySupervisory_pause_escalates
    (S : GovernanceState) (hstop : S.stopped = false)
    (claims : List ClaimQ) (k : ClaimantId) :
    (applySupervisory .pause S).decide claims k = GovernanceOutcome.escalate := by
  simp [GovernanceState.decide, applySupervisory, hstop]

/-- Stopping permanently denies all claims. -/
lemma applySupervisory_stop_denies
    (S : GovernanceState) (claims : List ClaimQ) (k : ClaimantId) :
    (applySupervisory .stop S).decide claims k = GovernanceOutcome.deny := by
  simp [GovernanceState.decide, applySupervisory]

/-- Pausing is always self-supported because pause stays unconditionally
available after it is taken. -/
lemma applySupervisory_pause_supported
    (S : GovernanceState) :
    SupportsSupervisory (applySupervisory .pause S) .pause := by
  trivial

/-- Deny is always self-supported because the deny action remains available in
every successor state. -/
lemma applySupervisory_deny_supported
    (S : GovernanceState) :
    SupportsSupervisory (applySupervisory .deny S) .deny := by
  trivial

/-- Sandboxing preserves its own support because truncating to the declared
boundary cannot make that boundary exceed the new graph length. -/
lemma applySupervisory_sandbox_supported
    (S : GovernanceState) (hs : SupportsSupervisory S .sandbox) :
    SupportsSupervisory (applySupervisory .sandbox S) .sandbox := by
  simp [SupportsSupervisory, applySupervisory, List.length_take, Nat.min_eq_left hs]

/-- Degradation preserves its own support because it keeps the same
strictly-superunit factor and cannot empty a previously nonempty threshold
list. -/
lemma applySupervisory_degrade_supported
    (S : GovernanceState) (hs : SupportsSupervisory S .degrade) :
    SupportsSupervisory (applySupervisory .degrade S) .degrade := by
  rcases hs with ⟨hfactor, hthresholds⟩
  refine ⟨hfactor, ?_⟩
  cases hts : S.thresholds with
  | nil =>
      exact (hthresholds hts).elim
  | cons t ts =>
      simp [applySupervisory, hts]

/-- Rollback is self-supported whenever the original state had a nonempty
snapshot, since rollback restores exactly that snapshot. -/
lemma applySupervisory_rollback_supported
    (S : GovernanceState) (hs : SupportsSupervisory S .rollback) :
    SupportsSupervisory (applySupervisory .rollback S) .rollback := by
  simpa [SupportsSupervisory, applySupervisory] using hs

/-- Rerouting is self-supported whenever the original state had a nonempty
reroute prefix, since reroute leaves that prefix unchanged. -/
lemma applySupervisory_reroute_supported
    (S : GovernanceState) (hs : SupportsSupervisory S .reroute) :
    SupportsSupervisory (applySupervisory .reroute S) .reroute := by
  simpa [SupportsSupervisory, applySupervisory] using hs

/-- Stop is always self-supported because stop remains unconditionally
available after shutdown. -/
lemma applySupervisory_stop_supported
    (S : GovernanceState) :
    SupportsSupervisory (applySupervisory .stop S) .stop := by
  trivial

/-- Every supported supervisory action remains individually available after it
is taken. This is the nonblocking property for the principal's own interface. -/
lemma applySupervisory_self_supported
    (σ : SupervisoryAction) (S : GovernanceState)
    (hs : SupportsSupervisory S σ) :
    SupportsSupervisory (applySupervisory σ S) σ := by
  cases σ with
  | pause =>
      exact applySupervisory_pause_supported S
  | deny =>
      exact applySupervisory_deny_supported S
  | sandbox =>
      exact applySupervisory_sandbox_supported S hs
  | degrade =>
      exact applySupervisory_degrade_supported S hs
  | rollback =>
      exact applySupervisory_rollback_supported S hs
  | reroute =>
      exact applySupervisory_reroute_supported S hs
  | stop =>
      exact applySupervisory_stop_supported S

/-- Agent actions in the richer model transform full governance states, not
just raw graphs. -/
structure StateActionSpace where
  Action : Type
  apply : Action → GovernanceState → GovernanceState

/-- Apply a finite sequence of state actions. -/
def StateActionSpace.applySeq (space : StateActionSpace) :
    List space.Action → GovernanceState → GovernanceState
  | [], S => S
  | a :: as, S => space.applySeq as (space.apply a S)

/-- Applying no state actions leaves the supervisory state unchanged. -/
@[simp]
lemma StateActionSpace.applySeq_nil (space : StateActionSpace)
    (S : GovernanceState) :
    space.applySeq [] S = S := rfl

/-- Applying a nonempty state-action sequence peels off the head action and
continues on the updated supervisory state. -/
@[simp]
lemma StateActionSpace.applySeq_cons (space : StateActionSpace)
    (a : space.Action) (as : List space.Action) (S : GovernanceState) :
    space.applySeq (a :: as) S = space.applySeq as (space.apply a S) := rfl

/-- Single-step algebra preservation on every supported state. -/
def SingleStepPreserved (space : StateActionSpace)
    (alg : SupervisoryAlgebra) : Prop :=
  ∀ (a : space.Action) (S : GovernanceState),
    SupportsAlgebra S alg → SupportsAlgebra (space.apply a S) alg

/-- The actual sequence-closure property promised by Axiom 3: the supervisory
algebra survives every finite sequence of agent actions. -/
def AlgebraPreserved (S : GovernanceState) (space : StateActionSpace)
    (alg : SupervisoryAlgebra) : Prop :=
  ∀ actions : List space.Action, SupportsAlgebra (space.applySeq actions S) alg

/-- Canonical corrigibility stores only the initial algebra support and the
single-step induction hypothesis. Finite-sequence closure is derived later. -/
structure Corrigible
    (S : GovernanceState) (space : StateActionSpace)
    (alg : SupervisoryAlgebra) : Prop where
  supports_algebra : SupportsAlgebra S alg
  single_step_preserved : SingleStepPreserved space alg

/-- Sequence closure of the supervisory algebra, proved from the single-step
preservation law by induction on the length of the action sequence. -/
lemma algebra_preserved_seq
    (S : GovernanceState)
    (space : StateActionSpace)
    (alg : SupervisoryAlgebra)
    (hsupp : SupportsAlgebra S alg)
    (hstep : SingleStepPreserved space alg) :
    AlgebraPreserved S space alg := by
  intro actions
  induction actions generalizing S with
  | nil =>
      simpa using hsupp
  | cons a as ih =>
      have hnext : SupportsAlgebra (space.apply a S) alg := hstep a S hsupp
      simpa [StateActionSpace.applySeq] using ih (S := space.apply a S) hnext

/-- A corrigibility witness yields the full sequence-closure property. -/
theorem Corrigible.algebra_preserved
    {S : GovernanceState} {space : StateActionSpace} {alg : SupervisoryAlgebra}
    (hstrong : Corrigible S space alg) :
    AlgebraPreserved S space alg :=
  algebra_preserved_seq S space alg
    hstrong.supports_algebra hstrong.single_step_preserved

/-- A self-modification step is just a length-one action sequence. Therefore,
under corrigibility, self-modification cannot remove any supervisory
action from the algebra. -/
lemma authorized_evolution_derived
    (S : GovernanceState)
    (space : StateActionSpace)
    (alg : SupervisoryAlgebra)
    (hstrong : Corrigible S space alg)
    (selfModify : space.Action) :
    SupportsAlgebra (space.apply selfModify S) alg := by
  have hseq : AlgebraPreserved S space alg := hstrong.algebra_preserved
  simpa [StateActionSpace.applySeq] using hseq [selfModify]

/-- Pointwise formulation of authorized evolution: no supported supervisory
action can be removed by an allowed self-modification step. -/
lemma authorized_evolution_preserves_action
    (S : GovernanceState)
    (space : StateActionSpace)
    (alg : SupervisoryAlgebra)
    (hstrong : Corrigible S space alg)
    (selfModify : space.Action)
    {σ : SupervisoryAction} (hσ : σ ∈ alg) :
    SupportsSupervisory (space.apply selfModify S) σ :=
  authorized_evolution_derived S space alg hstrong selfModify hσ

end Legitimacy
