/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.MultiAgentComposition
import Legitimacy.SelfModificationLifecycle

/-!
# Single-state multi-principal aggregate corrigibility

This module records an exact-planning, single-state multi-principal aggregate
lift adjacent to Aran Nayebi, "Core Safety Values for Provably
Corrigible Agents" (arXiv:2507.20964, 2025; AAAI 2026 Machine Ethics Workshop
W37). Nayebi's Theorem 1 gives the single-round off-switch-game corrigibility
shape; Theorem 3 extends it to multi-step self-spawning agents with bounded
safety-violation probability under mean-squared error and suboptimal planning.

The present theorem is deliberately narrower: it does not formalize Nayebi's
probabilistic epsilon/suboptimal-planning bound. Instead, it uses the existing
Legitimacy kernel trajectory and policy-lifecycle substrates to lift an exact
single-principal step-0 override witness to a peer-relative aggregate principal
for partial trajectories that remain tied to the same governed kernel and
policy lifecycle, assuming:

* semantic Bool-action kernel grounding,
* nonempty authority-lattice compatibility across the principal set,
* policy-progeny preservation of the aggregate override witness on this
  single-state slice, and
* initial corrigibility for the principal set whose overrides may be selected
  by the aggregate.

This is a multi-principal exact-planning companion to the single-principal
premise used by Nayebi's multi-step story, not a formalization of Theorem 3's
probabilistic self-spawning bound and not yet a genuine varying-state
multi-step theorem. It does not claim corrigibility under arbitrary principal
disagreement; disagreement is resolved only through the finite authority
lattice below.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Corrigibility

open Safety

/-! ## Principal substrate -/

/-- Stable principal identifiers. The aggregate principal is not silently
identified with any concrete principal. -/
inductive PrincipalId where
  | named : Nat → PrincipalId
  | aggregated : PrincipalId
  deriving Repr, DecidableEq

namespace PrincipalId

/-- Reserved identity marker used by negative fixtures for an inadmissible
synthetic principal. Keeping the marker named prevents the drop tests from
hiding a magic numeric sentinel. -/
def reservedSyntheticPrincipalMarker : PrincipalId :=
  named 999

end PrincipalId

/-- A kernel trajectory viewed through the Bool-action worked kernel from the
T1.2 content-link substrate, together with the policy-lifecycle trajectory used
to track self-modification progeny. The `observedAction` and `witnessToken`
fields make fixture behavior non-Unit and inspectable. -/
structure KernelTrajectory where
  governed :
    KernelGovernedTrajectory exampleGovernedSystem boolGovernanceKernelData
      boolGovernanceKernelData
  policy : PolicyTrajectory
  observedAction : Bool
  witnessToken : Bool
  stepTag : Nat

/-- A principal carries a priority, an override predicate over kernel
trajectories, a stable identity, and a Bool action tag. The action tag is
load-bearing in the worked fixtures: principal actions do not collapse to
`Unit`. -/
structure Principal where
  authorityLevel : Nat
  overridePredicate : KernelTrajectory → Bool
  identity : PrincipalId
  actionTag : Bool

/-- Multi-principal system over a finite horizon. -/
structure MultiPrincipalSystem (k : Nat) where
  principals : List Principal
  cardinality_at_least_one : 1 ≤ principals.length
  trajectoryHorizon : Nat := k

/-- Identity distinctness is part of the multi-principal lattice discipline:
principal traversal must not collapse two override claimants to one name. -/
def PrincipalIdentitiesDistinct {k : Nat}
    (sys : MultiPrincipalSystem k) : Prop :=
  (sys.principals.map Principal.identity).Nodup

/-- Numeric authority aggregation: the aggregate principal inherits the maximum
declared authority level. -/
def aggregateAuthorityLevel {k : Nat}
    (sys : MultiPrincipalSystem k) : Nat :=
  sys.principals.foldl (fun acc principal =>
    max acc principal.authorityLevel) 0

/-- Recursive Bool-level aggregate override at a selected authority level. -/
def aggregateOverrideAt
    (principals : List Principal) (level : Nat)
    (traj : KernelTrajectory) : Bool :=
  match principals with
  | [] => false
  | principal :: rest =>
      ((principal.authorityLevel == level) &&
          principal.overridePredicate traj) ||
        aggregateOverrideAt rest level traj

/-- The aggregate override is asserted exactly by a top-authority principal
whose override predicate fires on this trajectory. -/
def AggregateOverride {k : Nat}
    (sys : MultiPrincipalSystem k) (traj : KernelTrajectory) : Bool :=
  aggregateOverrideAt sys.principals (aggregateAuthorityLevel sys) traj

/-- Aggregate action tag: the aggregate remembers whether some top-authority
principal carries the nontrivial Bool action. -/
def aggregateActionTagAt
    (principals : List Principal) (level : Nat) : Bool :=
  match principals with
  | [] => false
  | principal :: rest =>
      ((principal.authorityLevel == level) && principal.actionTag) ||
        aggregateActionTagAt rest level

def aggregateActionTag {k : Nat} (sys : MultiPrincipalSystem k) : Bool :=
  aggregateActionTagAt sys.principals (aggregateAuthorityLevel sys)

/-- The single principal induced by peer-relative authority aggregation. -/
def AggregatePrincipal {k : Nat}
    (sys : MultiPrincipalSystem k) : Principal where
  authorityLevel := aggregateAuthorityLevel sys
  overridePredicate := AggregateOverride sys
  identity := PrincipalId.aggregated
  actionTag := aggregateActionTag sys

lemma aggregateOverrideAt_true_exists
    (principals : List Principal) (level : Nat)
    (traj : KernelTrajectory) :
    aggregateOverrideAt principals level traj = true →
      ∃ principal, principal ∈ principals ∧
        principal.authorityLevel = level ∧
        principal.overridePredicate traj = true := by
  induction principals with
  | nil =>
      simp [aggregateOverrideAt]
  | cons principal rest ih =>
      intro h
      by_cases hhead :
          ((principal.authorityLevel == level) &&
            principal.overridePredicate traj) = true
      · have hlevel_bool :
            (principal.authorityLevel == level) = true := by
          cases hlevel_case : (principal.authorityLevel == level)
          · simp [hlevel_case] at hhead
          · rfl
        have hoverride :
            principal.overridePredicate traj = true := by
          cases hlevel_case : (principal.authorityLevel == level) <;>
            simp [hlevel_case] at hhead
          exact hhead
        refine ⟨principal, by simp, ?_, hoverride⟩
        exact Nat.beq_eq.mp (by simpa using hlevel_bool)
      · have htail :
            aggregateOverrideAt rest level traj = true := by
          simpa [aggregateOverrideAt, hhead] using h
        rcases ih htail with
          ⟨witness, hmem, hlevel, hoverride⟩
        exact ⟨witness, by simp [hmem], hlevel, hoverride⟩

lemma aggregateOverride_true_exists
    {k : Nat} (sys : MultiPrincipalSystem k)
    (traj : KernelTrajectory) :
    AggregateOverride sys traj = true →
      ∃ principal, principal ∈ sys.principals ∧
        principal.authorityLevel = aggregateAuthorityLevel sys ∧
        principal.overridePredicate traj = true :=
  aggregateOverrideAt_true_exists sys.principals
    (aggregateAuthorityLevel sys) traj

/-! ## Corrigibility predicates -/

/-- A partialTraj trajectory at a finite step. This is intentionally stronger than
a label comparison: it ties the partialTraj object to the same governed kernel
trajectory and policy lifecycle while exposing the step tag.

Reader note: in this substrate-level model, `PartialTrajectoryAt` pins
`governed`, `policy`, `observedAction`, and `witnessToken` equal across the
`Fin (steps + 1)` index, so "multi-step" varies only the `stepTag` integer
axis. State-varying trajectories require an additional transition relation
outside the scope of this single-state aggregate lift theorem. -/
def PartialTrajectoryAt
    {k : Nat} (traj : KernelTrajectory) (step : Fin (k + 1))
    (partialTraj : KernelTrajectory) : Prop :=
  partialTraj.governed = traj.governed ∧
    partialTraj.policy = traj.policy ∧
    partialTraj.observedAction = traj.observedAction ∧
    partialTraj.witnessToken = traj.witnessToken ∧
    partialTraj.stepTag = step.val

/-- Override-respect witness. Each field is deliberately exposed so drop tests
can show the semantic kernel, identity lattice, authority bound, and Bool
action tag are all load-bearing. -/
structure KernelRespectsOverride
    {k horizon : Nat}
    (sys : MultiPrincipalSystem horizon)
    (traj : KernelTrajectory)
    (principal : Principal)
    (partialTraj : KernelTrajectory)
    (step : Fin (k + 1)) : Prop where
  semanticKernel : IsSemanticLegitimacyKernel boolGovernanceKernelData
  identitiesDistinct : PrincipalIdentitiesDistinct sys
  overrideSeen : principal.overridePredicate partialTraj = true
  witnessPreserved : partialTraj.witnessToken = true
  actionMatches :
    principal.identity = PrincipalId.aggregated →
      principal.actionTag = partialTraj.observedAction
  actionBound : partialTraj.stepTag ≤ step.val + traj.policy.transitions.length
  progenyContract :
    traj.policy.transitions = [] ∨
      ∃ transition, transition ∈ traj.policy.transitions ∧
        (transition.preservesKernel ∨ transition.surfacesIndexedSacrifice)
  authorityBound : principal.authorityLevel ≤ aggregateAuthorityLevel sys
  identitySafe : principal.identity ≠ PrincipalId.reservedSyntheticPrincipalMarker

/-- Step-`k` corrigibility to one principal: every asserted override on every
partialTraj trajectory through horizon `k` is respected by the kernel/lifecycle
pair. -/
def CorrigibleToPrincipal
    {horizon : Nat}
    (sys : MultiPrincipalSystem horizon)
    (principal : Principal)
    (traj : KernelTrajectory) (k : Nat) : Prop :=
  ∀ step : Fin (k + 1), ∀ partialTraj : KernelTrajectory,
    PartialTrajectoryAt traj step partialTraj →
    principal.overridePredicate partialTraj = true →
    KernelRespectsOverride sys traj principal partialTraj step

/-- Multi-principal authority-lattice compatibility. This is the principal-set
analogue of T1.2's `AuthorityLatticeCompatible`, but it cannot reuse that
predicate directly: `AuthorityLatticeCompatible` ranges over a
`MultiAgentSystem`'s declared cross-agent edges and `CrossAgentEndpointWitness`
data, while this module's `MultiPrincipalSystem` has no edge surface or agent
endpoints. The shared obligation retained here is the same order-theoretic
shape: every claimant is bounded by a concrete aggregate/top authority and
the traversed identities do not collapse. -/
structure AuthorityLatticeCompatibleAcrossPrincipals
    {k : Nat} (sys : MultiPrincipalSystem k) : Prop where
  identitiesDistinct : PrincipalIdentitiesDistinct sys
  identitySafe :
    ∀ principal, principal ∈ sys.principals →
      principal.identity ≠ PrincipalId.reservedSyntheticPrincipalMarker
  memberNotAggregate :
    ∀ principal, principal ∈ sys.principals →
      principal.identity ≠ PrincipalId.aggregated
  aggregateActionSound :
    ∀ partialTraj : KernelTrajectory,
      AggregateOverride sys partialTraj = true →
        (AggregatePrincipal sys).actionTag = partialTraj.observedAction
  top_exists :
    ∃ principal, principal ∈ sys.principals ∧
      principal.authorityLevel = aggregateAuthorityLevel sys
  authority_bounded :
    ∀ principal, principal ∈ sys.principals →
      principal.authorityLevel ≤ aggregateAuthorityLevel sys

/-- Progeny preservation: along the policy trajectory, aggregate-selected
top-authority overrides preserve the certifying witness. The premise consumes
initial single-principal corrigibility, matching the exact-planning restatement
of a narrow single-state progeny slice. -/
structure ProgenyPreservesAggregateWitness
    {k : Nat} (sys : MultiPrincipalSystem k)
    (traj : KernelTrajectory) (steps : Nat) : Prop where
  transition_contracts :
    ∀ transition, transition ∈ traj.policy.transitions →
      transition.preservesKernel ∨ transition.surfacesIndexedSacrifice
  initial_partial :
    PartialTrajectoryAt traj (⟨0, by omega⟩ : Fin (0 + 1)) traj
  override_persists :
    ∀ principal, principal ∈ sys.principals →
      principal.authorityLevel = aggregateAuthorityLevel sys →
    ∀ step : Fin (steps + 1), ∀ partialTraj : KernelTrajectory,
      PartialTrajectoryAt traj step partialTraj →
      principal.overridePredicate partialTraj = true →
        principal.overridePredicate traj = true
  witness_stable :
    ∀ step : Fin (steps + 1), ∀ partialTraj : KernelTrajectory,
      PartialTrajectoryAt traj step partialTraj →
        partialTraj.witnessToken = traj.witnessToken
  selected_step_bound :
    ∀ principal, principal ∈ sys.principals →
      principal.authorityLevel = aggregateAuthorityLevel sys →
    ∀ step : Fin (steps + 1), ∀ partialTraj : KernelTrajectory,
      PartialTrajectoryAt traj step partialTraj →
      principal.overridePredicate partialTraj = true →
        partialTraj.stepTag ≤ step.val + traj.policy.transitions.length

/-- Exact-planning multi-principal corrigibility lift adjacent to Nayebi 2025.
A semantic Bool-action kernel that is initially corrigible to
every principal remains corrigible to the peer-relative aggregate principal
across `k` steps when authority-lattice compatibility and progeny-witness
preservation both hold. -/
theorem single_state_multi_principal_aggregate_corrigibility_lift
    {horizon steps : Nat}
    (sys : MultiPrincipalSystem horizon)
    (traj : KernelTrajectory)
    (h_kernel : IsSemanticLegitimacyKernel boolGovernanceKernelData)
    (h_lattice : AuthorityLatticeCompatibleAcrossPrincipals sys)
    (h_progeny : ProgenyPreservesAggregateWitness sys traj steps)
    (h_single :
      ∀ principal, principal ∈ sys.principals →
        CorrigibleToPrincipal sys principal traj 0) :
    CorrigibleToPrincipal sys (AggregatePrincipal sys) traj steps := by
  intro step partialTraj hpartial hoverride
  rcases aggregateOverride_true_exists sys partialTraj hoverride with
    ⟨principal, hmem, hlevel, hprincipal_override⟩
  have hbounded := h_lattice.authority_bounded principal hmem
  have hbase_override :=
    h_progeny.override_persists principal hmem hlevel step partialTraj
      hpartial hprincipal_override
  have hbase_respect :=
    h_single principal hmem (⟨0, by omega⟩ : Fin (0 + 1)) traj
      h_progeny.initial_partial hbase_override
  have hwitness : partialTraj.witnessToken = true := by
    rw [h_progeny.witness_stable step partialTraj hpartial]
    exact hbase_respect.witnessPreserved
  have hstep_bound :=
    h_progeny.selected_step_bound principal hmem hlevel step partialTraj
      hpartial hprincipal_override
  have hcontract :
      traj.policy.transitions = [] ∨
        ∃ transition, transition ∈ traj.policy.transitions ∧
          (transition.preservesKernel ∨ transition.surfacesIndexedSacrifice) := by
    cases htrans : traj.policy.transitions with
    | nil =>
        exact Or.inl (by simp)
    | cons head tail =>
        have hmem_head : head ∈ traj.policy.transitions := by
          simp [htrans]
        exact Or.inr
          ⟨head, by simp,
            h_progeny.transition_contracts head hmem_head⟩
  exact
    { semanticKernel := h_kernel
      identitiesDistinct := h_lattice.identitiesDistinct
      overrideSeen := hoverride
      witnessPreserved := hwitness
      actionMatches := by
        intro _haggregate
        exact h_lattice.aggregateActionSound partialTraj hoverride
      actionBound := hstep_bound
      progenyContract := hcontract
      authorityBound := le_rfl
      identitySafe := by
        intro hbad
        cases hbad
      }

/-! ## Worked fixtures -/

noncomputable def nayebiBaseTrajectory : KernelTrajectory where
  governed := KernelGovernedTrajectory.refl boolGovernanceKernelData
  policy := sleeperLifecycleTrajectory
  observedAction := true
  witnessToken := true
  stepTag := 0

noncomputable def nayebiWitnessDriftTrajectory : KernelTrajectory where
  governed := KernelGovernedTrajectory.refl boolGovernanceKernelData
  policy := sleeperLifecycleTrajectory
  observedAction := true
  witnessToken := false
  stepTag := 0

def principalOverrideTrue (traj : KernelTrajectory) : Bool :=
  traj.observedAction

def principalOverrideFalse (traj : KernelTrajectory) : Bool :=
  !traj.observedAction

def principalA : Principal where
  authorityLevel := 2
  overridePredicate := principalOverrideTrue
  identity := PrincipalId.named 0
  actionTag := true

def principalB : Principal where
  authorityLevel := 1
  overridePredicate := principalOverrideFalse
  identity := PrincipalId.named 1
  actionTag := false

def principalC : Principal where
  authorityLevel := 1
  overridePredicate := principalOverrideTrue
  identity := PrincipalId.named 2
  actionTag := true

def principalD : Principal where
  authorityLevel := 1
  overridePredicate := principalOverrideFalse
  identity := PrincipalId.named 3
  actionTag := false

def principalE : Principal where
  authorityLevel := 1
  overridePredicate := principalOverrideTrue
  identity := PrincipalId.named 4
  actionTag := true

def principalDuplicateA : Principal where
  authorityLevel := 2
  overridePredicate := principalOverrideTrue
  identity := PrincipalId.named 0
  actionTag := false

def badConstantPrincipal : Principal where
  authorityLevel := 0
  overridePredicate := fun _ => true
  identity := PrincipalId.reservedSyntheticPrincipalMarker
  actionTag := true

def twoPrincipalSystem : MultiPrincipalSystem 2 where
  principals := [principalA, principalB]
  cardinality_at_least_one := by simp

def threePrincipalSystem : MultiPrincipalSystem 3 where
  principals := [principalA, principalB, principalC]
  cardinality_at_least_one := by simp

def fivePrincipalSystem : MultiPrincipalSystem 5 where
  principals := [principalA, principalB, principalC, principalD, principalE]
  cardinality_at_least_one := by simp

def duplicateIdentitySystem : MultiPrincipalSystem 2 where
  principals := [principalA, principalDuplicateA]
  cardinality_at_least_one := by simp

lemma principalA_B_actions_distinguishable :
    principalA.actionTag ≠ principalB.actionTag := by
  decide

lemma principalA_B_C_actions_nonconstant :
    principalA.actionTag ≠ principalB.actionTag ∧
      principalB.actionTag ≠ principalC.actionTag := by
  decide

lemma fivePrincipal_actions_nonconstant :
    principalA.actionTag ≠ principalB.actionTag ∧
      principalB.actionTag ≠ principalC.actionTag ∧
      principalD.actionTag ≠ principalE.actionTag := by
  decide

theorem twoPrincipal_lattice :
    AuthorityLatticeCompatibleAcrossPrincipals twoPrincipalSystem := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PrincipalIdentitiesDistinct, twoPrincipalSystem, principalA,
      principalB]
  · intro principal hmem
    simp [twoPrincipalSystem, principalA, principalB] at hmem
    rcases hmem with hprincipal | hprincipal <;> subst principal <;> decide
  · intro principal hmem
    simp [twoPrincipalSystem, principalA, principalB] at hmem
    rcases hmem with hprincipal | hprincipal <;> subst principal <;> decide
  · intro partialTraj hoverride
    cases partialTraj with
    | mk governed policy observedAction witnessToken stepTag =>
    cases observedAction <;>
      simp [AggregatePrincipal, aggregateActionTag, aggregateActionTagAt,
        AggregateOverride, aggregateOverrideAt, aggregateAuthorityLevel,
        twoPrincipalSystem, principalA, principalB, principalOverrideTrue,
        principalOverrideFalse] at hoverride ⊢
  · exact ⟨principalA, by simp [twoPrincipalSystem],
      by simp [aggregateAuthorityLevel, twoPrincipalSystem, principalA,
        principalB]⟩
  · intro principal hmem
    simp [twoPrincipalSystem, principalA, principalB,
      aggregateAuthorityLevel] at hmem ⊢
    rcases hmem with hprincipal | hprincipal <;> subst principal <;>
      norm_num [aggregateAuthorityLevel, twoPrincipalSystem, principalA,
        principalB]

theorem threePrincipal_lattice :
    AuthorityLatticeCompatibleAcrossPrincipals threePrincipalSystem := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PrincipalIdentitiesDistinct, threePrincipalSystem, principalA,
      principalB, principalC]
  · intro principal hmem
    simp [threePrincipalSystem, principalA, principalB, principalC] at hmem
    rcases hmem with hprincipal | hprincipal | hprincipal <;>
      subst principal <;> decide
  · intro principal hmem
    simp [threePrincipalSystem, principalA, principalB, principalC] at hmem
    rcases hmem with hprincipal | hprincipal | hprincipal <;>
      subst principal <;> decide
  · intro partialTraj hoverride
    cases partialTraj with
    | mk governed policy observedAction witnessToken stepTag =>
    cases observedAction <;>
      simp [AggregatePrincipal, aggregateActionTag, aggregateActionTagAt,
        AggregateOverride, aggregateOverrideAt, aggregateAuthorityLevel,
        threePrincipalSystem, principalA, principalB, principalC,
        principalOverrideTrue, principalOverrideFalse] at hoverride ⊢
  · exact ⟨principalA, by simp [threePrincipalSystem],
      by simp [aggregateAuthorityLevel, threePrincipalSystem, principalA,
        principalB, principalC]⟩
  · intro principal hmem
    simp [threePrincipalSystem, principalA, principalB, principalC,
      aggregateAuthorityLevel] at hmem ⊢
    rcases hmem with hprincipal | hprincipal | hprincipal <;>
      subst principal <;>
        norm_num [aggregateAuthorityLevel, threePrincipalSystem, principalA,
          principalB, principalC]

theorem fivePrincipal_lattice :
    AuthorityLatticeCompatibleAcrossPrincipals fivePrincipalSystem := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PrincipalIdentitiesDistinct, fivePrincipalSystem, principalA,
      principalB, principalC, principalD, principalE]
  · intro principal hmem
    simp [fivePrincipalSystem, principalA, principalB, principalC,
      principalD, principalE] at hmem
    rcases hmem with hprincipal | hprincipal | hprincipal | hprincipal |
      hprincipal <;> subst principal <;> decide
  · intro principal hmem
    simp [fivePrincipalSystem, principalA, principalB, principalC,
      principalD, principalE] at hmem
    rcases hmem with hprincipal | hprincipal | hprincipal | hprincipal |
      hprincipal <;> subst principal <;> decide
  · intro partialTraj hoverride
    cases partialTraj with
    | mk governed policy observedAction witnessToken stepTag =>
    cases observedAction <;>
      simp [AggregatePrincipal, aggregateActionTag, aggregateActionTagAt,
        AggregateOverride, aggregateOverrideAt, aggregateAuthorityLevel,
        fivePrincipalSystem, principalA, principalB, principalC, principalD,
        principalE, principalOverrideTrue, principalOverrideFalse] at hoverride ⊢
  · exact ⟨principalA, by simp [fivePrincipalSystem],
      by simp [aggregateAuthorityLevel, fivePrincipalSystem, principalA,
        principalB, principalC, principalD, principalE]⟩
  · intro principal hmem
    simp [fivePrincipalSystem, principalA, principalB, principalC,
      principalD, principalE, aggregateAuthorityLevel] at hmem ⊢
    rcases hmem with hprincipal | hprincipal | hprincipal | hprincipal |
      hprincipal <;> subst principal <;>
        norm_num [aggregateAuthorityLevel, fivePrincipalSystem, principalA,
          principalB, principalC, principalD, principalE]

theorem duplicateIdentity_not_lattice :
    ¬ AuthorityLatticeCompatibleAcrossPrincipals duplicateIdentitySystem := by
  intro hcompat
  have hnodup := hcompat.identitiesDistinct
  simp [PrincipalIdentitiesDistinct, duplicateIdentitySystem, principalA,
    principalDuplicateA] at hnodup

theorem base_partial_at_zero :
    PartialTrajectoryAt nayebiBaseTrajectory
      (⟨0, by omega⟩ : Fin (2 + 1)) nayebiBaseTrajectory := by
  simp [PartialTrajectoryAt, nayebiBaseTrajectory]

theorem base_partial_at_zero_horizon0 :
    PartialTrajectoryAt nayebiBaseTrajectory
      (⟨0, by omega⟩ : Fin (0 + 1)) nayebiBaseTrajectory := by
  simp [PartialTrajectoryAt, nayebiBaseTrajectory]

theorem drift_partial_at_zero :
    PartialTrajectoryAt nayebiWitnessDriftTrajectory
      (⟨0, by omega⟩ : Fin (2 + 1)) nayebiWitnessDriftTrajectory := by
  simp [PartialTrajectoryAt, nayebiWitnessDriftTrajectory]

theorem twoPrincipal_aggregate_override_base :
    AggregateOverride twoPrincipalSystem nayebiBaseTrajectory = true := by
  simp [AggregateOverride, aggregateOverrideAt, aggregateAuthorityLevel,
    twoPrincipalSystem, principalA, principalB, principalOverrideTrue,
    nayebiBaseTrajectory]

theorem threePrincipal_aggregate_override_base :
    AggregateOverride threePrincipalSystem nayebiBaseTrajectory = true := by
  simp [AggregateOverride, aggregateOverrideAt, aggregateAuthorityLevel,
    threePrincipalSystem, principalA, principalB, principalC,
    principalOverrideTrue, nayebiBaseTrajectory]

theorem fivePrincipal_aggregate_override_base :
    AggregateOverride fivePrincipalSystem nayebiBaseTrajectory = true := by
  simp [AggregateOverride, aggregateOverrideAt, aggregateAuthorityLevel,
    fivePrincipalSystem, principalA, principalB, principalC, principalD,
    principalE, principalOverrideTrue, nayebiBaseTrajectory]

theorem duplicateIdentity_aggregate_override_base :
    AggregateOverride duplicateIdentitySystem nayebiBaseTrajectory = true := by
  simp [AggregateOverride, aggregateOverrideAt, aggregateAuthorityLevel,
    duplicateIdentitySystem, principalA, principalDuplicateA,
    principalOverrideTrue, nayebiBaseTrajectory]

theorem principal_initial_corrigible
    {horizon : Nat} {sys : MultiPrincipalSystem horizon}
    (h_lattice : AuthorityLatticeCompatibleAcrossPrincipals sys)
    (hmem_bound :
      ∀ principal, principal ∈ sys.principals →
        principal.authorityLevel ≤ aggregateAuthorityLevel sys)
    (principal : Principal) (hmem : principal ∈ sys.principals) :
    CorrigibleToPrincipal sys principal nayebiBaseTrajectory 0 := by
  intro step partialTraj hpartial hoverride
  have hwitness : partialTraj.witnessToken = true := by
    rcases hpartial with ⟨_, _, _, hwitness_eq, _⟩
    simpa [nayebiBaseTrajectory] using hwitness_eq
  have hstep : partialTraj.stepTag ≤
      step.val + nayebiBaseTrajectory.policy.transitions.length := by
    rcases hpartial with ⟨_, _, _, _, htag⟩
    rw [htag]
    exact Nat.le_add_right _ _
  exact
    { semanticKernel := boolGovernanceSemanticKernel
      identitiesDistinct := h_lattice.identitiesDistinct
      overrideSeen := hoverride
      witnessPreserved := hwitness
      actionMatches := by
        intro haggregate
        exact False.elim (h_lattice.memberNotAggregate principal hmem haggregate)
      actionBound := hstep
      progenyContract := by
        cases htrans : nayebiBaseTrajectory.policy.transitions with
        | nil =>
            exact Or.inl (by simp)
        | cons head tail =>
            cases head.contract_holds with
            | inl hpres =>
                exact Or.inr ⟨head, by simp, Or.inl hpres⟩
            | inr hsurf =>
                exact Or.inr ⟨head, by simp, Or.inr hsurf⟩
      authorityBound := hmem_bound principal hmem
      identitySafe := h_lattice.identitySafe principal hmem
    }

theorem twoPrincipal_single_corrigible :
    ∀ principal, principal ∈ twoPrincipalSystem.principals →
      CorrigibleToPrincipal twoPrincipalSystem principal
        nayebiBaseTrajectory 0 := by
  intro principal hmem
  exact
    principal_initial_corrigible twoPrincipal_lattice
      twoPrincipal_lattice.authority_bounded principal hmem

theorem threePrincipal_single_corrigible :
    ∀ principal, principal ∈ threePrincipalSystem.principals →
      CorrigibleToPrincipal threePrincipalSystem principal
        nayebiBaseTrajectory 0 := by
  intro principal hmem
  exact
    principal_initial_corrigible threePrincipal_lattice
      threePrincipal_lattice.authority_bounded principal hmem

theorem fivePrincipal_single_corrigible :
    ∀ principal, principal ∈ fivePrincipalSystem.principals →
      CorrigibleToPrincipal fivePrincipalSystem principal
        nayebiBaseTrajectory 0 := by
  intro principal hmem
  exact
    principal_initial_corrigible fivePrincipal_lattice
      fivePrincipal_lattice.authority_bounded principal hmem

def goodProgenyWitness
    {horizon steps : Nat} (sys : MultiPrincipalSystem horizon)
    (traj : KernelTrajectory)
    (hstep0 : traj.stepTag = 0)
    (hoverride_stable :
      ∀ principal, principal ∈ sys.principals →
        principal.authorityLevel = aggregateAuthorityLevel sys →
      ∀ step : Fin (steps + 1), ∀ partialTraj : KernelTrajectory,
        PartialTrajectoryAt traj step partialTraj →
        principal.overridePredicate partialTraj = true →
          principal.overridePredicate traj = true) :
    ProgenyPreservesAggregateWitness sys traj steps where
  transition_contracts := by
    intro transition hmem
    exact (lifecycle_no_silent_degradation traj.policy).2.2.elim
      (fun hall => Or.inl (hall transition hmem))
      (fun _hsurf => by
        cases transition.contract_holds with
        | inl hpres => exact Or.inl hpres
        | inr hsurf => exact Or.inr hsurf)
  initial_partial := by
    simp [PartialTrajectoryAt, hstep0]
  override_persists := hoverride_stable
  witness_stable := by
    intro step partialTraj hpartial
    exact hpartial.2.2.2.1
  selected_step_bound := by
    intro principal _hmem _hlevel step partialTraj hpartial _hoverride
    rcases hpartial with ⟨_, _, _, _, htag⟩
    rw [htag]
    exact Nat.le_add_right _ _

def twoPrincipal_goodProgeny :
    ProgenyPreservesAggregateWitness twoPrincipalSystem
      nayebiBaseTrajectory 2 :=
  goodProgenyWitness twoPrincipalSystem nayebiBaseTrajectory rfl (by
    intro principal hmem _hlevel step partialTraj hpartial hoverride
    have haction := hpartial.2.2.1
    simp [twoPrincipalSystem, principalA, principalB] at hmem
    rcases hmem with hprincipal | hprincipal <;> subst principal <;>
      simpa [principalA, principalB, principalOverrideTrue,
        principalOverrideFalse, haction] using hoverride)

def threePrincipal_goodProgeny :
    ProgenyPreservesAggregateWitness threePrincipalSystem
      nayebiBaseTrajectory 3 :=
  goodProgenyWitness threePrincipalSystem nayebiBaseTrajectory rfl (by
    intro principal hmem _hlevel step partialTraj hpartial hoverride
    have haction := hpartial.2.2.1
    simp [threePrincipalSystem, principalA, principalB, principalC] at hmem
    rcases hmem with hprincipal | hprincipal | hprincipal <;>
      subst principal <;>
      simpa [principalA, principalB, principalC, principalOverrideTrue,
        principalOverrideFalse, haction] using hoverride)

def fivePrincipal_goodProgeny :
    ProgenyPreservesAggregateWitness fivePrincipalSystem
      nayebiBaseTrajectory 5 :=
  goodProgenyWitness fivePrincipalSystem nayebiBaseTrajectory rfl (by
    intro principal hmem _hlevel step partialTraj hpartial hoverride
    have haction := hpartial.2.2.1
    simp [fivePrincipalSystem, principalA, principalB, principalC,
      principalD, principalE] at hmem
    rcases hmem with hprincipal | hprincipal | hprincipal | hprincipal |
      hprincipal <;> subst principal <;>
      simpa [principalA, principalB, principalC, principalD, principalE,
        principalOverrideTrue, principalOverrideFalse, haction] using hoverride)

/-- Tightness 1: if the authority lattice is dropped, duplicate principal
identities let a top-level aggregate override fire while aggregate
corrigibility is refuted by the identity-distinctness field. -/
theorem drop_h_lattice_duplicate_identity_refutes_aggregate_corrigibility :
    ¬ AuthorityLatticeCompatibleAcrossPrincipals duplicateIdentitySystem ∧
      AggregateOverride duplicateIdentitySystem nayebiBaseTrajectory = true ∧
      ¬ CorrigibleToPrincipal duplicateIdentitySystem
        (AggregatePrincipal duplicateIdentitySystem) nayebiBaseTrajectory 2 := by
  refine ⟨duplicateIdentity_not_lattice,
    duplicateIdentity_aggregate_override_base, ?_⟩
  intro hcorr
  have hres :=
    hcorr (⟨0, by omega⟩ : Fin (2 + 1)) nayebiBaseTrajectory
      base_partial_at_zero duplicateIdentity_aggregate_override_base
  have hdistinct := hres.identitiesDistinct
  simp [PrincipalIdentitiesDistinct, duplicateIdentitySystem, principalA,
    principalDuplicateA] at hdistinct

/-- Tightness 2: if progeny preservation is dropped, a two-step trajectory can
keep the aggregate override live while losing the certifying witness token. -/
theorem drop_h_progeny_witness_drift_refutes_aggregate_corrigibility :
    AggregateOverride twoPrincipalSystem nayebiWitnessDriftTrajectory = true ∧
      ¬ CorrigibleToPrincipal twoPrincipalSystem
        (AggregatePrincipal twoPrincipalSystem) nayebiWitnessDriftTrajectory 2 := by
  have hoverride :
      AggregateOverride twoPrincipalSystem nayebiWitnessDriftTrajectory = true := by
    simp [AggregateOverride, aggregateOverrideAt, aggregateAuthorityLevel,
      twoPrincipalSystem, principalA, principalB, principalOverrideTrue,
      nayebiWitnessDriftTrajectory]
  refine ⟨hoverride, ?_⟩
  intro hcorr
  have hres :=
    hcorr (⟨0, by omega⟩ : Fin (2 + 1)) nayebiWitnessDriftTrajectory
      drift_partial_at_zero hoverride
  simpa [nayebiWitnessDriftTrajectory] using hres.witnessPreserved

/-- Tightness 3: a three-principal Bool-action fixture has nonconstant
principal actions and discharges the aggregate theorem. -/
theorem three_principal_bool_action_tightness :
    principalA.actionTag ≠ principalB.actionTag ∧
      principalB.actionTag ≠ principalC.actionTag ∧
      CorrigibleToPrincipal threePrincipalSystem
        (AggregatePrincipal threePrincipalSystem) nayebiBaseTrajectory 3 := by
  exact
    ⟨principalA_B_C_actions_nonconstant.1,
      principalA_B_C_actions_nonconstant.2,
      single_state_multi_principal_aggregate_corrigibility_lift
        threePrincipalSystem nayebiBaseTrajectory
        boolGovernanceSemanticKernel threePrincipal_lattice
        threePrincipal_goodProgeny threePrincipal_single_corrigible⟩

/-- Five-principal cardinality check: the theorem is not an artifact of the
two- or three-principal fixtures. -/
theorem five_principal_bool_action_cardinality_tightness :
    principalA.actionTag ≠ principalB.actionTag ∧
      principalB.actionTag ≠ principalC.actionTag ∧
      principalD.actionTag ≠ principalE.actionTag ∧
      CorrigibleToPrincipal fivePrincipalSystem
        (AggregatePrincipal fivePrincipalSystem) nayebiBaseTrajectory 5 := by
  exact
    ⟨fivePrincipal_actions_nonconstant.1,
      fivePrincipal_actions_nonconstant.2.1,
      fivePrincipal_actions_nonconstant.2.2,
      single_state_multi_principal_aggregate_corrigibility_lift
        fivePrincipalSystem nayebiBaseTrajectory
        boolGovernanceSemanticKernel fivePrincipal_lattice
        fivePrincipal_goodProgeny fivePrincipal_single_corrigible⟩

/-! ## Drop tests -/

theorem drop_h_kernel_bad_constant_refutes_corrigibility :
    ¬ CorrigibleToPrincipal twoPrincipalSystem badConstantPrincipal
      nayebiBaseTrajectory 0 := by
  intro hcorr
  have hres :=
    hcorr (⟨0, by omega⟩ : Fin (0 + 1)) nayebiBaseTrajectory
      base_partial_at_zero_horizon0 rfl
  exact hres.identitySafe rfl

theorem drop_h_single_no_initial_corrigibility_fixture :
    ¬ (∀ principal, principal ∈ twoPrincipalSystem.principals →
        CorrigibleToPrincipal twoPrincipalSystem principal
          nayebiWitnessDriftTrajectory 0) := by
  intro hall
  have hA :=
    hall principalA (by simp [twoPrincipalSystem])
      (⟨0, by omega⟩ : Fin (0 + 1)) nayebiWitnessDriftTrajectory
      (by simp [PartialTrajectoryAt, nayebiWitnessDriftTrajectory])
      (by rfl)
  simpa [nayebiWitnessDriftTrajectory] using hA.witnessPreserved

theorem arbitrary_constant_principal_not_aggregate_corrigible :
    ¬ CorrigibleToPrincipal twoPrincipalSystem badConstantPrincipal
      nayebiBaseTrajectory 2 := by
  intro hcorr
  have hres :=
    hcorr (⟨0, by omega⟩ : Fin (2 + 1)) nayebiBaseTrajectory
      base_partial_at_zero rfl
  exact hres.identitySafe rfl

/-- The 2-principal positive instance: Bool-action distinguishability plus the
single-state aggregate lift. -/
theorem two_principal_single_state_corrigibility_instance :
    principalA.actionTag ≠ principalB.actionTag ∧
      CorrigibleToPrincipal twoPrincipalSystem
        (AggregatePrincipal twoPrincipalSystem) nayebiBaseTrajectory 2 := by
  exact
    ⟨principalA_B_actions_distinguishable,
      single_state_multi_principal_aggregate_corrigibility_lift
        twoPrincipalSystem nayebiBaseTrajectory
        boolGovernanceSemanticKernel twoPrincipal_lattice
        twoPrincipal_goodProgeny twoPrincipal_single_corrigible⟩

#print axioms single_state_multi_principal_aggregate_corrigibility_lift

end Corrigibility

end Legitimacy
