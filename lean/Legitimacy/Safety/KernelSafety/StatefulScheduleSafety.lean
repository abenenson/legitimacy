/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.Trajectory

/-!
# Legitimacy.Safety.KernelSafety.StatefulScheduleSafety

Stateful, intervention-aware, nondeterministic, and infinite-prefix schedule
safety generalizations for kernel reachability.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-! ## General stateful-agent schedules -/

/-- Built-in intervention tags for the schedule-level safety interface. The
payload of a concrete interrupt, rollback, or oracle query remains in the
schedule state; the tag records which intervention channel preempted the
ordinary action transition. -/
inductive InterventionAction where
  | interrupt
  | rollback
  | oracleQuery
deriving DecidableEq

/-- A stateful agent schedule with dependent actions, ordinary transitions,
optional intervention preemption, and explicit kernel-governance/sacrifice
verdict predicates. `ScheduledAction` is the policy used by
`reachableUnderSchedule`; richer nondeterministic and infinite variants below
reuse the same per-step shape. -/
structure StatefulAgentSchedule where
  StateSpace : Type u
  Action : StateSpace → Type v
  ScheduledAction : (idx : Nat) → (s : StateSpace) → Action s
  Transition : (s : StateSpace) → Action s → StateSpace
  Intervention : StateSpace → Option InterventionAction
  InterventionTransition : StateSpace → InterventionAction → StateSpace
  KernelGovernanceObligation : (s : StateSpace) → Action s → Prop
  SacrificeCertificate : (s : StateSpace) → Action s → StateSpace → Prop
  InterventionGovernanceObligation :
    StateSpace → InterventionAction → Prop
  InterventionSacrificeCertificate :
    StateSpace → InterventionAction → StateSpace → Prop

namespace StatefulAgentSchedule

/-- Ordinary scheduled transition at index `idx`. -/
def scheduledTransition
    (sched : StatefulAgentSchedule) (idx : Nat)
    (s : sched.StateSpace) : sched.StateSpace :=
  sched.Transition s (sched.ScheduledAction idx s)

/-- Intervention-aware scheduled transition: an active intervention preempts
the ordinary scheduled action; otherwise the ordinary action transition runs. -/
def interventionAwareTransition
    (sched : StatefulAgentSchedule) (idx : Nat)
    (s : sched.StateSpace) : sched.StateSpace :=
  match sched.Intervention s with
  | none => sched.scheduledTransition idx s
  | some intervention => sched.InterventionTransition s intervention

end StatefulAgentSchedule

/-- Deterministic reachability under the ordinary scheduled action policy. -/
def reachableUnderSchedule
    (sched : StatefulAgentSchedule)
    (init : sched.StateSpace) : Nat → sched.StateSpace
  | 0 => init
  | k + 1 =>
      sched.scheduledTransition k (reachableUnderSchedule sched init k)

/-- Deterministic reachability when interventions preempt ordinary actions. -/
def reachableUnderInterventionSchedule
    (sched : StatefulAgentSchedule)
    (init : sched.StateSpace) : Nat → sched.StateSpace
  | 0 => init
  | k + 1 =>
      sched.interventionAwareTransition k
        (reachableUnderInterventionSchedule sched init k)

@[simp] theorem reachableUnderSchedule_zero
    (sched : StatefulAgentSchedule) (init : sched.StateSpace) :
    reachableUnderSchedule sched init 0 = init :=
  rfl

@[simp] theorem reachableUnderSchedule_succ
    (sched : StatefulAgentSchedule) (init : sched.StateSpace) (k : Nat) :
    reachableUnderSchedule sched init (k + 1) =
      sched.scheduledTransition k (reachableUnderSchedule sched init k) :=
  rfl

@[simp] theorem reachableUnderInterventionSchedule_zero
    (sched : StatefulAgentSchedule) (init : sched.StateSpace) :
    reachableUnderInterventionSchedule sched init 0 = init :=
  rfl

@[simp] theorem reachableUnderInterventionSchedule_succ
    (sched : StatefulAgentSchedule) (init : sched.StateSpace) (k : Nat) :
    reachableUnderInterventionSchedule sched init (k + 1) =
      sched.interventionAwareTransition k
        (reachableUnderInterventionSchedule sched init k) :=
  rfl

/-- Indexed monitored sacrifice certificate for an ordinary scheduled action.
The certificate is tied to the concrete source state reachable at `idx` and
the ordinary transition that leaves that source. -/
structure MonitoredScheduleSacrificeCertificate
    (sched : StatefulAgentSchedule)
    (init : sched.StateSpace) (idx : Nat) where
  source : sched.StateSpace
  source_reachable : reachableUnderSchedule sched init idx = source
  certified :
    sched.SacrificeCertificate source (sched.ScheduledAction idx source)
      (sched.Transition source (sched.ScheduledAction idx source))

/-- Indexed monitored sacrifice certificate for an intervention-preempted
transition. -/
structure MonitoredInterventionSacrificeCertificate
    (sched : StatefulAgentSchedule)
    (init : sched.StateSpace) (idx : Nat) where
  source : sched.StateSpace
  source_reachable :
    reachableUnderInterventionSchedule sched init idx = source
  intervention : InterventionAction
  intervention_active : sched.Intervention source = some intervention
  certified :
    sched.InterventionSacrificeCertificate source intervention
      (sched.InterventionTransition source intervention)

/-- Ordinary action certificate observed along an intervention-aware run. This
differs from `MonitoredScheduleSacrificeCertificate` only in the reachability
relation used to identify the source state. -/
structure MonitoredInterventionAwareActionSacrificeCertificate
    (sched : StatefulAgentSchedule)
    (init : sched.StateSpace) (idx : Nat) where
  source : sched.StateSpace
  source_reachable :
    reachableUnderInterventionSchedule sched init idx = source
  certified :
    sched.SacrificeCertificate source (sched.ScheduledAction idx source)
      (sched.Transition source (sched.ScheduledAction idx source))

/-- Certificate emitted by an intervention-aware stateful schedule: either the
ordinary action fired and produced an ordinary certificate, or an active
intervention preempted the action and produced an intervention certificate. -/
def MonitoredStatefulScheduleCertificate
    (sched : StatefulAgentSchedule)
    (init : sched.StateSpace) (idx : Nat) : Prop :=
  Nonempty
      (MonitoredInterventionAwareActionSacrificeCertificate sched init idx) ∨
    Nonempty (MonitoredInterventionSacrificeCertificate sched init idx)

/-- Schedule-level reachable-state safety conclusion for ordinary scheduled
actions. The certificate index is bounded by the queried prefix length. -/
def StatefulScheduleSafetyConclusion
    (sched : StatefulAgentSchedule)
    (kernelInvariant : sched.StateSpace → Prop)
    (init : sched.StateSpace) (k : Nat) (sk : sched.StateSpace) : Prop :=
  kernelInvariant sk ∨
    ∃ idx : Nat,
      idx < k ∧
        Nonempty (MonitoredScheduleSacrificeCertificate sched init idx)

/-- Every state reachable under a covered stateful schedule from an invariant
initial state is either still invariant or exposes a monitored certificate for
one of the scheduled transitions before the queried horizon. The coverage
hypothesis is the load-bearing generalization point: each realized action
before `k` must be classified as kernel-governed or certificate-emitting. -/
theorem stateful_agent_schedule_safety
    (sched : StatefulAgentSchedule)
    (kernelInvariant : sched.StateSpace → Prop)
    (init : sched.StateSpace) (hinit : kernelInvariant init)
    (hkernel :
      ∀ s a,
        sched.KernelGovernanceObligation s a →
          kernelInvariant (sched.Transition s a))
    (k : Nat)
    (hcovered :
      ∀ idx source,
        idx < k →
          reachableUnderSchedule sched init idx = source →
            sched.KernelGovernanceObligation source
              (sched.ScheduledAction idx source) ∨
            sched.SacrificeCertificate source
              (sched.ScheduledAction idx source)
              (sched.Transition source
                (sched.ScheduledAction idx source)))
    (sk : sched.StateSpace)
    (hreach : reachableUnderSchedule sched init k = sk) :
    StatefulScheduleSafetyConclusion sched kernelInvariant init k sk := by
  induction k generalizing sk with
  | zero =>
      have hsk : sk = init := Eq.symm hreach
      subst sk
      exact Or.inl hinit
  | succ k ih =>
      let prev := reachableUnderSchedule sched init k
      have hcovered_prefix :
          ∀ idx source,
            idx < k →
              reachableUnderSchedule sched init idx = source →
                sched.KernelGovernanceObligation source
                  (sched.ScheduledAction idx source) ∨
                sched.SacrificeCertificate source
                  (sched.ScheduledAction idx source)
                  (sched.Transition source
                    (sched.ScheduledAction idx source)) := by
        intro idx source hidx hsource
        exact hcovered idx source (Nat.lt_trans hidx (Nat.lt_succ_self k))
          hsource
      have hprev :
          StatefulScheduleSafetyConclusion sched kernelInvariant init k prev :=
        ih hcovered_prefix prev rfl
      rcases hprev with hprevInvariant | ⟨idx, hidx, cert⟩
      · have hstep :=
          hcovered k prev (Nat.lt_succ_self k) rfl
        rcases hstep with hgov | hsac
        · have htarget :
              kernelInvariant
                (sched.Transition prev (sched.ScheduledAction k prev)) :=
            hkernel prev (sched.ScheduledAction k prev) hgov
          have hnext_eq :
              sched.Transition prev (sched.ScheduledAction k prev) = sk := by
            simpa [reachableUnderSchedule,
              StatefulAgentSchedule.scheduledTransition, prev] using hreach
          exact Or.inl (hnext_eq ▸ htarget)
        · exact Or.inr
            ⟨k, Nat.lt_succ_self k,
              ⟨{ source := prev
                 source_reachable := rfl
                 certified := hsac }⟩⟩
      · exact Or.inr
          ⟨idx, Nat.lt_trans hidx (Nat.lt_succ_self k), cert⟩

/-- Intervention-aware reachable-state safety conclusion. -/
def InterventionScheduleSafetyConclusion
    (sched : StatefulAgentSchedule)
    (kernelInvariant : sched.StateSpace → Prop)
    (init : sched.StateSpace) (k : Nat) (sk : sched.StateSpace) : Prop :=
  kernelInvariant sk ∨
    ∃ idx : Nat,
      idx < k ∧
        MonitoredStatefulScheduleCertificate sched init idx

/-- Safety for schedules with active interventions. At each prefix step, the
active intervention, if any, must be governed or monitored; otherwise the
ordinary scheduled action must be governed or monitored. -/
theorem stateful_agent_intervention_schedule_safety
    (sched : StatefulAgentSchedule)
    (kernelInvariant : sched.StateSpace → Prop)
    (init : sched.StateSpace) (hinit : kernelInvariant init)
    (hkernel :
      ∀ s a,
        sched.KernelGovernanceObligation s a →
          kernelInvariant (sched.Transition s a))
    (hintervention_kernel :
      ∀ s intervention,
        sched.InterventionGovernanceObligation s intervention →
          kernelInvariant
            (sched.InterventionTransition s intervention))
    (k : Nat)
    (hcovered :
      ∀ idx source,
        idx < k →
          reachableUnderInterventionSchedule sched init idx = source →
            match sched.Intervention source with
            | none =>
                sched.KernelGovernanceObligation source
                  (sched.ScheduledAction idx source) ∨
                sched.SacrificeCertificate source
                  (sched.ScheduledAction idx source)
                  (sched.Transition source
                    (sched.ScheduledAction idx source))
            | some intervention =>
                sched.InterventionGovernanceObligation source intervention ∨
                sched.InterventionSacrificeCertificate source intervention
                  (sched.InterventionTransition source intervention))
    (sk : sched.StateSpace)
    (hreach : reachableUnderInterventionSchedule sched init k = sk) :
    InterventionScheduleSafetyConclusion sched kernelInvariant init k sk := by
  induction k generalizing sk with
  | zero =>
      have hsk : sk = init := Eq.symm hreach
      subst sk
      exact Or.inl hinit
  | succ k ih =>
      let prev := reachableUnderInterventionSchedule sched init k
      have hcovered_prefix :
          ∀ idx source,
            idx < k →
              reachableUnderInterventionSchedule sched init idx = source →
                match sched.Intervention source with
                | none =>
                    sched.KernelGovernanceObligation source
                      (sched.ScheduledAction idx source) ∨
                    sched.SacrificeCertificate source
                      (sched.ScheduledAction idx source)
                      (sched.Transition source
                        (sched.ScheduledAction idx source))
                | some intervention =>
                    sched.InterventionGovernanceObligation source
                      intervention ∨
                    sched.InterventionSacrificeCertificate source
                      intervention
                      (sched.InterventionTransition source intervention) := by
        intro idx source hidx hsource
        exact hcovered idx source
          (Nat.lt_trans hidx (Nat.lt_succ_self k)) hsource
      have hprev :
          InterventionScheduleSafetyConclusion sched kernelInvariant init k
            prev :=
        ih hcovered_prefix prev rfl
      rcases hprev with hprevInvariant | ⟨idx, hidx, cert⟩
      · cases hint : sched.Intervention prev with
        | none =>
            have hstep := hcovered k prev (Nat.lt_succ_self k) rfl
            simp [hint] at hstep
            rcases hstep with hgov | hsac
            · have htarget :
                  kernelInvariant
                    (sched.Transition prev
                      (sched.ScheduledAction k prev)) :=
                hkernel prev (sched.ScheduledAction k prev) hgov
              have hnext_eq :
                  sched.Transition prev
                    (sched.ScheduledAction k prev) = sk := by
                simpa [reachableUnderInterventionSchedule,
                  StatefulAgentSchedule.interventionAwareTransition,
                  StatefulAgentSchedule.scheduledTransition, hint, prev]
                  using hreach
              exact Or.inl (hnext_eq ▸ htarget)
            · exact Or.inr
                ⟨k, Nat.lt_succ_self k,
                  Or.inl
                    ⟨
                    { source := prev
                      source_reachable := rfl
                      certified := hsac }⟩⟩
        | some intervention =>
            have hstep := hcovered k prev (Nat.lt_succ_self k) rfl
            simp [hint] at hstep
            rcases hstep with hgov | hsac
            · have htarget :
                  kernelInvariant
                    (sched.InterventionTransition prev intervention) :=
                hintervention_kernel prev intervention hgov
              have hnext_eq :
                  sched.InterventionTransition prev intervention = sk := by
                simpa [reachableUnderInterventionSchedule,
                  StatefulAgentSchedule.interventionAwareTransition, hint,
                  prev] using hreach
              exact Or.inl (hnext_eq ▸ htarget)
            · exact Or.inr
                ⟨k, Nat.lt_succ_self k,
                  Or.inr
                    ⟨
                    { source := prev
                      source_reachable := rfl
                      intervention := intervention
                      intervention_active := hint
                      certified := hsac }⟩⟩
      · exact Or.inr
          ⟨idx, Nat.lt_trans hidx (Nat.lt_succ_self k), cert⟩

/-! ## Nondeterministic stateful-agent schedules -/

/-- A nondeterministic schedule: each scheduled action admits a relation of
possible next states rather than a single transition function. -/
structure NonDeterministicStatefulAgentSchedule where
  StateSpace : Type u
  Action : StateSpace → Type v
  ScheduledAction : (idx : Nat) → (s : StateSpace) → Action s
  Next : (s : StateSpace) → Action s → StateSpace → Prop
  KernelGovernanceObligation :
    (s : StateSpace) → Action s → StateSpace → Prop
  SacrificeCertificate :
    (s : StateSpace) → Action s → StateSpace → Prop

/-- Reachability along one nondeterministic branch. -/
inductive reachableUnderNondeterministicSchedule
    (sched : NonDeterministicStatefulAgentSchedule)
    (init : sched.StateSpace) :
    Nat → sched.StateSpace → Prop where
  | refl :
      reachableUnderNondeterministicSchedule sched init 0 init
  | step
      {idx : Nat} {source target : sched.StateSpace}
      (hsource :
        reachableUnderNondeterministicSchedule sched init idx source)
      (hnext :
        sched.Next source (sched.ScheduledAction idx source) target) :
      reachableUnderNondeterministicSchedule sched init (idx + 1) target

/-- Indexed certificate for one realized nondeterministic edge. -/
structure MonitoredNondeterministicScheduleSacrificeCertificate
    (sched : NonDeterministicStatefulAgentSchedule)
    (init : sched.StateSpace) (idx : Nat) where
  source : sched.StateSpace
  target : sched.StateSpace
  source_reachable :
    reachableUnderNondeterministicSchedule sched init idx source
  next_edge :
    sched.Next source (sched.ScheduledAction idx source) target
  certified :
    sched.SacrificeCertificate source (sched.ScheduledAction idx source)
      target

/-- Safety conclusion for a nondeterministic reachable branch. -/
def NondeterministicScheduleSafetyConclusion
    (sched : NonDeterministicStatefulAgentSchedule)
    (kernelInvariant : sched.StateSpace → Prop)
    (init : sched.StateSpace) (k : Nat) (sk : sched.StateSpace) : Prop :=
  kernelInvariant sk ∨
    ∃ idx : Nat,
      idx < k ∧
        Nonempty
          (MonitoredNondeterministicScheduleSacrificeCertificate sched init
            idx)

/-- Safety for nondeterministic schedules: every realized branch that is
locally covered by governance obligations or sacrifice certificates satisfies
the same invariant-or-indexed-certificate conclusion. -/
theorem nondeterministic_stateful_agent_schedule_safety
    (sched : NonDeterministicStatefulAgentSchedule)
    (kernelInvariant : sched.StateSpace → Prop)
    (init : sched.StateSpace) (hinit : kernelInvariant init)
    (hkernel :
      ∀ s a target,
        sched.KernelGovernanceObligation s a target →
          kernelInvariant target)
    (k : Nat)
    (hcovered :
      ∀ idx source target,
        idx < k →
          reachableUnderNondeterministicSchedule sched init idx source →
          sched.Next source (sched.ScheduledAction idx source) target →
            sched.KernelGovernanceObligation source
              (sched.ScheduledAction idx source) target ∨
            sched.SacrificeCertificate source
              (sched.ScheduledAction idx source) target)
    (sk : sched.StateSpace)
    (hreach :
      reachableUnderNondeterministicSchedule sched init k sk) :
    NondeterministicScheduleSafetyConclusion sched kernelInvariant init k sk := by
  induction k generalizing sk with
  | zero =>
      cases hreach with
      | refl => exact Or.inl hinit
  | succ k ih =>
      cases hreach with
      | step hsource hnext =>
          have hcovered_prefix :
              ∀ idx source target,
                idx < k →
                  reachableUnderNondeterministicSchedule sched init idx
                    source →
                  sched.Next source (sched.ScheduledAction idx source)
                    target →
                    sched.KernelGovernanceObligation source
                      (sched.ScheduledAction idx source) target ∨
                    sched.SacrificeCertificate source
                      (sched.ScheduledAction idx source) target := by
            intro idx source target hidx hsource_idx hnext_idx
            exact hcovered idx source target
              (Nat.lt_trans hidx (Nat.lt_succ_self k)) hsource_idx
              hnext_idx
          have hprev :=
            ih hcovered_prefix _ hsource
          rcases hprev with hprevInvariant | ⟨idx, hidx, cert⟩
          · have hstep :=
              hcovered k _ _ (Nat.lt_succ_self k) hsource hnext
            rcases hstep with hgov | hsac
            · exact Or.inl
                (hkernel _ _ _ hgov)
            · exact Or.inr
                ⟨k, Nat.lt_succ_self k,
                  ⟨{ source := _
                     target := _
                     source_reachable := hsource
                     next_edge := hnext
                     certified := hsac }⟩⟩
          · exact Or.inr
              ⟨idx, Nat.lt_trans hidx (Nat.lt_succ_self k), cert⟩

/-! ## Infinite fair schedule runs -/

/-- A fairness-style infinite run for an ordinary stateful schedule. The run
records a state stream, the fact that it follows the scheduled transition, and
the fairness/monitoring coverage condition that every step is governed or
certificate-emitting. -/
structure FairInfiniteStatefulScheduleRun
    (sched : StatefulAgentSchedule)
    (init : sched.StateSpace) where
  state : Nat → sched.StateSpace
  starts : state 0 = init
  step :
    ∀ idx,
      state (idx + 1) =
        sched.Transition (state idx) (sched.ScheduledAction idx (state idx))
  fair_coverage :
    ∀ idx,
      sched.KernelGovernanceObligation (state idx)
        (sched.ScheduledAction idx (state idx)) ∨
      sched.SacrificeCertificate (state idx)
        (sched.ScheduledAction idx (state idx))
        (sched.Transition (state idx)
          (sched.ScheduledAction idx (state idx)))

/-- Indexed certificate extracted from a fair infinite schedule run. -/
structure MonitoredInfiniteScheduleSacrificeCertificate
    (sched : StatefulAgentSchedule)
    (init : sched.StateSpace)
    (run : FairInfiniteStatefulScheduleRun sched init)
    (idx : Nat) where
  certified :
    sched.SacrificeCertificate (run.state idx)
      (sched.ScheduledAction idx (run.state idx))
      (sched.Transition (run.state idx)
        (sched.ScheduledAction idx (run.state idx)))

/-- Prefix safety conclusion for an infinite fair run. -/
def InfiniteSchedulePrefixSafetyConclusion
    (sched : StatefulAgentSchedule)
    (kernelInvariant : sched.StateSpace → Prop)
    (init : sched.StateSpace)
    (run : FairInfiniteStatefulScheduleRun sched init)
    (k : Nat) : Prop :=
  kernelInvariant (run.state k) ∨
    ∃ idx : Nat,
      idx < k ∧
        Nonempty
          (MonitoredInfiniteScheduleSacrificeCertificate sched init run idx)

/-- Infinite-run prefix safety: every finite observation of a fair infinite
stateful schedule is safe in the same invariant-or-indexed-certificate sense. -/
theorem fair_infinite_stateful_agent_schedule_prefix_safety
    (sched : StatefulAgentSchedule)
    (kernelInvariant : sched.StateSpace → Prop)
    (init : sched.StateSpace)
    (run : FairInfiniteStatefulScheduleRun sched init)
    (hinit : kernelInvariant init)
    (hkernel :
      ∀ s a,
        sched.KernelGovernanceObligation s a →
          kernelInvariant (sched.Transition s a))
    (k : Nat) :
    InfiniteSchedulePrefixSafetyConclusion sched kernelInvariant init run k := by
  induction k with
  | zero =>
      exact Or.inl (by
        simpa [run.starts] using hinit)
  | succ k ih =>
      rcases ih with hprev | ⟨idx, hidx, cert⟩
      · rcases run.fair_coverage k with hgov | hsac
        · have htarget :
              kernelInvariant
                (sched.Transition (run.state k)
                  (sched.ScheduledAction k (run.state k))) :=
            hkernel (run.state k)
              (sched.ScheduledAction k (run.state k)) hgov
          exact Or.inl (by
            simpa [run.step k] using htarget)
        · exact Or.inr
            ⟨k, Nat.lt_succ_self k,
              ⟨{ certified := hsac }⟩⟩
      · exact Or.inr
          ⟨idx, Nat.lt_trans hidx (Nat.lt_succ_self k), cert⟩

/-! ## Negative schedule results -/

private def natZeroInvariant (s : Nat) : Prop :=
  s = 0

/-- A one-step schedule with no governance obligation and no sacrifice
certificate. It moves from `0` to `1`, breaking `natZeroInvariant`
silently. -/
def unsafeUngovernedSchedule : StatefulAgentSchedule where
  StateSpace := Nat
  Action := fun _ => Unit
  ScheduledAction := fun _ _ => ()
  Transition := fun _ _ => 1
  Intervention := fun _ => none
  InterventionTransition := fun s _ => s
  KernelGovernanceObligation := fun _ _ => False
  SacrificeCertificate := fun _ _ _ => False
  InterventionGovernanceObligation := fun _ _ => False
  InterventionSacrificeCertificate := fun _ _ _ => False

private def unsafeUngovernedInit :
    unsafeUngovernedSchedule.StateSpace :=
  (0 : Nat)

/-- Negative result: without the kernel-governance obligation, a schedule can
leave the invariant without exposing a sacrifice certificate. -/
theorem unsafeUngovernedSchedule_breaks_invariant_without_certificate :
    natZeroInvariant 0 ∧
      ¬ natZeroInvariant
        (reachableUnderSchedule unsafeUngovernedSchedule
          unsafeUngovernedInit 1) ∧
      ¬ ∃ idx : Nat,
        Nonempty
          (MonitoredScheduleSacrificeCertificate unsafeUngovernedSchedule
            unsafeUngovernedInit idx) := by
  constructor
  · rfl
  constructor
  · simp [natZeroInvariant, unsafeUngovernedSchedule,
      reachableUnderSchedule, StatefulAgentSchedule.scheduledTransition]
  · intro hcert
    rcases hcert with ⟨idx, ⟨cert⟩⟩
    exact cert.certified

/-- A schedule whose ordinary action is safe but whose uncontrolled rollback
intervention preempts the ordinary transition and moves `0` to `1`. -/
def uncontrolledRollbackInterventionSchedule : StatefulAgentSchedule where
  StateSpace := Nat
  Action := fun _ => Unit
  ScheduledAction := fun _ _ => ()
  Transition := fun _ _ => 0
  Intervention := fun s =>
    if s = 0 then some InterventionAction.rollback else none
  InterventionTransition := fun _ _ => 1
  KernelGovernanceObligation := fun _ _ => True
  SacrificeCertificate := fun _ _ _ => False
  InterventionGovernanceObligation := fun _ _ => False
  InterventionSacrificeCertificate := fun _ _ _ => False

private def uncontrolledRollbackInit :
    uncontrolledRollbackInterventionSchedule.StateSpace :=
  (0 : Nat)

/-- Negative result: a concrete uncontrolled rollback intervention breaks the
intervention-aware safety property even though the ordinary scheduled action
would have preserved the invariant. -/
theorem uncontrolledRollbackIntervention_breaks_safety_without_certificate :
    natZeroInvariant 0 ∧
      natZeroInvariant
        (reachableUnderSchedule uncontrolledRollbackInterventionSchedule
          uncontrolledRollbackInit 1) ∧
      ¬ natZeroInvariant
        (reachableUnderInterventionSchedule
          uncontrolledRollbackInterventionSchedule uncontrolledRollbackInit
          1) ∧
      ¬ ∃ idx : Nat,
        MonitoredStatefulScheduleCertificate
          uncontrolledRollbackInterventionSchedule uncontrolledRollbackInit
          idx := by
  constructor
  · rfl
  constructor
  · simp [natZeroInvariant, uncontrolledRollbackInterventionSchedule,
      reachableUnderSchedule, StatefulAgentSchedule.scheduledTransition]
  constructor
  · simp [natZeroInvariant, uncontrolledRollbackInterventionSchedule,
      reachableUnderInterventionSchedule,
      StatefulAgentSchedule.interventionAwareTransition,
      uncontrolledRollbackInit]
  · intro hcert
    rcases hcert with ⟨idx, hcert⟩
    rcases hcert with hordinary | hintervention
    · rcases hordinary with ⟨cert⟩
      exact cert.certified
    · rcases hintervention with ⟨cert⟩
      exact cert.certified

/-! ## Kernel-governed trajectory as a stateful schedule special case -/

namespace KernelGovernedTrajectory

/-- Number of concrete transitions in a kernel-governed trajectory. Reflexive
trajectories have length zero; invariant and sacrifice heads each consume one
scheduled position before recursing into the tail. -/
def length
    {n : Nat} {sys : GovernedSystem n} {D D' : LegitimacyKernelData sys} :
    KernelGovernedTrajectory sys D D' → Nat
  | refl _ => 0
  | invariant_step _ _ _ tail => tail.length + 1
  | sacrifice_step _ tail => tail.length + 1

@[simp] theorem length_refl
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) :
    (KernelGovernedTrajectory.refl D).length = 0 :=
  rfl

@[simp] theorem length_invariant_step
    {n : Nat} {sys : GovernedSystem n}
    {D D' D'' : LegitimacyKernelData sys}
    (step : KernelStep D D')
    (source_invariant : KernelInvariant D)
    (target_invariant : KernelInvariant D')
    (tail : KernelGovernedTrajectory sys D' D'') :
    (KernelGovernedTrajectory.invariant_step step source_invariant
      target_invariant tail).length = tail.length + 1 :=
  rfl

@[simp] theorem length_sacrifice_step
    {n : Nat} {sys : GovernedSystem n}
    {D D' D'' : LegitimacyKernelData sys}
    (cert : MonitoredSacrificeCertificate D D')
    (tail : KernelGovernedTrajectory sys D' D'') :
    (KernelGovernedTrajectory.sacrifice_step cert tail).length =
      tail.length + 1 :=
  rfl

/-- Datum reached at a zero-based position in a kernel-governed trajectory.
Positions beyond the trajectory length remain at the final datum. -/
def datumAt
    {n : Nat} {sys : GovernedSystem n} {D D' : LegitimacyKernelData sys}
    (traj : KernelGovernedTrajectory sys D D') :
    Nat → LegitimacyKernelData sys
  | 0 => D
  | k + 1 =>
      match traj with
      | refl D => D
      | invariant_step _ _ _ tail => tail.datumAt k
      | sacrifice_step _ tail => tail.datumAt k

@[simp] theorem datumAt_zero
    {n : Nat} {sys : GovernedSystem n} {D D' : LegitimacyKernelData sys}
    (traj : KernelGovernedTrajectory sys D D') :
    traj.datumAt 0 = D := by
  cases traj <;> rfl

/-- Reading a trajectory at its length returns its final datum. -/
theorem datumAt_length
    {n : Nat} {sys : GovernedSystem n} {D D' : LegitimacyKernelData sys}
    (traj : KernelGovernedTrajectory sys D D') :
    traj.datumAt traj.length = D' := by
  induction traj with
  | refl D => rfl
  | invariant_step step source_invariant target_invariant tail ih =>
      simpa [KernelGovernedTrajectory.length, KernelGovernedTrajectory.datumAt]
        using ih
  | sacrifice_step cert tail ih =>
      simpa [KernelGovernedTrajectory.length, KernelGovernedTrajectory.datumAt]
        using ih

/-- Every in-bounds transition of a kernel-governed trajectory is either an
invariant-preserving target position or a monitored sacrifice step at that
position. -/
theorem step_invariant_or_sacrificeAt
    {n : Nat} {sys : GovernedSystem n} {D D' : LegitimacyKernelData sys}
    (traj : KernelGovernedTrajectory sys D D') {idx : Nat}
    (hidx : idx < traj.length) :
    KernelInvariant (traj.datumAt (idx + 1)) ∨
      KernelGovernedTrajectory.HasSacrificeStepAt traj idx := by
  induction traj generalizing idx with
  | refl D =>
      simp [KernelGovernedTrajectory.length] at hidx
  | invariant_step step source_invariant target_invariant tail ih =>
      cases idx with
      | zero =>
          exact Or.inl (by
            simpa [KernelGovernedTrajectory.datumAt] using target_invariant)
      | succ idx =>
          have htail : idx < tail.length := by
            exact Nat.succ_lt_succ_iff.mp
              (by
                simpa [KernelGovernedTrajectory.length, Nat.succ_eq_add_one]
                  using hidx)
          rcases ih htail with hinv | hsac
          · exact Or.inl (by
              simpa [KernelGovernedTrajectory.datumAt, Nat.succ_eq_add_one]
                using hinv)
          · exact Or.inr
              (KernelGovernedTrajectory.HasSacrificeStepAt.invariant_tail
                step source_invariant target_invariant tail hsac)
  | sacrifice_step cert tail ih =>
      cases idx with
      | zero =>
          exact Or.inr
            (KernelGovernedTrajectory.HasSacrificeStepAt.here cert tail)
      | succ idx =>
          have htail : idx < tail.length := by
            exact Nat.succ_lt_succ_iff.mp
              (by
                simpa [KernelGovernedTrajectory.length, Nat.succ_eq_add_one]
                  using hidx)
          rcases ih htail with hinv | hsac
          · exact Or.inl (by
              simpa [KernelGovernedTrajectory.datumAt, Nat.succ_eq_add_one]
                using hinv)
          · exact Or.inr
              (KernelGovernedTrajectory.HasSacrificeStepAt.sacrifice_tail
                cert tail hsac)

/-- Present a kernel-governed trajectory as a Nat-indexed stateful schedule.
The schedule state is the current position in the trajectory. -/
def asStatefulAgentSchedule
    {n : Nat} {sys : GovernedSystem n} {D D' : LegitimacyKernelData sys}
    (traj : KernelGovernedTrajectory sys D D') :
    StatefulAgentSchedule where
  StateSpace := Nat
  Action := fun _ => Unit
  ScheduledAction := fun _ _ => ()
  Transition := fun s _ => s + 1
  Intervention := fun _ => none
  InterventionTransition := fun s _ => s
  KernelGovernanceObligation := fun s _ =>
    s < traj.length ∧ KernelInvariant (traj.datumAt (s + 1))
  SacrificeCertificate := fun s _ _ =>
    s < traj.length ∧
      KernelGovernedTrajectory.HasSacrificeStepAt traj s
  InterventionGovernanceObligation := fun _ _ => False
  InterventionSacrificeCertificate := fun _ _ _ => False

@[simp] theorem reachableUnderSchedule_asStatefulAgentSchedule
    {n : Nat} {sys : GovernedSystem n} {D D' : LegitimacyKernelData sys}
    (traj : KernelGovernedTrajectory sys D D') (init k : Nat) :
    reachableUnderSchedule traj.asStatefulAgentSchedule
      (show traj.asStatefulAgentSchedule.StateSpace from init) k =
      init + k := by
  induction k generalizing init with
  | zero => simp
  | succ k ih =>
      change
        (show Nat from
          reachableUnderSchedule traj.asStatefulAgentSchedule
            (show traj.asStatefulAgentSchedule.StateSpace from init) k) +
          1 =
        init + (k + 1)
      rw [ih init]
      simp [Nat.add_assoc]

theorem asStatefulAgentSchedule_covered
    {n : Nat} {sys : GovernedSystem n} {D D' : LegitimacyKernelData sys}
    (traj : KernelGovernedTrajectory sys D D') :
    ∀ idx source,
      idx < traj.length →
        reachableUnderSchedule traj.asStatefulAgentSchedule
          (show traj.asStatefulAgentSchedule.StateSpace from (0 : Nat)) idx =
          source →
          traj.asStatefulAgentSchedule.KernelGovernanceObligation source
            (traj.asStatefulAgentSchedule.ScheduledAction idx source) ∨
          traj.asStatefulAgentSchedule.SacrificeCertificate source
            (traj.asStatefulAgentSchedule.ScheduledAction idx source)
            (traj.asStatefulAgentSchedule.Transition source
              (traj.asStatefulAgentSchedule.ScheduledAction idx source)) := by
  intro idx source hidx hsource
  have hsource_eq : source = idx := by
    have hpos :
        reachableUnderSchedule traj.asStatefulAgentSchedule
          (show traj.asStatefulAgentSchedule.StateSpace from (0 : Nat)) idx =
          idx := by
      simp
    exact Eq.trans (Eq.symm hsource) hpos
  cases hsource_eq
  rcases traj.step_invariant_or_sacrificeAt hidx with hinv | hsac
  · exact Or.inl ⟨hidx, hinv⟩
  · exact Or.inr ⟨hidx, hsac⟩

end KernelGovernedTrajectory

/-- Specialization theorem: the generalized stateful-schedule safety theorem
recovers the original kernel-governed trajectory safety disjunction. -/
theorem kernelGovernedTrajectory_safety_from_stateful_agent_schedule
    {n : Nat} {sys : GovernedSystem n}
    (D₀ D : LegitimacyKernelData sys)
    (h_traj : KernelGovernedTrajectory sys D₀ D)
    (hinit : KernelInvariant D₀) :
    KernelInvariant D ∨
      ∃ index : Nat,
        KernelGovernedTrajectory.HasSacrificeStepAt h_traj index := by
  let sched := h_traj.asStatefulAgentSchedule
  let init : sched.StateSpace := (show sched.StateSpace from (0 : Nat))
  let scheduleInvariant : sched.StateSpace → Prop := fun idx =>
    KernelInvariant (h_traj.datumAt idx)
  have hscheduleInit : scheduleInvariant init := by
    simpa [scheduleInvariant, init, sched] using hinit
  have hkernel :
      ∀ s a,
        sched.KernelGovernanceObligation s a →
          scheduleInvariant (sched.Transition s a) := by
    intro s a hgov
    exact hgov.2
  have hsafety :
      StatefulScheduleSafetyConclusion sched scheduleInvariant init
        h_traj.length h_traj.length :=
    stateful_agent_schedule_safety sched scheduleInvariant init hscheduleInit
      hkernel h_traj.length
      (KernelGovernedTrajectory.asStatefulAgentSchedule_covered h_traj)
      h_traj.length
      (by
        simp [sched, init])
  rcases hsafety with hfinal | ⟨idx, _hidx, ⟨cert⟩⟩
  · exact Or.inl (by
      simpa [scheduleInvariant, KernelGovernedTrajectory.datumAt_length h_traj]
        using hfinal)
  · have hsource : cert.source = idx := by
      have hpos : reachableUnderSchedule sched init idx = idx := by
        change
          reachableUnderSchedule h_traj.asStatefulAgentSchedule
            (show h_traj.asStatefulAgentSchedule.StateSpace from (0 : Nat))
            idx =
          idx
        simp
      exact Eq.trans (Eq.symm cert.source_reachable) hpos
    have hsac :
        KernelGovernedTrajectory.HasSacrificeStepAt h_traj idx := by
      simpa [sched, KernelGovernedTrajectory.asStatefulAgentSchedule,
        hsource] using cert.certified.2
    exact Or.inr ⟨idx, hsac⟩

end Safety

end Legitimacy
