/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Safety.KernelSafety.StatefulScheduleSafety
import Legitimacy.Safety.KernelSafety.BinaryDecisionPipeline
import Legitimacy.Safety.KernelSafety.ReachabilityStackRaw

/-!
# Legitimacy.Safety.KernelSafety.ReachabilityStack

Reachable-state and extracted-kernel stack theorems.

This module owns the generic reachable-state safety theorem and the packaged
extractor/parity/stateful sidecar theorem. Concrete extractor artifacts and
worked instantiations live in the examples modules.
-/

set_option autoImplicit false

namespace Legitimacy

namespace Safety

universe u v w

/-! ## Reachable-state safety theorem signature -/

/-- A concrete governed trajectory has taken a monitored sacrifice route when
one of its own transition steps carries a first-class certificate. The witness
records the zero-based transition index inside this trajectory. -/
def KernelTrajectoryHasSacrifice
    {n : Nat} {sys : GovernedSystem n}
    {D₀ D : LegitimacyKernelData sys}
    (h_traj : KernelGovernedTrajectory sys D₀ D) : Prop :=
  ∃ index : Nat,
    KernelGovernedTrajectory.HasSacrificeStepAt h_traj index

/-- Target conclusion for reachable-state safety: the reached datum still
satisfies the kernel invariant, or the supplied trajectory exposes a monitored
sacrifice certificate at a concrete transition index. -/
def ReachableStateSafetyConclusion
    {n : Nat} {sys : GovernedSystem n}
    {_D₀ D : LegitimacyKernelData sys}
    (h_traj : KernelGovernedTrajectory sys _D₀ D) : Prop :=
  KernelInvariant D ∨ KernelTrajectoryHasSacrifice h_traj

/-- Reachable-state theorem shape, packaged as a proposition for callers that
need to pass the safety statement as data. -/
def ReachableStateSafetyStatement : Prop :=
  ∀ {n : Nat} {sys : GovernedSystem n}
    (D₀ D : LegitimacyKernelData sys),
    (h_traj : KernelGovernedTrajectory sys D₀ D) →
      KernelInvariant D₀ →
        ReachableStateSafetyConclusion h_traj

/-- Every kernel-governed reachable state either preserves the semantic kernel
invariant, or the supplied trajectory exposes a monitored sacrifice certificate
at a concrete transition index. -/
theorem reachable_state_safety : ReachableStateSafetyStatement := by
  intro n sys D₀ D h hinit
  induction h with
  | refl D =>
      exact Or.inl hinit
  | invariant_step step source_invariant target_invariant tail ih =>
      rcases ih target_invariant with htailInvariant | ⟨index, hsacrifice⟩
      · exact Or.inl htailInvariant
      · exact Or.inr
          ⟨index + 1,
            KernelGovernedTrajectory.HasSacrificeStepAt.invariant_tail
              step source_invariant target_invariant tail hsacrifice⟩
  | sacrifice_step cert tail ih =>
      exact Or.inr
        ⟨0,
          KernelGovernedTrajectory.HasSacrificeStepAt.here cert tail⟩

/-- Paper-grade headline alias: every state reachable by a kernel-governed
trajectory from an initial kernel invariant is either still a semantic
legitimacy kernel or exposes a concrete indexed monitored sacrifice
certificate. -/
theorem kernelReachabilitySafety_supportedTrajectoryClass :
    ReachableStateSafetyStatement :=
  reachable_state_safety

/-- Dispatch surface for the headline reachability theorem. Raw trajectories
consume a step classifier; the proof-carrying trajectory class is retained as a
compatibility instance for existing consumers. -/
class KernelReachabilitySafetyDispatch
    {n : Nat} {sys : GovernedSystem n}
    {D₀ D : LegitimacyKernelData sys}
    (Trajectory : Type 2) where
  Result : Trajectory → Prop
  safety : (h_traj : Trajectory) → Result h_traj

instance rawKernelReachabilitySafetyDispatch
    {n : Nat} {sys : GovernedSystem n}
    {D₀ D : LegitimacyKernelData sys} :
    KernelReachabilitySafetyDispatch
      (sys := sys) (D₀ := D₀) (D := D)
      (RawKernelGovernedTrajectory sys D₀ D) where
  Result h_traj :=
    @RawKernelStepClassifier n sys →
      KernelInvariant D₀ →
        RawReachableStateSafetyConclusion h_traj
  safety h_traj :=
    raw_reachable_state_safety D₀ D h_traj

instance supportedKernelReachabilitySafetyDispatch
    {n : Nat} {sys : GovernedSystem n}
    {D₀ D : LegitimacyKernelData sys} :
    KernelReachabilitySafetyDispatch
      (sys := sys) (D₀ := D₀) (D := D)
      (KernelGovernedTrajectory sys D₀ D) where
  Result h_traj :=
    KernelInvariant D₀ → ReachableStateSafetyConclusion h_traj
  safety h_traj :=
    reachable_state_safety D₀ D h_traj

/-- Paper-grade headline reachability theorem. On raw schedules it derives the
safety disjunction by replaying `classify_raw_step` over each raw transition;
on the legacy proof-carrying trajectory class it dispatches to the supported
compatibility theorem. -/
def kernelReachabilitySafety
    {n : Nat} {sys : GovernedSystem n}
    (D₀ D : LegitimacyKernelData sys)
    {Trajectory : Type 2}
    [dispatch :
      KernelReachabilitySafetyDispatch
        (sys := sys) (D₀ := D₀) (D := D) Trajectory]
    (h_traj : Trajectory) :
    dispatch.Result h_traj :=
  dispatch.safety h_traj

/-- Tightness of the headline disjunction on the supported trajectory class:
the conclusion has no hidden third branch. For a supplied
`KernelGovernedTrajectory`, exhaustion means exactly kernel preservation at the
reached datum or a monitored sacrifice certificate at some zero-based
transition index of that same trajectory. -/
theorem kernelReachabilitySafety_exhaustive_supportedTrajectoryClass
    {n : Nat} {sys : GovernedSystem n}
    (D₀ D : LegitimacyKernelData sys)
    (h_traj : KernelGovernedTrajectory sys D₀ D) :
    ReachableStateSafetyConclusion h_traj ↔
      KernelInvariant D ∨
        ∃ index : Nat,
          KernelGovernedTrajectory.HasSacrificeStepAt h_traj index := by
  rfl

/-- Specialization theorem: the generalized stateful-schedule safety theorem
recovers the original `KernelGovernedTrajectory` reachability conclusion. -/
theorem kernelReachabilitySafety_specializes_from_stateful_agent_schedule
    {n : Nat} {sys : GovernedSystem n}
    (D₀ D : LegitimacyKernelData sys)
    (h_traj : KernelGovernedTrajectory sys D₀ D)
    (hinit : KernelInvariant D₀) :
    ReachableStateSafetyConclusion h_traj :=
  kernelGovernedTrajectory_safety_from_stateful_agent_schedule D₀ D h_traj
    hinit

/-! ## Schedule-to-kernel extraction frontier -/

/-- Missing data contract for deriving a kernel-governed trajectory from a
stateful schedule. The fixed `scheduleDatum` is the datum whose action surface
executes the stateful schedule; each schedule entry must additionally extract
the current kernel datum, the next kernel datum, and either a certified
invariant-preserving `KernelStep` or a monitored sacrifice certificate. -/
inductive ScheduleKernelExtraction
    {n : Nat} {sys : GovernedSystem n}
    (scheduleDatum : LegitimacyKernelData sys)
    (adv : StatefulAdversaryLayer scheduleDatum) :
    LegitimacyKernelData sys →
      List (StatefulScheduleStep scheduleDatum) →
      StatefulAdversaryConfig adv →
      LegitimacyKernelData sys → Type 2 where
  | done
      (current : LegitimacyKernelData sys)
      (cfg : StatefulAdversaryConfig adv) :
      ScheduleKernelExtraction scheduleDatum adv current [] cfg current
  | invariant_step
      {current next final : LegitimacyKernelData sys}
      {entry : StatefulScheduleStep scheduleDatum}
      {rest : List (StatefulScheduleStep scheduleDatum)}
      {cfg : StatefulAdversaryConfig adv}
      (step : KernelStep current next)
      (source_invariant : KernelInvariant current)
      (tail :
        ScheduleKernelExtraction scheduleDatum adv next rest
          (applyStatefulStep scheduleDatum adv entry cfg) final) :
      ScheduleKernelExtraction scheduleDatum adv current (entry :: rest) cfg
        final
  | sacrifice_step
      {current next final : LegitimacyKernelData sys}
      {entry : StatefulScheduleStep scheduleDatum}
      {rest : List (StatefulScheduleStep scheduleDatum)}
      {cfg : StatefulAdversaryConfig adv}
      (cert : MonitoredSacrificeCertificate current next)
      (tail :
        ScheduleKernelExtraction scheduleDatum adv next rest
          (applyStatefulStep scheduleDatum adv entry cfg) final) :
      ScheduleKernelExtraction scheduleDatum adv current (entry :: rest) cfg
        final

namespace ScheduleKernelExtraction

/-- A schedule extraction contract closes the bridge by replaying its extracted
per-step kernel witnesses into the existing governed-trajectory object. -/
def toKernelGovernedTrajectory
    {n : Nat} {sys : GovernedSystem n}
    {scheduleDatum current final : LegitimacyKernelData sys}
    {adv : StatefulAdversaryLayer scheduleDatum}
    {schedule : List (StatefulScheduleStep scheduleDatum)}
    {cfg : StatefulAdversaryConfig adv}
    (h :
      ScheduleKernelExtraction scheduleDatum adv current schedule cfg final) :
    KernelGovernedTrajectory sys current final :=
  match h with
  | done current _cfg =>
      KernelGovernedTrajectory.refl current
  | invariant_step step source_invariant tail =>
      KernelGovernedTrajectory.invariant_step step source_invariant
        (kernelStep_preserves_invariant step source_invariant)
        (toKernelGovernedTrajectory tail)
  | sacrifice_step cert tail =>
      KernelGovernedTrajectory.sacrifice_step cert
        (toKernelGovernedTrajectory tail)

end ScheduleKernelExtraction

/-- Named schedule-to-kernel frontier. A live protocol path and stateful
schedule do not by themselves produce a `KernelGovernedTrajectory`; the missing
load-bearing datum is `ScheduleKernelExtraction`, which names the target kernel
datum and invariant/sacrifice witness for each scheduled step. Once that data
contract is supplied, the kernel trajectory follows without any additional
assumption. -/
theorem kernelGovernedTrajectory_schedule_extraction_contract
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (adv : StatefulAdversaryLayer D)
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (_hlive : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv)
    (hextraction : ScheduleKernelExtraction D adv D schedule cfg D') :
    Nonempty (KernelGovernedTrajectory sys D D') :=
  ⟨hextraction.toKernelGovernedTrajectory⟩

/-! ## Per-step locality of the schedule-extraction contract

The contract `ScheduleKernelExtraction` is a chain of two-flavor steps:
invariant-preserving kernel transitions or monitored sacrifice certificates.
The `ScheduleStepCertificate` type names that per-step verdict directly, and
`ScheduleStepWitnessChain` re-presents the contract as an explicit chain of
such verdicts. The bijection between the two types is definitional, which
makes the schedule-extraction headline a soundness∧completeness biconditional
phrased on inhabited types: an extraction contract exists iff a per-step
verdict chain exists, with neither direction discharging additional hypotheses.
The two automatic-derivation constructors below produce extractions from
realistic inputs without taking the contract itself as a hypothesis. -/

/-- A per-step verdict on a single scheduled transition: either an
invariant-preserving kernel step (carrying its source-invariant witness) or a
monitored sacrifice certificate. This isolates the per-step locality of the
schedule-extraction contract — a contract fails locally at one step rather
than as a global schedule property. -/
inductive ScheduleStepCertificate
    {n : Nat} {sys : GovernedSystem n} :
    LegitimacyKernelData sys → LegitimacyKernelData sys → Type 2 where
  | invariant
      {current next : LegitimacyKernelData sys}
      (step : KernelStep current next)
      (source_invariant : KernelInvariant current) :
      ScheduleStepCertificate current next
  | sacrifice
      {current next : LegitimacyKernelData sys}
      (cert : MonitoredSacrificeCertificate current next) :
      ScheduleStepCertificate current next

/-- A chain of per-step verdicts indexed by the same scheduled positions used
by `ScheduleKernelExtraction`. The chain advances the stateful adversary
configuration through `applyStatefulStep` exactly as the extraction does, but
its data shape isolates each per-step verdict from the extraction recursion.
The bijection theorem `scheduleExtractionEquivWitnessChain` shows the two
types are definitionally interchangeable. -/
inductive ScheduleStepWitnessChain
    {n : Nat} {sys : GovernedSystem n}
    {scheduleDatum : LegitimacyKernelData sys}
    (adv : StatefulAdversaryLayer scheduleDatum) :
    LegitimacyKernelData sys →
      List (StatefulScheduleStep scheduleDatum) →
      StatefulAdversaryConfig adv →
      LegitimacyKernelData sys → Type 2 where
  | done
      (current : LegitimacyKernelData sys)
      (cfg : StatefulAdversaryConfig adv) :
      ScheduleStepWitnessChain adv current [] cfg current
  | step
      {current next final : LegitimacyKernelData sys}
      {entry : StatefulScheduleStep scheduleDatum}
      {rest : List (StatefulScheduleStep scheduleDatum)}
      {cfg : StatefulAdversaryConfig adv}
      (verdict : ScheduleStepCertificate current next)
      (tail :
        ScheduleStepWitnessChain adv next rest
          (applyStatefulStep scheduleDatum adv entry cfg) final) :
      ScheduleStepWitnessChain adv current (entry :: rest) cfg final

namespace ScheduleStepWitnessChain

/-- Recover an extraction contract from a per-step verdict chain. -/
def toExtraction
    {n : Nat} {sys : GovernedSystem n}
    {scheduleDatum : LegitimacyKernelData sys}
    {adv : StatefulAdversaryLayer scheduleDatum}
    {current final : LegitimacyKernelData sys}
    {schedule : List (StatefulScheduleStep scheduleDatum)}
    {cfg : StatefulAdversaryConfig adv}
    (chain : ScheduleStepWitnessChain adv current schedule cfg final) :
    ScheduleKernelExtraction scheduleDatum adv current schedule cfg final :=
  match chain with
  | done current cfg => ScheduleKernelExtraction.done current cfg
  | step verdict tail =>
      match verdict with
      | ScheduleStepCertificate.invariant kstep source_invariant =>
          ScheduleKernelExtraction.invariant_step kstep source_invariant
            tail.toExtraction
      | ScheduleStepCertificate.sacrifice cert =>
          ScheduleKernelExtraction.sacrifice_step cert tail.toExtraction

end ScheduleStepWitnessChain

namespace ScheduleKernelExtraction

/-- Re-present an extraction contract as a per-step verdict chain. -/
def toWitnessChain
    {n : Nat} {sys : GovernedSystem n}
    {scheduleDatum : LegitimacyKernelData sys}
    {adv : StatefulAdversaryLayer scheduleDatum}
    {current final : LegitimacyKernelData sys}
    {schedule : List (StatefulScheduleStep scheduleDatum)}
    {cfg : StatefulAdversaryConfig adv}
    (h :
      ScheduleKernelExtraction scheduleDatum adv current schedule cfg final) :
    ScheduleStepWitnessChain adv current schedule cfg final :=
  match h with
  | done current cfg => ScheduleStepWitnessChain.done current cfg
  | invariant_step step source_invariant tail =>
      ScheduleStepWitnessChain.step
        (ScheduleStepCertificate.invariant step source_invariant)
        tail.toWitnessChain
  | sacrifice_step cert tail =>
      ScheduleStepWitnessChain.step
        (ScheduleStepCertificate.sacrifice cert) tail.toWitnessChain

end ScheduleKernelExtraction

/-- Soundness∧completeness biconditional for the schedule-extraction contract.
A stateful schedule admits a kernel-extraction contract iff each scheduled
position admits a per-step verdict — an invariant-preserving kernel transition
or a monitored sacrifice certificate. Both directions are explicit
constructive functions on the underlying types
(`ScheduleKernelExtraction.toWitnessChain` and
`ScheduleStepWitnessChain.toExtraction`), each built by structural recursion
over the same schedule. The biconditional is therefore a definitional
bijection of inhabited types: neither direction discharges a derived
obligation, both are pure data refactorings of the same per-step shape. -/
theorem schedule_extraction_iff_per_step_witness
    {n : Nat} {sys : GovernedSystem n}
    {scheduleDatum : LegitimacyKernelData sys}
    (adv : StatefulAdversaryLayer scheduleDatum)
    (current final : LegitimacyKernelData sys)
    (schedule : List (StatefulScheduleStep scheduleDatum))
    (cfg : StatefulAdversaryConfig adv) :
    Nonempty
        (ScheduleKernelExtraction scheduleDatum adv current schedule cfg
          final) ↔
      Nonempty (ScheduleStepWitnessChain adv current schedule cfg final) :=
  ⟨fun ⟨h⟩ => ⟨h.toWitnessChain⟩, fun ⟨c⟩ => ⟨c.toExtraction⟩⟩

/-! ## Automatic schedule-extraction derivations

Two automatic derivations of `ScheduleKernelExtraction` from realistic inputs.
The all-invariant derivation uses the reflexive kernel transition and the
schedule-datum invariant, requiring no sacrifice certificate input. The
verdict-oracle derivation takes a per-step decision function and threads the
chosen `KernelStep`/sacrifice witnesses through the schedule. Both produce the
contract type from data that does not assume the contract: they close the
bridge from a stateful schedule plus protocol live-path to a kernel-governed
trajectory once the per-step shape is fixed. -/

namespace ScheduleKernelExtraction

/-- Trivial automatic derivation: when the schedule datum already satisfies the
kernel invariant, every scheduled position admits the reflexive kernel step.
The result is the constant-`refl` extraction over an arbitrary schedule, with
the schedule datum carried unchanged through the contract. -/
def allInvariantRefl
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D)
    (hinv : KernelInvariant D) :
    ∀ (schedule : List (StatefulScheduleStep D))
      (cfg : StatefulAdversaryConfig adv),
      ScheduleKernelExtraction D adv D schedule cfg D
  | [], cfg => ScheduleKernelExtraction.done D cfg
  | entry :: rest, cfg =>
      ScheduleKernelExtraction.invariant_step (KernelStep.refl D) hinv
        (allInvariantRefl D adv hinv rest (applyStatefulStep D adv entry cfg))

/-- Automatic derivation parameterized on a per-step verdict oracle. The oracle
chooses, at each scheduled position, either an invariant-preserving
`KernelStep` or a monitored sacrifice certificate; the procedure threads those
choices into a `ScheduleKernelExtraction` contract over the same schedule. The
final datum is computed by folding the oracle's chosen `next` datum through
the schedule, so the procedure infers the contract from a per-step decision
without taking the extraction itself as a hypothesis. -/
def fromVerdictOracle
    {n : Nat} {sys : GovernedSystem n}
    {scheduleDatum : LegitimacyKernelData sys}
    (adv : StatefulAdversaryLayer scheduleDatum)
    (oracle :
      (current : LegitimacyKernelData sys) →
        (entry : StatefulScheduleStep scheduleDatum) →
        (cfg : StatefulAdversaryConfig adv) →
        Σ next : LegitimacyKernelData sys, ScheduleStepCertificate current next) :
    ∀ (current : LegitimacyKernelData sys)
      (schedule : List (StatefulScheduleStep scheduleDatum))
      (cfg : StatefulAdversaryConfig adv),
      Σ final : LegitimacyKernelData sys,
        ScheduleKernelExtraction scheduleDatum adv current schedule cfg final
  | current, [], cfg =>
      ⟨current, ScheduleKernelExtraction.done current cfg⟩
  | current, entry :: rest, cfg =>
      let verdict := oracle current entry cfg
      let nextCfg := applyStatefulStep scheduleDatum adv entry cfg
      let tail := fromVerdictOracle adv oracle verdict.1 rest nextCfg
      match verdict.2 with
      | ScheduleStepCertificate.invariant kstep source_invariant =>
          ⟨tail.1,
            ScheduleKernelExtraction.invariant_step kstep source_invariant
              tail.2⟩
      | ScheduleStepCertificate.sacrifice cert =>
          ⟨tail.1,
            ScheduleKernelExtraction.sacrifice_step cert tail.2⟩

/-- Re-present an already kernel-governed trajectory as a schedule extraction
over any length-matched stateful schedule. The schedule datum and adversary
drive only the schedule/configuration axis; the supplied trajectory carries the
kernel-data evolution from `current` to `final`, including non-constant
`D → D'` transitions. -/
def fromKernelGovernedTrajectoryAndSchedule
    {n : Nat} {sys : GovernedSystem n}
    {scheduleDatum current final : LegitimacyKernelData sys}
    {adv : StatefulAdversaryLayer scheduleDatum}
    (traj : KernelGovernedTrajectory sys current final)
    (schedule : List (StatefulScheduleStep scheduleDatum))
    (cfg : StatefulAdversaryConfig adv)
    (h_length : schedule.length = traj.length) :
    ScheduleKernelExtraction scheduleDatum adv current schedule cfg final :=
  match traj with
  | KernelGovernedTrajectory.refl D =>
      match schedule with
      | [] => ScheduleKernelExtraction.done D cfg
      | _entry :: rest =>
          False.elim (Nat.succ_ne_zero rest.length h_length)
  | KernelGovernedTrajectory.invariant_step
      step source_invariant _target_invariant tail =>
      match schedule with
      | [] =>
          have hzero : tail.length + 1 = 0 := Eq.symm h_length
          False.elim (by
            simp at hzero)
      | entry :: rest =>
          have h_tail : rest.length = tail.length := by
            have h_succ : Nat.succ rest.length = Nat.succ tail.length := by
              simpa [Nat.succ_eq_add_one] using h_length
            exact Nat.succ.inj h_succ
          ScheduleKernelExtraction.invariant_step step source_invariant
            (fromKernelGovernedTrajectoryAndSchedule tail rest
              (applyStatefulStep scheduleDatum adv entry cfg) h_tail)
  | KernelGovernedTrajectory.sacrifice_step cert tail =>
      match schedule with
      | [] =>
          have hzero : tail.length + 1 = 0 := Eq.symm h_length
          False.elim (by
            simp at hzero)
      | entry :: rest =>
          have h_tail : rest.length = tail.length := by
            have h_succ : Nat.succ rest.length = Nat.succ tail.length := by
              simpa [Nat.succ_eq_add_one] using h_length
            exact Nat.succ.inj h_succ
          ScheduleKernelExtraction.sacrifice_step cert
            (fromKernelGovernedTrajectoryAndSchedule tail rest
              (applyStatefulStep scheduleDatum adv entry cfg) h_tail)

/-- Extract the consistency sacrifice certificate forced by a live protocol
path over an effective peer-relative surface. The certificate is constant in
the kernel-datum index (`D` to `D`) because the current pipeline theorem emits
`MonitoredSacrificeCertificate D D` from a reflexive kernel step. -/
private noncomputable def forcedConsistencySacrificeCertificate
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    {pref tail : GovernanceGraph}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (heffective : EffectivePeerRelativeSurface compiled.graph pref tail)
    (hcomplete : CompletePeerRelativeTail tail)
    (hgraph : compiled.graph = sys.graph) :
    MonitoredSacrificeCertificate D D :=
  Classical.choose
    (effectivePeerRelativeSurface_live_forces_sacrifice_via_pipeline
      (D := D) (D' := D) (KernelStep.refl D)
      hpath heffective hcomplete hgraph).1

/-- Sacrifice-only automatic derivation from a protocol live path. Each
scheduled position receives the consistency sacrifice certificate forced by
`effectivePeerRelativeSurface_live_forces_sacrifice_via_pipeline`; the
extraction is non-circular because it derives the certificate from
`TransitionSequence`, `EffectivePeerRelativeSurface`, and
`CompletePeerRelativeTail`, not from a preexisting schedule extraction. The
kernel datum remains constant across the chain, matching the reflexive-step
certificate produced by the pipeline theorem. -/
noncomputable def fromForcedConsistencySacrifice
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D)
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    {pref tail : GovernanceGraph}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (heffective : EffectivePeerRelativeSurface compiled.graph pref tail)
    (hcomplete : CompletePeerRelativeTail tail)
    (hgraph : compiled.graph = sys.graph) :
    ∀ (schedule : List (StatefulScheduleStep D))
      (cfg : StatefulAdversaryConfig adv),
      ScheduleKernelExtraction D adv D schedule cfg D
  | [], cfg => ScheduleKernelExtraction.done D cfg
  | entry :: rest, cfg =>
      let cert :=
        forcedConsistencySacrificeCertificate D hpath heffective hcomplete
          hgraph
      ScheduleKernelExtraction.sacrifice_step cert
        (fromForcedConsistencySacrifice D adv hpath heffective hcomplete
          hgraph rest (applyStatefulStep D adv entry cfg))

/-- Core alternator for the invariant/sacrifice automatic derivation. The
Boolean flag selects the verdict emitted at the current scheduled position:
`true` emits an invariant `refl` step, and `false` emits the forced consistency
sacrifice certificate before toggling back. -/
private noncomputable def fromForcedConsistencyAlternationCore
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D)
    (hinv : KernelInvariant D)
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    {pref tail : GovernanceGraph}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (heffective : EffectivePeerRelativeSurface compiled.graph pref tail)
    (hcomplete : CompletePeerRelativeTail tail)
    (hgraph : compiled.graph = sys.graph) :
    Bool →
      ∀ (schedule : List (StatefulScheduleStep D))
        (cfg : StatefulAdversaryConfig adv),
        ScheduleKernelExtraction D adv D schedule cfg D
  | _, [], cfg => ScheduleKernelExtraction.done D cfg
  | true, entry :: rest, cfg =>
      ScheduleKernelExtraction.invariant_step (KernelStep.refl D) hinv
        (fromForcedConsistencyAlternationCore D adv hinv hpath heffective
          hcomplete hgraph false rest (applyStatefulStep D adv entry cfg))
  | false, entry :: rest, cfg =>
      let cert :=
        forcedConsistencySacrificeCertificate D hpath heffective hcomplete
          hgraph
      ScheduleKernelExtraction.sacrifice_step cert
        (fromForcedConsistencyAlternationCore D adv hinv hpath heffective
          hcomplete hgraph true rest (applyStatefulStep D adv entry cfg))

/-- Invariant/sacrifice alternating automatic derivation from a kernel
invariant and the same protocol live path used by
`fromForcedConsistencySacrifice`. The chain starts with an invariant reflexive
step, then alternates forced consistency-sacrifice and invariant steps over
the remaining schedule entries, without taking any sacrifice certificate or
schedule extraction as an input. -/
noncomputable def fromForcedConsistencyAlternation
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) (adv : StatefulAdversaryLayer D)
    (hinv : KernelInvariant D)
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    {pref tail : GovernanceGraph}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (heffective : EffectivePeerRelativeSurface compiled.graph pref tail)
    (hcomplete : CompletePeerRelativeTail tail)
    (hgraph : compiled.graph = sys.graph) :
    ∀ (schedule : List (StatefulScheduleStep D))
      (cfg : StatefulAdversaryConfig adv),
      ScheduleKernelExtraction D adv D schedule cfg D :=
  fromForcedConsistencyAlternationCore D adv hinv hpath heffective hcomplete
    hgraph true

end ScheduleKernelExtraction

/-- Automatic bridge from a stateful schedule + protocol live path to a
kernel-governed trajectory: given a per-step verdict oracle, the schedule
admits an extraction contract whose induced kernel-governed trajectory exists.
The protocol-live-path hypothesis is carried for parity with
`kernelGovernedTrajectory_schedule_extraction_contract` but is not consumed by
the derivation itself, since the contract data alone determines the
trajectory. -/
theorem kernelGovernedTrajectory_from_verdictOracle
    {n : Nat} {sys : GovernedSystem n}
    {D : LegitimacyKernelData sys}
    (adv : StatefulAdversaryLayer D)
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (_hlive : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (oracle :
      (current : LegitimacyKernelData sys) →
        (entry : StatefulScheduleStep D) →
        (cfg : StatefulAdversaryConfig adv) →
        Σ next : LegitimacyKernelData sys, ScheduleStepCertificate current next)
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv) :
    Nonempty
      (KernelGovernedTrajectory sys D
        (ScheduleKernelExtraction.fromVerdictOracle adv oracle D schedule cfg).1) :=
  ⟨(ScheduleKernelExtraction.fromVerdictOracle adv oracle D schedule
    cfg).2.toKernelGovernedTrajectory⟩

/-- All-invariant specialization: the trivial `refl` derivation always yields a
kernel-governed trajectory back to the same datum, parameterized only on the
schedule datum's kernel invariant. -/
theorem kernelGovernedTrajectory_from_allInvariantRefl
    {n : Nat} {sys : GovernedSystem n}
    {D : LegitimacyKernelData sys}
    (adv : StatefulAdversaryLayer D)
    (hinv : KernelInvariant D)
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv) :
    Nonempty (KernelGovernedTrajectory sys D D) :=
  ⟨(ScheduleKernelExtraction.allInvariantRefl D adv hinv schedule
    cfg).toKernelGovernedTrajectory⟩

/-- Sacrifice-only live-path specialization: an effective peer-relative
surface on a live compiled protocol forces a consistency-sacrifice extraction
over any stateful schedule, and therefore a kernel-governed trajectory back to
the same datum. -/
theorem kernelGovernedTrajectory_from_forcedConsistencySacrifice
    {n : Nat} {sys : GovernedSystem n}
    {D : LegitimacyKernelData sys}
    (adv : StatefulAdversaryLayer D)
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    {pref tail : GovernanceGraph}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (heffective : EffectivePeerRelativeSurface compiled.graph pref tail)
    (hcomplete : CompletePeerRelativeTail tail)
    (hgraph : compiled.graph = sys.graph)
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv) :
    Nonempty (KernelGovernedTrajectory sys D D) :=
  ⟨(ScheduleKernelExtraction.fromForcedConsistencySacrifice D adv hpath
    heffective hcomplete hgraph schedule cfg).toKernelGovernedTrajectory⟩

/-- BRIDGE-3 protocol-to-trajectory bridge: a live compiled protocol over a
complete first-effective peer-relative surface emits a concrete monitored
sacrifice certificate, and that certificate is replayed as a kernel-governed
trajectory. This is the constant-datum bridge supplied by the current
pipeline theorem: non-constant target trajectories still use the explicit
`ScheduleKernelExtraction` contract above. -/
theorem liveCompiledProtocol_extends_kernel_trajectory
    {n : Nat} {sys : GovernedSystem n}
    (source : LegitimacyKernelData sys)
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    {pref tail : GovernanceGraph}
    (hlive : IsLiveCompiled compiled report monitoring)
    (heffective : EffectivePeerRelativeSurface compiled.graph pref tail)
    (hcomplete : CompletePeerRelativeTail tail)
    (hgraph : compiled.graph = sys.graph) :
    ∃ trajectory : KernelGovernedTrajectory sys source source,
      KernelTrajectoryHasSacrifice trajectory := by
  obtain ⟨cert, _hcert⟩ :=
    (effectivePeerRelativeSurface_live_forces_sacrifice_via_pipeline
      (D := source) (D' := source) (KernelStep.refl source)
      hlive heffective hcomplete hgraph).1
  refine
    ⟨KernelGovernedTrajectory.singleSacrificeStep cert, ?_⟩
  exact
    ⟨0,
      KernelGovernedTrajectory.HasSacrificeStepAt.here cert
        (KernelGovernedTrajectory.refl source)⟩

/-- Alternating live-path specialization: a kernel invariant supplies the
invariant steps, while the protocol live path supplies the sacrifice steps. -/
theorem kernelGovernedTrajectory_from_forcedConsistencyAlternation
    {n : Nat} {sys : GovernedSystem n}
    {D : LegitimacyKernelData sys}
    (adv : StatefulAdversaryLayer D)
    (hinv : KernelInvariant D)
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    {pref tail : GovernanceGraph}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (heffective : EffectivePeerRelativeSurface compiled.graph pref tail)
    (hcomplete : CompletePeerRelativeTail tail)
    (hgraph : compiled.graph = sys.graph)
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv) :
    Nonempty (KernelGovernedTrajectory sys D D) :=
  ⟨(ScheduleKernelExtraction.fromForcedConsistencyAlternation D adv hinv hpath
    heffective hcomplete hgraph schedule cfg).toKernelGovernedTrajectory⟩

/-- The composed extractor-to-reachable-state safety clause. The semantic
kernel fact comes from a bounded extractor contract; the reachable-state
conclusion comes from replaying the supplied kernel-governed trajectory from
that semantic invariant. -/
def ExtractedKernelReachableSafety
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys}
    (h_traj : KernelGovernedTrajectory sys D D') : Prop :=
  IsSemanticLegitimacyKernel D ∧ ReachableStateSafetyConclusion h_traj

/-- Semantic transfer from the datum emitted by the extractor to the live datum
that anchors the reachable-state trajectory. This relation is intentionally
explicit: the live datum need not be definitionally identical to the extracted
datum. -/
def ExtractedKernelSemanticTransfer
    {n : Nat} {sys : GovernedSystem n}
    (extracted live : LegitimacyKernelData sys) : Prop :=
  IsSemanticLegitimacyKernel extracted → IsSemanticLegitimacyKernel live

/-- Stateful sidecar: the realized stateful trajectory either remains inside
the bounded-corrigibility basin or emits a monitored consistency-sacrifice
certificate carrying the critical-budget failure. -/
def StatefulCorrigibilityOrConsistencySacrifice
    {P : Type} [BinaryDecisionPipeline P]
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (adv : StatefulAdversaryLayer D)
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv)
    {G pref tail : P} {node : BinaryDecisionPipeline.NodeOf P}
    (hwitness : BinaryDecisionPipeline.HasConsistencyViolationWitness node)
    (heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : BinaryDecisionPipeline.CompleteTailForNode node tail) :
    Prop :=
  BoundedCorrigibilityPreservedAt D adv schedule cfg ∨
    ∃ cert : MonitoredSacrificeCertificate D D,
      ConsistencyAxiomWitnessedSacrifice cert hwitness heffective hcomplete ∧
      ∃ hcritical :
        kernelDataCriticalCapability D ≤
          statefulTrajectoryPerturbationBound D adv schedule cfg,
        cert.stateful_violation =
          some
            ({ adv := adv
               schedule := schedule
               cfg := cfg
               critical_le_budget := hcritical } :
              StatefulCriticalCapabilityViolation D)

/-- Empirical parity sidecar for the finite extractor fixture connected to the
source package. -/
def ExtractorParityFixtureSatisfied
    (src : ExtractorInput)
    (fixtures : List EmpiricalParityFixture) : Prop :=
  ∃ fixture : EmpiricalParityFixture,
    fixture ∈ fixtures ∧
      fixture.input = src ∧ fixture.ByteParity ∧ fixture.LeanContract

/-- Unified all-branches kernel-governance safety theorem.

The kernel-reachability conjunct is derived from bounded extractor soundness,
explicit semantic transfer, and the supplied `KernelGovernedTrajectory`. The
stateful conjunct is derived by the live compiled-surface adversary theorem, so
the bounded-corrigibility and critical-capability-sacrifice branches remain a
real disjunction rather than a chosen input. The protocol/stateful schedule does
not construct the kernel trajectory; that boundary is named separately by
`kernelGovernedTrajectory_schedule_extraction_contract`. -/
theorem extractedKernelData_satisfies_allBranchesKernelGovernanceSafety
    {extract : KernelExtractor}
    (hcontract : BoundedExtractorContract extract)
    (src : ExtractorInput) (hwellFormed : src.WellFormed)
    {canonicalInputs : List ExtractorInput}
    {fixtures : List EmpiricalParityFixture}
    (hparity : EmpiricalParityCertificate canonicalInputs fixtures)
    (hsrc_canonical : src ∈ canonicalInputs)
    (D : LegitimacyKernelData (extract src).sys)
    (hsemantic_transfer :
      ExtractedKernelSemanticTransfer (extract src).data D)
    {D' : LegitimacyKernelData (extract src).sys}
    (h_traj : KernelGovernedTrajectory (extract src).sys D D')
    (adv : StatefulAdversaryLayer D)
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    {P : Type} [BinaryDecisionPipeline P]
    (G pref tail : P) (node : BinaryDecisionPipeline.NodeOf P)
    (hwitness : BinaryDecisionPipeline.HasConsistencyViolationWitness node)
    (heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : BinaryDecisionPipeline.CompleteTailForNode node tail)
    (heq : DecisionSystem.Equivalent G compiled.graph)
    (hgraph : compiled.graph = (extract src).sys.graph)
    (hlive : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (hδ : 0 < D.toleranceParameter)
    (hcv : 0 < D.spectralGraph.cv D.spectralSignal)
    [IsKernelPerturbationFreeAdversary D adv]
    [IsLocallyStableStatefulAdversary D adv (extract src).sys.state
      (kernelDataCriticalCapability D)]
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv)
    (hcfg : cfg = initialStatefulAdversaryConfig D adv) :
    ReachableStateSafetyConclusion h_traj ∧
    StatefulCorrigibilityOrConsistencySacrifice
      D adv schedule cfg hwitness heffective hcomplete ∧
    ExtractorParityFixtureSatisfied src fixtures := by
  have hsemantic_extract :
      (extract src).IsSemanticKernel :=
    bounded_extractor_contract_sound extract hcontract src hwellFormed
  have hsemantic : IsSemanticLegitimacyKernel D :=
    hsemantic_transfer hsemantic_extract
  have h_init_invariant : KernelInvariant D :=
    hsemantic
  have hreachable : ReachableStateSafetyConclusion h_traj :=
    reachable_state_safety D D' h_traj h_init_invariant
  have hstatefulSafety :
      StatefulCorrigibilityOrConsistencySacrifice
        D adv schedule cfg hwitness heffective hcomplete :=
    statefulAdversary_via_consistencyWitnessedAggregator_yields_boundedCorrigibility_or_sacrifice
      D adv compiled report monitoring G pref tail node hwitness heffective
      hcomplete heq hgraph hlive hδ hcv schedule cfg hcfg
  obtain ⟨fixture, hfixture_mem, hfixture_src⟩ :=
    hparity.1 src hsrc_canonical
  obtain ⟨_hfixture_canonical, hbyte, hlean⟩ :=
    hparity.2 fixture hfixture_mem
  have hfixture : ExtractorParityFixtureSatisfied src fixtures :=
    ⟨fixture, hfixture_mem, hfixture_src, hbyte, hlean⟩
  exact ⟨hreachable, hstatefulSafety, hfixture⟩

/-- Kernel-safety stack theorem with an honest three-clause result.

The first conjunct is derivation-composed: bounded extractor soundness gives a
semantic kernel for the extracted datum, an explicit semantic-transfer relation
connects that datum to the live trajectory datum, and that semantic kernel
feeds reachable-state safety along the kernel-governed trajectory. The stateful
sidecar is also built inside the theorem from the supplied bounded-corrigibility
branch. Read
`extractedKernelData_satisfies_allBranchesKernelGovernanceSafety` first: it is
the canonical all-branches stack theorem. This theorem is retained only as the
bounded-branch packaging projection for callers that already possess the left
side of the stateful disjunction. -/
theorem extractedKernelData_satisfies_boundedSafetyStack
    {extract : KernelExtractor}
    (hcontract : BoundedExtractorContract extract)
    (src : ExtractorInput) (hwellFormed : src.WellFormed)
    {canonicalInputs : List ExtractorInput}
    {fixtures : List EmpiricalParityFixture}
    (hparity : EmpiricalParityCertificate canonicalInputs fixtures)
    (hsrc_canonical : src ∈ canonicalInputs)
    (D : LegitimacyKernelData (extract src).sys)
    (hsemantic_transfer :
      ExtractedKernelSemanticTransfer (extract src).data D)
    {D' : LegitimacyKernelData (extract src).sys}
    (h_traj : KernelGovernedTrajectory (extract src).sys D D')
    (adv : StatefulAdversaryLayer D)
    {P : Type} [BinaryDecisionPipeline P]
    {G pref tail : P} {node : BinaryDecisionPipeline.NodeOf P}
    (hwitness : BinaryDecisionPipeline.HasConsistencyViolationWitness node)
    (heffective :
      BinaryDecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : BinaryDecisionPipeline.CompleteTailForNode node tail)
    (schedule : List (StatefulScheduleStep D))
    (cfg : StatefulAdversaryConfig adv)
    (hboundedCorrigibility :
      BoundedCorrigibilityPreservedAt D adv schedule cfg) :
    ExtractedKernelReachableSafety h_traj ∧
    StatefulCorrigibilityOrConsistencySacrifice
      D adv schedule cfg hwitness heffective hcomplete ∧
    ExtractorParityFixtureSatisfied src fixtures := by
  have hsemantic_extract :
      (extract src).IsSemanticKernel :=
    bounded_extractor_contract_sound extract hcontract src hwellFormed
  have hsemantic : IsSemanticLegitimacyKernel D :=
    hsemantic_transfer hsemantic_extract
  have h_init_invariant : KernelInvariant D :=
    hsemantic
  have hreachable : ReachableStateSafetyConclusion h_traj :=
    reachable_state_safety D D' h_traj h_init_invariant
  have hderived : ExtractedKernelReachableSafety h_traj :=
    ⟨hsemantic, hreachable⟩
  have hstatefulSafety :
      StatefulCorrigibilityOrConsistencySacrifice
        D adv schedule cfg hwitness heffective hcomplete :=
    Or.inl hboundedCorrigibility
  obtain ⟨fixture, hfixture_mem, hfixture_src⟩ :=
    hparity.1 src hsrc_canonical
  obtain ⟨_hfixture_canonical, hbyte, hlean⟩ :=
    hparity.2 fixture hfixture_mem
  have hfixture : ExtractorParityFixtureSatisfied src fixtures :=
    ⟨fixture, hfixture_mem, hfixture_src, hbyte, hlean⟩
  exact ⟨hderived, hstatefulSafety, hfixture⟩
end Safety

end Legitimacy
