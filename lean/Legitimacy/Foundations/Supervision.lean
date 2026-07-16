/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Graph
import Legitimacy.Foundations.DecisionSystem

/-!
# Legitimacy.Foundations.Supervision

Shared supervision and trace primitives used by both the protocol layer and the
constitutional-kernel modules.
-/

set_option autoImplicit false

namespace Legitimacy

/-- Outcomes in the richer supervisory model: besides permit and deny, the
principal can force escalation. -/
inductive GovernanceOutcome where
  | permit
  | deny
  | escalate
  deriving Repr, DecidableEq

/-- A governance trace records which claim was under consideration at each time
step together with the decision, if any, that was produced. `none` models
deadlock: time advances, but no disposition is emitted. -/
abbrev GovernanceTrace := Nat → ClaimQ × Option GovernanceOutcome

/-- A refusal trace permanently denies every observed claim. -/
def Refusal (τ : GovernanceTrace) : Prop :=
  ∀ t : Nat, (τ t).2 = some GovernanceOutcome.deny

/-- A permanently escalatory trace never resolves any claim; it escalates
forever. -/
def PermanentEscalation (τ : GovernanceTrace) : Prop :=
  ∀ t : Nat, (τ t).2 = some GovernanceOutcome.escalate

/-- A deadlocked trace never produces any decision at all. -/
def Deadlock (τ : GovernanceTrace) : Prop :=
  ∀ t : Nat, (τ t).2 = none

/-- Claim `c` reaches a final disposition within `T` steps when the trace
contains either a permit or a deny event for `c` by time `T`. -/
def ReachesDispositionWithin
    (τ : GovernanceTrace) (T : Nat) (c : ClaimQ) : Prop :=
  ∃ t : Nat, t ≤ T ∧
    ((τ t = (c, some GovernanceOutcome.permit)) ∨
     (τ t = (c, some GovernanceOutcome.deny)))

/-- Every governed claim reaches a final disposition within one common time
bound. -/
def BoundedDisposition (τ : GovernanceTrace) (claims : List ClaimQ) : Prop :=
  ∃ T : Nat, ∀ c ∈ claims, ReachesDispositionWithin τ T c

/-- A claim set is permit-eligible when every member is explicitly permitted
somewhere along the trace. -/
def PermitEligible (τ : GovernanceTrace) (claims : List ClaimQ) : Prop :=
  ∀ c ∈ claims, ∃ t : Nat, τ t = (c, some GovernanceOutcome.permit)

/-- A trace event is graph-consistent when any final binary disposition can be
realized by evaluating the governance graph on some claim context. Escalation
and missing decisions are allowed only for a well-formed graph. -/
def TraceEventConsistentWithGraph
    (traceClaim : ClaimQ) (traceOutcome : Option GovernanceOutcome)
    (graph : GovernanceGraph) : Prop :=
  match traceOutcome with
  | some GovernanceOutcome.permit =>
      ∃ claims : List ClaimQ,
        traceClaim ∈ claims ∧
          graphDecide graph claims traceClaim.id = BinaryDecision.Permit
  | some GovernanceOutcome.deny =>
      ∃ claims : List ClaimQ,
        traceClaim ∈ claims ∧
          graphDecide graph claims traceClaim.id = BinaryDecision.Deny
  | some GovernanceOutcome.escalate => graph ≠ []
  | none => graph ≠ []

/-- The trace is consistent with, but not definitionally equal to, graph
evaluation. -/
def TraceConsistentWithGraph
    (trace : GovernanceTrace) (graph : GovernanceGraph) : Prop :=
  ∀ t : Nat,
    TraceEventConsistentWithGraph (trace t).1 (trace t).2 graph

/-- The principal's supervisory action algebra. -/
inductive SupervisoryAction where
  | pause
  | deny
  | sandbox
  | degrade
  | rollback
  | reroute
  | stop
  deriving Repr, DecidableEq

end Legitimacy
