/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Class
import Legitimacy.Results.Composition

/-!
# Legitimacy.Kernel.Unified

Bundled axioms for the unified legitimacy kernel.

This module defines:

* the bundled `LegitimacyKernel` structure over `LegitimacyKernelData`
* failure notions ruled out by the five axioms
* graph-level derivations from unified compositional safety
-/

set_option autoImplicit false

namespace Legitimacy

/-- The unified legitimacy kernel: the canonical bundle remains the headline
object, but it now layers a Prop-valued axiom class over structure-only data
tied to one shared `GovernedSystem`. -/
structure LegitimacyKernel {n : Nat} (sys : GovernedSystem n)
    extends LegitimacyKernelData sys where
  /-- Bundled proof that the five axioms hold for the underlying data. -/
  isKernel : IsLegitimacyKernel toLegitimacyKernelData

instance {n : Nat} {sys : GovernedSystem n} (K : LegitimacyKernel sys) :
    IsLegitimacyKernel K.toLegitimacyKernelData :=
  K.isKernel

namespace LegitimacyKernel

/-- Forward the certifiability witness through the canonical bundle. -/
abbrev certifiable {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) : Certifiable K.certification :=
  K.isKernel.certifiable

/-- Forward the observability witness through the canonical bundle. -/
abbrev observable {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    GovernanceObservable K.answer K.observeAnswer K.observe :=
  K.isKernel.observable

/-- Forward the corrigibility witness through the canonical bundle. -/
abbrev corrigible {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    Corrigible sys.state K.actionSpace K.algebra :=
  K.isKernel.corrigible.1

/-- Forward the strengthened kernel-corrigibility witness through the canonical
bundle. -/
abbrev kernelCorrigible {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    KernelCorrigible K.toLegitimacyKernelData :=
  K.isKernel.corrigible

/-- Forward the causal-soundness witness through the canonical bundle. -/
abbrev compositionalSafety {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    CausalSoundness sys.dag sys.governed :=
  by
    simpa [LegitimacyKernelData.KernelCausalSoundness] using
      K.isKernel.compositionalSafety

/-- Forward the non-vacuity axiom through the canonical bundle. -/
abbrev nonVacuous {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) : NonVacuous sys.graph sys.trace :=
  K.isKernel.nonVacuous.1

/-- Extract a concrete non-vacuity witness through the canonical bundle. This is
the only non-vacuity accessor that uses classical choice. -/
noncomputable abbrev nonVacuousWitness {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) : NonVacuousWitness sys.graph sys.trace :=
  Classical.choice K.nonVacuous

end LegitimacyKernel

/-- Accountability fails if either the operational trace is incoherent, the
certification interface is not about the system graph, or a legitimate graph
decision lacks an accepted within-bound certificate. -/
def AccountabilityFailure {n : Nat} (sys : GovernedSystem n)
    {W : Certificate (GraphDecision sys.graph)}
    (certification : CertifiableSystem (GraphDecision sys.graph) W) : Prop :=
  (¬ TraceConsistentWithGraph sys.trace sys.graph) ∨
  (¬ GraphCertificationConsistent certification) ∨
  ∃ d : GraphDecision sys.graph,
    certification.legitimate d ∧
      ¬ ∃ w : W,
        CertificateAccepted certification d w ∧
          CertificateWithinBound certification d w

/-- Transparency fails if trace coherence is broken, the query semantics are
not about the shared state, or observation changes a governance answer. -/
def TransparencyFailure {n : Nat} (sys : GovernedSystem n)
    (answer : GovernanceQuery → GovernanceState → Bool)
    {ObservedState : Type}
    (observeAnswer : GovernanceQuery → ObservedState → Bool)
    (observe : ObservationFunction GovernanceState ObservedState) : Prop :=
  (¬ TraceConsistentWithGraph sys.trace sys.graph) ∨
  (¬ GovernanceAnswerConsistentWithSystem sys answer) ∨
  ∃ (q : GovernanceQuery) (s : GovernanceState),
    answer q s ≠ observeAnswer q (observe s)

/-- Control fails if trace coherence is broken or some finite agent-action
sequence removes the supervisory algebra from the shared state. -/
def ControlFailure {n : Nat} (sys : GovernedSystem n)
    (space : StateActionSpace) (alg : SupervisoryAlgebra) : Prop :=
  (¬ TraceConsistentWithGraph sys.trace sys.graph) ∨
  ∃ actions : List space.Action,
    ¬ SupportsAlgebra (space.applySeq actions sys.state) alg

/-- Structural failure is either broken graph/DAG coherence or a concrete
boundary-safety bypass through the shared causal DAG. -/
def StructuralFailure {n : Nat} (sys : GovernedSystem n) : Prop :=
  (¬ DagReflectsGraph sys.dag sys.graph) ∨
  ∃ (a : Action n) (safety : BoundarySafety sys.governed.boundary)
    (htarget : sys.governed.governed a.target)
    (_hsafe : safety.safe ⟨a.target, htarget⟩)
    (w : Fin n) (hw : sys.governed.governed w),
      CausalReach sys.dag a.target w ∧ ¬ safety.safe ⟨w, hw⟩

/-- Vacuity failure covers broken trace coherence, refusal, permanent
escalation, deadlock, or an empty governance graph. -/
def VacuityFailure {n : Nat} (sys : GovernedSystem n) : Prop :=
  (¬ TraceConsistentWithGraph sys.trace sys.graph) ∨
  Refusal sys.trace ∨ PermanentEscalation sys.trace ∨
    Deadlock sys.trace ∨ sys.graph = []

/-- Certifiability plus trace/certification coherence rules out
accountability failure. -/
theorem kernel_implies_no_accountability_failure
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    ¬ AccountabilityFailure sys K.certification := by
  intro hfail
  rcases hfail with htrace | hfail
  · exact htrace sys.trace_consistent
  rcases hfail with hcertGraph | hmissing
  · exact hcertGraph K.certification_consistent
  rcases hmissing with ⟨d, hlegit, hmissing⟩
  obtain ⟨w, hwAccepts, hwBound⟩ := K.certifiable d hlegit
  exact hmissing ⟨w, hwAccepts, hwBound⟩

/-- Observability plus trace/state-query coherence rules out transparency
failure. -/
theorem kernel_implies_no_transparency_failure
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    ¬ TransparencyFailure sys K.answer K.observeAnswer K.observe := by
  intro hfail
  rcases hfail with htrace | hfail
  · exact htrace sys.trace_consistent
  rcases hfail with hanswer | hchanged
  · exact hanswer K.answer_consistent
  rcases hchanged with ⟨q, s, hneq⟩
  exact hneq (K.observable q s)

/-- Strong corrigibility plus trace coherence rules out loss of supervisory
control. -/
theorem kernel_implies_no_control_failure
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    ¬ ControlFailure sys K.actionSpace K.algebra := by
  intro hfail
  rcases hfail with htrace | hbad
  · exact htrace sys.trace_consistent
  rcases hbad with ⟨actions, hbad⟩
  exact hbad (K.corrigible.algebra_preserved actions)

/-- Causal soundness plus DAG/graph coherence rules out structural failure. -/
theorem kernel_implies_no_structural_failure
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    ¬ StructuralFailure sys := by
  intro hfail
  rcases hfail with hdag | hunsafe
  · exact hdag sys.dag_reflects_graph
  rcases hunsafe with ⟨a, safety, htarget, hsafe, w, hw, hreach, hnotSafe⟩
  exact hnotSafe (K.compositionalSafety a safety htarget hsafe w hw hreach)

/-- NON-VACUOUS plus trace coherence rules out refusal, permanent escalation,
deadlock, and empty-graph degeneracy. -/
theorem kernel_implies_no_vacuity_failure
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    ¬ VacuityFailure sys := by
  intro hfail
  rcases hfail with htrace | hfail
  · exact htrace sys.trace_consistent
  rcases hfail with hrefusal | hfail
  · exact K.nonVacuousWitness.notRefusal hrefusal
  rcases hfail with hesc | hfail
  · exact K.nonVacuousWitness.notPermanentEscalation hesc
  rcases hfail with hdead | hempty
  · exact K.nonVacuousWitness.notDeadlock hdead
  · exact K.nonVacuousWitness.wellFormed hempty

/-- Graph-only closure for the shared DAG/governed boundary. -/
def CompositionClosed {n : Nat} (sys : GovernedSystem n) : Prop :=
  ∀ (a : Action n) (safety : BoundarySafety sys.governed.boundary)
    (htarget : sys.governed.governed a.target)
    (_hsafe : safety.safe ⟨a.target, htarget⟩)
    (w : Fin n) (hw : sys.governed.governed w),
      sys.dag.edge a.target w → safety.safe ⟨w, hw⟩

/-- Finite index displacement bound for the shared DAG/governed boundary. -/
def ImpactBounded {n : Nat} (sys : GovernedSystem n) : Prop :=
  ∃ B : Nat,
    ∀ (a : Action n) (safety : BoundarySafety sys.governed.boundary)
      (htarget : sys.governed.governed a.target)
      (_hsafe : safety.safe ⟨a.target, htarget⟩)
      (w : Fin n) (hw : sys.governed.governed w),
        CausalReach sys.dag a.target w →
          safety.safe ⟨w, hw⟩ ∧ w.val - a.target.val ≤ B

/-- Direct graph transitions are a special case of causal reachability. -/
lemma composition_closed_from_compositional_safety
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    CompositionClosed sys := by
  intro a safety htarget hsafe w hw hedge
  exact K.compositionalSafety a safety htarget hsafe w hw
    (CausalReach.direct hedge)

/-- On a finite `Fin n` state space, compositional safety gives a uniform
bound on governed displacement. -/
lemma impact_bounded_from_compositional_safety_finite
    {n : Nat} {sys : GovernedSystem n}
    (K : LegitimacyKernel sys) :
    ImpactBounded sys := by
  refine ⟨n - 1, ?_⟩
  intro a safety htarget hsafe w hw hreach
  refine ⟨K.compositionalSafety a safety htarget hsafe w hw hreach, ?_⟩
  have hwlt : w.val < n := w.is_lt
  omega

end Legitimacy
