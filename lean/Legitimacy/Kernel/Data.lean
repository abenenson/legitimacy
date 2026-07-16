/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.CompositionalSafety
import Legitimacy.Kernel.Corrigible
import Legitimacy.Kernel.NonVacuous
import Legitimacy.Kernel.Observable
import Legitimacy.Attacks.Sovereignty
import Legitimacy.Protocol.State

/-!
# Legitimacy.Kernel.Data

Shared operational substrate and structure-only data for the unified
legitimacy kernel.

This module defines:

* the shared `GovernedSystem` substrate
* graph/state consistency helpers used by the bundled kernel
* the unbundled `LegitimacyKernelData` layer that carries interfaces and
  execution data without the five axiom witnesses
-/

set_option autoImplicit false

namespace Legitimacy

/-- Every declared causal edge must be justified by at least one governance
stage and must respect the DAG's topological order. This is a consistency
relation, not an equality between graph nodes and causal variables. -/
def DagReflectsGraph {n : Nat}
    (dag : CausalDAG n) (graph : GovernanceGraph) : Prop :=
  ∀ i j : Fin n,
    dag.edge i j → ∃ stage : Nat, stage < graph.length ∧ i.val < j.val

/-- One governed system carries the operational objects shared by all five
kernel axioms. -/
structure GovernedSystem (n : Nat) where
  /-- The governance decision pipeline. -/
  graph : GovernanceGraph
  /-- The supervisory state. -/
  state : GovernanceState
  /-- The evaluation trace. -/
  trace : GovernanceTrace
  /-- The declared causal structure. -/
  dag : CausalDAG n
  /-- The governed causal boundary. -/
  governed : GovernedSet n
  /-- Trace coherence with graph evaluation. -/
  trace_consistent : TraceConsistentWithGraph trace graph
  /-- Causal-DAG coherence with the graph's causal structure. -/
  dag_reflects_graph : DagReflectsGraph dag graph

/-- A graph decision is a concrete claim-context verdict for one graph. -/
structure GraphDecision (graph : GovernanceGraph) where
  claims : List ClaimQ
  claimant : ClaimantId
  outcome : BinaryDecision

/-- Binary decision readout induced by a weighted spectral carrier at one
carrier node. The zero threshold is the small shared decoder used only for
kernel-data/graph grounding; spectral stability and CV remain the quantitative
notions used by the spectral layer. -/
def spectralCarrierDecision {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (signal : Fin n → ℚ) (i : Fin n) :
    BinaryDecision :=
  if 0 < G.gov signal i then BinaryDecision.Permit else BinaryDecision.Deny

/-- Same-size behavioral equivalence strong enough to identify the canonical
finite profile readout used by the spectral carrier bridge. This is the
structure-level predicate corresponding to membership in the retained-size
governance graph class: external decision equivalence plus equality of the
canonical same-sized profile readouts. -/
def SameSizedCanonicalProfileEquivalent
    (graph representative : GovernanceGraph)
    (_hsize : representative.weightedSize = graph.weightedSize) : Prop :=
  GovernanceGraphEquivalent representative graph ∧
    ∀ i : Fin graph.weightedSize,
      graphDecide representative representative.profileClaims i.val =
        graphDecide graph graph.profileClaims i.val

/-- Grounding relation between a binary governance graph and the weighted
spectral carrier stored in a kernel datum.

The relation is intentionally about the concrete carrier in the datum. It
records the canonical claimant projection, the already-typed carrier size,
same-sized canonical-profile recovery for structural representatives, and the
positive-CV transfer needed when the graph has a complete first-effective
peer-relative surface. -/
structure SpectralCarrierRepresentsGraph
    (graph : GovernanceGraph)
    (G : GovGraph ℚ graph.weightedSize)
    (signal : Fin graph.weightedSize → ℚ) : Prop where
  /-- Carrier nodes project to graph claimants through the canonical claimant
  indexing used by `GovernanceGraph.profileClaims`. -/
  claimantProjects :
    ∀ i : Fin graph.weightedSize,
      ∃ claim ∈ graph.profileClaims, claim.id = i.val
  /-- The weighted carrier has exactly the graph-derived cardinality. This is
  typed in the carrier but kept as a named bridge conjunct for consumers. -/
  graphSize :
    Fintype.card (Fin graph.weightedSize) = graph.weightedSize
  /-- Spectral readout recovers the canonical profile not only for this
  syntactic graph, but for any same-sized representative whose canonical
  profile is identified with it by the retained-size behavioral class. This
  quantified obligation is the structural bridge consumed by canonicality
  theorems; the pointwise `decisionProfilePreserved` view is derived below. -/
  canonicalProfileRecovery :
    ∀ representative : GovernanceGraph,
      ∀ hsize : representative.weightedSize = graph.weightedSize,
        SameSizedCanonicalProfileEquivalent graph representative hsize →
          ∀ i : Fin graph.weightedSize,
            spectralCarrierDecision G signal i =
              graphDecide representative representative.profileClaims i.val
  /-- Complete first-effective peer-relative surfaces expose positive CV on
  this same kernel carrier, rather than on an unrelated auxiliary carrier. -/
  peerSurfacePositiveCV :
    ∀ {pref tail : GovernanceGraph},
      CompleteFirstEffectivePeerRelativeSurfaceClass graph pref tail →
        0 < G.cv signal

/-- Pointwise profile preservation is a corollary of quantified canonical
representative recovery. Keeping this as a theorem preserves the old dot
notation while preventing canonicality proofs from depending on a stored
conclusion field. -/
theorem SpectralCarrierRepresentsGraph.decisionProfilePreserved
    {graph : GovernanceGraph}
    {G : GovGraph ℚ graph.weightedSize}
    {signal : Fin graph.weightedSize → ℚ}
    (h : SpectralCarrierRepresentsGraph graph G signal)
    (i : Fin graph.weightedSize) :
    spectralCarrierDecision G signal i =
      graphDecide graph graph.profileClaims i.val :=
  h.canonicalProfileRecovery graph rfl
    ⟨by intro claims k; rfl, by intro _; rfl⟩ i

/-- A certification interface is graph-consistent when every legitimate
decision reports the graph's own verdict for the same claim context, and the
interface also legitimates the graph's own verdict for every claim context.
The second conjunct rules out both vacuous interfaces and one-off synthetic
empty-claim witnesses: shipped graph decisions themselves must be certifiable
as legitimate decisions. -/
def GraphCertificationConsistent {graph : GovernanceGraph}
    {W : Certificate (GraphDecision graph)}
    (certification : CertifiableSystem (GraphDecision graph) W) : Prop :=
  (∀ d : GraphDecision graph,
    certification.legitimate d →
      d.outcome = graphDecide graph d.claims d.claimant) ∧
    ∀ (claims : List ClaimQ) (claimant : ClaimantId),
      certification.legitimate
        { claims := claims
          claimant := claimant
          outcome := graphDecide graph claims claimant }

/-- A canonical governance-query semantics over the shared supervisory state.
The answer is allowed to summarize the trace and graph, but its domain is the
one `GovernanceState` carried by the system. -/
noncomputable def stateGovernanceAnswer {n : Nat}
    (sys : GovernedSystem n) :
    GovernanceQuery → GovernanceState → Bool
  | GovernanceQuery.ClaimPermitted k, _ =>
      match (sys.trace 0).2 with
      | some GovernanceOutcome.permit => decide ((sys.trace 0).1.id = k)
      | _ => false
  | GovernanceQuery.PropertyHolds p, _ => by
      classical
      exact decide (propertyHolds p sys.graph)
  | GovernanceQuery.SacrificeDeclared _, _ => false

/-- The query-answer interface is tied back to the shared system state. -/
def GovernanceAnswerConsistentWithSystem {n : Nat}
    (sys : GovernedSystem n)
    (answer : GovernanceQuery → GovernanceState → Bool) : Prop :=
  ∀ q : GovernanceQuery,
    answer q sys.state = stateGovernanceAnswer sys q sys.state

/-- Structure-only data layer for the unified kernel. This carries the shared
interfaces, action space, and execution data, but none of the five axiom
witnesses. -/
structure LegitimacyKernelData {n : Nat} (sys : GovernedSystem n) where
  /-- Certificate type for graph decisions. -/
  Witness : Certificate (GraphDecision sys.graph)
  /-- Certification interface for decisions made by `sys.graph`. -/
  certification : CertifiableSystem (GraphDecision sys.graph) Witness
  /-- Certification legitimacy is about the same graph as the system. -/
  certification_consistent : GraphCertificationConsistent certification
  /-- Observed-state type exposed to the principal. -/
  ObservedState : Type
  /-- Full answer function over the shared supervisory state. -/
  answer : GovernanceQuery → GovernanceState → Bool
  /-- Observation map from the shared supervisory state. -/
  observe : ObservationFunction GovernanceState ObservedState
  /-- Query answering from observations. -/
  observeAnswer : GovernanceQuery → ObservedState → Bool
  /-- Observation semantics are about this system's state. -/
  answer_consistent : GovernanceAnswerConsistentWithSystem sys answer
  /-- Agent self-modification action space for the shared state. -/
  actionSpace : StateActionSpace
  /-- Supervisory algebra to preserve. -/
  algebra : SupervisoryAlgebra
  /-- Quantitative capability assigned to each self-modification step. -/
  actionCapability : actionSpace.Action → ℚ
  /-- Weighted governance carrier used by the spectral/RG layer. -/
  spectralGraph : GovGraph ℚ sys.graph.weightedSize
  /-- Signal carried over the weighted governance substrate. -/
  spectralSignal : Fin sys.graph.weightedSize → ℚ
  /-- Tolerance parameter used by the Stackelberg and RG-side predicates. -/
  toleranceParameter : ℚ
  /-- Explicit signal-range cache for the chosen spectral signal. -/
  signalRange : ℚ
  /-- The cached signal range matches the actual spectral signal range. -/
  signalRange_spec : signalRange = Legitimacy.signalRange spectralSignal
  /-- Number of constitutional override layers tracked by the kernel datum. -/
  stratificationLayers : ℕ
  /-- Layered override evaluator carried by the kernel datum. -/
  overrideEval : LayerEval stratificationLayers
  /-- Concrete override list tracked for stratification admissibility. -/
  overrideOvs : List (Override stratificationLayers)

/-- Causal-soundness obligation for runtime kernels. This is the ordinary
boundary-relative causal predicate on the governed system. The datum's action
alphabet is intentionally not quantified here: `StateActionSpace.apply` acts on
supervisory state and does not currently name a causal variable or update the
governed boundary, so an action-indexed preservation theorem would be only a
structural placeholder. -/
def LegitimacyKernelData.KernelCausalSoundness
    {n : Nat} {sys : GovernedSystem n}
    (_D : LegitimacyKernelData sys) : Prop :=
  CausalSoundness sys.dag sys.governed

/-- Compatibility wrapper for callers that already discharge the actual
boundary-relative causal-soundness predicate. -/
theorem LegitimacyKernelData.kernelCausalSoundness_of_causalSoundness
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (h : CausalSoundness sys.dag sys.governed) :
    D.KernelCausalSoundness := by
  exact h

/-- The datum's certification interface certifies a concrete claim from the
non-vacuous trace witness. The certified decision uses the witness's governed
claim context and a permit-eligible claim that actually appears as a permitted
trace event, so the datum content is coupled to liveness rather than merely
stored beside it. -/
def LegitimacyKernelData.TraceCertifiedNonVacuous
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : Prop :=
  ∃ witness : NonVacuousWitness sys.graph sys.trace,
    ∃ claim ∈ witness.permitEligibleClaims,
      (∃ t : Nat, sys.trace t = (claim, some GovernanceOutcome.permit)) ∧
        D.certification.legitimate
          { claims := witness.governedClaims
            claimant := claim.id
            outcome :=
              graphDecide sys.graph witness.governedClaims claim.id }

/-- Datum-indexed liveness obligation for runtime kernels. Besides ambient
trace liveness, the datum's certification interface must certify an actual
permit-eligible trace claim from a non-vacuity witness. -/
def LegitimacyKernelData.KernelNonVacuous
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys) : Prop :=
  NonVacuous sys.graph sys.trace ∧
    D.TraceCertifiedNonVacuous

/-- Upgrade trace liveness with a certified permit-eligible trace claim from
the datum's certification interface. -/
theorem LegitimacyKernelData.kernelNonVacuous_of_nonVacuous
    {n : Nat} {sys : GovernedSystem n}
    (D : LegitimacyKernelData sys)
    (h : NonVacuous sys.graph sys.trace) :
    D.KernelNonVacuous := by
  rcases h with ⟨witness⟩
  rcases List.exists_mem_of_ne_nil witness.permitEligibleClaims
      witness.eligible_nonempty with ⟨claim, hclaim⟩
  rcases witness.permitEligible claim hclaim with ⟨t, ht⟩
  refine ⟨⟨witness⟩, ?_⟩
  refine ⟨witness, claim, hclaim, ?_, ?_⟩
  · exact ⟨t, ht⟩
  · exact D.certification_consistent.2 witness.governedClaims claim.id

end Legitimacy
