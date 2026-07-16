/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.Protocol
import Mathlib.Tactic.NormNum

/-!
# Legitimacy.Kernel.Observable — The GOVERNANCE-OBSERVABLE axiom

This module formalizes a weakened observability requirement for governance:
the principal need not observe raw internal state, but must be able to answer
every governance-relevant query from the observation interface.

We work with a concrete governance snapshot built from the existing protocol
state machine together with the currently governed claims and estate. Queries
range over the decision-relevant observables singled out in the axiom text:

- whether a claim is permitted,
- whether a governance property holds,
- whether a sacrifice has been declared.

The central predicate `GovernanceObservable` says that an observation function
preserves the answer to every governance query.

The module also gives constructive independence witnesses:

- a certifiable-but-not-observable system, modeling a zero-knowledge style
  certificate that hides governance answers, and
- an observable-but-not-certifiable system, modeling a perfectly transparent
  interface with no successful certification procedure.

Finally, `observable_sufficient_for_protocol` shows that governance-observable
views suffice to recover the protocol soundness conclusions for `Live` states.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A concrete governance snapshot: protocol state plus currently governed
claims and estate. -/
structure ObservableGovernanceState where
  /-- The current protocol state. -/
  protocol : ProtocolState
  /-- The active claims under governance. -/
  claims : List ClaimQ
  /-- The current estate being governed. -/
  estate : EstateQ

/-- Governance-relevant queries exposed to the principal. -/
inductive GovernanceQuery where
  /-- Is claimant `k` currently permitted by the governance graph? -/
  | ClaimPermitted (k : ClaimantId)
  /-- Does governance property `p` hold for the declared graph? -/
  | PropertyHolds (p : GovernanceProperty)
  /-- Has governance property `p` been declared as sacrificed? -/
  | SacrificeDeclared (p : GovernanceProperty)
  deriving Repr, DecidableEq

/-- Extract the governance graph carried by a protocol state, if one exists. -/
def ProtocolState.graph? : ProtocolState → Option GovernanceGraph
  | .Undeclared => none
  | .Declared graph _ => some graph
  | .Compiled compiled => some compiled.graph
  | .Measured compiled _ => some compiled.graph
  | .Live compiled _ _ => some compiled.graph
  | .Supervised compiled _ _ _ => some compiled.graph
  | .Drifted _ report => some report.observed_graph
  | .Recompiling _ _ revised => some revised

/-- Extract the declared sacrifices from a protocol state. -/
def ProtocolState.sacrifices : ProtocolState → List GovernanceProperty
  | .Undeclared => []
  | .Declared _ sacrifices => sacrifices
  | .Compiled compiled => compiled.sacrifices
  | .Measured compiled _ => compiled.sacrifices
  | .Live compiled _ _ => compiled.sacrifices
  | .Supervised compiled _ _ _ => compiled.sacrifices
  | .Drifted compiled _ => compiled.sacrifices
  | .Recompiling orig _ _ => orig.sacrifices

/-- Answer a governance query from the full governance state. -/
noncomputable def governanceAnswer
    (q : GovernanceQuery) (s : ObservableGovernanceState) : Bool :=
  match q with
  | .ClaimPermitted k =>
      match s.protocol.graph? with
      | none => false
      | some graph => graphDecide graph s.claims k == BinaryDecision.Permit
  | .PropertyHolds p =>
      match s.protocol.graph? with
      | none => false
      | some graph => by
          classical
          exact decide (propertyHolds p graph)
  | .SacrificeDeclared p => by
      classical
      exact decide (p ∈ s.protocol.sacrifices)

/-- An observation function maps full governance state `S` to observed state
`S'`. -/
abbrev ObservationFunction (S S' : Type) := S → S'

/-- `QueryPreserving answer answer' O q` means that observation `O` preserves
the answer to governance query `q`. -/
def QueryPreserving {S S' : Type}
    (answer : GovernanceQuery → S → Bool)
    (answer' : GovernanceQuery → S' → Bool)
    (O : ObservationFunction S S') (q : GovernanceQuery) : Prop :=
  ∀ s : S, answer q s = answer' q (O s)

/-- `GovernanceObservable` means that every governance query is preserved by
the observation interface. -/
def GovernanceObservable {S S' : Type}
    (answer : GovernanceQuery → S → Bool)
    (answer' : GovernanceQuery → S' → Bool)
    (O : ObservationFunction S S') : Prop :=
  ∀ q : GovernanceQuery, QueryPreserving answer answer' O q

/-- The identity observation is governance-observable in a load-bearing sense:
it both preserves every governance query and reflects observation equality back
to query equality. -/
lemma id_is_observable {S : Type}
    (answer : GovernanceQuery → S → Bool) :
    GovernanceObservable answer answer (fun s : S => s) ∧
      ∀ (s t : S), (fun x : S => x) s = (fun x : S => x) t →
        ∀ q : GovernanceQuery, answer q s = answer q t := by
  constructor
  · intro q s
    rfl
  · intro s t hst q
    cases hst
    rfl

/-- A certificate witness for a governance decision. -/
abbrev Certificate (_Decision : Type*) := Type*

/-- A verifier checks a governance decision against a certificate witness. -/
abbrev Verifier (Decision : Type*) (W : Certificate Decision) :=
  Decision → W → Bool

/-- A resource bound for verifier execution, indexed by the decision size. -/
abbrev VerifierBound (Decision : Type*) := Decision → ℕ

/-- A certifiable decision system exposes certificates, a verifier, and a
resource bound for checking legitimate governance decisions. -/
structure CertifiableSystem (Decision : Type*) (W : Certificate Decision) where
  /-- Which governance decisions count as legitimate. -/
  legitimate : Decision → Prop
  /-- The third-party verifier. -/
  verifier : Verifier Decision W
  /-- A concrete step count for running the verifier on this input. -/
  verifierSteps : Decision → W → ℕ
  /-- The allowed verification budget for the decision. -/
  bound : VerifierBound Decision

/-- `CertificateAccepted sys d w` means that `w` certifies the legitimacy of
decision `d`. -/
def CertificateAccepted {Decision : Type*} {W : Certificate Decision}
    (sys : CertifiableSystem Decision W) (d : Decision) (w : W) : Prop :=
  sys.verifier d w = true

/-- `CertificateWithinBound sys d w` means that the verifier checks `w` for
decision `d` within the stated resource budget. -/
def CertificateWithinBound {Decision : Type*} {W : Certificate Decision}
    (sys : CertifiableSystem Decision W) (d : Decision) (w : W) : Prop :=
  sys.verifierSteps d w ≤ sys.bound d

/-- A decision system is certifiable when every legitimate decision admits a
certificate that is accepted within the stated verification budget. -/
def Certifiable {Decision : Type*} {W : Certificate Decision}
    (sys : CertifiableSystem Decision W) : Prop :=
  ∀ d : Decision, sys.legitimate d →
    ∃ w : W, CertificateAccepted sys d w ∧ CertificateWithinBound sys d w

/-- A governance system packages an observation interface together with a
resource-bounded certification interface for governance decisions. -/
structure GovernanceSystem where
  /-- The observed-state space exposed to the principal. -/
  ObservedState : Type
  /-- The observation function. -/
  observe : ObservationFunction ObservableGovernanceState ObservedState
  /-- How the principal answers governance queries from observed state. -/
  observeAnswer : GovernanceQuery → ObservedState → Bool
  /-- The type of governance decisions whose legitimacy is certified. -/
  Decision : Type
  /-- The type of certificates for governance decisions. -/
  Witness : Certificate Decision
  /-- The certification interface for governance decisions. -/
  certification : CertifiableSystem Decision Witness

/-- A governance system is certifiable when its decision interface is. -/
def SystemCertifiable (sys : GovernanceSystem) : Prop :=
  Certifiable sys.certification

/-- A system is governance-observable when its observation preserves every
governance query answer. -/
def SystemGovernanceObservable (sys : GovernanceSystem) : Prop :=
  GovernanceObservable governanceAnswer sys.observeAnswer sys.observe

/-- A concrete state whose declared sacrifice is visibly non-empty. -/
private def hiddenSacrificeState : ObservableGovernanceState where
  protocol :=
    ProtocolState.Declared peerGraph [GovernanceProperty.Consistency]
  claims := []
  estate := ⟨1, by norm_num⟩

/-- A decision system with no certificate witness type cannot certify even the
single trivial legitimate decision. -/
private def noCertificateSystem : CertifiableSystem Unit Empty where
  legitimate _ := True
  verifier _ w := nomatch w
  verifierSteps _ w := nomatch w
  bound _ := 0

/-- If the certificate type is empty, certifiability fails because no witness
can exist for a legitimate decision. -/
lemma no_certificate_type_not_certifiable :
    ¬ Certifiable noCertificateSystem := by
  intro hcert
  obtain ⟨w, _, _⟩ := hcert () trivial
  exact nomatch w

/-- A family where accepted certificates must have exponential size. -/
private def exponentialCertificateSystem
    (bound : VerifierBound ℕ) : CertifiableSystem ℕ ℕ where
  legitimate _ := True
  verifier n w := decide (w = 2 ^ n)
  verifierSteps _ w := w
  bound := bound

/-- For the exponential witness family, acceptance is exactly equality with the
required exponential certificate size. -/
lemma exponentialCertificateSystem_accepts_iff
    (bound : VerifierBound ℕ) (n w : ℕ) :
    CertificateAccepted (exponentialCertificateSystem bound) n w ↔ w = 2 ^ n := by
  simp [CertificateAccepted, exponentialCertificateSystem]

/-- Any claimed bound that is already below the required exponential witness
size on some input rules out certifiability. -/
lemma exponential_only_not_certifiable_at_bound
    (bound : VerifierBound ℕ) (n : ℕ)
    (hgap : bound n < 2 ^ n) :
    ¬ Certifiable (exponentialCertificateSystem bound) := by
  intro hcert
  obtain ⟨w, hwAccepts, hwBound⟩ := hcert n trivial
  have hw : w = 2 ^ n := by
    exact (exponentialCertificateSystem_accepts_iff bound n w).mp hwAccepts
  have hexp : 2 ^ n ≤ bound n := by
    simpa [CertificateWithinBound, exponentialCertificateSystem, hw] using hwBound
  exact Nat.not_lt_of_ge hexp hgap

/-- A concrete polynomial verification budget. -/
private def quadraticBound (n : ℕ) : ℕ :=
  n ^ 2 + 1

/-- Exponential-only certificates are not certifiable within a polynomial
budget; here the quadratic bound already fails at input size `6`. -/
lemma exponential_only_not_certifiable_with_polynomial_bound :
    ¬ Certifiable (exponentialCertificateSystem quadraticBound) := by
  apply exponential_only_not_certifiable_at_bound quadraticBound 6
  norm_num [quadraticBound]

/-- One step of a governance evaluation trace: which node ran and which local
decision it produced. -/
structure EvaluationTraceStep where
  nodeId : ℕ
  localDecision : BinaryDecision
  deriving Repr, DecidableEq

/-- A governance certificate records the replayable node-local trace together
with the claimed final decision. -/
structure GovernanceCertificate where
  trace : List EvaluationTraceStep
  finalDecision : BinaryDecision
  deriving Repr, DecidableEq

/-- Replay a trace against a concrete governance graph. The replay succeeds
only when each logged local decision matches the node computation and the trace
stops exactly when the pipeline returns a final verdict. -/
private def replayEvaluationTrace :
    GovernanceGraph → List ClaimQ → ClaimantId → ℕ →
      List EvaluationTraceStep → Option BinaryDecision
  | [], _, _, _, [] => some BinaryDecision.Permit
  | [], _, _, _, _ :: _ => none
  | node :: rest, claims, claimant, nodeId, step :: trace =>
      if step.nodeId = nodeId then
        let localDecision := node claims claimant
        if step.localDecision = localDecision then
          match localDecision with
          | .Deny =>
              match trace with
              | [] => some BinaryDecision.Deny
              | _ :: _ => none
          | .Permit =>
              replayEvaluationTrace rest (filterPermitted node claims) claimant
                (nodeId + 1) trace
        else
          none
      else
        none
  | _ :: _, _, _, _, [] => none

/-- A hidden governance scenario used for the certifiability witness. The
public verifier can replay the trace, but the observation interface still
hides the full governance state. -/
private def hiddenTraceClaims : List ClaimQ :=
  [⟨0, 1/4, by norm_num, []⟩, ⟨1, 1/2, by norm_num, []⟩, ⟨2, 3/4, by norm_num, []⟩]

/-- The claimant whose decision is certified by the hidden governance trace. -/
private def hiddenTraceClaimant : ClaimantId := 1

/-- A concrete three-stage governance graph with a nontrivial evaluation
trace for the certified claimant. -/
private def hiddenTraceGraph : GovernanceGraph :=
  [thresholdNode (1/5), peerRelativeNode, thresholdNode (3/5)]

/-- The canonical trace certificate for the hidden governance evaluation. -/
private def hiddenTraceCertificate : GovernanceCertificate where
  trace :=
    [ ⟨0, BinaryDecision.Permit⟩
    , ⟨1, BinaryDecision.Permit⟩
    , ⟨2, BinaryDecision.Deny⟩
    ]
  finalDecision := BinaryDecision.Deny

/-- Replaying the hidden governance trace yields the certified final decision. -/
private theorem hidden_trace_replays :
    replayEvaluationTrace hiddenTraceGraph hiddenTraceClaims
        hiddenTraceClaimant 0 hiddenTraceCertificate.trace =
      some hiddenTraceCertificate.finalDecision := by
  -- native_decide: finite concrete kernel-safety fixture equality and inequality checks.
  native_decide

/-- The hidden governance graph really returns the same final decision as the
certificate's replayed trace. -/
private theorem hidden_trace_matches_graph :
    graphDecide hiddenTraceGraph hiddenTraceClaims hiddenTraceClaimant =
      hiddenTraceCertificate.finalDecision := by
  native_decide

/-- A certifiable interface whose certificate is a replayable governance
evaluation trace for a concrete binary decision. -/
private def zkDecisionSystem :
    CertifiableSystem BinaryDecision GovernanceCertificate where
  legitimate d :=
    d = graphDecide hiddenTraceGraph hiddenTraceClaims hiddenTraceClaimant
  verifier d cert :=
    decide (
      replayEvaluationTrace hiddenTraceGraph hiddenTraceClaims
          hiddenTraceClaimant 0 cert.trace = some cert.finalDecision ∧
      cert.finalDecision = d
    )
  verifierSteps _ cert := cert.trace.length + hiddenTraceGraph.length
  bound _ := hiddenTraceGraph.length * 2

/-- A zero-knowledge-style certification interface: every legitimate decision
has a certificate, but the observation channel reveals no governance state. -/
private def zkCertificateSystem : GovernanceSystem where
  ObservedState := Unit
  observe := fun _ => ()
  observeAnswer := fun _ _ => false
  Decision := BinaryDecision
  Witness := GovernanceCertificate
  certification := zkDecisionSystem

/-- A legitimate zero-knowledge decision is exactly the hidden trace's final
decision. -/
lemma zk_legitimate_decision_eq_hidden_final
    {d : BinaryDecision}
    (hd : zkDecisionSystem.legitimate d) :
    d = hiddenTraceCertificate.finalDecision := by
  simpa [zkDecisionSystem, hidden_trace_matches_graph] using hd

/-- The canonical hidden trace certificate is accepted for every legitimate
zero-knowledge decision. -/
private lemma zk_hidden_certificate_accepted
    {d : BinaryDecision}
    (hd : zkDecisionSystem.legitimate d) :
    CertificateAccepted zkDecisionSystem d hiddenTraceCertificate := by
  have hd' :
      d = hiddenTraceCertificate.finalDecision :=
    zk_legitimate_decision_eq_hidden_final hd
  simp [CertificateAccepted, zkDecisionSystem, hidden_trace_replays, hd']

/-- The canonical hidden trace certificate fits the verifier's resource bound.
-/
private lemma zk_hidden_certificate_within_bound
    (d : BinaryDecision) :
    CertificateWithinBound zkDecisionSystem d hiddenTraceCertificate := by
  simp [CertificateWithinBound, zkDecisionSystem, hiddenTraceCertificate, hiddenTraceGraph]

/-- The hidden state really declares the consistency sacrifice at the full
governance interface. -/
private lemma hiddenSacrificeState_consistency_true :
    governanceAnswer
        (GovernanceQuery.SacrificeDeclared GovernanceProperty.Consistency)
        hiddenSacrificeState = true := by
  classical
  simp [governanceAnswer, hiddenSacrificeState, ProtocolState.sacrifices]

/-- The zero-knowledge observation interface answers every sacrifice query with
`false`, including the hidden consistency sacrifice. -/
private lemma zkCertificateSystem_consistency_false :
    zkCertificateSystem.observeAnswer
        (GovernanceQuery.SacrificeDeclared GovernanceProperty.Consistency)
        (zkCertificateSystem.observe hiddenSacrificeState) = false := by
  simp [zkCertificateSystem]

/-- There exists a certifiable system that is not governance-observable. -/
theorem zk_certifiable_not_observable :
    ∃ sys : GovernanceSystem, SystemCertifiable sys ∧ ¬ SystemGovernanceObservable sys := by
  refine ⟨zkCertificateSystem, ?_, ?_⟩
  · intro d hd
    refine ⟨hiddenTraceCertificate, ?_, ?_⟩
    · exact zk_hidden_certificate_accepted hd
    · exact zk_hidden_certificate_within_bound d
  · intro hobs
    have hq :=
      hobs (GovernanceQuery.SacrificeDeclared GovernanceProperty.Consistency)
        hiddenSacrificeState
    rw [zkCertificateSystem_consistency_false] at hq
    rw [hiddenSacrificeState_consistency_true] at hq
    cases hq

/-- The perfect observation interface exposes exactly the full governance query
behavior of a state, without exposing the raw state itself. -/
private abbrev PerfectObservation := GovernanceQuery → Bool

/-- Observe a state by recording its complete governance query behavior. -/
private noncomputable def perfectObserve :
    ObservationFunction ObservableGovernanceState PerfectObservation :=
  fun s q => governanceAnswer q s

/-- Answer a governance query from a perfect observation by function lookup. -/
private def perfectObserveAnswer : GovernanceQuery → PerfectObservation → Bool :=
  fun q obs => obs q

/-- A perfectly observable but non-certifiable system. -/
private noncomputable def transparentUncertifiedSystem : GovernanceSystem where
  ObservedState := PerfectObservation
  observe := perfectObserve
  observeAnswer := perfectObserveAnswer
  Decision := Unit
  Witness := Empty
  certification := noCertificateSystem

/-- There exists a governance-observable system that is not certifiable. -/
theorem observable_not_certifiable :
    ∃ sys : GovernanceSystem, SystemGovernanceObservable sys ∧ ¬ SystemCertifiable sys := by
  refine ⟨transparentUncertifiedSystem, ?_, ?_⟩
  · intro q s
    rfl
  · simpa [SystemCertifiable, transparentUncertifiedSystem] using
      no_certificate_type_not_certifiable

/-- If a property holds for the graph in a live state, the corresponding full
query answer is `true`. -/
private theorem governanceAnswer_property_true
    (claims : List ClaimQ) (estate : EstateQ)
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (p : GovernanceProperty)
    (hp : propertyHolds p compiled.graph) :
    governanceAnswer (GovernanceQuery.PropertyHolds p)
        ⟨ProtocolState.Live compiled report monitoring, claims, estate⟩ = true := by
  classical
  simp [governanceAnswer, ProtocolState.graph?, hp]

/-- If a property fails for the graph in a live state, the corresponding full
query answer is `false`. -/
private theorem governanceAnswer_property_false
    (claims : List ClaimQ) (estate : EstateQ)
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (p : GovernanceProperty)
    (hp : ¬ propertyHolds p compiled.graph) :
    governanceAnswer (GovernanceQuery.PropertyHolds p)
        ⟨ProtocolState.Live compiled report monitoring, claims, estate⟩ = false := by
  classical
  simp [governanceAnswer, ProtocolState.graph?, hp]

/-- In any live protocol execution, every non-sacrificed property truly holds
of the compiled governance graph. -/
lemma protocol_live_soundness_property_holds
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (p : GovernanceProperty)
    (hp : p ∉ compiled.sacrifices) :
    propertyHolds p compiled.graph :=
  (protocol_live_soundness hpath).1 p hp

/-- In any live protocol execution, every sacrificed property truly fails for
the compiled governance graph. -/
lemma protocol_live_soundness_property_fails
    {compiled : CompiledGovernance}
    {report : GovernanceRiskReport}
    {monitoring : MonitoringPlan}
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring))
    (p : GovernanceProperty)
    (hp : p ∈ compiled.sacrifices) :
    ¬ propertyHolds p compiled.graph :=
  (protocol_live_soundness hpath).2.1 p hp

/-- Governance observability preserves property-query answers from the full
state to the observed interface. -/
lemma observable_preserves_property_query
    {S' : Type}
    (observe : ObservationFunction ObservableGovernanceState S')
    (observeAnswer : GovernanceQuery → S' → Bool)
    (hobs : GovernanceObservable governanceAnswer observeAnswer observe)
    (s : ObservableGovernanceState)
    (p : GovernanceProperty) :
    observeAnswer (GovernanceQuery.PropertyHolds p) (observe s) =
      governanceAnswer (GovernanceQuery.PropertyHolds p) s := by
  simpa using (hobs (GovernanceQuery.PropertyHolds p) s).symm

/-- Governance observability is sufficient to recover the protocol soundness
conclusions from the observed interface alone. -/
theorem observable_sufficient_for_protocol
    {S' : Type}
    (observe : ObservationFunction ObservableGovernanceState S')
    (observeAnswer : GovernanceQuery → S' → Bool)
    (hobs : GovernanceObservable governanceAnswer observeAnswer observe)
    (claims : List ClaimQ) (estate : EstateQ)
    (compiled : CompiledGovernance)
    (report : GovernanceRiskReport)
    (monitoring : MonitoringPlan)
    (hpath : TransitionSequence
      ProtocolState.Undeclared
      (ProtocolState.Live compiled report monitoring)) :
    let s : ObservableGovernanceState :=
      ⟨ProtocolState.Live compiled report monitoring, claims, estate⟩
    (∀ p : GovernanceProperty,
        p ∉ compiled.sacrifices →
          observeAnswer (GovernanceQuery.PropertyHolds p) (observe s) = true) ∧
    (∀ p : GovernanceProperty,
        p ∈ compiled.sacrifices →
          observeAnswer (GovernanceQuery.PropertyHolds p) (observe s) = false) := by
  let s : ObservableGovernanceState :=
    ⟨ProtocolState.Live compiled report monitoring, claims, estate⟩
  constructor
  · intro p hp
    have hprop : propertyHolds p compiled.graph :=
      protocol_live_soundness_property_holds hpath p hp
    rw [observable_preserves_property_query observe observeAnswer hobs s p]
    exact governanceAnswer_property_true claims estate compiled report monitoring p hprop
  · intro p hp
    have hprop : ¬ propertyHolds p compiled.graph :=
      protocol_live_soundness_property_fails hpath p hp
    rw [observable_preserves_property_query observe observeAnswer hobs s p]
    exact governanceAnswer_property_false claims estate compiled report monitoring p hprop

end Legitimacy
