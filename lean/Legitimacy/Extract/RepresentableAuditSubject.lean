/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Reflective.ProductionSelfAudit
import Legitimacy.Impossibility.PeerRelativeReachable
import Legitimacy.Extract.AuditClaimQEncoding

/-!
# Faithful representation for constrained audit subjects

This module gives the narrow bridge used by the production self-audit and
peer-relative obstruction layers.  The represented class is deliberately small:
source-backed subjects whose source semantics are first-match gates with
explicit gate metadata.  The representation into `GovernanceGraph` carries the
gate decision behavior itself; it is not the placeholder
`liftGovernanceGraphToAuditGraph` projection.

The load-bearing theorem is `RepresentableAuditSubject.decision_equivalent`:
for every represented subject, every `List ClaimQ`, and every claimant, the
independently defined source evaluator agrees with `graphDecide` on the
represented graph.  This is the all-profile bridge; no finite synthetic corpus
is used in that proof.

FRAMEWORK-LIMITS: `GovernanceGraph` is binary, while extracted audit graphs
use the three-valued `AuditDecision`.  The scarce-allocation projection used
below treats a terminal `.escalate` as binary denial, because unresolved review
is not a resource grant.  Edge-bearing escalation is represented as
continuation to downstream adjudication; if no downstream stage grants the
claim, the terminal projection is still denial.  The round-2 companion module
states which projected decision surface is represented rather than silently
collapsing the three-valued audit semantics.
-/

set_option autoImplicit false

namespace Legitimacy

/-! ## First-match source representation -/

/-- Gate families admitted by the faithful representation class.  Metadata and
strength gates cover Codex/Claude/CrewAI-style hook surfaces; the
`weakestWithStrongerPeer` gate supplies the peer-relative obstruction witness
without turning the class into an arbitrary graph carrier. -/
inductive RepresentableGateKind where
  | always
  | metadataExact (field value : String)
  | metadataAll (fields : List (String × String))
  | strengthAtLeast (minimum : ℚ)
  | weakestWithStrongerPeer
  deriving Repr

/-- Semantic match predicate for represented source gates. -/
def RepresentableGateKind.Matches
    (kind : RepresentableGateKind)
    (claims : List ClaimQ)
    (claimant : ClaimantId) : Prop :=
  match kind with
  | .always => True
  | .metadataExact field value =>
      ClaimProfile.lookup claims claimant field = some value
  | .metadataAll fields =>
      ∀ fieldValue ∈ fields,
        ClaimProfile.lookup claims claimant fieldValue.1 =
          some fieldValue.2
  | .strengthAtLeast minimum =>
      minimum ≤ lookupStrength claimant claims
  | .weakestWithStrongerPeer =>
      DecisionPipeline.WeakestWithStrongerPeer claims claimant

/-- A represented first-match gate carries both source behavior and audit-facing
metadata/polarity.  The metadata fields do not drive the proof; they prevent
the representation class from being an unannotated function list. -/
structure RepresentableGate where
  kind : RepresentableGateKind
  decision : BinaryDecision
  polarity : AuditMetricPolarity
  metadataField : Option String
  deriving Repr

/-- A represented source node is exactly a first-match gate sequence with a
known default decision. -/
structure RepresentableNode where
  name : String
  gates : List RepresentableGate
  default : BinaryDecision
  deriving Repr

namespace RepresentableNode

/-- First-match evaluation over a gate list. -/
noncomputable def decideGates
    (claims : List ClaimQ) (claimant : ClaimantId)
    (default : BinaryDecision) : List RepresentableGate → BinaryDecision
  | [] => default
  | gate :: rest => by
      classical
      exact
        if gate.kind.Matches claims claimant then
          gate.decision
        else
          decideGates claims claimant default rest

@[simp] theorem decideGates_nil
    (claims : List ClaimQ) (claimant : ClaimantId)
    (default : BinaryDecision) :
    decideGates claims claimant default [] = default :=
  rfl

theorem decideGates_cons_of_matches
    {claims : List ClaimQ} {claimant : ClaimantId}
    {default : BinaryDecision} {gate : RepresentableGate}
    {rest : List RepresentableGate}
    (h : gate.kind.Matches claims claimant) :
    decideGates claims claimant default (gate :: rest) =
      gate.decision := by
  classical
  simp [decideGates, h]

theorem decideGates_cons_of_not_matches
    {claims : List ClaimQ} {claimant : ClaimantId}
    {default : BinaryDecision} {gate : RepresentableGate}
    {rest : List RepresentableGate}
    (h : ¬ gate.kind.Matches claims claimant) :
    decideGates claims claimant default (gate :: rest) =
      decideGates claims claimant default rest := by
  classical
  simp [decideGates, h]

/-- Independent source evaluator for a represented first-match node. -/
noncomputable def decide (node : RepresentableNode)
    (claims : List ClaimQ) (claimant : ClaimantId) : BinaryDecision :=
  decideGates claims claimant node.default node.gates

/-- Faithful node representation: the governance node is the represented
first-match source evaluator itself. -/
noncomputable def toGovernanceNode (node : RepresentableNode) :
    GovernanceNodeFn :=
  fun claims claimant => node.decide claims claimant

end RepresentableNode

/-- Source-level represented audit surface. -/
structure RepresentableSource where
  nodes : List RepresentableNode
  deriving Repr

namespace RepresentableSource

/-- Independent source traversal for represented first-match nodes. -/
noncomputable def decideNodes : List RepresentableNode →
    List ClaimQ → ClaimantId → BinaryDecision
  | [], _, _ => BinaryDecision.Permit
  | node :: rest, claims, claimant =>
      match node.decide claims claimant with
      | BinaryDecision.Deny => BinaryDecision.Deny
      | BinaryDecision.Permit =>
          let forwarded := filterPermitted node.toGovernanceNode claims
          decideNodes rest forwarded claimant

/-- Source traversal packaged at the `RepresentableSource` level.  It is
defined separately from `graphDecide` so the equivalence theorem below is a
derived induction rather than definitional pass-through. -/
noncomputable def decide (source : RepresentableSource)
    (claims : List ClaimQ) (claimant : ClaimantId) : BinaryDecision :=
  decideNodes source.nodes claims claimant

/-- The faithful `GovernanceGraph` representation of a represented source. -/
noncomputable def toGovernanceGraph
    (source : RepresentableSource) : GovernanceGraph :=
  source.nodes.map RepresentableNode.toGovernanceNode

/-- Wrapper exposing represented source semantics through `DecisionSystem`. -/
structure Semantics where
  source : RepresentableSource

noncomputable instance :
    DecisionSystem Semantics (List ClaimQ) ClaimantId BinaryDecision where
  decide system := system.source.decide

/-- All-profile decision equivalence between the independent source traversal
and the concrete `GovernanceGraph` representation. -/
theorem graphDecide_map_toGovernanceNode_eq_decideNodes
    (nodes : List RepresentableNode)
    (claims : List ClaimQ)
    (claimant : ClaimantId) :
    graphDecide (nodes.map RepresentableNode.toGovernanceNode) claims
        claimant =
      decideNodes nodes claims claimant := by
  induction nodes generalizing claims with
  | nil =>
      rfl
  | cons node rest ih =>
      cases hnode : node.decide claims claimant
      · simp [decideNodes, RepresentableNode.toGovernanceNode,
          graphDecide, hnode, ih]
      · simp [decideNodes, RepresentableNode.toGovernanceNode,
          graphDecide, hnode]

/-- All-profile decision equivalence between the independent source traversal
and the concrete `GovernanceGraph` representation. -/
theorem graphDecide_toGovernanceGraph_eq_decide
    (source : RepresentableSource)
    (claims : List ClaimQ)
    (claimant : ClaimantId) :
    graphDecide source.toGovernanceGraph claims claimant =
      source.decide claims claimant := by
  simpa [toGovernanceGraph, decide] using
    graphDecide_map_toGovernanceNode_eq_decideNodes
      source.nodes claims claimant

end RepresentableSource

/-- The canonical all-profile source-faithful evaluator for a represented
source.  For every audit profile reaching a node, it validates the profile,
reflects non-query claims into `ClaimQ`, evaluates the represented source, and
embeds the binary result back into the audit decision surface.  Reserved query
claims ask for a claimant decision without becoming part of the decided
profile. -/
noncomputable def sourceFaithfulAuditNodeEvaluator
    (source : RepresentableSource) : AuditNodeEvaluator :=
  fun _node claims => do
    validateAuditGovernanceClaims claims
    let profile := auditGovernanceClaimsToDecisionProfile claims
    claims.mapM fun claim =>
      pure
        { claimantId := claim.claimantId
          decision :=
            (source.decide profile
              (auditGovernanceClaimToClaimantId claims claim)).toAuditDecision }

/-- Audit subjects admitted by the bridge.  The `AuditSubject` is retained so
the production certificate and reflective box remain about the same object; the
source is retained so the represented graph has all-profile source semantics. -/
structure RepresentableAuditSubject where
  name : String
  subject : AuditSubject
  source : RepresentableSource

namespace RepresentableAuditSubject

/-- Every audit node in the constrained class is a first-match binary gate. -/
def AuditGraphFirstMatchOnly (subject : AuditSubject) : Prop :=
  ∀ node ∈ subject.graph.nodes,
    ∃ id name gates defaultDecision,
      node =
        AuditGovernanceNode.binary id name gates defaultDecision
          AuditGateLogic.firstMatch

/-- Constrained representation predicate: nonempty first-match source nodes
with an audit graph carrying the same node count and no non-first-match audit
nodes. -/
def Representable (subject : RepresentableAuditSubject) : Prop :=
  subject.source.nodes ≠ [] ∧
    subject.subject.graph.nodes.length = subject.source.nodes.length ∧
      AuditGraphFirstMatchOnly subject.subject

/-- Audit-source faithfulness for represented subjects.  The carried audit
evaluator itself must be the all-profile source-faithful evaluator; a
structurally representable source paired with an unrelated production
`evalNode` is excluded. -/
def AuditSourceFaithful (subject : RepresentableAuditSubject) : Prop :=
  subject.subject.evalNode = sourceFaithfulAuditNodeEvaluator subject.source

theorem AuditSourceFaithful.evalNode_all_profiles
    {subject : RepresentableAuditSubject}
    (hfaith : AuditSourceFaithful subject)
    (node : AuditGovernanceNode)
    (claims : List AuditGovernanceClaim) :
    subject.subject.evalNode node claims =
      sourceFaithfulAuditNodeEvaluator subject.source node claims := by
  rw [hfaith]

/-- Strengthened representation predicate: structural representability plus an
all-profile evaluator/source weld. -/
def FaithfulRepresentable (subject : RepresentableAuditSubject) : Prop :=
  Representable subject ∧ AuditSourceFaithful subject

/-- Faithful representation of constrained audit subjects as governance
graphs. -/
noncomputable def repr
    (subject : { s : RepresentableAuditSubject // Representable s }) :
    GovernanceGraph :=
  subject.1.source.toGovernanceGraph

/-- Representation for the strengthened subtype. -/
noncomputable def faithfulRepr
    (subject : { s : RepresentableAuditSubject // FaithfulRepresentable s }) :
    GovernanceGraph :=
  repr ⟨subject.1, subject.2.1⟩

/-- Source semantics for a represented audit subject. -/
def sourceSemantics
    (subject : { s : RepresentableAuditSubject // Representable s }) :
    RepresentableSource.Semantics :=
  ⟨subject.1.source⟩

/-- All-profile decision equivalence for represented audit subjects.  The
universal quantifier is over the real `ClaimQ` profile type consumed by
`GraphConsistencyP`, not over `auditGraphClaims`. -/
theorem decision_equivalent
    (subject : { s : RepresentableAuditSubject // Representable s }) :
    DecisionSystem.Equivalent (sourceSemantics subject) (repr subject) := by
  intro claims claimant
  exact
    (RepresentableSource.graphDecide_toGovernanceGraph_eq_decide
      subject.1.source claims claimant).symm

end RepresentableAuditSubject

/-! ## A structural peer-relative source node -/

/-- The obstruction node denies exactly claimants that are weakest in a
nontrivial profile with a stronger peer; otherwise it permits. -/
noncomputable def weakestWithStrongerPeerNode : GovernanceNodeFn := fun claims k => by
  classical
  exact
    if DecisionPipeline.WeakestWithStrongerPeer claims k then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit

lemma weakestWithStrongerPeerNode_of_weakest
    {claims : List ClaimQ} {k : ClaimantId}
    (h : DecisionPipeline.WeakestWithStrongerPeer claims k) :
    weakestWithStrongerPeerNode claims k = BinaryDecision.Deny := by
  classical
  simp [weakestWithStrongerPeerNode, h]

lemma weakestWithStrongerPeerNode_of_not_weakest
    {claims : List ClaimQ} {k : ClaimantId}
    (h : ¬ DecisionPipeline.WeakestWithStrongerPeer claims k) :
    weakestWithStrongerPeerNode claims k = BinaryDecision.Permit := by
  classical
  simp [weakestWithStrongerPeerNode, h]

private lemma hasStrictlyWeakerPeer_not_weakest
    {claims : List ClaimQ} {k : ClaimantId}
    (hweaker : DecisionPipeline.HasStrictlyWeakerPeer claims k) :
    ¬ DecisionPipeline.WeakestWithStrongerPeer claims k := by
  intro hweakest
  rcases hweaker with ⟨j, _hjk, hj, hlt⟩
  have hle := hweakest.2.1 j hj
  linarith

private lemma weakestWithStrongerPeer_congr_equal_strength
    {claims : List ClaimQ} {k j : ClaimantId}
    (hj : InClaims j claims)
    (hsame : lookupStrength k claims = lookupStrength j claims) :
    DecisionPipeline.WeakestWithStrongerPeer claims k →
      DecisionPipeline.WeakestWithStrongerPeer claims j := by
  intro hweak
  rcases hweak with ⟨_hk, hall, m, _hmk, hm, hlt⟩
  refine ⟨hj, ?_, ?_⟩
  · intro q hq
    rw [← hsame]
    exact hall q hq
  · refine ⟨m, ?_, hm, ?_⟩
    · intro hmj
      subst m
      rw [hsame] at hlt
      exact (lt_irrefl _ hlt).elim
    · rw [← hsame]
      exact hlt

private theorem weakestWithStrongerPeerNode_symmetry :
    DecisionPipeline.ClaimantSymmetric
      (P := GovernanceGraph) weakestWithStrongerPeerNode := by
  intro claims k j _hdist hk hj hsame
  change weakestWithStrongerPeerNode claims k =
    weakestWithStrongerPeerNode claims j
  by_cases hkweak : DecisionPipeline.WeakestWithStrongerPeer claims k
  · have hjweak : DecisionPipeline.WeakestWithStrongerPeer claims j :=
      weakestWithStrongerPeer_congr_equal_strength hj hsame hkweak
    rw [weakestWithStrongerPeerNode_of_weakest hkweak,
      weakestWithStrongerPeerNode_of_weakest hjweak]
  · have hjnot : ¬ DecisionPipeline.WeakestWithStrongerPeer claims j := by
      intro hjweak
      have hkweak' : DecisionPipeline.WeakestWithStrongerPeer claims k :=
        weakestWithStrongerPeer_congr_equal_strength hk hsame.symm hjweak
      exact hkweak hkweak'
    rw [weakestWithStrongerPeerNode_of_not_weakest hkweak,
      weakestWithStrongerPeerNode_of_not_weakest hjnot]

private theorem weakestWithStrongerPeerNode_own_response :
    DecisionPipeline.OwnStrengthResponsive
      (P := GovernanceGraph) weakestWithStrongerPeerNode := by
  intro claims k _hdist _hk hweaker
  change weakestWithStrongerPeerNode claims k = BinaryDecision.Permit
  exact weakestWithStrongerPeerNode_of_not_weakest
    (hasStrictlyWeakerPeer_not_weakest hweaker)

private theorem weakestWithStrongerPeerNode_tie_break :
    DecisionPipeline.TieBreakNeutral
      (P := GovernanceGraph) weakestWithStrongerPeerNode := by
  intro claims k _hdist _hk hweak
  change weakestWithStrongerPeerNode claims k = BinaryDecision.Deny
  exact weakestWithStrongerPeerNode_of_weakest hweak

private theorem weakestWithStrongerPeerNode_finite_estate :
    DecisionPipeline.FiniteEstateCoupled
      (P := GovernanceGraph) weakestWithStrongerPeerNode := by
  intro claims hdistinct hscarce _hadmissible
  rcases hscarce with ⟨hgenerator, _⟩
  refine ⟨hgenerator.displaced, hgenerator.displaced_in_claims, ?_⟩
  exact weakestWithStrongerPeerNode_tie_break claims hgenerator.displaced
    hdistinct hgenerator.displaced_in_claims hgenerator.displaced_weakest

private def structuralWitnessA : ClaimQ :=
  ⟨0, 1 / 4, by norm_num, []⟩

private def structuralWitnessAStrengthened : ClaimQ :=
  ⟨0, 3 / 4, by norm_num, []⟩

private def structuralWitnessB : ClaimQ :=
  ⟨1, 1 / 2, by norm_num, []⟩

private def structuralWitnessC : ClaimQ :=
  ⟨2, 3 / 4, by norm_num, []⟩

private def structuralWitnessClaims : List ClaimQ :=
  [structuralWitnessA, structuralWitnessB, structuralWitnessC]

private def structuralContextClaims : List ClaimQ :=
  [structuralWitnessA, structuralWitnessB]

private def structuralContextClaimsSingleton : List ClaimQ :=
  [structuralWitnessA]

private lemma in_structuralWitnessClaims_ids {j : ClaimantId}
    (h : InClaims j structuralWitnessClaims) :
    j = 0 ∨ j = 1 ∨ j = 2 := by
  rcases h with ⟨c, hc, hid⟩
  simp [structuralWitnessClaims] at hc
  rcases hc with hc | hc | hc
  · subst c
    simp [structuralWitnessA] at hid
    exact Or.inl hid.symm
  · subst c
    simp [structuralWitnessB] at hid
    exact Or.inr (Or.inl hid.symm)
  · subst c
    simp [structuralWitnessC] at hid
    exact Or.inr (Or.inr hid.symm)

private lemma in_strengthenedStructuralWitnessClaims_ids {j : ClaimantId}
    (h :
      InClaims j
        (strengthenClaim 0 (3 / 4) (by norm_num)
          structuralWitnessClaims)) :
    j = 0 ∨ j = 1 ∨ j = 2 := by
  rcases h with ⟨c, hc, hid⟩
  simp [structuralWitnessClaims, structuralWitnessA, structuralWitnessB,
    structuralWitnessC, strengthenClaim] at hc
  rcases hc with hc | hc | hc
  · subst c
    simp at hid
    exact Or.inl hid.symm
  · subst c
    simp at hid
    exact Or.inr (Or.inl hid.symm)
  · subst c
    simp at hid
    exact Or.inr (Or.inr hid.symm)

private lemma in_removedStructuralWitnessClaims_ids {j : ClaimantId}
    (h : InClaims j (removeClaimGraph 0 structuralWitnessClaims)) :
    j = 1 ∨ j = 2 := by
  rcases h with ⟨c, hc, hid⟩
  simp [structuralWitnessClaims, structuralWitnessA, structuralWitnessB,
    structuralWitnessC, removeClaimGraph] at hc
  rcases hc with hc | hc
  · subst c
    simp at hid
    exact Or.inl hid.symm
  · subst c
    simp at hid
    exact Or.inr hid.symm

private theorem structuralWitnessClaims_distinct :
    ClaimsDistinct structuralWitnessClaims := by
  unfold ClaimsDistinct structuralWitnessClaims structuralWitnessA
    structuralWitnessB structuralWitnessC
  show ([0, 1, 2] : List Nat).Nodup
  decide

private theorem structuralWitnessB_has_weaker :
    DecisionPipeline.HasStrictlyWeakerPeer structuralWitnessClaims 1 := by
  refine ⟨0, ?_, ?_, ?_⟩ <;> native_decide

private theorem structuralWitnessA_weakest :
    DecisionPipeline.WeakestWithStrongerPeer structuralWitnessClaims 0 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · intro j hj
    rcases in_structuralWitnessClaims_ids hj with rfl | rfl | rfl <;>
      native_decide
  · refine ⟨1, ?_, ?_, ?_⟩ <;> native_decide

private theorem structuralWitnessB_weakest_after_strengthening :
    DecisionPipeline.WeakestWithStrongerPeer
      (strengthenClaim 0 (3 / 4) (by norm_num)
        structuralWitnessClaims) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · intro j hj
    rcases in_strengthenedStructuralWitnessClaims_ids hj with
      rfl | rfl | rfl <;> native_decide
  · refine ⟨0, ?_, ?_, ?_⟩ <;> native_decide

private theorem structuralWitnessB_weakest_after_removal :
    DecisionPipeline.WeakestWithStrongerPeer
      (removeClaimGraph 0 structuralWitnessClaims) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · intro j hj
    rcases in_removedStructuralWitnessClaims_ids hj with rfl | rfl <;>
      native_decide
  · refine ⟨2, ?_, ?_, ?_⟩ <;> native_decide

private def weakestWithStrongerPeerObstructionGenerator :
    DecisionPipeline.ObstructionGenerator structuralWitnessClaims where
  displaced := 0
  affected := 1
  strengthened_strength := 3 / 4
  strengthened_strength_pos := by norm_num
  distinct_claimants := by decide
  displaced_in_claims := by native_decide
  affected_in_claims := by native_decide
  affected_in_strengthened := by native_decide
  affected_in_removed := by native_decide
  strengthened_claims_distinct := by
    unfold ClaimsDistinct structuralWitnessClaims structuralWitnessA
      structuralWitnessB structuralWitnessC strengthenClaim
    show ([0, 1, 2] : List Nat).Nodup
    decide
  removed_claims_distinct := by
    unfold ClaimsDistinct
    simp [structuralWitnessClaims, structuralWitnessA, structuralWitnessB,
      structuralWitnessC, removeClaimGraph]
  strengthened_bound := by
    intro c hc hid
    rcases List.mem_cons.mp hc with hcA | htail
    · subst c
      simp [structuralWitnessA] at hid ⊢
      norm_num
    · rcases List.mem_cons.mp htail with hcB | htail2
      · subst c
        simp [structuralWitnessB] at hid
      · rcases List.mem_cons.mp htail2 with hcC | hnil
        · subst c
          simp [structuralWitnessC] at hid
        · exact False.elim (List.not_mem_nil hnil)
  affected_strength_preserved := by native_decide
  affected_has_weaker := structuralWitnessB_has_weaker
  displaced_weakest := structuralWitnessA_weakest
  affected_weakest_after_strengthening :=
    structuralWitnessB_weakest_after_strengthening
  affected_weakest_after_removal :=
    structuralWitnessB_weakest_after_removal

private theorem singleton_not_weakest (claim : ClaimQ) :
    ¬ DecisionPipeline.WeakestWithStrongerPeer [claim] claim.id := by
  intro hweak
  rcases hweak.2.2 with ⟨m, _hm, hm_in, hlt⟩
  rcases hm_in with ⟨d, hd, hid⟩
  simp at hd
  subst d
  subst m
  simp [lookupStrength] at hlt

private theorem weakestWithStrongerPeerNode_individually_admissible :
    DecisionPipeline.IndividuallyAdmissible
      (P := GovernanceGraph) weakestWithStrongerPeerNode
      structuralWitnessClaims := by
  intro c _hc
  change weakestWithStrongerPeerNode [c] c.id = BinaryDecision.Permit
  exact weakestWithStrongerPeerNode_of_not_weakest (singleton_not_weakest c)

private theorem weakestWithStrongerPeerNode_peer_sensitive :
    DecisionPipeline.PeerRelativeByContext
      (P := GovernanceGraph) weakestWithStrongerPeerNode := by
  refine
    ⟨structuralContextClaims, structuralContextClaimsSingleton, 0,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · unfold ClaimsDistinct structuralContextClaims structuralWitnessA
      structuralWitnessB
    show ([0, 1] : List Nat).Nodup
    decide
  · unfold ClaimsDistinct structuralContextClaimsSingleton structuralWitnessA
    show ([0] : List Nat).Nodup
    decide
  · native_decide
  · change weakestWithStrongerPeerNode structuralContextClaims 0 ≠
      weakestWithStrongerPeerNode structuralContextClaimsSingleton 0
    have hweak : DecisionPipeline.WeakestWithStrongerPeer
        structuralContextClaims 0 := by
      refine ⟨?_, ?_, ?_⟩
      · native_decide
      · intro j hj
        rcases hj with ⟨c, hc, hid⟩
        simp [structuralContextClaims] at hc
        rcases hc with hcA | hcB
        · subst c
          simp [structuralWitnessA] at hid
          subst j
          native_decide
        · subst c
          simp [structuralWitnessB] at hid
          subst j
          native_decide
      · refine ⟨1, ?_, ?_, ?_⟩ <;> native_decide
    have hnot : ¬ DecisionPipeline.WeakestWithStrongerPeer
        structuralContextClaimsSingleton 0 := by
      intro hsingle
      rcases hsingle.2.2 with ⟨m, _hm, hm_in, hlt⟩
      rcases hm_in with ⟨c, hc, hid⟩
      simp [structuralContextClaimsSingleton] at hc
      subst c
      simp [structuralWitnessA] at hid
      subst m
      exact (lt_irrefl _ hlt).elim
    rw [weakestWithStrongerPeerNode_of_weakest hweak,
      weakestWithStrongerPeerNode_of_not_weakest hnot]
    exact BinaryDecision.noConfusion

private theorem weakestWithStrongerPeerNode_nontrivial_acceptance :
    ∃ claims k, ClaimsDistinct claims ∧ InClaims k claims ∧
      DecisionPipeline.evalNode (P := GovernanceGraph)
        weakestWithStrongerPeerNode claims k = BinaryDecision.Permit := by
  refine ⟨[structuralWitnessA], 0, ?_, ?_, ?_⟩
  · unfold ClaimsDistinct structuralWitnessA
    show ([0] : List Nat).Nodup
    decide
  · native_decide
  · change weakestWithStrongerPeerNode [structuralWitnessA] 0 =
      BinaryDecision.Permit
    exact weakestWithStrongerPeerNode_of_not_weakest
      (singleton_not_weakest structuralWitnessA)

private theorem weakestWithStrongerPeerNode_scarcity_pressure :
    ∃ claims, ClaimsDistinct claims ∧
      DecisionPipeline.OverSubscribed claims ∧
        DecisionPipeline.IndividuallyAdmissible
          (P := GovernanceGraph) weakestWithStrongerPeerNode claims := by
  exact
    ⟨structuralWitnessClaims, structuralWitnessClaims_distinct,
      ⟨weakestWithStrongerPeerObstructionGenerator, True.intro⟩,
      weakestWithStrongerPeerNode_individually_admissible⟩

/-- The represented weakest-with-stronger-peer source node satisfies the
structural scarce peer-relative class consumed by the reachable obstruction. -/
theorem weakestWithStrongerPeerNode_structural :
    DecisionPipeline.StructuralScarcePeerRelativeAllocator
      (P := GovernanceGraph) weakestWithStrongerPeerNode where
  peer_sensitive := weakestWithStrongerPeerNode_peer_sensitive
  finite_estate := weakestWithStrongerPeerNode_finite_estate
  nontrivial_acceptance := weakestWithStrongerPeerNode_nontrivial_acceptance
  scarcity_pressure := weakestWithStrongerPeerNode_scarcity_pressure
  symmetry := weakestWithStrongerPeerNode_symmetry
  positive_own_response := weakestWithStrongerPeerNode_own_response
  no_arbitrary_tie_break := weakestWithStrongerPeerNode_tie_break

/-! ## Canonical median node structural boundary -/

private def peerRelativeEvenWeakA : ClaimQ :=
  ⟨0, 1 / 4, by norm_num, []⟩

private def peerRelativeEvenWeakB : ClaimQ :=
  ⟨1, 1 / 2, by norm_num, []⟩

private def peerRelativeEvenWeakClaims : List ClaimQ :=
  [peerRelativeEvenWeakA, peerRelativeEvenWeakB]

private theorem peerRelativeEvenWeakClaims_distinct :
    ClaimsDistinct peerRelativeEvenWeakClaims := by
  unfold ClaimsDistinct peerRelativeEvenWeakClaims peerRelativeEvenWeakA
    peerRelativeEvenWeakB
  show ([0, 1] : List Nat).Nodup
  decide

private theorem peerRelativeEvenWeakA_weakest :
    DecisionPipeline.WeakestWithStrongerPeer peerRelativeEvenWeakClaims 0 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · intro j hj
    rcases hj with ⟨c, hc, hid⟩
    simp [peerRelativeEvenWeakClaims] at hc
    rcases hc with hA | hB
    · subst c
      simp [peerRelativeEvenWeakA] at hid
      subst j
      native_decide
    · subst c
      simp [peerRelativeEvenWeakB] at hid
      subst j
      native_decide
  · refine ⟨1, ?_, ?_, ?_⟩ <;> native_decide

private theorem peerRelativeNode_permits_even_weakest :
    peerRelativeNode peerRelativeEvenWeakClaims 0 = BinaryDecision.Permit := by
  native_decide

/-- The canonical median-style `peerRelativeNode` is not an inhabitant of
`StructuralScarcePeerRelativeAllocator`: in a two-claimant profile it permits the
weaker claimant, while the structural class's tie-break-neutral field requires
every weakest claimant with a stronger peer to be denied. -/
theorem peerRelativeNode_not_structural :
    ¬ DecisionPipeline.StructuralScarcePeerRelativeAllocator
      (P := GovernanceGraph) peerRelativeNode := by
  intro hstruct
  have hdeny_eval := hstruct.no_arbitrary_tie_break
    peerRelativeEvenWeakClaims 0
    peerRelativeEvenWeakClaims_distinct (by native_decide)
    peerRelativeEvenWeakA_weakest
  have hdeny :
      peerRelativeNode peerRelativeEvenWeakClaims 0 = BinaryDecision.Deny := by
    simpa [DecisionPipeline.evalNode] using hdeny_eval
  rw [peerRelativeNode_permits_even_weakest] at hdeny
  exact BinaryDecision.noConfusion hdeny

/-! ## Concrete represented subjects and floor tests -/

def weakestWithStrongerPeerGate : RepresentableGate where
  kind := .weakestWithStrongerPeer
  decision := BinaryDecision.Deny
  polarity := AuditMetricPolarity.lowerBetter
  metadataField := some "peer_relative_rank"

def weakestWithStrongerPeerRepresentableNode : RepresentableNode where
  name := "weakest-with-stronger-peer"
  gates := [weakestWithStrongerPeerGate]
  default := BinaryDecision.Permit

theorem weakestWithStrongerPeerRepresentableNode_toGovernanceNode :
    weakestWithStrongerPeerRepresentableNode.toGovernanceNode =
      weakestWithStrongerPeerNode := by
  funext claims claimant
  classical
  by_cases hweak :
      DecisionPipeline.WeakestWithStrongerPeer claims claimant
  · have hmatch :
        weakestWithStrongerPeerGate.kind.Matches claims claimant := by
      simpa [weakestWithStrongerPeerGate, RepresentableGateKind.Matches]
        using hweak
    rw [RepresentableNode.toGovernanceNode, RepresentableNode.decide,
      weakestWithStrongerPeerRepresentableNode,
      weakestWithStrongerPeerNode_of_weakest hweak]
    exact RepresentableNode.decideGates_cons_of_matches hmatch
  · have hmatch :
        ¬ weakestWithStrongerPeerGate.kind.Matches claims claimant := by
      simpa [weakestWithStrongerPeerGate, RepresentableGateKind.Matches]
        using hweak
    rw [RepresentableNode.toGovernanceNode, RepresentableNode.decide,
      weakestWithStrongerPeerRepresentableNode,
      weakestWithStrongerPeerNode_of_not_weakest hweak]
    exact RepresentableNode.decideGates_cons_of_not_matches hmatch

private def representedPeerAuditNodeId : AuditNodeId :=
  "represented-peer-source"

private def representedPeerAuditGates : List AuditGate :=
  [ .thresholdGate "peer_relative_rank" (1 / 2) .permit
  , .thresholdGate "peer_relative_rank" (3 / 4) .permit
  , .thresholdGate "peer_relative_rank" 1 .permit
  ]

private def representedPeerAuditGraphData : AuditGovernanceGraph where
  nodes :=
    [ .binary representedPeerAuditNodeId "represented peer source"
        representedPeerAuditGates .permit .firstMatch ]
  edges := []

private def representedPeerAuditRank (claimantId : AuditClaimantId) : ℚ :=
  if claimantId = "baseline" then 1 / 4
  else if claimantId = representedPeerAuditNodeId ++ "-gate-0" then 1 / 2
  else if claimantId = representedPeerAuditNodeId ++ "-gate-1" then 3 / 4
  else if claimantId = representedPeerAuditNodeId ++ "-gate-2" then 1
  else 1

private def auditWeakestWithStronger
    (claims : List AuditGovernanceClaim) (claim : AuditGovernanceClaim) :
    Bool :=
  let s := representedPeerAuditRank claim.claimantId
  claims.all (fun other => s ≤ representedPeerAuditRank other.claimantId) &&
    claims.any (fun other => s < representedPeerAuditRank other.claimantId)

private def representedPeerAuditEvalNode : AuditNodeEvaluator :=
  fun _node claims => do
    validateAuditGovernanceClaims claims
    claims.mapM fun claim =>
      pure
        { claimantId := claim.claimantId
          decision :=
            if auditWeakestWithStronger claims claim then
              AuditDecision.deny
            else
              AuditDecision.permit }

def representedPeerAuditSubject : AuditSubject where
  graph := representedPeerAuditGraphData
  evalNode := representedPeerAuditEvalNode

def representedPeerSource : RepresentableSource where
  nodes := [weakestWithStrongerPeerRepresentableNode]

def representedPeerSubject : RepresentableAuditSubject where
  name := "represented-peer-relative-obstruction"
  subject := representedPeerAuditSubject
  source := representedPeerSource

theorem representedPeerSubject_representable :
    RepresentableAuditSubject.Representable representedPeerSubject := by
  refine ⟨?_, ?_, ?_⟩
  · simp [representedPeerSubject, representedPeerSource]
  · rfl
  · intro node hnode
    simp [representedPeerSubject, representedPeerAuditSubject,
      representedPeerAuditGraphData] at hnode
    rcases hnode with rfl
    exact
      ⟨representedPeerAuditNodeId, "represented peer source",
        representedPeerAuditGates, AuditDecision.permit, rfl⟩

def representedPeer :
    { s : RepresentableAuditSubject //
      RepresentableAuditSubject.Representable s } :=
  ⟨representedPeerSubject, representedPeerSubject_representable⟩

theorem representedPeer_repr_eq :
    RepresentableAuditSubject.repr representedPeer =
      [weakestWithStrongerPeerNode] := by
  simp [RepresentableAuditSubject.repr, representedPeer,
    representedPeerSubject, representedPeerSource,
    RepresentableSource.toGovernanceGraph,
    weakestWithStrongerPeerRepresentableNode_toGovernanceNode]

theorem representedPeer_decision_equivalent :
    DecisionSystem.Equivalent
      (RepresentableAuditSubject.sourceSemantics representedPeer)
      (RepresentableAuditSubject.repr representedPeer) :=
  RepresentableAuditSubject.decision_equivalent representedPeer

theorem weakestWithStrongerPeer_reachable_stage :
    ReachablePeerRelativeDecisiveStage
      (P := GovernanceGraph)
      [weakestWithStrongerPeerNode] ([] : GovernanceGraph)
      weakestWithStrongerPeerNode ([] : GovernanceGraph) := by
  refine ⟨?_, weakestWithStrongerPeerNode_structural, ?_, rfl⟩
  · exact ⟨by intro node hmem claims claimant; cases hmem⟩
  · exact ⟨by intro claims claimant _hpermit; rfl⟩

theorem representedPeer_reachable_stage :
    ReachablePeerRelativeDecisiveStage
      (P := GovernanceGraph)
      (RepresentableAuditSubject.repr representedPeer) []
      weakestWithStrongerPeerNode [] := by
  simpa [representedPeer_repr_eq] using
    weakestWithStrongerPeer_reachable_stage

theorem representedPeer_obstructs_diagnostics :
    ¬ (GraphConsistencyP (RepresentableAuditSubject.repr representedPeer) ∧
        GraphSolidarityP (RepresentableAuditSubject.repr representedPeer) ∧
          GraphMonotonicityP
            (RepresentableAuditSubject.repr representedPeer)) :=
  reachable_peer_relative_decisive_stage_obstructs_diagnostics
    (RepresentableAuditSubject.repr representedPeer) []
    weakestWithStrongerPeerNode [] representedPeer_reachable_stage

theorem representedPeer_not_graphConsistent :
    ¬ GraphConsistencyP (RepresentableAuditSubject.repr representedPeer) :=
  (reachable_peer_relative_decisive_stage_forces_consistency_and_monotonicity_sacrifice
    (RepresentableAuditSubject.repr representedPeer) []
    weakestWithStrongerPeerNode [] representedPeer_reachable_stage).1

end Legitimacy
