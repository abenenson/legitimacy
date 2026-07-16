/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Graph
import Legitimacy.Results.Composition

/-!
# Decision-system interfaces

This module defines the decision-system abstraction, its binary sequential
pipeline refinement, and the concrete `GovernanceGraph` instances used by the
peer-relative theorem stack.
-/

set_option autoImplicit false

namespace Legitimacy

universe u u' u'' v w z

/-- A broad semantic interface for decision processes.

The class records only external decision behavior. It intentionally carries no
sequential, binary, or list-like structure. Extensional equivalence and
diagnostic congruence should be derived from `decide`, not bundled as class
fields. -/
class DecisionSystem
    (P : Type u) (Profile : outParam (Type v))
    (Subject : outParam (Type w)) (Outcome : outParam (Type z)) where
  /-- External decision made by a system on a profile and subject. -/
  decide : P → Profile → Subject → Outcome

namespace DecisionSystem

/-- Extensional equivalence of decision systems: same external decision on
every profile and subject. -/
def Equivalent
    {P : Type u} {Q : Type u'} {Profile : Type v} {Subject : Type w}
    {Outcome : Type z}
    [DecisionSystem P Profile Subject Outcome]
    [DecisionSystem Q Profile Subject Outcome]
    (x : P) (y : Q) : Prop :=
  ∀ (profile : Profile) (subject : Subject),
    DecisionSystem.decide x profile subject =
      DecisionSystem.decide y profile subject

/-- Decision-system equivalence is reflexive. -/
lemma Equivalent.refl
    {P : Type u} {Profile : Type v} {Subject : Type w} {Outcome : Type z}
    [DecisionSystem P Profile Subject Outcome] (x : P) :
    Equivalent x x := by
  intro profile subject
  rfl

/-- Decision-system equivalence is symmetric. -/
lemma Equivalent.symm
    {P : Type u} {Q : Type u'} {Profile : Type v} {Subject : Type w}
    {Outcome : Type z}
    [DecisionSystem P Profile Subject Outcome]
    [DecisionSystem Q Profile Subject Outcome]
    {x : P} {y : Q} (heq : Equivalent x y) :
    Equivalent y x := by
  intro profile subject
  exact (heq profile subject).symm

/-- Decision-system equivalence is transitive. -/
lemma Equivalent.trans
    {P : Type u} {Q : Type u'} {R : Type u''}
    {Profile : Type v} {Subject : Type w} {Outcome : Type z}
    [DecisionSystem P Profile Subject Outcome]
    [DecisionSystem Q Profile Subject Outcome]
    [DecisionSystem R Profile Subject Outcome]
    {x : P} {y : Q} {z : R}
    (hxy : Equivalent x y) (hyz : Equivalent y z) :
    Equivalent x z := by
  intro profile subject
  exact (hxy profile subject).trans (hyz profile subject)

end DecisionSystem

/-- Governance graphs are decision systems under their existing external
binary decision semantics. -/
instance : DecisionSystem GovernanceGraph (List ClaimQ) ClaimantId BinaryDecision where
  decide := graphDecide

private lemma governanceGraph_filterPermitted_transparent
    {node : GovernanceNodeFn}
    (hnode : ∀ (claims : List ClaimQ) (k : ClaimantId),
      node claims k = BinaryDecision.Permit)
    (claims : List ClaimQ) :
    filterPermitted node claims = claims := by
  unfold filterPermitted
  apply List.filter_eq_self.mpr
  intro c _
  simp [hnode claims c.id]

private lemma governanceGraph_transparentPrefix_append
    (pref rest : GovernanceGraph)
    (hpref : ∀ node, List.Mem node pref →
      ∀ (claims : List ClaimQ) (k : ClaimantId),
        node claims k = BinaryDecision.Permit)
    (claims : List ClaimQ)
    (k : ClaimantId) :
    graphDecide (List.append pref rest) claims k = graphDecide rest claims k := by
  induction pref generalizing claims with
  | nil =>
      simp
  | cons node pref ih =>
      have hnode :
          ∀ (claims : List ClaimQ) (k : ClaimantId),
            node claims k = BinaryDecision.Permit :=
        hpref node List.mem_cons_self
      have htail :
          ∀ n, List.Mem n pref →
            ∀ (claims : List ClaimQ) (k : ClaimantId),
              n claims k = BinaryDecision.Permit := by
        intro n hn
        exact hpref n (List.mem_cons_of_mem node hn)
      calc
        graphDecide ((node :: pref).append rest) claims k =
            graphDecide (pref.append rest) (filterPermitted node claims) k := by
          simp [graphDecide, hnode claims k]
        _ = graphDecide (pref.append rest) claims k := by
          rw [governanceGraph_filterPermitted_transparent hnode claims]
        _ = graphDecide rest claims k :=
          ih htail claims

/-- A branching binary decision pipeline.

Internal nodes host ordinary governance node functions. A permitting decision
continues through the permit branch on the forwarded profile; a denying
decision continues through the deny branch on the original profile. Leaves are
terminal decisions. -/
inductive BinaryDecisionTree where
  | leaf_permit : BinaryDecisionTree
  | leaf_deny : BinaryDecisionTree
  | node :
      GovernanceNodeFn →
      (permit_branch : BinaryDecisionTree) →
      (deny_branch : BinaryDecisionTree) →
      BinaryDecisionTree

namespace BinaryDecisionTree

/-- Evaluate a binary decision tree on a claim profile and claimant. -/
def decide : BinaryDecisionTree → List ClaimQ → ClaimantId → BinaryDecision
  | leaf_permit, _, _ => BinaryDecision.Permit
  | leaf_deny, _, _ => BinaryDecision.Deny
  | node gate permitBranch denyBranch, claims, k =>
      match gate claims k with
      | BinaryDecision.Permit =>
          decide permitBranch (filterPermitted gate claims) k
      | BinaryDecision.Deny =>
          decide denyBranch claims k

end BinaryDecisionTree

/-- Binary decision trees are decision systems under their recursive external
decision semantics. -/
instance : DecisionSystem BinaryDecisionTree (List ClaimQ) ClaimantId BinaryDecision where
  decide := BinaryDecisionTree.decide

namespace BinaryDecisionTree

/-- Head-gate composition: Permit continues into the tail, Deny terminates. -/
def cons (gate : GovernanceNodeFn) (tail : BinaryDecisionTree) :
    BinaryDecisionTree :=
  node gate tail leaf_deny

/-- Sequential tree composition by grafting the right pipeline at every
terminal Permit leaf of the left pipeline. -/
def append : BinaryDecisionTree → BinaryDecisionTree → BinaryDecisionTree
  | leaf_permit, tail => tail
  | leaf_deny, _tail => leaf_deny
  | node gate permitBranch denyBranch, tail =>
      node gate (append permitBranch tail) (append denyBranch tail)

/-- A tree node is transparent when it permits every claimant on every profile. -/
def transparentNode (gate : GovernanceNodeFn) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId),
    gate claims k = BinaryDecision.Permit

/-- Structural transparency for tree prefixes. The predicate is intentionally
strong enough to make appending after a transparent prefix decision-neutral for
all possible continuations. -/
def transparentPrefix : BinaryDecisionTree → Prop
  | leaf_permit => True
  | leaf_deny => False
  | node gate permitBranch denyBranch =>
      transparentNode gate ∧ transparentPrefix permitBranch ∧
        transparentPrefix denyBranch

private lemma transparentNode_filterPermitted
    {gate : GovernanceNodeFn} (hgate : transparentNode gate)
    (claims : List ClaimQ) :
    filterPermitted gate claims = claims :=
  governanceGraph_filterPermitted_transparent hgate claims

lemma transparentPrefix_decide_append
    (pref rest : BinaryDecisionTree)
    (claims : List ClaimQ) (k : ClaimantId)
    (hpref : transparentPrefix pref) :
    decide (append pref rest) claims k = decide rest claims k := by
  induction pref generalizing claims with
  | leaf_permit =>
      rfl
  | leaf_deny =>
      cases hpref
  | node gate permitBranch denyBranch ihPermit _ihDeny =>
      rcases hpref with ⟨hgate, hpermit, _hdeny⟩
      calc
        decide (append (node gate permitBranch denyBranch) rest) claims k =
            decide (append permitBranch rest) (filterPermitted gate claims) k := by
          simp [append, decide, hgate claims k]
        _ = decide (append permitBranch rest) claims k := by
          rw [transparentNode_filterPermitted hgate claims]
        _ = decide rest claims k :=
          ihPermit claims hpermit

lemma equivalent_cons
    (gate : GovernanceNodeFn) {tail₁ tail₂ : BinaryDecisionTree}
    (heq : DecisionSystem.Equivalent tail₁ tail₂) :
    DecisionSystem.Equivalent (cons gate tail₁) (cons gate tail₂) := by
  intro claims k
  cases hgate : gate claims k with
  | Permit =>
      have h := heq (filterPermitted gate claims) k
      simpa [DecisionSystem.decide, cons, decide, hgate] using h
  | Deny =>
      simp [DecisionSystem.decide, cons, decide, hgate]

lemma equivalent_append_right
    (pref : BinaryDecisionTree) {tail₁ tail₂ : BinaryDecisionTree}
    (heq : DecisionSystem.Equivalent tail₁ tail₂) :
    DecisionSystem.Equivalent (append pref tail₁) (append pref tail₂) := by
  intro claims k
  induction pref generalizing claims with
  | leaf_permit =>
      exact heq claims k
  | leaf_deny =>
      rfl
  | node gate permitBranch denyBranch ihPermit ihDeny =>
      cases hgate : gate claims k with
      | Permit =>
          have h := ihPermit (filterPermitted gate claims)
          simpa [DecisionSystem.decide, append, decide, hgate] using h
      | Deny =>
          have h := ihDeny claims
          simpa [DecisionSystem.decide, append, decide, hgate] using h

end BinaryDecisionTree

/-- Sequential decision pipelines over first-party claim profiles.

The refinement supplies node-level evaluation, forwarding, empty/cons/append
structure, and the laws needed to normalize transparent prefixes. The
`GovernanceGraph` instance below discharges these laws for the existing graph
semantics.

**Honest scope note**: this class is *field-identical* to
`BinaryDecisionPipeline` at the time of introduction. The two classes are
inter-derivable (forward direction is the named instance
`binaryDecisionPipeline_to_decisionPipeline`; reverse direction is trivially
constructible by 1:1 field forwarding). The lift exists to reserve a
polymorphism slot for future genuine multi-decision pipelines (e.g. when the
codomain becomes `Decision3` or richer); it does not add current generality
over `BinaryDecisionPipeline` and does not weaken any existing theorem. The
obstruction theorems are routed through this class for forward-compat naming. -/
class DecisionPipeline (P : Type u) extends
    DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision where
  /-- One stage of the pipeline. -/
  Node : Type
  /-- Stage-level binary decision. -/
  evalNode : Node → List ClaimQ → ClaimantId → BinaryDecision
  /-- Profile forwarded downstream after a permitting stage. -/
  forward : Node → List ClaimQ → List ClaimQ
  /-- Empty pipeline. -/
  empty : P
  /-- Head-stage composition. -/
  cons : Node → P → P
  /-- Sequential composition of two pipelines. -/
  append : P → P → P
  /-- Empty pipelines permit every claimant. -/
  decide_empty :
    ∀ (claims : List ClaimQ) (k : ClaimantId),
      decide empty claims k = BinaryDecision.Permit
  /-- A denying head stage short-circuits the pipeline. -/
  decide_cons_deny :
    ∀ (node : Node) (tail : P) (claims : List ClaimQ) (k : ClaimantId),
      evalNode node claims k = BinaryDecision.Deny →
        decide (cons node tail) claims k = BinaryDecision.Deny
  /-- A permitting head stage forwards the profile to the tail. -/
  decide_cons_permit :
    ∀ (node : Node) (tail : P) (claims : List ClaimQ) (k : ClaimantId),
      evalNode node claims k = BinaryDecision.Permit →
        decide (cons node tail) claims k = decide tail (forward node claims) k
  /-- Semantic transparency for a node. -/
  transparentNode : Node → Prop
  /-- Semantic transparency for a prefix pipeline. -/
  transparentPrefix : P → Prop
  /-- Transparent prefixes do not affect external decisions. -/
  transparentPrefix_decide_append :
    ∀ (pref rest : P) (claims : List ClaimQ) (k : ClaimantId),
      transparentPrefix pref →
        decide (append pref rest) claims k = decide rest claims k
  /-- Equivalent tails remain equivalent after adding a common head stage. -/
  equivalent_cons :
    ∀ (node : Node) {tail₁ tail₂ : P},
      DecisionSystem.Equivalent tail₁ tail₂ →
        DecisionSystem.Equivalent (cons node tail₁) (cons node tail₂)
  /-- Equivalent tails remain equivalent after appending them after a common
  prefix pipeline. -/
  equivalent_append_right :
    ∀ (pref : P) {tail₁ tail₂ : P},
      DecisionSystem.Equivalent tail₁ tail₂ →
        DecisionSystem.Equivalent (append pref tail₁) (append pref tail₂)

/-- Backward-compatible marker for the canonical binary-decision pipeline
instance family. All operational structure now lives in `DecisionPipeline`; this
class records that the instance is one of the binary pipeline models used by
the existing theorem stack. -/
class BinaryDecisionPipeline (P : Type u) extends
    DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision where
  /-- One stage of the binary pipeline. -/
  Node : Type
  /-- Stage-level binary decision. -/
  evalNode : Node → List ClaimQ → ClaimantId → BinaryDecision
  /-- Profile forwarded downstream after a permitting stage. -/
  forward : Node → List ClaimQ → List ClaimQ
  /-- Empty pipeline. -/
  empty : P
  /-- Head-stage composition. -/
  cons : Node → P → P
  /-- Sequential composition of two pipelines. -/
  append : P → P → P
  /-- Empty pipelines permit every claimant. -/
  decide_empty :
    ∀ (claims : List ClaimQ) (k : ClaimantId),
      decide empty claims k = BinaryDecision.Permit
  /-- A denying head stage short-circuits the pipeline. -/
  decide_cons_deny :
    ∀ (node : Node) (tail : P) (claims : List ClaimQ) (k : ClaimantId),
      evalNode node claims k = BinaryDecision.Deny →
        decide (cons node tail) claims k = BinaryDecision.Deny
  /-- A permitting head stage forwards the profile to the tail. -/
  decide_cons_permit :
    ∀ (node : Node) (tail : P) (claims : List ClaimQ) (k : ClaimantId),
      evalNode node claims k = BinaryDecision.Permit →
        decide (cons node tail) claims k = decide tail (forward node claims) k
  /-- Semantic transparency for a node. -/
  transparentNode : Node → Prop
  /-- Semantic transparency for a prefix pipeline. -/
  transparentPrefix : P → Prop
  /-- Transparent prefixes do not affect external decisions. -/
  transparentPrefix_decide_append :
    ∀ (pref rest : P) (claims : List ClaimQ) (k : ClaimantId),
      transparentPrefix pref →
        decide (append pref rest) claims k = decide rest claims k
  /-- Equivalent tails remain equivalent after adding a common head stage. -/
  equivalent_cons :
    ∀ (node : Node) {tail₁ tail₂ : P},
      DecisionSystem.Equivalent tail₁ tail₂ →
        DecisionSystem.Equivalent (cons node tail₁) (cons node tail₂)
  /-- Equivalent tails remain equivalent after appending them after a common
  prefix pipeline. -/
  equivalent_append_right :
    ∀ (pref : P) {tail₁ tail₂ : P},
      DecisionSystem.Equivalent tail₁ tail₂ →
        DecisionSystem.Equivalent (append pref tail₁) (append pref tail₂)

instance (priority := 100) binaryDecisionPipeline_to_decisionPipeline
    {P : Type u} [BinaryDecisionPipeline P] : DecisionPipeline P where
  toDecisionSystem := inferInstance
  Node := BinaryDecisionPipeline.Node (P := P)
  evalNode := BinaryDecisionPipeline.evalNode (P := P)
  forward := BinaryDecisionPipeline.forward (P := P)
  empty := BinaryDecisionPipeline.empty (P := P)
  cons := BinaryDecisionPipeline.cons (P := P)
  append := BinaryDecisionPipeline.append (P := P)
  decide_empty := BinaryDecisionPipeline.decide_empty (P := P)
  decide_cons_deny := BinaryDecisionPipeline.decide_cons_deny (P := P)
  decide_cons_permit := BinaryDecisionPipeline.decide_cons_permit (P := P)
  transparentNode := BinaryDecisionPipeline.transparentNode (P := P)
  transparentPrefix := BinaryDecisionPipeline.transparentPrefix (P := P)
  transparentPrefix_decide_append :=
    BinaryDecisionPipeline.transparentPrefix_decide_append (P := P)
  equivalent_cons := BinaryDecisionPipeline.equivalent_cons (P := P)
  equivalent_append_right :=
    BinaryDecisionPipeline.equivalent_append_right (P := P)

instance : BinaryDecisionPipeline GovernanceGraph where
  toDecisionSystem := inferInstance
  Node := GovernanceNodeFn
  evalNode := fun node claims k => node claims k
  forward := filterPermitted
  empty := []
  cons := List.cons
  append := List.append
  decide_empty := by
    intro claims k
    rfl
  decide_cons_deny := by
    intro node tail claims k hdeny
    simp [DecisionSystem.decide, graphDecide, hdeny]
  decide_cons_permit := by
    intro node tail claims k hpermit
    simp [DecisionSystem.decide, graphDecide, hpermit]
  transparentNode := fun node =>
    ∀ (claims : List ClaimQ) (k : ClaimantId),
      node claims k = BinaryDecision.Permit
  transparentPrefix := fun pref =>
    ∀ node, List.Mem node pref →
      ∀ (claims : List ClaimQ) (k : ClaimantId),
        node claims k = BinaryDecision.Permit
  transparentPrefix_decide_append := by
    intro pref rest claims k hpref
    exact governanceGraph_transparentPrefix_append pref rest hpref claims k
  equivalent_cons := by
    intro node tail₁ tail₂ heq claims k
    cases hnode : node claims k
    · have h := heq (filterPermitted node claims) k
      change graphDecide tail₁ (filterPermitted node claims) k =
        graphDecide tail₂ (filterPermitted node claims) k at h
      simpa [DecisionSystem.decide, graphDecide, hnode] using h
    · simp [DecisionSystem.decide, graphDecide, hnode]
  equivalent_append_right := by
    intro pref tail₁ tail₂ heq claims k
    induction pref generalizing claims with
    | nil =>
        exact heq claims k
    | cons node pref ih =>
        cases hnode : node claims k
        · have h := ih (filterPermitted node claims)
          change graphDecide (List.append pref tail₁) (filterPermitted node claims) k =
            graphDecide (List.append pref tail₂) (filterPermitted node claims) k at h
          simpa [DecisionSystem.decide, graphDecide, hnode] using h
        · simp [DecisionSystem.decide, graphDecide, hnode]

instance : BinaryDecisionPipeline BinaryDecisionTree where
  toDecisionSystem := inferInstance
  Node := GovernanceNodeFn
  evalNode := fun gate claims k => gate claims k
  forward := filterPermitted
  empty := BinaryDecisionTree.leaf_permit
  cons := BinaryDecisionTree.cons
  append := BinaryDecisionTree.append
  decide_empty := by
    intro claims k
    rfl
  decide_cons_deny := by
    intro gate tail claims k hdeny
    simp [DecisionSystem.decide, BinaryDecisionTree.cons,
      BinaryDecisionTree.decide, hdeny]
  decide_cons_permit := by
    intro gate tail claims k hpermit
    simp [DecisionSystem.decide, BinaryDecisionTree.cons,
      BinaryDecisionTree.decide, hpermit]
  transparentNode := BinaryDecisionTree.transparentNode
  transparentPrefix := BinaryDecisionTree.transparentPrefix
  transparentPrefix_decide_append := by
    intro pref rest claims k hpref
    exact BinaryDecisionTree.transparentPrefix_decide_append pref rest claims k hpref
  equivalent_cons := by
    intro gate tail₁ tail₂ heq
    exact BinaryDecisionTree.equivalent_cons gate heq
  equivalent_append_right := by
    intro pref tail₁ tail₂ heq
    exact BinaryDecisionTree.equivalent_append_right pref heq

namespace DecisionPipeline

variable {P : Type u} [DecisionPipeline P]

/-- The node type associated to a decision pipeline. -/
abbrev NodeOf (P : Type u) [DecisionPipeline P] : Type :=
  DecisionPipeline.Node (P := P)

/-- Abstract first-effective surface for an arbitrary node: the system is a
transparent prefix followed by the node and its tail. -/
def EffectiveSurfaceForNode
    (node : NodeOf P) (G pref tail : P) : Prop :=
  G = append pref (cons node tail) ∧ transparentPrefix pref

/-- Abstract complete-tail predicate: downstream stages preserve every permit
emitted by the exposed head node on the forwarded profile. -/
def CompleteTailForNode (node : NodeOf P) (tail : P) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId),
    evalNode node claims k = BinaryDecision.Permit →
      DecisionSystem.decide tail (forward node claims) k = BinaryDecision.Permit

/-- The canonical singleton pipeline for a node. -/
def canonicalPipelineFor (node : NodeOf P) : P :=
  cons node empty

/-- The canonical singleton pipeline exposes exactly its head-node decision. -/
lemma decide_canonicalPipelineFor
    (node : NodeOf P) (claims : List ClaimQ) (k : ClaimantId) :
    DecisionSystem.decide (canonicalPipelineFor node) claims k =
      evalNode node claims k := by
  change DecisionSystem.decide (cons node (empty : P)) claims k =
    evalNode node claims k
  cases hnode : evalNode node claims k with
  | Permit =>
      rw [DecisionPipeline.decide_cons_permit
        (P := P) node (empty : P) claims k hnode]
      rw [DecisionPipeline.decide_empty]
  | Deny =>
      rw [DecisionPipeline.decide_cons_deny
        (P := P) node (empty : P) claims k hnode]

/-- Equivalent tails remain equivalent after a common head node. -/
lemma equivalent_cons_of_equivalent (node : NodeOf P) {tail₁ tail₂ : P}
    (heq : DecisionSystem.Equivalent tail₁ tail₂) :
    DecisionSystem.Equivalent (cons node tail₁) (cons node tail₂) :=
  DecisionPipeline.equivalent_cons node heq

/-- Equivalent tails remain equivalent after a common appended prefix. -/
lemma equivalent_append_right_of_equivalent (pref : P) {tail₁ tail₂ : P}
    (heq : DecisionSystem.Equivalent tail₁ tail₂) :
    DecisionSystem.Equivalent (append pref tail₁) (append pref tail₂) :=
  DecisionPipeline.equivalent_append_right pref heq

/-- Transparent prefixes erase by decision equivalence. -/
lemma transparentPrefix_append_equivalent
    {pref rest : P} (hpref : transparentPrefix pref) :
    DecisionSystem.Equivalent (append pref rest) rest := by
  intro claims k
  exact transparentPrefix_decide_append pref rest claims k hpref

/-- A first-effective node surface is decision-equivalent to the exposed
head-and-tail pipeline. -/
lemma effectiveSurfaceForNode_equivalent_head
    {node : NodeOf P} {G pref tail : P}
    (heffective : EffectiveSurfaceForNode node G pref tail) :
    DecisionSystem.Equivalent G (cons node tail) := by
  rcases heffective with ⟨hshape, hpref⟩
  rw [hshape]
  exact transparentPrefix_append_equivalent hpref

/-- A complete exposed head-and-tail pipeline is equivalent to the canonical
singleton pipeline for the exposed node. -/
lemma completeTail_equivalent_canonical
    {node : NodeOf P} {tail : P}
    (hcomplete : CompleteTailForNode node tail) :
    DecisionSystem.Equivalent (cons node tail) (canonicalPipelineFor node) := by
  intro claims k
  cases hnode : evalNode node claims k
  · calc
      DecisionSystem.decide (cons node tail) claims k =
          DecisionSystem.decide tail (forward node claims) k :=
        decide_cons_permit node tail claims k hnode
      _ = BinaryDecision.Permit :=
        hcomplete claims k hnode
      _ = DecisionSystem.decide (canonicalPipelineFor node) claims k := by
        exact ((decide_canonicalPipelineFor node claims k).trans hnode).symm
  · calc
      DecisionSystem.decide (cons node tail) claims k = BinaryDecision.Deny :=
        decide_cons_deny node tail claims k hnode
      _ = DecisionSystem.decide (canonicalPipelineFor node) claims k := by
        exact ((decide_canonicalPipelineFor node claims k).trans hnode).symm

/-- A complete first-effective node surface is decision-equivalent to the
canonical singleton pipeline for that node. -/
lemma effectiveSurfaceForNode_completeTail_decision_equivalent_to_canonical
    (G pref tail : P) (node : NodeOf P)
    (heffective : EffectiveSurfaceForNode node G pref tail)
    (hcomplete : CompleteTailForNode node tail) :
    DecisionSystem.Equivalent G (canonicalPipelineFor node) :=
  DecisionSystem.Equivalent.trans
    (effectiveSurfaceForNode_equivalent_head heffective)
    (completeTail_equivalent_canonical hcomplete)

/-- Complete-tail predicates transfer across decision equivalence of tails. -/
lemma completeTailForNode_congr
    {node : NodeOf P} {tail₁ tail₂ : P}
    (heq : DecisionSystem.Equivalent tail₁ tail₂) :
    CompleteTailForNode node tail₁ ↔ CompleteTailForNode node tail₂ := by
  constructor <;> intro hcomplete claims k hpermit
  · exact (heq (forward node claims) k).symm.trans
      (hcomplete claims k hpermit)
  · exact (heq (forward node claims) k).trans
      (hcomplete claims k hpermit)

/-- Concrete removal/consistency-violation witness for an exposed binary
decision-pipeline node. The fields are the witness data consumed by the
route-specific graph-consistency obstruction; the class intentionally carries
no peer-relative or monotonicity assumptions. -/
class HasConsistencyViolationWitness (node : NodeOf P) where
  /-- Claim profile on which one claimant is denied while another survives. -/
  claims : List ClaimQ
  /-- Claimant denied on the witness profile. -/
  denied : ClaimantId
  /-- Surviving claimant flipped by removing the denied claimant. -/
  survivor : ClaimantId
  /-- The denied and surviving claimants are distinct. -/
  distinct_claimants : denied ≠ survivor
  /-- The denied claimant appears in the witness profile. -/
  denied_in_claims : InClaims denied claims
  /-- The surviving claimant appears in the witness profile. -/
  survivor_in_claims : InClaims survivor claims
  /-- Witness profiles use distinct claimant identifiers. -/
  claims_distinct : ClaimsDistinct claims
  /-- The exposed node denies the denied claimant on the witness profile. -/
  denied_decision :
    evalNode node claims denied = BinaryDecision.Deny
  /-- The exposed node permits the survivor before removal. -/
  survivor_permitted :
    evalNode node claims survivor = BinaryDecision.Permit
  /-- Removing the denied claimant makes the survivor denied. -/
  survivor_denied_after_removal :
    evalNode node (removeClaimGraph denied claims) survivor =
      BinaryDecision.Deny

/-- Existential view of a concrete consistency-violation witness, useful when
interoperating with older Prop-shaped predicates. -/
lemma HasConsistencyViolationWitness.exists_witness {node : NodeOf P}
    (h : HasConsistencyViolationWitness node) :
    ∃ (claims : List ClaimQ) (k j : ClaimantId),
      k ≠ j ∧
      InClaims k claims ∧ InClaims j claims ∧
      ClaimsDistinct claims ∧
      evalNode node claims k = BinaryDecision.Deny ∧
      evalNode node claims j = BinaryDecision.Permit ∧
      evalNode node (removeClaimGraph k claims) j = BinaryDecision.Deny :=
  ⟨h.claims, h.denied, h.survivor, h.distinct_claimants,
    h.denied_in_claims, h.survivor_in_claims, h.claims_distinct,
    h.denied_decision, h.survivor_permitted,
    h.survivor_denied_after_removal⟩

/-- Concrete competitive-displacement/monotonicity witness for an exposed
binary decision-pipeline node. The fields are the witness data consumed by the
route-specific graph-monotonicity obstruction. -/
class HasMonotonicityViolationWitness (node : NodeOf P) where
  /-- Original witness profile. -/
  claims : List ClaimQ
  /-- Claimant whose claim is strengthened. -/
  strengthened : ClaimantId
  /-- Different claimant whose decision flips. -/
  affected : ClaimantId
  /-- New strength for the strengthened claimant. -/
  strengthened_strength : ℚ
  /-- Positivity proof for the new strength. -/
  strengthened_strength_pos : 0 < strengthened_strength
  /-- The strengthened and affected claimants are distinct. -/
  distinct_claimants : strengthened ≠ affected
  /-- The strengthened claimant appears in the original profile. -/
  strengthened_in_claims : InClaims strengthened claims
  /-- The affected claimant appears in the original profile. -/
  affected_in_claims : InClaims affected claims
  /-- The affected claimant remains after strengthening. -/
  affected_in_strengthened :
    InClaims affected
      (strengthenClaim strengthened strengthened_strength
        strengthened_strength_pos claims)
  /-- Original witness profile has distinct claimant identifiers. -/
  claims_distinct : ClaimsDistinct claims
  /-- Strengthened witness profile has distinct claimant identifiers. -/
  strengthened_claims_distinct :
    ClaimsDistinct
      (strengthenClaim strengthened strengthened_strength
        strengthened_strength_pos claims)
  /-- The strengthened value is at least the prior strength. -/
  strengthened_bound :
    ∀ c ∈ claims, c.id = strengthened → c.strength ≤ strengthened_strength
  /-- The affected claimant's own strength is unchanged. -/
  affected_strength_preserved :
    lookupStrength affected claims =
      lookupStrength affected
        (strengthenClaim strengthened strengthened_strength
          strengthened_strength_pos claims)
  /-- The exposed node permits the affected claimant before strengthening. -/
  affected_permitted :
    evalNode node claims affected = BinaryDecision.Permit
  /-- The exposed node denies the affected claimant after strengthening. -/
  affected_denied_after_strengthening :
    evalNode node
        (strengthenClaim strengthened strengthened_strength
          strengthened_strength_pos claims) affected =
      BinaryDecision.Deny

/-- Existential view of a concrete monotonicity-violation witness, matching the
older theorem interface. -/
lemma HasMonotonicityViolationWitness.exists_witness {node : NodeOf P}
    (h : HasMonotonicityViolationWitness node) :
    ∃ (claims : List ClaimQ) (k j : ClaimantId) (s' : ℚ) (hs' : 0 < s'),
      k ≠ j ∧
      InClaims k claims ∧
      InClaims j claims ∧
      InClaims j (strengthenClaim k s' hs' claims) ∧
      ClaimsDistinct claims ∧
      ClaimsDistinct (strengthenClaim k s' hs' claims) ∧
      (∀ c ∈ claims, c.id = k → c.strength ≤ s') ∧
      lookupStrength j claims =
        lookupStrength j (strengthenClaim k s' hs' claims) ∧
      evalNode node claims j = BinaryDecision.Permit ∧
      evalNode node (strengthenClaim k s' hs' claims) j =
        BinaryDecision.Deny :=
  ⟨h.claims, h.strengthened, h.affected, h.strengthened_strength,
    h.strengthened_strength_pos, h.distinct_claimants,
    h.strengthened_in_claims, h.affected_in_claims,
    h.affected_in_strengthened, h.claims_distinct,
    h.strengthened_claims_distinct, h.strengthened_bound,
    h.affected_strength_preserved, h.affected_permitted,
    h.affected_denied_after_strengthening⟩

/-- Node-level peer-relative aggregator witness stated against the abstract
node evaluator. This is still first-party claim semantics, so it belongs in the
binary-pipeline refinement rather than the broad `DecisionSystem` class. The
predicate records both the competitive-displacement witness used for
monotonicity and the removal witness used for consistency. -/
def IsPeerRelativeAggregator (node : NodeOf P) : Prop :=
  (∃ (claims : List ClaimQ) (k j : ClaimantId) (s' : ℚ) (hs' : 0 < s'),
      k ≠ j ∧
      InClaims k claims ∧
      InClaims j claims ∧
      InClaims j (strengthenClaim k s' hs' claims) ∧
      ClaimsDistinct claims ∧
      ClaimsDistinct (strengthenClaim k s' hs' claims) ∧
      (∀ c ∈ claims, c.id = k → c.strength ≤ s') ∧
      lookupStrength j claims =
        lookupStrength j (strengthenClaim k s' hs' claims) ∧
      evalNode node claims j = BinaryDecision.Permit ∧
      evalNode node (strengthenClaim k s' hs' claims) j =
        BinaryDecision.Deny) ∧
  (∃ (claims : List ClaimQ) (k j : ClaimantId),
      k ≠ j ∧
      InClaims k claims ∧ InClaims j claims ∧
      ClaimsDistinct claims ∧
      evalNode node claims k = BinaryDecision.Deny ∧
      evalNode node claims j = BinaryDecision.Permit ∧
      evalNode node (removeClaimGraph k claims) j = BinaryDecision.Deny)

/-- Projection for the competitive-displacement component of a peer-relative
aggregator witness. -/
lemma IsPeerRelativeAggregator.monotonicityWitness {node : NodeOf P}
    (h : IsPeerRelativeAggregator node) :
    ∃ (claims : List ClaimQ) (k j : ClaimantId) (s' : ℚ) (hs' : 0 < s'),
      k ≠ j ∧
      InClaims k claims ∧
      InClaims j claims ∧
      InClaims j (strengthenClaim k s' hs' claims) ∧
      ClaimsDistinct claims ∧
      ClaimsDistinct (strengthenClaim k s' hs' claims) ∧
      (∀ c ∈ claims, c.id = k → c.strength ≤ s') ∧
      lookupStrength j claims =
        lookupStrength j (strengthenClaim k s' hs' claims) ∧
      evalNode node claims j = BinaryDecision.Permit ∧
      evalNode node (strengthenClaim k s' hs' claims) j =
        BinaryDecision.Deny :=
  h.1

/-- Projection for the removal/consistency component of a peer-relative
aggregator witness. -/
lemma IsPeerRelativeAggregator.consistencyViolationWitness {node : NodeOf P}
    (h : IsPeerRelativeAggregator node) :
    ∃ (claims : List ClaimQ) (k j : ClaimantId),
      k ≠ j ∧
      InClaims k claims ∧ InClaims j claims ∧
      ClaimsDistinct claims ∧
      evalNode node claims k = BinaryDecision.Deny ∧
      evalNode node claims j = BinaryDecision.Permit ∧
      evalNode node (removeClaimGraph k claims) j = BinaryDecision.Deny :=
  h.2

/-- A peer-relative aggregator exposes the broader consistency-violation
witness route by projection from its removal component. -/
@[reducible]
noncomputable def HasConsistencyViolationWitness.ofPeerRelativeAggregator {node : NodeOf P}
    (h : IsPeerRelativeAggregator node) :
    HasConsistencyViolationWitness node :=
  Classical.choice <| by
    rcases IsPeerRelativeAggregator.consistencyViolationWitness h with
      ⟨claims, denied, survivor, hneq, hdeniedIn, hsurvivorIn, hdistinct,
        hdeny, hpermit, hremovedDeny⟩
    exact
      ⟨{ claims := claims
         denied := denied
         survivor := survivor
         distinct_claimants := hneq
         denied_in_claims := hdeniedIn
         survivor_in_claims := hsurvivorIn
         claims_distinct := hdistinct
         denied_decision := hdeny
         survivor_permitted := hpermit
         survivor_denied_after_removal := hremovedDeny }⟩

end DecisionPipeline

namespace BinaryDecisionPipeline

variable {P : Type u} [BinaryDecisionPipeline P]

/-- Backward-compatible alias for the node type associated to a binary decision
pipeline. -/
abbrev NodeOf (P : Type u) [BinaryDecisionPipeline P] : Type :=
  DecisionPipeline.NodeOf P

abbrev EffectiveSurfaceForNode
    (node : NodeOf P) (G pref tail : P) : Prop :=
  DecisionPipeline.EffectiveSurfaceForNode node G pref tail

abbrev CompleteTailForNode (node : NodeOf P) (tail : P) : Prop :=
  DecisionPipeline.CompleteTailForNode node tail

abbrev canonicalPipelineFor (node : NodeOf P) : P :=
  DecisionPipeline.canonicalPipelineFor node

lemma decide_canonicalPipelineFor
    (node : NodeOf P) (claims : List ClaimQ) (k : ClaimantId) :
    DecisionSystem.decide (canonicalPipelineFor node) claims k =
      BinaryDecisionPipeline.evalNode node claims k :=
  DecisionPipeline.decide_canonicalPipelineFor node claims k

lemma equivalent_cons_of_equivalent (node : NodeOf P) {tail₁ tail₂ : P}
    (heq : DecisionSystem.Equivalent tail₁ tail₂) :
    DecisionSystem.Equivalent
      (BinaryDecisionPipeline.cons node tail₁)
      (BinaryDecisionPipeline.cons node tail₂) :=
  DecisionPipeline.equivalent_cons_of_equivalent node heq

lemma equivalent_append_right_of_equivalent (pref : P) {tail₁ tail₂ : P}
    (heq : DecisionSystem.Equivalent tail₁ tail₂) :
    DecisionSystem.Equivalent
      (BinaryDecisionPipeline.append pref tail₁)
      (BinaryDecisionPipeline.append pref tail₂) :=
  DecisionPipeline.equivalent_append_right_of_equivalent pref heq

lemma transparentPrefix_append_equivalent
    {pref rest : P} (hpref : BinaryDecisionPipeline.transparentPrefix pref) :
    DecisionSystem.Equivalent (BinaryDecisionPipeline.append pref rest) rest :=
  DecisionPipeline.transparentPrefix_append_equivalent hpref

lemma effectiveSurfaceForNode_equivalent_head
    {node : NodeOf P} {G pref tail : P}
    (heffective : EffectiveSurfaceForNode node G pref tail) :
    DecisionSystem.Equivalent G
      (BinaryDecisionPipeline.cons node tail) :=
  DecisionPipeline.effectiveSurfaceForNode_equivalent_head heffective

lemma completeTail_equivalent_canonical
    {node : NodeOf P} {tail : P}
    (hcomplete : CompleteTailForNode node tail) :
    DecisionSystem.Equivalent
      (BinaryDecisionPipeline.cons node tail) (canonicalPipelineFor node) :=
  DecisionPipeline.completeTail_equivalent_canonical hcomplete

lemma effectiveSurfaceForNode_completeTail_decision_equivalent_to_canonical
    (G pref tail : P) (node : NodeOf P)
    (heffective : EffectiveSurfaceForNode node G pref tail)
    (hcomplete : CompleteTailForNode node tail) :
    DecisionSystem.Equivalent G (canonicalPipelineFor node) :=
  DecisionPipeline.effectiveSurfaceForNode_completeTail_decision_equivalent_to_canonical
    G pref tail node heffective hcomplete

lemma completeTailForNode_congr
    {node : NodeOf P} {tail₁ tail₂ : P}
    (heq : DecisionSystem.Equivalent tail₁ tail₂) :
    CompleteTailForNode node tail₁ ↔ CompleteTailForNode node tail₂ :=
  DecisionPipeline.completeTailForNode_congr heq

abbrev HasConsistencyViolationWitness (node : NodeOf P) : Type :=
  DecisionPipeline.HasConsistencyViolationWitness node

lemma HasConsistencyViolationWitness.exists_witness {node : NodeOf P}
    (h : HasConsistencyViolationWitness node) :
    ∃ (claims : List ClaimQ) (k j : ClaimantId),
      k ≠ j ∧
      InClaims k claims ∧ InClaims j claims ∧
      ClaimsDistinct claims ∧
      BinaryDecisionPipeline.evalNode node claims k = BinaryDecision.Deny ∧
      BinaryDecisionPipeline.evalNode node claims j = BinaryDecision.Permit ∧
      BinaryDecisionPipeline.evalNode node (removeClaimGraph k claims) j =
        BinaryDecision.Deny :=
  DecisionPipeline.HasConsistencyViolationWitness.exists_witness h

abbrev HasMonotonicityViolationWitness (node : NodeOf P) : Type :=
  DecisionPipeline.HasMonotonicityViolationWitness node

lemma HasMonotonicityViolationWitness.exists_witness {node : NodeOf P}
    (h : HasMonotonicityViolationWitness node) :
    ∃ (claims : List ClaimQ) (k j : ClaimantId) (s' : ℚ) (hs' : 0 < s'),
      k ≠ j ∧
      InClaims k claims ∧
      InClaims j claims ∧
      InClaims j (strengthenClaim k s' hs' claims) ∧
      ClaimsDistinct claims ∧
      ClaimsDistinct (strengthenClaim k s' hs' claims) ∧
      (∀ c ∈ claims, c.id = k → c.strength ≤ s') ∧
      lookupStrength j claims =
        lookupStrength j (strengthenClaim k s' hs' claims) ∧
      BinaryDecisionPipeline.evalNode node claims j = BinaryDecision.Permit ∧
      BinaryDecisionPipeline.evalNode node (strengthenClaim k s' hs' claims) j =
        BinaryDecision.Deny :=
  DecisionPipeline.HasMonotonicityViolationWitness.exists_witness h

abbrev IsPeerRelativeAggregator (node : NodeOf P) : Prop :=
  DecisionPipeline.IsPeerRelativeAggregator node

lemma IsPeerRelativeAggregator.monotonicityWitness {node : NodeOf P}
    (h : IsPeerRelativeAggregator node) :
    ∃ (claims : List ClaimQ) (k j : ClaimantId) (s' : ℚ) (hs' : 0 < s'),
      k ≠ j ∧
      InClaims k claims ∧
      InClaims j claims ∧
      InClaims j (strengthenClaim k s' hs' claims) ∧
      ClaimsDistinct claims ∧
      ClaimsDistinct (strengthenClaim k s' hs' claims) ∧
      (∀ c ∈ claims, c.id = k → c.strength ≤ s') ∧
      lookupStrength j claims =
        lookupStrength j (strengthenClaim k s' hs' claims) ∧
      BinaryDecisionPipeline.evalNode node claims j = BinaryDecision.Permit ∧
      BinaryDecisionPipeline.evalNode node (strengthenClaim k s' hs' claims) j =
        BinaryDecision.Deny :=
  DecisionPipeline.IsPeerRelativeAggregator.monotonicityWitness h

lemma IsPeerRelativeAggregator.consistencyViolationWitness {node : NodeOf P}
    (h : IsPeerRelativeAggregator node) :
    ∃ (claims : List ClaimQ) (k j : ClaimantId),
      k ≠ j ∧
      InClaims k claims ∧ InClaims j claims ∧
      ClaimsDistinct claims ∧
      BinaryDecisionPipeline.evalNode node claims k = BinaryDecision.Deny ∧
      BinaryDecisionPipeline.evalNode node claims j = BinaryDecision.Permit ∧
      BinaryDecisionPipeline.evalNode node (removeClaimGraph k claims) j =
        BinaryDecision.Deny :=
  DecisionPipeline.IsPeerRelativeAggregator.consistencyViolationWitness h

@[reducible]
noncomputable def HasConsistencyViolationWitness.ofPeerRelativeAggregator
    {node : NodeOf P} (h : IsPeerRelativeAggregator node) :
    HasConsistencyViolationWitness node :=
  DecisionPipeline.HasConsistencyViolationWitness.ofPeerRelativeAggregator h

end BinaryDecisionPipeline

end Legitimacy
