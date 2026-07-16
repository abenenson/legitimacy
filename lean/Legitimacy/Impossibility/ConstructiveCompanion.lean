/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Impossibility.PeerRelativeClass
import Legitimacy.Protocol.State

/-!
# Constructive companion for the peer-relative impossibility

The quantified peer-relative impossibility has a constructive counterpart:
once the head is fixed to `peerRelativeNode` and the tail is complete, the
external decision behavior is forced. The canonical construction is the
singleton `peerGraph`, and every complete peer-relative-head implementation is
behaviorally equal to it and to every other such implementation.

Without the completeness restriction, uniqueness is false. The correct
Arrow-style statement is a behavioral representative: every peer-relative-head
graph is decision-equivalent to the singleton node that first applies the
peer-relative gate and, only on claimants admitted by that gate, exposes the
residual decision surface of its tail on the forwarded profile.
-/

set_option autoImplicit false

namespace Legitimacy

/-- The empty tail is complete: a claimant permitted by the peer-relative head
is permitted by the downstream empty pipeline. This supplies the canonical
construction used by the uniqueness theorem. -/
lemma empty_completePeerRelativeTail :
    CompletePeerRelativeTail [] := by
  intro claims k _hpermit
  rfl

/-- The canonical peer graph is exactly a peer-relative head with empty tail. -/
lemma peerGraph_peerRelativeHead :
    PeerRelativeHead peerGraph [] := by
  rfl

/-- Construction theorem: the canonical singleton peer graph is a complete
peer-relative-head mechanism. -/
theorem peerGraph_complete_peerRelative_construction :
    PeerRelativeHead peerGraph [] ∧ CompletePeerRelativeTail [] := by
  exact ⟨peerGraph_peerRelativeHead, empty_completePeerRelativeTail⟩

/-- Pairwise equivalence theorem: complete peer-relative-head mechanisms have a
forced external decision surface. The two head hypotheses expose the common
syntactic construction, and the two completeness hypotheses rule out downstream
narrowing on the forwarded profile. -/
theorem complete_peerRelativeHead_pairwise_equiv
    (G H tailG tailH : GovernanceGraph)
    (hheadG : PeerRelativeHead G tailG)
    (hcompleteG : CompletePeerRelativeTail tailG)
    (hheadH : PeerRelativeHead H tailH)
    (hcompleteH : CompletePeerRelativeTail tailH) :
    GovernanceGraphEquivalent G H := by
  intro claims k
  have hG := peerRelativeHead_complete_equiv_peerGraph
    G tailG hheadG hcompleteG claims k
  have hH := peerRelativeHead_complete_equiv_peerGraph
    H tailH hheadH hcompleteH claims k
  exact hG.trans hH.symm

/-- Decision-equivalence: every complete peer-relative-head mechanism is
externally decision-equivalent to the canonical singleton peerGraph, which
is a canonical behavioral representative under GovernanceGraphEquivalent. -/
theorem complete_peerRelativeHead_behaviorally_equiv_peerGraph
    (G tail : GovernanceGraph)
    (hhead : PeerRelativeHead G tail)
    (hcomplete : CompletePeerRelativeTail tail) :
    GovernanceGraphEquivalent G peerGraph :=
  peerRelativeHead_complete_equiv_peerGraph G tail hhead hcomplete

/-- Existence of a canonical behavioral representative: `peerGraph` is a
complete peer-relative-head pipeline, and every other such pipeline is
decision-equivalent to it. Uniqueness is up to GovernanceGraphEquivalent, not
syntactic equality. -/
theorem complete_peerRelativeHead_behavioral_representative_exists :
    ∃ G : GovernanceGraph,
      PeerRelativeHead G [] ∧
      CompletePeerRelativeTail [] ∧
      ∀ (H tailH : GovernanceGraph),
        PeerRelativeHead H tailH →
        CompletePeerRelativeTail tailH →
        GovernanceGraphEquivalent H G := by
  refine ⟨peerGraph, peerGraph_peerRelativeHead, empty_completePeerRelativeTail, ?_⟩
  intro H tailH hheadH hcompleteH
  exact complete_peerRelativeHead_behaviorally_equiv_peerGraph H tailH hheadH hcompleteH

/-- Behavioral equivalence of governance graphs as a setoid, used to turn
decision-equivalence uniqueness into type-level quotient uniqueness. -/
def governanceGraphEquivalentSetoid : Setoid GovernanceGraph where
  r := GovernanceGraphEquivalent
  iseqv := by
    constructor
    · intro G claims k
      rfl
    · intro G H heq claims k
      exact (heq claims k).symm
    · intro G H K hGH hHK claims k
      exact (hGH claims k).trans (hHK claims k)

/-- Quotient of governance graphs by external decision behavior. -/
abbrev GovernanceGraphClass : Type :=
  Quotient governanceGraphEquivalentSetoid

/-- The behavior class represented by a governance graph. -/
def governanceGraphClass (G : GovernanceGraph) : GovernanceGraphClass :=
  Quotient.mk governanceGraphEquivalentSetoid G

/-- Size-indexed behavioral equivalence for governance graphs. In addition to
external decision equivalence, it retains the canonical profile readout used by
the finite spectral carrier bridge. This is deliberately stronger than the
legacy behavioral quotient, whose classes cannot retain representative size. -/
def GovernanceGraphEquivalentAtSize (n : Nat)
    (G H : { graph : GovernanceGraph // graph.weightedSize = n }) : Prop :=
  GovernanceGraphEquivalent G.1 H.1 ∧
    ∀ i : Fin n,
      graphDecide G.1 G.1.profileClaims i.val =
        graphDecide H.1 H.1.profileClaims i.val

/-- Setoid for the size-indexed governance graph class. -/
def governanceGraphEquivalentAtSizeSetoid (n : Nat) :
    Setoid { graph : GovernanceGraph // graph.weightedSize = n } where
  r := GovernanceGraphEquivalentAtSize n
  iseqv := by
    constructor
    · intro G
      exact ⟨by intro claims k; rfl, by intro i; rfl⟩
    · intro G H heq
      exact ⟨by
        intro claims k
        exact (heq.1 claims k).symm, by
        intro i
        exact (heq.2 i).symm⟩
    · intro G H K hGH hHK
      exact ⟨by
        intro claims k
        exact (hGH.1 claims k).trans (hHK.1 claims k), by
        intro i
        exact (hGH.2 i).trans (hHK.2 i)⟩

/-- Governance graph classes at a fixed retained weighted size. -/
abbrev GovernanceGraphClassAtSize (n : Nat) : Type :=
  Quotient (governanceGraphEquivalentAtSizeSetoid n)

/-- A governance graph class carrying its retained weighted size. -/
abbrev SizedGovernanceGraphClass : Type :=
  Σ n : Nat, GovernanceGraphClassAtSize n

/-- The size-indexed class represented by a governance graph. -/
def governanceGraphClassAtSize (G : GovernanceGraph) :
    GovernanceGraphClassAtSize G.weightedSize :=
  Quotient.mk (governanceGraphEquivalentAtSizeSetoid G.weightedSize) ⟨G, rfl⟩

/-- The sigma-sized class represented by a governance graph. -/
def sizedGovernanceGraphClass (G : GovernanceGraph) :
    SizedGovernanceGraphClass :=
  ⟨G.weightedSize, governanceGraphClassAtSize G⟩

/-- Forget the retained-size quotient down to the legacy behavioral quotient. -/
noncomputable def GovernanceGraphClassAtSize.forget {n : Nat} :
    GovernanceGraphClassAtSize n → GovernanceGraphClass :=
  Quotient.lift
    (fun G : { graph : GovernanceGraph // graph.weightedSize = n } =>
      governanceGraphClass G.1)
    (by
      intro G H heq
      exact Quotient.sound heq.1)

/-- Forget a sigma-sized governance graph class down to the legacy behavioral
class. -/
noncomputable def SizedGovernanceGraphClass.forget :
    SizedGovernanceGraphClass → GovernanceGraphClass
  | ⟨_, C⟩ => GovernanceGraphClassAtSize.forget C

@[simp]
lemma GovernanceGraphClassAtSize.forget_mk (G : GovernanceGraph) :
    GovernanceGraphClassAtSize.forget (governanceGraphClassAtSize G) =
      governanceGraphClass G := by
  rfl

@[simp]
lemma SizedGovernanceGraphClass.forget_mk (G : GovernanceGraph) :
    SizedGovernanceGraphClass.forget (sizedGovernanceGraphClass G) =
      governanceGraphClass G := by
  rfl

/-- Morphisms for the sized behavioral lineage explicitly carry retained-size
equality. The existing `BehavioralLineage.Hom` transports behavioral violation
sets; this theorem-facing category records the extra proof needed to reindex
size-indexed classes. -/
structure SizedGovernanceGraphHom (source target : GovernanceGraph) where
  behavior : GovernanceGraphEquivalent source target
  size_eq : source.weightedSize = target.weightedSize

/-- Decision-layer consistency vulnerability is invariant under behavioral
equivalence. This is the quotient-compatible `cv` from
`Results.Impossibility`, not the spectral weighted-graph `GovGraph.cv`. -/
theorem governanceGraph_cv_well_defined_on_equivalence_classes
    {G H : GovernanceGraph}
    (heq : GovernanceGraphEquivalent G H) :
    cv G = cv H := by
  unfold cv
  have hcons := graphConsistency_congr heq
  by_cases hG : GraphConsistency G
  · have hH : GraphConsistency H := hcons.mp hG
    simp [hG, hH]
  · have hH : ¬ GraphConsistency H := by
      intro h
      exact hG (hcons.mpr h)
    simp [hG, hH]

/-- The decision-layer `cv` descends to the behavioral quotient. -/
noncomputable def governanceGraphCvClass : GovernanceGraphClass → ℝ :=
  Quotient.lift cv (by
    intro G H heq
    exact governanceGraph_cv_well_defined_on_equivalence_classes heq)

@[simp]
lemma governanceGraphCvClass_mk (G : GovernanceGraph) :
    governanceGraphCvClass (governanceGraphClass G) = cv G := by
  rfl

/-- Complete peer-relative-head mechanisms determine a unique behavioral
quotient class. This is a genuine Lean `ExistsUnique` statement over the
quotient type, not merely uniqueness modulo a relation in the conclusion. -/
theorem complete_peerRelativeHead_behavior_class_unique :
    ∃! C : GovernanceGraphClass,
      ∃ (G tailG : GovernanceGraph),
        governanceGraphClass G = C ∧
          PeerRelativeHead G tailG ∧
          CompletePeerRelativeTail tailG := by
  refine ⟨governanceGraphClass peerGraph, ?_, ?_⟩
  · exact ⟨peerGraph, [], rfl, peerGraph_peerRelativeHead,
      empty_completePeerRelativeTail⟩
  · intro C hC
    rcases hC with ⟨G, tailG, hclass, hhead, hcomplete⟩
    rw [← hclass]
    apply Quotient.sound
    intro claims k
    exact complete_peerRelativeHead_behaviorally_equiv_peerGraph
      G tailG hhead hcomplete claims k

/-! ### Unrestricted tails -/

/-- The observable decision surface of a peer-relative head with an arbitrary
tail. The head fixes all denials; when the head permits, the tail's decision on
the forwarded profile is the only remaining degree of freedom. -/
def peerRelativeTailSurface (tail : GovernanceGraph) : GovernanceNodeFn :=
  fun claims k =>
    match peerRelativeNode claims k with
    | BinaryDecision.Deny => BinaryDecision.Deny
    | BinaryDecision.Permit =>
      graphDecide tail (filterPermitted peerRelativeNode claims) k

/-- Singleton tail-surface representative for an arbitrary peer-relative-head
graph. -/
def peerRelativeHeadTailSurfaceRepresentative (tail : GovernanceGraph) :
    GovernanceGraph :=
  [peerRelativeTailSurface tail]

/-- The singleton tail-surface representative evaluates to its residual
surface. -/
lemma graphDecide_peerRelativeHeadTailSurfaceRepresentative
    (tail : GovernanceGraph) (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide (peerRelativeHeadTailSurfaceRepresentative tail) claims k =
      peerRelativeTailSurface tail claims k := by
  unfold peerRelativeHeadTailSurfaceRepresentative
  cases hsurface : peerRelativeTailSurface tail claims k <;> simp [graphDecide, hsurface]

/-- Behavioral representative for arbitrary peer-relative-head mechanisms. The
tail is not assumed complete; instead, its residual decision surface is retained
as the canonical invariant. -/
theorem peerRelativeHead_behaviorally_equiv_tailSurfaceRepresentative
    (G tail : GovernanceGraph)
    (hhead : PeerRelativeHead G tail) :
    GovernanceGraphEquivalent G (peerRelativeHeadTailSurfaceRepresentative tail) := by
  intro claims k
  rw [hhead]
  cases hpeer : peerRelativeNode claims k with
  | Permit =>
      rw [graphDecide_peerRelativeHeadTailSurfaceRepresentative]
      simp [peerRelativeTailSurface, graphDecide, hpeer]
  | Deny =>
      rw [graphDecide_peerRelativeHeadTailSurfaceRepresentative]
      simp [peerRelativeTailSurface, graphDecide, hpeer]

/-- Two arbitrary peer-relative-head mechanisms are equivalent exactly when
their residual tail surfaces agree on every original profile and claimant. -/
theorem peerRelativeHead_equiv_iff_tailSurface_eq
    (G H tailG tailH : GovernanceGraph)
    (hheadG : PeerRelativeHead G tailG)
    (hheadH : PeerRelativeHead H tailH) :
    GovernanceGraphEquivalent G H ↔
      ∀ (claims : List ClaimQ) (k : ClaimantId),
        peerRelativeTailSurface tailG claims k =
          peerRelativeTailSurface tailH claims k := by
  constructor
  · intro heq claims k
    have hG :=
      peerRelativeHead_behaviorally_equiv_tailSurfaceRepresentative G tailG hheadG claims k
    have hH :=
      peerRelativeHead_behaviorally_equiv_tailSurfaceRepresentative H tailH hheadH claims k
    simpa [graphDecide_peerRelativeHeadTailSurfaceRepresentative] using
      (hG.symm.trans (heq claims k)).trans hH
  · intro hsurface claims k
    have hG :=
      peerRelativeHead_behaviorally_equiv_tailSurfaceRepresentative G tailG hheadG claims k
    have hH :=
      peerRelativeHead_behaviorally_equiv_tailSurfaceRepresentative H tailH hheadH claims k
    exact (hG.trans
      ((by
        simp [graphDecide_peerRelativeHeadTailSurfaceRepresentative,
          hsurface claims k]) :
        graphDecide (peerRelativeHeadTailSurfaceRepresentative tailG) claims k =
          graphDecide (peerRelativeHeadTailSurfaceRepresentative tailH) claims k)).trans hH.symm

/-- Structural divergence criterion: arbitrary peer-relative-head mechanisms
diverge exactly when their residual tail surfaces disagree somewhere. -/
theorem peerRelativeHead_not_equiv_iff_tailSurface_ne
    (G H tailG tailH : GovernanceGraph)
    (hheadG : PeerRelativeHead G tailG)
    (hheadH : PeerRelativeHead H tailH) :
    ¬ GovernanceGraphEquivalent G H ↔
      ∃ (claims : List ClaimQ) (k : ClaimantId),
        peerRelativeTailSurface tailG claims k ≠
          peerRelativeTailSurface tailH claims k := by
  classical
  constructor
  · intro hne
    rw [peerRelativeHead_equiv_iff_tailSurface_eq G H tailG tailH hheadG hheadH] at hne
    by_contra hnone
    apply hne
    intro claims k
    by_contra hdiff
    exact hnone ⟨claims, k, hdiff⟩
  · intro hdiff heq
    rcases hdiff with ⟨claims, k, hdiff⟩
    have hsurface :=
      (peerRelativeHead_equiv_iff_tailSurface_eq G H tailG tailH hheadG hheadH).mp heq
    exact hdiff (hsurface claims k)

/-- The residual tail surface is peer-relative invariant on head-denied
claimants: all tails collapse to `Deny` whenever the peer-relative head denies. -/
theorem peerRelativeTailSurface_of_head_deny
    (tail : GovernanceGraph) (claims : List ClaimQ) (k : ClaimantId)
    (hdeny : peerRelativeNode claims k = BinaryDecision.Deny) :
    peerRelativeTailSurface tail claims k = BinaryDecision.Deny := by
  simp [peerRelativeTailSurface, hdeny]

/-- The earlier completeness condition is exactly the special case where the
arbitrary-tail residual surface is the original peer-relative surface. -/
theorem completePeerRelativeTail_iff_tailSurface_eq_peerRelativeNode
    (tail : GovernanceGraph) :
    CompletePeerRelativeTail tail ↔
      ∀ (claims : List ClaimQ) (k : ClaimantId),
        peerRelativeTailSurface tail claims k = peerRelativeNode claims k := by
  constructor
  · intro hcomplete claims k
    cases hpeer : peerRelativeNode claims k with
    | Permit =>
        simp [peerRelativeTailSurface, hpeer, hcomplete claims k hpeer]
    | Deny =>
        simp [peerRelativeTailSurface, hpeer]
  · intro hsurface claims k hpermit
    have h := hsurface claims k
    simpa [peerRelativeTailSurface, hpermit] using h

private def denyTailNode : GovernanceNodeFn := fun _ _ => BinaryDecision.Deny

private lemma peerThenDenyTail_peerRelativeHead :
    PeerRelativeHead [peerRelativeNode, denyTailNode] [denyTailNode] := by
  rfl

private lemma peerThenDenyTail_denies
    (claims : List ClaimQ) (k : ClaimantId) :
    graphDecide [peerRelativeNode, denyTailNode] claims k = BinaryDecision.Deny := by
  cases hpeer : peerRelativeNode claims k with
  | Permit =>
      simp [graphDecide, hpeer, denyTailNode]
  | Deny =>
      simp [graphDecide, hpeer]

private def singletonPeerClaim : ClaimQ :=
  ⟨0, 1, by norm_num, []⟩

private def singletonPeerClaims : List ClaimQ :=
  [singletonPeerClaim]

/-- A concrete singleton claimant is admitted by the peer-relative node. -/
private lemma peerRelativeNode_singleton_permits :
    peerRelativeNode singletonPeerClaims 0 = BinaryDecision.Permit := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

private lemma peerGraph_singleton_permits :
    graphDecide peerGraph singletonPeerClaims 0 = BinaryDecision.Permit := by
  rw [peerGraph, graphDecide, peerRelativeNode_singleton_permits]
  simp [graphDecide]

/-- The deny-all tail is not complete: it revokes a claimant that the
peer-relative head permitted. -/
theorem denyTail_not_completePeerRelativeTail :
    ¬ CompletePeerRelativeTail [denyTailNode] := by
  intro hcomplete
  have htail := hcomplete singletonPeerClaims 0 peerRelativeNode_singleton_permits
  have hdeny :
      graphDecide [denyTailNode]
          (filterPermitted peerRelativeNode singletonPeerClaims) 0 =
        BinaryDecision.Deny := by
    simp [denyTailNode, graphDecide]
  rw [hdeny] at htail
  exact BinaryDecision.noConfusion htail

/-- Unrestricted uniqueness is false: the canonical peer graph and the graph
with the same peer-relative head followed by a deny-all tail are both
peer-relative-head mechanisms, but they are not behaviorally equivalent. -/
theorem peerRelativeHead_unrestricted_uniqueness_refutation :
    ∃ (G H tailG tailH : GovernanceGraph),
      PeerRelativeHead G tailG ∧
      PeerRelativeHead H tailH ∧
      ¬ GovernanceGraphEquivalent G H := by
  refine ⟨peerGraph, [peerRelativeNode, denyTailNode], [],
    [denyTailNode], peerGraph_peerRelativeHead, peerThenDenyTail_peerRelativeHead, ?_⟩
  intro heq
  have hpermit : graphDecide peerGraph singletonPeerClaims 0 = BinaryDecision.Permit :=
    peerGraph_singleton_permits
  have hdeny :
      graphDecide [peerRelativeNode, denyTailNode] singletonPeerClaims 0 =
        BinaryDecision.Deny :=
    peerThenDenyTail_denies singletonPeerClaims 0
  rw [heq singletonPeerClaims 0] at hpermit
  rw [hdeny] at hpermit
  exact BinaryDecision.noConfusion hpermit

end Legitimacy
