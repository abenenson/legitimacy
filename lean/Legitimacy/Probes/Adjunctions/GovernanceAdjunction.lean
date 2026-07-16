/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Whiskering
import Legitimacy.Foundations.Graph
import Mathlib.Tactic
/-!
# Universal governance adjunction probe

Coarse/fine claimant-resolution adjunctions, first at preorder count level and
then at governance-graph level with decision-preserving graph homomorphisms.
-/
set_option autoImplicit false
namespace Legitimacy
open CategoryTheory Functor
universe u₁ u₂ v₁ v₂
/-! ## A governance adjunction bundle -/
structure GovernanceAdjunction
    (C : Type u₁) (D : Type u₂)
    [Category.{v₁} C] [Category.{v₂} D] where
  left : C ⥤ D
  right : D ⥤ C
  unit : 𝟭 C ⟶ left ⋙ right
  counit : right ⋙ left ⟶ 𝟭 D
  left_triangle :
    Functor.whiskerRight unit left ≫ Functor.whiskerLeft left counit = 𝟙 left
  right_triangle :
    Functor.whiskerLeft right unit ≫ Functor.whiskerRight counit right = 𝟙 right
namespace GovernanceAdjunction
def toMathlibAdjunction
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    (adj : GovernanceAdjunction C D) : adj.left ⊣ adj.right where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    simpa using congr_app adj.left_triangle X
  right_triangle_components Y := by
    simpa using congr_app adj.right_triangle Y
def ofMathlibAdjunction
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) :
    GovernanceAdjunction C D where
  left := L
  right := R
  unit := adj.unit
  counit := adj.counit
  left_triangle := adj.left_triangle
  right_triangle := adj.right_triangle
end GovernanceAdjunction
/-! ## Identity sanity probe -/
structure FineClaimantResolution where
  cells : Nat
  deriving DecidableEq, Repr
structure CoarseClaimantResolution where
  cells : Nat
  deriving DecidableEq, Repr
instance : LE FineClaimantResolution where
  le X Y := X.cells ≤ Y.cells
instance : Preorder FineClaimantResolution where
  le_refl := by
    intro X
    exact Nat.le_refl X.cells
  le_trans := by
    intro X Y Z hXY hYZ
    exact Nat.le_trans hXY hYZ
instance : LE CoarseClaimantResolution where
  le X Y := X.cells ≤ Y.cells
instance : Preorder CoarseClaimantResolution where
  le_refl := by
    intro X
    exact Nat.le_refl X.cells
  le_trans := by
    intro X Y Z hXY hYZ
    exact Nat.le_trans hXY hYZ
def identityGovernanceAdjunction :
    GovernanceAdjunction FineClaimantResolution FineClaimantResolution :=
  GovernanceAdjunction.ofMathlibAdjunction
    (Adjunction.id (C := FineClaimantResolution))
/-- The identity governance adjunction satisfies the left triangle law. This is the sanity check that the local `GovernanceAdjunction` wrapper preserves the standard Mathlib adjunction identity when no coarsening or relabeling is present. -/
theorem identity_governance_adjunction_left_triangle :
    Functor.whiskerRight identityGovernanceAdjunction.unit
        identityGovernanceAdjunction.left ≫
      Functor.whiskerLeft identityGovernanceAdjunction.left
        identityGovernanceAdjunction.counit =
      𝟙 identityGovernanceAdjunction.left :=
  identityGovernanceAdjunction.left_triangle
/-- The identity governance adjunction satisfies the right triangle law. Paired with the left triangle theorem, this confirms that converting the Mathlib identity adjunction into the local bundle does not lose either coherence equation. -/
theorem identity_governance_adjunction_right_triangle :
    Functor.whiskerLeft identityGovernanceAdjunction.right
        identityGovernanceAdjunction.unit ≫
      Functor.whiskerRight identityGovernanceAdjunction.counit
        identityGovernanceAdjunction.right =
      𝟙 identityGovernanceAdjunction.right :=
  identityGovernanceAdjunction.right_triangle
/-! ## Coarse-fine claimant-resolution adjunction -/
def coarsenFineCount (n : Nat) : Nat :=
  (n + 1) / 2

def refineCoarseCount (m : Nat) : Nat :=
  2 * m

/-- Coarsening claimant-resolution counts is monotone. Increasing the fine count cannot decrease the rounded-up half count, which is the order-preserving map used for the left functor in the coarse/fine adjunction. -/
theorem coarsenFineCount_monotone :
    Monotone coarsenFineCount := by
  intro n m hnm
  unfold coarsenFineCount
  omega

/-- Refining claimant-resolution counts is monotone. Doubling preserves the preorder on coarse counts, giving the order-preserving map used for the right functor in the coarse/fine adjunction. -/
theorem refineCoarseCount_monotone :
    Monotone refineCoarseCount := by
  intro n m hnm
  unfold refineCoarseCount
  omega

/-- Numeric adjunction law for the coarse/fine claimant-resolution counts. A fine count coarsens below `m` exactly when the original fine count is below the refined coarse count `2 * m`. This arithmetic equivalence supplies the unit and counit inequalities for the claimant-resolution adjunction. -/
theorem coarsenFineCount_le_iff_le_refineCoarseCount
    (n m : Nat) :
    coarsenFineCount n ≤ m ↔ n ≤ refineCoarseCount m := by
  unfold coarsenFineCount refineCoarseCount
  omega

/-- Unit inequality for the coarse/fine count adjunction. A fine count is below the refinement of its coarsening, so the unit component exists in the preorder category. -/
theorem coarsen_refine_unit_count (n : Nat) :
    n ≤ refineCoarseCount (coarsenFineCount n) := by
  exact (coarsenFineCount_le_iff_le_refineCoarseCount n
    (coarsenFineCount n)).mp (Nat.le_refl _)

/-- Counit inequality for the coarse/fine count adjunction. Coarsening a refined coarse count returns below the original coarse count, so the counit component exists in the preorder category. -/
theorem refine_coarsen_counit_count (m : Nat) :
    coarsenFineCount (refineCoarseCount m) ≤ m := by
  exact (coarsenFineCount_le_iff_le_refineCoarseCount
    (refineCoarseCount m) m).mpr (Nat.le_refl _)

def claimantCoarseningFunctor :
    FineClaimantResolution ⥤ CoarseClaimantResolution where
  obj X := ⟨coarsenFineCount X.cells⟩
  map f := homOfLE (by
    exact coarsenFineCount_monotone f.le)

def claimantRefinementFunctor :
    CoarseClaimantResolution ⥤ FineClaimantResolution where
  obj X := ⟨refineCoarseCount X.cells⟩
  map f := homOfLE (by
    exact refineCoarseCount_monotone f.le)

def coarseFineUnit :
    𝟭 FineClaimantResolution ⟶
      claimantCoarseningFunctor ⋙ claimantRefinementFunctor where
  app X := homOfLE (by
    change X.cells ≤ refineCoarseCount (coarsenFineCount X.cells)
    exact coarsen_refine_unit_count X.cells)
  naturality X Y f := by
    apply Subsingleton.elim

def coarseFineCounit :
    claimantRefinementFunctor ⋙ claimantCoarseningFunctor ⟶
      𝟭 CoarseClaimantResolution where
  app X := homOfLE (by
    change coarsenFineCount (refineCoarseCount X.cells) ≤ X.cells
    exact refine_coarsen_counit_count X.cells)
  naturality X Y f := by
    apply Subsingleton.elim

def coarseFineAdjunction :
    claimantCoarseningFunctor ⊣ claimantRefinementFunctor where
  unit := coarseFineUnit
  counit := coarseFineCounit
  left_triangle_components X := by
    apply Subsingleton.elim
  right_triangle_components Y := by
    apply Subsingleton.elim

def coarseFineGovernanceAdjunction :
    GovernanceAdjunction FineClaimantResolution CoarseClaimantResolution :=
  GovernanceAdjunction.ofMathlibAdjunction coarseFineAdjunction

/-- Triangle identities for the coarse/fine claimant-resolution adjunction. The theorem states both component equations: coarsen then unit/counit collapses to the identity on coarse objects, and refine then unit/counit collapses to the identity on fine objects. Since these categories are thin, the proof delegates to the adjunction components, making the count-level construction usable as a governance adjunction witness. -/
theorem coarseFineGovernanceAdjunction_triangle_identities :
    (∀ X : FineClaimantResolution,
      claimantCoarseningFunctor.map (coarseFineUnit.app X) ≫
        coarseFineCounit.app (claimantCoarseningFunctor.obj X) =
        𝟙 (claimantCoarseningFunctor.obj X)) ∧
    (∀ Y : CoarseClaimantResolution,
      coarseFineUnit.app (claimantRefinementFunctor.obj Y) ≫
        claimantRefinementFunctor.map (coarseFineCounit.app Y) =
        𝟙 (claimantRefinementFunctor.obj Y)) := by
  constructor
  · intro X
    exact coarseFineAdjunction.left_triangle_components X
  · intro Y
    exact coarseFineAdjunction.right_triangle_components Y

/-! ## Concrete pair probe witnesses -/

def fineThreeResolution : FineClaimantResolution :=
  ⟨3⟩

def coarseTwoResolution : CoarseClaimantResolution :=
  ⟨2⟩

/-- The concrete three-cell fine resolution expands under the unit round trip. Coarsening three cells gives two coarse cells and refining back gives four, so this fixture witnesses that the unit is not always an isomorphism on raw counts. -/
theorem fineThree_unit_expands_count :
    fineThreeResolution.cells <
      (claimantRefinementFunctor.obj
        (claimantCoarseningFunctor.obj fineThreeResolution)).cells := by
  native_decide

/-- The left triangle identity holds at the concrete three-cell fine fixture. This specializes the abstract coarse/fine adjunction coherence to a finite object where the unit genuinely expands the count. -/
theorem coarseFine_left_triangle_fineThree :
    claimantCoarseningFunctor.map (coarseFineUnit.app fineThreeResolution) ≫
      coarseFineCounit.app
        (claimantCoarseningFunctor.obj fineThreeResolution) =
      𝟙 (claimantCoarseningFunctor.obj fineThreeResolution) :=
  coarseFineAdjunction.left_triangle_components fineThreeResolution

/-- The right triangle identity holds at the concrete two-cell coarse fixture. It gives the paired finite check for the coarse/fine adjunction after refining and then coarsening the object. -/
theorem coarseFine_right_triangle_coarseTwo :
    coarseFineUnit.app (claimantRefinementFunctor.obj coarseTwoResolution) ≫
      claimantRefinementFunctor.map (coarseFineCounit.app coarseTwoResolution) =
      𝟙 (claimantRefinementFunctor.obj coarseTwoResolution) :=
  coarseFineAdjunction.right_triangle_components coarseTwoResolution

/-- The governance-adjunction substrate contains the coarse/fine claimant resolution adjunction. The witness is the concrete adjunction built from halving and doubling claimant-resolution counts, with unit and counit supplied by the arithmetic laws above. This gives the file a nonempty adjunction object, not just isolated monotone maps. -/
theorem governance_adjunction_substrate_supports_coarse_fine :
    Nonempty
      (GovernanceAdjunction
        FineClaimantResolution CoarseClaimantResolution) :=
  ⟨coarseFineGovernanceAdjunction⟩

/-! ## Governance-graph homomorphism lift -/

namespace GovernanceGraphLevel

/-! ### Claimant relabeling on graph inputs -/

def relabelClaim (φ : ClaimantId → ClaimantId) (claim : ClaimQ) :
    ClaimQ where
  id := φ claim.id
  strength := claim.strength
  strength_pos := claim.strength_pos
  metadata := claim.metadata

@[simp] theorem relabelClaim_id (claim : ClaimQ) :
    relabelClaim id claim = claim := by
  cases claim
  rfl

@[simp] theorem relabelClaim_self (claim : ClaimQ) :
    relabelClaim (fun claimant : ClaimantId => claimant) claim = claim := by
  cases claim
  rfl

@[simp] theorem map_relabel_self (claims : List ClaimQ) :
    claims.map (relabelClaim (fun claimant : ClaimantId => claimant)) =
      claims := by
  induction claims with
  | nil =>
      rfl
  | cons claim claims ih =>
      simp [ih]

@[simp] theorem relabelClaim_comp
    (φ ψ : ClaimantId → ClaimantId) (claim : ClaimQ) :
    relabelClaim ψ (relabelClaim φ claim) =
      relabelClaim (ψ ∘ φ) claim := by
  cases claim
  rfl

def relabelGovernanceNode (φ : ClaimantId → ClaimantId)
    (node : GovernanceNodeFn) : GovernanceNodeFn :=
  fun claims claimant =>
    node (claims.map (relabelClaim φ)) (φ claimant)

def relabelGovernanceGraph (φ : ClaimantId → ClaimantId)
    (graph : GovernanceGraph) : GovernanceGraph :=
  graph.map (relabelGovernanceNode φ)

def pairRepresentative (claimant : ClaimantId) : ClaimantId :=
  2 * claimant

def pairBlock (claimant : ClaimantId) : ClaimantId :=
  claimant / 2

def claimantCoarsenGraph (graph : GovernanceGraph) : GovernanceGraph :=
  relabelGovernanceGraph pairRepresentative graph

def claimantRefineGraph (graph : GovernanceGraph) : GovernanceGraph :=
  relabelGovernanceGraph pairBlock graph

/-- Relabeling commutes with the node-level permitted-claim filter. The theorem pushes `relabelClaim` through the filtered list used by a relabeled governance node, so later graph-decision calculations can reason on the original node after changing claimant coordinates. -/
theorem map_relabel_filter_relabelGovernanceNode (φ : ClaimantId → ClaimantId)
    (node : GovernanceNodeFn) (profile claims : List ClaimQ) :
    (claims.filter (fun claim =>
      relabelGovernanceNode φ node profile claim.id == BinaryDecision.Permit)).map
        (relabelClaim φ) =
      (claims.map (relabelClaim φ)).filter (fun claim =>
        node (profile.map (relabelClaim φ)) claim.id == BinaryDecision.Permit) := by
  induction claims with
  | nil => simp
  | cons claim claims ih =>
      by_cases h : node (profile.map (relabelClaim φ)) (φ claim.id) == BinaryDecision.Permit
      · simp only [List.filter_cons, List.map_cons]
        simp [relabelGovernanceNode, relabelClaim, h]
        simpa [relabelGovernanceNode] using ih
      · simp only [List.filter_cons, List.map_cons]
        simp [relabelGovernanceNode, relabelClaim, h]
        simpa [relabelGovernanceNode] using ih

/-- Relabeling commutes with `filterPermitted` for a relabeled governance node. This packages the more general filter lemma at the exact API boundary used by `graphDecide`, avoiding duplicated list reasoning in graph relabeling proofs. -/
theorem map_relabel_filterPermitted_relabelGovernanceNode (φ : ClaimantId → ClaimantId)
    (node : GovernanceNodeFn) (claims : List ClaimQ) :
    (filterPermitted (relabelGovernanceNode φ node) claims).map
        (relabelClaim φ) =
      filterPermitted node (claims.map (relabelClaim φ)) := by
  simpa [filterPermitted] using
    map_relabel_filter_relabelGovernanceNode φ node claims claims

/-- Graph decisions after claimant relabeling are computed by deciding the original graph on relabeled claims and the relabeled claimant. This theorem is the main operational equation for `relabelGovernanceGraph`, and it is the bridge used by both coarsening/refinement graph homomorphisms. -/
theorem graphDecide_relabelGovernanceGraph (φ : ClaimantId → ClaimantId)
    (graph : GovernanceGraph) (claims : List ClaimQ) (claimant : ClaimantId) :
    graphDecide (relabelGovernanceGraph φ graph) claims claimant =
      graphDecide graph (claims.map (relabelClaim φ)) (φ claimant) := by
  induction graph generalizing claims with
  | nil => simp [relabelGovernanceGraph, graphDecide]
  | cons node rest ih =>
      cases hdecision : node (claims.map (relabelClaim φ)) (φ claimant) with
      | Permit =>
          simp [relabelGovernanceGraph, relabelGovernanceNode, graphDecide, hdecision]
          change graphDecide (relabelGovernanceGraph φ rest)
              (filterPermitted (relabelGovernanceNode φ node) claims) claimant =
            graphDecide rest
              (filterPermitted node (claims.map (relabelClaim φ))) (φ claimant)
          rw [ih]
          rw [map_relabel_filterPermitted_relabelGovernanceNode]
      | Deny =>
          simp [relabelGovernanceGraph, relabelGovernanceNode, graphDecide, hdecision]

/-- Taking the representative of a claimant block and then projecting back returns the original claimant. This is the arithmetic round-trip equation that makes the pair-block counit decision-preserving on stable graphs. -/
theorem pairBlock_pairRepresentative (claimant : ClaimantId) :
    pairBlock (pairRepresentative claimant) = claimant := by
  simp [pairBlock, pairRepresentative, Nat.mul_comm]

/-- Projecting a claimant to its pair block is stable under representative round trips. The equation is the companion arithmetic fact used when coarsened and refined claim lists are normalized. -/
theorem pairRepresentative_pairBlock_pairBlock (claimant : ClaimantId) :
    pairBlock (pairRepresentative (pairBlock claimant)) = pairBlock claimant := by
  rw [pairBlock_pairRepresentative]

@[simp] theorem relabelClaim_pairBlock_pairRepresentative (claim : ClaimQ) :
    relabelClaim pairBlock (relabelClaim pairRepresentative claim) = claim := by
  cases claim
  simp [relabelClaim, pairBlock_pairRepresentative]

@[simp] theorem relabelClaim_pairBlock_comp_pairRepresentative (claim : ClaimQ) :
    relabelClaim (pairBlock ∘ pairRepresentative) claim = claim := by
  cases claim
  simp [relabelClaim, Function.comp, pairBlock_pairRepresentative]

@[simp] theorem relabelClaim_pairBlock_pairRepresentative_pairBlock (claim : ClaimQ) :
    relabelClaim (pairBlock ∘ pairRepresentative ∘ pairBlock) claim =
      relabelClaim pairBlock claim := by
  cases claim
  simp [relabelClaim, Function.comp, pairBlock_pairRepresentative]

@[simp] theorem map_relabel_pairBlock_pairRepresentative (claims : List ClaimQ) :
    (claims.map (relabelClaim pairRepresentative)).map
        (relabelClaim pairBlock) = claims := by
  induction claims with
  | nil => rfl
  | cons claim claims ih => simp [ih]

/-- Coarsening after refining by pair representatives preserves graph decisions. The proof rewrites both relabeling layers and uses the pair-block arithmetic round trip on claim lists and claimants. This is the decision equation behind the graph-level counit. -/
theorem graphDecide_pairBlock_pairRepresentative_relabel
    (graph : GovernanceGraph) (claims : List ClaimQ) (claimant : ClaimantId) :
    graphDecide (claimantCoarsenGraph (claimantRefineGraph graph))
        claims claimant =
      graphDecide graph claims claimant := by
  unfold claimantCoarsenGraph claimantRefineGraph
  rw [graphDecide_relabelGovernanceGraph]
  rw [graphDecide_relabelGovernanceGraph]
  rw [pairBlock_pairRepresentative]
  exact congrArg (fun relabeledClaims => graphDecide graph relabeledClaims claimant)
    (map_relabel_pairBlock_pairRepresentative claims)

/-- The mixed pair-block graph is stable under the refine-after-coarsen round trip. Its decision rule depends on the claimant's pair block, so relabeling through representative and block maps leaves every decision unchanged. -/
theorem graphDecide_pairBlockMixedGraph_roundTrip (claims : List ClaimQ)
    (claimant : ClaimantId) :
    graphDecide (claimantRefineGraph (claimantCoarsenGraph
        [fun _ claimant =>
          if (claimant / 2) % 2 == 0 then BinaryDecision.Permit else BinaryDecision.Deny]))
        claims claimant =
      graphDecide [fun _ claimant =>
        if (claimant / 2) % 2 == 0 then BinaryDecision.Permit else BinaryDecision.Deny]
        claims claimant := by
  simp [claimantRefineGraph, claimantCoarsenGraph, graphDecide,
    relabelGovernanceGraph, relabelGovernanceNode, pairRepresentative,
    pairBlock]

/-! ### Decision-preserving governance-graph homomorphisms -/

structure GovernanceGraphObject where
  graph : GovernanceGraph

structure GovernanceGraphHom (X Y : GovernanceGraphObject) where
  claimantMap : ClaimantId → ClaimantId
  preserves_decision :
    ∀ claims claimant,
      graphDecide Y.graph (claims.map (relabelClaim claimantMap))
          (claimantMap claimant) =
        graphDecide X.graph claims claimant

namespace GovernanceGraphHom

@[ext] theorem ext {X Y : GovernanceGraphObject}
    {f g : GovernanceGraphHom X Y}
    (h : f.claimantMap = g.claimantMap) : f = g := by
  cases f with
  | mk fMap fPres =>
    cases g with
    | mk gMap gPres =>
      simp only at h
      subst gMap
      congr

end GovernanceGraphHom

instance governanceGraphObjectCategory : Category GovernanceGraphObject where
  Hom X Y := GovernanceGraphHom X Y
  id X := {
    claimantMap := id
    preserves_decision := by
      intro claims claimant
      congr 1
      induction claims with
      | nil => rfl
      | cons claim claims ih =>
          simp [relabelClaim_id, ih] }
  comp f g := {
    claimantMap := g.claimantMap ∘ f.claimantMap
    preserves_decision := by
      intro claims claimant
      have hg := g.preserves_decision
        (claims.map (relabelClaim f.claimantMap)) (f.claimantMap claimant)
      have hf := f.preserves_decision claims claimant
      simpa [Function.comp, List.map_map] using hg.trans hf }
  id_comp := by
    intro X Y f
    apply GovernanceGraphHom.ext
    funext claimant
    rfl
  comp_id := by
    intro X Y f
    apply GovernanceGraphHom.ext
    funext claimant
    rfl
  assoc := by
    intro W X Y Z f g h
    apply GovernanceGraphHom.ext
    funext claimant
    rfl

/-! ### Decision-preserving stable pair category carrying the graph adjunction -/

structure FinePairStableGovernanceGraphObject where
  graph : GovernanceGraph
  unit_stable :
    ∀ claims claimant,
      graphDecide (claimantRefineGraph (claimantCoarsenGraph graph))
          claims claimant =
        graphDecide graph claims claimant

structure CoarsePairStableGovernanceGraphObject where
  graph : GovernanceGraph
  counit_stable :
    ∀ claims claimant,
      graphDecide (claimantCoarsenGraph (claimantRefineGraph graph))
          claims claimant =
        graphDecide graph claims claimant

def FinePairStableGovernanceGraphObject.toGovernanceGraphObject
    (X : FinePairStableGovernanceGraphObject) : GovernanceGraphObject :=
  ⟨X.graph⟩

def CoarsePairStableGovernanceGraphObject.toGovernanceGraphObject
    (X : CoarsePairStableGovernanceGraphObject) : GovernanceGraphObject :=
  ⟨X.graph⟩

structure PairCoherentGovernanceGraphHom
    (X Y : GovernanceGraphObject) where
  claimantMap : ClaimantId → ClaimantId
  preserves_decision :
    ∀ claims claimant,
      graphDecide Y.graph (claims.map (relabelClaim claimantMap))
          (claimantMap claimant) =
        graphDecide X.graph claims claimant
  commutes_pairRepresentative :
    ∀ claimant,
      claimantMap (pairRepresentative claimant) =
        pairRepresentative (claimantMap claimant)
  commutes_pairBlock :
    ∀ claimant,
      claimantMap (pairBlock claimant) =
        pairBlock (claimantMap claimant)

namespace PairCoherentGovernanceGraphHom

@[ext] theorem ext {X Y : GovernanceGraphObject}
    {f g : PairCoherentGovernanceGraphHom X Y}
    (h : f.claimantMap = g.claimantMap) : f = g := by
  cases f with
  | mk fMap fPres fRep fBlock =>
    cases g with
    | mk gMap gPres gRep gBlock =>
      simp only at h
      subst gMap
      congr

def id (X : GovernanceGraphObject) :
    PairCoherentGovernanceGraphHom X X where
  claimantMap := fun claimant => claimant
  preserves_decision := by
    intro claims claimant
    congr 1
    induction claims with
    | nil => rfl
    | cons claim claims ih =>
        simp [ih]
  commutes_pairRepresentative := by
    intro claimant
    rfl
  commutes_pairBlock := by
    intro claimant
    rfl

def comp {X Y Z : GovernanceGraphObject}
    (f : PairCoherentGovernanceGraphHom X Y)
    (g : PairCoherentGovernanceGraphHom Y Z) :
    PairCoherentGovernanceGraphHom X Z where
  claimantMap := g.claimantMap ∘ f.claimantMap
  preserves_decision := by
    intro claims claimant
    have hg := g.preserves_decision
      (claims.map (relabelClaim f.claimantMap)) (f.claimantMap claimant)
    have hf := f.preserves_decision claims claimant
    simpa [Function.comp, List.map_map] using hg.trans hf
  commutes_pairRepresentative := by
    intro claimant
    simp [Function.comp, f.commutes_pairRepresentative,
      g.commutes_pairRepresentative]
  commutes_pairBlock := by
    intro claimant
    simp [Function.comp, f.commutes_pairBlock, g.commutes_pairBlock]

/-- Pair representatives commute with any pair-coherent claimant map on claim lists. This list-level equation is the naturality calculation for graph homomorphisms that preserve the representative map. -/
theorem map_relabel_pairRepresentative_commute {X Y : GovernanceGraphObject}
    (f : PairCoherentGovernanceGraphHom X Y) (claims : List ClaimQ) :
    ((claims.map (relabelClaim f.claimantMap)).map
        (relabelClaim pairRepresentative)) =
      ((claims.map (relabelClaim pairRepresentative)).map
        (relabelClaim f.claimantMap)) := by
  induction claims with
  | nil =>
      simp
  | cons claim claims ih =>
      cases claim
      simp [relabelClaim, ih, f.commutes_pairRepresentative]

/-- Pair blocks commute with any pair-coherent claimant map on claim lists. This is the companion naturality calculation needed for the refinement side of the graph adjunction. -/
theorem map_relabel_pairBlock_commute {X Y : GovernanceGraphObject}
    (f : PairCoherentGovernanceGraphHom X Y) (claims : List ClaimQ) :
    ((claims.map (relabelClaim f.claimantMap)).map
        (relabelClaim pairBlock)) =
      ((claims.map (relabelClaim pairBlock)).map
        (relabelClaim f.claimantMap)) := by
  induction claims with
  | nil =>
      simp
  | cons claim claims ih =>
      cases claim
      simp [relabelClaim, ih, f.commutes_pairBlock]

end PairCoherentGovernanceGraphHom

instance finePairStableGovernanceGraphObjectCategory :
    Category FinePairStableGovernanceGraphObject where
  Hom X Y := PairCoherentGovernanceGraphHom
    X.toGovernanceGraphObject Y.toGovernanceGraphObject
  id X := PairCoherentGovernanceGraphHom.id X.toGovernanceGraphObject
  comp f g := PairCoherentGovernanceGraphHom.comp f g
  id_comp := by
    intro X Y f
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    simp [PairCoherentGovernanceGraphHom.comp,
      PairCoherentGovernanceGraphHom.id, Function.comp]
  comp_id := by
    intro X Y f
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    simp [PairCoherentGovernanceGraphHom.comp,
      PairCoherentGovernanceGraphHom.id, Function.comp]
  assoc := by
    intro W X Y Z f g h
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    simp [PairCoherentGovernanceGraphHom.comp, Function.comp]

instance coarsePairStableGovernanceGraphObjectCategory :
    Category CoarsePairStableGovernanceGraphObject where
  Hom X Y := PairCoherentGovernanceGraphHom
    X.toGovernanceGraphObject Y.toGovernanceGraphObject
  id X := PairCoherentGovernanceGraphHom.id X.toGovernanceGraphObject
  comp f g := PairCoherentGovernanceGraphHom.comp f g
  id_comp := by
    intro X Y f
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    simp [PairCoherentGovernanceGraphHom.comp,
      PairCoherentGovernanceGraphHom.id, Function.comp]
  comp_id := by
    intro X Y f
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    simp [PairCoherentGovernanceGraphHom.comp,
      PairCoherentGovernanceGraphHom.id, Function.comp]
  assoc := by
    intro W X Y Z f g h
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    simp [PairCoherentGovernanceGraphHom.comp, Function.comp]

def claimantCoarseningFunctor :
    FinePairStableGovernanceGraphObject ⥤
      CoarsePairStableGovernanceGraphObject where
  obj X := {
    graph := claimantCoarsenGraph X.graph
    counit_stable := by
      intro claims claimant
      exact graphDecide_pairBlock_pairRepresentative_relabel
        (claimantCoarsenGraph X.graph) claims claimant }
  map {X Y} f := {
    claimantMap := f.claimantMap
    preserves_decision := by
      intro claims claimant
      change graphDecide (claimantCoarsenGraph Y.graph)
          (claims.map (relabelClaim f.claimantMap))
          (f.claimantMap claimant) =
        graphDecide (claimantCoarsenGraph X.graph) claims claimant
      unfold claimantCoarsenGraph
      rw [graphDecide_relabelGovernanceGraph]
      rw [graphDecide_relabelGovernanceGraph]
      rw [PairCoherentGovernanceGraphHom.map_relabel_pairRepresentative_commute]
      rw [← f.commutes_pairRepresentative]
      exact f.preserves_decision
        (claims.map (relabelClaim pairRepresentative))
        (pairRepresentative claimant)
    commutes_pairRepresentative := f.commutes_pairRepresentative
    commutes_pairBlock := f.commutes_pairBlock }
  map_id := by
    intro X
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    rfl
  map_comp := by
    intro X Y Z f g
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    rfl

def claimantRefinementFunctor :
    CoarsePairStableGovernanceGraphObject ⥤
      FinePairStableGovernanceGraphObject where
  obj X := {
    graph := claimantRefineGraph X.graph
    unit_stable := by
      intro claims claimant
      unfold claimantRefineGraph claimantCoarsenGraph
      rw [graphDecide_relabelGovernanceGraph]
      rw [graphDecide_relabelGovernanceGraph]
      rw [graphDecide_relabelGovernanceGraph]
      rw [graphDecide_relabelGovernanceGraph]
      have hstable :=
        X.counit_stable
          (claims.map (relabelClaim pairBlock)) (pairBlock claimant)
      unfold claimantCoarsenGraph claimantRefineGraph at hstable
      rw [graphDecide_relabelGovernanceGraph] at hstable
      rw [graphDecide_relabelGovernanceGraph] at hstable
      simpa [claimantCoarsenGraph, claimantRefineGraph, List.map_map,
        relabelClaim_comp, Function.comp, pairBlock_pairRepresentative] using
        hstable }
  map {X Y} f := {
    claimantMap := f.claimantMap
    preserves_decision := by
      intro claims claimant
      change graphDecide (claimantRefineGraph Y.graph)
          (claims.map (relabelClaim f.claimantMap))
          (f.claimantMap claimant) =
        graphDecide (claimantRefineGraph X.graph) claims claimant
      unfold claimantRefineGraph
      rw [graphDecide_relabelGovernanceGraph]
      rw [graphDecide_relabelGovernanceGraph]
      rw [PairCoherentGovernanceGraphHom.map_relabel_pairBlock_commute]
      rw [← f.commutes_pairBlock]
      exact f.preserves_decision
        (claims.map (relabelClaim pairBlock)) (pairBlock claimant)
    commutes_pairRepresentative := f.commutes_pairRepresentative
    commutes_pairBlock := f.commutes_pairBlock }
  map_id := by
    intro X
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    rfl
  map_comp := by
    intro X Y Z f g
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    rfl

def claimantGraphUnit :
    𝟭 FinePairStableGovernanceGraphObject ⟶
      claimantCoarseningFunctor ⋙ claimantRefinementFunctor where
  app X := {
    claimantMap := fun claimant => claimant
    preserves_decision := by
      intro claims claimant
      change graphDecide (claimantRefineGraph (claimantCoarsenGraph X.graph))
          (claims.map (relabelClaim (fun claimant : ClaimantId => claimant)))
          claimant =
        graphDecide X.graph claims claimant
      simpa using X.unit_stable claims claimant
    commutes_pairRepresentative := by
      intro claimant
      rfl
    commutes_pairBlock := by
      intro claimant
      rfl }
  naturality X Y f := by
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    rfl

def claimantGraphCounit :
    claimantRefinementFunctor ⋙ claimantCoarseningFunctor ⟶
      𝟭 CoarsePairStableGovernanceGraphObject where
  app X := {
    claimantMap := fun claimant => claimant
    preserves_decision := by
      intro claims claimant
      change graphDecide X.graph
          (claims.map (relabelClaim (fun claimant : ClaimantId => claimant)))
          claimant =
        graphDecide (claimantCoarsenGraph (claimantRefineGraph X.graph))
          claims claimant
      simpa using (X.counit_stable claims claimant).symm
    commutes_pairRepresentative := by
      intro claimant
      rfl
    commutes_pairBlock := by
      intro claimant
      rfl }
  naturality X Y f := by
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    rfl

/-- Decision-level left-triangle coherence for pair-stable governance graphs. After applying coarsening to the unit and then the counit, the proof object for decision preservation agrees with the identity hom's preservation proof. The content is proof irrelevance over an already stable graph, ensuring the categorical triangle is compatible with the decision-preservation field. -/
theorem claimantGraph_left_triangle_decision_coherence
    (X : FinePairStableGovernanceGraphObject)
    (claims : List ClaimQ) (claimant : ClaimantId) :
    ((claimantCoarseningFunctor.map (claimantGraphUnit.app X)) ≫
        claimantGraphCounit.app (claimantCoarseningFunctor.obj X)).preserves_decision
        claims claimant =
      (𝟙 (claimantCoarseningFunctor.obj X) :
        (claimantCoarseningFunctor.obj X) ⟶
          (claimantCoarseningFunctor.obj X)).preserves_decision
        claims claimant := by
  apply proof_irrel

/-- Decision-level right-triangle coherence for pair-stable governance graphs. Refining the counit after the unit gives the same decision-preservation proof as the identity hom on the refined object. This is the companion coherence check that the graph-level adjunction respects the governance decision API, not only the underlying claimant relabeling maps. -/
theorem claimantGraph_right_triangle_decision_coherence
    (X : CoarsePairStableGovernanceGraphObject)
    (claims : List ClaimQ) (claimant : ClaimantId) :
    ((claimantGraphUnit.app (claimantRefinementFunctor.obj X)) ≫
        claimantRefinementFunctor.map (claimantGraphCounit.app X)).preserves_decision
        claims claimant =
      (𝟙 (claimantRefinementFunctor.obj X) :
        (claimantRefinementFunctor.obj X) ⟶
          (claimantRefinementFunctor.obj X)).preserves_decision
        claims claimant := by
  apply proof_irrel

def claimantGraphAdjunction :
    claimantCoarseningFunctor ⊣ claimantRefinementFunctor where
  unit := claimantGraphUnit
  counit := claimantGraphCounit
  left_triangle_components X := by
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    rfl
  right_triangle_components X := by
    apply PairCoherentGovernanceGraphHom.ext
    funext claimant
    rfl

def claimantGraphGovernanceAdjunction :
    GovernanceAdjunction
      FinePairStableGovernanceGraphObject
      CoarsePairStableGovernanceGraphObject :=
  GovernanceAdjunction.ofMathlibAdjunction claimantGraphAdjunction

/-- Triangle identities for the graph-level claimant coarsening/refinement adjunction. The theorem packages the left and right component equations for pair-stable governance graph objects, using extensionality of coherent graph homomorphisms. This lifts the count-level adjunction into a decision-preserving graph substrate. -/
theorem claimantGraphAdjunction_triangle_identities :
    (∀ X : FinePairStableGovernanceGraphObject,
      claimantCoarseningFunctor.map (claimantGraphUnit.app X) ≫
        claimantGraphCounit.app (claimantCoarseningFunctor.obj X) =
        𝟙 (claimantCoarseningFunctor.obj X)) ∧
    (∀ Y : CoarsePairStableGovernanceGraphObject,
      claimantGraphUnit.app (claimantRefinementFunctor.obj Y) ≫
        claimantRefinementFunctor.map (claimantGraphCounit.app Y) =
        𝟙 (claimantRefinementFunctor.obj Y)) := by
  constructor
  · intro X
    exact claimantGraphAdjunction.left_triangle_components X
  · intro Y
    exact claimantGraphAdjunction.right_triangle_components Y

/-! ### Weaker claimant-map category retained as graph-free scaffolding -/

structure ClaimantMapGraphObject where
  point : Unit := ()

structure ClaimantMapGraphHom (X Y : ClaimantMapGraphObject) where
  claimantMap : ClaimantId → ClaimantId

namespace ClaimantMapGraphHom

@[ext] theorem ext {X Y : ClaimantMapGraphObject}
    {f g : ClaimantMapGraphHom X Y}
  (h : f.claimantMap = g.claimantMap) : f = g := by
  cases f
  cases g
  simp only at h
  subst h
  rfl

end ClaimantMapGraphHom

instance claimantMapGraphObjectCategory :
    Category ClaimantMapGraphObject where
  Hom X Y := ClaimantMapGraphHom X Y
  id X := { claimantMap := id }
  comp f g := { claimantMap := g.claimantMap ∘ f.claimantMap }
  id_comp := by intro X Y f; ext claimant; rfl
  comp_id := by intro X Y f; ext claimant; rfl
  assoc := by intro W X Y Z f g h; ext claimant; rfl

def claimantMapOnlyCoarseningFunctor :
    ClaimantMapGraphObject ⥤ ClaimantMapGraphObject where
  obj X := ⟨()⟩
  map f := ⟨f.claimantMap⟩
  map_id := by intro X; apply ClaimantMapGraphHom.ext; funext claimant; rfl
  map_comp := by intro X Y Z f g; apply ClaimantMapGraphHom.ext; funext claimant; rfl

def claimantMapOnlyRefinementFunctor :
    ClaimantMapGraphObject ⥤ ClaimantMapGraphObject where
  obj X := ⟨()⟩
  map f := ⟨f.claimantMap⟩
  map_id := by intro X; apply ClaimantMapGraphHom.ext; funext claimant; rfl
  map_comp := by intro X Y Z f g; apply ClaimantMapGraphHom.ext; funext claimant; rfl

def claimantMapOnlyUnit :
    𝟭 ClaimantMapGraphObject ⟶
      claimantMapOnlyCoarseningFunctor ⋙ claimantMapOnlyRefinementFunctor where
  app X := ⟨id⟩
  naturality X Y f := by apply ClaimantMapGraphHom.ext; funext claimant; rfl

def claimantMapOnlyCounit :
    claimantMapOnlyRefinementFunctor ⋙ claimantMapOnlyCoarseningFunctor ⟶
      𝟭 ClaimantMapGraphObject where
  app X := ⟨id⟩
  naturality X Y f := by apply ClaimantMapGraphHom.ext; funext claimant; rfl

def claimantMapOnlyAdjunction :
    claimantMapOnlyCoarseningFunctor ⊣ claimantMapOnlyRefinementFunctor where
  unit := claimantMapOnlyUnit
  counit := claimantMapOnlyCounit
  left_triangle_components X := by apply ClaimantMapGraphHom.ext; funext claimant; rfl
  right_triangle_components X := by apply ClaimantMapGraphHom.ext; funext claimant; rfl

/-! ### Concrete decision-preserving graph pair witnesses -/

def concretePermitGraph : GovernanceGraph := [fun _ _ => BinaryDecision.Permit]

def concretePermitGraphObject : GovernanceGraphObject := ⟨concretePermitGraph⟩

def concretePermitCoarsenRefineObject : GovernanceGraphObject :=
  ⟨claimantRefineGraph (claimantCoarsenGraph concretePermitGraph)⟩

def concretePermitRefineCoarsenObject : GovernanceGraphObject :=
  ⟨claimantCoarsenGraph (claimantRefineGraph concretePermitGraph)⟩

def concretePermitGraphUnitHom :
    GovernanceGraphHom
      concretePermitGraphObject concretePermitCoarsenRefineObject where
  claimantMap := id
  preserves_decision := by
    intro claims claimant
    simp [concretePermitGraphObject, concretePermitCoarsenRefineObject, concretePermitGraph,
      claimantRefineGraph, claimantCoarsenGraph, relabelGovernanceGraph, relabelGovernanceNode, graphDecide]

def concretePermitGraphCounitHom :
    GovernanceGraphHom
      concretePermitRefineCoarsenObject concretePermitGraphObject where
  claimantMap := id
  preserves_decision := by
    intro claims claimant
    simp [concretePermitGraphObject, concretePermitRefineCoarsenObject, concretePermitGraph,
      claimantRefineGraph, claimantCoarsenGraph, relabelGovernanceGraph, relabelGovernanceNode, graphDecide]

/-- The constant-permit graph has decision-preserving unit and counit witnesses. Both directions of the coarsen/refine round trip are inhabited because relabeling claimants does not change the graph's permit decision. This is the concrete positive fixture for the graph-level adjunction API. -/
theorem concretePermitGraph_has_decision_preserving_unit_counit :
    Nonempty (concretePermitGraphObject ⟶ concretePermitCoarsenRefineObject) ∧
    Nonempty (concretePermitRefineCoarsenObject ⟶ concretePermitGraphObject) :=
  ⟨⟨concretePermitGraphUnitHom⟩, ⟨concretePermitGraphCounitHom⟩⟩

/-! ### Non-trivial mixed graph witnesses and the general no-go -/

def mixedParityGraph : GovernanceGraph :=
  [fun _ claimant => if claimant % 2 == 0 then BinaryDecision.Permit else BinaryDecision.Deny]

/-- Pair-representative relabeling is not decision preserving for the mixed parity graph. The finite calculation compares the coarsened representative decision at claimant `1` against the original mixed-parity decision and shows they differ. This is the explicit obstruction showing graph-level adjunction data needs stability hypotheses. -/
theorem graphDecide_pairRepresentative_relabel_no_go :
    graphDecide (claimantCoarsenGraph mixedParityGraph)
        (([] : List ClaimQ).map (relabelClaim pairRepresentative))
        (pairRepresentative 1) ≠
      graphDecide mixedParityGraph [] 1 := by
  native_decide

def pairBlockMixedGraph : GovernanceGraph :=
  [fun _ claimant => if (claimant / 2) % 2 == 0 then BinaryDecision.Permit else BinaryDecision.Deny]

def pairBlockMixedFineObject : FinePairStableGovernanceGraphObject where
  graph := pairBlockMixedGraph
  unit_stable := by
    intro claims claimant
    simpa [pairBlockMixedGraph] using graphDecide_pairBlockMixedGraph_roundTrip claims claimant

def pairBlockMixedCoarseObject : CoarsePairStableGovernanceGraphObject where
  graph := pairBlockMixedGraph
  counit_stable := by
    intro claims claimant
    exact graphDecide_pairBlock_pairRepresentative_relabel pairBlockMixedGraph claims claimant

def pairBlockMixedCoarsenRefineObject : GovernanceGraphObject :=
  ⟨claimantRefineGraph (claimantCoarsenGraph pairBlockMixedGraph)⟩

def pairBlockMixedRefineCoarsenObject : GovernanceGraphObject :=
  ⟨claimantCoarsenGraph (claimantRefineGraph pairBlockMixedGraph)⟩

def pairBlockMixedGraphUnitHom :
    GovernanceGraphHom
      ⟨pairBlockMixedGraph⟩ pairBlockMixedCoarsenRefineObject where
  claimantMap := id
  preserves_decision := by
    intro claims claimant
    simpa [pairBlockMixedCoarsenRefineObject, pairBlockMixedGraph] using
      graphDecide_pairBlockMixedGraph_roundTrip claims claimant

def pairBlockMixedGraphCounitHom :
    GovernanceGraphHom
      pairBlockMixedRefineCoarsenObject ⟨pairBlockMixedGraph⟩ where
  claimantMap := id
  preserves_decision := by
    intro claims claimant
    exact (graphDecide_pairBlock_pairRepresentative_relabel pairBlockMixedGraph claims claimant).symm

/-- The pair-block mixed graph is nontrivial: it permits claimant `0` and denies claimant `2` on the empty profile. This finite check shows the later decision-preserving unit/counit fixture is not just the constant-permit case. -/
theorem pairBlockMixedGraph_has_mixed_decisions :
    graphDecide pairBlockMixedGraph [] 0 = BinaryDecision.Permit ∧
    graphDecide pairBlockMixedGraph [] 2 = BinaryDecision.Deny := by
  native_decide

/-- The pair-block mixed graph has decision-preserving unit and counit witnesses despite having mixed decisions. Its decisions are stable under the pair-block round trip, so both hom directions are inhabited for the coarsen/refine graph objects. This separates pair-stability from the trivial constant-permit fixture. -/
theorem pairBlockMixedGraph_has_decision_preserving_unit_counit :
    Nonempty (⟨pairBlockMixedGraph⟩ ⟶ pairBlockMixedCoarsenRefineObject) ∧
    Nonempty (pairBlockMixedRefineCoarsenObject ⟶ ⟨pairBlockMixedGraph⟩) :=
  ⟨⟨pairBlockMixedGraphUnitHom⟩, ⟨pairBlockMixedGraphCounitHom⟩⟩

end GovernanceGraphLevel

end Legitimacy
