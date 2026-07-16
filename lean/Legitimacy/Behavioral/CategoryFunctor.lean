/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/
import Legitimacy.Behavioral.StackelbergLineage
import Legitimacy.Behavioral.ConstitutionalAILineage
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic
/-! # Morphism-shaped probe for behavioral lineages -/
set_option autoImplicit false
namespace Legitimacy
open Finset Matrix BigOperators CategoryTheory
structure BehavioralLineage where
  n : Nat
  nonzero : NeZero n
  G : GovGraph ℚ n
  s : Fin n → ℚ
  game : BehavioralGovernanceGame
  perturbationBudget : game.Agents → game.State → ℚ
  utility_nonneg :
    ∀ agent state profile, 0 ≤ game.Utility agent state profile
  utility_le_budget_at_state :
    ∀ agent state profile,
      game.Utility agent state profile ≤ perturbationBudget agent state
  budget_spViolation :
    ∀ agent state,
      letI : NeZero n := nonzero
      G.spViolation s (perturbationBudget agent state)
  spectral_vulnerability_exposes_deviation :
    ∀ {γ : ℚ}, 0 < γ →
      (letI : NeZero n := nonzero
      G.spViolation s γ) →
        ∃ κ : ℚ, 0 < κ ∧ ∃ _dev : game.ProfitableDeviation κ, True
  spectral_threshold_exposes_deviation :
    ∀ {δ κ : ℚ}, 0 < κ → 0 < δ →
      (letI : NeZero n := nonzero
      G.spViolation s (δ / κ)) →
        ∃ _dev : game.ProfitableDeviation κ, True
namespace BehavioralLineage
def spViolation (X : BehavioralLineage) (γ : ℚ) : Prop :=
  letI : NeZero X.n := X.nonzero
  X.G.spViolation X.s γ
structure Hom (X Y : BehavioralLineage) where
  mapProfitableDeviation :
    ∀ {κ : ℚ}, X.game.ProfitableDeviation κ → Y.game.ProfitableDeviation κ
  mapSpectralViolation : ∀ {γ : ℚ}, X.spViolation γ → Y.spViolation γ
namespace Hom
def id (X : BehavioralLineage) : Hom X X where
  mapProfitableDeviation := fun dev => dev
  mapSpectralViolation := fun hviol => hviol
def comp {X Y Z : BehavioralLineage} (f : Hom X Y) (g : Hom Y Z) :
    Hom X Z where
  mapProfitableDeviation := fun dev =>
    g.mapProfitableDeviation (f.mapProfitableDeviation dev)
  mapSpectralViolation := fun hviol =>
    g.mapSpectralViolation (f.mapSpectralViolation hviol)
@[simp] theorem id_mapProfitableDeviation
    (X : BehavioralLineage) {κ : ℚ}
    (dev : X.game.ProfitableDeviation κ) :
    (id X).mapProfitableDeviation dev = dev :=
  rfl
@[simp] theorem id_mapSpectralViolation
    (X : BehavioralLineage) {γ : ℚ} (hviol : X.spViolation γ) :
    (id X).mapSpectralViolation hviol = hviol :=
  rfl
@[simp] theorem comp_mapProfitableDeviation
    {X Y Z : BehavioralLineage} (f : Hom X Y) (g : Hom Y Z)
    {κ : ℚ} (dev : X.game.ProfitableDeviation κ) :
    (comp f g).mapProfitableDeviation dev =
      g.mapProfitableDeviation (f.mapProfitableDeviation dev) :=
  rfl
@[simp] theorem comp_mapSpectralViolation
    {X Y Z : BehavioralLineage} (f : Hom X Y) (g : Hom Y Z)
    {γ : ℚ} (hviol : X.spViolation γ) :
    (comp f g).mapSpectralViolation hviol =
      g.mapSpectralViolation (f.mapSpectralViolation hviol) :=
  rfl
@[ext] theorem ext_of_mapProfitableDeviation
    {X Y : BehavioralLineage} {f g : Hom X Y}
    (hdev :
      ∀ {κ : ℚ} (dev : X.game.ProfitableDeviation κ),
        f.mapProfitableDeviation dev = g.mapProfitableDeviation dev) :
    f = g := by
  cases f with
  | mk fdev fspec =>
    cases g with
    | mk gdev gspec =>
      simp only at hdev
      congr
      funext κ dev
      exact hdev dev
end Hom
lemma spViolation_of_le (X : BehavioralLineage) {δ γ : ℚ}
    (hδ : δ ≤ γ) (hγ : X.spViolation γ) :
    X.spViolation δ := by
  dsimp [spViolation] at hγ ⊢
  letI : NeZero X.n := X.nonzero
  exact (X.G.spViolation_iff_le_cv X.s δ).mpr
    (le_trans hδ ((X.G.spViolation_iff_le_cv X.s γ).mp hγ))
lemma gain_le_deviated_utility (X : BehavioralLineage) {κ : ℚ}
    (dev : X.game.ProfitableDeviation κ) :
    dev.gain ≤ X.game.Utility dev.agent dev.state dev.deviated := by
  have hbase_nonneg :
      0 ≤ X.game.Utility dev.agent dev.state dev.base :=
    X.utility_nonneg dev.agent dev.state dev.base
  unfold BehavioralGovernanceGame.ProfitableDeviation.gain
  unfold BehavioralGovernanceGame.utilityGain
  linarith
theorem perturbation_budget_reflects_best_response_gain
    (X : BehavioralLineage) {κ : ℚ}
    (dev : X.game.ProfitableDeviation κ) :
    X.spViolation dev.gain := by
  have hgain_le_deviated :
      dev.gain ≤ X.game.Utility dev.agent dev.state dev.deviated :=
    X.gain_le_deviated_utility dev
  have hdeviated_budget :
      X.game.Utility dev.agent dev.state dev.deviated ≤
        X.perturbationBudget dev.agent dev.state :=
    X.utility_le_budget_at_state dev.agent dev.state dev.deviated
  exact X.spViolation_of_le (le_trans hgain_le_deviated hdeviated_budget)
    (X.budget_spViolation dev.agent dev.state)
theorem graph_decision_matches_game
    (X : BehavioralLineage) {κ : ℚ}
    (dev : X.game.ProfitableDeviation κ)
    (_hflip :
      X.game.GovernanceDecision dev.state dev.deviated dev.agent ≠
        X.game.GovernanceDecision dev.state dev.base dev.agent) :
    X.spViolation dev.gain :=
  X.perturbation_budget_reflects_best_response_gain dev
def toSpectralBehavioralEmbedding (X : BehavioralLineage) :
    letI : NeZero X.n := X.nonzero
    SpectralBehavioralEmbedding X.G X.s X.game := by
  letI : NeZero X.n := X.nonzero
  exact
    { graph_decision_matches_game := fun dev hflip =>
        show X.G.spViolation X.s dev.gain from
          X.graph_decision_matches_game dev hflip
      perturbation_budget_reflects_best_response_gain := fun dev =>
        show X.G.spViolation X.s dev.gain from
          X.perturbation_budget_reflects_best_response_gain dev
      spectral_vulnerability_exposes_profitable_deviation :=
        fun _hregular {γ} hγ hviol =>
          X.spectral_vulnerability_exposes_deviation hγ hviol
      spectral_threshold_violation_exposes_profitable_deviation :=
        fun _hregular {δ κ} hκ hδ hviol =>
          X.spectral_threshold_exposes_deviation hκ hδ hviol }
structure EmbeddedBehavioralLineage where
  carrier : BehavioralLineage
  embedding :
    letI : NeZero carrier.n := carrier.nonzero
    SpectralBehavioralEmbedding carrier.G carrier.s carrier.game
namespace EmbeddedBehavioralLineage
structure Hom (X Y : EmbeddedBehavioralLineage) where
  base : BehavioralLineage.Hom X.carrier Y.carrier
  maps_profitable_deviation_to_embedding_violation :
    ∀ {κ : ℚ} (dev : X.carrier.game.ProfitableDeviation κ),
      letI : NeZero Y.carrier.n := Y.carrier.nonzero
      Y.carrier.G.spViolation Y.carrier.s
        ((base.mapProfitableDeviation dev).gain)
  transports_positive_spectral_vulnerability :
    ∀ {γ : ℚ}, 0 < γ → X.carrier.spViolation γ →
      Y.carrier.game.BestResponseDecomposedRegularity →
        ∃ κ : ℚ, 0 < κ ∧
          ∃ _dev : Y.carrier.game.ProfitableDeviation κ, True
namespace Hom
/-- Identity morphism in the embedded target. -/
def id (X : EmbeddedBehavioralLineage) : Hom X X where
  base := BehavioralLineage.Hom.id X.carrier
  maps_profitable_deviation_to_embedding_violation := fun dev => by
    letI : NeZero X.carrier.n := X.carrier.nonzero
    exact X.embedding.perturbation_budget_reflects_best_response_gain dev
  transports_positive_spectral_vulnerability := fun hγ hviol hregular => by
    letI : NeZero X.carrier.n := X.carrier.nonzero
    exact X.embedding.spectral_vulnerability_exposes_profitable_deviation
      hregular hγ hviol
/-- Composition in the embedded target. -/
def comp {X Y Z : EmbeddedBehavioralLineage} (f : Hom X Y) (g : Hom Y Z) :
    Hom X Z where
  base := BehavioralLineage.Hom.comp f.base g.base
  maps_profitable_deviation_to_embedding_violation := fun dev =>
    g.maps_profitable_deviation_to_embedding_violation
      (f.base.mapProfitableDeviation dev)
  transports_positive_spectral_vulnerability := fun hγ hviol hregular =>
    g.transports_positive_spectral_vulnerability hγ
      (f.base.mapSpectralViolation hviol) hregular
@[ext] theorem ext_of_base
    {X Y : EmbeddedBehavioralLineage} {f g : Hom X Y}
    (hbase : f.base = g.base) :
    f = g := by
  cases f with
  | mk fbase fdev fspec =>
    cases g with
    | mk gbase gdev gspec =>
      cases hbase
      rfl
end Hom
end EmbeddedBehavioralLineage
instance instCategoryBehavioralLineage : CategoryTheory.Category BehavioralLineage where
  Hom X Y := BehavioralLineage.Hom X Y
  id X := BehavioralLineage.Hom.id X
  comp f g := BehavioralLineage.Hom.comp f g
  id_comp := by intro X Y f; cases f; rfl
  comp_id := by intro X Y f; cases f; rfl
  assoc := by intro W X Y Z f g h; cases f; cases g; cases h; rfl
instance instCategoryEmbeddedBehavioralLineage : CategoryTheory.Category EmbeddedBehavioralLineage where
  Hom X Y := EmbeddedBehavioralLineage.Hom X Y
  id X := EmbeddedBehavioralLineage.Hom.id X
  comp f g := EmbeddedBehavioralLineage.Hom.comp f g
  id_comp := by intro X Y f; apply EmbeddedBehavioralLineage.Hom.ext_of_base; rfl
  comp_id := by intro X Y f; apply EmbeddedBehavioralLineage.Hom.ext_of_base; rfl
  assoc := by intro W X Y Z f g h; apply EmbeddedBehavioralLineage.Hom.ext_of_base; rfl
/-- A functor-shaped map from primitive behavioral lineages to their derived
spectral-behavioral embeddings. -/
structure LineageEmbeddingFunctor where
  mapObj : BehavioralLineage → EmbeddedBehavioralLineage
  mapHom :
    {X Y : BehavioralLineage} → Hom X Y →
      EmbeddedBehavioralLineage.Hom (mapObj X) (mapObj Y)
  mapId :
    ∀ X : BehavioralLineage,
      mapHom (Hom.id X) = EmbeddedBehavioralLineage.Hom.id (mapObj X)
  mapComp :
    ∀ {X Y Z : BehavioralLineage} (f : Hom X Y) (g : Hom Y Z),
      mapHom (Hom.comp f g) =
        EmbeddedBehavioralLineage.Hom.comp (mapHom f) (mapHom g)
def LineageEmbeddingFunctor.toCategoryTheoryFunctor (F : LineageEmbeddingFunctor) :
    CategoryTheory.Functor BehavioralLineage EmbeddedBehavioralLineage where
  obj := F.mapObj
  map := fun f => F.mapHom f
  map_id := F.mapId
  map_comp := F.mapComp
/-- The canonical functor candidate: objects are sent to the derived embedding
bundle, and morphisms are transported unchanged as primitive witness maps. -/
def embeddingFunctor : LineageEmbeddingFunctor where
  mapObj := fun X =>
    { carrier := X
      embedding := X.toSpectralBehavioralEmbedding }
  mapHom := fun {X Y} f =>
    { base := f
      maps_profitable_deviation_to_embedding_violation := fun dev => by
        letI : NeZero Y.n := Y.nonzero
        exact Y.toSpectralBehavioralEmbedding
          |>.perturbation_budget_reflects_best_response_gain
            (f.mapProfitableDeviation dev)
      transports_positive_spectral_vulnerability := fun hγ hviol hregular => by
        letI : NeZero Y.n := Y.nonzero
        exact Y.toSpectralBehavioralEmbedding
          |>.spectral_vulnerability_exposes_profitable_deviation
            hregular hγ (f.mapSpectralViolation hviol) }
  mapId := by
    intro X
    rfl
  mapComp := by
    intro X Y Z f g
    rfl
@[simp] theorem embeddingFunctor_map_id_profitableDeviation
    (X : BehavioralLineage) {κ : ℚ}
    (dev : X.game.ProfitableDeviation κ) :
    ((embeddingFunctor.mapHom (Hom.id X)).base.mapProfitableDeviation dev) = dev :=
  rfl
@[simp] theorem embeddingFunctor_map_comp_profitableDeviation
    {X Y Z : BehavioralLineage} (f : Hom X Y) (g : Hom Y Z)
    {κ : ℚ} (dev : X.game.ProfitableDeviation κ) :
    ((embeddingFunctor.mapHom (Hom.comp f g)).base.mapProfitableDeviation dev) =
      g.mapProfitableDeviation (f.mapProfitableDeviation dev) :=
  rfl
theorem embeddingFunctor_mathlib_id_comp_base
    {X Y : BehavioralLineage} (f : X ⟶ Y) :
    ((embeddingFunctor.toCategoryTheoryFunctor.map (𝟙 X ≫ f)).base) =
      (embeddingFunctor.toCategoryTheoryFunctor.map f).base := by
  rw [CategoryTheory.Category.id_comp]
/-- The embedding functor constructs target embedding evidence for every
mapped profitable deviation. -/
theorem embeddingFunctor_mapHom_embedding_violation
    {X Y : BehavioralLineage} (f : Hom X Y) {κ : ℚ}
    (dev : X.game.ProfitableDeviation κ) :
    letI : NeZero Y.n := Y.nonzero
    Y.G.spViolation Y.s
      (((embeddingFunctor.mapHom f).base.mapProfitableDeviation dev).gain) :=
  (embeddingFunctor.mapHom f).maps_profitable_deviation_to_embedding_violation dev
section PermRelabelFunctor
def permRelabelGraph {n : Nat} (σ : Equiv.Perm (Fin n)) (G : GovGraph ℚ n) : GovGraph ℚ n where
  weights := fun i j => G.weights (σ.symm i) (σ.symm j)
  weight_symm := fun i j => G.weight_symm (σ.symm i) (σ.symm j)
  weight_nonneg := fun i j => G.weight_nonneg (σ.symm i) (σ.symm j)
  weight_self_zero := fun i => G.weight_self_zero (σ.symm i)
def permRelabelSignal {n : Nat} (σ : Equiv.Perm (Fin n)) (s : Fin n → ℚ) : Fin n → ℚ :=
  fun i => s (σ.symm i)
@[simp] theorem permRelabelGraph_gov_apply {n : Nat}
    (σ : Equiv.Perm (Fin n)) (G : GovGraph ℚ n) (s : Fin n → ℚ) (i : Fin n) :
    (permRelabelGraph σ G).gov (permRelabelSignal σ s) (σ i) = G.gov s i := by
  dsimp [GovGraph.gov, GovGraph.deg, GovGraph.W, permRelabelGraph, permRelabelSignal]
  simp only [Equiv.symm_apply_apply]
  have hsum := Equiv.sum_comp σ.symm (fun j => G.weights i j * s j)
  have hdeg := Equiv.sum_comp σ.symm (fun j => G.weights i j)
  simp only at hsum hdeg
  rw [hsum, hdeg]
@[simp] theorem permRelabelGraph_govRemoved_apply {n : Nat}
    (σ : Equiv.Perm (Fin n)) (G : GovGraph ℚ n) (s : Fin n → ℚ) (k i : Fin n) :
    (permRelabelGraph σ G).govRemoved (permRelabelSignal σ s) (σ k) (σ i) = G.govRemoved s k i := by
  dsimp [GovGraph.govRemoved, GovGraph.degRemoved, GovGraph.W, permRelabelGraph, permRelabelSignal]
  simp only [Equiv.symm_apply_apply]
  have hsum :
      (∑ j : Fin n, if j = σ k then (0 : ℚ) else G.weights i (σ.symm j) * s (σ.symm j)) =
        ∑ j : Fin n, if j = k then (0 : ℚ) else G.weights i j * s j := by
    simpa [Equiv.symm_apply_eq] using
      Equiv.sum_comp σ.symm (fun j => if j = k then (0 : ℚ) else G.weights i j * s j)
  have hdeg :
      (∑ j : Fin n, if j = σ k then (0 : ℚ) else G.weights i (σ.symm j)) =
        ∑ j : Fin n, if j = k then (0 : ℚ) else G.weights i j := by
    simpa [Equiv.symm_apply_eq] using
      Equiv.sum_comp σ.symm (fun j => if j = k then (0 : ℚ) else G.weights i j)
  rw [hsum, hdeg]
theorem permRelabel_spViolation_of_spViolation {n : Nat} [NeZero n]
    (σ : Equiv.Perm (Fin n)) (G : GovGraph ℚ n) (s : Fin n → ℚ) {γ : ℚ} :
    G.spViolation s γ → (permRelabelGraph σ G).spViolation (permRelabelSignal σ s) γ := by
  rintro ⟨p, hp⟩
  exact ⟨(σ p.1, σ p.2), by simpa using hp⟩
theorem spViolation_of_permRelabel_spViolation {n : Nat} [NeZero n]
    (σ : Equiv.Perm (Fin n)) (G : GovGraph ℚ n) (s : Fin n → ℚ) {γ : ℚ} :
    (permRelabelGraph σ G).spViolation (permRelabelSignal σ s) γ → G.spViolation s γ := by
  rintro ⟨p, hp⟩
  refine ⟨(σ.symm p.1, σ.symm p.2), ?_⟩
  have hgov : (permRelabelGraph σ G).gov (permRelabelSignal σ s) p.2 = G.gov s (σ.symm p.2) := by
    simpa [Equiv.apply_symm_apply] using permRelabelGraph_gov_apply σ G s (σ.symm p.2)
  have hremoved : (permRelabelGraph σ G).govRemoved (permRelabelSignal σ s) p.1 p.2 =
      G.govRemoved s (σ.symm p.1) (σ.symm p.2) := by
    simpa [Equiv.apply_symm_apply] using permRelabelGraph_govRemoved_apply σ G s (σ.symm p.1) (σ.symm p.2)
  simpa [hgov, hremoved] using hp
def permRelabelLineage (X : BehavioralLineage) (σ : Equiv.Perm (Fin X.n)) : BehavioralLineage where
  n := X.n
  nonzero := X.nonzero
  G := permRelabelGraph σ X.G
  s := permRelabelSignal σ X.s
  game := X.game
  perturbationBudget := X.perturbationBudget
  utility_nonneg := X.utility_nonneg
  utility_le_budget_at_state := X.utility_le_budget_at_state
  budget_spViolation := fun agent state => by
    letI : NeZero X.n := X.nonzero; exact permRelabel_spViolation_of_spViolation σ X.G X.s (X.budget_spViolation agent state)
  spectral_vulnerability_exposes_deviation := by
    intro γ hγ hviol; letI : NeZero X.n := X.nonzero
    exact X.spectral_vulnerability_exposes_deviation hγ (spViolation_of_permRelabel_spViolation σ X.G X.s hviol)
  spectral_threshold_exposes_deviation := by
    intro δ κ hκ hδ hviol; letI : NeZero X.n := X.nonzero
    exact X.spectral_threshold_exposes_deviation hκ hδ (spViolation_of_permRelabel_spViolation σ X.G X.s hviol)
def permRelabelHom (σ : (m : Nat) → Equiv.Perm (Fin m)) {X Y : BehavioralLineage} (f : Hom X Y) :
    Hom (permRelabelLineage X (σ X.n)) (permRelabelLineage Y (σ Y.n)) where
  mapProfitableDeviation := fun dev => f.mapProfitableDeviation dev
  mapSpectralViolation := fun hviol => by
    letI : NeZero X.n := X.nonzero; letI : NeZero Y.n := Y.nonzero
    exact permRelabel_spViolation_of_spViolation (σ Y.n) Y.G Y.s
      (f.mapSpectralViolation (spViolation_of_permRelabel_spViolation (σ X.n) X.G X.s hviol))
def permRelabelEmbeddingFunctor (σ : (m : Nat) → Equiv.Perm (Fin m)) : LineageEmbeddingFunctor where
  mapObj := fun X =>
    { carrier := permRelabelLineage X (σ X.n)
      embedding := (permRelabelLineage X (σ X.n)).toSpectralBehavioralEmbedding }
  mapHom := fun {X Y} f =>
    { base := permRelabelHom σ f
      maps_profitable_deviation_to_embedding_violation := fun dev => by
        letI : NeZero (permRelabelLineage Y (σ Y.n)).n := (permRelabelLineage Y (σ Y.n)).nonzero
        exact (permRelabelLineage Y (σ Y.n)).toSpectralBehavioralEmbedding
          |>.perturbation_budget_reflects_best_response_gain
            ((permRelabelHom σ f).mapProfitableDeviation dev)
      transports_positive_spectral_vulnerability := fun hγ hviol hregular => by
        letI : NeZero (permRelabelLineage Y (σ Y.n)).n := (permRelabelLineage Y (σ Y.n)).nonzero
        exact (permRelabelLineage Y (σ Y.n)).toSpectralBehavioralEmbedding
          |>.spectral_vulnerability_exposes_profitable_deviation
            hregular hγ ((permRelabelHom σ f).mapSpectralViolation hviol) }
  mapId := by intro X; rfl
  mapComp := by intro X Y Z f g; rfl
theorem permRelabelSignal_trans {n : Nat}
    (σ τ : Equiv.Perm (Fin n)) (s : Fin n → ℚ) :
    permRelabelSignal (τ.trans σ) s =
      permRelabelSignal σ (permRelabelSignal τ s) := by
  funext i
  rfl
theorem permRelabelGraph_trans {n : Nat}
    (σ τ : Equiv.Perm (Fin n)) (G : GovGraph ℚ n) :
    permRelabelGraph (τ.trans σ) G =
      permRelabelGraph σ (permRelabelGraph τ G) := by
  cases G
  rfl
theorem permRelabelLineage_trans
    (X : BehavioralLineage) (σ τ : Equiv.Perm (Fin X.n)) :
    permRelabelLineage X (τ.trans σ) =
      permRelabelLineage (permRelabelLineage X τ) σ := by
  cases X
  simp [permRelabelLineage, permRelabelGraph_trans, permRelabelSignal_trans]
theorem permRelabelEmbeddingFunctor_compose
    (σ τ : (m : Nat) → Equiv.Perm (Fin m))
    (X : BehavioralLineage) :
    (permRelabelEmbeddingFunctor (fun m => (τ m).trans (σ m))).mapObj X =
      (permRelabelEmbeddingFunctor σ).mapObj
        ((permRelabelEmbeddingFunctor τ).mapObj X).carrier := by
  simp [permRelabelEmbeddingFunctor, EmbeddedBehavioralLineage.mk.injEq]
  change permRelabelLineage X ((τ X.n).trans (σ X.n)) =
    permRelabelLineage (permRelabelLineage X (τ X.n)) (σ X.n)
  exact permRelabelLineage_trans X (σ X.n) (τ X.n)
end PermRelabelFunctor
section UnitRelabelFunctor
/-- A non-identity relabeling of a game by a terminal coordinate on agents and
states.  It is equivalent to the original game but not definitionally the same
object. -/
def unitRelabelGame (game : BehavioralGovernanceGame) :
    BehavioralGovernanceGame where
  Agents := game.Agents × Unit
  State := game.State × Unit
  Action := fun agent => game.Action agent.1
  Utility := fun agent state profile =>
    game.Utility agent.1 state.1 (fun a => profile (a, ()))
  Transition := fun state profile =>
    (game.Transition state.1 (fun a => profile (a, ())), ())
  Observation := fun agent state => game.Observation agent.1 state.1
  GovernanceDecision := fun state profile agent =>
    game.GovernanceDecision state.1 (fun a => profile (a, ())) agent.1
/-- Relabel an action profile into the terminal-coordinate game copy. -/
def unitRelabelProfile {game : BehavioralGovernanceGame}
    (profile : ActionProfile game.Action) :
    ActionProfile (unitRelabelGame game).Action :=
  fun agent => profile agent.1
/-- Forget the terminal coordinate from an action profile. -/
def unitUnrelabelProfile {game : BehavioralGovernanceGame}
    (profile : ActionProfile (unitRelabelGame game).Action) :
    ActionProfile game.Action :=
  fun agent => profile (agent, ())
@[simp] theorem unitUnrelabelProfile_unitRelabelProfile
    {game : BehavioralGovernanceGame}
    (profile : ActionProfile game.Action) :
    unitUnrelabelProfile (unitRelabelProfile profile) = profile :=
  rfl
@[simp] theorem unitRelabelProfile_unitUnrelabelProfile
    {game : BehavioralGovernanceGame}
    (profile : ActionProfile (unitRelabelGame game).Action) :
    unitRelabelProfile (unitUnrelabelProfile profile) = profile := by
  funext agent
  cases agent with
  | mk a u =>
    cases u
    rfl
/-- Relabel a profitable deviation into the terminal-coordinate game copy. -/
def unitRelabelDeviation {game : BehavioralGovernanceGame} {κ : ℚ}
    (dev : game.ProfitableDeviation κ) :
    (unitRelabelGame game).ProfitableDeviation κ where
  agent := (dev.agent, ())
  state := (dev.state, ())
  base := unitRelabelProfile dev.base
  deviated := unitRelabelProfile dev.deviated
  unilateral := by
    intro agent hne
    dsimp [unitRelabelProfile]
    exact dev.unilateral agent.1 (by
      intro hagent
      apply hne
      cases agent with
      | mk a u =>
        cases u
        exact Prod.ext hagent (Subsingleton.elim _ _))
  positive_gain := by
    simpa [unitRelabelGame, unitRelabelProfile,
      BehavioralGovernanceGame.utilityGain] using dev.positive_gain
  capability_feasible := by
    simpa [unitRelabelGame, unitRelabelProfile,
      BehavioralGovernanceGame.utilityGain] using dev.capability_feasible
/-- Forget the terminal coordinate from a relabeled profitable deviation. -/
def unitUnrelabelDeviation {game : BehavioralGovernanceGame} {κ : ℚ}
    (dev : (unitRelabelGame game).ProfitableDeviation κ) :
    game.ProfitableDeviation κ where
  agent := dev.agent.1
  state := dev.state.1
  base := unitUnrelabelProfile dev.base
  deviated := unitUnrelabelProfile dev.deviated
  unilateral := by
    intro agent hne
    exact dev.unilateral (agent, ()) (by
      intro hagent
      exact hne (congrArg Prod.fst hagent))
  positive_gain := by
    simpa [unitRelabelGame, unitUnrelabelProfile,
      BehavioralGovernanceGame.utilityGain] using dev.positive_gain
  capability_feasible := by
    simpa [unitRelabelGame, unitUnrelabelProfile,
      BehavioralGovernanceGame.utilityGain] using dev.capability_feasible
@[simp] theorem unitUnrelabelDeviation_unitRelabelDeviation
    {game : BehavioralGovernanceGame} {κ : ℚ}
    (dev : game.ProfitableDeviation κ) :
    unitUnrelabelDeviation (unitRelabelDeviation dev) = dev := by
  cases dev
  rfl
@[simp] theorem unitRelabelDeviation_unitUnrelabelDeviation
    {game : BehavioralGovernanceGame} {κ : ℚ}
    (dev : (unitRelabelGame game).ProfitableDeviation κ) :
    unitRelabelDeviation (unitUnrelabelDeviation dev) = dev := by
  cases dev with
  | mk agent state base deviated unilateral positive_gain capability_feasible =>
    cases agent with
    | mk agent agentUnit =>
      cases agentUnit
      cases state with
      | mk state stateUnit =>
        cases stateUnit
        simp [unitRelabelDeviation, unitUnrelabelDeviation,
          unitRelabelProfile_unitUnrelabelProfile]
/-- Relabel a behavioral lineage by adding a terminal coordinate to game
agents and states while leaving its spectral substrate unchanged. -/
def unitRelabelLineage (X : BehavioralLineage) : BehavioralLineage where
  n := X.n
  nonzero := X.nonzero
  G := X.G
  s := X.s
  game := unitRelabelGame X.game
  perturbationBudget := fun agent state =>
    X.perturbationBudget agent.1 state.1
  utility_nonneg := fun agent state profile =>
    X.utility_nonneg agent.1 state.1 (unitUnrelabelProfile profile)
  utility_le_budget_at_state := fun agent state profile =>
    X.utility_le_budget_at_state agent.1 state.1
      (unitUnrelabelProfile profile)
  budget_spViolation := fun agent state => X.budget_spViolation agent.1 state.1
  spectral_vulnerability_exposes_deviation := by
    intro γ hγ hviol
    obtain ⟨κ, hκ, dev, hdev⟩ :=
      X.spectral_vulnerability_exposes_deviation hγ hviol
    exact ⟨κ, hκ, unitRelabelDeviation dev, hdev⟩
  spectral_threshold_exposes_deviation := by
    intro δ κ hκ hδ hviol
    obtain ⟨dev, hdev⟩ :=
      X.spectral_threshold_exposes_deviation hκ hδ hviol
    exact ⟨unitRelabelDeviation dev, hdev⟩
/-- Transport a primitive morphism through the terminal-coordinate relabeling.
The deviation component is a genuine unlabel-map-relabel operation. -/
def unitRelabelHom {X Y : BehavioralLineage} (f : Hom X Y) :
    Hom (unitRelabelLineage X) (unitRelabelLineage Y) where
  mapProfitableDeviation := fun dev =>
    unitRelabelDeviation (f.mapProfitableDeviation
      (unitUnrelabelDeviation dev))
  mapSpectralViolation := fun hviol => f.mapSpectralViolation hviol
/-- The terminal-coordinate relabeling is a non-identity functor candidate:
objects are changed to equivalent `× Unit` games, and morphisms are transported
by explicit relabeling rather than by reusing `base := f`. -/
def unitRelabelEmbeddingFunctor : LineageEmbeddingFunctor where
  mapObj := fun X =>
    { carrier := unitRelabelLineage X
      embedding := (unitRelabelLineage X).toSpectralBehavioralEmbedding }
  mapHom := fun {X Y} f =>
    { base := unitRelabelHom f
      maps_profitable_deviation_to_embedding_violation := fun dev => by
        letI : NeZero (unitRelabelLineage Y).n :=
          (unitRelabelLineage Y).nonzero
        exact (unitRelabelLineage Y).toSpectralBehavioralEmbedding
          |>.perturbation_budget_reflects_best_response_gain
            ((unitRelabelHom f).mapProfitableDeviation dev)
      transports_positive_spectral_vulnerability := fun hγ hviol hregular => by
        letI : NeZero (unitRelabelLineage Y).n :=
          (unitRelabelLineage Y).nonzero
        exact (unitRelabelLineage Y).toSpectralBehavioralEmbedding
          |>.spectral_vulnerability_exposes_profitable_deviation
            hregular hγ ((unitRelabelHom f).mapSpectralViolation hviol) }
  mapId := by
    intro X
    apply EmbeddedBehavioralLineage.Hom.ext_of_base
    apply Hom.ext_of_mapProfitableDeviation
    intro κ dev
    exact unitRelabelDeviation_unitUnrelabelDeviation dev
  mapComp := by
    intro X Y Z f g
    apply EmbeddedBehavioralLineage.Hom.ext_of_base
    apply Hom.ext_of_mapProfitableDeviation
    intro κ dev
    simp [unitRelabelHom, EmbeddedBehavioralLineage.Hom.comp, Hom.comp]
@[simp] theorem unitRelabelEmbeddingFunctor_mapObj_agents
    (X : BehavioralLineage) :
    (unitRelabelEmbeddingFunctor.mapObj X).carrier.game.Agents =
      (X.game.Agents × Unit) :=
  rfl
@[simp] theorem unitRelabelEmbeddingFunctor_mapHom_agent
    {X Y : BehavioralLineage} (f : Hom X Y) {κ : ℚ}
    (dev : (unitRelabelEmbeddingFunctor.mapObj X).carrier.game.ProfitableDeviation κ) :
    (((unitRelabelEmbeddingFunctor.mapHom f).base.mapProfitableDeviation dev).agent) =
      ((f.mapProfitableDeviation (unitUnrelabelDeviation dev)).agent, ()) :=
  rfl
end UnitRelabelFunctor
section ConcreteLineages
variable {n : Nat} [NeZero n]
/-- Stackelberg node-removal lineages instantiate the primitive
behavioral-lineage object shape. -/
def ofStackelberg (L : StackelbergBehavioralLineage n) : BehavioralLineage where
  n := n
  nonzero := inferInstance
  G := L.G
  s := L.s
  game := L.toGame
  perturbationBudget := fun agent state => L.perturbationBudget agent state
  utility_nonneg := fun agent state profile =>
    L.utility_nonneg agent state profile
  utility_le_budget_at_state := fun agent state profile =>
    L.utility_le_budget_at_state agent state profile
  budget_spViolation := by
    intro agent state
    exact ⟨(agent, state), le_rfl⟩
  spectral_vulnerability_exposes_deviation := by
    intro γ hγ hviol
    rcases hviol with ⟨p, hp⟩
    refine ⟨γ, hγ, ?_⟩
    exact ⟨L.profitableDeviationOfBudget hγ le_rfl hp, trivial⟩
  spectral_threshold_exposes_deviation := by
    intro δ κ hκ hδ hviol
    rcases hviol with ⟨p, hp⟩
    let η : ℚ := min (δ / κ) κ
    have hscale : 0 < δ / κ := div_pos hδ hκ
    have hη : 0 < η := StackelbergBehavioralLineage.rat_min_pos hscale hκ
    have hη_capability : η ≤ κ := min_le_right _ _
    have hη_budget : η ≤ L.perturbationBudget p.1 p.2 :=
      le_trans (min_le_left _ _) hp
    exact ⟨L.profitableDeviationOfBudget hη hη_capability hη_budget, trivial⟩
/-- Constitutional-AI audit lineages instantiate the same primitive
behavioral-lineage object shape. -/
def ofConstitutionalAI (L : ConstitutionalAIBehavioralLineage n) :
    BehavioralLineage where
  n := n
  nonzero := inferInstance
  G := L.G
  s := L.s
  game := L.toGame
  perturbationBudget := fun agent state => L.perturbationBudget agent state
  utility_nonneg := fun agent state profile =>
    L.utility_nonneg agent state profile
  utility_le_budget_at_state := fun agent state profile =>
    L.utility_le_budget_at_state agent state profile
  budget_spViolation := by
    intro agent state
    exact ⟨(agent, state), le_rfl⟩
  spectral_vulnerability_exposes_deviation := by
    intro γ hγ hviol
    rcases hviol with ⟨p, hp⟩
    refine ⟨γ, hγ, ?_⟩
    exact ⟨L.profitableDeviationOfBudget hγ le_rfl hp, trivial⟩
  spectral_threshold_exposes_deviation := by
    intro δ κ hκ hδ hviol
    rcases hviol with ⟨p, hp⟩
    let η : ℚ := min (δ / κ) κ
    have hscale : 0 < δ / κ := div_pos hδ hκ
    have hη : 0 < η := ConstitutionalAIBehavioralLineage.rat_min_pos hscale hκ
    have hη_capability : η ≤ κ := min_le_right _ _
    have hη_budget : η ≤ L.perturbationBudget p.1 p.2 :=
      le_trans (min_le_left _ _) hp
    exact ⟨L.profitableDeviationOfBudget hη hη_capability hη_budget, trivial⟩
end ConcreteLineages
section ToyCase
def stackelbergWitnessLineage : StackelbergBehavioralLineage 3 where
  G := uniTriGraph
  s := sig
def stackelbergWitnessObject : BehavioralLineage :=
  ofStackelberg stackelbergWitnessLineage
noncomputable def constitutionalAIWitnessObject : BehavioralLineage :=
  ofConstitutionalAI
    ConstitutionalAIBehavioralLineage.constitutionalAIWitnessLineage
def strongStackelbergWitnessLineage : StackelbergBehavioralLineage 3 where
  G := asymTriGraph
  s := sig
def strongStackelbergWitnessObject : BehavioralLineage :=
  ofStackelberg strongStackelbergWitnessLineage
def swapZeroOneFamily : (m : Nat) → Equiv.Perm (Fin m) := fun m =>
  if h : 2 ≤ m then
    Equiv.swap (⟨0, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin m)
  else
    Equiv.refl (Fin m)
theorem swapZeroOneFamily_m_ne_refl :
    ∀ m, 2 ≤ m → swapZeroOneFamily m ≠ Equiv.refl (Fin m) := by
  intro m hm h
  have h0 := congrArg (fun σ : Equiv.Perm (Fin m) =>
    σ (⟨0, by omega⟩ : Fin m)) h
  simp [swapZeroOneFamily, hm] at h0
theorem permRelabelEmbeddingFunctor_nonidentity_witness :
    swapZeroOneFamily 3 ≠ Equiv.refl (Fin 3) ∧
      ((permRelabelEmbeddingFunctor swapZeroOneFamily).mapObj
          stackelbergWitnessObject).carrier.s ⟨0, by native_decide⟩ ≠
        (embeddingFunctor.mapObj stackelbergWitnessObject).carrier.s
          ⟨0, by native_decide⟩ := by
  constructor
  · exact swapZeroOneFamily_m_ne_refl 3 (by norm_num)
  · change (2 : ℚ) ≠ 1
    norm_num
def behavioralLineageZero (X : BehavioralLineage) : Fin X.n :=
  ⟨0, Nat.pos_of_ne_zero (@NeZero.ne Nat _ X.n X.nonzero)⟩
def embeddedCarrierEnvelope (F : LineageEmbeddingFunctor)
    {X Y : BehavioralLineage} (f : Hom X Y) :
    Σ A : EmbeddedBehavioralLineage, Σ B : EmbeddedBehavioralLineage,
      EmbeddedBehavioralLineage.Hom A B :=
  ⟨F.mapObj X, F.mapObj Y, F.mapHom f⟩
theorem permRelabelEmbeddingFunctor_carrier_nonidentity :
    ∃ (X : BehavioralLineage) (f : BehavioralLineage.Hom X X),
      embeddedCarrierEnvelope (permRelabelEmbeddingFunctor swapZeroOneFamily) f ≠
        embeddedCarrierEnvelope embeddingFunctor f := by
  refine ⟨stackelbergWitnessObject, Hom.id stackelbergWitnessObject, ?_⟩
  intro h
  have hobj := congrArg Sigma.fst h
  have hcarrier := congrArg EmbeddedBehavioralLineage.carrier hobj
  have hsignal := congrArg
    (fun X : BehavioralLineage => X.s (behavioralLineageZero X)) hcarrier
  change (2 : ℚ) = 1 at hsignal
  norm_num at hsignal
def strongStackelbergWitness_spViolation_at_two_one {γ : ℚ} (hγ : γ ≤ 4 / 3) :
    strongStackelbergWitnessObject.spViolation γ := by
  dsimp [strongStackelbergWitnessObject, strongStackelbergWitnessLineage, ofStackelberg, spViolation]
  refine ⟨((2 : Fin 3), (1 : Fin 3)), ?_⟩
  convert hγ using 1
  native_decide
lemma strongStackelbergWitness_spViolation_four_thirds_unique (p : Fin 3 × Fin 3) :
    (4 / 3 : ℚ) ≤ |asymTriGraph.gov sig p.2 - asymTriGraph.govRemoved sig p.1 p.2| ↔
      p = ((2 : Fin 3), (1 : Fin 3)) := by
  cases p with
  | mk p₁ p₂ => fin_cases p₁ <;> fin_cases p₂ <;> native_decide
lemma strongStackelbergWitness_spViolation_four_thirds_choose
    (hviol : strongStackelbergWitnessObject.spViolation (4 / 3 : ℚ)) :
    Classical.choose hviol = ((2 : Fin 3), (1 : Fin 3)) := by
  dsimp [strongStackelbergWitnessObject, strongStackelbergWitnessLineage, ofStackelberg, spViolation] at hviol
  exact (strongStackelbergWitness_spViolation_four_thirds_unique
    (Classical.choose hviol)).mp (Classical.choose_spec hviol)
def swapZeroOneRelabeledStrongStackelbergWitness_spViolation_four_thirds_at_two_zero :
    ((permRelabelEmbeddingFunctor swapZeroOneFamily).mapObj
      strongStackelbergWitnessObject).carrier.spViolation (4 / 3 : ℚ) := by
  dsimp [permRelabelEmbeddingFunctor, permRelabelLineage, strongStackelbergWitnessObject,
    strongStackelbergWitnessLineage, ofStackelberg, spViolation, permRelabelGraph,
    permRelabelSignal, swapZeroOneFamily]
  refine ⟨((2 : Fin 3), (0 : Fin 3)), ?_⟩
  native_decide
lemma swapZeroOneRelabeledStrongStackelbergWitness_spViolation_four_thirds_unique
    (p : Fin 3 × Fin 3) :
    (4 / 3 : ℚ) ≤ |(permRelabelGraph (swapZeroOneFamily 3) asymTriGraph).gov
        (permRelabelSignal (swapZeroOneFamily 3) sig) p.2 -
      (permRelabelGraph (swapZeroOneFamily 3) asymTriGraph).govRemoved
        (permRelabelSignal (swapZeroOneFamily 3) sig) p.1 p.2| ↔
      p = ((2 : Fin 3), (0 : Fin 3)) := by
  cases p with
  | mk p₁ p₂ => fin_cases p₁ <;> fin_cases p₂ <;> native_decide
lemma swapZeroOneRelabeledStrongStackelbergWitness_spViolation_four_thirds_choose
    (hviol :
      ((permRelabelEmbeddingFunctor swapZeroOneFamily).mapObj
      strongStackelbergWitnessObject).carrier.spViolation (4 / 3 : ℚ)) :
    Classical.choose hviol = ((2 : Fin 3), (0 : Fin 3)) := by
  dsimp [permRelabelEmbeddingFunctor, permRelabelLineage, strongStackelbergWitnessObject,
    strongStackelbergWitnessLineage, ofStackelberg, spViolation, permRelabelGraph,
    permRelabelSignal, swapZeroOneFamily] at hviol
  exact (swapZeroOneRelabeledStrongStackelbergWitness_spViolation_four_thirds_unique
    (Classical.choose hviol)).mp (Classical.choose_spec hviol)
theorem strongStackelbergWitness_lineage_graph_ne :
    strongStackelbergWitnessLineage.G ≠ stackelbergWitnessLineage.G := by
  intro h
  have hweight :
      strongStackelbergWitnessLineage.G.weights 1 2 =
        stackelbergWitnessLineage.G.weights 1 2 :=
    congrArg (fun G : GovGraph ℚ 3 => G.weights 1 2) h
  have hne :
      strongStackelbergWitnessLineage.G.weights 1 2 ≠
        stackelbergWitnessLineage.G.weights 1 2 := by
    native_decide
  exact hne hweight
theorem strongStackelbergWitness_cv_gt_source :
    stackelbergWitnessLineage.G.cv stackelbergWitnessLineage.s <
      strongStackelbergWitnessLineage.G.cv strongStackelbergWitnessLineage.s := by
  rw [stackelbergWitnessLineage, strongStackelbergWitnessLineage]
  rw [concrete_cv_values.1, concrete_cv_values.2.1]
  norm_num
/-- The identity toy case is preserved by the embedding functor for the
Stackelberg witness object. -/
theorem stackelbergWitness_functor_preserves_identity :
    (embeddingFunctor.mapHom (Hom.id stackelbergWitnessObject)).base =
      Hom.id stackelbergWitnessObject :=
  congrArg EmbeddedBehavioralLineage.Hom.base
    (embeddingFunctor.mapId stackelbergWitnessObject)
/-- The identity toy case is preserved by the embedding functor for the
Constitutional AI witness object. -/
theorem constitutionalAIWitness_functor_preserves_identity :
    (embeddingFunctor.mapHom (Hom.id constitutionalAIWitnessObject)).base =
      Hom.id constitutionalAIWitnessObject :=
  congrArg EmbeddedBehavioralLineage.Hom.base
    (embeddingFunctor.mapId constitutionalAIWitnessObject)
/-- Spectral violations transport from the uniform triangle to the higher-CV
asymmetric triangle through an explicit CV inequality, not through shared-CV
side-channel equality. -/
lemma stackelbergWitness_spViolation_to_strong {γ : ℚ}
    (hviol : stackelbergWitnessObject.spViolation γ) :
    strongStackelbergWitnessObject.spViolation γ := by
  dsimp [stackelbergWitnessObject, strongStackelbergWitnessObject,
    stackelbergWitnessLineage, strongStackelbergWitnessLineage,
    ofStackelberg, spViolation] at hviol ⊢
  have hle_uni : γ ≤ uniTriGraph.cv sig :=
    (uniTriGraph.spViolation_iff_le_cv sig γ).mp hviol
  have hcv_le : uniTriGraph.cv sig ≤ asymTriGraph.cv sig := by
    rw [concrete_cv_values.1, concrete_cv_values.2.1]
    norm_num
  exact (asymTriGraph.spViolation_iff_le_cv sig γ).mpr
    (le_trans hle_uni hcv_le)
/-- Profitable deviations transport across the distinct substrate by first
reflecting the source deviation to a spectral violation, then realizing that
transported violation as a fresh target-side executable perturbation. -/
noncomputable def stackelbergWitnessToStrongDeviation {κ : ℚ}
    (dev : stackelbergWitnessObject.game.ProfitableDeviation κ) :
    strongStackelbergWitnessObject.game.ProfitableDeviation κ := by
  have hsource : stackelbergWitnessObject.spViolation dev.gain :=
    stackelbergWitnessObject.perturbation_budget_reflects_best_response_gain dev
  have htarget : strongStackelbergWitnessObject.spViolation dev.gain :=
    stackelbergWitness_spViolation_to_strong hsource
  dsimp [strongStackelbergWitnessObject, strongStackelbergWitnessLineage,
    ofStackelberg, spViolation] at htarget ⊢
  let p : Fin 3 × Fin 3 := Classical.choose htarget
  have hp : dev.gain ≤
      strongStackelbergWitnessLineage.perturbationBudget p.1 p.2 :=
    Classical.choose_spec htarget
  exact strongStackelbergWitnessLineage.profitableDeviationOfBudget
    dev.positive_gain dev.capability_feasible hp
/-- Concrete primitive morphism from the uniform-triangle Stackelberg witness
to the strongly connected Stackelberg witness. -/
noncomputable def stackelbergWitnessToStrongHom :
    Hom stackelbergWitnessObject strongStackelbergWitnessObject where
  mapProfitableDeviation := fun dev =>
    stackelbergWitnessToStrongDeviation dev
  mapSpectralViolation := fun hviol =>
    stackelbergWitness_spViolation_to_strong hviol
/-- The distinct-substrate morphism transports spectral violations via the
proved CV comparison. -/
theorem distinct_substrate_morphism_transports_spectral_violation {γ : ℚ}
    (hviol : stackelbergWitnessObject.spViolation γ) :
    strongStackelbergWitnessObject.spViolation γ :=
  stackelbergWitnessToStrongHom.mapSpectralViolation hviol
def swapZeroOneRelabeledStackelbergWitness_spViolation_one_at_two_zero :
    ((permRelabelEmbeddingFunctor swapZeroOneFamily).mapObj
      stackelbergWitnessObject).carrier.spViolation (1 : ℚ) := by
  dsimp [permRelabelEmbeddingFunctor, permRelabelLineage, stackelbergWitnessObject,
    stackelbergWitnessLineage, ofStackelberg, spViolation, permRelabelGraph,
    permRelabelSignal, swapZeroOneFamily]
  refine ⟨((2 : Fin 3), (0 : Fin 3)), ?_⟩
  native_decide
lemma strongStackelbergWitness_spViolation_one_unique (p : Fin 3 × Fin 3) :
    (1 : ℚ) ≤ |asymTriGraph.gov sig p.2 -
      asymTriGraph.govRemoved sig p.1 p.2| ↔
      p = ((2 : Fin 3), (1 : Fin 3)) := by
  cases p with
  | mk p₁ p₂ => fin_cases p₁ <;> fin_cases p₂ <;> native_decide
lemma strongStackelbergWitness_spViolation_one_choose
    (hviol : strongStackelbergWitnessObject.spViolation (1 : ℚ)) :
    Classical.choose hviol = ((2 : Fin 3), (1 : Fin 3)) := by
  dsimp [strongStackelbergWitnessObject, strongStackelbergWitnessLineage,
    ofStackelberg, spViolation] at hviol
  exact (strongStackelbergWitness_spViolation_one_unique
    (Classical.choose hviol)).mp (Classical.choose_spec hviol)
lemma swapZeroOneRelabeledStrongStackelbergWitness_spViolation_one_unique
    (p : Fin 3 × Fin 3) :
    (1 : ℚ) ≤ |(permRelabelGraph (swapZeroOneFamily 3) asymTriGraph).gov
        (permRelabelSignal (swapZeroOneFamily 3) sig) p.2 -
      (permRelabelGraph (swapZeroOneFamily 3) asymTriGraph).govRemoved
        (permRelabelSignal (swapZeroOneFamily 3) sig) p.1 p.2| ↔
      p = ((2 : Fin 3), (0 : Fin 3)) := by
  cases p with
  | mk p₁ p₂ => fin_cases p₁ <;> fin_cases p₂ <;> native_decide
lemma swapZeroOneRelabeledStrongStackelbergWitness_spViolation_one_choose
    (hviol :
      ((permRelabelEmbeddingFunctor swapZeroOneFamily).mapObj
      strongStackelbergWitnessObject).carrier.spViolation (1 : ℚ)) :
    Classical.choose hviol = ((2 : Fin 3), (0 : Fin 3)) := by
  dsimp [permRelabelEmbeddingFunctor, permRelabelLineage,
    strongStackelbergWitnessObject, strongStackelbergWitnessLineage,
    ofStackelberg, spViolation, permRelabelGraph, permRelabelSignal,
    swapZeroOneFamily] at hviol
  exact (swapZeroOneRelabeledStrongStackelbergWitness_spViolation_one_unique
    (Classical.choose hviol)).mp (Classical.choose_spec hviol)
theorem permRelabelEmbeddingFunctor_mapHom_genuinely_distinct :
    ∃ (X Y : BehavioralLineage) (f : BehavioralLineage.Hom X Y)
      (hviol :
        BehavioralLineage.spViolation
          (((permRelabelEmbeddingFunctor swapZeroOneFamily).mapObj X).carrier)
          (1 : ℚ)),
      letI : NeZero X.n := X.nonzero
      let canonicalInput :=
        spViolation_of_permRelabel_spViolation
          (swapZeroOneFamily X.n) X.G X.s hviol
      let perm_mapped :=
        (permRelabelEmbeddingFunctor swapZeroOneFamily).mapHom f
      let canonical_mapped := embeddingFunctor.mapHom f
      Classical.choose (perm_mapped.base.mapSpectralViolation hviol) =
          ((swapZeroOneFamily Y.n)
              (Classical.choose
                (f.mapSpectralViolation canonicalInput)).1,
            (swapZeroOneFamily Y.n)
              (Classical.choose
                (f.mapSpectralViolation canonicalInput)).2) ∧
        Classical.choose (perm_mapped.base.mapSpectralViolation hviol) ≠
          Classical.choose (canonical_mapped.base.mapSpectralViolation canonicalInput) := by
  refine ⟨stackelbergWitnessObject, strongStackelbergWitnessObject,
    stackelbergWitnessToStrongHom,
    swapZeroOneRelabeledStackelbergWitness_spViolation_one_at_two_zero, ?_⟩
  constructor
  · rw [swapZeroOneRelabeledStrongStackelbergWitness_spViolation_one_choose,
      strongStackelbergWitness_spViolation_one_choose]
    change ((2 : Fin 3), (0 : Fin 3)) =
      ((swapZeroOneFamily 3) (2 : Fin 3),
        (swapZeroOneFamily 3) (1 : Fin 3))
    native_decide
  · rw [swapZeroOneRelabeledStrongStackelbergWitness_spViolation_one_choose]
    letI : NeZero stackelbergWitnessObject.n := stackelbergWitnessObject.nonzero
    change ((2 : Fin 3), (0 : Fin 3)) ≠
      Classical.choose
        (stackelbergWitnessToStrongHom.mapSpectralViolation
          (spViolation_of_permRelabel_spViolation
            (swapZeroOneFamily stackelbergWitnessObject.n)
            stackelbergWitnessObject.G stackelbergWitnessObject.s
            swapZeroOneRelabeledStackelbergWitness_spViolation_one_at_two_zero))
    rw [strongStackelbergWitness_spViolation_one_choose]
    native_decide
/-- Action map from the concrete Stackelberg witness into the concrete
Constitutional AI witness.  It preserves the primitive target and amplitude
data; the deployment decision label is not part of this morphism. -/
def stackelbergWitnessToConstitutionalAIAction
    (agent : Fin 3)
    (action : stackelbergWitnessLineage.Action agent) :
    ConstitutionalAIBehavioralLineage.constitutionalAIWitnessLineage.Action agent :=
  ⟨action.1, ⟨action.2.1, by
    constructor
    · exact action.2.2.1
    · simpa [stackelbergWitnessLineage,
        ConstitutionalAIBehavioralLineage.constitutionalAIWitnessLineage,
        StackelbergBehavioralLineage.perturbationBudget,
        ConstitutionalAIBehavioralLineage.perturbationBudget] using action.2.2.2⟩⟩
/-- Profile-level action map for the concrete toy morphism. -/
def stackelbergWitnessToConstitutionalAIProfile
    (profile : ActionProfile stackelbergWitnessLineage.Action) :
    ActionProfile
      ConstitutionalAIBehavioralLineage.constitutionalAIWitnessLineage.Action :=
  fun agent => stackelbergWitnessToConstitutionalAIAction agent (profile agent)
@[simp] lemma stackelbergWitnessToConstitutionalAIAction_target
    (agent : Fin 3) (action : stackelbergWitnessLineage.Action agent) :
    ConstitutionalAIBehavioralLineage.constitutionalAIWitnessLineage.actionTarget
      (stackelbergWitnessToConstitutionalAIAction agent action) =
        stackelbergWitnessLineage.actionTarget action :=
  rfl
@[simp] lemma stackelbergWitnessToConstitutionalAIAction_amplitude
    (agent : Fin 3) (action : stackelbergWitnessLineage.Action agent) :
    ConstitutionalAIBehavioralLineage.constitutionalAIWitnessLineage.actionAmplitude
      (stackelbergWitnessToConstitutionalAIAction agent action) =
        stackelbergWitnessLineage.actionAmplitude action :=
  rfl
/-- Profitable deviations in the Stackelberg witness map to profitable
deviations in the Constitutional AI witness because the primitive
target/amplitude utility surface is shared. -/
def stackelbergWitnessToConstitutionalAIDeviation {κ : ℚ}
    (dev : stackelbergWitnessLineage.toGame.ProfitableDeviation κ) :
    BehavioralGovernanceGame.ProfitableDeviation
      ConstitutionalAIBehavioralLineage.constitutionalAIWitnessLineage.toGame κ where
  agent := dev.agent
  state := dev.state
  base := stackelbergWitnessToConstitutionalAIProfile dev.base
  deviated := stackelbergWitnessToConstitutionalAIProfile dev.deviated
  unilateral := by
    intro agent hne
    simp [stackelbergWitnessToConstitutionalAIProfile, dev.unilateral agent hne]
  positive_gain := by
    simpa [BehavioralGovernanceGame.utilityGain,
      StackelbergBehavioralLineage.toGame,
      ConstitutionalAIBehavioralLineage.toGame,
      stackelbergWitnessToConstitutionalAIProfile] using dev.positive_gain
  capability_feasible := by
    simpa [BehavioralGovernanceGame.utilityGain,
      StackelbergBehavioralLineage.toGame,
      ConstitutionalAIBehavioralLineage.toGame,
      stackelbergWitnessToConstitutionalAIProfile] using dev.capability_feasible
/-- Concrete primitive morphism from the Stackelberg witness object to the
Constitutional AI witness object. -/
def stackelbergWitnessToConstitutionalAIHom :
    Hom stackelbergWitnessObject constitutionalAIWitnessObject where
  mapProfitableDeviation := fun dev =>
    stackelbergWitnessToConstitutionalAIDeviation dev
  mapSpectralViolation := by
    intro γ hviol
    simpa [stackelbergWitnessObject, constitutionalAIWitnessObject,
      stackelbergWitnessLineage, ofStackelberg, ofConstitutionalAI,
      ConstitutionalAIBehavioralLineage.constitutionalAIWitnessLineage,
      spViolation] using hviol
/-- The toy morphism preserves composition under the embedding functor. -/
theorem toy_functor_preserves_composition :
    (embeddingFunctor.mapHom
      (Hom.comp stackelbergWitnessToConstitutionalAIHom
        (Hom.id constitutionalAIWitnessObject))).base =
      Hom.comp
        (embeddingFunctor.mapHom stackelbergWitnessToConstitutionalAIHom).base
        (embeddingFunctor.mapHom (Hom.id constitutionalAIWitnessObject)).base :=
  congrArg EmbeddedBehavioralLineage.Hom.base
    (embeddingFunctor.mapComp stackelbergWitnessToConstitutionalAIHom
      (Hom.id constitutionalAIWitnessObject))
/-- The toy morphism preserves profitable-deviation witnesses pointwise. -/
theorem toy_morphism_preserves_profitable_deviation
    {κ : ℚ}
    (dev : stackelbergWitnessLineage.toGame.ProfitableDeviation κ) :
    (stackelbergWitnessToConstitutionalAIHom.mapProfitableDeviation dev) =
      stackelbergWitnessToConstitutionalAIDeviation dev :=
  rfl
end ToyCase
end BehavioralLineage
end Legitimacy
