/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Behavioral.CategoryFunctor
import Legitimacy.Diagnostics.Graph
import Legitimacy.Spectral.Dynamics.AdversarialStackelberg
import Legitimacy.Spectral.CrossScale.ClaimantInteraction

/-!
# Cross-substrate graph/spectral bridge probe

This file probes the smallest honest equivalence target between the binary
`GovernanceGraph` substrate and the spectral-behavioral substrate. A bare
binary graph does not contain a weighted graph, signal, or game semantics, so
the bridge is an enriched correspondence witness: the graph is related to a
behavioral lineage whose spectral embedding is already supplied by the
behavioral functor layer.

The probe proves:

* a constructive graph-to-spectral CV bridge for complete first-effective
  peer-relative surfaces, using the claimant-interaction lift;
* a structure-preserving one-way theorem for strategyproofness, requiring only
  the embedding fields;
* a two-way theorem when the existing decomposed-regularity hypothesis is
  supplied;
* two concrete witnesses, one strategyproof and one non-strategyproof, whose
  graph-side and spectral-side predicates are transported without relying on
  definitional equality.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

/-! ## Complete peer-relative obstruction to positive spectral CV -/

/-- The explicit spectral carrier used for the complete first-effective
peer-relative obstruction bridge. The graph side supplies the certified
first-effective peer-relative surface; the spectral side is the induced
claimant-interaction carrier at the five-claimant arity used by the finite
spectral certificates. -/
noncomputable abbrev completePeerRelativeSpectralGraph
    (G : GovernanceGraph) : GovGraph ℚ 5 :=
  claimantInteractionGraph G 5

/-- The concrete signal paired with `completePeerRelativeSpectralGraph`.
Together these two definitions are the graph-to-spectral correspondence for
BRIDGE-1; the theorem below proves that a complete first-effective
peer-relative surface forces positive CV for this lift. -/
abbrev completePeerRelativeSpectralSignal
    (_G : GovernanceGraph) : Fin 5 → ℚ :=
  sig5

/-- Carrier identification for the explicit BRIDGE-1 lift: a graph with a
complete first-effective peer-relative surface is sent to the constructed
complete claimant-interaction graph, which is definitionally `uniK5` at arity
five. -/
theorem completePeerRelativeSpectralGraph_eq_uniK5_of_completeSurface
    {G : GovernanceGraph}
    (h : ∃ pref tail,
      CompleteFirstEffectivePeerRelativeSurfaceClass G pref tail) :
    completePeerRelativeSpectralGraph G = uniK5 := by
  change claimantInteractionGraph G 5 = uniK5
  rw [claimantInteractionGraph_eq_constructedPeerRelativeCarrier_of_completeSurface
    (G := G) (n := 5) h]
  rfl

/-- BRIDGE-1, constructive form: a complete first-effective peer-relative graph
obstruction induces positive spectral consistency vulnerability on the explicit
claimant-interaction lift. The calculation is not existential: the structural
certificate rewrites the lift to `uniK5`, and the finite spectral certificate
computes `uniK5.cv sig5 = 3 / 4`. -/
theorem completePeerRelativeObstruction_implies_positiveSpectralCV
    {G : GovernanceGraph}
    (h : ∃ pref tail,
      CompleteFirstEffectivePeerRelativeSurfaceClass G pref tail) :
    0 < (completePeerRelativeSpectralGraph G).cv
      (completePeerRelativeSpectralSignal G) := by
  rw [completePeerRelativeSpectralGraph_eq_uniK5_of_completeSurface h]
  change 0 < uniK5.cv sig5
  rw [fiveNode_cv_values.1]
  norm_num

/-- Prefix/tail-specialized BRIDGE-1 entry point for callers that already have
the complete first-effective surface certificate unbundled. -/
theorem completeFirstEffectivePeerRelativeSurface_implies_positiveSpectralCV
    (G pref tail : GovernanceGraph)
    (h : CompleteFirstEffectivePeerRelativeSurfaceClass G pref tail) :
    0 < (completePeerRelativeSpectralGraph G).cv
      (completePeerRelativeSpectralSignal G) :=
  completePeerRelativeObstruction_implies_positiveSpectralCV
    (G := G) ⟨pref, tail, h⟩

/-- An enriched correspondence from a binary governance graph to a concrete
spectral-behavioral realization. The graph/game equivalence is kept separate
from the spectral embedding so the bridge exposes exactly which substrate
assumption closes the gap. -/
structure GraphSpectralCorrespondence (graph : GovernanceGraph) where
  n : Nat
  nonzero : NeZero n
  spectralGraph : GovGraph ℚ n
  signal : Fin n → ℚ
  game : BehavioralGovernanceGame
  embedding :
    letI : NeZero n := nonzero
    SpectralBehavioralEmbedding spectralGraph signal game
  graph_game_strategyproof :
    GraphStrategyproofness graph ↔ game.GameStrategyproof

namespace GraphSpectralCorrespondence

/-- The spectral predicate corresponding to binary graph strategyproofness. -/
def ZeroConsistencyVulnerabilityPredicate
    {graph : GovernanceGraph} (corr : GraphSpectralCorrespondence graph) : Prop :=
  letI : NeZero corr.n := corr.nonzero
  ZeroConsistencyVulnerability corr.spectralGraph corr.signal

/-- Deprecated compatibility alias: the corrected name is
`ZeroConsistencyVulnerabilityPredicate`. -/
def SpectralStrategyproofPredicate
    {graph : GovernanceGraph} (corr : GraphSpectralCorrespondence graph) : Prop :=
  corr.ZeroConsistencyVulnerabilityPredicate

/-- The binary graph predicate used in the probe. -/
def GraphStrategyproofPredicate (graph : GovernanceGraph) : Prop :=
  GraphStrategyproofness graph

/-- Construct a graph/spectral correspondence from the stronger F2 behavioral
lineage substrate. -/
def ofLineage (graph : GovernanceGraph) (lineage : BehavioralLineage)
    (hgraphGame : GraphStrategyproofness graph ↔ lineage.game.GameStrategyproof) :
    GraphSpectralCorrespondence graph where
  n := lineage.n
  nonzero := lineage.nonzero
  spectralGraph := lineage.G
  signal := lineage.s
  game := lineage.game
  embedding := lineage.toSpectralBehavioralEmbedding
  graph_game_strategyproof := hgraphGame

/-- One-way structure preservation: zero consistency vulnerability transports back
to graph strategyproofness through the behavioral witness. -/
theorem zero_consistency_vulnerability_implies_graph_strategyproof
    {graph : GovernanceGraph} (corr : GraphSpectralCorrespondence graph) :
    corr.ZeroConsistencyVulnerabilityPredicate →
      GraphStrategyproofPredicate graph := by
  intro hspectral
  have hgame : corr.game.GameStrategyproof := by
    letI : NeZero corr.n := corr.nonzero
    exact SpectralBehavioralEmbedding.zero_consistency_vulnerability_implies_game_strategyproof
      corr.embedding hspectral
  exact corr.graph_game_strategyproof.mpr hgame

/-- Deprecated compatibility alias for
`zero_consistency_vulnerability_implies_graph_strategyproof`. -/
theorem spectral_strategyproof_implies_graph_strategyproof
    {graph : GovernanceGraph} (corr : GraphSpectralCorrespondence graph) :
    corr.SpectralStrategyproofPredicate →
      GraphStrategyproofPredicate graph :=
  corr.zero_consistency_vulnerability_implies_graph_strategyproof

/-- The reverse direction is available exactly under the existing
decomposed-regularity assumption for the behavioral substrate. -/
theorem graph_strategyproof_implies_zero_consistency_vulnerability
    {graph : GovernanceGraph} (corr : GraphSpectralCorrespondence graph)
    (hregular : corr.game.BestResponseDecomposedRegularity) :
    GraphStrategyproofPredicate graph →
      corr.ZeroConsistencyVulnerabilityPredicate := by
  intro hgraph
  have hgame : corr.game.GameStrategyproof :=
    corr.graph_game_strategyproof.mp hgraph
  letI : NeZero corr.n := corr.nonzero
  exact SpectralBehavioralEmbedding.game_strategyproof_implies_zero_consistency_vulnerability
    corr.embedding hregular hgame

/-- Deprecated compatibility alias for
`graph_strategyproof_implies_zero_consistency_vulnerability`. -/
theorem graph_strategyproof_implies_spectral_strategyproof
    {graph : GovernanceGraph} (corr : GraphSpectralCorrespondence graph)
    (hregular : corr.game.BestResponseDecomposedRegularity) :
    GraphStrategyproofPredicate graph →
      corr.SpectralStrategyproofPredicate :=
  corr.graph_strategyproof_implies_zero_consistency_vulnerability hregular

/-- Universalized two-way target: graph and zero consistency vulnerability are
equivalent for correspondences whose behavioral witness is decomposed-regular. -/
theorem graph_strategyproof_iff_zero_consistency_vulnerability
    {graph : GovernanceGraph} (corr : GraphSpectralCorrespondence graph)
    (hregular : corr.game.BestResponseDecomposedRegularity) :
    GraphStrategyproofPredicate graph ↔
      corr.ZeroConsistencyVulnerabilityPredicate := by
  constructor
  · exact corr.graph_strategyproof_implies_zero_consistency_vulnerability hregular
  · exact corr.zero_consistency_vulnerability_implies_graph_strategyproof

/-- Deprecated compatibility alias for
`graph_strategyproof_iff_zero_consistency_vulnerability`. -/
theorem graph_strategyproof_iff_spectral_strategyproof
    {graph : GovernanceGraph} (corr : GraphSpectralCorrespondence graph)
    (hregular : corr.game.BestResponseDecomposedRegularity) :
    GraphStrategyproofPredicate graph ↔
      corr.SpectralStrategyproofPredicate :=
  corr.graph_strategyproof_iff_zero_consistency_vulnerability hregular

end GraphSpectralCorrespondence

/-! ## Strategyproof fixture: empty graph against a zero spectral signal -/

/-- Behavioral fixture with no agents. It has no profitable deviations by
construction and therefore is strategyproof. -/
def noAgentGame : BehavioralGovernanceGame where
  Agents := Empty
  State := Unit
  Action := fun agent => Empty.elim agent
  Utility := fun agent _state _profile => Empty.elim agent
  Transition := fun state _profile => state
  Observation := fun agent _state => Empty.elim agent
  GovernanceDecision := fun _state _profile agent => Empty.elim agent

lemma noAgentGame_strategyproof : noAgentGame.GameStrategyproof := by
  intro κ _hκ
  rintro ⟨dev, _⟩
  exact Empty.elim dev.agent

lemma noAgentGame_no_profitable_deviation {κ : ℚ}
    (dev : noAgentGame.ProfitableDeviation κ) : False :=
  Empty.elim dev.agent

lemma emptyGovernanceGraph_strategyproof :
    GraphStrategyproofness ([] : GovernanceGraph) := by
  intro claims k s_r hs_r hmem hdistinct hpermit
  simp [graphDecide]

/-- The no-agent game embeds into the zero-signal triangle. The reverse
spectral-vulnerability fields are nontrivial: they use the concrete theorem
that the zero signal has `cv = 0`, not definitional equality of embeddings. -/
def noAgentZeroSpectralEmbedding :
    SpectralBehavioralEmbedding uniTriGraph zeroSig3 noAgentGame where
  graph_decision_matches_game := by
    intro κ dev _hflip
    exact False.elim (noAgentGame_no_profitable_deviation dev)
  perturbation_budget_reflects_best_response_gain := by
    intro κ dev
    exact False.elim (noAgentGame_no_profitable_deviation dev)
  spectral_vulnerability_exposes_profitable_deviation := by
    intro _hregular γ hγ hviol
    have hle : γ ≤ (0 : ℚ) := by
      have hle' := (uniTriGraph.spViolation_iff_le_cv zeroSig3 γ).mp hviol
      rw [zeroConsistencyVulnerability_fixture_zeroSig3] at hle'
      exact hle'
    exact False.elim (not_le_of_gt hγ hle)
  spectral_threshold_violation_exposes_profitable_deviation := by
    intro _hregular δ κ hκ hδ hviol
    have hscale_pos : 0 < δ / κ := div_pos hδ hκ
    have hle : δ / κ ≤ (0 : ℚ) := by
      have hle' := (uniTriGraph.spViolation_iff_le_cv zeroSig3 (δ / κ)).mp hviol
      rw [zeroConsistencyVulnerability_fixture_zeroSig3] at hle'
      exact hle'
    exact False.elim (not_le_of_gt hscale_pos hle)

/-- Lineage package for the empty-graph/zero-signal fixture. -/
def noAgentZeroLineage : BehavioralLineage where
  n := 3
  nonzero := inferInstance
  G := uniTriGraph
  s := zeroSig3
  game := noAgentGame
  perturbationBudget := fun agent _state => Empty.elim agent
  utility_nonneg := fun agent _state _profile => Empty.elim agent
  utility_le_budget_at_state := fun agent _state _profile => Empty.elim agent
  budget_spViolation := fun agent _state => Empty.elim agent
  spectral_vulnerability_exposes_deviation := by
    intro γ hγ hviol
    have hle : γ ≤ (0 : ℚ) := by
      have hle' := (uniTriGraph.spViolation_iff_le_cv zeroSig3 γ).mp hviol
      rw [zeroConsistencyVulnerability_fixture_zeroSig3] at hle'
      exact hle'
    exact False.elim (not_le_of_gt hγ hle)
  spectral_threshold_exposes_deviation := by
    intro δ κ hκ hδ hviol
    have hscale_pos : 0 < δ / κ := div_pos hδ hκ
    have hle : δ / κ ≤ (0 : ℚ) := by
      have hle' := (uniTriGraph.spViolation_iff_le_cv zeroSig3 (δ / κ)).mp hviol
      rw [zeroConsistencyVulnerability_fixture_zeroSig3] at hle'
      exact hle'
    exact False.elim (not_le_of_gt hscale_pos hle)

/-- Concrete strategyproof graph/spectral correspondence. -/
def emptyGraphZeroSpectralCorrespondence :
    GraphSpectralCorrespondence ([] : GovernanceGraph) :=
  GraphSpectralCorrespondence.ofLineage ([] : GovernanceGraph) noAgentZeroLineage (by
    constructor
    · intro _hgraph
      exact noAgentGame_strategyproof
    · intro _hgame
      exact emptyGovernanceGraph_strategyproof)

theorem emptyGraphZeroSpectral_strategyproof_preserved :
    GraphSpectralCorrespondence.GraphStrategyproofPredicate ([] : GovernanceGraph) ↔
      emptyGraphZeroSpectralCorrespondence.ZeroConsistencyVulnerabilityPredicate := by
  constructor
  · intro _hgraph
    exact zeroConsistencyVulnerability_fixture_zeroSig3
  · exact emptyGraphZeroSpectralCorrespondence.zero_consistency_vulnerability_implies_graph_strategyproof

/-! ## Non-zero-CV fixture: threshold graph against positive CV -/

/-- A binary node that permits exactly claimants whose current strength is at
least one. Strengthening a below-threshold claim can flip denial into permit. -/
def thresholdAtOneNode : GovernanceNodeFn :=
  fun claims k =>
    if 1 ≤ lookupStrength k claims then BinaryDecision.Permit else BinaryDecision.Deny

/-- One-stage threshold graph used as the positive-CV graph fixture. -/
def thresholdAtOneGraph : GovernanceGraph :=
  [thresholdAtOneNode]

def thresholdWeakClaim : ClaimQ :=
  ⟨0, 1 / 2, by norm_num, []⟩

lemma thresholdAtOneGraph_weak_denied :
    graphDecide thresholdAtOneGraph [thresholdWeakClaim] 0 = BinaryDecision.Deny := by
  native_decide

lemma thresholdAtOneGraph_strengthened_permitted :
    graphDecide thresholdAtOneGraph
        (strengthenClaim 0 1 (by norm_num : (0 : ℚ) < 1) [thresholdWeakClaim])
        0 = BinaryDecision.Permit := by
  native_decide

lemma thresholdWeakClaim_inClaims :
    InClaims 0 [thresholdWeakClaim] := by
  unfold InClaims thresholdWeakClaim
  simp

lemma thresholdWeakClaim_distinct :
    ClaimsDistinct [thresholdWeakClaim] := by
  unfold ClaimsDistinct thresholdWeakClaim
  simp

lemma thresholdAtOneGraph_not_strategyproof :
    ¬ GraphStrategyproofness thresholdAtOneGraph := by
  intro hsp
  have hpermit := thresholdAtOneGraph_strengthened_permitted
  have hgraph :=
    hsp [thresholdWeakClaim] 0 1 (by norm_num)
      thresholdWeakClaim_inClaims thresholdWeakClaim_distinct hpermit
  rw [thresholdAtOneGraph_weak_denied] at hgraph
  cases hgraph

lemma thresholdAtOneGraph_graph_game_strategyproof :
    GraphStrategyproofness thresholdAtOneGraph ↔ binaryChoiceGame.GameStrategyproof := by
  constructor
  · intro hgraph
    exact False.elim (thresholdAtOneGraph_not_strategyproof hgraph)
  · intro hgame
    exact False.elim (binaryChoiceGame_not_strategyproof hgame)

/-- A threshold graph correspondence to the concrete nonzero-signal spectral
fixture. This witness uses the existing spectral behavioral embedding from the
spectral layer and a separately proved graph/game strategyproof equivalence. -/
def thresholdGraphPositiveSpectralCorrespondence :
    GraphSpectralCorrespondence thresholdAtOneGraph where
  n := 3
  nonzero := inferInstance
  spectralGraph := uniTriGraph
  signal := sig
  game := binaryChoiceGame
  embedding := binaryChoiceSpectralEmbedding
  graph_game_strategyproof := thresholdAtOneGraph_graph_game_strategyproof

theorem thresholdGraphPositiveSpectral_positive_cv_obstruction_preserved :
    ¬ GraphSpectralCorrespondence.GraphStrategyproofPredicate thresholdAtOneGraph ↔
      ¬ thresholdGraphPositiveSpectralCorrespondence.ZeroConsistencyVulnerabilityPredicate := by
  constructor
  · intro _hgraph
    exact positiveConsistencyVulnerability_fixture_sig
  · intro _hspectral
    exact thresholdAtOneGraph_not_strategyproof

/-- Deprecated compatibility alias for
`thresholdGraphPositiveSpectral_positive_cv_obstruction_preserved`. -/
theorem thresholdGraphPositiveSpectral_not_strategyproof_preserved :
    ¬ GraphSpectralCorrespondence.GraphStrategyproofPredicate thresholdAtOneGraph ↔
      ¬ thresholdGraphPositiveSpectralCorrespondence.SpectralStrategyproofPredicate :=
  thresholdGraphPositiveSpectral_positive_cv_obstruction_preserved

theorem thresholdGraphPositiveSpectral_cv_obstructs_zero_consistency_vulnerability :
    uniTriGraph.cv sig = 1 ∧
      thresholdGraphPositiveSpectralCorrespondence.ZeroConsistencyVulnerabilityPredicate ↔ False := by
  constructor
  · rintro ⟨hcv, hspectral⟩
    have hzero : uniTriGraph.cv sig = 0 := hspectral
    rw [hcv] at hzero
    norm_num at hzero
  · intro hfalse
    exact False.elim hfalse

/-- Deprecated compatibility alias for
`thresholdGraphPositiveSpectral_cv_obstructs_zero_consistency_vulnerability`. -/
theorem thresholdGraphPositiveSpectral_cv_obstructs_spectral_strategyproof :
    uniTriGraph.cv sig = 1 ∧
      thresholdGraphPositiveSpectralCorrespondence.SpectralStrategyproofPredicate ↔ False :=
  thresholdGraphPositiveSpectral_cv_obstructs_zero_consistency_vulnerability

end Legitimacy
