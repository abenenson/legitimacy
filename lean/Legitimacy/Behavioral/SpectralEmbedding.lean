/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Behavioral.GovernanceGame
import Legitimacy.Spectral.Dynamics.StackelbergConvergence

/-!
# Spectral-to-behavioral embeddings

The existing spectral layer measures exploitability by `spViolation` and `cv`.
This module adds the missing semantic layer: an embedding records that
profitable unilateral deviations in a deterministic rational governance game
are witnessed by concrete spectral perturbations at the embedded signal, and
that decomposed-regular spectral vulnerabilities are executable as behavioral
deviations.

`Legitimacy.Behavioral.StackelbergLineage` gives a concrete realization for
the Stackelberg node-removal perturbation lineage: the four embedding fields
are derived as theorems from bounded-amplitude actions whose budgets are
exactly the existing `govRemoved` spectral witnesses. This realizes the bridge
for that lineage class only; it does not make the purely spectral Stackelberg
limit theorem a general behavioral theorem.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

section SpectralBridge

variable {n : Nat}

/-- A signal-specific embedding of a behavioral game into a spectral
governance graph. The signal parameter is essential: utility gains are
represented by perturbations of a particular spectral state, not by every
possible signal on the graph. -/
structure SpectralBehavioralEmbedding
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ)
    (game : BehavioralGovernanceGame) where
  /-- Game-level decision flips are represented by spectral perturbation
  witnesses at the same utility-gain scale. -/
  graph_decision_matches_game :
    ∀ {κ : ℚ} (dev : game.ProfitableDeviation κ),
      game.GovernanceDecision dev.state dev.deviated dev.agent ≠
        game.GovernanceDecision dev.state dev.base dev.agent →
        G.spViolation s dev.gain
  /-- Every profitable best-response gain is reflected as a spectral
  perturbation budget. This is the main semantic bridge field. -/
  perturbation_budget_reflects_best_response_gain :
    ∀ {κ : ℚ} (dev : game.ProfitableDeviation κ), G.spViolation s dev.gain
  /-- Under decomposed regularity, every positive spectral vulnerability
  exposes a concrete profitable behavioral deviation. -/
  spectral_vulnerability_exposes_profitable_deviation :
    game.BestResponseDecomposedRegularity →
      ∀ {γ : ℚ}, 0 < γ → G.spViolation s γ →
        ∃ κ : ℚ, 0 < κ ∧ ∃ _dev : game.ProfitableDeviation κ, True
  /-- Under decomposed regularity, a spectral violation at the equilibrium
  threshold exposes a profitable deviation feasible at the same capability. -/
  spectral_threshold_violation_exposes_profitable_deviation :
    game.BestResponseDecomposedRegularity →
      ∀ {δ κ : ℚ}, 0 < κ → 0 < δ → G.spViolation s (δ / κ) →
        ∃ _dev : game.ProfitableDeviation κ, True

/-- A richer embedding keeps audit-oriented bounds that are redundant for the
core strategyproofness and persistence theorems. -/
structure ExtendedSpectralBehavioralEmbedding
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ)
    (game : BehavioralGovernanceGame) extends
      SpectralBehavioralEmbedding G s game where
  /-- Equivalently, the embedded graph-wide CV bounds the profitable
  behavioral gain. -/
  cv_bounds_profitable_deviation :
    ∀ {κ : ℚ} (dev : game.ProfitableDeviation κ), dev.gain ≤ G.cv s
  /-- The behavioral capability budget agrees with the action-budget side of
  the deviation record. This duplicates `ProfitableDeviation.gain_le_capability`
  and is retained only for extended audits. -/
  capability_scale_matches_action_budget :
    ∀ {κ : ℚ} (dev : game.ProfitableDeviation κ), dev.gain ≤ κ

namespace ExtendedSpectralBehavioralEmbedding

variable {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
variable {game : BehavioralGovernanceGame}

/-- Compatibility lift: every extended embedding is usable wherever the core
spectral-behavioral embedding is required. -/
def toCore (emb : ExtendedSpectralBehavioralEmbedding G s game) :
    SpectralBehavioralEmbedding G s game :=
  emb.toSpectralBehavioralEmbedding

end ExtendedSpectralBehavioralEmbedding

namespace SpectralBehavioralEmbedding

variable {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
variable {game : BehavioralGovernanceGame}

/-- Spectral violations are monotone in the requested perturbation scale. -/
lemma spViolation_of_le_gain
    {δ γ : ℚ} (hδ : δ ≤ γ) (hγ : G.spViolation s γ) :
    G.spViolation s δ := by
  exact (G.spViolation_iff_le_cv s δ).mpr
    (le_trans hδ ((G.spViolation_iff_le_cv s γ).mp hγ))

/-- If the embedded spectral state has no violation at scale `δ`, no
profitable behavioral deviation can have gain at least `δ`. -/
theorem no_spViolation_implies_no_profitable_deviation
    (emb : SpectralBehavioralEmbedding G s game) {δ κ : ℚ}
    (h : ¬ G.spViolation s δ) :
    ¬ ∃ dev : game.ProfitableDeviation κ, δ ≤ dev.gain := by
  rintro ⟨dev, hgain⟩
  exact h (spViolation_of_le_gain hgain
    (emb.perturbation_budget_reflects_best_response_gain dev))

/-- Zero consistency vulnerability has behavioral force under an embedding:
positive utility-improving unilateral deviations would imply a positive
spectral perturbation even though `cv = 0`. -/
theorem zero_consistency_vulnerability_implies_game_strategyproof
    (emb : SpectralBehavioralEmbedding G s game)
    (hsp : ZeroConsistencyVulnerability G s) :
    game.GameStrategyproof := by
  intro κ hκ
  rintro ⟨dev, _⟩
  have hviol : G.spViolation s dev.gain :=
    emb.perturbation_budget_reflects_best_response_gain dev
  have hle : dev.gain ≤ G.cv s :=
    (G.spViolation_iff_le_cv s dev.gain).mp hviol
  rw [hsp] at hle
  exact not_le_of_gt dev.gain_pos hle

/-- Deprecated compatibility alias for
`zero_consistency_vulnerability_implies_game_strategyproof`. -/
theorem spectral_strategyproof_implies_game_strategyproof
    (emb : SpectralBehavioralEmbedding G s game)
    (hsp : SpectralStrategyproof G s) :
    game.GameStrategyproof :=
  zero_consistency_vulnerability_implies_game_strategyproof emb hsp

/-- Behavioral strategyproofness forces zero consistency vulnerability once the
embedding can execute decomposed-regular spectral vulnerabilities as concrete
game deviations. -/
theorem game_strategyproof_implies_zero_consistency_vulnerability
    (emb : SpectralBehavioralEmbedding G s game)
    (hregular : game.BestResponseDecomposedRegularity)
    (hgsp : game.GameStrategyproof) :
    ZeroConsistencyVulnerability G s := by
  by_contra hsp
  have hcv_ne : G.cv s ≠ 0 := by
    simpa [ZeroConsistencyVulnerability] using hsp
  have hcv_pos : 0 < G.cv s :=
    lt_of_le_of_ne (G.cv_nonneg s) (Ne.symm hcv_ne)
  have hviol : G.spViolation s (G.cv s) :=
    (G.spViolation_iff_le_cv s (G.cv s)).mpr le_rfl
  obtain ⟨κ, hκ, dev, hdev⟩ :=
    emb.spectral_vulnerability_exposes_profitable_deviation
      hregular hcv_pos hviol
  exact hgsp κ hκ ⟨dev, hdev⟩

/-- Deprecated compatibility alias for
`game_strategyproof_implies_zero_consistency_vulnerability`. -/
theorem game_strategyproof_implies_spectral_strategyproof
    (emb : SpectralBehavioralEmbedding G s game)
    (hregular : game.BestResponseDecomposedRegularity)
    (hgsp : game.GameStrategyproof) :
    SpectralStrategyproof G s :=
  game_strategyproof_implies_zero_consistency_vulnerability emb hregular hgsp

/-- Spectral and behavioral strategyproofness coincide for decomposed-regular
games with a two-way spectral-behavioral embedding. -/
theorem zero_consistency_vulnerability_iff_game_strategyproof
    (emb : SpectralBehavioralEmbedding G s game)
    (hregular : game.BestResponseDecomposedRegularity) :
    ZeroConsistencyVulnerability G s ↔ game.GameStrategyproof := by
  constructor
  · exact zero_consistency_vulnerability_implies_game_strategyproof emb
  · exact game_strategyproof_implies_zero_consistency_vulnerability emb hregular

/-- Deprecated compatibility alias for
`zero_consistency_vulnerability_iff_game_strategyproof`. -/
theorem spectral_strategyproof_iff_game_strategyproof
    (emb : SpectralBehavioralEmbedding G s game)
    (hregular : game.BestResponseDecomposedRegularity) :
    SpectralStrategyproof G s ↔ game.GameStrategyproof :=
  zero_consistency_vulnerability_iff_game_strategyproof emb hregular

/-- A fixed-scale one-way equilibrium correspondence. Spectral stability
forbids threshold-scale perturbations. The decomposed best-response hypothesis
separates the two load-bearing behavioral steps: `lowerBound` relates the
explicit gain floor to `δ / κ`, and `existence` constructs a profitable
deviation that reaches that floor. -/
theorem spectral_stable_equilibrium_implies_behavioral_persistence_at_scale
    (emb : SpectralBehavioralEmbedding G s game)
    (hregular : game.BestResponseAtScaleRegularity)
    {δ κ : ℚ} (h : SpectralStableEquilibrium G s δ κ) :
    game.BehavioralPersistentEquilibrium κ δ := by
  rcases h with ⟨hκ, hno⟩
  have hδ : 0 < δ := by
    by_contra hnot
    have hδ_nonpos : δ ≤ 0 := le_of_not_gt hnot
    have hscale_nonpos : δ / κ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ_nonpos hκ.le
    have hscale_le_cv : δ / κ ≤ G.cv s := le_trans hscale_nonpos (G.cv_nonneg s)
    exact hno ((G.spViolation_iff_le_cv s (δ / κ)).mpr hscale_le_cv)
  rcases hregular with ⟨regular⟩
  refine ⟨hκ, hδ, ⟨regular⟩, ?_⟩
  intro hdev
  obtain ⟨dev, hfloor_gain⟩ := regular.existence hκ hδ hdev
  have hthreshold_floor : δ / κ ≤ regular.gainFloor κ δ :=
    regular.lowerBound hκ hδ
  have hthreshold_gain : δ / κ ≤ dev.gain :=
    le_trans hthreshold_floor hfloor_gain
  exact hno (spViolation_of_le_gain hthreshold_gain
    (emb.perturbation_budget_reflects_best_response_gain dev))

/-- Across capability floors, arbitrarily large spectral stable equilibria
induce behavioral persistence at arbitrarily large capabilities. The
capability-monotone decomposition is the stronger regularity package used for
varying-capability persistence. -/
theorem spectral_stable_equilibrium_implies_behavioral_persistence_across_capabilities
    (emb : SpectralBehavioralEmbedding G s game)
    (hregular : game.BestResponseDecomposedRegularity)
    {δ : ℚ} (h : HasArbitrarilyLargeStableEquilibria G s δ) :
    game.BehavioralUnboundedPersistence δ := by
  intro κ₀ hκ₀
  obtain ⟨κ, hκ_ge, hstable⟩ := h κ₀ hκ₀
  let hAtScale := game.bestResponseAtScaleRegularity_of_decomposed hregular
  exact ⟨κ, hκ_ge,
    spectral_stable_equilibrium_implies_behavioral_persistence_at_scale
      emb hAtScale hstable⟩

/-- Behavioral persistence rules out the normalized spectral perturbation
threshold through the reverse direction of the embedding. -/
theorem behavioral_persistence_implies_spectral_stable_equilibrium
    (emb : SpectralBehavioralEmbedding G s game)
    (hregular : game.BestResponseDecomposedRegularity)
    {δ κ : ℚ} (h : game.BehavioralPersistentEquilibrium κ δ) :
    SpectralStableEquilibrium G s δ κ := by
  rcases h with ⟨hκ, hδ, _hpersistent_regular, hnash⟩
  refine ⟨hκ, ?_⟩
  intro hviol
  obtain ⟨dev, hdev⟩ :=
    emb.spectral_threshold_violation_exposes_profitable_deviation
      hregular hκ hδ hviol
  exact hnash ⟨dev, hdev⟩

/-- Stable spectral equilibrium is equivalent to behavioral persistence under
a decomposed-regular two-way embedding. -/
theorem spectral_stable_equilibrium_iff_behavioral_persistence
    (emb : SpectralBehavioralEmbedding G s game)
    (hregular : game.BestResponseDecomposedRegularity)
    (κ δ : ℚ) :
    SpectralStableEquilibrium G s δ κ ↔
      game.BehavioralPersistentEquilibrium κ δ := by
  constructor
  · exact spectral_stable_equilibrium_implies_behavioral_persistence_at_scale
      emb (game.bestResponseAtScaleRegularity_of_decomposed hregular)
  · exact behavioral_persistence_implies_spectral_stable_equilibrium
      emb hregular

end SpectralBehavioralEmbedding

end SpectralBridge

/-! ## Phase-1 countermodels -/

/-- A one-agent executable behavioral game. Choosing `true` yields utility
`1/2`; choosing `false` yields utility `0`. -/
def binaryChoiceGame : BehavioralGovernanceGame where
  Agents := Unit
  State := Unit
  Action := fun _ => Bool
  Utility := fun agent _state profile => if profile agent then 1 / 2 else 0
  Transition := fun state _ => state
  Observation := fun _ _ => ObservationType.Public
  GovernanceDecision := fun _state profile agent =>
    if profile agent then BinaryDecision.Permit else BinaryDecision.Deny

def binaryStayProfile : ActionProfile binaryChoiceGame.Action :=
  fun _ => false

def binaryDeviateProfile : ActionProfile binaryChoiceGame.Action :=
  fun _ => true

/-- The executable profitable deviation in `binaryChoiceGame`. -/
def binaryChoiceProfitableDeviation :
    binaryChoiceGame.ProfitableDeviation 1 where
  agent := ()
  state := ()
  base := binaryStayProfile
  deviated := binaryDeviateProfile
  unilateral := by
    intro j hj
    cases j
    exact False.elim (hj rfl)
  positive_gain := by native_decide
  capability_feasible := by native_decide

lemma binaryChoiceGame_not_strategyproof :
    ¬ binaryChoiceGame.GameStrategyproof :=
  binaryChoiceGame.not_gameStrategyproof_of_profitable_deviation
    (κ := 1) (by norm_num) binaryChoiceProfitableDeviation

lemma binaryChoiceGame_profitable_gain_le_one
    {κ : ℚ} (dev : binaryChoiceGame.ProfitableDeviation κ) :
    dev.gain ≤ 1 := by
  unfold BehavioralGovernanceGame.ProfitableDeviation.gain
  unfold BehavioralGovernanceGame.utilityGain
  dsimp [binaryChoiceGame]
  cases hbase : dev.base dev.agent <;>
    cases hdev : dev.deviated dev.agent <;>
    simp <;>
    norm_num

lemma binaryChoiceGame_profitable_gain_eq_half
    {κ : ℚ} (dev : binaryChoiceGame.ProfitableDeviation κ) :
    dev.gain = 1 / 2 := by
  have hpos := dev.positive_gain
  unfold BehavioralGovernanceGame.utilityGain at hpos
  unfold BehavioralGovernanceGame.ProfitableDeviation.gain
  unfold BehavioralGovernanceGame.utilityGain
  dsimp [binaryChoiceGame] at hpos ⊢
  cases hbase : dev.base dev.agent
  · cases hdev : dev.deviated dev.agent
    · exfalso
      simp [hbase, hdev] at hpos
    · norm_num
  · cases hdev : dev.deviated dev.agent
    · exfalso
      have hnot : ¬ ((2 : ℚ) < 0) := by norm_num
      exact hnot (by simpa [hbase, hdev] using hpos)
    · exfalso
      simp [hbase, hdev] at hpos

/-- The binary choice game embeds into the uniform triangle at the nonzero
signal `sig`: its only positive gain, `1/2`, is below `cv = 1`. -/
def binaryChoiceSpectralEmbedding :
    SpectralBehavioralEmbedding uniTriGraph sig binaryChoiceGame where
  graph_decision_matches_game := by
    intro κ dev _
    exact (uniTriGraph.spViolation_iff_le_cv sig dev.gain).mpr (by
      rw [concrete_cv_values.1]
      exact binaryChoiceGame_profitable_gain_le_one dev)
  perturbation_budget_reflects_best_response_gain := by
    intro κ dev
    exact (uniTriGraph.spViolation_iff_le_cv sig dev.gain).mpr (by
      rw [concrete_cv_values.1]
      exact binaryChoiceGame_profitable_gain_le_one dev)
  spectral_vulnerability_exposes_profitable_deviation := by
    intro hregular
    exact False.elim (by
      have hbr := binaryChoiceGame.bestResponseRegularity_of_monotone_decomposed
        hregular
      obtain ⟨dev, hgain⟩ :=
        hbr (κ := 1) (δ := 2) (by norm_num) (by norm_num)
          ⟨binaryChoiceProfitableDeviation, trivial⟩
      rw [binaryChoiceGame_profitable_gain_eq_half dev] at hgain
      norm_num at hgain)
  spectral_threshold_violation_exposes_profitable_deviation := by
    intro hregular
    exact False.elim (by
      have hbr := binaryChoiceGame.bestResponseRegularity_of_monotone_decomposed
        hregular
      obtain ⟨dev, hgain⟩ :=
        hbr (κ := 1) (δ := 2) (by norm_num) (by norm_num)
          ⟨binaryChoiceProfitableDeviation, trivial⟩
      rw [binaryChoiceGame_profitable_gain_eq_half dev] at hgain
      norm_num at hgain)

/-- The extended fixture retains the redundant CV and capability bounds for
audit surfaces that want them explicitly. -/
def binaryChoiceExtendedSpectralEmbedding :
    ExtendedSpectralBehavioralEmbedding uniTriGraph sig binaryChoiceGame where
  toSpectralBehavioralEmbedding := binaryChoiceSpectralEmbedding
  cv_bounds_profitable_deviation := by
    intro κ dev
    rw [concrete_cv_values.1]
    exact binaryChoiceGame_profitable_gain_le_one dev
  capability_scale_matches_action_budget := by
    intro κ dev
    exact dev.gain_le_capability

lemma binaryChoiceExtendedSpectralEmbedding_toCore :
    binaryChoiceExtendedSpectralEmbedding.toCore =
      binaryChoiceSpectralEmbedding :=
  rfl

/-- Without best-response regularity, spectral stability alone does not imply
behavioral stability: the profitable gain `1/2` is below the spectral tolerance
scale `2`, so `cv` misses the actual deviation. -/
theorem behavioral_embedding_fails_without_bestResponseRegularity :
    SpectralStableEquilibrium uniTriGraph sig 2 1 ∧
      ¬ binaryChoiceGame.NashStableAtCapability 1 := by
  constructor
  · rw [spectralStableEquilibrium_iff]
    rw [concrete_cv_values.1]
    norm_num
  · exact fun hstable => hstable ⟨binaryChoiceProfitableDeviation, trivial⟩

/-- The concrete counterexample is non-regular at `δ = 2`, `κ = 1`: the only
profitable gain is `1/2`, below the threshold `δ / κ = 2`. -/
theorem binaryChoiceGame_not_bestResponseRegularity :
    ¬ binaryChoiceGame.BestResponseRegularity := by
  intro hregular
  obtain ⟨dev, hgain⟩ :=
    hregular (κ := 1) (δ := 2) (by norm_num) (by norm_num)
      ⟨binaryChoiceProfitableDeviation, trivial⟩
  rw [binaryChoiceGame_profitable_gain_eq_half dev] at hgain
  norm_num at hgain

/-- The same counterexample rejects the decomposed replacement: any valid
decomposition would imply the old threshold regularity, but the only profitable
gain is too small at `δ = 2`, `κ = 1`. -/
theorem binaryChoiceGame_not_bestResponseDecomposedRegularity :
    ¬ binaryChoiceGame.BestResponseDecomposedRegularity := by
  intro hregular
  exact binaryChoiceGame_not_bestResponseRegularity
    (binaryChoiceGame.bestResponseRegularity_of_monotone_decomposed hregular)

/-- At the same capability/tolerance pair, the decomposed regularity gap is
visible as non-persistence. -/
theorem binaryChoiceGame_not_behavioralPersistentEquilibrium_at_gap :
    ¬ binaryChoiceGame.BehavioralPersistentEquilibrium 1 2 := by
  intro hpersistent
  exact hpersistent.2.2.2 ⟨binaryChoiceProfitableDeviation, trivial⟩

/-- Spectral stability plus an embedding still does not produce behavioral
persistence when the decomposed best-response regularity certificate is absent. -/
theorem behavioral_embedding_fails_without_decomposed_regularity :
    SpectralStableEquilibrium uniTriGraph sig 2 1 ∧
      ¬ binaryChoiceGame.BehavioralPersistentEquilibrium 1 2 :=
  ⟨behavioral_embedding_fails_without_bestResponseRegularity.1,
    binaryChoiceGame_not_behavioralPersistentEquilibrium_at_gap⟩

/-- `cv` is not the right quantity for non-regular best-response dynamics:
the spectral equilibrium at threshold `2` coexists with a concrete profitable
deviation of gain `1/2`. -/
theorem cv_not_right_quantity_for_nonregular_best_response :
    uniTriGraph.cv sig = 1 ∧
      SpectralStableEquilibrium uniTriGraph sig 2 1 ∧
      ∃ dev : binaryChoiceGame.ProfitableDeviation 1, dev.gain = 1 / 2 := by
  refine ⟨concrete_cv_values.1, ?_, ?_⟩
  · exact behavioral_embedding_fails_without_bestResponseRegularity.1
  · exact ⟨binaryChoiceProfitableDeviation, by
      native_decide⟩

end Legitimacy
