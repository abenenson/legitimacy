/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Kernel.Observable

/-!
# Legitimacy.Results.Amplification

This module formalizes a minimal model of scalable oversight for
`GOVERNANCE-OBSERVABLE`.

The model makes the budget constraint load-bearing:

- governance queries carry a natural-number difficulty,
- directly evaluating a query consumes exactly its difficulty in steps,
- a bounded overseer can directly evaluate only queries whose difficulty fits
  within budget,
- amplification decomposes a hard query into easier sub-queries together with a
  Boolean combiner, and
- adequacy means both that every sub-query is directly evaluable within budget
  and that combining their observable answers recovers the correct governance
  answer.

This captures the core oversight intuition behind amplification, debate, and
related bounded-overseer schemes without collapsing the budget witness to a
tautology.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A capability gap is the amount by which a query exceeds an overseer's
budget. -/
abbrev CapabilityGap := Nat

/-- A difficulty assignment for governance queries. -/
abbrev QueryDifficulty := GovernanceQuery → Nat

/-- A bounded overseer can spend at most `budget` evaluation steps. -/
structure BoundedOverseer where
  /-- The overseer's computational budget. -/
  budget : Nat

/-- A query is directly answerable by an overseer exactly when its difficulty is
within the overseer's budget. -/
def BoundedOverseer.CanAnswer (overseer : BoundedOverseer)
    (difficulty : QueryDifficulty) (q : GovernanceQuery) : Prop :=
  difficulty q ≤ overseer.budget

/-- A direct evaluation witness records that answering `q` consumes exactly its
difficulty in steps and stays within the overseer's budget. -/
structure DirectEvaluation (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer) (q : GovernanceQuery) where
  /-- The concrete number of steps used by the evaluation. -/
  steps : Nat
  /-- Query evaluation cost is proportional to query difficulty. -/
  steps_eq : steps = difficulty q
  /-- The evaluation fits within the overseer's budget. -/
  within_budget : steps ≤ overseer.budget

/-- A query is directly evaluable when there exists a budget-valid evaluation
witness for it. -/
def DirectlyEvaluable (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer) (q : GovernanceQuery) : Prop :=
  Nonempty (DirectEvaluation difficulty overseer q)

/-- Direct evaluability is equivalent to the raw budget bound on query
difficulty. -/
@[simp] theorem directlyEvaluable_iff_canAnswer
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer) (q : GovernanceQuery) :
    DirectlyEvaluable difficulty overseer q ↔ overseer.CanAnswer difficulty q := by
  constructor
  · rintro ⟨hEval⟩
    rcases hEval with ⟨steps, hsteps, hwithin⟩
    simpa [BoundedOverseer.CanAnswer, hsteps] using hwithin
  · intro hCanAnswer
    exact ⟨⟨difficulty q, rfl, hCanAnswer⟩⟩

/-- If a query is strictly harder than the overseer's budget, then it cannot be
directly evaluated. -/
lemma not_directly_evaluable_of_budget_lt_difficulty
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer) (q : GovernanceQuery)
    (hhard : overseer.budget < difficulty q) :
    ¬ DirectlyEvaluable difficulty overseer q := by
  intro hEval
  have hCanAnswer :
      overseer.CanAnswer difficulty q :=
    (directlyEvaluable_iff_canAnswer difficulty overseer q).mp hEval
  exact Nat.not_le_of_lt hhard hCanAnswer

/-- The direct capability gap between a query and a bounded overseer. -/
def directCapabilityGap (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer) (q : GovernanceQuery) : CapabilityGap :=
  difficulty q - overseer.budget

/-- An amplification protocol decomposes a governance query into sub-queries and
combines their Boolean answers into a final judgment. -/
structure AmplificationProtocol where
  /-- Decompose a governance query into easier governance sub-queries. -/
  decompose : GovernanceQuery → List GovernanceQuery
  /-- Combine the sub-query answers into an answer for the original query. -/
  combine : GovernanceQuery → List Bool → Bool

/-- Evaluate a query by answering each amplified sub-query and applying the
protocol combiner. -/
def amplifiedAnswer {S : Type}
    (answer : GovernanceQuery → S → Bool)
    (protocol : AmplificationProtocol) (s : S) (q : GovernanceQuery) : Bool :=
  protocol.combine q ((protocol.decompose q).map (fun sub => answer sub s))

/-- The effective difficulty of an amplified query is the largest difficulty
among its sub-queries. -/
def amplifiedDifficulty (difficulty : QueryDifficulty)
    (protocol : AmplificationProtocol) (q : GovernanceQuery) : Nat :=
  ((protocol.decompose q).map difficulty).foldr Nat.max 0

/-- The capability gap after amplification is the residual gap between the
hardest sub-query and the overseer's budget. -/
def amplifiedCapabilityGap (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol) (q : GovernanceQuery) : CapabilityGap :=
  amplifiedDifficulty difficulty protocol q - overseer.budget

/-- A query is within the amplified budget when every sub-query produced by the
protocol is within the overseer's budget. -/
def QueryWithinAmplifiedBudget (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol) (q : GovernanceQuery) : Prop :=
  ∀ sub ∈ protocol.decompose q, difficulty sub ≤ overseer.budget

/-- An amplified query is evaluable when every generated sub-query admits a
direct budget-valid evaluation witness. -/
def AmplifiedEvaluable (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol) (q : GovernanceQuery) : Prop :=
  ∀ sub ∈ protocol.decompose q, DirectlyEvaluable difficulty overseer sub

/-- A decomposition stays within budget exactly when all of its sub-queries are
directly evaluable. -/
@[simp] theorem amplifiedEvaluable_iff_within_budget
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol) (q : GovernanceQuery) :
    AmplifiedEvaluable difficulty overseer protocol q ↔
      QueryWithinAmplifiedBudget difficulty overseer protocol q := by
  constructor
  · intro hEval sub hsub
    exact (directlyEvaluable_iff_canAnswer difficulty overseer sub).mp (hEval sub hsub)
  · intro hBudget sub hsub
    exact (directlyEvaluable_iff_canAnswer difficulty overseer sub).mpr (hBudget sub hsub)

/-- An amplification protocol is correct for an answer function when its
combiner reconstructs the original answer from the answers to the sub-queries.
-/
def AmplificationCorrect {S : Type}
    (answer : GovernanceQuery → S → Bool)
    (protocol : AmplificationProtocol) : Prop :=
  ∀ s q, amplifiedAnswer answer protocol s q = answer q s

/-- Oversight is adequate when every query whose decomposition stays within
budget can be evaluated by directly answering the sub-queries within budget and
the amplified observable answer recovers the original governance answer. -/
def OversightAdequate {S S' : Type}
    (answer : GovernanceQuery → S → Bool)
    (observeAnswer : GovernanceQuery → S' → Bool)
    (observe : ObservationFunction S S')
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol) : Prop :=
  ∀ s q, QueryWithinAmplifiedBudget difficulty overseer protocol q →
    AmplifiedEvaluable difficulty overseer protocol q ∧
      amplifiedAnswer observeAnswer protocol (observe s) q = answer q s

/-- Adequate oversight packages the direct-evaluability witnesses for every
budget-respecting decomposition. -/
lemma OversightAdequate.amplifiedEvaluable
    {S S' : Type}
    {answer : GovernanceQuery → S → Bool}
    {observeAnswer : GovernanceQuery → S' → Bool}
    {observe : ObservationFunction S S'}
    {difficulty : QueryDifficulty}
    {overseer : BoundedOverseer}
    {protocol : AmplificationProtocol}
    (hadequate :
      OversightAdequate answer observeAnswer observe difficulty overseer protocol)
    (s : S) (q : GovernanceQuery)
    (hbudget : QueryWithinAmplifiedBudget difficulty overseer protocol q) :
    AmplifiedEvaluable difficulty overseer protocol q :=
  (hadequate s q hbudget).1

/-- Adequate oversight reconstructs the original governance answer from the
observable amplified answer on every budget-respecting decomposition. -/
lemma OversightAdequate.correct
    {S S' : Type}
    {answer : GovernanceQuery → S → Bool}
    {observeAnswer : GovernanceQuery → S' → Bool}
    {observe : ObservationFunction S S'}
    {difficulty : QueryDifficulty}
    {overseer : BoundedOverseer}
    {protocol : AmplificationProtocol}
    (hadequate :
      OversightAdequate answer observeAnswer observe difficulty overseer protocol)
    (s : S) (q : GovernanceQuery)
    (hbudget : QueryWithinAmplifiedBudget difficulty overseer protocol q) :
    amplifiedAnswer observeAnswer protocol (observe s) q = answer q s :=
  (hadequate s q hbudget).2

/-- Compose two rounds of amplification by using `inner` to answer each
sub-query produced by `outer`. -/
def composedAmplifiedAnswer {S : Type}
    (outer inner : AmplificationProtocol)
    (answer : GovernanceQuery → S → Bool)
    (s : S) (q : GovernanceQuery) : Bool :=
  outer.combine q
    ((outer.decompose q).map (fun sub => amplifiedAnswer answer inner s sub))

/-- An adversarial-refinement semantics for debate records the calibration
error of each individual debater together with the refined amplified error
sequence. -/
structure DebateRefinement where
  leftError : GovernanceQuery → ℚ
  rightError : GovernanceQuery → ℚ
  amplifiedError : GovernanceQuery → Nat → ℚ
  soundness :
    ∀ (q : GovernanceQuery) (round : Nat),
      amplifiedError q round ≤ leftError q ∧
        amplifiedError q round ≤ rightError q
  convergence :
    ∀ (q : GovernanceQuery) (ε : ℚ), 0 < ε →
      ∃ N : Nat, ∀ round ≥ N, |amplifiedError q round| ≤ ε
  strictImprovement :
    ∃ (q : GovernanceQuery) (round : Nat),
      amplifiedError q round < leftError q ∧
        amplifiedError q round < rightError q

/-- A debate protocol asks two competing provers for governance-relevant
sub-queries and lets a bounded judge combine their answers. -/
structure DebateProtocol where
  /-- The bounded judge overseeing the debate. -/
  judge : BoundedOverseer
  /-- The first prover's sub-query. -/
  proverLeft : GovernanceQuery → GovernanceQuery
  /-- The second prover's sub-query. -/
  proverRight : GovernanceQuery → GovernanceQuery
  /-- The bounded judge's decision rule over the two prover answers. -/
  judgeVerdict : GovernanceQuery → Bool → Bool → Bool
  /-- Adversarial refinement semantics for the debate's amplified answer. -/
  refinement : DebateRefinement

/-- A debate counts as a genuine amplification mechanism only when its
adversarial-refinement semantics proves calibration soundness, convergence, and
strict improvement over either individual debater. -/
structure Amplification (debate : DebateProtocol) : Prop where
  soundness :
    ∀ (q : GovernanceQuery) (round : Nat),
      debate.refinement.amplifiedError q round ≤ debate.refinement.leftError q ∧
        debate.refinement.amplifiedError q round ≤ debate.refinement.rightError q
  convergence :
    ∀ (q : GovernanceQuery) (ε : ℚ), 0 < ε →
      ∃ N : Nat, ∀ round ≥ N,
        |debate.refinement.amplifiedError q round| ≤ ε
  strictImprovement :
    ∃ (q : GovernanceQuery) (round : Nat),
      debate.refinement.amplifiedError q round < debate.refinement.leftError q ∧
        debate.refinement.amplifiedError q round < debate.refinement.rightError q

/-- A debate protocol is an amplification protocol with exactly two
sub-queries. -/
def DebateProtocol.toAmplificationProtocol
    (debate : DebateProtocol) : AmplificationProtocol where
  decompose := fun q => [debate.proverLeft q, debate.proverRight q]
  combine := fun q answers =>
    match answers with
    | left :: right :: _ => debate.judgeVerdict q left right
    | [left] => debate.judgeVerdict q left left
    | [] => debate.judgeVerdict q false false

/-- A debate protocol with adversarial-refinement witnesses is a genuine
amplification mechanism: every refinement round is at least as calibrated as
either debater, the refinement converges to ground truth, and some round
strictly improves on both individual debaters. -/
theorem debate_is_amplification (debate : DebateProtocol) :
    Amplification debate where
  soundness := debate.refinement.soundness
  convergence := debate.refinement.convergence
  strictImprovement := debate.refinement.strictImprovement

/-- A concrete hard governance query used in the unamplified failure witness. -/
private def hardQuery : GovernanceQuery :=
  GovernanceQuery.ClaimPermitted 0

/-- A difficulty assignment where `hardQuery` exceeds budget `B` by exactly one
step. -/
private def hardDifficulty (B : Nat) : QueryDifficulty :=
  fun q => if q = hardQuery then B + 1 else 0

/-- If every element of a finite list is bounded by `budget`, then the fold by
`Nat.max` is also bounded by `budget`. -/
private theorem foldr_max_le_of_forall_le {xs : List Nat} {budget : Nat}
    (hxs : ∀ x ∈ xs, x ≤ budget) :
    xs.foldr Nat.max 0 ≤ budget := by
  induction xs with
  | nil =>
      exact Nat.zero_le budget
  | cons x xs ih =>
      have hx : x ≤ budget := hxs x (List.Mem.head _)
      have htail : ∀ y ∈ xs, y ≤ budget := by
        intro y hy
        exact hxs y (List.Mem.tail _ hy)
      simpa using (max_le_iff.mpr ⟨hx, ih htail⟩)

/-- If every amplified sub-query is within budget, then the amplified query has
no residual difficulty beyond that budget. -/
lemma amplifiedDifficulty_le_budget
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol)
    (q : GovernanceQuery)
    (hbudget : QueryWithinAmplifiedBudget difficulty overseer protocol q) :
    amplifiedDifficulty difficulty protocol q ≤ overseer.budget := by
  unfold amplifiedDifficulty
  apply foldr_max_le_of_forall_le
  intro n hn
  rcases List.mem_map.mp hn with ⟨sub, hsub, rfl⟩
  exact hbudget sub hsub

/-- If an amplified decomposition stays within budget, its residual capability
gap is zero. -/
lemma amplifiedCapabilityGap_eq_zero_of_within_budget
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol)
    (q : GovernanceQuery)
    (hbudget : QueryWithinAmplifiedBudget difficulty overseer protocol q) :
    amplifiedCapabilityGap difficulty overseer protocol q = 0 := by
  exact Nat.sub_eq_zero_of_le
    (amplifiedDifficulty_le_budget difficulty overseer protocol q hbudget)

/-- A budget-respecting amplification protocol never has larger residual gap
than the original direct-evaluation gap. -/
lemma amplifiedCapabilityGap_le_directCapabilityGap_of_within_budget
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol)
    (q : GovernanceQuery)
    (hbudget : QueryWithinAmplifiedBudget difficulty overseer protocol q) :
    amplifiedCapabilityGap difficulty overseer protocol q ≤
      directCapabilityGap difficulty overseer q := by
  rw [amplifiedCapabilityGap_eq_zero_of_within_budget
    difficulty overseer protocol q hbudget]
  exact Nat.zero_le _

/-- Without amplification, any query whose difficulty exceeds the budget is
impossible to evaluate directly. -/
lemma hard_query_cannot_be_directly_evaluated
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer) (q : GovernanceQuery)
    (hhard : overseer.budget < difficulty q) :
    ¬ DirectlyEvaluable difficulty overseer q :=
  not_directly_evaluable_of_budget_lt_difficulty difficulty overseer q hhard

/-- Without amplification, there are always governance queries that a bounded
overseer cannot directly evaluate: take a query whose difficulty is exactly one
larger than the overseer's budget. -/
theorem unamplified_oversight_fails (B : Nat) :
    ∃ overseer : BoundedOverseer, ∃ difficulty : QueryDifficulty,
      ∃ q : GovernanceQuery,
        directCapabilityGap difficulty overseer q = 1 ∧
        ¬ DirectlyEvaluable difficulty overseer q := by
  refine ⟨⟨B⟩, hardDifficulty B, hardQuery, ?_, ?_⟩
  · simp [directCapabilityGap, hardDifficulty, hardQuery]
  · apply hard_query_cannot_be_directly_evaluated
    simp [hardDifficulty, hardQuery]

/-- A budget-respecting amplification protocol makes every produced sub-query
directly evaluable by the bounded overseer. -/
lemma amplification_makes_subqueries_evaluable
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol)
    (q : GovernanceQuery)
    (hbudget : QueryWithinAmplifiedBudget difficulty overseer protocol q) :
    AmplifiedEvaluable difficulty overseer protocol q :=
  (amplifiedEvaluable_iff_within_budget difficulty overseer protocol q).mpr hbudget

/-- A budget-respecting amplification protocol collapses the effective
capability gap to zero, and therefore never increases the original gap. -/
lemma amplification_reduces_effective_gap
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol)
    (q : GovernanceQuery)
    (hbudget : QueryWithinAmplifiedBudget difficulty overseer protocol q) :
    amplifiedCapabilityGap difficulty overseer protocol q = 0 ∧
      amplifiedCapabilityGap difficulty overseer protocol q ≤
        directCapabilityGap difficulty overseer q := by
  exact ⟨amplifiedCapabilityGap_eq_zero_of_within_budget
      difficulty overseer protocol q hbudget,
    amplifiedCapabilityGap_le_directCapabilityGap_of_within_budget
      difficulty overseer protocol q hbudget⟩

/-- If a query is too hard to evaluate directly but decomposes into
budget-sized pieces, then amplification supplies exactly the missing
evaluability witness. -/
lemma hard_query_requires_amplification
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol)
    (q : GovernanceQuery)
    (hhard : overseer.budget < difficulty q)
    (hbudget : QueryWithinAmplifiedBudget difficulty overseer protocol q) :
    ¬ DirectlyEvaluable difficulty overseer q ∧
      AmplifiedEvaluable difficulty overseer protocol q := by
  constructor
  · exact hard_query_cannot_be_directly_evaluated difficulty overseer q hhard
  · exact amplification_makes_subqueries_evaluable difficulty overseer protocol q hbudget

/-- Governance observability plus a correct amplification protocol yields
oversight adequacy for every query whose decomposition stays within budget. The
budget witness is load-bearing: it constructs the direct evaluation witnesses
for the sub-queries. -/
lemma observable_plus_amplification_adequate
    {S S' : Type}
    (answer : GovernanceQuery → S → Bool)
    (observeAnswer : GovernanceQuery → S' → Bool)
    (observe : ObservationFunction S S')
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol)
    (hobs : GovernanceObservable answer observeAnswer observe)
    (hcorrect : AmplificationCorrect observeAnswer protocol) :
    OversightAdequate answer observeAnswer observe difficulty overseer protocol := by
  intro s q hbudget
  constructor
  · exact amplification_makes_subqueries_evaluable difficulty overseer protocol q hbudget
  · calc
      amplifiedAnswer observeAnswer protocol (observe s) q
        = observeAnswer q (observe s) := hcorrect (observe s) q
      _ = answer q s := (hobs q s).symm

/-- In the intended regime, amplification evaluates a hard query by reducing it
to budget-sized observable sub-queries and then combining the results
correctly. -/
theorem hard_query_observable_via_amplification
    {S S' : Type}
    (answer : GovernanceQuery → S → Bool)
    (observeAnswer : GovernanceQuery → S' → Bool)
    (observe : ObservationFunction S S')
    (difficulty : QueryDifficulty)
    (overseer : BoundedOverseer)
    (protocol : AmplificationProtocol)
    (s : S) (q : GovernanceQuery)
    (hhard : overseer.budget < difficulty q)
    (hbudget : QueryWithinAmplifiedBudget difficulty overseer protocol q)
    (hobs : GovernanceObservable answer observeAnswer observe)
    (hcorrect : AmplificationCorrect observeAnswer protocol) :
    ¬ DirectlyEvaluable difficulty overseer q ∧
      AmplifiedEvaluable difficulty overseer protocol q ∧
      amplifiedAnswer observeAnswer protocol (observe s) q = answer q s := by
  have hAdequate :=
    observable_plus_amplification_adequate
      answer observeAnswer observe difficulty overseer protocol hobs hcorrect
  refine ⟨hard_query_cannot_be_directly_evaluated difficulty overseer q hhard, ?_, ?_⟩
  · exact hAdequate.amplifiedEvaluable s q hbudget
  · exact hAdequate.correct s q hbudget

/-- If an inner amplification layer is pointwise correct, then mapping it over
an outer decomposition is extensionally the same as mapping the base answer
function over that decomposition. -/
private lemma map_amplifiedAnswer_eq_map_answer_of_correct_inner
    {S : Type}
    (answer : GovernanceQuery → S → Bool)
    (outer inner : AmplificationProtocol)
    (s : S) (q : GovernanceQuery)
    (hinner : AmplificationCorrect answer inner) :
    (outer.decompose q).map (fun sub => amplifiedAnswer answer inner s sub) =
      (outer.decompose q).map (fun sub => answer sub s) := by
  simp [hinner s]

/-- Oversight adequacy composes: if an inner amplification layer correctly
answers every outer sub-query, and the outer layer correctly combines those
answers, then the two-layer composition is also correct. -/
lemma oversight_adequacy_composes
    {S : Type}
    (answer : GovernanceQuery → S → Bool)
    (outer inner : AmplificationProtocol)
    (houter : AmplificationCorrect answer outer)
    (hinner : AmplificationCorrect answer inner) :
    ∀ s q, composedAmplifiedAnswer outer inner answer s q = answer q s := by
  intro s q
  unfold composedAmplifiedAnswer
  rw [map_amplifiedAnswer_eq_map_answer_of_correct_inner
    answer outer inner s q hinner]
  simpa [amplifiedAnswer] using houter s q

end Legitimacy
