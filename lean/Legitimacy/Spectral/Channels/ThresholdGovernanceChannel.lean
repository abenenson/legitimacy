/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Capacity.CriticalCapability
import Mathlib.InformationTheory.Hamming
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
  Threshold governance channel capacity as a Shannon analog.

  Verdict: PARTIAL.

  The current spectral layer exposes deterministic perturbation magnitudes
  (`gov`, `govRemoved`, `cv`, `C_star`) but not an intrinsic decision-layer
  channel map, an information-rate notion, or the strict-concavity machinery
  needed to prove uniqueness of a capacity-achieving prior from the present
  `klDiv`-based mutual-information definition. This file records the
  unconditional failure on the toy `uniTriGraph` case, then adds the finite
  `RowSeparating` non-degeneracy hypothesis that rules out that counterexample.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

instance : MeasurableSpace BinaryDecision := ⊤

instance : MeasurableSingletonClass BinaryDecision := ⟨fun _ => trivial⟩

instance : Fintype BinaryDecision where
  elems := [BinaryDecision.Permit, BinaryDecision.Deny].toFinset
  complete := by
    intro d
    cases d <;> simp

/-- Finite discrete simplex specialization used for this probe. -/
abbrev Simplex (α : Type*) := PMF α

/-- Finite governance channels are Markov kernels from inputs to decisions. -/
structure GovernanceChannel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  kernel : Kernel α β
  isMarkov : IsMarkovKernel kernel

attribute [instance] GovernanceChannel.isMarkov

namespace GovernanceChannel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Output marginal induced by an input prior and a channel. -/
noncomputable def outputMeasure (p : Simplex α) (c : GovernanceChannel α β) :
    Measure β :=
  c.kernel ∘ₘ p.toMeasure

/-- Joint input-output law induced by an input prior and a channel. -/
noncomputable def jointMeasure (p : Simplex α) (c : GovernanceChannel α β) :
    Measure (α × β) :=
  p.toMeasure ⊗ₘ c.kernel

/-- Constant decision channel. -/
noncomputable def constant (d : β) : GovernanceChannel α β where
  kernel := Kernel.const α (Measure.dirac d)
  isMarkov := by infer_instance

/-- The finite output row of a governance channel, viewed as a `PMF`. -/
noncomputable def row [Countable β] [MeasurableSingletonClass β]
    (c : GovernanceChannel α β) (x : α) : PMF β :=
  (c.kernel x).toPMF

/-- Row-separating channels distinguish distinct inputs at the output law level. -/
def RowSeparating [Countable β] [MeasurableSingletonClass β]
    (c : GovernanceChannel α β) : Prop :=
  ∀ x₁ x₂ : α, x₁ ≠ x₂ → c.row x₁ ≠ c.row x₂

lemma row_congr [Countable β] [MeasurableSingletonClass β]
    {c₁ c₂ : GovernanceChannel α β} (h : c₁.kernel = c₂.kernel) (x : α) :
    c₁.row x = c₂.row x := by
  cases c₁
  cases c₂
  cases h
  rfl

@[simp]
lemma row_constant [Countable β] [MeasurableSingletonClass β]
    (d : β) (x : α) :
    (GovernanceChannel.constant (α := α) d).row x = PMF.pure d := by
  simp [row, GovernanceChannel.constant, PMF.toPMF_dirac]

lemma not_RowSeparating_constant [Countable β] [MeasurableSingletonClass β]
    [Nontrivial α] (d : β) :
    ¬ (GovernanceChannel.constant (α := α) d).RowSeparating := by
  intro hsep
  obtain ⟨x₁, x₂, hneq⟩ := exists_pair_ne α
  have hrows := hsep x₁ x₂ hneq
  have heq :
      (GovernanceChannel.constant (α := α) d).row x₁ =
        (GovernanceChannel.constant (α := α) d).row x₂ := by
    simp [row_constant]
  exact hrows heq

noncomputable instance instDecidableEqRow [DecidableEq β] :
    DecidableEq (PMF β) := by
  classical
  infer_instance

noncomputable instance instDecidableRowSeparating [Fintype α] [DecidableEq α]
    [Countable β] [MeasurableSingletonClass β] [DecidableEq β]
    (c : GovernanceChannel α β) : Decidable c.RowSeparating := by
  classical
  unfold RowSeparating row
  infer_instance

end GovernanceChannel

/-- Mutual information of a finite governance channel, defined as KL divergence
    between the induced joint law and the product of its marginals. -/
noncomputable def mutualInformation {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (p : Simplex α) (c : GovernanceChannel α β) : ℝ≥0∞ :=
  klDiv (GovernanceChannel.jointMeasure p c)
    (p.toMeasure.prod (GovernanceChannel.outputMeasure p c))

/-- Channel capacity as the supremum of mutual information over priors. -/
noncomputable def channelCapacity {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (c : GovernanceChannel α β) : ℝ≥0∞ :=
  sSup (Set.range (fun p : Simplex α => mutualInformation p c))

lemma mutualInformation_congr {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {c₁ c₂ : GovernanceChannel α β} (h : c₁.kernel = c₂.kernel)
    (p : Simplex α) :
    mutualInformation p c₁ = mutualInformation p c₂ := by
  cases c₁
  cases c₂
  cases h
  rfl

lemma channelCapacity_congr {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {c₁ c₂ : GovernanceChannel α β} (h : c₁.kernel = c₂.kernel) :
    channelCapacity c₁ = channelCapacity c₂ := by
  cases c₁
  cases c₂
  cases h
  rfl

/-- The finite-input `ℓ∞` distance between two claimant-strength profiles. -/
def inputLInf {n : Nat} [NeZero n] (s s' : Fin n → ℚ) : ℚ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty) (fun i => |s i - s' i|)

/-- Every coordinate difference is bounded by the finite `ℓ∞` distance. -/
lemma le_inputLInf {n : Nat} [NeZero n] (s s' : Fin n → ℚ) (i : Fin n) :
    |s i - s' i| ≤ inputLInf s s' := by
  simpa [inputLInf] using
    (Finset.le_sup'
      (s := Finset.univ (α := Fin n))
      (f := fun j : Fin n => |s j - s' j|)
      (by simp : i ∈ Finset.univ))

/-- A simple allocation layer obtained by thresholding the governance output. -/
def thresholdAllocation {n : Nat}
    (G : GovGraph ℚ n) (τ : ℚ) (s : Fin n → ℚ) : Fin n → BinaryDecision :=
  fun i => if τ < G.gov s i then BinaryDecision.Permit else BinaryDecision.Deny

/-- Deterministic governance channel obtained by thresholding graph outputs. -/
noncomputable def GovGraph.asThresholdChannel {n : Nat}
    (G : GovGraph ℚ n) (τ : ℚ) (s : Fin n → ℚ) :
    GovernanceChannel (Fin n) BinaryDecision where
  kernel := Kernel.deterministic (thresholdAllocation G τ s) (measurable_of_countable _)
  isMarkov := by infer_instance

/-- Toy finite channel with pairwise distinct rows. -/
noncomputable def triIdentityChannel : GovernanceChannel (Fin 3) (Fin 3) where
  kernel := Kernel.deterministic id (measurable_of_countable _)
  isMarkov := by infer_instance

@[simp]
lemma triIdentityChannel_row (i : Fin 3) :
    triIdentityChannel.row i = PMF.pure i := by
  ext j
  simp [triIdentityChannel, GovernanceChannel.row, Kernel.deterministic_apply]

lemma triIdentityChannel_rowSeparating :
    triIdentityChannel.RowSeparating := by
  intro i j hij hrow
  have happly := congrArg (fun p : PMF (Fin 3) => p i) hrow
  simp [triIdentityChannel_row, hij] at happly

/-- Closest in-framework analog of the desired Shannon statement: interpret the
    existing structural threshold `C_star` as a candidate capacity and ask
    whether every rate above it forces some nearby profile to incur positive
    Hamming distortion at the thresholded allocation layer. -/
def governance_channel_capacity_bound_candidate {n : Nat} [NeZero n]
    (G : GovGraph ℚ n) (s : Fin n → ℚ) (τ ε : ℚ) : Prop :=
  ∀ R : ℚ, C_star G s ε < R →
    ∃ s' : Fin n → ℚ,
      inputLInf s s' ≤ ε ∧
      0 < hammingDist (thresholdAllocation G τ s) (thresholdAllocation G τ s')

/-- Toy probe computation: the existing structural threshold on `uniTriGraph`
    at tolerance `1/10` is exactly `1/10`. -/
lemma uniTriGraph_C_star_one_tenth :
    C_star uniTriGraph sig (1 / 10) = 1 / 10 := by
  exact concrete_C_star_values.1

lemma uniTriGraph_gov_zero (s : Fin 3 → ℚ) :
    uniTriGraph.gov s 0 = (s 1 + s 2) / 2 := by
  rw [GovGraph.gov, uniTriGraph_deg 0, Fin.sum_univ_three]
  simp [GovGraph.W, uniTriGraph]

lemma uniTriGraph_gov_one (s : Fin 3 → ℚ) :
    uniTriGraph.gov s 1 = (s 0 + s 2) / 2 := by
  rw [GovGraph.gov, uniTriGraph_deg 1, Fin.sum_univ_three]
  simp [GovGraph.W, uniTriGraph]

lemma uniTriGraph_gov_two (s : Fin 3 → ℚ) :
    uniTriGraph.gov s 2 = (s 0 + s 1) / 2 := by
  rw [GovGraph.gov, uniTriGraph_deg 2, Fin.sum_univ_three]
  simp [GovGraph.W, uniTriGraph]

private lemma sig_coord_lower_bounds
    (s' : Fin 3 → ℚ) (hclose : inputLInf sig s' ≤ 1 / 10) :
    9 / 10 ≤ s' 0 ∧ 19 / 10 ≤ s' 1 ∧ 29 / 10 ≤ s' 2 := by
  have h0abs : |s' 0 - 1| ≤ 1 / 10 := by
    have h0 := le_trans (le_inputLInf sig s' 0) hclose
    simpa [sig, abs_sub_comm] using h0
  have h1abs : |s' 1 - 2| ≤ 1 / 10 := by
    have h1 := le_trans (le_inputLInf sig s' 1) hclose
    simpa [sig, abs_sub_comm] using h1
  have h2abs : |s' 2 - 3| ≤ 1 / 10 := by
    have h2 := le_trans (le_inputLInf sig s' 2) hclose
    simpa [sig, abs_sub_comm] using h2
  constructor
  · linarith [(abs_le.mp h0abs).1]
  constructor
  · linarith [(abs_le.mp h1abs).1]
  · linarith [(abs_le.mp h2abs).1]

/-- The threshold-0 allocation map is stable on the entire `1/10`-ball around
    `sig` for `uniTriGraph`: every claimant remains permitted. -/
lemma uniTriGraph_threshold_zero_stable
    (s' : Fin 3 → ℚ) (hclose : inputLInf sig s' ≤ 1 / 10) :
    thresholdAllocation uniTriGraph 0 s' = fun _ => BinaryDecision.Permit := by
  rcases sig_coord_lower_bounds s' hclose with ⟨h0, h1, h2⟩
  funext i
  fin_cases i
  · have hg : 0 < uniTriGraph.gov s' 0 := by
      rw [uniTriGraph_gov_zero]
      linarith
    simp [thresholdAllocation, hg]
  · have hg : 0 < uniTriGraph.gov s' 1 := by
      rw [uniTriGraph_gov_one]
      linarith
    simp [thresholdAllocation, hg]
  · have hg : 0 < uniTriGraph.gov s' 2 := by
      rw [uniTriGraph_gov_two]
      linarith
    simp [thresholdAllocation, hg]

lemma uniTriGraph_threshold_zero_sig :
    thresholdAllocation uniTriGraph 0 sig = fun _ => BinaryDecision.Permit := by
  apply uniTriGraph_threshold_zero_stable
  simp [inputLInf]

/-- Toy distortion computation: under the natural thresholded allocation map,
    every profile within `1/10` of `sig` has zero Hamming distortion relative
    to `sig`. -/
lemma uniTriGraph_zero_hamming_on_one_tenth_ball
    (s' : Fin 3 → ℚ) (hclose : inputLInf sig s' ≤ 1 / 10) :
    hammingDist (thresholdAllocation uniTriGraph 0 sig)
      (thresholdAllocation uniTriGraph 0 s') = 0 := by
  rw [uniTriGraph_threshold_zero_sig, uniTriGraph_threshold_zero_stable s' hclose]
  simp

/-- The closest available Shannon-style formulation already fails on the toy
    witness: above the structural threshold `C_star = 1/10`, no positive
    Hamming distortion is forced inside the `1/10` input ball around `sig`. -/
theorem governance_channel_capacity_probe_failure_uniTriGraph :
    ¬ governance_channel_capacity_bound_candidate uniTriGraph sig 0 (1 / 10) := by
  intro hcap
  have hlt : C_star uniTriGraph sig (1 / 10) < 1 := by
    rw [uniTriGraph_C_star_one_tenth]
    norm_num
  obtain ⟨s', hclose, hdist⟩ := hcap 1 hlt
  have hzero := uniTriGraph_zero_hamming_on_one_tenth_ball s' hclose
  simp [hzero] at hdist

lemma GovernanceChannel.outputMeasure_constant {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : Simplex α) (d : β) :
    GovernanceChannel.outputMeasure p (GovernanceChannel.constant (α := α) d) =
      Measure.dirac d := by
  ext s hs
  rw [GovernanceChannel.outputMeasure, Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp [GovernanceChannel.constant, Kernel.const_apply]

lemma GovernanceChannel.jointMeasure_constant {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (p : Simplex α) (d : β) :
    GovernanceChannel.jointMeasure p (GovernanceChannel.constant (α := α) d) =
      p.toMeasure.prod (Measure.dirac d) := by
  rw [GovernanceChannel.jointMeasure, GovernanceChannel.constant]
  exact MeasureTheory.Measure.compProd_const

lemma mutualInformation_constant {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : Simplex α) (d : β) :
    mutualInformation p (GovernanceChannel.constant (α := α) d) = 0 := by
  rw [mutualInformation, GovernanceChannel.jointMeasure_constant,
    GovernanceChannel.outputMeasure_constant, klDiv_self]

lemma range_mutualInformation_constant {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    [Nonempty α] (d : β) :
    Set.range (fun p : Simplex α =>
      mutualInformation p (GovernanceChannel.constant (α := α) d)) = {0} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    simp [mutualInformation_constant]
  · intro hx
    refine hx.symm ▸ ?_
    exact ⟨PMF.pure (Classical.arbitrary α),
      mutualInformation_constant (PMF.pure (Classical.arbitrary α)) d⟩

lemma channelCapacity_constant {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    [Nonempty α] (d : β) :
    channelCapacity (GovernanceChannel.constant (α := α) d) = 0 := by
  rw [channelCapacity, range_mutualInformation_constant (α := α) (β := β) d]
  simp

lemma asThresholdChannel_eq_constant_of_thresholdAllocation_eq {n : Nat}
    (G : GovGraph ℚ n) (τ : ℚ) (s : Fin n → ℚ) (d : BinaryDecision)
    (hconst : thresholdAllocation G τ s = fun _ => d) :
    (G.asThresholdChannel τ s).kernel =
      (GovernanceChannel.constant (α := Fin n) d).kernel := by
  ext i t
  rw [GovGraph.asThresholdChannel, GovernanceChannel.constant]
  simp [hconst, Kernel.const_apply, Kernel.deterministic_apply]

lemma uniTriGraph_asThresholdChannel_eq_constant :
    (uniTriGraph.asThresholdChannel 0 sig).kernel =
      (GovernanceChannel.constant (α := Fin 3) BinaryDecision.Permit).kernel := by
  exact asThresholdChannel_eq_constant_of_thresholdAllocation_eq
    uniTriGraph 0 sig BinaryDecision.Permit uniTriGraph_threshold_zero_sig

lemma uniTriGraph_asThresholdChannel_not_RowSeparating :
    ¬ (uniTriGraph.asThresholdChannel 0 sig).RowSeparating := by
  let c : GovernanceChannel (Fin 3) BinaryDecision := uniTriGraph.asThresholdChannel 0 sig
  let c0 : GovernanceChannel (Fin 3) BinaryDecision :=
    GovernanceChannel.constant (α := Fin 3) BinaryDecision.Permit
  have hc : c.kernel = c0.kernel := uniTriGraph_asThresholdChannel_eq_constant
  intro hsep
  have hsep0 : c0.RowSeparating := by
    intro x₁ x₂ hneq
    have hx₁ : c.row x₁ = c0.row x₁ := GovernanceChannel.row_congr hc x₁
    have hx₂ : c.row x₂ = c0.row x₂ := GovernanceChannel.row_congr hc x₂
    intro hrow
    exact hsep x₁ x₂ hneq (hx₁.trans (hrow.trans hx₂.symm))
  exact GovernanceChannel.not_RowSeparating_constant BinaryDecision.Permit hsep0

/-- The Shannon-analog uniqueness target fails for the natural public
    threshold-channel bridge: `uniTriGraph` at threshold `0` sends every
    claimant deterministically to `Permit`, so every prior attains capacity
    `0`. -/
theorem governance_channel_capacity_unique_failure_uniTriGraph :
    ¬ ∃! p : Simplex (Fin 3),
      mutualInformation p (uniTriGraph.asThresholdChannel 0 sig) =
        channelCapacity (uniTriGraph.asThresholdChannel 0 sig) := by
  let c : GovernanceChannel (Fin 3) BinaryDecision := uniTriGraph.asThresholdChannel 0 sig
  let c0 : GovernanceChannel (Fin 3) BinaryDecision :=
    GovernanceChannel.constant (α := Fin 3) BinaryDecision.Permit
  let p0 : Simplex (Fin 3) := PMF.pure 0
  let p1 : Simplex (Fin 3) := PMF.pure 1
  have hc :
      c.kernel = c0.kernel :=
    uniTriGraph_asThresholdChannel_eq_constant
  have hp0 :
      mutualInformation p0 c = channelCapacity c := by
    calc
      mutualInformation p0 c = mutualInformation p0 c0 := mutualInformation_congr hc p0
      _ = 0 := mutualInformation_constant p0 BinaryDecision.Permit
      _ = channelCapacity c0 := by
        simp [c0, channelCapacity_constant]
      _ = channelCapacity c := (channelCapacity_congr hc).symm
  have hp1 :
      mutualInformation p1 c = channelCapacity c := by
    calc
      mutualInformation p1 c = mutualInformation p1 c0 := mutualInformation_congr hc p1
      _ = 0 := mutualInformation_constant p1 BinaryDecision.Permit
      _ = channelCapacity c0 := by
        simp [c0, channelCapacity_constant]
      _ = channelCapacity c := (channelCapacity_congr hc).symm
  have hneq : p0 ≠ p1 := by
    intro h
    have happly := congrArg (fun p : Simplex (Fin 3) => p 0) h
    simp [p0, p1] at happly
  intro huniq
  rcases huniq with ⟨p, hp, hpuniq⟩
  have hp0eq : p0 = p := hpuniq p0 hp0
  have hp1eq : p1 = p := hpuniq p1 hp1
  exact hneq (hp0eq.trans hp1eq.symm)

end Legitimacy
