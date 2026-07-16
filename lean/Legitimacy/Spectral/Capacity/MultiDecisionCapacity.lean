/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Capacity.CapacityConverse
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Multi-decision capability-response capacity

This module lifts the deterministic finite-output capacity converse from the
binary capability-response channel to a `k`-decision response alphabet.
-/

set_option autoImplicit false

namespace Legitimacy

namespace GovGraph

variable {n : Nat}

/-- Subcritical bucket index for the `k`-decision capability response.

The final output letter is reserved for capabilities at or above `C_star`; the
remaining letters discretize the subcritical interval. -/
def karySubcriticalBucketIndex (Cstar C : ℚ) (k : Nat) : Nat :=
  Nat.findGreatest
    (fun j : Nat => ((j : ℚ) * Cstar) / ((k - 1 : Nat) : ℚ) ≤ C)
    (k - 2)

/-- `k`-decision capability response calibrated by the same reciprocal
critical-capability threshold as the binary response. -/
noncomputable def karyCapabilityResponse
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (k : Nat) (hk : 2 ≤ k) (C : ℚ) : Fin k :=
  if htop : C_star G s δ ≤ C then
    ⟨k - 1, by omega⟩
  else
    ⟨karySubcriticalBucketIndex (C_star G s δ) C k,
      lt_of_le_of_lt (Nat.findGreatest_le (k - 2)) (by omega)⟩

/-- Coordinatewise block use of the deterministic `k`-decision response. -/
noncomputable def karyCapabilityResponseBlock
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (k : Nat) (hk : 2 ≤ k) {block : Nat} (x : Fin block → ℚ) :
    Fin block → Fin k :=
  fun i => karyCapabilityResponse G s δ k hk (x i)

/-- A block code for repeated deterministic `k`-decision capability-response
uses. -/
structure KaryCapabilityResponseBlockCode
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ)
    (δ : ℚ) (k : Nat) (hk : 2 ≤ k) (block : Nat) where
  Message : Type
  [messageFintype : Fintype Message]
  encoder : Message → Fin block → ℚ
  decoder : (Fin block → Fin k) → Message

attribute [instance] KaryCapabilityResponseBlockCode.messageFintype

namespace KaryCapabilityResponseBlockCode

variable [NeZero n] {G : GovGraph ℚ n} {s : Fin n → ℚ}
  {δ : ℚ} {k block : Nat} {hk : 2 ≤ k}

/-- The realized `k`-decision output word of a block code. -/
noncomputable def output
    (code : KaryCapabilityResponseBlockCode G s δ k hk block)
    (m : code.Message) : Fin block → Fin k :=
  karyCapabilityResponseBlock G s δ k hk (code.encoder m)

/-- Zero-error decoding for the deterministic repeated `k`-decision channel. -/
def ZeroError (code : KaryCapabilityResponseBlockCode G s δ k hk block) :
    Prop :=
  ∀ m : code.Message, code.decoder (code.output m) = m

/-- A zero-error block code injects messages into output words. -/
theorem output_injective_of_zeroError
    (code : KaryCapabilityResponseBlockCode G s δ k hk block)
    (hzero : code.ZeroError) :
    Function.Injective code.output := by
  intro m₁ m₂ h
  have h₁ := hzero m₁
  have h₂ := hzero m₂
  calc
    m₁ = code.decoder (code.output m₁) := h₁.symm
    _ = code.decoder (code.output m₂) := by rw [h]
    _ = m₂ := h₂

/-- A zero-error `k`-decision block code cannot carry more messages than
there are output words. -/
theorem card_message_le_output_words_of_zeroError
    (code : KaryCapabilityResponseBlockCode G s δ k hk block)
    (hzero : code.ZeroError) :
    Fintype.card code.Message ≤ Fintype.card (Fin block → Fin k) := by
  classical
  exact Fintype.card_le_of_injective code.output
    (output_injective_of_zeroError code hzero)

/-- Cardinality converse in contrapositive form. -/
theorem not_zeroError_of_output_words_lt_card_message
    (code : KaryCapabilityResponseBlockCode G s δ k hk block)
    (hcard : Fintype.card (Fin block → Fin k) <
      Fintype.card code.Message) :
    ¬ code.ZeroError := by
  intro hzero
  exact not_lt_of_ge
    (card_message_le_output_words_of_zeroError code hzero) hcard

end KaryCapabilityResponseBlockCode

/-- The `k`-decision output alphabet over `block` deterministic uses has
`k^block` words. -/
theorem karyCapabilityResponse_output_word_card
    (k block : Nat) :
    Fintype.card (Fin block → Fin k) = k ^ block := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- The base-`k` natural log of the full output-word alphabet is the block
length. -/
theorem karyCapabilityResponse_output_word_nat_log
    (k block : Nat) (hk : 2 ≤ k) :
    Nat.log k (Fintype.card (Fin block → Fin k)) = block := by
  rw [karyCapabilityResponse_output_word_card]
  exact Nat.log_pow (by omega : 1 < k) block

private lemma kary_output_words_lt_card_of_log_rate
    (block M k : Nat) (hblock : 1 ≤ block) (hk : 2 ≤ k)
    (rate : ℚ)
    (hrate : (Real.log k / Real.log 2 : ℝ) < (rate : ℝ))
    (hrate_code :
      (rate : ℝ) ≤ (Real.logb 2 (M : ℝ) : ℝ) / (block : ℝ)) :
    k ^ block < M := by
  have hblock_pos_nat : 0 < block := lt_of_lt_of_le Nat.zero_lt_one hblock
  have hblock_pos : (0 : ℝ) < (block : ℝ) := by
    exact_mod_cast hblock_pos_nat
  have hk_one : 1 < k := by omega
  have hk_pos : 0 < k := by omega
  have hk_real_one : (1 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk_one
  have hnat_log :
      Nat.log k (Fintype.card (Fin block → Fin k)) = block :=
    karyCapabilityResponse_output_word_nat_log k block hk
  have hnat_log_real :
      ((Nat.log k (Fintype.card (Fin block → Fin k)) : Nat) : ℝ) =
        (block : ℝ) := by
    exact_mod_cast hnat_log
  have hnat_log_pow_real :
      ((Nat.log k (k ^ block) : Nat) : ℝ) = (block : ℝ) := by
    simpa [karyCapabilityResponse_output_word_card] using hnat_log_real
  have hlog_rate : Real.logb 2 (k : ℝ) < (rate : ℝ) := by
    simpa [Real.log_div_log] using hrate
  have hrate_pos : (0 : ℝ) < (rate : ℝ) :=
    lt_trans (Real.logb_pos (by norm_num : (1 : ℝ) < 2) hk_real_one)
      hlog_rate
  have hrate_mul_le_log :
      (rate : ℝ) * (block : ℝ) ≤ Real.logb 2 (M : ℝ) := by
    exact (le_div_iff₀ hblock_pos).mp hrate_code
  have hlog_power_lt_logM :
      Real.logb 2 ((k ^ block : Nat) : ℝ) < Real.logb 2 (M : ℝ) := by
    have hmul_lt :
        Real.logb 2 (k : ℝ) * (block : ℝ) <
          (rate : ℝ) * (block : ℝ) :=
      mul_lt_mul_of_pos_right hlog_rate hblock_pos
    have hpow_log :
        Real.logb 2 ((k ^ block : Nat) : ℝ) =
          (block : ℝ) * Real.logb 2 (k : ℝ) := by
      rw [← hnat_log_pow_real, hnat_log_pow_real]
      simpa [Nat.cast_pow] using Real.logb_pow (2 : ℝ) (k : ℝ) block
    calc
      Real.logb 2 ((k ^ block : Nat) : ℝ)
          = (block : ℝ) * Real.logb 2 (k : ℝ) := hpow_log
      _ = Real.logb 2 (k : ℝ) * (block : ℝ) := by ring
      _ < (rate : ℝ) * (block : ℝ) := hmul_lt
      _ ≤ Real.logb 2 (M : ℝ) := hrate_mul_le_log
  have hlogM_pos : (0 : ℝ) < Real.logb 2 (M : ℝ) := by
    have hdiv_pos : (0 : ℝ) < Real.logb 2 (M : ℝ) / (block : ℝ) :=
      lt_of_lt_of_le hrate_pos hrate_code
    exact (div_pos_iff_of_pos_right hblock_pos).mp hdiv_pos
  have hM_ne_zero : M ≠ 0 := by
    intro hzero
    simp [hzero, Real.logb_zero] at hlogM_pos
  have hM_pos : 0 < M := Nat.pos_of_ne_zero hM_ne_zero
  have hpow_pos : 0 < k ^ block := pow_pos hk_pos block
  by_contra hnot
  have hle_nat : M ≤ k ^ block := Nat.le_of_not_gt hnot
  have hle_real : (M : ℝ) ≤ ((k ^ block : Nat) : ℝ) := by
    exact_mod_cast hle_nat
  have hlogM_le_log_power :
      Real.logb 2 (M : ℝ) ≤ Real.logb 2 ((k ^ block : Nat) : ℝ) := by
    exact (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hM_pos) (by exact_mod_cast hpow_pos)).mpr hle_real
  exact not_lt_of_ge hlogM_le_log_power hlog_power_lt_logM

/-- Pure `k`-decision zero-error converse. Any deterministic `k`-output block
code whose base-2 log-message rate is strictly above `log₂ k` decisions per use
has too many messages for the available output words, so it cannot be
zero-error. -/
theorem multi_decision_capability_response_log_rate_converse
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (k : Nat) (hk : 2 ≤ k)
    (rate : ℚ)
    (hrate : (Real.log k / Real.log 2 : ℝ) < (rate : ℝ)) :
    ∃ block_threshold : Nat, ∀ block ≥ block_threshold,
      ∀ code : KaryCapabilityResponseBlockCode G s δ k hk block,
        (rate : ℝ) ≤
          (Real.logb 2 (Fintype.card code.Message) : ℝ) / (block : ℝ) →
          ¬ code.ZeroError := by
  refine ⟨1, ?_⟩
  intro block hblock code hrate_code
  have hcard :
      k ^ block < Fintype.card code.Message :=
    kary_output_words_lt_card_of_log_rate block
      (Fintype.card code.Message) k hblock hk rate hrate hrate_code
  have houtput :
      Fintype.card (Fin block → Fin k) < Fintype.card code.Message := by
    simpa [karyCapabilityResponse_output_word_card] using hcard
  exact
    KaryCapabilityResponseBlockCode.not_zeroError_of_output_words_lt_card_message
      code houtput

noncomputable local instance : DecidableEq (GovGraph ℚ 3) := Classical.decEq _

private lemma log_two_le_log_nat_of_two_le (k : Nat) (hk : 2 ≤ k) :
    Real.log 2 ≤ Real.log (k : ℝ) := by
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  exact Real.log_le_log (by norm_num : (0 : ℝ) < 2) hk_real

private lemma half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 :=
  lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9

private lemma two_thirds_lt_log_two : (2 / 3 : ℝ) < Real.log 2 :=
  lt_trans (by norm_num : (2 / 3 : ℝ) < 0.6931471803) Real.log_two_gt_d9

/-- The strongly connected triangle has half-scale CV exactly `1 / 2`. -/
lemma stronglyConnectedGraph_cv_halfSig :
    stronglyConnectedGraph.cv halfSig = (1 / 2 : ℚ) := by
  native_decide

/-- The strongly connected triangle has positive half-scale CV. -/
lemma stronglyConnectedGraph_cv_halfSig_pos :
    0 < stronglyConnectedGraph.cv halfSig := by
  rw [stronglyConnectedGraph_cv_halfSig]
  norm_num

/-- The five canonical three-node graphs admit concrete signals whose CV lies
strictly inside the native `k`-decision calibrated range. -/
theorem canonical_graphs_inhabit_kary_calibrated_range
    (k : Nat) (hk : 2 ≤ k) :
    ∀ G ∈ ({uniTriGraph, asymTriGraph, nearPathGraph,
            stronglyConnectedGraph, bottleneckGraph} :
            Finset (GovGraph ℚ 3)),
      ∃ s_kary : Fin 3 → ℚ,
        (0 < G.cv s_kary) ∧
        ((G.cv s_kary : ℝ) < Real.log k) := by
  intro G hG
  have hlog : Real.log 2 ≤ Real.log (k : ℝ) :=
    log_two_le_log_nat_of_two_le k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hG
  rcases hG with hG | hG | hG | hG | hG
  · subst G
    refine ⟨halfSig, ?_, ?_⟩
    · exact GovernanceChannel.uniTriGraph_cv_halfSig_pos
    · have hcv :
          ((uniTriGraph.cv halfSig : ℚ) : ℝ) = (1 / 2 : ℝ) := by
        rw [GovernanceChannel.uniTriGraph_cv_halfSig]
        norm_num
      rw [hcv]
      exact lt_of_lt_of_le half_lt_log_two hlog
  · subst G
    refine ⟨asymTriHalfSig, ?_, ?_⟩
    · exact GovernanceChannel.asymTriGraph_cv_asymTriHalfSig_pos
    · have hcv :
          ((asymTriGraph.cv asymTriHalfSig : ℚ) : ℝ) = (2 / 3 : ℝ) := by
        rw [GovernanceChannel.asymTriGraph_cv_asymTriHalfSig]
        norm_num
      rw [hcv]
      exact lt_of_lt_of_le two_thirds_lt_log_two hlog
  · subst G
    refine ⟨nearPathHalfSig, ?_, ?_⟩
    · exact GovernanceChannel.nearPathGraph_cv_nearPathHalfSig_pos
    · have hcv :
          ((nearPathGraph.cv nearPathHalfSig : ℚ) : ℝ) = (1 / 2 : ℝ) := by
        rw [GovernanceChannel.nearPathGraph_cv_nearPathHalfSig]
        norm_num
      rw [hcv]
      exact lt_of_lt_of_le half_lt_log_two hlog
  · subst G
    refine ⟨halfSig, ?_, ?_⟩
    · exact stronglyConnectedGraph_cv_halfSig_pos
    · have hcv :
          ((stronglyConnectedGraph.cv halfSig : ℚ) : ℝ) = (1 / 2 : ℝ) := by
        rw [stronglyConnectedGraph_cv_halfSig]
        norm_num
      rw [hcv]
      exact lt_of_lt_of_le half_lt_log_two hlog
  · subst G
    refine ⟨bottleneckHalfSig, ?_, ?_⟩
    · exact GovernanceChannel.bottleneckGraph_cv_bottleneckHalfSig_pos
    · have hcv :
          ((bottleneckGraph.cv bottleneckHalfSig : ℚ) : ℝ) = (1 / 2 : ℝ) := by
        rw [GovernanceChannel.bottleneckGraph_cv_bottleneckHalfSig]
        norm_num
      rw [hcv]
      exact lt_of_lt_of_le half_lt_log_two hlog

private def finTwoEquivBool : Fin 2 ≃ Bool where
  toFun i := if i = 0 then false else true
  invFun b := if b then 1 else 0
  left_inv := by
    intro i
    fin_cases i <;> simp
  right_inv := by
    intro b
    cases b <;> simp

/-- The `k`-decision response separates strictly subcritical positive
capabilities from capabilities at or above `C_star`, and at `k = 2` recovers
the existing binary capability-response channel up to the canonical finite
alphabet equivalence. -/
theorem multi_decision_capability_response_C_star_binding
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (k : Nat) (hk : 2 ≤ k) (hδ : 0 < δ) (hcv : 0 < G.cv s) :
    (∀ C₁ C₂ : ℚ, 0 < C₁ → 0 < C₂ →
       C₁ < C_star G s δ → C_star G s δ ≤ C₂ →
         karyCapabilityResponse G s δ k hk C₁ ≠
         karyCapabilityResponse G s δ k hk C₂) ∧
    (k = 2 → ∀ C : ℚ, 0 < C →
       ∃ φ : Fin 2 ≃ BinaryDecision,
         φ (karyCapabilityResponse G s δ 2 (by omega) C) =
         G.capabilityResponse s δ C) := by
  constructor
  · intro C₁ C₂ _hC₁ _hC₂ hlt hle heq
    have hnot_top₁ : ¬ C_star G s δ ≤ C₁ := not_le_of_gt hlt
    have hleft_val :
        (karyCapabilityResponse G s δ k hk C₁).val ≤ k - 2 := by
      simp [karyCapabilityResponse, hnot_top₁, karySubcriticalBucketIndex,
        Nat.findGreatest_le]
    have hright_val :
        (karyCapabilityResponse G s δ k hk C₂).val = k - 1 := by
      simp [karyCapabilityResponse, hle]
    have hval_eq :
        (karyCapabilityResponse G s δ k hk C₁).val =
          (karyCapabilityResponse G s δ k hk C₂).val :=
      congrArg Fin.val heq
    rw [hright_val] at hval_eq
    omega
  · intro hk_two C hC
    subst k
    let φ : Fin 2 ≃ BinaryDecision :=
      finTwoEquivBool.trans GovernanceChannel.binaryDecisionEquivBool.symm
    refine ⟨φ, ?_⟩
    by_cases htop : C_star G s δ ≤ C
    · have hpermit :
          G.capabilityResponse s δ C = BinaryDecision.Permit :=
        (G.capabilityResponse_eq_permit_iff_C_star_le s δ C hδ hcv hC).mpr
          htop
      simp [φ, finTwoEquivBool, GovernanceChannel.binaryDecisionEquivBool,
        karyCapabilityResponse, htop, hpermit]
    · have hlt : C < C_star G s δ := lt_of_not_ge htop
      have hdeny :
          G.capabilityResponse s δ C = BinaryDecision.Deny :=
        (G.capabilityResponse_threshold s δ hδ hcv).1 C hC hlt
      simp [φ, finTwoEquivBool, GovernanceChannel.binaryDecisionEquivBool,
        karyCapabilityResponse, htop, karySubcriticalBucketIndex, hdeny]

end GovGraph

end Legitimacy
