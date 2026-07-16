/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Channels.CStarChannelBridge
import Mathlib.Data.Nat.Log

/-!
# Governance capacity converse

This module packages the finite zero-error converse for the deterministic
capability-response channel in Shannon-style log-rate form.

## Main results

* `binary_output_log_rate_converse`: no zero-error binary-output block code can
  sustain log-rate strictly above one binary decision per channel use.
* `governance_capacity_threshold_C_star_binding`: the rate threshold is tied
  to the exact `C_star` response transition, including the CV quotient form.
* `governance_capacity_alignment_threshold`: target-saturating alignment
  protocols above `C_star` collapse to the all-`Permit` output word, so their
  sustainable log-rate threshold is zero.
* `raw_cardinality_rate_padding_counterexample`: the raw `card / block` form is
  not a valid capacity converse; the existing full binary code already refutes
  it.
-/

set_option autoImplicit false

namespace Legitimacy

namespace GovGraph

variable {n : Nat}

private lemma output_words_lt_card_of_log_rate
    (block M : Nat) (hblock : 1 ≤ block)
    (rate : ℚ) (hrate : binaryDecisionPerUseRate < rate)
    (hrate_code : rate ≤ (Nat.log2 M : ℚ) / (block : ℚ)) :
    2 ^ block < M := by
  have hblock_pos_nat : 0 < block := lt_of_lt_of_le Nat.zero_lt_one hblock
  have hblock_pos : (0 : ℚ) < block := by
    exact_mod_cast hblock_pos_nat
  have hrate_one : (1 : ℚ) < rate := by
    simpa [binaryDecisionPerUseRate] using hrate
  have hblock_lt_rate_mul : (block : ℚ) < rate * block := by
    simpa using mul_lt_mul_of_pos_right hrate_one hblock_pos
  have hrate_mul_le_log : rate * (block : ℚ) ≤ Nat.log2 M := by
    exact (le_div_iff₀ hblock_pos).mp hrate_code
  have hblock_lt_log : (block : ℚ) < Nat.log2 M :=
    lt_of_lt_of_le hblock_lt_rate_mul hrate_mul_le_log
  have hnat : block < Nat.log2 M := by
    exact_mod_cast hblock_lt_log
  have hMpos : M ≠ 0 := by
    intro hzero
    simp [hzero] at hnat
  by_contra hnot
  have hle : M ≤ 2 ^ block := Nat.le_of_not_gt hnot
  have hpow_lt : 2 ^ block < 2 ^ (block + 1) := by
    exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self block)
  have hMlt : M < 2 ^ (block + 1) := lt_of_le_of_lt hle hpow_lt
  have hlog_lt : Nat.log2 M < block + 1 := (Nat.log2_lt hMpos).2 hMlt
  omega

private lemma one_lt_card_of_positive_log_rate
    (block M : Nat) (hblock : 1 ≤ block)
    (rate : ℚ) (hrate : 0 < rate)
    (hrate_code : rate ≤ (Nat.log2 M : ℚ) / (block : ℚ)) :
    1 < M := by
  have hblock_pos_nat : 0 < block := lt_of_lt_of_le Nat.zero_lt_one hblock
  have hblock_pos : (0 : ℚ) < block := by
    exact_mod_cast hblock_pos_nat
  have hrate_mul_pos : 0 < rate * (block : ℚ) := mul_pos hrate hblock_pos
  have hrate_mul_le_log : rate * (block : ℚ) ≤ Nat.log2 M := by
    exact (le_div_iff₀ hblock_pos).mp hrate_code
  have hlog_pos : (0 : ℚ) < Nat.log2 M :=
    lt_of_lt_of_le hrate_mul_pos hrate_mul_le_log
  have hlog_nat_pos : 0 < Nat.log2 M := by
    exact_mod_cast hlog_pos
  by_contra hnot
  have hle : M ≤ 1 := Nat.le_of_not_gt hnot
  interval_cases M
  · simp at hlog_nat_pos
  · have hlog1 : Nat.log2 1 = 0 := by
      native_decide
    omega

/-- Pure binary-output zero-error converse. Any deterministic binary-output
block code whose base-2 log-message rate is strictly above one binary decision
per use has too many messages for the available output words, so it cannot be
zero-error. This counting lemma intentionally has no `C_star`/CV hypotheses;
those enter in the capability-response wrapper below. -/
theorem binary_output_log_rate_converse
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (rate : ℚ) (hrate : binaryDecisionPerUseRate < rate) :
    ∃ block_threshold : Nat, ∀ block ≥ block_threshold,
      ∀ code : CapabilityResponseBlockCode G s δ block,
        rate ≤ (Nat.log2 (Fintype.card code.Message) : ℚ) / block →
          ¬ code.ZeroError := by
  refine ⟨1, ?_⟩
  intro block hblock code hrate_code
  have hcard :
      2 ^ block < Fintype.card code.Message :=
    output_words_lt_card_of_log_rate block (Fintype.card code.Message)
      hblock rate hrate hrate_code
  have houtput :
      Fintype.card (Fin block → BinaryDecision) <
        Fintype.card code.Message := by
    simpa [capabilityResponse_output_word_card] using hcard
  exact CapabilityResponseBlockCode.not_zeroError_of_output_words_lt_card_message
    code houtput

/-- The capacity threshold is one binary decision per use, and the same
package records the exact structural binding to `C_star`: clearing `C_star` is
equivalent to a `Permit` response, both on concrete graphs and on the CV
quotient class where `C_star` descends. -/
theorem governance_capacity_threshold_C_star_binding
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hcv : 0 < G.cv s) :
    ∃ rate_threshold : ℚ,
      rate_threshold ≤ binaryDecisionPerUseRate ∧
      (∀ rate, rate_threshold < rate →
        ∃ block_threshold : Nat, ∀ block ≥ block_threshold,
          ∀ code : CapabilityResponseBlockCode G s δ block,
            rate ≤ (Nat.log2 (Fintype.card code.Message) : ℚ) / block →
              ¬ code.ZeroError) ∧
      (∀ C : ℚ, 0 < C →
        (G.capabilityResponse s δ C = BinaryDecision.Permit ↔ C_star G s δ ≤ C)) ∧
      (∀ C : ℚ, 0 < C →
        (capabilityResponseClass s δ C (cvClass G s) = BinaryDecision.Permit ↔
          C_starClass s δ (cvClass G s) ≤ C)) := by
  refine ⟨binaryDecisionPerUseRate, le_rfl, ?_, ?_, ?_⟩
  · intro rate hrate
    exact binary_output_log_rate_converse G s δ rate hrate
  · intro C hC
    exact G.capabilityResponse_eq_permit_iff_C_star_le s δ C hδ hcv hC
  · intro C hC
    have hcvClass : 0 < cvValueClass s (cvClass G s) := by
      simpa using hcv
    exact capabilityResponseClass_eq_permit_iff_C_starClass_le
      s (cvClass G s) δ C hδ hcvClass hC

/-! ## Alignment protocols -/

/-- An alignment protocol over the capability-response channel.

The message family is indexed by block length, so a protocol that claims a
positive asymptotic certification rate has to expose its growing message set.
The deployment Boolean is constrained by the concrete channel code: a `true`
claim means the protocol's embedded channel message decodes back to itself.
This prevents vacuous instances where deployment success is unrelated to the
capability-response substrate. The target-capability bound is used by the
`C_star` threshold theorem below together with an explicit target-use floor:
target-saturating protocols collapse to a single `Permit` output word above
`C_star`. -/
structure AlignmentProtocol
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) where
  /-- Alignment-relevant messages available at each block length. -/
  Message : Nat → Type
  /-- Each block message alphabet is finite. -/
  messageFintype : ∀ block, Fintype (Message block)
  /-- Capability level claimed by the protocol. -/
  target_capability : ℚ
  /-- The concrete capability-response block code through which messages are certified. -/
  code : ∀ block, CapabilityResponseBlockCode G s δ block
  /-- Structural embedding of protocol messages into the channel code's message set. -/
  encode : ∀ block, Message block → (code block).Message
  /-- The embedding cannot identify two alignment messages. -/
  encode_injective : ∀ block, Function.Injective (encode block)
  /-- Deployment claim for one block/message pair. -/
  deploy_zero_error_at_capability : ∀ block, Message block → Bool
  /-- A successful deployment claim is exactly successful channel decoding of
  the embedded message. -/
  deploy_true_iff_decodes : ∀ block m,
    deploy_zero_error_at_capability block m = true ↔
      (code block).decoder ((code block).output (encode block m)) = encode block m
  /-- The protocol uses no coordinate capability above its stated target. -/
  encoder_respects_target : ∀ block m i,
    (code block).encoder (encode block m) i ≤ target_capability

attribute [instance] AlignmentProtocol.messageFintype

/-- Honest alignment-protocol log-rate converse. This is the protocol-level
form of `binary_output_log_rate_converse`: if an encode-injective protocol claims
log-rate strictly above one binary decision per use, then some message must
fail deployment at every positive block length. It does not use a `C_star`
hypothesis. -/
theorem governance_capacity_alignment_log_rate_converse
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (protocol : AlignmentProtocol G s δ)
    (rate : ℚ) (hrate : binaryDecisionPerUseRate < rate)
    (hprotocol_rate : ∀ block, 1 ≤ block →
      rate ≤ (Nat.log2 (Fintype.card (protocol.Message block)) : ℚ) / block) :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ message : protocol.Message block,
        protocol.deploy_zero_error_at_capability block message = false := by
  refine ⟨1, ?_⟩
  intro block hblock
  have hcard :
      2 ^ block < Fintype.card (protocol.Message block) :=
    output_words_lt_card_of_log_rate block (Fintype.card (protocol.Message block))
      hblock rate hrate (hprotocol_rate block hblock)
  have htoo_many :
      Fintype.card (Fin block → BinaryDecision) <
        Fintype.card (protocol.Message block) := by
    simpa [capabilityResponse_output_word_card] using hcard
  by_contra hnone
  have hall : ∀ message : protocol.Message block,
      protocol.deploy_zero_error_at_capability block message = true := by
    intro message
    cases hdeploy : protocol.deploy_zero_error_at_capability block message with
    | false => exact False.elim (hnone ⟨message, hdeploy⟩)
    | true => rfl
  let realized : protocol.Message block → Fin block → BinaryDecision :=
    fun message => (protocol.code block).output (protocol.encode block message)
  have hinj : Function.Injective realized := by
    intro m₁ m₂ hsame
    have hdecode₁ := (protocol.deploy_true_iff_decodes block m₁).mp (hall m₁)
    have hdecode₂ := (protocol.deploy_true_iff_decodes block m₂).mp (hall m₂)
    have hencoded : protocol.encode block m₁ = protocol.encode block m₂ := by
      calc
        protocol.encode block m₁ =
            (protocol.code block).decoder
              ((protocol.code block).output (protocol.encode block m₁)) :=
          hdecode₁.symm
        _ = (protocol.code block).decoder
              ((protocol.code block).output (protocol.encode block m₂)) := by
          simpa [realized] using congrArg (protocol.code block).decoder hsame
        _ = protocol.encode block m₂ := hdecode₂
    exact protocol.encode_injective block hencoded
  have hle : Fintype.card (protocol.Message block) ≤
      Fintype.card (Fin block → BinaryDecision) :=
    Fintype.card_le_of_injective realized hinj
  exact (not_lt_of_ge hle) htoo_many

/-- C*-bound alignment threshold for target-saturating protocols. If every
embedded coordinate is used exactly at the protocol's target capability, then
`target_capability ≥ C_star` forces every capability-response output letter to
be `Permit`. The available output alphabet collapses to one word, so any
positive log-rate family has a failed deployment at every positive block
length. -/
theorem governance_capacity_alignment_threshold
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hcv : 0 < G.cv s)
    (protocol : AlignmentProtocol G s δ)
    (hcap : C_star G s δ ≤ protocol.target_capability)
    (htarget_floor : ∀ block m i,
      protocol.target_capability ≤ (protocol.code block).encoder (protocol.encode block m) i)
    (rate : ℚ) (hrate : 0 < rate)
    (hprotocol_rate : ∀ block, 1 ≤ block →
      rate ≤ (Nat.log2 (Fintype.card (protocol.Message block)) : ℚ) / block) :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ message : protocol.Message block,
        protocol.deploy_zero_error_at_capability block message = false := by
  refine ⟨1, ?_⟩
  intro block hblock
  have hmany : 1 < Fintype.card (protocol.Message block) :=
    one_lt_card_of_positive_log_rate block (Fintype.card (protocol.Message block))
      hblock rate hrate (hprotocol_rate block hblock)
  have hCstar_pos : 0 < C_star G s δ := by
    simpa [C_star] using div_pos hδ hcv
  have htarget_pos : 0 < protocol.target_capability :=
    lt_of_lt_of_le hCstar_pos hcap
  by_contra hnone
  have hall : ∀ message : protocol.Message block,
      protocol.deploy_zero_error_at_capability block message = true := by
    intro message
    cases hdeploy : protocol.deploy_zero_error_at_capability block message with
    | false => exact False.elim (hnone ⟨message, hdeploy⟩)
    | true => rfl
  let permitWord : Fin block → BinaryDecision := fun _ => BinaryDecision.Permit
  have houtput_permit : ∀ message : protocol.Message block,
      (protocol.code block).output (protocol.encode block message) = permitWord := by
    intro message
    funext i
    have hcoord_eq :
        (protocol.code block).encoder (protocol.encode block message) i =
          protocol.target_capability :=
      le_antisymm (protocol.encoder_respects_target block message i)
        (htarget_floor block message i)
    have hcoord_pos :
        0 < (protocol.code block).encoder (protocol.encode block message) i := by
      rw [hcoord_eq]
      exact htarget_pos
    have hcoord_Cstar :
        C_star G s δ ≤
          (protocol.code block).encoder (protocol.encode block message) i := by
      rw [hcoord_eq]
      exact hcap
    have hpermit :=
      (G.capabilityResponse_eq_permit_iff_C_star_le
        s δ ((protocol.code block).encoder (protocol.encode block message) i)
        hδ hcv hcoord_pos).mpr hcoord_Cstar
    simpa [CapabilityResponseBlockCode.output, capabilityResponseBlock, permitWord]
      using hpermit
  have hall_eq : ∀ m₁ m₂ : protocol.Message block, m₁ = m₂ := by
    intro m₁ m₂
    have hdecode₁ := (protocol.deploy_true_iff_decodes block m₁).mp (hall m₁)
    have hdecode₂ := (protocol.deploy_true_iff_decodes block m₂).mp (hall m₂)
    have hencoded : protocol.encode block m₁ = protocol.encode block m₂ := by
      calc
        protocol.encode block m₁ =
            (protocol.code block).decoder
              ((protocol.code block).output (protocol.encode block m₁)) :=
          hdecode₁.symm
        _ = (protocol.code block).decoder permitWord := by
          rw [houtput_permit m₁]
        _ = (protocol.code block).decoder
              ((protocol.code block).output (protocol.encode block m₂)) := by
          rw [houtput_permit m₂]
        _ = protocol.encode block m₂ := hdecode₂
    exact protocol.encode_injective block hencoded
  have hle : Fintype.card (protocol.Message block) ≤ 1 :=
    (Fintype.card_le_one_iff).2 hall_eq
  exact (not_lt_of_ge hle) hmany

/-! ## Concrete bottleneck checks -/

/-- Computable counterpart of `capabilityResponse`, used only for concrete
`native_decide` fixtures. -/
def decidableCapabilityResponse
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ C : ℚ) :
    BinaryDecision :=
  if 0 < C ∧ δ / C ≤ G.cv s then
    BinaryDecision.Permit
  else
    BinaryDecision.Deny

@[simp]
lemma decidableCapabilityResponse_eq_capabilityResponse
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ C : ℚ) :
    decidableCapabilityResponse G s δ C = G.capabilityResponse s δ C := by
  rw [decidableCapabilityResponse, capabilityResponse, G.spViolation_iff_le_cv]
  by_cases h : 0 < C ∧ δ / C ≤ G.cv s <;> simp [h]

/-- Below the bottleneck graph's concrete `C_star = 1/10`, the response is
`Deny`. This is the concrete subcritical side of the worked example. -/
example :
    decidableCapabilityResponse bottleneckGraph sig (1 / 10) (1 / 20) =
      BinaryDecision.Deny := by
  native_decide

/-- At the bottleneck graph's concrete `C_star = 1/10`, the response is
`Permit`. This is the concrete supercritical side of the worked example. -/
example :
    decidableCapabilityResponse bottleneckGraph sig (1 / 10) (1 / 10) =
      BinaryDecision.Permit := by
  native_decide

/-- The bottleneck fixture has positive CV, so the concrete binary
zero-error construction applies. -/
example :
    0 < bottleneckGraph.cv sig := by
  native_decide

/-- Concrete achievability side: the full binary block code is zero-error on
the bottleneck fixture. -/
example :
    (capabilityResponseBinaryBlockCode bottleneckGraph sig (1 / 10) 4).ZeroError := by
  exact capabilityResponseBinaryBlockCode_zeroError
    bottleneckGraph sig (1 / 10) 4 (by norm_num) (by native_decide)

/-! ## Concrete alignment-protocol fixtures -/

/-- Bottleneck binary protocol backed by the substrate's zero-error binary
block code. Deployment is computed from the channel decoder, not asserted as a
constant. -/
noncomputable def bottleneckBinaryAlignmentProtocol :
    AlignmentProtocol bottleneckGraph sig (1 / 10) where
  Message := fun block =>
    (capabilityResponseBinaryBlockCode bottleneckGraph sig (1 / 10) block).Message
  messageFintype := fun _ => inferInstance
  target_capability := 1 / 10
  code := fun block =>
    capabilityResponseBinaryBlockCode bottleneckGraph sig (1 / 10) block
  encode := fun _ message => message
  encode_injective := by
    intro _ _ _ h
    exact h
  deploy_zero_error_at_capability := fun block message =>
    by
      classical
      exact
        decide
          ((capabilityResponseBinaryBlockCode bottleneckGraph sig (1 / 10) block).decoder
            ((capabilityResponseBinaryBlockCode bottleneckGraph sig (1 / 10) block).output
              message) = message)
  deploy_true_iff_decodes := by
    classical
    intro block message
    constructor
    · intro h
      exact of_decide_eq_true h
    · intro h
      exact decide_eq_true h
  encoder_respects_target := by
    intro block message i
    have hC : C_star bottleneckGraph sig (1 / 10) = (1 / 10 : ℚ) := by
      exact concrete_C_star_values.2.2.2.2
    by_cases hpermit : message i = BinaryDecision.Permit
    · simp [capabilityResponseBinaryBlockCode, hpermit]
      have hC_le : C_star bottleneckGraph sig (1 / 10) ≤ (1 / 10 : ℚ) := by
        rw [hC]
      simpa using hC_le
    · have hdeny : message i = BinaryDecision.Deny := by
        cases h : message i with
        | Permit => exact False.elim (hpermit h)
        | Deny => rfl
      simp [capabilityResponseBinaryBlockCode, hdeny]
      have hhalf : C_star bottleneckGraph sig (1 / 10) / 2 ≤ (1 / 10 : ℚ) := by
        rw [hC]
        norm_num
      simpa using hhalf

/-- Concrete achievability-side protocol check: the binary fixture certifies
the all-permit word at block length one by decoding through the channel. -/
example :
    bottleneckBinaryAlignmentProtocol.deploy_zero_error_at_capability 1
      (fun _ => BinaryDecision.Permit) =
      true := by
  classical
  exact decide_eq_true
    (capabilityResponseBinaryBlockCode_zeroError
      bottleneckGraph sig (1 / 10) 1 (by norm_num) (by native_decide)
      (fun _ => BinaryDecision.Permit))

/-- The same non-constant deployment computation certifies a denial-bearing
word in the binary fixture. -/
example :
    bottleneckBinaryAlignmentProtocol.deploy_zero_error_at_capability 1
      (fun _ => BinaryDecision.Deny) =
      true := by
  classical
  exact decide_eq_true
    (capabilityResponseBinaryBlockCode_zeroError
      bottleneckGraph sig (1 / 10) 1 (by norm_num) (by native_decide)
      (fun _ => BinaryDecision.Deny))

/-- Hostile target-saturating padded block code: it exposes exponentially too
many messages while every coordinate is evaluated by the capability-response
channel at the stated target capability. -/
def paddedTargetBlockCode (target : ℚ) (block : Nat) :
    CapabilityResponseBlockCode bottleneckGraph sig (1 / 10) block where
  Message := Fin (2 ^ (2 * block))
  encoder := fun _ _ => target
  decoder := fun _ => 0

/-- Padded supercritical protocol at the bottleneck graph's concrete `C_star`.
Its deployment claim is derived from the channel decoder; above `C_star`, the
target-saturating encoder makes all output words `Permit`, so the C*-threshold
converse rejects the inflated message set. -/
def bottleneckPaddedAlignmentProtocol :
    AlignmentProtocol bottleneckGraph sig (1 / 10) where
  Message := fun block => Fin (2 ^ (2 * block))
  messageFintype := fun _ => inferInstance
  target_capability := 1 / 10
  code := fun block => paddedTargetBlockCode (1 / 10) block
  encode := fun _ message => message
  encode_injective := by
    intro _ _ _ h
    exact h
  deploy_zero_error_at_capability := fun _ message => decide (message = 0)
  deploy_true_iff_decodes := by
    intro block message
    change decide (message = 0) = true ↔ (0 : Fin (2 ^ (2 * block))) = message
    rw [show ((0 : Fin (2 ^ (2 * block))) = message) ↔ message = 0 by
      exact eq_comm]
    constructor
    · intro h
      exact of_decide_eq_true h
    · intro h
      exact decide_eq_true h
  encoder_respects_target := by
    intro _ _ _
    rfl

/-- Concrete converse-side protocol check: a padded nonzero message is not
certified. -/
example :
    bottleneckPaddedAlignmentProtocol.deploy_zero_error_at_capability 1
      (⟨1, by norm_num⟩ : bottleneckPaddedAlignmentProtocol.Message 1) = false := by
  native_decide

lemma bottleneckPaddedAlignmentProtocol_log_rate
    (block : Nat) (hblock : 1 ≤ block) :
    (3 / 2 : ℚ) ≤
      (Nat.log2
        (Fintype.card (bottleneckPaddedAlignmentProtocol.Message block)) : ℚ) /
        block := by
  change (3 / 2 : ℚ) ≤
    (Nat.log2 (Fintype.card (Fin (2 ^ (2 * block))) : Nat) : ℚ) / block
  rw [Fintype.card_fin, Nat.log2_eq_log_two]
  rw [Nat.log_pow Nat.one_lt_two]
  have hblock_pos_nat : 0 < block := lt_of_lt_of_le Nat.zero_lt_one hblock
  have hblock_pos : (0 : ℚ) < block := by
    exact_mod_cast hblock_pos_nat
  rw [Nat.cast_mul]
  calc
    (3 / 2 : ℚ) ≤ 2 := by norm_num
    _ = (2 * (block : ℚ)) / block := by
      field_simp [ne_of_gt hblock_pos]

/-- Concrete protocol-level converse: the padded supercritical bottleneck
protocol has a witnessed failed deployment at every block length at least one. -/
theorem bottleneck_padded_alignment_converse_fires :
    ∃ block_length : Nat, ∀ block ≥ block_length,
      ∃ message : bottleneckPaddedAlignmentProtocol.Message block,
        bottleneckPaddedAlignmentProtocol.deploy_zero_error_at_capability
          block message = false := by
  have hcap :
      C_star bottleneckGraph sig (1 / 10) ≤
        bottleneckPaddedAlignmentProtocol.target_capability := by
    change C_star bottleneckGraph sig (1 / 10) ≤ (1 / 10 : ℚ)
    rw [concrete_C_star_values.2.2.2.2]
  have htarget_floor : ∀ block m i,
      bottleneckPaddedAlignmentProtocol.target_capability ≤
        (bottleneckPaddedAlignmentProtocol.code block).encoder
          (bottleneckPaddedAlignmentProtocol.encode block m) i := by
    intro _ _ _
    rfl
  exact governance_capacity_alignment_threshold
    bottleneckGraph sig (1 / 10) (by norm_num) (by native_decide)
    bottleneckPaddedAlignmentProtocol hcap htarget_floor (3 / 2) (by norm_num)
    bottleneckPaddedAlignmentProtocol_log_rate

/-! ## Tightness against padded raw-cardinality rates -/

/-- Hostile padded-rate witness: if "rate" is incorrectly read as
`card Message / block` instead of Shannon's `log₂(card Message) / block`, the
existing zero-error binary block code already violates the proposed converse.
For block length `4`, it has `16` messages, raw rate `4`, and zero error while
the claimed threshold is only `1`. -/
theorem raw_cardinality_rate_padding_counterexample :
    ∃ block : Nat,
      ∃ code : CapabilityResponseBlockCode bottleneckGraph sig (1 / 10) block,
        ∃ rate : ℚ,
          binaryDecisionPerUseRate < rate ∧
          rate ≤ (Fintype.card code.Message : ℚ) / block ∧
          code.ZeroError := by
  let code := capabilityResponseBinaryBlockCode bottleneckGraph sig (1 / 10) 4
  refine ⟨4, code, 2, ?_, ?_, ?_⟩
  · norm_num [binaryDecisionPerUseRate]
  · rw [capabilityResponseBinaryBlockCode_message_card]
    norm_num
  · exact capabilityResponseBinaryBlockCode_zeroError
      bottleneckGraph sig (1 / 10) 4 (by norm_num) (by native_decide)

end GovGraph

end Legitimacy
