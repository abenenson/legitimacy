/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Spectral.Channels.ConcreteNoisyChannel
import Mathlib.Data.Nat.Log

/-!
# Critical capability calibration bridge

This module records the strongest bridge currently supported by the spectral
layer.

The finite low-noise binary channel from `NoisyGovernanceCapacity` has a
Shannon capacity in the imported `ChannelCapacity` sense, and
`NoisyThresholdClosedForm` now computes that BSC capacity as
`log 2 - Real.binEntropy η`. That capacity is still only a property of the
chosen kernel. A fixed noisy-threshold channel therefore cannot be the
graph-varying quantity `C_star G s δ`.

The upgraded bridge below is for graph-parameterized finite channels equipped
with an explicit rational-budget calibration certificate. The generic
certificate remains available for abstract calibrated channels, but the concrete
erasure channel now has a derived capacity equality
`concreteNoisyChannel_channelCapacity_eq_cv`: its capacity value is computed
from the constructed kernel before the graph-specific calibration is applied by
`ConcreteNoisyCStarCalibration.capacity_eq_cv`. The BSC companion calibration
uses the same discipline: its capacity is derived from the noisy-threshold
kernel, while matching a graph's `cv` is isolated as a calibration equality.

What is available now is an exact operational bridge: using `cv` as the
local-sensitivity norm, the deterministic capability-response channel flips
from `Deny` to `Permit` exactly at `C_star`.
-/

set_option autoImplicit false

namespace Legitimacy

open MeasureTheory ProbabilityTheory

namespace GovGraph

variable {n : Nat}

/-- CV-calibrated capability response. At capability `C`, the channel answers
`Permit` precisely when the graph has a strategyproofness violation at the
effective perturbation scale `δ / C`. -/
noncomputable def capabilityResponse
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ C : ℚ) : BinaryDecision :=
  by
    classical
    exact
      if 0 < C ∧ G.spViolation s (δ / C) then
        BinaryDecision.Permit
      else
        BinaryDecision.Deny

/-- Deterministic channel view of `capabilityResponse`. The input alphabet is
the rational capability level; the output is the binary governance response. -/
noncomputable def asCapabilityResponseChannel
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) :
    GovernanceChannel ℚ BinaryDecision where
  kernel := Kernel.deterministic (fun C => G.capabilityResponse s δ C)
    (measurable_of_countable (fun C => G.capabilityResponse s δ C))
  isMarkov := by infer_instance

/-- Exact response characterization: for positive capabilities, the
CV-calibrated channel permits exactly at and above `C_star`. -/
theorem capabilityResponse_eq_permit_iff_C_star_le
    (G : GovGraph ℚ n) [NeZero n]
    (s : Fin n → ℚ) (δ C : ℚ) (hδ : 0 < δ)
    (hcv : 0 < G.cv s) (hC : 0 < C) :
    G.capabilityResponse s δ C = BinaryDecision.Permit ↔ C_star G s δ ≤ C := by
  classical
  constructor
  · intro hpermit
    unfold capabilityResponse at hpermit
    by_cases hresp : 0 < C ∧ G.spViolation s (δ / C)
    · by_contra hnot
      have hlt : C < C_star G s δ := lt_of_not_ge hnot
      have hno := (C_star_exists G s δ hδ hcv).1 C hC hlt
      exact hno hresp.2
    · simp [hresp] at hpermit
  · intro hle
    have hviol := (C_star_exists G s δ hδ hcv).2 C hle
    have hresp : 0 < C ∧ G.spViolation s (δ / C) := ⟨hC, hviol⟩
    unfold capabilityResponse
    simp [hresp]

/-- Achievability/converse form of the capability-response channel: every
positive capability below `C_star` is denied, and every capability at or above
`C_star` is permitted. -/
theorem capabilityResponse_threshold
    (G : GovGraph ℚ n) [NeZero n]
    (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hcv : 0 < G.cv s) :
    (∀ C : ℚ, 0 < C → C < C_star G s δ →
      G.capabilityResponse s δ C = BinaryDecision.Deny) ∧
    (∀ C : ℚ, C_star G s δ ≤ C →
      G.capabilityResponse s δ C = BinaryDecision.Permit) := by
  classical
  constructor
  · intro C hC hlt
    have hno := (C_star_exists G s δ hδ hcv).1 C hC hlt
    have hresp : ¬ (0 < C ∧ G.spViolation s (δ / C)) := fun h => hno h.2
    unfold capabilityResponse
    simp [hresp]
  · intro C hle
    have hCstar_pos : 0 < C_star G s δ := by
      simpa [C_star] using div_pos hδ hcv
    have hC : 0 < C := lt_of_lt_of_le hCstar_pos hle
    exact (G.capabilityResponse_eq_permit_iff_C_star_le s δ C hδ hcv hC).mpr hle

/-! ### CV quotient descent for `C_star` and capability response -/

/-- Spectral graphs are equivalent at signal `s` when they have the same
graph-wide consistency vulnerability. This is the exact invariant used by
`C_star`; it is deliberately not the decision-pipeline
`GovernanceGraphEquivalent` relation. -/
def CvEquivalent [NeZero n] (s : Fin n → ℚ) (G H : GovGraph ℚ n) : Prop :=
  G.cv s = H.cv s

/-- Setoid quotienting weighted spectral graphs by equality of `cv` at the
chosen signal. -/
def cvEquivalentSetoid (s : Fin n → ℚ) [NeZero n] :
    Setoid (GovGraph ℚ n) where
  r := CvEquivalent s
  iseqv := by
    constructor
    · intro G
      rfl
    · intro G H h
      exact h.symm
    · intro G H K hGH hHK
      exact hGH.trans hHK

/-- Weighted spectral graph class at fixed signal, quotienting by the actual
invariant on which `C_star` depends. -/
abbrev CvClass (n : Nat) [NeZero n] (s : Fin n → ℚ) : Type :=
  Quotient (cvEquivalentSetoid (n := n) s)

/-- The spectral CV class represented by a weighted graph. -/
def cvClass (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) :
    CvClass n s :=
  Quotient.mk (cvEquivalentSetoid (n := n) s) G

/-- Equal spectral CV gives equal reciprocal critical capability. -/
theorem C_star_eq_of_cv_eq
    (G H : GovGraph ℚ n) [NeZero n]
    (s : Fin n → ℚ) (δ : ℚ)
    (hcv : G.cv s = H.cv s) :
    C_star G s δ = C_star H s δ := by
  simp [C_star, hcv]

/-- `C_star` descends to the spectral CV quotient. -/
noncomputable def C_starClass
    [NeZero n] (s : Fin n → ℚ) (δ : ℚ) :
    CvClass n s → ℚ :=
  Quotient.lift (fun G : GovGraph ℚ n => C_star G s δ) (by
    intro G H hcv
    exact C_star_eq_of_cv_eq G H s δ hcv)

@[simp]
lemma C_starClass_mk
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ) :
    C_starClass s δ (cvClass G s) = C_star G s δ := by
  rfl

/-- The CV value itself descends to the spectral CV quotient. -/
noncomputable def cvValueClass [NeZero n] (s : Fin n → ℚ) :
    CvClass n s → ℚ :=
  Quotient.lift (fun G : GovGraph ℚ n => G.cv s) (by
    intro G H hcv
    exact hcv)

@[simp]
lemma cvValueClass_mk
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) :
    cvValueClass s (cvClass G s) = G.cv s := by
  rfl

/-- Equal spectral CV gives equal deterministic capability response at every
receiver capability. -/
theorem capabilityResponse_eq_of_cv_eq
    (G H : GovGraph ℚ n) [NeZero n]
    (s : Fin n → ℚ) (δ C : ℚ)
    (hcv : G.cv s = H.cv s) :
    G.capabilityResponse s δ C = H.capabilityResponse s δ C := by
  classical
  have hviol :
      G.spViolation s (δ / C) ↔ H.spViolation s (δ / C) := by
    rw [G.spViolation_iff_le_cv, H.spViolation_iff_le_cv, hcv]
  have hguard :
      (0 < C ∧ G.spViolation s (δ / C)) =
        (0 < C ∧ H.spViolation s (δ / C)) := by
    exact propext (and_congr Iff.rfl hviol)
  by_cases hGguard : 0 < C ∧ G.spViolation s (δ / C)
  · have hHguard : 0 < C ∧ H.spViolation s (δ / C) := by
      simpa [hguard] using hGguard
    simp [capabilityResponse, hGguard, hHguard]
  · have hHguard : ¬ (0 < C ∧ H.spViolation s (δ / C)) := by
      simpa [hguard] using hGguard
    simp [capabilityResponse, hGguard, hHguard]

/-- Deterministic capability response descends to the spectral CV quotient. -/
noncomputable def capabilityResponseClass
    [NeZero n] (s : Fin n → ℚ) (δ C : ℚ) :
    CvClass n s → BinaryDecision :=
  Quotient.lift (fun G : GovGraph ℚ n => G.capabilityResponse s δ C) (by
    intro G H hcv
    exact capabilityResponse_eq_of_cv_eq G H s δ C hcv)

@[simp]
lemma capabilityResponseClass_mk
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ C : ℚ) :
    capabilityResponseClass s δ C (cvClass G s) =
      G.capabilityResponse s δ C := by
  rfl

/-- Quotient-level response characterization: on spectral CV classes, the
deterministic channel permits exactly when receiver capability clears the
class-level `C_star`. -/
theorem capabilityResponseClass_eq_permit_iff_C_starClass_le
    [NeZero n] (s : Fin n → ℚ) (K : CvClass n s) (δ C : ℚ)
    (hδ : 0 < δ) (hcv : 0 < cvValueClass s K) (hC : 0 < C) :
    capabilityResponseClass s δ C K = BinaryDecision.Permit ↔
      C_starClass s δ K ≤ C := by
  revert hcv
  refine Quotient.inductionOn K ?_
  intro G hcv
  have hcvG : 0 < G.cv s := by
    simpa [cvValueClass]
  exact G.capabilityResponse_eq_permit_iff_C_star_le s δ C hδ
    hcvG hC

/-! ### Zero-error block coding shape for capability response -/

/-- Coordinatewise block use of the deterministic capability-response channel. -/
noncomputable def capabilityResponseBlock
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    {block : Nat} (x : Fin block → ℚ) :
    Fin block → BinaryDecision :=
  fun i => G.capabilityResponse s δ (x i)

/-- A block code for repeated deterministic capability-response uses. This is
the finite zero-error substrate available here; it is not a stochastic
Shannon-code/error-probability layer. -/
structure CapabilityResponseBlockCode
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (block : Nat) where
  Message : Type
  [messageFintype : Fintype Message]
  encoder : Message → Fin block → ℚ
  decoder : (Fin block → BinaryDecision) → Message

attribute [instance] CapabilityResponseBlockCode.messageFintype

namespace CapabilityResponseBlockCode

variable [NeZero n] {G : GovGraph ℚ n} {s : Fin n → ℚ}
  {δ : ℚ} {block : Nat}

/-- The realized binary output word of a block code. -/
noncomputable def output
    (code : CapabilityResponseBlockCode G s δ block) (m : code.Message) :
    Fin block → BinaryDecision :=
  capabilityResponseBlock G s δ (code.encoder m)

/-- Zero-error decoding for the deterministic repeated channel. -/
def ZeroError (code : CapabilityResponseBlockCode G s δ block) : Prop :=
  ∀ m : code.Message, code.decoder (code.output m) = m

/-- A zero-error block code injects messages into binary output words. -/
theorem output_injective_of_zeroError
    (code : CapabilityResponseBlockCode G s δ block)
    (hzero : code.ZeroError) :
    Function.Injective code.output := by
  intro m₁ m₂ h
  have h₁ := hzero m₁
  have h₂ := hzero m₂
  calc
    m₁ = code.decoder (code.output m₁) := h₁.symm
    _ = code.decoder (code.output m₂) := by rw [h]
    _ = m₂ := h₂

/-- Converse for the available finite block-code substrate: a zero-error code
cannot carry more messages than the binary output alphabet has words. -/
theorem card_message_le_output_words_of_zeroError
    (code : CapabilityResponseBlockCode G s δ block)
    (hzero : code.ZeroError) :
    Fintype.card code.Message ≤
      Fintype.card (Fin block → BinaryDecision) := by
  classical
  exact Fintype.card_le_of_injective code.output
    (output_injective_of_zeroError code hzero)

/-- Cardinality converse in contrapositive form. -/
theorem not_zeroError_of_output_words_lt_card_message
    (code : CapabilityResponseBlockCode G s δ block)
    (hcard :
      Fintype.card (Fin block → BinaryDecision) <
        Fintype.card code.Message) :
    ¬ code.ZeroError := by
  intro hzero
  exact not_lt_of_ge
    (card_message_le_output_words_of_zeroError code hzero) hcard

/-- If a code has too many messages for the binary output words, some message
is decoded incorrectly. This is the current deterministic substitute for a
positive error-probability lower bound. -/
theorem exists_decoding_error_of_output_words_lt_card_message
    (code : CapabilityResponseBlockCode G s δ block)
    (hcard :
      Fintype.card (Fin block → BinaryDecision) <
        Fintype.card code.Message) :
    ∃ m : code.Message, code.decoder (code.output m) ≠ m := by
  classical
  by_contra hnone
  exact not_zeroError_of_output_words_lt_card_message code hcard
    (fun m => by
      by_contra hbad
      exact hnone ⟨m, hbad⟩)

end CapabilityResponseBlockCode

private lemma binaryDecision_card : Fintype.card BinaryDecision = 2 := by
  -- native_decide: finite rational spectral certificate checks over concrete matrices/signals.
  native_decide

/-- The output alphabet of `block` deterministic binary channel uses has
`2^block` words. -/
theorem capabilityResponse_output_word_card (block : Nat) :
    Fintype.card (Fin block → BinaryDecision) = 2 ^ block := by
  rw [Fintype.card_fun, Fintype.card_fin, binaryDecision_card]

/-- A concrete zero-error binary block code: capabilities below `C_star` encode
`Deny`, and capability exactly at `C_star` encodes `Permit`. -/
noncomputable def capabilityResponseBinaryBlockCode
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (block : Nat) :
    CapabilityResponseBlockCode G s δ block where
  Message := Fin block → BinaryDecision
  encoder := fun m i =>
    if m i = BinaryDecision.Permit then
      C_star G s δ
    else
      C_star G s δ / 2
  decoder := id

/-- Achievability in the zero-error block-code substrate: whenever `δ > 0`
and the graph has positive CV, the deterministic response channel carries one
binary decision per use with zero block error. -/
theorem capabilityResponseBinaryBlockCode_zeroError
    (G : GovGraph ℚ n) [NeZero n]
    (s : Fin n → ℚ) (δ : ℚ) (block : Nat)
    (hδ : 0 < δ) (hcv : 0 < G.cv s) :
    (capabilityResponseBinaryBlockCode G s δ block).ZeroError := by
  classical
  intro m
  funext i
  have hCstar_pos : 0 < C_star G s δ := by
    simpa [C_star] using div_pos hδ hcv
  by_cases hm : m i = BinaryDecision.Permit
  · have hpermit :
        G.capabilityResponse s δ (C_star G s δ) =
          BinaryDecision.Permit :=
      (G.capabilityResponse_eq_permit_iff_C_star_le
        s δ (C_star G s δ) hδ hcv hCstar_pos).mpr le_rfl
    simp [CapabilityResponseBlockCode.output, capabilityResponseBlock,
      capabilityResponseBinaryBlockCode, hm, hpermit]
  · have hmdeny : m i = BinaryDecision.Deny := by
      cases hmi : m i with
      | Permit => exact False.elim (hm hmi)
      | Deny => rfl
    have hhalf_pos : 0 < C_star G s δ / 2 := by
      linarith
    have hhalf_lt : C_star G s δ / 2 < C_star G s δ := by
      linarith
    have hdeny :
        G.capabilityResponse s δ (C_star G s δ / 2) =
          BinaryDecision.Deny :=
      (G.capabilityResponse_threshold s δ hδ hcv).1
        (C_star G s δ / 2) hhalf_pos hhalf_lt
    simp [CapabilityResponseBlockCode.output, capabilityResponseBlock,
      capabilityResponseBinaryBlockCode, hmdeny, hdeny]

/-- The concrete binary block code has exactly the full binary output alphabet
as its message set. -/
theorem capabilityResponseBinaryBlockCode_message_card
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (block : Nat) :
    Fintype.card (capabilityResponseBinaryBlockCode G s δ block).Message =
      2 ^ block := by
  change Fintype.card (Fin block → BinaryDecision) = 2 ^ block
  exact capabilityResponse_output_word_card block

/-- The base-2 logarithm of the concrete binary block code's message
cardinality is the block length. -/
theorem capabilityResponseBinaryBlockCode_log2_message_card
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (block : Nat) :
    Nat.log2
        (Fintype.card (capabilityResponseBinaryBlockCode G s δ block).Message) =
      block := by
  rw [capabilityResponseBinaryBlockCode_message_card, Nat.log2_eq_log_two]
  exact Nat.log_pow Nat.one_lt_two block

/-- Rate parameter for the concrete binary zero-error construction. The value
is one binary decision per channel use; it is not a Shannon capacity identity
for `C_star`. -/
def binaryDecisionPerUseRate : ℚ := 1

/-- Any rational target rate strictly below one binary decision per use is
achievable by the concrete zero-error block code at every positive block
length. The rate claim is explicit: the code has `2^block` messages, and the
target rate times block length is strictly below the base-2 message logarithm. -/
theorem capabilityResponse_zeroError_achievable_below_binary_rate
    (G : GovGraph ℚ n) [NeZero n]
    (s : Fin n → ℚ) (δ R : ℚ)
    (hδ : 0 < δ) (hcv : 0 < G.cv s)
    (hR : R < binaryDecisionPerUseRate) :
    ∀ block : Nat, 0 < block →
      ∃ code : CapabilityResponseBlockCode G s δ block,
        code.ZeroError ∧
        Fintype.card code.Message = 2 ^ block ∧
        R * (block : ℚ) <
          (Nat.log2 (Fintype.card code.Message) : ℚ) := by
  intro block hblock
  let code := capabilityResponseBinaryBlockCode G s δ block
  have hzero : code.ZeroError :=
    capabilityResponseBinaryBlockCode_zeroError G s δ block hδ hcv
  have hcard : Fintype.card code.Message = 2 ^ block :=
    capabilityResponseBinaryBlockCode_message_card G s δ block
  have hlog : Nat.log2 (Fintype.card code.Message) = block := by
    simpa [code] using
      capabilityResponseBinaryBlockCode_log2_message_card G s δ block
  have hR_one : R < 1 := by
    simpa [binaryDecisionPerUseRate] using hR
  have hblock_rat : 0 < (block : ℚ) := by
    exact_mod_cast hblock
  have hrate : R * (block : ℚ) < (block : ℚ) := by
    simpa using mul_lt_mul_of_pos_right hR_one hblock_rat
  refine ⟨code, hzero, hcard, ?_⟩
  simpa [hlog] using hrate

/-- Spectral sandwich for the CV-calibrated capability-response channel: the
expander-style lower bound controls the exact response threshold, and the
channel switches from denial to permission at that threshold. -/
theorem capabilityResponse_spectral_threshold_bound
    (G : GovGraph ℚ n) [NeZero n]
    (hn : 2 ≤ n)
    (s : Fin n → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hcv : 0 < G.cv s)
    (hmin : 0 < G.minRemovedDeg)
    (hsg : 0 < G.spectralGap hn)
    (hsg_le : ∀ i : Fin n, G.spectralGap hn ≤ Rat.cast (G.deg i)) :
    (δ : ℝ) * G.spectralGap hn / (((signalRange s : ℚ) : ℝ) * (G.maxDeg : ℝ)) ≤
      (C_star G s δ : ℝ) ∧
    (∀ C : ℚ, 0 < C → C < C_star G s δ →
      G.capabilityResponse s δ C = BinaryDecision.Deny) ∧
    (∀ C : ℚ, C_star G s δ ≤ C →
      G.capabilityResponse s δ C = BinaryDecision.Permit) := by
  refine ⟨governance_graph_C_star_expander_bound G hn s δ hδ hcv hmin hsg hsg_le, ?_⟩
  exact G.capabilityResponse_threshold s δ hδ hcv

end GovGraph

namespace GovernanceChannel

variable {n : Nat}

/-- Rational-budget calibration certificate for a graph/signal pair.

The channel may be noisy and finite, but it is not fixed independently of the
graph: the certificate identifies its imported `ChannelCapacity` value with a
rational budget that is no larger than the graph's CV. Concrete noisy-threshold
instances should use `ConcreteNoisyCStarCalibration`, where the channel-capacity
equality is derived from the constructed kernel and only graph calibration
remains as a hypothesis. -/
structure RationalBudgetCalibrationCertificate
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [Finite β]
    (c : GovernanceChannel α β)
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) where
  capacityValue : ℚ
  channelCapacity_eq :
    ChannelCapacity.channelCapacity c.kernel = (capacityValue : ℝ)
  capacity_pos : 0 < capacityValue
  capacity_le_cv : capacityValue ≤ G.cv s

/-- Exact finite capacity certificate calibrated to a graph/signal pair.
This is the graph-varying channel class where the rational capacity budget
characterizes `C_star`, rather than merely bounding it. Concrete noisy-channel
instances should prefer `concreteNoisyChannel_finite_capacity_implies_C_star_threshold`,
which derives the channel-capacity equality from the constructed noisy kernel. -/
structure CStarExactCapacityCertificate
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [Finite β]
    (c : GovernanceChannel α β)
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) where
  channelCapacity_eq :
    ChannelCapacity.channelCapacity c.kernel = (G.cv s : ℝ)
  capacity_pos : 0 < G.cv s

def CStarExactCapacityCertificate.capacityValue {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Finite α] [Finite β] {c : GovernanceChannel α β} {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ} (_cert : CStarExactCapacityCertificate c G s) : ℚ := G.cv s



/-- Exact calibration implies the weaker rational-budget calibration. -/
def CStarExactCapacityCertificate.toCalibrationCertificate
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [Finite β]
    {c : GovernanceChannel α β}
    {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
    (cert : CStarExactCapacityCertificate c G s) :
    RationalBudgetCalibrationCertificate c G s where
  capacityValue := cert.capacityValue
  channelCapacity_eq := cert.channelCapacity_eq
  capacity_pos := cert.capacity_pos
  capacity_le_cv := le_rfl

/-- A concrete noisy-channel calibration produces the exact
finite-capacity certificate expected by the generic `C_star` bridge. The
Shannon-capacity equality in this certificate is derived by
`concreteNoisyChannel_channelCapacity_eq_cv`, not supplied as a free equality
field for an arbitrary channel. -/
noncomputable def ConcreteNoisyCStarCalibration.toExactCapacityCertificate
    {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
    (cal : ConcreteNoisyCStarCalibration G s) (hcv : 0 < G.cv s) :
    CStarExactCapacityCertificate cal.channel G s where
  channelCapacity_eq := concreteNoisyChannel_channelCapacity_eq_cv cal
  capacity_pos := hcv

/-- Concrete noisy-channel capacity equality packaged as the exact finite
certificate for the graph-calibrated `C_star` bridge. -/
theorem concreteNoisyChannel_exact_capacity_certificate_eq
    {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
    (cal : ConcreteNoisyCStarCalibration G s) (hcv : 0 < G.cv s) :
    ChannelCapacity.channelCapacity cal.channel.kernel =
      ((cal.toExactCapacityCertificate hcv).capacityValue : ℝ) :=
  (cal.toExactCapacityCertificate hcv).channelCapacity_eq

/-- Capacity-to-`C_star` bridge for graph-calibrated finite channels: if the
certificate rational capacity value is no larger than graph CV, then it determines
an upper bound on the critical capability threshold. The certificate is a
calibration vehicle; use the concrete noisy-channel theorem below when the
channel is graph calibrated. -/
theorem channel_capacity_bounds_C_star
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [Finite β]
    (c : GovernanceChannel α β)
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (cert : RationalBudgetCalibrationCertificate c G s)
    (hδ : 0 ≤ δ) :
    (C_star G s δ : ℝ) ≤
      (δ : ℝ) / ChannelCapacity.channelCapacity c.kernel := by
  have hcapR_pos : (0 : ℝ) < (cert.capacityValue : ℝ) := by
    exact_mod_cast cert.capacity_pos
  have hcapR_le_cv : (cert.capacityValue : ℝ) ≤ (G.cv s : ℝ) := by
    exact_mod_cast cert.capacity_le_cv
  have hδR : (0 : ℝ) ≤ (δ : ℝ) := by
    exact_mod_cast hδ
  have hbound :
      (δ : ℝ) / (G.cv s : ℝ) ≤
        (δ : ℝ) / (cert.capacityValue : ℝ) :=
    div_le_div_of_nonneg_left hδR hcapR_pos hcapR_le_cv
  have hcap_eq_symm : (cert.capacityValue : ℝ) =
      ChannelCapacity.channelCapacity c.kernel := cert.channelCapacity_eq.symm
  simpa [C_star, hcap_eq_symm] using hbound

/-- Exact capacity-to-`C_star` bridge for graph-calibrated finite channels: a
positive finite certificate whose rational value is exactly graph CV
characterizes the critical capability threshold. The certificate is a
calibration vehicle; use the concrete noisy-channel theorem below when the
channel is graph calibrated. -/
theorem finite_capacity_implies_C_star_threshold
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [Finite β]
    (c : GovernanceChannel α β)
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (cert : CStarExactCapacityCertificate c G s) :
    0 < ChannelCapacity.channelCapacity c.kernel ∧
      (C_star G s δ : ℝ) =
        (δ : ℝ) / ChannelCapacity.channelCapacity c.kernel := by
  have hcapR_pos : (0 : ℝ) < (cert.capacityValue : ℝ) := by
    exact_mod_cast cert.capacity_pos
  have hchannel_pos : 0 < ChannelCapacity.channelCapacity c.kernel := by
    simpa [cert.channelCapacity_eq] using hcapR_pos
  have hchannel_eq_cv : ChannelCapacity.channelCapacity c.kernel = (G.cv s : ℝ) :=
    cert.channelCapacity_eq
  have hchannel_eq_cv_symm : (G.cv s : ℝ) =
      ChannelCapacity.channelCapacity c.kernel := hchannel_eq_cv.symm
  exact ⟨hchannel_pos, by simp [C_star, hchannel_eq_cv_symm]⟩

/-- A fixed low-noise binary channel cannot be the requested graph-derived
capacity bridge for the concrete spectral examples: its single Shannon capacity
value cannot equal both distinct concrete `C_star` values. -/
theorem fixed_noisyThreshold_capacity_not_concrete_C_star_bridge
    (η : NNReal) (hη : η < (1 / 2 : NNReal)) :
    ¬ (ChannelCapacity.channelCapacity (asNoisyThresholdChannel η hη).kernel =
        (C_star uniTriGraph sig (1 / 10) : ℝ) ∧
      ChannelCapacity.channelCapacity (asNoisyThresholdChannel η hη).kernel =
        (C_star asymTriGraph sig (1 / 10) : ℝ)) := by
  intro h
  have hsame :
      (C_star uniTriGraph sig (1 / 10) : ℝ) =
        (C_star asymTriGraph sig (1 / 10) : ℝ) := by
    exact h.1.symm.trans h.2
  have huni : (C_star uniTriGraph sig (1 / 10) : ℝ) = (1 / 10 : ℝ) := by
    norm_num [concrete_C_star_values.1]
  have hasym : (C_star asymTriGraph sig (1 / 10) : ℝ) = (3 / 40 : ℝ) := by
    norm_num [concrete_C_star_values.2.1]
  rw [huni, hasym] at hsame
  norm_num at hsame

/-- The exact-capacity value is a projection from the calibrated graph/signal,
not an independent field on the certificate. -/
theorem CStarExactCapacityCertificate_capacityValue_field_eq_projection
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [Finite β]
    {c : GovernanceChannel α β}
    {G : GovGraph ℚ n} [NeZero n] {s : Fin n → ℚ}
    (cert : CStarExactCapacityCertificate c G s) :
    cert.capacityValue = G.cv s :=
  rfl

end GovernanceChannel

end Legitimacy
