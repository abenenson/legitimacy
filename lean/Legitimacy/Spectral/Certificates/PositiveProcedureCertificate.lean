/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Diagnostics.Graph
import Legitimacy.Spectral.Channels.CStarChannelBridge

/-!
# Positive-procedure certificates below the capability threshold

This module is the constructive companion to the `C_star` forcing surface.  It
packages the data needed to read a governance threshold from a concrete finite
channel and exposes the well-conditioned class over which a certificate can be
extracted.
-/

set_option autoImplicit false

namespace Legitimacy

open MeasureTheory ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Finite α] [Finite β]
variable {n : Nat} [NeZero n]

/-- Kernel-level data for the positive procedure.

The channel is kept as data, while the graph, signal, and tolerance define the
spectral `C_star` threshold that the channel must calibrate to. -/
structure CapacityKernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [Finite β] (n : Nat) [NeZero n] where
  G : GovGraph ℚ n
  s : Fin n → ℚ
  δ : ℚ
  channel : GovernanceChannel α β

/-- The exact threshold read from a capacity kernel. -/
noncomputable def CapacityKernel.C_star (K : CapacityKernel α β n) : ℚ :=
  Legitimacy.C_star K.G K.s K.δ

/-- Well-conditioned kernels for the positive procedure.

The predicate consumes the non-decorative ingredients needed by the existing
`C_star` bridge: positive tolerance, positive graph CV, and an exact finite
channel-capacity calibration whose rational capacity value is the graph CV.
It does not assume any downstream governance certificate. -/
structure WellConditionedForCapacity (K : CapacityKernel α β n) where
  tolerance_pos : 0 < K.δ
  cv_pos : 0 < K.G.cv K.s
  exact_capacity :
    GovernanceChannel.CStarExactCapacityCertificate K.channel K.G K.s

/-- The diagnostic named by a positive-procedure certificate. -/
inductive PreservedDiagnostic where
  | consistency
  | solidarity
  | monotonicity
  deriving DecidableEq, Repr

/-- Exact channel-capacity identity consumed by positive-procedure certificates. -/
theorem WellConditionedForCapacity.capacity_threshold
    {K : CapacityKernel α β n} (hK : WellConditionedForCapacity K) :
    0 < ChannelCapacity.channelCapacity K.channel.kernel ∧
      (K.C_star : ℝ) =
        (K.δ : ℝ) / ChannelCapacity.channelCapacity K.channel.kernel := by
  simpa [CapacityKernel.C_star] using
    GovernanceChannel.finite_capacity_implies_C_star_threshold
      K.channel K.G K.s K.δ hK.exact_capacity

/-- Constructive certificate extracted below the calibrated `C_star` boundary.

In the exact finite-channel substrate, every strict subcritical scale has the
same downward persistence that earlier drafts attached to a boundary-near
solidarity name: every smaller positive scale is also denied and has no
spectral violation witness. The exact extractor therefore returns consistency
throughout the strict subcritical interval and monotonicity at the boundary.
Both constructors carry the exact capacity identity extracted from the
well-conditioned kernel. -/
inductive PositiveProcedureCertificate (K : CapacityKernel α β n) (c : ℚ) where
  | consistency
      (capacity_pos : 0 < c)
      (below_threshold : c < K.C_star)
      (verdict :
        K.G.capabilityResponse K.s K.δ c = BinaryDecision.Deny)
      (no_violation : ¬ K.G.spViolation K.s (K.δ / c))
      (lower_scales_deny :
        ∀ C : ℚ, 0 < C → C ≤ c →
          K.G.capabilityResponse K.s K.δ C = BinaryDecision.Deny)
      (lower_scales_no_violation :
        ∀ C : ℚ, 0 < C → C ≤ c →
          ¬ K.G.spViolation K.s (K.δ / C))
      (capacity_threshold :
        (K.C_star : ℝ) =
          (K.δ : ℝ) / ChannelCapacity.channelCapacity K.channel.kernel)
  | monotonicity
      (at_threshold : c = K.C_star)
      (verdict :
        K.G.capabilityResponse K.s K.δ c = BinaryDecision.Permit)
      (upper_scales_permit :
        ∀ C : ℚ, K.C_star ≤ C →
          K.G.capabilityResponse K.s K.δ C = BinaryDecision.Permit)
      (capacity_threshold :
        (K.C_star : ℝ) =
          (K.δ : ℝ) / ChannelCapacity.channelCapacity K.channel.kernel)

namespace PositiveProcedureCertificate

/-- The diagnostic selected by a positive-procedure certificate. -/
def kind {K : CapacityKernel α β n} {c : ℚ} :
    PositiveProcedureCertificate K c → PreservedDiagnostic
  | consistency .. => PreservedDiagnostic.consistency
  | monotonicity .. => PreservedDiagnostic.monotonicity

/-- Semantic reflection from all-profile binary consistency counterexamples
back into the fixed spectral profile carried by a capacity kernel.

This is the profile-uniform substrate missing from the bare spectral
certificate: every binary graph consistency counterexample must emit a
positive spectral violation at some scale already covered by the strict
subcritical certificate's lower-scale no-violation field. -/
structure GraphConsistencySpectralReflection
    (K : CapacityKernel α β n) (c : ℚ) (graph : GovernanceGraph) : Prop where
  counterexample_reflects_violation :
    ∀ (claims : List ClaimQ) (k j : ClaimantId),
      InClaims k claims →
      InClaims j claims →
      k ≠ j →
      ClaimsDistinct claims →
      graphDecide graph claims k = BinaryDecision.Deny →
      graphDecide graph claims j ≠
        graphDecide graph (removeClaimGraph k claims) j →
      ∃ C : ℚ, 0 < C ∧ C ≤ c ∧ K.G.spViolation K.s (K.δ / C)

/-- Legacy semantic carrier for callers that directly supply graph-level
diagnostic interpretations of one spectral positive-procedure certificate.

The consistency path now has the stronger
`GraphConsistencySpectralReflection` bridge: all-profile counterexamples are
reflected into spectral violations covered by the certificate. This carrier
remains for monotonicity and for legacy direct-interpretation callers. -/
structure GraphDiagnosticCarrier (K : CapacityKernel α β n) (c : ℚ)
    (graph : GovernanceGraph) : Prop where
  /-- The graph must make a same-claimant decision distinction across valid
  profiles, ruling out claimant-constant witnesses. -/
  nontrivial :
    ∃ (claims claims' : List ClaimQ) (k : ClaimantId),
      InClaims k claims ∧
      InClaims k claims' ∧
      ClaimsDistinct claims ∧
      ClaimsDistinct claims' ∧
      graphDecide graph claims k ≠ graphDecide graph claims' k
  consistency_from_exact_subcritical :
    WellConditionedForCapacity K →
    0 < c →
    c < K.C_star →
    K.G.capabilityResponse K.s K.δ c = BinaryDecision.Deny →
    ¬ K.G.spViolation K.s (K.δ / c) →
    (∀ C : ℚ, 0 < C → C ≤ c →
      K.G.capabilityResponse K.s K.δ C = BinaryDecision.Deny) →
    (∀ C : ℚ, 0 < C → C ≤ c →
      ¬ K.G.spViolation K.s (K.δ / C)) →
    GraphConsistency graph
  monotonicity_from_boundary :
    WellConditionedForCapacity K →
    c = K.C_star →
    K.G.capabilityResponse K.s K.δ c = BinaryDecision.Permit →
    (∀ C : ℚ, K.C_star ≤ C →
      K.G.capabilityResponse K.s K.δ C = BinaryDecision.Permit) →
    GraphMonotonicity graph

/-- Semantic bridge from an exact-case consistency certificate to the
all-profile graph-level consistency axiom. The proof consumes the certificate's
lower-scale no-violation field and a profile-uniform reflection theorem from
binary consistency counterexamples back to fixed-profile spectral violations. -/
theorem kind_consistency_to_GraphConsistency
    {K : CapacityKernel α β n} {c : ℚ} {graph : GovernanceGraph}
    (hreflection : GraphConsistencySpectralReflection K c graph)
    {cert : PositiveProcedureCertificate K c}
    (hkind : cert.kind = PreservedDiagnostic.consistency) :
    GraphConsistency graph := by
  cases cert with
  | consistency capacity_pos below_threshold verdict no_violation
      lower_scales_deny lower_scales_no_violation capacity_threshold =>
      intro claims k j hk hj hkj hdistinct hdeny
      by_contra hchanged
      rcases hreflection.counterexample_reflects_violation
        claims k j hk hj hkj hdistinct hdeny hchanged with
        ⟨C, hCpos, hCle, hviolation⟩
      exact lower_scales_no_violation C hCpos hCle hviolation
  | monotonicity =>
      simp [kind] at hkind

/-- Legacy conditional bridge through a direct graph-diagnostic carrier.
New consistency users should prefer `GraphConsistencySpectralReflection`,
which reflects all-profile counterexamples into the spectral lower-scale
no-violation range instead of assuming `GraphConsistency` outright. -/
theorem kind_consistency_to_GraphConsistency_of_diagnosticCarrier
    {K : CapacityKernel α β n} {c : ℚ} {graph : GovernanceGraph}
    (hK : WellConditionedForCapacity K)
    (hcarrier : GraphDiagnosticCarrier K c graph)
    {cert : PositiveProcedureCertificate K c}
    (hkind : cert.kind = PreservedDiagnostic.consistency) :
    GraphConsistency graph := by
  cases cert with
  | consistency capacity_pos below_threshold verdict no_violation
      lower_scales_deny lower_scales_no_violation capacity_threshold =>
      exact hcarrier.consistency_from_exact_subcritical hK capacity_pos
        below_threshold verdict no_violation lower_scales_deny
        lower_scales_no_violation
  | monotonicity =>
      simp [kind] at hkind

/-- Conditional bridge from a boundary certificate to the graph-level
monotonicity axiom. -/
theorem kind_monotonicity_to_GraphMonotonicity
    {K : CapacityKernel α β n} {c : ℚ} {graph : GovernanceGraph}
    (hK : WellConditionedForCapacity K)
    (hcarrier : GraphDiagnosticCarrier K c graph)
    {cert : PositiveProcedureCertificate K c}
    (hkind : cert.kind = PreservedDiagnostic.monotonicity) :
    GraphMonotonicity graph := by
  cases cert with
  | consistency =>
      simp [kind] at hkind
  | monotonicity at_threshold verdict upper_scales_permit capacity_threshold =>
      exact hcarrier.monotonicity_from_boundary hK at_threshold verdict
        upper_scales_permit

end PositiveProcedureCertificate

/-- Exact-case downward persistence is not boundary-near: every strict
subcritical scale has denied, no-violation lower scales under the
well-conditioned capacity hypotheses. This theorem records why the exact
substrate cannot honestly distinguish the reserved solidarity name by the
`C*/2` split alone. -/
theorem strictSubcritical_downward_persistence
    (K : CapacityKernel α β n) (hK : WellConditionedForCapacity K)
    (c : ℚ) (hc : c < K.C_star) :
    (∀ C : ℚ, 0 < C → C ≤ c →
        K.G.capabilityResponse K.s K.δ C = BinaryDecision.Deny) ∧
      (∀ C : ℚ, 0 < C → C ≤ c →
        ¬ K.G.spViolation K.s (K.δ / C)) := by
  have hthreshold := K.G.capabilityResponse_threshold K.s K.δ
    hK.tolerance_pos hK.cv_pos
  constructor
  · intro C hCpos hC
    exact hthreshold.1 C hCpos (by
      have hC_lt : C < K.C_star := lt_of_le_of_lt hC hc
      simpa [CapacityKernel.C_star] using hC_lt)
  · intro C hCpos hC
    exact (C_star_exists K.G K.s K.δ hK.tolerance_pos hK.cv_pos).1
      C hCpos (by
        have hC_lt : C < K.C_star := lt_of_le_of_lt hC hc
        simpa [CapacityKernel.C_star] using hC_lt)

/-- Extract the governance certificate for a positive scale at or below the
calibrated `C_star` boundary. -/
noncomputable def governance_certificate
    (K : CapacityKernel α β n) (hK : WellConditionedForCapacity K)
    (c : ℚ) (hcpos : 0 < c) (hc : c ≤ K.C_star) :
    PositiveProcedureCertificate K c := by
  classical
  have hcap := hK.capacity_threshold
  have hthreshold := K.G.capabilityResponse_threshold K.s K.δ
    hK.tolerance_pos hK.cv_pos
  by_cases hlt : c < K.C_star
  · have hdeny :
        K.G.capabilityResponse K.s K.δ c = BinaryDecision.Deny := by
      exact hthreshold.1 c hcpos (by simpa [CapacityKernel.C_star] using hlt)
    have hno :
        ¬ K.G.spViolation K.s (K.δ / c) := by
      exact (C_star_exists K.G K.s K.δ hK.tolerance_pos hK.cv_pos).1
        c hcpos (by simpa [CapacityKernel.C_star] using hlt)
    have hpersist := strictSubcritical_downward_persistence K hK c hlt
    exact PositiveProcedureCertificate.consistency
      hcpos hlt hdeny hno hpersist.1 hpersist.2 hcap.2
  · have hle_boundary : K.C_star ≤ c := le_of_not_gt hlt
    have heq : c = K.C_star := le_antisymm hc hle_boundary
    have hpermit :
        K.G.capabilityResponse K.s K.δ c = BinaryDecision.Permit := by
      rw [heq]
      exact hthreshold.2 (K.C_star) (by simp [CapacityKernel.C_star])
    have hupper :
        ∀ C : ℚ, K.C_star ≤ C →
          K.G.capabilityResponse K.s K.δ C = BinaryDecision.Permit := by
      intro C hC
      exact hthreshold.2 C (by simpa [CapacityKernel.C_star] using hC)
    exact PositiveProcedureCertificate.monotonicity heq hpermit hupper hcap.2

/-- Positive-procedure theorem: every positive capacity scale at or below the
calibrated threshold has an explicit exact-case certificate. The extractor
returns consistency throughout the strict subcritical interval and monotonicity
at the boundary. -/
theorem governance_certificate_constructible
    (K : CapacityKernel α β n) (hK : WellConditionedForCapacity K)
    (c : ℚ) (hcpos : 0 < c) (hc : c ≤ K.C_star) :
    ∃ cert : PositiveProcedureCertificate K c,
      cert.kind = PreservedDiagnostic.consistency ∨
        cert.kind = PreservedDiagnostic.monotonicity := by
  classical
  refine ⟨governance_certificate K hK c hcpos hc, ?_⟩
  unfold governance_certificate
  by_cases hlt : c < K.C_star
  · simp [hlt, PositiveProcedureCertificate.kind]
  · simp [hlt, PositiveProcedureCertificate.kind]

namespace PositiveProcedureExamples

/-- Concrete capacity kernel built from the half-scale uniform-triangle erasure
calibration. -/
noncomputable def concreteHalfNoisyKernel :
    CapacityKernel BinaryDecision (Option BinaryDecision) 3 where
  G := uniTriGraph
  s := halfSig
  δ := 1 / 10
  channel := GovernanceChannel.concreteHalfNoisyCStarCalibration.channel

/-- The concrete half-scale erasure-channel kernel is in the well-conditioned
class. -/
noncomputable def concreteHalfNoisyKernel_wellConditioned :
    WellConditionedForCapacity concreteHalfNoisyKernel := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [concreteHalfNoisyKernel]
  · simpa [concreteHalfNoisyKernel] using
      GovernanceChannel.uniTriGraph_cv_halfSig_pos
  · simpa [concreteHalfNoisyKernel] using
      GovernanceChannel.ConcreteNoisyCStarCalibration.toExactCapacityCertificate
        GovernanceChannel.concreteHalfNoisyCStarCalibration
        GovernanceChannel.uniTriGraph_cv_halfSig_pos

/-- The concrete half-scale uniform-triangle threshold is `1 / 5`. -/
theorem concreteHalfNoisyKernel_C_star :
    concreteHalfNoisyKernel.C_star = 1 / 5 := by
  simp [concreteHalfNoisyKernel, CapacityKernel.C_star, Legitimacy.C_star,
    GovernanceChannel.uniTriGraph_cv_halfSig]
  norm_num

/-- The worked scale `1 / 10` is strictly below the concrete threshold. -/
theorem concreteHalfNoisyKernel_one_tenth_lt_C_star :
    (1 / 10 : ℚ) < concreteHalfNoisyKernel.C_star := by
  rw [concreteHalfNoisyKernel_C_star]
  norm_num

/-- The boundary-near worked scale `19 / 100` is strictly below the concrete
threshold `1 / 5`. -/
theorem concreteHalfNoisyKernel_near_boundary_lt_C_star :
    (19 / 100 : ℚ) < concreteHalfNoisyKernel.C_star := by
  rw [concreteHalfNoisyKernel_C_star]
  norm_num

/-- Worked certificate extracted from the concrete half-scale erasure-channel
kernel at the subcritical scale `1 / 10`. -/
noncomputable def concreteHalfNoisyCertificateAtOneTenth :
    PositiveProcedureCertificate concreteHalfNoisyKernel (1 / 10) :=
  governance_certificate
    concreteHalfNoisyKernel
    concreteHalfNoisyKernel_wellConditioned
    (1 / 10)
    (by norm_num)
    (by
      rw [concreteHalfNoisyKernel_C_star]
      norm_num)

/-- Reading the worked certificate selects the consistency-side diagnostic. -/
theorem concreteHalfNoisyCertificateAtOneTenth_kind :
    concreteHalfNoisyCertificateAtOneTenth.kind =
      PreservedDiagnostic.consistency := by
  unfold concreteHalfNoisyCertificateAtOneTenth governance_certificate
  have hlt : (1 / 10 : ℚ) < concreteHalfNoisyKernel.C_star :=
    concreteHalfNoisyKernel_one_tenth_lt_C_star
  rw [dif_pos hlt]
  simp [PositiveProcedureCertificate.kind]

/-- The concrete worked verdict at `c = 1 / 10 < C*` is denial, with no
effective spectral-violation witness. -/
theorem concreteHalfNoisyCertificateAtOneTenth_verdict_and_no_violation :
    uniTriGraph.capabilityResponse halfSig (1 / 10) (1 / 10) =
        BinaryDecision.Deny ∧
      ¬ uniTriGraph.spViolation halfSig ((1 / 10) / (1 / 10)) := by
  have hthreshold := uniTriGraph.capabilityResponse_threshold halfSig
    (1 / 10) (by norm_num) GovernanceChannel.uniTriGraph_cv_halfSig_pos
  have hdeny :
      uniTriGraph.capabilityResponse halfSig (1 / 10) (1 / 10) =
        BinaryDecision.Deny := by
    exact hthreshold.1 (1 / 10) (by norm_num) (by
      simpa [CapacityKernel.C_star, concreteHalfNoisyKernel_C_star,
        concreteHalfNoisyKernel]
        using concreteHalfNoisyKernel_one_tenth_lt_C_star)
  have hno :
      ¬ uniTriGraph.spViolation halfSig ((1 / 10) / (1 / 10)) := by
    exact (C_star_exists uniTriGraph halfSig (1 / 10)
      (by norm_num) GovernanceChannel.uniTriGraph_cv_halfSig_pos).1
        (1 / 10) (by norm_num) (by
          simpa [CapacityKernel.C_star, concreteHalfNoisyKernel_C_star,
            concreteHalfNoisyKernel]
            using concreteHalfNoisyKernel_one_tenth_lt_C_star)
  exact ⟨hdeny, hno⟩

/-- Boundary-near worked certificate extracted from the concrete half-scale
erasure-channel kernel at `c = 19 / 100`, just below `C* = 1 / 5`. -/
noncomputable def concreteHalfNoisyCertificateNearBoundary :
    PositiveProcedureCertificate concreteHalfNoisyKernel (19 / 100) :=
  governance_certificate
    concreteHalfNoisyKernel
    concreteHalfNoisyKernel_wellConditioned
    (19 / 100)
    (by norm_num)
    (by
      rw [concreteHalfNoisyKernel_C_star]
      norm_num)

/-- Reading the boundary-near worked certificate selects the consistency-side
diagnostic in the exact finite-channel substrate. -/
theorem concreteHalfNoisyCertificateNearBoundary_kind :
    concreteHalfNoisyCertificateNearBoundary.kind =
      PreservedDiagnostic.consistency := by
  unfold concreteHalfNoisyCertificateNearBoundary governance_certificate
  have hlt : (19 / 100 : ℚ) < concreteHalfNoisyKernel.C_star :=
    concreteHalfNoisyKernel_near_boundary_lt_C_star
  rw [dif_pos hlt]
  simp [PositiveProcedureCertificate.kind]

/-- The boundary-near worked verdict at `c = 19 / 100 < C*` is denial, with no
effective spectral-violation witness. The proof consumes the strict `c < C*`
threshold fact. -/
theorem concreteHalfNoisyCertificateNearBoundary_verdict_and_no_violation :
    uniTriGraph.capabilityResponse halfSig (1 / 10) (19 / 100) =
        BinaryDecision.Deny ∧
      ¬ uniTriGraph.spViolation halfSig ((1 / 10) / (19 / 100)) := by
  have hthreshold := uniTriGraph.capabilityResponse_threshold halfSig
    (1 / 10) (by norm_num) GovernanceChannel.uniTriGraph_cv_halfSig_pos
  have hdeny :
      uniTriGraph.capabilityResponse halfSig (1 / 10) (19 / 100) =
        BinaryDecision.Deny := by
    exact hthreshold.1 (19 / 100) (by norm_num) (by
      simpa [CapacityKernel.C_star, concreteHalfNoisyKernel_C_star,
        concreteHalfNoisyKernel]
        using concreteHalfNoisyKernel_near_boundary_lt_C_star)
  have hno :
      ¬ uniTriGraph.spViolation halfSig ((1 / 10) / (19 / 100)) := by
    exact (C_star_exists uniTriGraph halfSig (1 / 10)
      (by norm_num) GovernanceChannel.uniTriGraph_cv_halfSig_pos).1
        (19 / 100) (by norm_num) (by
          simpa [CapacityKernel.C_star, concreteHalfNoisyKernel_C_star,
            concreteHalfNoisyKernel]
            using concreteHalfNoisyKernel_near_boundary_lt_C_star)
  exact ⟨hdeny, hno⟩

end PositiveProcedureExamples

end Legitimacy
