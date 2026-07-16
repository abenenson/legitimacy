/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Behavioral.ConstitutionalAILineage
import Legitimacy.Spectral.Certificates.PositiveProcedureCertificate

/-!
# Constitutional AI positive-procedure carrier

This module connects the capability-scaled Constitutional AI deployment
substrate to the positive-procedure certificate layer. Consistency is carried
by a profile-uniform reflection from every binary graph consistency
counterexample into the fixed spectral lower-scale no-violation range.
Monotonicity remains routed through the boundary semantic carrier.
-/

set_option autoImplicit false

namespace Legitimacy

open MeasureTheory ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Finite α] [Finite β]
variable {n : Nat} [NeZero n]

namespace ConstitutionalAICapacityLineage

/-- Capacity kernel obtained by reading the graph, signal, and tolerance from a
capability-scaled CAI deployment lineage while keeping the finite channel
explicit. -/
noncomputable def toCapacityKernel
    (L : ConstitutionalAICapacityLineage n)
    (channel : GovernanceChannel α β) :
    CapacityKernel α β n where
  G := L.lineage.G
  s := L.lineage.s
  δ := L.δ
  channel := channel

@[simp] lemma toCapacityKernel_C_star
    (L : ConstitutionalAICapacityLineage n)
    (channel : GovernanceChannel α β) :
    (L.toCapacityKernel channel).C_star = L.C_star := by
  rfl

end ConstitutionalAICapacityLineage

/-- Semantic data still required to interpret a CAI fixed-profile spectral
certificate as all-profile graph-diagnostic evidence. The consistency field is
not a direct `GraphConsistency` assumption: it reflects each all-profile
binary consistency counterexample into a spectral violation at a scale covered
by a strict-subcritical certificate. -/
structure ConstitutionalAIPositiveProcedureSemanticCarrier
    (L : ConstitutionalAICapacityLineage n) (c : ℚ)
    (graph : GovernanceGraph) : Prop where
  nontrivial :
    ∃ (claims claims' : List ClaimQ) (k : ClaimantId),
      InClaims k claims ∧
      InClaims k claims' ∧
      ClaimsDistinct claims ∧
      ClaimsDistinct claims' ∧
      graphDecide graph claims k ≠ graphDecide graph claims' k
  consistency_counterexample_reflects_violation :
    ∀ (claims : List ClaimQ) (k j : ClaimantId),
      InClaims k claims →
      InClaims j claims →
      k ≠ j →
      ClaimsDistinct claims →
      graphDecide graph claims k = BinaryDecision.Deny →
      graphDecide graph claims j ≠
        graphDecide graph (removeClaimGraph k claims) j →
      ∃ C : ℚ, 0 < C ∧ C ≤ c ∧
        L.lineage.G.spViolation L.lineage.s (L.δ / C)
  monotonicity_from_benign_boundary :
    (∀ (state : Fin n) (C : ℚ),
      L.lineage.claimClass.BenignClaim state → 0 < C →
        (L.capabilityResponse C = (L.lineage.policy state).toBinary ↔
          L.C_star ≤ C)) →
    GraphMonotonicity graph

/-- CAI-shaped profile-uniform consistency reflection for a positive-procedure
capacity kernel. -/
noncomputable def ConstitutionalAIPositiveProcedureConsistencyReflection
    (L : ConstitutionalAICapacityLineage n)
    (channel : GovernanceChannel α β) (c : ℚ)
    (graph : GovernanceGraph)
    (hsemantic :
      ConstitutionalAIPositiveProcedureSemanticCarrier L c graph) :
    PositiveProcedureCertificate.GraphConsistencySpectralReflection
      (L.toCapacityKernel channel) c graph where
  counterexample_reflects_violation := by
    intro claims k j hk hj hkj hdistinct hdeny hchanged
    exact hsemantic.consistency_counterexample_reflects_violation
      claims k j hk hj hkj hdistinct hdeny hchanged

/-- CAI-shaped graph diagnostic carrier for legacy callers that still consume
`GraphDiagnosticCarrier`. Its consistency field is derived from the same
profile-uniform spectral reflection used by the direct consistency theorem,
while the monotonicity field consumes the benign `C_star` transition. -/
noncomputable def ConstitutionalAIPositiveProcedureCarrier
    (L : ConstitutionalAICapacityLineage n)
    (channel : GovernanceChannel α β) (c : ℚ)
    (graph : GovernanceGraph)
    (hsemantic :
      ConstitutionalAIPositiveProcedureSemanticCarrier L c graph) :
    PositiveProcedureCertificate.GraphDiagnosticCarrier
      (L.toCapacityKernel channel) c graph where
  nontrivial := hsemantic.nontrivial
  consistency_from_exact_subcritical := by
    intro _hK _hcpos _hlt _verdict _no_violation _lower_deny
      lower_no_violation claims k j hk hj hkj hdistinct hdeny
    by_contra hchanged
    rcases hsemantic.consistency_counterexample_reflects_violation
      claims k j hk hj hkj hdistinct hdeny hchanged with
      ⟨C, hCpos, hCle, hviolation⟩
    exact lower_no_violation C hCpos hCle hviolation
  monotonicity_from_boundary := by
    intro _hK _hat_threshold _verdict _upper_scales_permit
    apply hsemantic.monotonicity_from_benign_boundary
    intro state C hbenign hC
    exact L.cai_capabilityBoundary_benign_response_matches_C_star hbenign hC

/-- CAI-shaped consistency bridge obtained by composing the profile-uniform
spectral reflection with the generic positive-procedure consistency bridge. -/
theorem ConstitutionalAIPositiveProcedureCarrier_kind_consistency_to_GraphConsistency
    (L : ConstitutionalAICapacityLineage n)
    (channel : GovernanceChannel α β) (c : ℚ)
    (graph : GovernanceGraph)
    (hsemantic :
      ConstitutionalAIPositiveProcedureSemanticCarrier L c graph)
    {cert : PositiveProcedureCertificate (L.toCapacityKernel channel) c}
    (hkind : cert.kind = PreservedDiagnostic.consistency) :
    GraphConsistency graph :=
  PositiveProcedureCertificate.kind_consistency_to_GraphConsistency
    (ConstitutionalAIPositiveProcedureConsistencyReflection
      L channel c graph hsemantic)
    hkind

/-- CAI-shaped monotonicity bridge obtained by composing the conditional carrier
with the generic positive-procedure graph diagnostic bridge. -/
theorem ConstitutionalAIPositiveProcedureCarrier_kind_monotonicity_to_GraphMonotonicity
    (L : ConstitutionalAICapacityLineage n)
    (channel : GovernanceChannel α β) (c : ℚ)
    (graph : GovernanceGraph)
    (hK : WellConditionedForCapacity (L.toCapacityKernel channel))
    (hsemantic :
      ConstitutionalAIPositiveProcedureSemanticCarrier L c graph)
    {cert : PositiveProcedureCertificate (L.toCapacityKernel channel) c}
    (hkind : cert.kind = PreservedDiagnostic.monotonicity) :
    GraphMonotonicity graph :=
  PositiveProcedureCertificate.kind_monotonicity_to_GraphMonotonicity
    hK
    (ConstitutionalAIPositiveProcedureCarrier L channel c graph hsemantic)
    hkind

end Legitimacy
