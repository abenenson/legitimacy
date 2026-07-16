/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Behavioral.ConstitutionalAILineage
import Legitimacy.Spectral.Certificates.PositiveProcedureCertificate

/-!
# Constitutional AI substrate verdicts

This module keeps the capability-aware verdict layer out of the core
behavioral lineage file. The definitions remain in the same namespace so
existing theorem names are preserved.
-/

set_option autoImplicit false

namespace Legitimacy

namespace ConstitutionalAIBehavioralLineage

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Finite α] [Finite β]
variable {n : Nat} [NeZero n]

/-- Failure modes exposed by the Constitutional AI deployment audit substrate. -/
inductive ConstitutionalAISubstrateFailureMode where
  | harmCategoryLeakPath : ConstitutionalAISubstrateFailureMode
  | overEscalationFalsePositiveResidual : ConstitutionalAISubstrateFailureMode
  deriving Repr, DecidableEq

/-- Binary substrate verdict for the worked Constitutional AI audit witness. -/
inductive ConstitutionalAISubstrateVerdict where
  | admissible : ConstitutionalAISubstrateVerdict
  | rejectWithFailureMode :
      ConstitutionalAISubstrateFailureMode → ConstitutionalAISubstrateVerdict
  deriving Repr, DecidableEq

/-- A harm-category leak path is a nonzero spectral perturbation surface in a
deployment graph whose claim partition contains a harm-categorical state. -/
def HarmCategoryLeakPath (L : ConstitutionalAIBehavioralLineage n) : Prop :=
  (∃ state : Fin n, L.claimClass.HarmCategoricalClaim state) ∧
    ∃ γ : ℚ, 0 < γ ∧ L.G.spViolation L.s γ

/-- Capability-aware policy verdict used by the CAI substrate.

The verdict reads the positive-procedure certificate kind rather than raw
`cv`: harm-categorical permits are leak paths, while benign denials at a
boundary/supercritical certificate are over-escalation residuals. -/
noncomputable def substrateVerdictForPolicy
    (claimClass : ConstitutionalAIClaimClass n)
    (policy : Fin n → ConstitutionalAIDecision)
    {K : CapacityKernel α β n} {c : ℚ}
    (cert : PositiveProcedureCertificate K c) :
    ConstitutionalAISubstrateVerdict := by
  classical
  exact
    if ∃ state : Fin n,
        claimClass.HarmCategoricalClaim state ∧
          (policy state).toBinary = BinaryDecision.Permit then
      ConstitutionalAISubstrateVerdict.rejectWithFailureMode
        ConstitutionalAISubstrateFailureMode.harmCategoryLeakPath
    else if cert.kind = PreservedDiagnostic.monotonicity ∧
        ∃ state : Fin n,
          claimClass.BenignClaim state ∧
            (policy state).toBinary = BinaryDecision.Deny then
      ConstitutionalAISubstrateVerdict.rejectWithFailureMode
        ConstitutionalAISubstrateFailureMode.overEscalationFalsePositiveResidual
    else
      ConstitutionalAISubstrateVerdict.admissible

/-- Capability-aware substrate verdict for a wrapped CAI capacity lineage. -/
noncomputable def substrateVerdict
    (L : ConstitutionalAICapacityLineage n)
    {K : CapacityKernel α β n} {c : ℚ}
    (cert : PositiveProcedureCertificate K c) :
    ConstitutionalAISubstrateVerdict :=
  substrateVerdictForPolicy L.lineage.claimClass L.lineage.policy cert

theorem substrateVerdictForPolicy_harm_permit_rejects
    (claimClass : ConstitutionalAIClaimClass n)
    (policy : Fin n → ConstitutionalAIDecision)
    {K : CapacityKernel α β n} {c : ℚ}
    (cert : PositiveProcedureCertificate K c)
    (hleak :
      ∃ state : Fin n,
        claimClass.HarmCategoricalClaim state ∧
          (policy state).toBinary = BinaryDecision.Permit) :
    substrateVerdictForPolicy claimClass policy cert =
      ConstitutionalAISubstrateVerdict.rejectWithFailureMode
        ConstitutionalAISubstrateFailureMode.harmCategoryLeakPath := by
  classical
  simp [substrateVerdictForPolicy, hleak]

theorem substrateVerdictForPolicy_benign_deny_at_monotonicity_rejects
    (claimClass : ConstitutionalAIClaimClass n)
    (policy : Fin n → ConstitutionalAIDecision)
    {K : CapacityKernel α β n} {c : ℚ}
    (cert : PositiveProcedureCertificate K c)
    (hno_leak :
      ¬ ∃ state : Fin n,
        claimClass.HarmCategoricalClaim state ∧
          (policy state).toBinary = BinaryDecision.Permit)
    (hkind : cert.kind = PreservedDiagnostic.monotonicity)
    (hdeny :
      ∃ state : Fin n,
        claimClass.BenignClaim state ∧
          (policy state).toBinary = BinaryDecision.Deny) :
    substrateVerdictForPolicy claimClass policy cert =
      ConstitutionalAISubstrateVerdict.rejectWithFailureMode
        ConstitutionalAISubstrateFailureMode.overEscalationFalsePositiveResidual := by
  classical
  simp [substrateVerdictForPolicy, hno_leak, hkind, hdeny]

omit [NeZero n] in
theorem no_harm_permit_of_respects_resolution
    (claimClass : ConstitutionalAIClaimClass n)
    (policy : Fin n → ConstitutionalAIDecision)
    (hrespect : ConstitutionallyRespectsResolution claimClass policy) :
    ¬ ∃ state : Fin n,
      claimClass.HarmCategoricalClaim state ∧
        (policy state).toBinary = BinaryDecision.Permit := by
  rintro ⟨state, hharm, hpermit⟩
  have hresolved :=
    (claimClass.harm_iff_resolved_denies state).mp hharm
  have hdeny : (policy state).toBinary = BinaryDecision.Deny := by
    rw [hrespect state, hresolved]
  rw [hdeny] at hpermit
  cases hpermit

omit [NeZero n] in
theorem no_benign_deny_of_respects_resolution
    (claimClass : ConstitutionalAIClaimClass n)
    (policy : Fin n → ConstitutionalAIDecision)
    (hrespect : ConstitutionallyRespectsResolution claimClass policy) :
    ¬ ∃ state : Fin n,
      claimClass.BenignClaim state ∧
        (policy state).toBinary = BinaryDecision.Deny := by
  rintro ⟨state, hbenign, hdeny⟩
  have hresolved :=
    (claimClass.benign_iff_resolved_permits state).mp hbenign
  have hpermit : (policy state).toBinary = BinaryDecision.Permit := by
    rw [hrespect state, hresolved]
  rw [hpermit] at hdeny
  cases hdeny

/-- Constitutionally-respecting deployment policies are substrate-admissible at
every positive audited capability scale `c ≤ C*` of a well-conditioned kernel. -/
theorem constitutionally_respecting_policy_substrate_admissible
    (claimClass : ConstitutionalAIClaimClass n)
    (policy : Fin n → ConstitutionalAIDecision)
    {K : CapacityKernel α β n} (hK : WellConditionedForCapacity K)
    {c : ℚ} (hcpos : 0 < c) (hc : c ≤ K.C_star)
    (hrespect : ConstitutionallyRespectsResolution claimClass policy) :
    substrateVerdictForPolicy claimClass policy
      (governance_certificate K hK c hcpos hc) =
        ConstitutionalAISubstrateVerdict.admissible := by
  classical
  have hno_leak :=
    no_harm_permit_of_respects_resolution claimClass policy hrespect
  have hno_benign_deny :=
    no_benign_deny_of_respects_resolution claimClass policy hrespect
  have hnot_over :
      ¬ ((governance_certificate K hK c hcpos hc).kind =
          PreservedDiagnostic.monotonicity ∧
        ∃ state : Fin n,
          claimClass.BenignClaim state ∧
            (policy state).toBinary = BinaryDecision.Deny) := by
    intro h
    exact hno_benign_deny h.2
  simp [substrateVerdictForPolicy, hno_leak, hnot_over]

theorem substrateVerdict_admissible_of_respects_resolution
    (L : ConstitutionalAICapacityLineage n)
    {K : CapacityKernel α β n} (hK : WellConditionedForCapacity K)
    {c : ℚ} (hcpos : 0 < c) (hc : c ≤ K.C_star)
    (hrespect :
      ConstitutionallyRespectsResolution L.lineage.claimClass
        L.lineage.policy) :
    substrateVerdict L (governance_certificate K hK c hcpos hc) =
      ConstitutionalAISubstrateVerdict.admissible :=
  constitutionally_respecting_policy_substrate_admissible
    L.lineage.claimClass L.lineage.policy hK hcpos hc hrespect

end ConstitutionalAIBehavioralLineage

end Legitimacy
