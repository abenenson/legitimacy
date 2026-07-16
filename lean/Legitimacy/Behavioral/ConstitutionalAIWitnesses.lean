/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Behavioral.ConstitutionalAIVerdict
import Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.FiveNode
import Legitimacy.Spectral.Certificates.ConstitutionalAIPositiveProcedure

/-!
# Constitutional AI worked witnesses

This module keeps the larger n=5 CAI witness out of the core lineage file while
preserving the same namespace and declaration names.
-/

set_option autoImplicit false

namespace Legitimacy

open Finset Matrix BigOperators

namespace ConstitutionalAIBehavioralLineage

section ConcreteWitness

/-! ### Three-principle Constitution-as-DAG witness -/

def helpfulPrinciple3 : Principle 3 where
  name := "helpfulness"
  rank := 0
  verdict := BinaryDecision.Permit

def privacyPrinciple3 : Principle 3 where
  name := "privacy"
  rank := 1
  verdict := BinaryDecision.Permit

def safetyPrinciple3 : Principle 3 where
  name := "safety"
  rank := 2
  verdict := BinaryDecision.Deny

@[simp] theorem helpful_ne_privacy3 :
    helpfulPrinciple3 ≠ privacyPrinciple3 := by
  intro h
  have hrank := congrArg Principle.rank h
  norm_num [helpfulPrinciple3, privacyPrinciple3] at hrank

@[simp] theorem helpful_ne_safety3 :
    helpfulPrinciple3 ≠ safetyPrinciple3 := by
  intro h
  have hrank := congrArg Principle.rank h
  norm_num [helpfulPrinciple3, safetyPrinciple3] at hrank

@[simp] theorem privacy_ne_safety3 :
    privacyPrinciple3 ≠ safetyPrinciple3 := by
  intro h
  have hrank := congrArg Principle.rank h
  norm_num [privacyPrinciple3, safetyPrinciple3] at hrank

def threePrinciples3 : Finset (Principle 3) :=
  {helpfulPrinciple3, privacyPrinciple3, safetyPrinciple3}

private theorem threePrinciples3_cases
    {p : Principle 3} (hp : p ∈ threePrinciples3) :
    p = helpfulPrinciple3 ∨ p = privacyPrinciple3 ∨ p = safetyPrinciple3 := by
  simpa [threePrinciples3] using hp

def rankConflictRel3 (p q : Principle 3) : Prop :=
  p.rank ≤ q.rank

private theorem rankConflictRel3_antisymm
    {p q : Principle 3} (hp : p ∈ threePrinciples3)
    (hq : q ∈ threePrinciples3)
    (hpq : rankConflictRel3 p q) (hqp : rankConflictRel3 q p) :
    p = q := by
  rcases threePrinciples3_cases hp with rfl | rfl | rfl
  · rcases threePrinciples3_cases hq with rfl | rfl | rfl
    · rfl
    · norm_num [rankConflictRel3, helpfulPrinciple3, privacyPrinciple3] at hqp
    · norm_num [rankConflictRel3, helpfulPrinciple3, safetyPrinciple3] at hqp
  · rcases threePrinciples3_cases hq with rfl | rfl | rfl
    · norm_num [rankConflictRel3, helpfulPrinciple3, privacyPrinciple3] at hpq
    · rfl
    · norm_num [rankConflictRel3, privacyPrinciple3, safetyPrinciple3] at hqp
  · rcases threePrinciples3_cases hq with rfl | rfl | rfl
    · norm_num [rankConflictRel3, helpfulPrinciple3, safetyPrinciple3] at hpq
    · norm_num [rankConflictRel3, privacyPrinciple3, safetyPrinciple3] at hpq
    · rfl

private theorem rankConflictRel3_wf :
    WellFounded
      (fun p q : Principle 3 =>
        p ∈ threePrinciples3 ∧ q ∈ threePrinciples3 ∧
          rankConflictRel3 p q ∧ ¬ rankConflictRel3 q p) := by
  refine Subrelation.wf ?_ (InvImage.wf Principle.rank Nat.lt_wfRel.wf)
  intro p q h
  exact lt_of_le_of_ne h.2.2.1
    (fun heq => h.2.2.2 (le_of_eq heq.symm))

def threePrincipleApplies3 (p : Principle 3) (claim : Fin 3) : Prop :=
  (claim = 0 ∧ (p = helpfulPrinciple3 ∨ p = safetyPrinciple3)) ∨
    (claim = 1 ∧ p = helpfulPrinciple3) ∨
    (claim = 2 ∧ p = privacyPrinciple3)

noncomputable def threePrincipleResolved3 (claim : Fin 3) :
    Principle 3 :=
  if claim = 0 then safetyPrinciple3
  else if claim = 1 then helpfulPrinciple3
  else privacyPrinciple3

noncomputable def threePrincipleConstitution3 : Constitution 3 where
  principles := threePrinciples3
  applies := threePrincipleApplies3
  conflictRel := rankConflictRel3
  conflictRel_refl := by intro p hp; exact le_rfl
  conflictRel_antisymm := by
    intro p q hp hq hpq hqp
    exact rankConflictRel3_antisymm hp hq hpq hqp
  conflictRel_trans := by
    intro p q r _hp _hq _hr hpq hqr
    exact le_trans hpq hqr
  conflictRel_wellFounded := rankConflictRel3_wf
  resolution := fun _p q _h => q
  resolution_mem := by intro p q h hp hq; exact hq
  resolution_upper_left := by intro p q h hp hq; exact h
  resolution_upper_right := by intro p q h hp hq; exact le_rfl
  complete := by
    intro claim
    fin_cases claim
    · exact ⟨helpfulPrinciple3, by simp [threePrinciples3],
        by simp [threePrincipleApplies3]⟩
    · exact ⟨helpfulPrinciple3, by simp [threePrinciples3],
        by simp [threePrincipleApplies3]⟩
    · exact ⟨privacyPrinciple3, by simp [threePrinciples3],
        by simp [threePrincipleApplies3]⟩
  resolvedPrinciple := threePrincipleResolved3
  resolved_mem := by
    intro claim
    fin_cases claim <;> simp [threePrincipleResolved3, threePrinciples3]
  resolved_applies := by
    intro claim
    fin_cases claim <;>
      simp [threePrincipleResolved3, threePrincipleApplies3]
  resolved_resolves := by
    intro claim p hp happ
    fin_cases claim
    · rcases happ with ⟨_, hp'⟩ | hrest
      · rcases hp' with rfl | rfl <;>
          norm_num [threePrincipleResolved3, rankConflictRel3,
            helpfulPrinciple3, safetyPrinciple3]
      · simp at hrest
    · rcases happ with hzero | hone | htwo
      · simp at hzero
      · rcases hone with ⟨_, rfl⟩
        norm_num [threePrincipleResolved3, rankConflictRel3,
          helpfulPrinciple3]
      · simp at htwo
    · rcases happ with hzero | hone | htwo
      · simp at hzero
      · simp at hone
      · rcases htwo with ⟨_, rfl⟩
        norm_num [threePrincipleResolved3, rankConflictRel3,
          privacyPrinciple3]

/-- Proves `threePrincipleConstitution3_substantive` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem threePrincipleConstitution3_substantive :
    threePrincipleConstitution3.Substantive := by
  refine ⟨helpfulPrinciple3, safetyPrinciple3, ?_, ?_, ?_, ?_, ?_⟩
  · simp [threePrincipleConstitution3, threePrinciples3]
  · simp [threePrincipleConstitution3, threePrinciples3]
  · exact helpful_ne_safety3
  · norm_num [threePrincipleConstitution3, rankConflictRel3,
      helpfulPrinciple3, safetyPrinciple3]
  · norm_num [threePrincipleConstitution3, rankConflictRel3,
      helpfulPrinciple3, safetyPrinciple3]

noncomputable def threePrincipleClaimClass3 :
    ConstitutionalAIClaimClass 3 where
  constitution := threePrincipleConstitution3
  HarmCategoricalClaim := fun claim => claim = 0
  BenignClaim := fun claim => claim ≠ 0
  harm_iff_resolved_denies := by
    intro claim
    fin_cases claim <;>
      simp [threePrincipleConstitution3, threePrincipleResolved3,
        safetyPrinciple3, helpfulPrinciple3, privacyPrinciple3]
  benign_iff_resolved_permits := by
    intro claim
    fin_cases claim <;>
      simp [threePrincipleConstitution3, threePrincipleResolved3,
        safetyPrinciple3, helpfulPrinciple3, privacyPrinciple3]
  exhaustive := by
    intro claim
    by_cases h : claim = 0
    · exact Or.inl h
    · exact Or.inr h
  disjoint := by
    intro claim hboth
    exact hboth.2 hboth.1

def threePrincipleRespectingPolicy3 (claim : Fin 3) :
    ConstitutionalAIDecision :=
  if claim = 0 then ConstitutionalAIDecision.deny
  else ConstitutionalAIDecision.permit

/-- The three-state respecting policy implements the resolved constitutional
partition exactly. Claim `0` is denied because the resolved harm principle
marks it as harmful, while the other two finite claims are permitted as benign.
This theorem supplies the policy-respects-resolution premise used by the
admissible verdict theorem. -/
theorem threePrincipleRespectingPolicy3_respects :
    ConstitutionallyRespectsResolution threePrincipleClaimClass3
      threePrincipleRespectingPolicy3 := by
  intro claim
  fin_cases claim <;>
    simp [threePrincipleRespectingPolicy3, threePrincipleClaimClass3,
      threePrincipleConstitution3, threePrincipleResolved3,
      helpfulPrinciple3, privacyPrinciple3, safetyPrinciple3]

def threePrinciplePermissivePolicy3 (_claim : Fin 3) :
    ConstitutionalAIDecision :=
  ConstitutionalAIDecision.permit

/-- The all-permit three-state policy violates the resolved constitution. Its
failure is witnessed at claim `0`, where the harm-categorical resolution
requires denial but the policy returns permit. This is the negative control
showing the witness rejects harm leakage rather than accepting every policy. -/
theorem threePrinciplePermissivePolicy3_not_respects :
    ¬ ConstitutionallyRespectsResolution threePrincipleClaimClass3
      threePrinciplePermissivePolicy3 := by
  intro hrespect
  have hzero := hrespect 0
  norm_num [threePrinciplePermissivePolicy3, threePrincipleClaimClass3,
    threePrincipleConstitution3, threePrincipleResolved3,
    safetyPrinciple3] at hzero
  cases hzero

/-- A policy that respects the three-principle resolution receives the
admissible substrate verdict under the concrete positive-procedure certificate.
The proof rules out both harm-permit leakage and monotonicity-certificate
over-escalation on benign claims from the resolution-respecting premise. This
is the small finite witness that the CAI substrate accepts a trained policy. -/
theorem threePrincipleRespectingPolicy3_substrate_verdict :
    substrateVerdictForPolicy threePrincipleClaimClass3
      threePrincipleRespectingPolicy3
      PositiveProcedureExamples.concreteHalfNoisyCertificateAtOneTenth =
        ConstitutionalAISubstrateVerdict.admissible := by
  classical
  have hrespect := threePrincipleRespectingPolicy3_respects
  have hno_leak :=
    no_harm_permit_of_respects_resolution
      threePrincipleClaimClass3 threePrincipleRespectingPolicy3 hrespect
  have hno_benign_deny :=
    no_benign_deny_of_respects_resolution
      threePrincipleClaimClass3 threePrincipleRespectingPolicy3 hrespect
  have hnot_over :
      ¬ (PositiveProcedureExamples.concreteHalfNoisyCertificateAtOneTenth.kind =
          PreservedDiagnostic.monotonicity ∧
        ∃ state : Fin 3,
          threePrincipleClaimClass3.BenignClaim state ∧
            (threePrincipleRespectingPolicy3 state).toBinary =
              BinaryDecision.Deny) := by
    intro h
    exact hno_benign_deny h.2
  simp [substrateVerdictForPolicy, hno_leak, hnot_over]

/-- The permissive three-state policy is rejected specifically through the
harm-category leak branch. The witness is claim `0`: it is harm-categorical in
the resolved constitution, yet the policy permits it. This pins the negative
verdict to a concrete failure mode instead of a generic non-admissible result. -/
theorem threePrinciplePermissivePolicy3_substrate_verdict :
    substrateVerdictForPolicy threePrincipleClaimClass3
      threePrinciplePermissivePolicy3
      PositiveProcedureExamples.concreteHalfNoisyCertificateAtOneTenth =
        ConstitutionalAISubstrateVerdict.rejectWithFailureMode
          ConstitutionalAISubstrateFailureMode.harmCategoryLeakPath := by
  apply substrateVerdictForPolicy_harm_permit_rejects
  exact ⟨0, rfl, rfl⟩

/-- The trained and all-permit three-state policies receive different substrate
verdicts. Rewriting by the two verdict theorems reduces the claim to the
constructor distinction between admissibility and the harm-leak rejection
branch. This is the finite separability check for the three-principle fixture. -/
theorem threePrinciplePolicy3_verdicts_differ :
    substrateVerdictForPolicy threePrincipleClaimClass3
      threePrincipleRespectingPolicy3
      PositiveProcedureExamples.concreteHalfNoisyCertificateAtOneTenth ≠
    substrateVerdictForPolicy threePrincipleClaimClass3
      threePrinciplePermissivePolicy3
      PositiveProcedureExamples.concreteHalfNoisyCertificateAtOneTenth := by
  rw [threePrincipleRespectingPolicy3_substrate_verdict,
    threePrinciplePermissivePolicy3_substrate_verdict]
  intro h
  cases h

/-- Proves `threePrincipleConstitution3_distinguishable_from_flat_special_case` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem threePrincipleConstitution3_distinguishable_from_flat_special_case :
    threePrincipleConstitution3 ≠
      constitutionalAIWitnessClaimClass.constitution := by
  apply Constitution.ne_of_resolvedPrinciple_ne (claim := (0 : Fin 3))
  norm_num [threePrincipleConstitution3, threePrincipleResolved3,
    constitutionalAIWitnessClaimClass,
    ConstitutionalAIClaimClass.ofFlat,
    Constitution.flatHarmBenignConstitution,
    Constitution.harmPrinciple, safetyPrinciple3]

/-- Proves `constitutionalAIWitness_has_harmCategoryLeakPath` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem constitutionalAIWitness_has_harmCategoryLeakPath :
    HarmCategoryLeakPath constitutionalAIWitnessLineage := by
  constructor
  · exact ⟨0, constitutionalAIWitness_harm_claim_zero⟩
  · exact ⟨1, by norm_num, constitutionalAIWitness_spViolation_one⟩

/-- Proves `constitutionalAIWitness_substrate_verdict` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem constitutionalAIWitness_substrate_verdict :
    substrateVerdict constitutionalAIWitnessCapacityLineage
      PositiveProcedureExamples.concreteHalfNoisyCertificateAtOneTenth =
        ConstitutionalAISubstrateVerdict.admissible := by
  classical
  have hno_leak :
      ¬ ∃ state : Fin 3,
        constitutionalAIWitnessCapacityLineage.lineage.claimClass.HarmCategoricalClaim state ∧
          (constitutionalAIWitnessCapacityLineage.lineage.policy state).toBinary =
            BinaryDecision.Permit := by
    rintro ⟨state, hharm, hpermit⟩
    dsimp [constitutionalAIWitnessCapacityLineage,
      constitutionalAIWitnessLineage, constitutionalAIWitnessClaimClass] at hharm
    rw [hharm] at hpermit
    norm_num [constitutionalAIWitnessCapacityLineage,
      constitutionalAIWitnessLineage, constitutionalAIWitnessPolicy] at hpermit
    cases hpermit
  have hnot_over :
      ¬ (PositiveProcedureExamples.concreteHalfNoisyCertificateAtOneTenth.kind =
          PreservedDiagnostic.monotonicity ∧
        ∃ state : Fin 3,
          constitutionalAIWitnessCapacityLineage.lineage.claimClass.BenignClaim state ∧
            (constitutionalAIWitnessCapacityLineage.lineage.policy state).toBinary =
              BinaryDecision.Deny) := by
    intro h
    have hkind :=
      PositiveProcedureExamples.concreteHalfNoisyCertificateAtOneTenth_kind
    rw [hkind] at h
    cases h.1
  simp [substrateVerdict, substrateVerdictForPolicy, hno_leak, hnot_over]

/-! ### Five-node capability witness -/

/-- Five-state claim partition: claim `0` is harm-categorical, all other
audited claim-states are benign. -/
noncomputable def constitutionalAIWitnessClaimClass5 :
    ConstitutionalAIClaimClass 5 :=
  ConstitutionalAIClaimClass.ofFlat
    (fun state => state = 0)
    (fun state => state ≠ 0)
    (by
      intro state
      by_cases h : state = 0
      · exact Or.inl h
      · exact Or.inr h)
    (by
      intro state hboth
      exact hboth.2 hboth.1)

/-- Five-state CAI witness policy: deny the harm-categorical claim and permit
the benign residual class. -/
def constitutionalAIWitnessPolicy5 (state : Fin 5) :
    ConstitutionalAIDecision :=
  if state = 0 then
    ConstitutionalAIDecision.deny
  else
    ConstitutionalAIDecision.permit

/-- Proves `constitutionalAIWitnessPolicy5_rule` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem constitutionalAIWitnessPolicy5_rule :
    ConstitutionalAITrainedAuditSubject constitutionalAIWitnessClaimClass5
      constitutionalAIWitnessPolicy5 := by
  constructor
  · intro state hharm
    change state = 0 at hharm
    exact Or.inr (by simp [constitutionalAIWitnessPolicy5, hharm])
  · intro state hbenign
    change state ≠ 0 at hbenign
    simp [constitutionalAIWitnessPolicy5, hbenign]

/-- Five-node CAI-class audit subject over the uniform complete graph and the
canonical five-node signal used by the ASI/RG witnesses. -/
noncomputable def constitutionalAIWitnessLineage5 :
    ConstitutionalAIBehavioralLineage 5 where
  G := uniK5
  s := sig5
  claimClass := constitutionalAIWitnessClaimClass5
  policy := constitutionalAIWitnessPolicy5
  policy_rule := constitutionalAIWitnessPolicy5_rule

/-- Proves `constitutionalAIWitness5_harm_claim_zero` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem constitutionalAIWitness5_harm_claim_zero :
    constitutionalAIWitnessLineage5.claimClass.HarmCategoricalClaim 0 :=
  rfl

/-- Proves `constitutionalAIWitness5_benign_claim_one` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem constitutionalAIWitness5_benign_claim_one :
    constitutionalAIWitnessLineage5.claimClass.BenignClaim 1 := by
  change (1 : Fin 5) ≠ 0
  norm_num

/-- Proves `constitutionalAIWitness5_harm_decision_denies` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem constitutionalAIWitness5_harm_decision_denies :
    constitutionalAIWitnessLineage5.deploymentBinaryDecision 0 =
      BinaryDecision.Deny := by
  exact constitutionalAIWitnessLineage5.deploymentBinaryDecision_harm_categorical
    constitutionalAIWitness5_harm_claim_zero

/-- Proves `constitutionalAIWitness5_benign_decision_permits` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem constitutionalAIWitness5_benign_decision_permits :
    constitutionalAIWitnessLineage5.deploymentBinaryDecision 1 =
      BinaryDecision.Permit := by
  exact constitutionalAIWitnessLineage5.deploymentBinaryDecision_benign
    constitutionalAIWitness5_benign_claim_one

/-- Proves `constitutionalAIWitness5_cv_eq_three_fourths` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem constitutionalAIWitness5_cv_eq_three_fourths :
    constitutionalAIWitnessLineage5.G.cv constitutionalAIWitnessLineage5.s =
      3 / 4 := by
  exact fiveNode_cv_values.1

/-- Proves `constitutionalAIWitness5_cv_pos` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem constitutionalAIWitness5_cv_pos :
    0 < constitutionalAIWitnessLineage5.G.cv constitutionalAIWitnessLineage5.s := by
  rw [constitutionalAIWitness5_cv_eq_three_fourths]
  norm_num

/-- Proves `constitutionalAIWitness5_C_star_one_tenth` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem constitutionalAIWitness5_C_star_one_tenth :
    Legitimacy.C_star constitutionalAIWitnessLineage5.G
      constitutionalAIWitnessLineage5.s (1 / 10) = 2 / 15 := by
  rw [Legitimacy.C_star, constitutionalAIWitness5_cv_eq_three_fourths]
  norm_num

/-- Proves `constitutionalAIWitness5_spViolation_three_fourths` for the finite Constitutional AI witness substrate; it is scoped to the encoded constitution or policy fixture. -/
theorem constitutionalAIWitness5_spViolation_three_fourths :
    constitutionalAIWitnessLineage5.G.spViolation
      constitutionalAIWitnessLineage5.s (3 / 4) := by
  rw [constitutionalAIWitnessLineage5, GovGraph.spViolation_iff_le_cv]
  rw [fiveNode_cv_values.1]

/-- Capability-scaled five-node CAI witness at tolerance `1 / 10`; the audit
budget is pinned to the exact `C_star = 2 / 15` boundary for `sig5`. -/
noncomputable def constitutionalAICapacityWitnessLineage :
    ConstitutionalAICapacityLineage 5 where
  lineage := constitutionalAIWitnessLineage5
  δ := 1 / 10
  δ_pos := by norm_num
  cv_pos := constitutionalAIWitness5_cv_pos
  auditAmplitudeBudget := 2 / 15
  auditAmplitudeBudget_pos := by norm_num

/-- The five-node CAI capacity lineage has exact critical capability `2 / 15`.
The theorem projects the calibrated value from the existing five-node CV
calculation at tolerance `1 / 10`, giving later budget and verdict checks a
named rational equality rather than repeating the arithmetic. -/
theorem constitutionalAICapacityWitnessLineage_C_star :
    constitutionalAICapacityWitnessLineage.C_star = 2 / 15 := by
  exact constitutionalAIWitness5_C_star_one_tenth

/-- The audit-amplitude budget is calibrated exactly to the lineage's
`C_star`. Using the named `2 / 15` equality, the theorem shows the stored
budget is not an independent slack parameter but the critical boundary used by
the positive-procedure witness. -/
theorem constitutionalAICapacityWitnessLineage_budget_calibrated :
    constitutionalAICapacityWitnessLineage.auditAmplitudeBudget =
      constitutionalAICapacityWitnessLineage.C_star := by
  rw [constitutionalAICapacityWitnessLineage_C_star]
  rfl

/-- The five-node witness contains a concrete profitable deviation of gain
`3 / 4`. The proof extracts the strategyproofness-violation pair, constructs
the executable action allowed by the lineage, and evaluates the utility-gain
equation exactly. This prevents the CAI game witness from being merely
syntactic. -/
theorem constitutionalAIWitness5_nonvacuous_profitable_deviation :
    ∃ dev : constitutionalAIWitnessLineage5.toGame.ProfitableDeviation (3 / 4),
      dev.gain = 3 / 4 := by
  rcases constitutionalAIWitness5_spViolation_three_fourths with ⟨p, hp⟩
  let action :=
    constitutionalAIWitnessLineage5.executableAction p.1 p.2 (3 / 4)
      (by norm_num) hp
  let dev :=
    constitutionalAIWitnessLineage5.profitableDeviationOfBudget
    (κ := 3 / 4) (η := 3 / 4) (k := p.1) (i := p.2)
    (by norm_num) le_rfl hp
  refine ⟨dev, ?_⟩
  change constitutionalAIWitnessLineage5.toGame.utilityGain p.1 p.2
      constitutionalAIWitnessLineage5.zeroProfile
      (constitutionalAIWitnessLineage5.replaceAction
        constitutionalAIWitnessLineage5.zeroProfile p.1 action) = 3 / 4
  rw [constitutionalAIWitnessLineage5.utilityGain_zero_to_action]
  · simp [action, executableAction]
  · simp [action, executableAction]

/-- N=5 positive-procedure kernel over the existing exact `uniK5` noisy-channel
calibration. The calibrated signal is the half-scale `uniK5HalfSig` fixture
already equipped with a channel-capacity equality. -/
noncomputable def constitutionalAIWitnessPositiveProcedureKernel5 :
    CapacityKernel BinaryDecision (Option BinaryDecision) 5 where
  G := uniK5
  s := uniK5HalfSig
  δ := 1 / 10
  channel := GovernanceChannel.concreteUniK5HalfNoisyCStarCalibration.channel

/-- The n=5 calibrated noisy-channel kernel is well-conditioned. -/
noncomputable def constitutionalAIWitnessPositiveProcedureKernel5_wellConditioned :
    WellConditionedForCapacity
      constitutionalAIWitnessPositiveProcedureKernel5 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [constitutionalAIWitnessPositiveProcedureKernel5]
  · simpa [constitutionalAIWitnessPositiveProcedureKernel5] using
      GovernanceChannel.uniK5_cv_uniK5HalfSig_pos
  · simpa [constitutionalAIWitnessPositiveProcedureKernel5] using
      GovernanceChannel.ConcreteNoisyCStarCalibration.toExactCapacityCertificate
        GovernanceChannel.concreteUniK5HalfNoisyCStarCalibration
        GovernanceChannel.uniK5_cv_uniK5HalfSig_pos

/-- The n=5 positive-procedure kernel has exact critical capability `4 / 15`.
This arithmetic result unfolds the calibrated kernel, the half-scale signal,
and the `C_star` definition so the later consistency and boundary
certificates can classify their diagnostic kind by comparison to a named
rational threshold. -/
theorem constitutionalAIWitnessPositiveProcedureKernel5_C_star :
    constitutionalAIWitnessPositiveProcedureKernel5.C_star = 4 / 15 := by
  simp [constitutionalAIWitnessPositiveProcedureKernel5,
    CapacityKernel.C_star, Legitimacy.C_star,
    GovernanceChannel.uniK5_cv_uniK5HalfSig]
  norm_num

/-- Strict-subcritical consistency certificate for the n=5 CAI-shaped kernel. -/
noncomputable def constitutionalAIWitnessPositiveProcedureCertificate5_consistency :
    PositiveProcedureCertificate
      constitutionalAIWitnessPositiveProcedureKernel5 (1 / 10) :=
  governance_certificate
    constitutionalAIWitnessPositiveProcedureKernel5
    constitutionalAIWitnessPositiveProcedureKernel5_wellConditioned
    (1 / 10)
    (by norm_num)
    (by
      rw [constitutionalAIWitnessPositiveProcedureKernel5_C_star]
      norm_num)

/-- The strict-subcritical certificate is a consistency certificate. At
capability `1 / 10`, the proof compares directly against the kernel's exact
`4 / 15` critical value, so the `governance_certificate` branch reduces to its
subcritical diagnostic kind. -/
theorem constitutionalAIWitnessPositiveProcedureCertificate5_consistency_kind :
    constitutionalAIWitnessPositiveProcedureCertificate5_consistency.kind =
      PreservedDiagnostic.consistency := by
  unfold constitutionalAIWitnessPositiveProcedureCertificate5_consistency
    governance_certificate
  have hlt :
      (1 / 10 : ℚ) <
        constitutionalAIWitnessPositiveProcedureKernel5.C_star := by
    rw [constitutionalAIWitnessPositiveProcedureKernel5_C_star]
    norm_num
  rw [dif_pos hlt]
  simp [PositiveProcedureCertificate.kind]

/-- Boundary monotonicity certificate for the n=5 CAI-shaped kernel. -/
noncomputable def constitutionalAIWitnessPositiveProcedureCertificate5_boundary :
    PositiveProcedureCertificate
      constitutionalAIWitnessPositiveProcedureKernel5 (4 / 15) :=
  governance_certificate
    constitutionalAIWitnessPositiveProcedureKernel5
    constitutionalAIWitnessPositiveProcedureKernel5_wellConditioned
    (4 / 15)
    (by norm_num)
    (by
      rw [constitutionalAIWitnessPositiveProcedureKernel5_C_star])

/-- The boundary certificate is a monotonicity certificate. At capability
`4 / 15`, strict subcriticality fails exactly, so the governance certificate
takes the boundary branch and records monotonicity as its preserved diagnostic.
This theorem fixes the branch used by the final five-node substrate verdict. -/
theorem constitutionalAIWitnessPositiveProcedureCertificate5_boundary_kind :
    constitutionalAIWitnessPositiveProcedureCertificate5_boundary.kind =
      PreservedDiagnostic.monotonicity := by
  unfold constitutionalAIWitnessPositiveProcedureCertificate5_boundary
    governance_certificate
  have hnot :
      ¬ (4 / 15 : ℚ) <
        constitutionalAIWitnessPositiveProcedureKernel5.C_star := by
    rw [constitutionalAIWitnessPositiveProcedureKernel5_C_star]
    norm_num
  rw [dif_neg hnot]
  simp [PositiveProcedureCertificate.kind]

/-- The positive-procedure kernel signal is intentionally not the lineage
signal. Evaluating equality at state `0` exposes the mismatch between the
half-scale noisy-channel calibration and the original CAI lineage signal. This
guards the fixture against silently treating calibration data as the policy
lineage itself. -/
theorem constitutionalAIWitness5_positiveProcedure_kernel_signal_mismatch :
    constitutionalAIWitnessPositiveProcedureKernel5.s ≠
      constitutionalAICapacityWitnessLineage.lineage.s := by
  intro hsame
  have hzero := congrFun hsame 0
  norm_num [constitutionalAIWitnessPositiveProcedureKernel5,
    constitutionalAICapacityWitnessLineage, constitutionalAIWitnessLineage5,
    uniK5HalfSig, sig5] at hzero

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Finite α] [Finite β]

/-- Conditional consumer for the CAI positive-procedure carrier at the concrete
five-node capacity lineage. The existing n=5 boundary certificate is calibrated
to `uniK5HalfSig`; `constitutionalAIWitness5_positiveProcedure_kernel_signal_mismatch`
records why that certificate cannot be directly reused for the `sig5` capacity
lineage without an additional exact channel calibration. -/
theorem constitutionalAIWitness5_carrier_monotonicity_diagnostic
    (channel : GovernanceChannel α β) (graph : GovernanceGraph)
    (hK :
      WellConditionedForCapacity
        (constitutionalAICapacityWitnessLineage.toCapacityKernel channel))
    (hsemantic :
      ConstitutionalAIPositiveProcedureSemanticCarrier
        constitutionalAICapacityWitnessLineage
        constitutionalAICapacityWitnessLineage.C_star graph)
    {cert :
      PositiveProcedureCertificate
        (constitutionalAICapacityWitnessLineage.toCapacityKernel channel)
        constitutionalAICapacityWitnessLineage.C_star}
    (hkind : cert.kind = PreservedDiagnostic.monotonicity) :
    GraphMonotonicity graph :=
  ConstitutionalAIPositiveProcedureCarrier_kind_monotonicity_to_GraphMonotonicity
    constitutionalAICapacityWitnessLineage channel
    constitutionalAICapacityWitnessLineage.C_star graph hK hsemantic hkind

/-- Policy-level negative control: it permits every audited claim, including
the harm-categorical state. It is therefore not a trained CAI audit subject,
but it concretely inhabits the harm-leak verdict branch. -/
def constitutionalAIWitnessPermitsHarmPolicy5 (_state : Fin 5) :
    ConstitutionalAIDecision :=
  ConstitutionalAIDecision.permit

/-- The five-node all-permit policy is not a trained audit subject. Claim `0`
is harm-categorical, and training requires such claims to deny or escape, but
the policy returns permit. This negative control isolates harm-category leakage
at the policy-training layer. -/
theorem constitutionalAIWitnessPermitsHarmPolicy5_not_trained :
    ¬ ConstitutionalAITrainedAuditSubject constitutionalAIWitnessClaimClass5
      constitutionalAIWitnessPermitsHarmPolicy5 := by
  intro htrained
  rcases htrained.1 0 constitutionalAIWitness5_harm_claim_zero with hesc | hdeny
  · cases hesc
  · cases hdeny

/-- The all-permit five-node policy is rejected by the harm-leak verdict
branch. The witness is the harm-categorical state `0`, which the policy permits
under the boundary positive-procedure certificate. This makes the failure mode
explicit at the substrate verdict layer. -/
theorem constitutionalAIWitness5_harm_permit_policy_rejects :
    substrateVerdictForPolicy constitutionalAIWitnessClaimClass5
      constitutionalAIWitnessPermitsHarmPolicy5
      constitutionalAIWitnessPositiveProcedureCertificate5_boundary =
        ConstitutionalAISubstrateVerdict.rejectWithFailureMode
          ConstitutionalAISubstrateFailureMode.harmCategoryLeakPath := by
  apply substrateVerdictForPolicy_harm_permit_rejects
  exact ⟨0, constitutionalAIWitness5_harm_claim_zero, rfl⟩

/-- Policy-level negative control: it denies every audited claim, including the
benign residual class. It is not a trained CAI audit subject, but it concretely
inhabits the over-escalation verdict branch under a monotonicity certificate. -/
def constitutionalAIWitnessDeniesBenignPolicy5 (_state : Fin 5) :
    ConstitutionalAIDecision :=
  ConstitutionalAIDecision.deny

/-- The five-node all-deny policy is not a trained audit subject. State `1` is
benign, and the training condition requires benign claims to be permitted, but
the policy denies it. This is the paired negative control for over-escalation
on benign residual claims. -/
theorem constitutionalAIWitnessDeniesBenignPolicy5_not_trained :
    ¬ ConstitutionalAITrainedAuditSubject constitutionalAIWitnessClaimClass5
      constitutionalAIWitnessDeniesBenignPolicy5 := by
  intro htrained
  have hpermit := htrained.2 1 constitutionalAIWitness5_benign_claim_one
  cases hpermit

/-- The all-deny five-node policy is rejected by the benign-over-escalation
branch under the monotonicity boundary certificate. The proof supplies a
benign state that is denied and discharges the absence of harm-permit leakage,
so the verdict lands on the intended residual false-positive mode. -/
theorem constitutionalAIWitness5_benign_deny_policy_rejects :
    substrateVerdictForPolicy constitutionalAIWitnessClaimClass5
      constitutionalAIWitnessDeniesBenignPolicy5
      constitutionalAIWitnessPositiveProcedureCertificate5_boundary =
        ConstitutionalAISubstrateVerdict.rejectWithFailureMode
          ConstitutionalAISubstrateFailureMode.overEscalationFalsePositiveResidual := by
  classical
  apply substrateVerdictForPolicy_benign_deny_at_monotonicity_rejects
  · rintro ⟨state, _hharm, hpermit⟩
    cases hpermit
  · exact constitutionalAIWitnessPositiveProcedureCertificate5_boundary_kind
  · exact ⟨1, constitutionalAIWitness5_benign_claim_one, rfl⟩

/-- The trained five-node witness remains admissible under the capability-aware
boundary certificate: monotonicity is present, but benign states are permitted
rather than denied. -/
theorem constitutionalAIWitness5_substrate_verdict :
    substrateVerdict constitutionalAICapacityWitnessLineage
      constitutionalAIWitnessPositiveProcedureCertificate5_boundary =
        ConstitutionalAISubstrateVerdict.admissible := by
  classical
  have hno_leak :
      ¬ ∃ state : Fin 5,
        constitutionalAICapacityWitnessLineage.lineage.claimClass.HarmCategoricalClaim state ∧
          (constitutionalAICapacityWitnessLineage.lineage.policy state).toBinary =
            BinaryDecision.Permit := by
    rintro ⟨state, hharm, hpermit⟩
    dsimp [constitutionalAICapacityWitnessLineage,
      constitutionalAIWitnessLineage5, constitutionalAIWitnessClaimClass5] at hharm
    rw [hharm] at hpermit
    norm_num [constitutionalAICapacityWitnessLineage,
      constitutionalAIWitnessLineage5, constitutionalAIWitnessPolicy5] at hpermit
    cases hpermit
  have hnot_over :
      ¬ (constitutionalAIWitnessPositiveProcedureCertificate5_boundary.kind =
          PreservedDiagnostic.monotonicity ∧
        ∃ state : Fin 5,
          constitutionalAICapacityWitnessLineage.lineage.claimClass.BenignClaim state ∧
            (constitutionalAICapacityWitnessLineage.lineage.policy state).toBinary =
              BinaryDecision.Deny) := by
    rintro ⟨_hkind, state, hbenign, hdeny⟩
    dsimp [constitutionalAICapacityWitnessLineage,
      constitutionalAIWitnessLineage5, constitutionalAIWitnessClaimClass5] at hbenign hdeny
    by_cases hstate : state = 0
    · exact hbenign hstate
    · simp [constitutionalAIWitnessPolicy5, hstate] at hdeny
  simp [substrateVerdict, substrateVerdictForPolicy, hno_leak, hnot_over]

end ConcreteWitness

end ConstitutionalAIBehavioralLineage

end Legitimacy
