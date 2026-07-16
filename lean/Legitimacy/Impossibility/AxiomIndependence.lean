/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Diagnostics.DecisionSystem
import Legitimacy.Results.NonPeerRelative
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Legitimacy.Impossibility.AxiomIndependence

This module hardens the four-axiom peer-relative impossibility theorem against
minimality objections. It gives explicit witnesses showing that consistency,
solidarity, and monotonicity are each independently omissible while the other
three graph-level axioms still hold.

For the fourth slot, the library's current binary graph semantics do not admit
a corresponding witness: graph solidarity plus graph monotonicity already imply
graph strategyproofness. So the honest conclusion is asymmetric:

* three axioms are independently omissible, with concrete witnesses;
* strategyproofness is redundant once solidarity and monotonicity are assumed.
-/

set_option autoImplicit false

namespace Legitimacy

private def scaleClaims (α : ℚ) (hα : 0 < α) (claims : List ClaimQ) :
    List ClaimQ :=
  claims.map (fun c => ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)

private lemma lookupStrength_scaleClaims
    (claims : List ClaimQ) (k : ClaimantId) (α : ℚ) (hα : 0 < α) :
    lookupStrength k (scaleClaims α hα claims) = α * lookupStrength k claims := by
  induction claims with
  | nil =>
      simp [scaleClaims, lookupStrength]
  | cons c cs ih =>
      by_cases hk : c.id = k
      · simp [scaleClaims, lookupStrength, hk]
      · simpa [scaleClaims, lookupStrength, hk] using ih

private lemma inClaims_strengthenClaim_self
    {claims : List ClaimQ} {k : ClaimantId} {s' : ℚ} {hs' : 0 < s'} :
    InClaims k claims → InClaims k (strengthenClaim k s' hs' claims) := by
  intro hk
  induction claims with
  | nil =>
      obtain ⟨_, hmem, _⟩ := hk
      simp at hmem
  | cons c cs ih =>
      by_cases hck : c.id = k
      · simp [strengthenClaim, hck]
        exact ⟨⟨k, s', hs', c.metadata⟩, by simp, rfl⟩
      · simp [strengthenClaim, hck]
        obtain ⟨c', hc'mem, hc'id⟩ := hk
        cases hc'mem with
        | head =>
            exact False.elim (hck hc'id)
        | tail _ htail =>
            rcases ih ⟨c', htail, hc'id⟩ with ⟨c'', hc''mem, hc''id⟩
            exact ⟨c'', List.Mem.tail _ hc''mem, hc''id⟩

private lemma lookupStrength_strengthenClaim_of_ne
    {claims : List ClaimQ} {j k : ClaimantId} {s' : ℚ} {hs' : 0 < s'}
    (hjk : j ≠ k) :
    lookupStrength j (strengthenClaim k s' hs' claims) = lookupStrength j claims := by
  induction claims with
  | nil =>
      simp [lookupStrength, strengthenClaim]
  | cons c cs ih =>
      by_cases hck : c.id = k
      · have hcj : c.id ≠ j := by
          intro hcj
          exact hjk (hcj.symm.trans hck)
        have hkj : k ≠ j := by
          intro hkj
          exact hjk hkj.symm
        simp [strengthenClaim, hck, lookupStrength, hkj]
      · by_cases hcj : c.id = j
        · simp [strengthenClaim, lookupStrength, hcj, hjk]
        · simp [strengthenClaim, hck, lookupStrength, hcj, ih]

private inductive SameIdsPointwiseLE : List ClaimQ → List ClaimQ → Prop
  | nil : SameIdsPointwiseLE [] []
  | cons {c₁ c₂ : ClaimQ} {lower upper : List ClaimQ} :
      c₁.id = c₂.id →
      c₁.strength ≤ c₂.strength →
      c₁.metadata = c₂.metadata →
      SameIdsPointwiseLE lower upper →
      SameIdsPointwiseLE (c₁ :: lower) (c₂ :: upper)

private lemma sameIdsPointwiseLE_map_ids_eq
    {lower upper : List ClaimQ} (hrel : SameIdsPointwiseLE lower upper) :
    lower.map Claim.id = upper.map Claim.id := by
  induction hrel with
  | nil =>
      rfl
  | @cons c₁ c₂ lower upper hid _hle _hmetadata hrest ih =>
      simp [hid, ih]

private lemma sameIdsPointwiseLE_claimsDistinct_left
    {lower upper : List ClaimQ} (hrel : SameIdsPointwiseLE lower upper)
    (hdist : ClaimsDistinct upper) :
    ClaimsDistinct lower := by
  simpa [ClaimsDistinct, sameIdsPointwiseLE_map_ids_eq hrel] using hdist

private lemma sameIdsPointwiseLE_append_left (pre : List ClaimQ)
    {lower upper : List ClaimQ} (hrel : SameIdsPointwiseLE lower upper) :
    SameIdsPointwiseLE (pre ++ lower) (pre ++ upper) := by
  induction pre with
  | nil =>
      simpa using hrel
  | cons c cs ih =>
      exact SameIdsPointwiseLE.cons rfl le_rfl rfl ih

private lemma strengthenClaim_append_of_not_mem_ids (pre : List ClaimQ)
    (k : ClaimantId) (s' : ℚ) (hs' : 0 < s') (suffix : List ClaimQ)
    (hnot : k ∉ pre.map Claim.id) :
    strengthenClaim k s' hs' (pre ++ suffix) = pre ++ strengthenClaim k s' hs' suffix := by
  induction pre with
  | nil =>
      simp
  | cons c cs ih =>
      simp at hnot
      have hck : c.id ≠ k := by
        intro hck
        exact hnot.1 hck.symm
      have hnot_cs : k ∉ cs.map Claim.id := by
        intro hkcs
        simp only [List.mem_map] at hkcs
        rcases hkcs with ⟨x, hx, rfl⟩
        exact hnot.2 x hx rfl
      simp [strengthenClaim, hck, ih hnot_cs]

private lemma sameIdsPointwiseLE_scale_self
    (claims : List ClaimQ) (α : ℚ) (hα : 0 < α) (hα_le_one : α ≤ 1) :
    SameIdsPointwiseLE (scaleClaims α hα claims) claims := by
  induction claims with
  | nil =>
      exact SameIdsPointwiseLE.nil
  | cons c cs ih =>
      refine SameIdsPointwiseLE.cons rfl ?_ rfl ih
      have hc_nonneg : 0 ≤ c.strength := le_of_lt c.strength_pos
      nlinarith

private lemma sameIdsPointwiseLE_scale_strengthen_to_self
    (claims : List ClaimQ) (k : ClaimantId) (s_r α : ℚ)
    (hs_r : 0 < s_r) (hα : 0 < α) (hα_le_one : α ≤ 1)
    (hscaled_k : α * s_r ≤ lookupStrength k claims)
    (hdist : ClaimsDistinct claims) :
    SameIdsPointwiseLE (scaleClaims α hα (strengthenClaim k s_r hs_r claims)) claims := by
  induction claims with
  | nil =>
      exact False.elim (by
        obtain ⟨_, hmem, _⟩ :=
          show InClaims k ([] : List ClaimQ) from by
            have hlookup : lookupStrength k ([] : List ClaimQ) = 0 := by simp [lookupStrength]
            have : False := by
              have hkpos := lt_of_lt_of_le (mul_pos hα hs_r) hscaled_k
              rw [hlookup] at hkpos
              linarith
            exact False.elim this
        simp at hmem)
  | cons c cs ih =>
      by_cases hck : c.id = k
      · have hhead :
            α * s_r ≤ c.strength := by
            simpa [lookupStrength, hck] using hscaled_k
        let scaledHead : ClaimQ := ⟨c.id, α * s_r, mul_pos hα hs_r, c.metadata⟩
        have hrel :
            SameIdsPointwiseLE (scaledHead :: scaleClaims α hα cs) (c :: cs) :=
          SameIdsPointwiseLE.cons rfl hhead rfl
            (sameIdsPointwiseLE_scale_self cs α hα hα_le_one)
        simpa [scaledHead, scaleClaims, strengthenClaim, hck] using hrel
      · have hdist_tail : ClaimsDistinct cs := ClaimsDistinct_tail hdist
        have hc_le : α * c.strength ≤ c.strength := by
          have hc_nonneg : 0 ≤ c.strength := le_of_lt c.strength_pos
          nlinarith
        have hscaled_k_tail : α * s_r ≤ lookupStrength k cs := by
          simpa [lookupStrength, hck] using hscaled_k
        let scaledHead : ClaimQ := ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩
        have hrel :
            SameIdsPointwiseLE
              (scaledHead :: scaleClaims α hα (strengthenClaim k s_r hs_r cs))
              (c :: cs) :=
          SameIdsPointwiseLE.cons rfl hc_le rfl (ih hscaled_k_tail hdist_tail)
        simpa [scaledHead, scaleClaims, strengthenClaim, hck] using hrel

private lemma permit_of_sameIdsPointwiseLE_with_prefixP
    {P : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision] {G : P}
    (hmon : GraphMonotonicityP G) {pre lower upper : List ClaimQ}
    {j : ClaimantId} (hdist : ClaimsDistinct (pre ++ upper))
    (hrel : SameIdsPointwiseLE lower upper)
    (hperm : DecisionSystem.decide G (pre ++ lower) j = BinaryDecision.Permit) :
    DecisionSystem.decide G (pre ++ upper) j = BinaryDecision.Permit := by
  induction hrel generalizing pre with
  | nil =>
      simpa using hperm
  | @cons c₁ c₂ lower upper hid hle hmetadata hrest ih =>
      have hrelCurrent :
          SameIdsPointwiseLE (pre ++ c₁ :: lower) (pre ++ c₂ :: upper) :=
        sameIdsPointwiseLE_append_left pre (SameIdsPointwiseLE.cons hid hle hmetadata hrest)
      have hdistCurrent :
          ClaimsDistinct (pre ++ c₁ :: lower) :=
        sameIdsPointwiseLE_claimsDistinct_left hrelCurrent hdist
      have hk : InClaims c₁.id (pre ++ c₁ :: lower) := by
        refine ⟨c₁, ?_, rfl⟩
        simp
      have hbound :
          ∀ c ∈ (pre ++ c₁ :: lower), c.id = c₁.id → c.strength ≤ c₂.strength := by
        intro c hc hcid
        have hlookupHead :
            lookupStrength c₁.id (pre ++ c₁ :: lower) = c₁.strength := by
          exact lookupStrength_eq_of_mem_distinct hdistCurrent (by simp)
        have hlookupC :
            lookupStrength c₁.id (pre ++ c₁ :: lower) = c.strength := by
          rw [← hcid]
          exact lookupStrength_eq_of_mem_distinct hdistCurrent hc
        linarith
      have hstep :=
        hmon (pre ++ c₁ :: lower) c₁.id c₂.strength c₂.strength_pos j
          hk hdistCurrent hbound hperm
      have hnot :
          c₁.id ∉ pre.map Claim.id := by
        have hnodup :
            (pre.map Claim.id ++ c₂.id :: upper.map Claim.id).Nodup := by
          simpa [ClaimsDistinct, List.map_append] using hdist
        have hdisj :
            List.Disjoint (pre.map Claim.id) (c₂.id :: upper.map Claim.id) :=
          List.disjoint_of_nodup_append hnodup
        intro hmem
        exact hdisj hmem (by simp [hid])
      have hstrengthened :
          strengthenClaim c₁.id c₂.strength c₂.strength_pos (pre ++ c₁ :: lower) =
            pre ++ c₂ :: lower := by
        rw [strengthenClaim_append_of_not_mem_ids pre c₁.id c₂.strength c₂.strength_pos
          (c₁ :: lower) hnot]
        cases c₂
        cases hid
        simp [strengthenClaim, hmetadata]
      have hperm' :
          DecisionSystem.decide G (pre ++ c₂ :: lower) j =
            BinaryDecision.Permit := by
        simpa [hstrengthened] using hstep
      simpa [List.append_assoc] using
        (ih (pre := pre ++ [c₂]) (by simpa [List.append_assoc] using hdist)
          (by simpa [List.append_assoc] using hperm'))

private lemma permit_of_sameIdsPointwiseLE_with_prefix {G : GovernanceGraph}
    (hmon : GraphMonotonicity G) {pre lower upper : List ClaimQ}
    {j : ClaimantId} (hdist : ClaimsDistinct (pre ++ upper))
    (hrel : SameIdsPointwiseLE lower upper)
    (hperm : graphDecide G (pre ++ lower) j = BinaryDecision.Permit) :
    graphDecide G (pre ++ upper) j = BinaryDecision.Permit :=
  permit_of_sameIdsPointwiseLE_with_prefixP
    ((graphMonotonicity_eq_graphMonotonicityP G).mp hmon) hdist hrel hperm
theorem decisionSystem_solidarity_monotonicity_imply_strategyproof
    {P : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    (G : P) (hsol : GraphSolidarityP G) (hmon : GraphMonotonicityP G) :
    GraphStrategyproofnessP G := by
  intro claims k s_r hs_r hk hdist hperm
  let α : ℚ := min 1 (lookupStrength k claims / s_r)
  have hα_pos : 0 < α := by
    unfold α
    apply lt_min
    · norm_num
    · exact div_pos (lookupStrength_pos_of_mem hk) hs_r
  have hα_le_one : α ≤ 1 := by
    unfold α
    exact min_le_left _ _
  have hscaled_k : α * s_r ≤ lookupStrength k claims := by
    unfold α
    by_cases hcase : lookupStrength k claims / s_r ≤ 1
    · have hmin :
          min 1 (lookupStrength k claims / s_r) = lookupStrength k claims / s_r :=
            min_eq_right hcase
      rw [hmin]
      have hsneq : s_r ≠ 0 := by linarith
      field_simp [hsneq]
      linarith
    · have hmin : min 1 (lookupStrength k claims / s_r) = 1 :=
          min_eq_left (le_of_not_ge hcase)
      rw [hmin]
      have hlt : 1 < lookupStrength k claims / s_r := lt_of_not_ge hcase
      have hlt' : s_r < lookupStrength k claims := by
        have hsneq : s_r ≠ 0 := by linarith
        field_simp [hsneq] at hlt
        linarith
      linarith
  let scaledMisreport :=
    scaleClaims α hα_pos (strengthenClaim k s_r hs_r claims)
  have hk_scaled : InClaims k (strengthenClaim k s_r hs_r claims) :=
    inClaims_strengthenClaim_self hk
  have hperm_scaled :
      DecisionSystem.decide G scaledMisreport k = BinaryDecision.Permit := by
    have hscaleEq := hsol (strengthenClaim k s_r hs_r claims) α hα_pos k hk_scaled
    have hscaleEq' :
        DecisionSystem.decide G (strengthenClaim k s_r hs_r claims) k =
          DecisionSystem.decide G scaledMisreport k := by
      simpa [scaledMisreport, scaleClaims] using hscaleEq
    rw [← hscaleEq']
    exact hperm
  have hrel :
      SameIdsPointwiseLE scaledMisreport claims :=
    sameIdsPointwiseLE_scale_strengthen_to_self claims k s_r α hs_r hα_pos
      hα_le_one hscaled_k hdist
  simpa using
    permit_of_sameIdsPointwiseLE_with_prefixP hmon
      (pre := []) (lower := scaledMisreport) (upper := claims)
      hdist hrel hperm_scaled

/-- Governance-graph specialization of the broad decision-system bridge:
graph solidarity and graph monotonicity imply graph strategyproofness for
binary permit/deny decisions under claim-strength misreports. This theorem
exposes the specialization route through `DecisionSystem`; its content is the
same substantive scaling proof as
`decisionSystem_solidarity_monotonicity_imply_strategyproof`, which constructs
`α := min 1 (lookupStrength k claims / s_r)`, proves positivity and bounds,
uses solidarity to scale the misreport, and uses monotonicity over
`SameIdsPointwiseLE`, not a `rfl` or `simp` short-circuit. -/
theorem solidarity_monotonicity_imply_strategyproof_via_decisionSystem
    (G : GovernanceGraph) (hsol : GraphSolidarity G) (hmon : GraphMonotonicity G) :
    GraphStrategyproofness G :=
  decisionSystem_solidarity_monotonicity_imply_strategyproof G hsol hmon

/-!
Claim-ledger anchor note.
The public ledger cites the concrete graph bridge below by line.
Metadata made claim constructors wider but did not alter this theorem.
Keep this local explanatory block in Lean source rather than editing
release-facing docs during the substrate dispatch.
The theorem below remains the narrow graph-level public bridge.
The broader decision-system proof above carries the substance.
-/
/-- Concrete paper-facing bridge: for a `GovernanceGraph`, solidarity plus
monotonicity already rule out beneficial unilateral claim-strength misreporting
under the binary graph strategyproofness predicate. The declaration is scoped
to the first-party claim-profile semantics and the permit/deny decision layer.
Its proof is inherited from the nontrivial decision-system argument that builds
`α := min 1 (lookupStrength k claims / s_r)`, discharges positivity/bound
obligations, scales by solidarity, and transports the permit through
`SameIdsPointwiseLE` monotonicity rather than unfolding to a trivial equality. -/
theorem solidarity_monotonicity_imply_strategyproof
    {G : GovernanceGraph}
    (hsol : GraphSolidarity G) (hmon : GraphMonotonicity G) :
    GraphStrategyproofness G :=
  solidarity_monotonicity_imply_strategyproof_via_decisionSystem G hsol hmon

/-- The retained concrete solidarity/monotonicity bridge agrees with the
decision-system-derived specialization. -/
theorem solidarity_monotonicity_imply_strategyproof_eq_via_decisionSystem
    (G : GovernanceGraph) (hsol : GraphSolidarity G) (hmon : GraphMonotonicity G) :
    solidarity_monotonicity_imply_strategyproof (G := G) hsol hmon =
      solidarity_monotonicity_imply_strategyproof_via_decisionSystem G hsol hmon :=
  Subsingleton.elim _ _

private def shortListNode : GovernanceNodeFn := fun claims _ =>
  if claims.length ≤ 2 then BinaryDecision.Permit else BinaryDecision.Deny

private def shortListGraph : GovernanceGraph := [shortListNode]

private lemma shortListGraph_solidary : GraphSolidarity shortListGraph := by
  intro claims α hα j hj
  simp [shortListGraph, shortListNode, graphDecide]

private lemma shortListGraph_monotone : GraphMonotonicity shortListGraph := by
  intro claims k s' hs' j hk hdist hle hperm
  simpa [shortListGraph, shortListNode, graphDecide, strengthenClaim_length] using hperm

private lemma shortListGraph_strategyproof : GraphStrategyproofness shortListGraph := by
  intro claims k s_r hs_r hk hdist hperm
  simpa [shortListGraph, shortListNode, graphDecide, strengthenClaim_length] using hperm

private def ncA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
private def ncB : ClaimQ := ⟨1, 1 / 2, by norm_num, []⟩
private def ncC : ClaimQ := ⟨2, 3 / 4, by norm_num, []⟩
private def ncClaims : List ClaimQ := [ncA, ncB, ncC]

private lemma ncA_in : InClaims 0 ncClaims := ⟨ncA, by simp [ncClaims], rfl⟩
private lemma ncB_in : InClaims 1 ncClaims := ⟨ncB, by simp [ncClaims], rfl⟩

private lemma ncClaims_distinct : ClaimsDistinct ncClaims := by
  unfold ClaimsDistinct ncClaims ncA ncB ncC
  decide

private lemma shortListGraph_not_consistent : ¬ GraphConsistency shortListGraph := by
  intro hcons
  have h :=
    -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
    hcons ncClaims 0 1 ncA_in ncB_in (by decide) ncClaims_distinct (by native_decide)
  rw [show graphDecide shortListGraph ncClaims 1 = BinaryDecision.Deny by native_decide] at h
  rw [show graphDecide shortListGraph (removeClaimGraph 0 ncClaims) 1 =
      BinaryDecision.Permit by native_decide] at h
  exact BinaryDecision.noConfusion h

private def bobAbsoluteNode : GovernanceNodeFn := fun claims k =>
  if k = 1 then
    if lookupStrength 0 claims + lookupStrength 2 claims ≥ 1 then
      BinaryDecision.Permit
    else
      BinaryDecision.Deny
  else
    BinaryDecision.Permit

private def bobAbsoluteGraph : GovernanceGraph := [bobAbsoluteNode]

private lemma bobAbsoluteGraph_consistent : GraphConsistency bobAbsoluteGraph := by
  intro claims k j hk hj hkj hdist hdeny
  have hk_one : k = 1 := by
    by_cases hk1 : k = 1
    · exact hk1
    · simp [bobAbsoluteGraph, bobAbsoluteNode, graphDecide, hk1] at hdeny
  subst k
  have hj_ne : j ≠ 1 := by simpa using hkj.symm
  simp [bobAbsoluteGraph, bobAbsoluteNode, graphDecide, hj_ne]

private lemma bobAbsoluteGraph_monotone : GraphMonotonicity bobAbsoluteGraph := by
  intro claims k s' hs' j hk hdist hle hperm
  by_cases hj : j = 1
  · subst j
    have hbase :
        lookupStrength 0 claims + lookupStrength 2 claims ≥ 1 := by
      by_cases hcond : 1 ≤ lookupStrength 0 claims + lookupStrength 2 claims
      · exact hcond
      · simp [bobAbsoluteGraph, bobAbsoluteNode, graphDecide, hcond] at hperm
    by_cases hk0 : k = 0
    · subst k
      have hkbound :
          lookupStrength 0 claims ≤ s' := by
        exact lookupStrength_le_of_all_le hk hle
      have hnew :
          lookupStrength 0 (strengthenClaim 0 s' hs' claims) +
              lookupStrength 2 (strengthenClaim 0 s' hs' claims) ≥ 1 := by
        rw [show lookupStrength 0 (strengthenClaim 0 s' hs' claims) = s' by
              exact lookupStrength_after_strengthen hk hdist,
            show lookupStrength 2 (strengthenClaim 0 s' hs' claims) = lookupStrength 2 claims by
              exact lookupStrength_strengthenClaim_of_ne (j := 2) (k := 0) (s' := s') (hs' := hs') (by decide)]
        linarith
      simp [bobAbsoluteGraph, bobAbsoluteNode, graphDecide, hnew]
    · by_cases hk2 : k = 2
      · subst k
        have hkbound :
            lookupStrength 2 claims ≤ s' := by
          exact lookupStrength_le_of_all_le hk hle
        have hnew :
            lookupStrength 0 (strengthenClaim 2 s' hs' claims) +
                lookupStrength 2 (strengthenClaim 2 s' hs' claims) ≥ 1 := by
          rw [show lookupStrength 0 (strengthenClaim 2 s' hs' claims) = lookupStrength 0 claims by
                exact lookupStrength_strengthenClaim_of_ne (j := 0) (k := 2) (s' := s') (hs' := hs') (by decide),
              show lookupStrength 2 (strengthenClaim 2 s' hs' claims) = s' by
                exact lookupStrength_after_strengthen hk hdist]
          linarith
        simp [bobAbsoluteGraph, bobAbsoluteNode, graphDecide, hnew]
      · have hsame0 :
            lookupStrength 0 (strengthenClaim k s' hs' claims) = lookupStrength 0 claims := by
          exact lookupStrength_strengthenClaim_of_ne (j := 0) (k := k) (s' := s') (hs' := hs')
            (by intro h; exact hk0 h.symm)
        have hsame2 :
            lookupStrength 2 (strengthenClaim k s' hs' claims) = lookupStrength 2 claims := by
          exact lookupStrength_strengthenClaim_of_ne (j := 2) (k := k) (s' := s') (hs' := hs')
            (by intro h; exact hk2 h.symm)
        simp [bobAbsoluteGraph, bobAbsoluteNode, graphDecide, hsame0, hsame2, hbase]
  · exact by simp [bobAbsoluteGraph, bobAbsoluteNode, graphDecide, hj]

private lemma bobAbsoluteGraph_strategyproof : GraphStrategyproofness bobAbsoluteGraph := by
  intro claims k s_r hs_r hk hdist hperm
  by_cases hk1 : k = 1
  · subst k
    have hperm' :
        lookupStrength 0 (strengthenClaim 1 s_r hs_r claims) +
            lookupStrength 2 (strengthenClaim 1 s_r hs_r claims) ≥ 1 := by
      by_cases hcond :
          1 ≤ lookupStrength 0 (strengthenClaim 1 s_r hs_r claims) +
            lookupStrength 2 (strengthenClaim 1 s_r hs_r claims)
      · exact hcond
      · simp [bobAbsoluteGraph, bobAbsoluteNode, graphDecide, hcond] at hperm
    have hbase :
        lookupStrength 0 claims + lookupStrength 2 claims ≥ 1 := by
      rw [lookupStrength_strengthenClaim_of_ne (j := 0) (k := 1) (s' := s_r) (hs' := hs_r) (by decide),
        lookupStrength_strengthenClaim_of_ne (j := 2) (k := 1) (s' := s_r) (hs' := hs_r) (by decide)] at hperm'
      exact hperm'
    simp [bobAbsoluteGraph, bobAbsoluteNode, graphDecide, hbase]
  · simp [bobAbsoluteGraph, bobAbsoluteNode, graphDecide, hk1]

private def nsA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
private def nsB : ClaimQ := ⟨1, 1 / 4, by norm_num, []⟩
private def nsC : ClaimQ := ⟨2, 1 / 4, by norm_num, []⟩
private def nsClaims : List ClaimQ := [nsA, nsB, nsC]

private lemma bobAbsoluteGraph_not_solidary : ¬ GraphSolidarity bobAbsoluteGraph := by
  intro hsol
  let scaled : List ClaimQ :=
    nsClaims.map (fun c => (⟨c.id, (2 : ℚ) * c.strength, by
      have hc := c.strength_pos
      nlinarith, c.metadata⟩ : ClaimQ))
  have h :=
    hsol nsClaims 2 (by norm_num) 1 (by exact ⟨nsB, by simp [nsClaims], rfl⟩)
  change graphDecide bobAbsoluteGraph nsClaims 1 = graphDecide bobAbsoluteGraph scaled 1 at h
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  rw [show graphDecide bobAbsoluteGraph nsClaims 1 = BinaryDecision.Deny by native_decide] at h
  rw [show graphDecide bobAbsoluteGraph scaled 1 = BinaryDecision.Permit by native_decide] at h
  exact BinaryDecision.noConfusion h

private def bobRelativeNode : GovernanceNodeFn := fun claims k =>
  if k = 1 then
    if lookupStrength 0 claims ≤ lookupStrength 2 claims then
      BinaryDecision.Permit
    else
      BinaryDecision.Deny
  else
    BinaryDecision.Permit

private def bobRelativeGraph : GovernanceGraph := [bobRelativeNode]

private lemma bobRelativeGraph_consistent : GraphConsistency bobRelativeGraph := by
  intro claims k j hk hj hkj hdist hdeny
  have hk_one : k = 1 := by
    by_cases hk1 : k = 1
    · exact hk1
    · simp [bobRelativeGraph, bobRelativeNode, graphDecide, hk1] at hdeny
  subst k
  have hj_ne : j ≠ 1 := by simpa using hkj.symm
  simp [bobRelativeGraph, bobRelativeNode, graphDecide, hj_ne]

private lemma bobRelativeGraph_solidary : GraphSolidarity bobRelativeGraph := by
  intro claims α hα j hj
  by_cases hj1 : j = 1
  · subst j
    have h0 :
        lookupStrength 0 (scaleClaims α hα claims) = α * lookupStrength 0 claims := by
      simpa using lookupStrength_scaleClaims claims 0 α hα
    have h2 :
        lookupStrength 2 (scaleClaims α hα claims) = α * lookupStrength 2 claims := by
      simpa using lookupStrength_scaleClaims claims 2 α hα
    by_cases hcmp : lookupStrength 0 claims ≤ lookupStrength 2 claims
    · have hcmp' :
          lookupStrength 0 (scaleClaims α hα claims) ≤
            lookupStrength 2 (scaleClaims α hα claims) := by
        rw [h0, h2]
        nlinarith
      change graphDecide bobRelativeGraph claims 1 =
        graphDecide bobRelativeGraph (scaleClaims α hα claims) 1
      simp [bobRelativeGraph, bobRelativeNode, graphDecide, hcmp, hcmp']
    · have hcmp' :
          ¬ lookupStrength 0 (scaleClaims α hα claims) ≤
            lookupStrength 2 (scaleClaims α hα claims) := by
        rw [h0, h2]
        intro h'
        apply hcmp
        nlinarith
      change graphDecide bobRelativeGraph claims 1 =
        graphDecide bobRelativeGraph (scaleClaims α hα claims) 1
      simp [bobRelativeGraph, bobRelativeNode, graphDecide, hcmp, hcmp']
  · simp [bobRelativeGraph, bobRelativeNode, graphDecide, hj1]

private lemma bobRelativeGraph_strategyproof : GraphStrategyproofness bobRelativeGraph := by
  intro claims k s_r hs_r hk hdist hperm
  by_cases hk1 : k = 1
  · subst k
    have hperm' :
        lookupStrength 0 (strengthenClaim 1 s_r hs_r claims) ≤
          lookupStrength 2 (strengthenClaim 1 s_r hs_r claims) := by
      by_cases hcond :
          lookupStrength 0 (strengthenClaim 1 s_r hs_r claims) ≤
            lookupStrength 2 (strengthenClaim 1 s_r hs_r claims)
      · exact hcond
      · simp [bobRelativeGraph, bobRelativeNode, graphDecide, hcond] at hperm
    have hbase :
        lookupStrength 0 claims ≤ lookupStrength 2 claims := by
      rw [lookupStrength_strengthenClaim_of_ne (j := 0) (k := 1) (s' := s_r) (hs' := hs_r) (by decide),
        lookupStrength_strengthenClaim_of_ne (j := 2) (k := 1) (s' := s_r) (hs' := hs_r) (by decide)] at hperm'
      exact hperm'
    simp [bobRelativeGraph, bobRelativeNode, graphDecide, hbase]
  · simp [bobRelativeGraph, bobRelativeNode, graphDecide, hk1]

private def nmA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
private def nmB : ClaimQ := ⟨1, 1 / 2, by norm_num, []⟩
private def nmC : ClaimQ := ⟨2, 3 / 4, by norm_num, []⟩
private def nmClaims : List ClaimQ := [nmA, nmB, nmC]

private lemma nmA_in : InClaims 0 nmClaims := ⟨nmA, by simp [nmClaims], rfl⟩

private lemma nmClaims_distinct : ClaimsDistinct nmClaims := by
  unfold ClaimsDistinct nmClaims nmA nmB nmC
  decide

private lemma nmStrengthBound :
    ∀ c ∈ nmClaims, c.id = 0 → c.strength ≤ (1 : ℚ) := by
  intro c hc hid
  cases hc with
  | head =>
      simp only [nmA] at hid ⊢
      norm_num
  | tail _ htail =>
      cases htail with
      | head =>
          simp only [nmB] at hid
          simp at hid
      | tail _ htail2 =>
          cases htail2 with
          | head =>
              simp only [nmC] at hid
              simp at hid
          | tail _ hnil =>
              cases hnil

private lemma bobRelativeGraph_not_monotone : ¬ GraphMonotonicity bobRelativeGraph := by
  intro hmon
  have h :=
    hmon nmClaims 0 1 (by norm_num) 1 nmA_in nmClaims_distinct nmStrengthBound
      -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
      (by native_decide)
  rw [show graphDecide bobRelativeGraph
      (strengthenClaim 0 1 (by norm_num) nmClaims) 1 = BinaryDecision.Deny by native_decide] at h
  exact BinaryDecision.noConfusion h

private def ownThresholdNode : GovernanceNodeFn := fun claims k =>
  if (1 : ℚ) ≤ lookupStrength k claims then
    BinaryDecision.Permit
  else
    BinaryDecision.Deny

private def ownThresholdGraph : GovernanceGraph := [ownThresholdNode]

private lemma ownThresholdGraph_consistent : GraphConsistency ownThresholdGraph := by
  intro claims k j _hk _hj hkj _hdist _hdeny
  have hlookup :
      lookupStrength j (removeClaimGraph k claims) = lookupStrength j claims := by
    exact lookupStrength_removeClaimGraph_of_ne (by intro h; exact hkj h.symm)
  by_cases hbase : (1 : ℚ) ≤ lookupStrength j claims
  · simp [ownThresholdGraph, ownThresholdNode, graphDecide, hbase, hlookup]
  · simp [ownThresholdGraph, ownThresholdNode, graphDecide, hbase, hlookup]

private lemma ownThresholdGraph_monotone : GraphMonotonicity ownThresholdGraph := by
  intro claims k s' hs' j hk hdist hle hperm
  have hbase : (1 : ℚ) ≤ lookupStrength j claims := by
    by_cases hcond : (1 : ℚ) ≤ lookupStrength j claims
    · exact hcond
    · simp [ownThresholdGraph, ownThresholdNode, graphDecide, hcond] at hperm
  by_cases hjk : j = k
  · subst j
    have hbound : lookupStrength k claims ≤ s' :=
      lookupStrength_le_of_all_le hk hle
    have hnew :
        (1 : ℚ) ≤ lookupStrength k (strengthenClaim k s' hs' claims) := by
      rw [lookupStrength_after_strengthen hk hdist]
      linarith
    simp [ownThresholdGraph, ownThresholdNode, graphDecide, hnew]
  · have hsame :
        lookupStrength j (strengthenClaim k s' hs' claims) = lookupStrength j claims :=
      lookupStrength_strengthenClaim_of_ne hjk
    simp [ownThresholdGraph, ownThresholdNode, graphDecide, hbase, hsame]

private def stA : ClaimQ := ⟨0, 1 / 2, by norm_num, []⟩
private def stClaims : List ClaimQ := [stA]

private lemma stA_in : InClaims 0 stClaims := ⟨stA, by simp [stClaims], rfl⟩

private lemma stClaims_distinct : ClaimsDistinct stClaims := by
  unfold ClaimsDistinct stClaims stA
  decide

private lemma ownThresholdGraph_not_strategyproof : ¬ GraphStrategyproofness ownThresholdGraph := by
  intro hsp
  have h :=
    -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
    hsp stClaims 0 1 (by norm_num) stA_in stClaims_distinct (by native_decide)
  rw [show graphDecide ownThresholdGraph stClaims 0 = BinaryDecision.Deny by native_decide] at h
  exact BinaryDecision.noConfusion h

private def relativeSelfNode : GovernanceNodeFn := fun claims k =>
  if k = 0 then
    if lookupStrength 1 claims ≤ lookupStrength 0 claims then
      BinaryDecision.Permit
    else
      BinaryDecision.Deny
  else
    BinaryDecision.Permit

private def relativeSelfGraph : GovernanceGraph := [relativeSelfNode]

private lemma relativeSelfGraph_consistent : GraphConsistency relativeSelfGraph := by
  intro claims k j _hk _hj hkj _hdist hdeny
  by_cases hk0 : k = 0
  · subst k
    have hj0 : j ≠ 0 := by
      intro hj0
      exact hkj hj0.symm
    simp [relativeSelfGraph, relativeSelfNode, graphDecide, hj0]
  · simp [relativeSelfGraph, relativeSelfNode, graphDecide, hk0] at hdeny

private lemma relativeSelfGraph_solidary : GraphSolidarity relativeSelfGraph := by
  intro claims α hα j _hj
  by_cases hj0 : j = 0
  · subst j
    have h0 :
        lookupStrength 0 (scaleClaims α hα claims) = α * lookupStrength 0 claims := by
      simpa using lookupStrength_scaleClaims claims 0 α hα
    have h1 :
        lookupStrength 1 (scaleClaims α hα claims) = α * lookupStrength 1 claims := by
      simpa using lookupStrength_scaleClaims claims 1 α hα
    by_cases hcmp : lookupStrength 1 claims ≤ lookupStrength 0 claims
    · have hcmp' :
          lookupStrength 1 (scaleClaims α hα claims) ≤
            lookupStrength 0 (scaleClaims α hα claims) := by
        rw [h0, h1]
        nlinarith
      change graphDecide relativeSelfGraph claims 0 =
        graphDecide relativeSelfGraph (scaleClaims α hα claims) 0
      simp [relativeSelfGraph, relativeSelfNode, graphDecide, hcmp, hcmp']
    · have hcmp' :
          ¬ lookupStrength 1 (scaleClaims α hα claims) ≤
            lookupStrength 0 (scaleClaims α hα claims) := by
        rw [h0, h1]
        intro h'
        apply hcmp
        nlinarith
      change graphDecide relativeSelfGraph claims 0 =
        graphDecide relativeSelfGraph (scaleClaims α hα claims) 0
      simp [relativeSelfGraph, relativeSelfNode, graphDecide, hcmp, hcmp']
  · simp [relativeSelfGraph, relativeSelfNode, graphDecide, hj0]

private def rsA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
private def rsB : ClaimQ := ⟨1, 1 / 2, by norm_num, []⟩
private def rsClaims : List ClaimQ := [rsA, rsB]

private lemma rsA_in : InClaims 0 rsClaims := ⟨rsA, by simp [rsClaims], rfl⟩

private lemma rsClaims_distinct : ClaimsDistinct rsClaims := by
  unfold ClaimsDistinct rsClaims rsA rsB
  decide

private lemma relativeSelfGraph_not_strategyproof : ¬ GraphStrategyproofness relativeSelfGraph := by
  intro hsp
  have h :=
    -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
    hsp rsClaims 0 (3 / 4) (by norm_num) rsA_in rsClaims_distinct (by native_decide)
  rw [show graphDecide relativeSelfGraph rsClaims 0 = BinaryDecision.Deny by native_decide] at h
  exact BinaryDecision.noConfusion h

/-- Axiom-independence witness: consistency is not derivable from solidarity,
monotonicity, and strategyproofness. -/
theorem exists_non_consistent_solid_monotone_strategyproof :
    ∃ G : GovernanceGraph,
      GraphSolidarity G ∧ GraphMonotonicity G ∧ GraphStrategyproofness G ∧
        ¬ GraphConsistency G := by
  exact ⟨shortListGraph, shortListGraph_solidary, shortListGraph_monotone,
    shortListGraph_strategyproof, shortListGraph_not_consistent⟩

/-- Axiom-independence witness: solidarity is not derivable from consistency,
monotonicity, and strategyproofness. -/
theorem exists_non_solidarity_consistent_monotone_strategyproof :
    ∃ G : GovernanceGraph,
      GraphConsistency G ∧ GraphMonotonicity G ∧ GraphStrategyproofness G ∧
        ¬ GraphSolidarity G := by
  exact ⟨bobAbsoluteGraph, bobAbsoluteGraph_consistent, bobAbsoluteGraph_monotone,
    bobAbsoluteGraph_strategyproof, bobAbsoluteGraph_not_solidary⟩

/-- Axiom-independence witness: monotonicity is not derivable from consistency,
solidarity, and strategyproofness. -/
theorem exists_non_monotonicity_consistent_solid_strategyproof :
    ∃ G : GovernanceGraph,
      GraphConsistency G ∧ GraphSolidarity G ∧ GraphStrategyproofness G ∧
        ¬ GraphMonotonicity G := by
  exact ⟨bobRelativeGraph, bobRelativeGraph_consistent, bobRelativeGraph_solidary,
    bobRelativeGraph_strategyproof, bobRelativeGraph_not_monotone⟩

/-- Strategyproofness is not derivable from consistency and monotonicity alone. -/
theorem exists_non_strategyproof_consistent_monotone :
    ∃ G : GovernanceGraph,
      GraphConsistency G ∧ GraphMonotonicity G ∧ ¬ GraphStrategyproofness G := by
  exact ⟨ownThresholdGraph, ownThresholdGraph_consistent, ownThresholdGraph_monotone,
    ownThresholdGraph_not_strategyproof⟩

/-- Strategyproofness is not derivable from consistency and solidarity alone. -/
theorem exists_non_strategyproof_consistent_solid :
    ∃ G : GovernanceGraph,
      GraphConsistency G ∧ GraphSolidarity G ∧ ¬ GraphStrategyproofness G := by
  exact ⟨relativeSelfGraph, relativeSelfGraph_consistent, relativeSelfGraph_solidary,
    relativeSelfGraph_not_strategyproof⟩

/-- In the current binary graph semantics, the fourth independence witness does
not exist: solidarity together with monotonicity already forces
strategyproofness. -/
theorem not_exists_non_strategyproof_consistent_solid_monotone :
    ¬ ∃ G : GovernanceGraph,
      GraphConsistency G ∧ GraphSolidarity G ∧ GraphMonotonicity G ∧
        ¬ GraphStrategyproofness G := by
  intro h
  rcases h with ⟨G, _hcons, hsol, hmon, hnsp⟩
  exact hnsp (solidarity_monotonicity_imply_strategyproof hsol hmon)

end Legitimacy
