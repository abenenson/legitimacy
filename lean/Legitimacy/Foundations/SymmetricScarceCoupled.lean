/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.StructuralPeerRelative
import Legitimacy.Impossibility.AxiomIndependence
import Mathlib.Tactic

/-!
# Symmetric scarce coupled allocators

This module isolates the three behavioral fields needed by the coupled scarcity
obstruction: claimant symmetry, finite-estate coupling, and a nonempty scarce
admissible profile. It deliberately omits the two rank laws used by
`StructuralScarcePeerRelativeAllocator`.
-/

set_option autoImplicit false

namespace Legitimacy

namespace DecisionPipeline

variable {P : Type} [DecisionPipeline P]

/-- Scarce symmetric coupled allocation: symmetry, finite-estate exclusion under
overload, and a concrete over-subscribed individually admissible profile. -/
class SymmetricScarceCoupledAllocator (node : NodeOf P) : Prop where
  symmetry : ClaimantSymmetric node
  finite_estate : FiniteEstateCoupled node
  scarcity_pressure :
    ∃ claims, ClaimsDistinct claims ∧
      OverSubscribed claims ∧ IndividuallyAdmissible node claims

/-- Structural scarce peer-relative allocators are symmetric scarce coupled
allocators after forgetting context-sensitivity and the two rank laws. -/
theorem structuralScarcePeerRelativeAllocator_symmetricScarceCoupled
    {node : NodeOf P}
    (hstruct : StructuralScarcePeerRelativeAllocator node) :
    SymmetricScarceCoupledAllocator node where
  symmetry := hstruct.symmetry
  finite_estate := hstruct.finite_estate
  scarcity_pressure := hstruct.scarcity_pressure

end DecisionPipeline

/-- Root-facing spelling for the widened coupled scarcity class. -/
abbrev SymmetricScarceCoupledAllocator
    {P : Type} [DecisionPipeline P]
    (node : DecisionPipeline.NodeOf P) : Prop :=
  DecisionPipeline.SymmetricScarceCoupledAllocator node

namespace SymmetricScarceCoupled

/-- Scale every claim in a profile by a common positive rational, preserving IDs
and metadata. -/
def scaleClaims (α : ℚ) (hα : 0 < α) (claims : List ClaimQ) :
    List ClaimQ :=
  claims.map (fun c =>
    ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)

lemma lookupStrength_scaleClaims
    (claims : List ClaimQ) (k : ClaimantId) (α : ℚ) (hα : 0 < α) :
    lookupStrength k (scaleClaims α hα claims) =
      α * lookupStrength k claims := by
  induction claims with
  | nil =>
      simp [scaleClaims, lookupStrength]
  | cons c cs ih =>
      by_cases hk : c.id = k
      · simp [scaleClaims, lookupStrength, hk]
      · simpa [scaleClaims, lookupStrength, hk] using ih

/-- Two profiles have the same claimant IDs and metadata, pointwise in list
order. Strengths may differ. -/
inductive SameIdsMetadata : List ClaimQ → List ClaimQ → Prop
  | nil : SameIdsMetadata [] []
  | cons {c₁ c₂ : ClaimQ} {xs ys : List ClaimQ} :
      c₁.id = c₂.id →
      c₁.metadata = c₂.metadata →
      SameIdsMetadata xs ys →
      SameIdsMetadata (c₁ :: xs) (c₂ :: ys)

lemma SameIdsMetadata.symm {xs ys : List ClaimQ} :
    SameIdsMetadata xs ys → SameIdsMetadata ys xs := by
  intro h
  induction h with
  | nil => exact SameIdsMetadata.nil
  | cons hid hmeta _ ih =>
      exact SameIdsMetadata.cons hid.symm hmeta.symm ih

lemma SameIdsMetadata.ids_eq {xs ys : List ClaimQ}
    (h : SameIdsMetadata xs ys) :
    xs.map Claim.id = ys.map Claim.id := by
  induction h with
  | nil => rfl
  | cons hid _ _ ih => simp [hid, ih]

lemma SameIdsMetadata.claimsDistinct_right {xs ys : List ClaimQ}
    (h : SameIdsMetadata xs ys) (hdist : ClaimsDistinct xs) :
    ClaimsDistinct ys := by
  simpa [ClaimsDistinct, ← SameIdsMetadata.ids_eq h] using hdist

lemma SameIdsMetadata.claimsDistinct_left {xs ys : List ClaimQ}
    (h : SameIdsMetadata xs ys) (hdist : ClaimsDistinct ys) :
    ClaimsDistinct xs := by
  exact SameIdsMetadata.claimsDistinct_right h.symm hdist

lemma SameIdsMetadata.inClaims_right {xs ys : List ClaimQ}
    (h : SameIdsMetadata xs ys) {j : ClaimantId} :
    InClaims j xs → InClaims j ys := by
  intro hj
  induction h with
  | nil =>
      rcases hj with ⟨_, hmem, _⟩
      simp at hmem
  | @cons c₁ c₂ xs ys hid _ hrest ih =>
      rcases hj with ⟨c, hmem, hc⟩
      cases hmem with
      | head =>
          refine ⟨c₂, by simp, ?_⟩
          exact hid.symm.trans hc
      | tail _ htail =>
          rcases ih ⟨c, htail, hc⟩ with ⟨d, hdmem, hdid⟩
          exact ⟨d, List.Mem.tail _ hdmem, hdid⟩

lemma SameIdsMetadata.inClaims_left {xs ys : List ClaimQ}
    (h : SameIdsMetadata xs ys) {j : ClaimantId} :
    InClaims j ys → InClaims j xs :=
  h.symm.inClaims_right

/-- Pointwise same-shape lower/upper relation used to apply graph
cross-monotonicity one coordinate at a time. -/
inductive SameIdsPointwiseLE : List ClaimQ → List ClaimQ → Prop
  | nil : SameIdsPointwiseLE [] []
  | cons {c₁ c₂ : ClaimQ} {lower upper : List ClaimQ} :
      c₁.id = c₂.id →
      c₁.strength ≤ c₂.strength →
      c₁.metadata = c₂.metadata →
      SameIdsPointwiseLE lower upper →
      SameIdsPointwiseLE (c₁ :: lower) (c₂ :: upper)

lemma SameIdsPointwiseLE.ids_eq {lower upper : List ClaimQ}
    (hrel : SameIdsPointwiseLE lower upper) :
    lower.map Claim.id = upper.map Claim.id := by
  induction hrel with
  | nil => rfl
  | cons hid _ _ _ ih => simp [hid, ih]

lemma SameIdsPointwiseLE.claimsDistinct_left
    {lower upper : List ClaimQ} (hrel : SameIdsPointwiseLE lower upper)
    (hdist : ClaimsDistinct upper) :
    ClaimsDistinct lower := by
  simpa [ClaimsDistinct, SameIdsPointwiseLE.ids_eq hrel] using hdist

lemma SameIdsPointwiseLE.append_left (pre : List ClaimQ)
    {lower upper : List ClaimQ} (hrel : SameIdsPointwiseLE lower upper) :
    SameIdsPointwiseLE (pre ++ lower) (pre ++ upper) := by
  induction pre with
  | nil =>
      simpa using hrel
  | cons c cs ih =>
      exact SameIdsPointwiseLE.cons rfl le_rfl rfl ih

lemma strengthenClaim_append_of_not_mem_ids (pre : List ClaimQ)
    (k : ClaimantId) (s' : ℚ) (hs' : 0 < s') (suffix : List ClaimQ)
    (hnot : k ∉ pre.map Claim.id) :
    strengthenClaim k s' hs' (pre ++ suffix) =
      pre ++ strengthenClaim k s' hs' suffix := by
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

lemma sameIdsPointwiseLE_scale_mono
    {xs ys : List ClaimQ} {α β : ℚ} {hα : 0 < α} {hβ : 0 < β}
    (hαβ : α ≤ β)
    (hrel : SameIdsPointwiseLE (scaleClaims β hβ xs) ys) :
    SameIdsPointwiseLE (scaleClaims α hα xs) ys := by
  induction xs generalizing ys with
  | nil =>
      cases hrel
      exact SameIdsPointwiseLE.nil
  | cons c cs ih =>
      cases ys with
      | nil =>
          cases hrel
      | cons d ds =>
          simp [scaleClaims] at hrel ⊢
          cases hrel with
          | cons hid hle hmeta hrest =>
              have hscaled_le : α * c.strength ≤ d.strength := by
                have hc_nonneg : 0 ≤ c.strength := le_of_lt c.strength_pos
                have hαβmul :
                    α * c.strength ≤ β * c.strength :=
                  mul_le_mul_of_nonneg_right hαβ hc_nonneg
                linarith
              exact SameIdsPointwiseLE.cons hid hscaled_le hmeta
                (ih hrest)

lemma permit_of_sameIdsPointwiseLE_with_prefix
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
        SameIdsPointwiseLE.append_left pre
          (SameIdsPointwiseLE.cons hid hle hmetadata hrest)
      have hdistCurrent :
          ClaimsDistinct (pre ++ c₁ :: lower) :=
        SameIdsPointwiseLE.claimsDistinct_left hrelCurrent hdist
      have hk : InClaims c₁.id (pre ++ c₁ :: lower) := by
        refine ⟨c₁, ?_, rfl⟩
        simp
      have hbound :
          ∀ c ∈ (pre ++ c₁ :: lower), c.id = c₁.id →
            c.strength ≤ c₂.strength := by
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
          strengthenClaim c₁.id c₂.strength c₂.strength_pos
              (pre ++ c₁ :: lower) =
            pre ++ c₂ :: lower := by
        rw [strengthenClaim_append_of_not_mem_ids pre c₁.id
          c₂.strength c₂.strength_pos (c₁ :: lower) hnot]
        cases c₂
        cases hid
        simp [strengthenClaim, hmetadata]
      have hperm' :
          DecisionSystem.decide G (pre ++ c₂ :: lower) j =
            BinaryDecision.Permit := by
        simpa [hstrengthened] using hstep
      simpa [List.append_assoc] using
        ih (pre := pre ++ [c₂])
          (by simpa [List.append_assoc] using hdist)
          (by simpa [List.append_assoc] using hperm')

lemma SameIdsMetadata.exists_scale_le :
    ∀ {xs ys : List ClaimQ}, SameIdsMetadata xs ys →
      ∃ (α : ℚ) (hα : 0 < α),
        SameIdsPointwiseLE (scaleClaims α hα xs) ys
  | [], [], SameIdsMetadata.nil =>
      ⟨1, by norm_num, SameIdsPointwiseLE.nil⟩
  | c₁ :: xs, c₂ :: ys, SameIdsMetadata.cons hid hmeta hrest => by
      rcases SameIdsMetadata.exists_scale_le hrest with
        ⟨β, hβ, hrel⟩
      let α : ℚ := min β (c₂.strength / c₁.strength)
      have hratio_pos : 0 < c₂.strength / c₁.strength :=
        div_pos c₂.strength_pos c₁.strength_pos
      have hα : 0 < α := by
        unfold α
        exact lt_min hβ hratio_pos
      have hα_le_ratio : α ≤ c₂.strength / c₁.strength := by
        unfold α
        exact min_le_right _ _
      have hα_le_β : α ≤ β := by
        unfold α
        exact min_le_left _ _
      have hhead : α * c₁.strength ≤ c₂.strength := by
        have hneq : c₁.strength ≠ 0 := by linarith [c₁.strength_pos]
        calc
          α * c₁.strength ≤
              (c₂.strength / c₁.strength) * c₁.strength :=
            mul_le_mul_of_nonneg_right hα_le_ratio
              (le_of_lt c₁.strength_pos)
          _ = c₂.strength := by
            field_simp [hneq]
      have htail :
          SameIdsPointwiseLE (scaleClaims α hα xs) ys := by
        exact sameIdsPointwiseLE_scale_mono hα_le_β hrel
      exact ⟨α, hα, SameIdsPointwiseLE.cons hid hhead hmeta htail⟩

/-- Solidarity plus graph monotonicity makes the system blind to all strength
changes that preserve claimant IDs and metadata. The distinctness hypothesis is
needed because `GraphMonotonicityP` is only stated for distinct profiles. -/
theorem decisionSystem_solidarity_monotonicity_sameIdsMetadata_blind
    {P : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    (K : P) (hsol : GraphSolidarityP K) (hmon : GraphMonotonicityP K)
    {X Y : List ClaimQ} (hshape : SameIdsMetadata X Y)
    (hdistX : ClaimsDistinct X) (j : ClaimantId) (hjX : InClaims j X) :
    DecisionSystem.decide K X j = DecisionSystem.decide K Y j := by
  have hdistY : ClaimsDistinct Y := hshape.claimsDistinct_right hdistX
  have hjY : InClaims j Y := hshape.inClaims_right hjX
  rcases SameIdsMetadata.exists_scale_le hshape with ⟨α, hα, hrelXY⟩
  rcases SameIdsMetadata.exists_scale_le hshape.symm with ⟨β, hβ, hrelYX⟩
  have hX_to_scaled :
      DecisionSystem.decide K X j =
        DecisionSystem.decide K (scaleClaims α hα X) j := by
    simpa [scaleClaims] using hsol X α hα j hjX
  have hY_to_scaled :
      DecisionSystem.decide K Y j =
        DecisionSystem.decide K (scaleClaims β hβ Y) j := by
    simpa [scaleClaims] using hsol Y β hβ j hjY
  cases hx : DecisionSystem.decide K X j <;>
    cases hy : DecisionSystem.decide K Y j
  · rfl
  · have hscaledPermit :
        DecisionSystem.decide K (scaleClaims α hα X) j =
          BinaryDecision.Permit := by
      exact hX_to_scaled ▸ hx
    have hYPermit :
        DecisionSystem.decide K Y j = BinaryDecision.Permit :=
      permit_of_sameIdsPointwiseLE_with_prefix hmon
        (pre := []) hdistY hrelXY hscaledPermit
    rw [hy] at hYPermit
    exact BinaryDecision.noConfusion hYPermit
  · have hscaledPermit :
        DecisionSystem.decide K (scaleClaims β hβ Y) j =
          BinaryDecision.Permit := by
      exact hY_to_scaled ▸ hy
    have hXPermit :
        DecisionSystem.decide K X j = BinaryDecision.Permit :=
      permit_of_sameIdsPointwiseLE_with_prefix hmon
        (pre := []) hdistX hrelYX hscaledPermit
    rw [hx] at hXPermit
    exact BinaryDecision.noConfusion hXPermit
  · rfl

/-- Equal-strength clone of a profile, preserving IDs and metadata. -/
def equalStrengthClaims (claims : List ClaimQ) : List ClaimQ :=
  claims.map (fun c => ⟨c.id, 1, by norm_num, c.metadata⟩)

lemma sameIdsMetadata_equalStrengthClaims (claims : List ClaimQ) :
    SameIdsMetadata claims (equalStrengthClaims claims) := by
  induction claims with
  | nil => exact SameIdsMetadata.nil
  | cons c cs ih =>
      exact SameIdsMetadata.cons rfl rfl ih

lemma claimsDistinct_equalStrengthClaims {claims : List ClaimQ}
    (hdist : ClaimsDistinct claims) :
    ClaimsDistinct (equalStrengthClaims claims) :=
  (sameIdsMetadata_equalStrengthClaims claims).claimsDistinct_right hdist

lemma inClaims_equalStrengthClaims {claims : List ClaimQ} {j : ClaimantId} :
    InClaims j claims → InClaims j (equalStrengthClaims claims) :=
  (sameIdsMetadata_equalStrengthClaims claims).inClaims_right

lemma lookupStrength_equalStrengthClaims_of_mem
    {claims : List ClaimQ} {j : ClaimantId}
    (hj : InClaims j (equalStrengthClaims claims)) :
    lookupStrength j (equalStrengthClaims claims) = 1 := by
  induction claims with
  | nil =>
      rcases hj with ⟨_, hmem, _⟩
      simp [equalStrengthClaims] at hmem
  | cons c cs ih =>
      let ec : ClaimQ := ⟨c.id, 1, by norm_num, c.metadata⟩
      change lookupStrength j (ec :: equalStrengthClaims cs) = 1
      change InClaims j (ec :: equalStrengthClaims cs) at hj
      rcases hj with ⟨d, hdmem, hdid⟩
      cases hdmem with
      | head =>
          have hcj : c.id = j := by
            change ec.id = j at hdid
            simpa [ec] using hdid
          simp [lookupStrength, ec, hcj]
      | tail _ htail =>
          by_cases hcj : c.id = j
          · simp [lookupStrength, ec, hcj]
          · have hjtail : InClaims j (equalStrengthClaims cs) :=
              ⟨d, htail, hdid⟩
            simpa [lookupStrength, ec, hcj] using ih hjtail

lemma removeClaimGraph_head {c : ClaimQ} {cs : List ClaimQ} :
    removeClaimGraph c.id (c :: cs) = cs := by
  simp [removeClaimGraph]

lemma inClaims_cons_self (c : ClaimQ) (cs : List ClaimQ) :
    InClaims c.id (c :: cs) :=
  ⟨c, by simp, rfl⟩

lemma head_id_ne_of_tail_mem {c d : ClaimQ} {cs : List ClaimQ}
    (hdist : ClaimsDistinct (c :: cs)) (hd : d ∈ cs) :
    c.id ≠ d.id := by
  intro h
  exact ClaimsDistinct_head_not_in_tail hdist
    (by
      simp only [List.mem_map]
      exact ⟨d, hd, h.symm⟩)

lemma all_denied_after_remove_head
    {P : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    {K : P} (hcons : GraphConsistencyP K)
    {c : ClaimQ} {cs : List ClaimQ}
    (hdist : ClaimsDistinct (c :: cs))
    (hall : ∀ j, InClaims j (c :: cs) →
      DecisionSystem.decide K (c :: cs) j = BinaryDecision.Deny) :
    ∀ j, InClaims j cs →
      DecisionSystem.decide K cs j = BinaryDecision.Deny := by
  intro j hj
  rcases hj with ⟨d, hdmem, hdid⟩
  have hneq : c.id ≠ j := by
    intro h
    exact head_id_ne_of_tail_mem hdist hdmem (h.trans hdid.symm)
  have hcurrent :
      DecisionSystem.decide K (c :: cs) j = BinaryDecision.Deny :=
    hall j ⟨d, List.Mem.tail _ hdmem, hdid⟩
  have hpreserve :=
    hcons (c :: cs) c.id j (inClaims_cons_self c cs)
      ⟨d, List.Mem.tail _ hdmem, hdid⟩ hneq hdist
      (hall c.id (inClaims_cons_self c cs))
  rw [removeClaimGraph_head] at hpreserve
  exact hpreserve ▸ hcurrent

/-- If every claimant in a nonempty distinct profile is denied and consistency
holds, repeated removal of denied claimants yields a denied singleton from the
original profile. -/
theorem exists_denied_singleton_of_all_denied
    {P : Type} [DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]
    {K : P} (hcons : GraphConsistencyP K) :
    ∀ {claims : List ClaimQ}, claims ≠ [] → ClaimsDistinct claims →
      (∀ j, InClaims j claims →
        DecisionSystem.decide K claims j = BinaryDecision.Deny) →
      ∃ c ∈ claims,
        DecisionSystem.decide K [c] c.id = BinaryDecision.Deny
  | [], hne, _, _ => False.elim (hne rfl)
  | [c], _hne, _hdist, hall =>
      ⟨c, by simp, by
        simpa using hall c.id (by exact ⟨c, by simp, rfl⟩)⟩
  | c :: d :: rest, _hne, hdist, hall => by
      have hdistTail : ClaimsDistinct (d :: rest) := ClaimsDistinct_tail hdist
      have hallTail :
          ∀ j, InClaims j (d :: rest) →
            DecisionSystem.decide K (d :: rest) j = BinaryDecision.Deny :=
        all_denied_after_remove_head hcons hdist hall
      rcases exists_denied_singleton_of_all_denied (K := K) hcons
          (claims := d :: rest) (by simp) hdistTail hallTail with
        ⟨x, hxmem, hxdeny⟩
      exact ⟨x, List.Mem.tail _ hxmem, hxdeny⟩

end SymmetricScarceCoupled

end Legitimacy
