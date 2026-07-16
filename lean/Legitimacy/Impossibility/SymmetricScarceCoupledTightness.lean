/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/


import Legitimacy.Impossibility.SymmetricScarceCoupledObstruction

/-!
# Tightness and separation witnesses for symmetric scarce coupled allocators

This module contains the field-necessity countermodels and the max-rule
separation witness for the widened coupled scarcity class.
-/

set_option autoImplicit false

namespace Legitimacy

namespace SymmetricScarceCoupledMedianWitness

/-! ## Field necessity countermodels -/

private def coupledDenyAllNode : GovernanceNodeFn :=
  fun _ _ => BinaryDecision.Deny

private def coupledPermitAllNode : GovernanceNodeFn :=
  fun _ _ => BinaryDecision.Permit

private lemma canonicalPipeline_decide_node
    (node : GovernanceNodeFn) (claims : List ClaimQ) (k : ClaimantId) :
    DecisionSystem.decide
        (DecisionPipeline.canonicalPipelineFor (P := GovernanceGraph) node)
        claims k = node claims k :=
  DecisionPipeline.decide_canonicalPipelineFor
    (P := GovernanceGraph) node claims k

private lemma inClaims_removeClaimGraph_to_original
    {claims : List ClaimQ} {j k : ClaimantId}
    (hdist : ClaimsDistinct claims)
    (hj : InClaims j (removeClaimGraph k claims)) :
    InClaims j claims ∧ j ≠ k := by
  induction claims with
  | nil =>
      rcases hj with ⟨_, hmem, _⟩
      simp [removeClaimGraph] at hmem
  | cons c cs ih =>
      by_cases hck : c.id = k
      · simp [removeClaimGraph, hck] at hj
        refine ⟨?_, ?_⟩
        · rcases hj with ⟨d, hdmem, hdid⟩
          exact ⟨d, List.Mem.tail _ hdmem, hdid⟩
        · intro hjk
          rcases hj with ⟨d, hdmem, hdid⟩
          exact ClaimsDistinct_head_not_in_tail hdist
            (by
              simp only [List.mem_map]
              exact ⟨d, hdmem, hdid.trans (hjk.trans hck.symm)⟩)
      · rcases hj with ⟨d, hdmem, hdid⟩
        simp [removeClaimGraph, hck] at hdmem
        rcases hdmem with hhead | htail
        · subst d
          exact ⟨⟨c, by simp, hdid⟩, by
            intro hjk
            exact hck (hdid.trans hjk)⟩
        · rcases ih (ClaimsDistinct_tail hdist) ⟨d, htail, hdid⟩ with
            ⟨hjorig, hjne⟩
          rcases hjorig with ⟨e, hemem, heid⟩
          exact ⟨⟨e, List.Mem.tail _ hemem, heid⟩, hjne⟩

private lemma denyAll_canonical_diagnostics :
    GraphConsistencyP
        (DecisionPipeline.canonicalPipelineFor
          (P := GovernanceGraph) coupledDenyAllNode) ∧
      GraphSolidarityP
        (DecisionPipeline.canonicalPipelineFor
          (P := GovernanceGraph) coupledDenyAllNode) ∧
        GraphMonotonicityP
          (DecisionPipeline.canonicalPipelineFor
            (P := GovernanceGraph) coupledDenyAllNode) := by
  refine ⟨?_, ?_, ?_⟩
  · intro claims k j _hk _hj _hkj _hdist _hden
    simp [canonicalPipeline_decide_node, coupledDenyAllNode]
  · intro claims α hα j _hj
    change
      DecisionSystem.decide
          (DecisionPipeline.canonicalPipelineFor
            (P := GovernanceGraph) coupledDenyAllNode) claims j =
        DecisionSystem.decide
          (DecisionPipeline.canonicalPipelineFor
            (P := GovernanceGraph) coupledDenyAllNode)
          (claims.map fun c =>
            ⟨c.id, α * c.strength, mul_pos hα c.strength_pos,
              c.metadata⟩) j
    simp [canonicalPipeline_decide_node, coupledDenyAllNode]
  · intro claims k s' hs' j _hk _hdist _hbound hpermit
    simp [canonicalPipeline_decide_node, coupledDenyAllNode] at hpermit

private lemma permitAll_canonical_diagnostics :
    GraphConsistencyP
        (DecisionPipeline.canonicalPipelineFor
          (P := GovernanceGraph) coupledPermitAllNode) ∧
      GraphSolidarityP
        (DecisionPipeline.canonicalPipelineFor
          (P := GovernanceGraph) coupledPermitAllNode) ∧
        GraphMonotonicityP
          (DecisionPipeline.canonicalPipelineFor
            (P := GovernanceGraph) coupledPermitAllNode) := by
  refine ⟨?_, ?_, ?_⟩
  · intro claims k j _hk _hj _hkj _hdist hden
    rw [canonicalPipeline_decide_node] at hden
    exact BinaryDecision.noConfusion hden
  · intro claims α hα j _hj
    change
      DecisionSystem.decide
          (DecisionPipeline.canonicalPipelineFor
            (P := GovernanceGraph) coupledPermitAllNode) claims j =
        DecisionSystem.decide
          (DecisionPipeline.canonicalPipelineFor
            (P := GovernanceGraph) coupledPermitAllNode)
          (claims.map fun c =>
            ⟨c.id, α * c.strength, mul_pos hα c.strength_pos,
              c.metadata⟩) j
    simp [canonicalPipeline_decide_node, coupledPermitAllNode]
  · intro claims k s' hs' j _hk _hdist _hbound _hpermit
    simp [canonicalPipeline_decide_node, coupledPermitAllNode]

private lemma coupledDenyAllNode_claimantSymmetric :
    DecisionPipeline.ClaimantSymmetric
      (P := GovernanceGraph) coupledDenyAllNode := by
  intro claims k j hdist hk hj hsame
  rfl

private lemma coupledDenyAllNode_finiteEstateCoupled :
    DecisionPipeline.FiniteEstateCoupled
      (P := GovernanceGraph) coupledDenyAllNode := by
  intro claims hdistinct hscarce hadmissible
  rcases hscarce with ⟨hgen, _⟩
  exact ⟨hgen.displaced, hgen.displaced_in_claims, rfl⟩

private lemma coupledDenyAllNode_no_scarcityPressure :
    ¬ (∃ claims, ClaimsDistinct claims ∧
      DecisionPipeline.OverSubscribed claims ∧
        DecisionPipeline.IndividuallyAdmissible
          (P := GovernanceGraph) coupledDenyAllNode claims) := by
  rintro ⟨claims, _hdist, hscarce, hadmissible⟩
  rcases hscarce with ⟨hgen, _⟩
  rcases hgen.displaced_in_claims with ⟨c, hc, hid⟩
  have hpermit := hadmissible c hc
  change coupledDenyAllNode [c] c.id = BinaryDecision.Permit at hpermit
  simp [coupledDenyAllNode] at hpermit

private lemma coupledPermitAllNode_claimantSymmetric :
    DecisionPipeline.ClaimantSymmetric
      (P := GovernanceGraph) coupledPermitAllNode := by
  intro claims k j hdist hk hj hsame
  rfl

private lemma coupledPermitAllNode_scarcityPressure :
    ∃ claims, ClaimsDistinct claims ∧
      DecisionPipeline.OverSubscribed claims ∧
        DecisionPipeline.IndividuallyAdmissible
          (P := GovernanceGraph) coupledPermitAllNode claims := by
  refine ⟨medianWitnessClaims, medianWitnessClaims_distinct,
    ⟨medianWitnessObstructionGenerator, True.intro⟩, ?_⟩
  intro c hc
  rfl

private lemma coupledPermitAllNode_not_finiteEstateCoupled :
    ¬ DecisionPipeline.FiniteEstateCoupled
      (P := GovernanceGraph) coupledPermitAllNode := by
  intro hfinite
  rcases hfinite medianWitnessClaims medianWitnessClaims_distinct
      ⟨medianWitnessObstructionGenerator, True.intro⟩
      (by intro c hc; rfl) with
    ⟨k, _hk, hdeny⟩
  change coupledPermitAllNode medianWitnessClaims k = BinaryDecision.Deny at hdeny
  simp [coupledPermitAllNode] at hdeny

/-- Dropping `scarcity_pressure` is unsound: the all-deny stage is symmetric,
finite-estate coupled, and satisfies all three graph diagnostics, but it has no
admissible scarce profile. -/
theorem symmetricScarceCoupled_scarcity_necessary :
    ∃ node : GovernanceNodeFn,
      DecisionPipeline.ClaimantSymmetric (P := GovernanceGraph) node ∧
        DecisionPipeline.FiniteEstateCoupled (P := GovernanceGraph) node ∧
          ¬ (∃ claims, ClaimsDistinct claims ∧
            DecisionPipeline.OverSubscribed claims ∧
              DecisionPipeline.IndividuallyAdmissible
                (P := GovernanceGraph) node claims) ∧
            GraphConsistencyP
              (DecisionPipeline.canonicalPipelineFor
                (P := GovernanceGraph) node) ∧
              GraphSolidarityP
                (DecisionPipeline.canonicalPipelineFor
                  (P := GovernanceGraph) node) ∧
                GraphMonotonicityP
                  (DecisionPipeline.canonicalPipelineFor
                    (P := GovernanceGraph) node) :=
  ⟨coupledDenyAllNode, coupledDenyAllNode_claimantSymmetric,
    coupledDenyAllNode_finiteEstateCoupled,
    coupledDenyAllNode_no_scarcityPressure,
    denyAll_canonical_diagnostics⟩

/-- Dropping `finite_estate` is unsound: the permit-all stage is symmetric,
has scarce admissible pressure, and satisfies all three graph diagnostics, but
it never excludes anyone. -/
theorem symmetricScarceCoupled_finiteEstate_necessary :
    ∃ node : GovernanceNodeFn,
      DecisionPipeline.ClaimantSymmetric (P := GovernanceGraph) node ∧
        ¬ DecisionPipeline.FiniteEstateCoupled (P := GovernanceGraph) node ∧
          (∃ claims, ClaimsDistinct claims ∧
            DecisionPipeline.OverSubscribed claims ∧
              DecisionPipeline.IndividuallyAdmissible
                (P := GovernanceGraph) node claims) ∧
            GraphConsistencyP
              (DecisionPipeline.canonicalPipelineFor
                (P := GovernanceGraph) node) ∧
              GraphSolidarityP
                (DecisionPipeline.canonicalPipelineFor
                  (P := GovernanceGraph) node) ∧
                GraphMonotonicityP
                  (DecisionPipeline.canonicalPipelineFor
                    (P := GovernanceGraph) node) :=
  ⟨coupledPermitAllNode, coupledPermitAllNode_claimantSymmetric,
    coupledPermitAllNode_not_finiteEstateCoupled,
    coupledPermitAllNode_scarcityPressure,
    permitAll_canonical_diagnostics⟩

private def idIslandGateNode : GovernanceNodeFn := fun claims k =>
  if k = 0 then
    if InClaims 1 claims ∧ InClaims 2 claims then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit
  else if k = 1 ∨ k = 2 then
    BinaryDecision.Permit
  else
    BinaryDecision.Deny

private lemma idIslandGateNode_singleton_permit_iff
    (c : ClaimQ) :
    idIslandGateNode [c] c.id = BinaryDecision.Permit ↔
      c.id = 0 ∨ c.id = 1 ∨ c.id = 2 := by
  by_cases h0 : c.id = 0
  · simp [idIslandGateNode, InClaims, h0]
  · by_cases h1 : c.id = 1
    · simp [idIslandGateNode, h1]
    · by_cases h2 : c.id = 2
      · simp [idIslandGateNode, h2]
      · simp [idIslandGateNode, h0, h1, h2]

private lemma idIslandGateNode_individually_allowed
    {claims : List ClaimQ}
    (hadmissible :
      DecisionPipeline.IndividuallyAdmissible
        (P := GovernanceGraph) idIslandGateNode claims)
    {c : ClaimQ} (hc : c ∈ claims) :
    c.id = 0 ∨ c.id = 1 ∨ c.id = 2 := by
  exact (idIslandGateNode_singleton_permit_iff c).mp (hadmissible c hc)

private lemma inClaims_strengthenClaim_iff
    (target k : ClaimantId) (s' : ℚ) (hs' : 0 < s')
    (claims : List ClaimQ) :
    InClaims target (strengthenClaim k s' hs' claims) ↔
      InClaims target claims := by
  induction claims with
  | nil =>
      simp [strengthenClaim]
  | cons c cs ih =>
      by_cases hck : c.id = k
      · constructor
        · intro h
          rcases h with ⟨d, hdmem, hdid⟩
          simp [strengthenClaim, hck] at hdmem
          rcases hdmem with hhead | htail
          · subst d
            exact ⟨c, by simp, hck.trans hdid⟩
          · exact ⟨d, List.Mem.tail _ htail, hdid⟩
        · intro h
          rcases h with ⟨d, hdmem, hdid⟩
          cases hdmem with
          | head =>
              refine ⟨⟨c.id, s', hs', c.metadata⟩, ?_, ?_⟩
              · simp [strengthenClaim, hck]
              · simpa using hdid
          | tail _ htail =>
              exact ⟨d, by
                simp [strengthenClaim, hck]
                exact Or.inr htail, hdid⟩
      · constructor
        · intro h
          rcases h with ⟨d, hdmem, hdid⟩
          simp [strengthenClaim, hck] at hdmem
          rcases hdmem with hhead | htail
          · subst d
            exact ⟨c, by simp, hdid⟩
          · rcases (ih.mp ⟨d, htail, hdid⟩) with ⟨e, hemem, heid⟩
            exact ⟨e, List.Mem.tail _ hemem, heid⟩
        · intro h
          rcases h with ⟨d, hdmem, hdid⟩
          cases hdmem with
          | head =>
              exact ⟨c, by simp [strengthenClaim, hck], hdid⟩
          | tail _ htail =>
              rcases (ih.mpr ⟨d, htail, hdid⟩) with
                ⟨e, hemem, heid⟩
              exact ⟨e, by simp [strengthenClaim, hck, hemem], heid⟩

private lemma three_allowed_ids_cover
    {x y z : ClaimantId}
    (hx : x = 0 ∨ x = 1 ∨ x = 2)
    (hy : y = 0 ∨ y = 1 ∨ y = 2)
    (hz : z = 0 ∨ z = 1 ∨ z = 2)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (x = 0 ∨ y = 0 ∨ z = 0) ∧
      (x = 1 ∨ y = 1 ∨ z = 1) ∧
        (x = 2 ∨ y = 2 ∨ z = 2) := by
  refine ⟨?_, ?_, ?_⟩
  · by_cases hx0 : x = 0
    · exact Or.inl hx0
    · by_cases hy0 : y = 0
      · exact Or.inr (Or.inl hy0)
      · by_cases hz0 : z = 0
        · exact Or.inr (Or.inr hz0)
        · exfalso
          aesop
  · by_cases hx1 : x = 1
    · exact Or.inl hx1
    · by_cases hy1 : y = 1
      · exact Or.inr (Or.inl hy1)
      · by_cases hz1 : z = 1
        · exact Or.inr (Or.inr hz1)
        · exfalso
          aesop
  · by_cases hx2 : x = 2
    · exact Or.inl hx2
    · by_cases hy2 : y = 2
      · exact Or.inr (Or.inl hy2)
      · by_cases hz2 : z = 2
        · exact Or.inr (Or.inr hz2)
        · exfalso
          aesop

private lemma inClaims_of_three_id_cover
    {claims : List ClaimQ} {x y z target : ClaimantId}
    (hx : InClaims x claims) (hy : InClaims y claims)
    (hz : InClaims z claims)
    (hcover : x = target ∨ y = target ∨ z = target) :
    InClaims target claims := by
  rcases hcover with rfl | rfl | rfl
  · exact hx
  · exact hy
  · exact hz

private lemma idIslandGateNode_finiteEstateCoupled :
    DecisionPipeline.FiniteEstateCoupled
      (P := GovernanceGraph) idIslandGateNode := by
  intro claims hdistinct hscarce hadmissible
  rcases hscarce with ⟨hgen, _⟩
  rcases hgen.affected_weakest_after_removal.2.2 with
    ⟨stronger, hstronger_ne_affected, hstronger_removed, _hstronger⟩
  rcases inClaims_removeClaimGraph_to_original hdistinct hstronger_removed with
    ⟨hstronger_claims, hstronger_ne_displaced⟩
  rcases hgen.displaced_in_claims with ⟨dClaim, hdmem, hdid⟩
  rcases hgen.affected_in_claims with ⟨aClaim, hamem, haid⟩
  rcases hstronger_claims with ⟨sClaim, hsmem, hsid⟩
  have hd_allowed :
      hgen.displaced = 0 ∨ hgen.displaced = 1 ∨ hgen.displaced = 2 := by
    simpa [hdid] using
      idIslandGateNode_individually_allowed hadmissible hdmem
  have ha_allowed :
      hgen.affected = 0 ∨ hgen.affected = 1 ∨ hgen.affected = 2 := by
    simpa [haid] using
      idIslandGateNode_individually_allowed hadmissible hamem
  have hs_allowed :
      stronger = 0 ∨ stronger = 1 ∨ stronger = 2 := by
    simpa [hsid] using
      idIslandGateNode_individually_allowed hadmissible hsmem
  have hcover := three_allowed_ids_cover hd_allowed ha_allowed hs_allowed
    hgen.distinct_claimants hstronger_ne_displaced.symm
    hstronger_ne_affected.symm
  have hzero : InClaims 0 claims :=
    inClaims_of_three_id_cover hgen.displaced_in_claims
      hgen.affected_in_claims ⟨sClaim, hsmem, hsid⟩ hcover.1
  have hone : InClaims 1 claims :=
    inClaims_of_three_id_cover hgen.displaced_in_claims
      hgen.affected_in_claims ⟨sClaim, hsmem, hsid⟩ hcover.2.1
  have htwo : InClaims 2 claims :=
    inClaims_of_three_id_cover hgen.displaced_in_claims
      hgen.affected_in_claims ⟨sClaim, hsmem, hsid⟩ hcover.2.2
  refine ⟨0, hzero, ?_⟩
  change
    (if InClaims 1 claims ∧ InClaims 2 claims then
      BinaryDecision.Deny
    else
      BinaryDecision.Permit) = BinaryDecision.Deny
  simp [hone, htwo]

private lemma idIslandGateNode_scarcityPressure :
    ∃ claims, ClaimsDistinct claims ∧
      DecisionPipeline.OverSubscribed claims ∧
        DecisionPipeline.IndividuallyAdmissible
          (P := GovernanceGraph) idIslandGateNode claims := by
  refine ⟨medianWitnessClaims, medianWitnessClaims_distinct,
    ⟨medianWitnessObstructionGenerator, True.intro⟩, ?_⟩
  intro c hc
  simp [medianWitnessClaims] at hc
  rcases hc with rfl | rfl | rfl <;>
    native_decide

private lemma idIslandGateNode_not_claimantSymmetric :
    ¬ DecisionPipeline.ClaimantSymmetric
      (P := GovernanceGraph) idIslandGateNode := by
  intro hsymm
  let c0 : ClaimQ := ⟨0, 1, by norm_num, []⟩
  let c1 : ClaimQ := ⟨1, 1, by norm_num, []⟩
  let c2 : ClaimQ := ⟨2, 1, by norm_num, []⟩
  let claims := [c0, c1, c2]
  have hdistinct : ClaimsDistinct claims := by
    unfold claims c0 c1 c2 ClaimsDistinct
    show ([0, 1, 2] : List Nat).Nodup
    decide
  have hsame : lookupStrength 0 claims = lookupStrength 1 claims := by
    native_decide
  have heq := hsymm claims 0 1 hdistinct
    (by native_decide) (by native_decide) hsame
  have hdeny : idIslandGateNode claims 0 = BinaryDecision.Deny := by
    native_decide
  have hpermit : idIslandGateNode claims 1 = BinaryDecision.Permit := by
    native_decide
  change idIslandGateNode claims 0 = idIslandGateNode claims 1 at heq
  rw [hdeny, hpermit] at heq
  exact BinaryDecision.noConfusion heq

private lemma idIslandGateNode_canonical_diagnostics :
    GraphConsistencyP
        (DecisionPipeline.canonicalPipelineFor
          (P := GovernanceGraph) idIslandGateNode) ∧
      GraphSolidarityP
        (DecisionPipeline.canonicalPipelineFor
          (P := GovernanceGraph) idIslandGateNode) ∧
        GraphMonotonicityP
          (DecisionPipeline.canonicalPipelineFor
            (P := GovernanceGraph) idIslandGateNode) := by
  refine ⟨?_, ?_, ?_⟩
  · intro claims k j hk hj hkj hdist hden
    rw [canonicalPipeline_decide_node] at hden
    rw [canonicalPipeline_decide_node, canonicalPipeline_decide_node]
    unfold idIslandGateNode at hden ⊢
    by_cases hj0 : j = 0
    · subst j
      have hk_ne_one : k ≠ 1 := by
        intro hk1
        simp [hk1] at hden
      have hk_ne_two : k ≠ 2 := by
        intro hk2
        simp [hk2] at hden
      have hpreserve_one :
          InClaims 1 (removeClaimGraph k claims) ↔ InClaims 1 claims := by
        constructor
        · intro h
          exact (inClaims_removeClaimGraph_to_original hdist h).1
        · exact inClaims_removeClaimGraph_of_ne hk_ne_one.symm
      have hpreserve_two :
          InClaims 2 (removeClaimGraph k claims) ↔ InClaims 2 claims := by
        constructor
        · intro h
          exact (inClaims_removeClaimGraph_to_original hdist h).1
        · exact inClaims_removeClaimGraph_of_ne hk_ne_two.symm
      simp [hpreserve_one, hpreserve_two]
    · by_cases hj12 : j = 1 ∨ j = 2
      · simp [hj0, hj12]
      · simp [hj0, hj12]
  · intro claims α hα j hj
    change
      DecisionSystem.decide
          (DecisionPipeline.canonicalPipelineFor
            (P := GovernanceGraph) idIslandGateNode) claims j =
        DecisionSystem.decide
          (DecisionPipeline.canonicalPipelineFor
            (P := GovernanceGraph) idIslandGateNode)
          (claims.map fun c =>
            ⟨c.id, α * c.strength, mul_pos hα c.strength_pos,
              c.metadata⟩) j
    rw [canonicalPipeline_decide_node, canonicalPipeline_decide_node]
    unfold idIslandGateNode
    by_cases hj0 : j = 0
    · subst j
      have hscale_one :
          InClaims 1
              (claims.map fun c =>
                ⟨c.id, α * c.strength, mul_pos hα c.strength_pos,
                  c.metadata⟩) ↔ InClaims 1 claims := by
        constructor
        · intro h
          rcases h with ⟨c, hc, hid⟩
          simp at hc
          rcases hc with ⟨orig, horig, horig_eq⟩
          have hidorig : orig.id = 1 := by
            have hidscaled :
                (⟨orig.id, α * orig.strength,
                  mul_pos hα orig.strength_pos, orig.metadata⟩ :
                    ClaimQ).id = c.id :=
              congrArg Claim.id horig_eq
            exact hidscaled.trans hid
          exact ⟨orig, horig, hidorig⟩
        · intro h
          rcases h with ⟨c, hc, hid⟩
          refine ⟨⟨c.id, α * c.strength, mul_pos hα c.strength_pos,
            c.metadata⟩, ?_, ?_⟩
          · exact List.mem_map.mpr ⟨c, hc, rfl⟩
          · simpa using hid
      have hscale_two :
          InClaims 2
              (claims.map fun c =>
                ⟨c.id, α * c.strength, mul_pos hα c.strength_pos,
                  c.metadata⟩) ↔ InClaims 2 claims := by
        constructor
        · intro h
          rcases h with ⟨c, hc, hid⟩
          simp at hc
          rcases hc with ⟨orig, horig, horig_eq⟩
          have hidorig : orig.id = 2 := by
            have hidscaled :
                (⟨orig.id, α * orig.strength,
                  mul_pos hα orig.strength_pos, orig.metadata⟩ :
                    ClaimQ).id = c.id :=
              congrArg Claim.id horig_eq
            exact hidscaled.trans hid
          exact ⟨orig, horig, hidorig⟩
        · intro h
          rcases h with ⟨c, hc, hid⟩
          refine ⟨⟨c.id, α * c.strength, mul_pos hα c.strength_pos,
            c.metadata⟩, ?_, ?_⟩
          · exact List.mem_map.mpr ⟨c, hc, rfl⟩
          · simpa using hid
      simp [hscale_one, hscale_two]
    · by_cases hj12 : j = 1 ∨ j = 2
      · simp [hj0, hj12]
      · simp [hj0, hj12]
  · intro claims k s' hs' j hk hdist hbound hpermit
    rw [canonicalPipeline_decide_node] at hpermit
    rw [canonicalPipeline_decide_node]
    unfold idIslandGateNode at hpermit ⊢
    by_cases hj0 : j = 0
    · subst j
      have hstrengthen_one :
          InClaims 1 (strengthenClaim k s' hs' claims) ↔ InClaims 1 claims := by
        exact inClaims_strengthenClaim_iff 1 k s' hs' claims
      have hstrengthen_two :
          InClaims 2 (strengthenClaim k s' hs' claims) ↔ InClaims 2 claims := by
        exact inClaims_strengthenClaim_iff 2 k s' hs' claims
      simpa [hstrengthen_one, hstrengthen_two] using hpermit
    · by_cases hj12 : j = 1 ∨ j = 2
      · simp [hj0, hj12]
      · simp [hj0, hj12] at hpermit

/-- Dropping `symmetry` is unsound: an ID-island stage has finite-estate
coupling, scarce admissible pressure, and all three graph diagnostics, while
equal-strength island peers receive different decisions. -/
theorem symmetricScarceCoupled_symmetry_necessary :
    ∃ node : GovernanceNodeFn,
      ¬ DecisionPipeline.ClaimantSymmetric (P := GovernanceGraph) node ∧
        DecisionPipeline.FiniteEstateCoupled (P := GovernanceGraph) node ∧
          (∃ claims, ClaimsDistinct claims ∧
            DecisionPipeline.OverSubscribed claims ∧
              DecisionPipeline.IndividuallyAdmissible
                (P := GovernanceGraph) node claims) ∧
            GraphConsistencyP
              (DecisionPipeline.canonicalPipelineFor
                (P := GovernanceGraph) node) ∧
              GraphSolidarityP
                (DecisionPipeline.canonicalPipelineFor
                  (P := GovernanceGraph) node) ∧
                GraphMonotonicityP
                  (DecisionPipeline.canonicalPipelineFor
                    (P := GovernanceGraph) node) :=
  ⟨idIslandGateNode, idIslandGateNode_not_claimantSymmetric,
    idIslandGateNode_finiteEstateCoupled, idIslandGateNode_scarcityPressure,
    idIslandGateNode_canonical_diagnostics⟩

/-! ## Two-tier separation witness -/

/-- Max-rule gate: a claimant is permitted exactly when their own strength is
maximal among the profile's claimants. -/
def maxStrengthNode : GovernanceNodeFn := fun claims k =>
  if ∀ c ∈ claims, c.strength ≤ lookupStrength k claims then
    BinaryDecision.Permit
  else
    BinaryDecision.Deny

lemma maxStrengthNode_claimantSymmetric :
    DecisionPipeline.ClaimantSymmetric
      (P := GovernanceGraph) maxStrengthNode := by
  intro claims k j hdist hk hj hsame
  have hiff :
      (∀ c ∈ claims, c.strength ≤ lookupStrength k claims) ↔
        (∀ c ∈ claims, c.strength ≤ lookupStrength j claims) := by
    rw [hsame]
  change maxStrengthNode claims k = maxStrengthNode claims j
  unfold maxStrengthNode
  by_cases hkmax : ∀ c ∈ claims, c.strength ≤ lookupStrength k claims
  · have hjmax := hiff.mp hkmax
    rw [if_pos hkmax, if_pos hjmax]
  · have hjnotmax : ¬ ∀ c ∈ claims,
        c.strength ≤ lookupStrength j claims := by
      intro hjmax
      exact hkmax (hiff.mpr hjmax)
    rw [if_neg hkmax, if_neg hjnotmax]

lemma maxStrengthNode_finiteEstateCoupled :
    DecisionPipeline.FiniteEstateCoupled
      (P := GovernanceGraph) maxStrengthNode := by
  intro claims hdistinct hscarce hadmissible
  rcases hscarce with ⟨hgen, _⟩
  refine ⟨hgen.displaced, hgen.displaced_in_claims, ?_⟩
  unfold maxStrengthNode
  apply if_neg
  intro hmax
  rcases hgen.displaced_weakest.2.2 with
    ⟨stronger, _hne, hstronger, hlt⟩
  rcases hstronger with ⟨c, hc, hid⟩
  have hlookup :
      lookupStrength stronger claims = c.strength := by
    rw [← hid]
    exact lookupStrength_eq_of_mem_distinct hdistinct hc
  have hle := hmax c hc
  rw [← hlookup] at hle
  linarith

lemma maxStrengthNode_medianWitness_individuallyAdmissible :
    DecisionPipeline.IndividuallyAdmissible
      (P := GovernanceGraph) maxStrengthNode medianWitnessClaims := by
  intro c hc
  simp [medianWitnessClaims] at hc
  rcases hc with rfl | rfl | rfl <;>
    native_decide

lemma maxStrengthNode_scarcityPressure :
    ∃ claims, ClaimsDistinct claims ∧
      DecisionPipeline.OverSubscribed claims ∧
        DecisionPipeline.IndividuallyAdmissible
          (P := GovernanceGraph) maxStrengthNode claims := by
  exact ⟨medianWitnessClaims, medianWitnessClaims_distinct,
    ⟨medianWitnessObstructionGenerator, True.intro⟩,
    maxStrengthNode_medianWitness_individuallyAdmissible⟩

theorem maxStrengthNode_symmetricScarceCoupled :
    DecisionPipeline.SymmetricScarceCoupledAllocator
      (P := GovernanceGraph) maxStrengthNode where
  symmetry := maxStrengthNode_claimantSymmetric
  finite_estate := maxStrengthNode_finiteEstateCoupled
  scarcity_pressure := maxStrengthNode_scarcityPressure

private lemma mem_removeClaimGraph_of_ne_id
    {claims : List ClaimQ} {c : ClaimQ} {k : ClaimantId}
    (hc : c ∈ claims) (hne : c.id ≠ k) :
    c ∈ removeClaimGraph k claims := by
  induction claims with
  | nil =>
      simp at hc
  | cons d ds ih =>
      by_cases hdk : d.id = k
      · simp [removeClaimGraph, hdk]
        cases hc with
        | head =>
            exact False.elim (hne hdk)
        | tail _ htail =>
            exact htail
      · simp [removeClaimGraph, hdk]
        cases hc with
        | head =>
            simp
        | tail _ htail =>
            exact Or.inr (ih htail)

private lemma mem_of_mem_removeClaimGraph
    {claims : List ClaimQ} {c : ClaimQ} {k : ClaimantId}
    (hc : c ∈ removeClaimGraph k claims) :
    c ∈ claims := by
  induction claims with
  | nil =>
      simp [removeClaimGraph] at hc
  | cons d ds ih =>
      by_cases hdk : d.id = k
      · simp [removeClaimGraph, hdk] at hc
        exact List.Mem.tail _ hc
      · simp [removeClaimGraph, hdk] at hc
        rcases hc with hhead | htail
        · simp [hhead]
        · exact List.Mem.tail _ (ih htail)

lemma maxStrengthNode_graphConsistencyP :
    GraphConsistencyP
      (DecisionPipeline.canonicalPipelineFor
        (P := GovernanceGraph) maxStrengthNode) := by
  intro claims k j hk hj hkj hdist hden
  rw [canonicalPipeline_decide_node] at hden
  rw [canonicalPipeline_decide_node, canonicalPipeline_decide_node]
  unfold maxStrengthNode at hden ⊢
  by_cases hjmax :
      ∀ c ∈ claims, c.strength ≤ lookupStrength j claims
  · have hjmax_removed :
      ∀ c ∈ removeClaimGraph k claims,
        c.strength ≤ lookupStrength j (removeClaimGraph k claims) := by
      intro c hc
      have hcclaims : c ∈ claims := mem_of_mem_removeClaimGraph hc
      have hle := hjmax c hcclaims
      rw [lookupStrength_removeClaimGraph_of_ne (claims := claims)
          (j := j) (k := k) hkj.symm]
      exact hle
    rw [if_pos hjmax, if_pos hjmax_removed]
  · have hknotmax :
      ¬ ∀ c ∈ claims, c.strength ≤ lookupStrength k claims := by
      intro hkmax
      rw [if_pos hkmax] at hden
      exact BinaryDecision.noConfusion hden
    have hjnotmax_removed :
      ¬ ∀ c ∈ removeClaimGraph k claims,
        c.strength ≤ lookupStrength j (removeClaimGraph k claims) := by
      push Not at hjmax hknotmax ⊢
      rcases hjmax with ⟨c, hcclaims, hj_lt_c⟩
      by_cases hck : c.id = k
      ·
        have hlookup_k : lookupStrength k claims = c.strength := by
          rw [← hck]
          exact lookupStrength_eq_of_mem_distinct hdist hcclaims
        rcases hknotmax with ⟨w, hwclaims, hk_lt_w⟩
        have hwne : w.id ≠ k := by
          intro hwk
          have hlookup_w : lookupStrength k claims = w.strength := by
            rw [← hwk]
            exact lookupStrength_eq_of_mem_distinct hdist hwclaims
          linarith
        refine ⟨w, mem_removeClaimGraph_of_ne_id hwclaims hwne, ?_⟩
        rw [lookupStrength_removeClaimGraph_of_ne (claims := claims)
            (j := j) (k := k) hkj.symm]
        linarith
      · refine ⟨c, mem_removeClaimGraph_of_ne_id hcclaims hck, ?_⟩
        rw [lookupStrength_removeClaimGraph_of_ne (claims := claims)
            (j := j) (k := k) hkj.symm]
        exact hj_lt_c
    rw [if_neg hjmax, if_neg hjnotmax_removed]

/-- The max-rule witness separates the tiers: the widened
`SymmetricScarceCoupledAllocator` class contains a canonical scarce symmetric
gate whose singleton surface satisfies graph consistency, so the narrow
structural class's stronger conclusion that consistency and monotonicity must
each fail cannot be widened to the three-field class. -/
theorem maxStrengthNode_separates_structural_from_symmetricScarceCoupled :
    DecisionPipeline.SymmetricScarceCoupledAllocator
        (P := GovernanceGraph) maxStrengthNode ∧
      GraphConsistencyP
        (DecisionPipeline.canonicalPipelineFor
          (P := GovernanceGraph) maxStrengthNode) :=
  ⟨maxStrengthNode_symmetricScarceCoupled,
    maxStrengthNode_graphConsistencyP⟩

end SymmetricScarceCoupledMedianWitness

end Legitimacy
