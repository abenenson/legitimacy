/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.SymmetricScarceCoupled
import Legitimacy.Impossibility.PeerRelativeReachable

/-!
# Obstruction for symmetric scarce coupled allocators

The proof uses only the widened class fields. Solidarity and cross-monotonicity
make the exposed canonical surface blind to strength changes that preserve IDs
and metadata. Applying that blindness to an equal-strength clone of the scarce
profile turns claimant symmetry into an all-deny overloaded profile; consistency
then cascades denial down to an individually admissible singleton.
-/

set_option autoImplicit false

namespace Legitimacy

open SymmetricScarceCoupled

namespace DecisionPipeline

variable {P : Type} [DecisionPipeline P]

private lemma canonical_decide_eq_eval (node : NodeOf P)
    (claims : List ClaimQ) (j : ClaimantId) :
    DecisionSystem.decide (DecisionPipeline.canonicalPipelineFor node) claims j =
      DecisionPipeline.evalNode node claims j :=
  DecisionPipeline.decide_canonicalPipelineFor node claims j

/-- Canonical singleton obstruction for the widened coupled class. -/
theorem symmetricScarceCoupled_canonical_obstructed
    (node : NodeOf P)
    (hcoupled : SymmetricScarceCoupledAllocator node) :
    ¬ (GraphConsistencyP (DecisionPipeline.canonicalPipelineFor node) ∧
      GraphSolidarityP (DecisionPipeline.canonicalPipelineFor node) ∧
      GraphMonotonicityP (DecisionPipeline.canonicalPipelineFor node)) := by
  intro haxioms
  let K := DecisionPipeline.canonicalPipelineFor node
  have hcons : GraphConsistencyP K := haxioms.1
  have hsol : GraphSolidarityP K := haxioms.2.1
  have hmon : GraphMonotonicityP K := haxioms.2.2
  rcases hcoupled.scarcity_pressure with
    ⟨claims, hdistinct, hscarce, hadmissible⟩
  rcases hcoupled.finite_estate claims hdistinct hscarce hadmissible with
    ⟨denied, hdeniedIn, hdeniedEval⟩
  let equalized := equalStrengthClaims claims
  have hshape : SameIdsMetadata claims equalized := by
    simpa [equalized] using sameIdsMetadata_equalStrengthClaims claims
  have hdistinctEq : ClaimsDistinct equalized := by
    simpa [equalized] using claimsDistinct_equalStrengthClaims hdistinct
  have hdeniedInEq : InClaims denied equalized := by
    simpa [equalized] using inClaims_equalStrengthClaims hdeniedIn
  have hdeniedK :
      DecisionSystem.decide K claims denied = BinaryDecision.Deny := by
    exact (canonical_decide_eq_eval node claims denied).trans hdeniedEval
  have hallDenied :
      ∀ j, InClaims j claims →
        DecisionSystem.decide K claims j = BinaryDecision.Deny := by
    intro j hj
    have hjEq : InClaims j equalized := by
      simpa [equalized] using inClaims_equalStrengthClaims hj
    have hblindDenied :
        DecisionSystem.decide K claims denied =
          DecisionSystem.decide K equalized denied :=
      decisionSystem_solidarity_monotonicity_sameIdsMetadata_blind
        K hsol hmon hshape hdistinct denied hdeniedIn
    have hblindJ :
        DecisionSystem.decide K claims j =
          DecisionSystem.decide K equalized j :=
      decisionSystem_solidarity_monotonicity_sameIdsMetadata_blind
        K hsol hmon hshape hdistinct j hj
    have hsameStrength :
        lookupStrength denied equalized = lookupStrength j equalized := by
      rw [lookupStrength_equalStrengthClaims_of_mem hdeniedInEq,
        lookupStrength_equalStrengthClaims_of_mem hjEq]
    have hsymmEval :
        DecisionPipeline.evalNode node equalized denied =
          DecisionPipeline.evalNode node equalized j :=
      hcoupled.symmetry equalized denied j hdistinctEq hdeniedInEq hjEq
        hsameStrength
    have hsymmK :
        DecisionSystem.decide K equalized denied =
          DecisionSystem.decide K equalized j := by
      calc
        DecisionSystem.decide K equalized denied =
            DecisionPipeline.evalNode node equalized denied :=
          canonical_decide_eq_eval node equalized denied
        _ = DecisionPipeline.evalNode node equalized j := hsymmEval
        _ = DecisionSystem.decide K equalized j :=
          (canonical_decide_eq_eval node equalized j).symm
    have hEqDenied :
        DecisionSystem.decide K equalized denied = BinaryDecision.Deny := by
      rw [← hblindDenied]
      exact hdeniedK
    have hEqJ :
        DecisionSystem.decide K equalized j = BinaryDecision.Deny := by
      rw [← hsymmK]
      exact hEqDenied
    rw [hblindJ]
    exact hEqJ
  have hnonempty : claims ≠ [] := by
    intro hnil
    rw [hnil] at hdeniedIn
    rcases hdeniedIn with ⟨_, hmem, _⟩
    simp at hmem
  rcases exists_denied_singleton_of_all_denied
      (K := K) hcons hnonempty hdistinct hallDenied with
    ⟨c, hcmem, hsingletonDeny⟩
  have hsingletonPermitEval :
      DecisionPipeline.evalNode node [c] c.id = BinaryDecision.Permit :=
    hadmissible c hcmem
  have hsingletonPermit :
      DecisionSystem.decide K [c] c.id = BinaryDecision.Permit := by
    exact (canonical_decide_eq_eval node [c] c.id).trans
      hsingletonPermitEval
  rw [hsingletonPermit] at hsingletonDeny
  exact BinaryDecision.noConfusion hsingletonDeny

end DecisionPipeline

/-- Complete first-effective surfaces over widened coupled allocators cannot
jointly satisfy consistency, solidarity, and cross-monotonicity. -/
theorem symmetric_scarce_coupled_allocators_obstructed
    {P : Type} [DecisionPipeline P]
    (G pref tail : P) (node : DecisionPipeline.NodeOf P)
    (hcoupled : SymmetricScarceCoupledAllocator node)
    (heffective : DecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : DecisionPipeline.CompleteTailForNode node tail) :
    ¬ (GraphConsistencyP G ∧ GraphSolidarityP G ∧ GraphMonotonicityP G) := by
  intro haxioms
  have heq : DecisionSystem.Equivalent G
      (DecisionPipeline.canonicalPipelineFor node) :=
    DecisionPipeline.effectiveSurfaceForNode_completeTail_decision_equivalent_to_canonical
      G pref tail node heffective hcomplete
  exact
    DecisionPipeline.symmetricScarceCoupled_canonical_obstructed node hcoupled
      ⟨(GraphConsistencyP_congr heq).mp haxioms.1,
        (GraphSolidarityP_congr heq).mp haxioms.2.1,
        (GraphMonotonicityP_congr heq).mp haxioms.2.2⟩

namespace DecisionPipeline

variable {P : Type} [DecisionPipeline P]

/-- Reachability class for a widened coupled decisive stage in the middle of a
pipeline. -/
def ReachableSymmetricScarceCoupledStage
    (G pref : P) (node : NodeOf P) (suffix : P) : Prop :=
  TransparentPrefix pref ∧
    SymmetricScarceCoupledAllocator node ∧
      NonDenyingSuffix node suffix ∧
        G = composedPipeline pref node suffix

lemma ReachableSymmetricScarceCoupledStage.effectiveSurfaceForNode
    {G pref suffix : P} {node : NodeOf P}
    (hreach : ReachableSymmetricScarceCoupledStage G pref node suffix) :
    EffectiveSurfaceForNode node G pref suffix := by
  rcases hreach with ⟨hprefix, _hcoupled, _hsuffix, hshape⟩
  rw [hshape]
  exact hprefix.effectiveSurface

lemma ReachableSymmetricScarceCoupledStage.completeTailForNode
    {G pref suffix : P} {node : NodeOf P}
    (hreach : ReachableSymmetricScarceCoupledStage G pref node suffix) :
    CompleteTailForNode node suffix :=
  hreach.2.2.1.completeTailForNode

lemma ReachableSymmetricScarceCoupledStage.coupled
    {G pref suffix : P} {node : NodeOf P}
    (hreach : ReachableSymmetricScarceCoupledStage G pref node suffix) :
    SymmetricScarceCoupledAllocator node :=
  hreach.2.1

end DecisionPipeline

/-- Root-facing spelling for the widened reachable-stage class. -/
abbrev ReachableSymmetricScarceCoupledStage
    {P : Type} [DecisionPipeline P]
    (G pref : P) (node : DecisionPipeline.NodeOf P) (suffix : P) : Prop :=
  DecisionPipeline.ReachableSymmetricScarceCoupledStage G pref node suffix

/-- Reachable-stage wrapper for the widened coupled obstruction. -/
theorem reachable_symmetric_scarce_coupled_stage_obstructs_diagnostics
    {P : Type} [DecisionPipeline P]
    (G pref : P) (node : DecisionPipeline.NodeOf P) (suffix : P)
    (hreach : ReachableSymmetricScarceCoupledStage G pref node suffix) :
    ¬ (GraphConsistencyP G ∧ GraphSolidarityP G ∧ GraphMonotonicityP G) :=
  symmetric_scarce_coupled_allocators_obstructed G pref suffix node
    (DecisionPipeline.ReachableSymmetricScarceCoupledStage.coupled hreach)
    (DecisionPipeline.ReachableSymmetricScarceCoupledStage.effectiveSurfaceForNode
      hreach)
    (DecisionPipeline.ReachableSymmetricScarceCoupledStage.completeTailForNode
      hreach)

/-- Structural scarce peer-relative allocators enter the widened theorem by
forgetting the two rank laws. -/
theorem structural_scarce_peer_relative_allocators_obstructed_via_coupled
    {P : Type} [DecisionPipeline P]
    (G pref tail : P) (node : DecisionPipeline.NodeOf P)
    (hstruct : StructuralScarcePeerRelativeAllocator node)
    (heffective : DecisionPipeline.EffectiveSurfaceForNode node G pref tail)
    (hcomplete : DecisionPipeline.CompleteTailForNode node tail) :
    ¬ (GraphConsistencyP G ∧ GraphSolidarityP G ∧ GraphMonotonicityP G) :=
  symmetric_scarce_coupled_allocators_obstructed G pref tail node
    (DecisionPipeline.structuralScarcePeerRelativeAllocator_symmetricScarceCoupled
      hstruct)
    heffective hcomplete

/-! ## Concrete median-rule witness facts -/

namespace SymmetricScarceCoupledMedianWitness

def medianWitnessA : ClaimQ := ⟨0, 1 / 4, by norm_num, []⟩
def medianWitnessB : ClaimQ := ⟨1, 1 / 2, by norm_num, []⟩
def medianWitnessC : ClaimQ := ⟨2, 3 / 4, by norm_num, []⟩

def medianWitnessClaims : List ClaimQ :=
  [medianWitnessA, medianWitnessB, medianWitnessC]

lemma medianWitnessClaims_distinct :
    ClaimsDistinct medianWitnessClaims := by
  unfold ClaimsDistinct medianWitnessClaims medianWitnessA medianWitnessB
    medianWitnessC
  show ([0, 1, 2] : List Nat).Nodup
  decide

private lemma in_medianWitnessClaims_ids {j : ClaimantId}
    (h : InClaims j medianWitnessClaims) :
    j = 0 ∨ j = 1 ∨ j = 2 := by
  rcases h with ⟨c, hc, hid⟩
  simp [medianWitnessClaims] at hc
  rcases hc with hc | hc | hc
  · subst c
    simp [medianWitnessA] at hid
    exact Or.inl hid.symm
  · subst c
    simp [medianWitnessB] at hid
    exact Or.inr (Or.inl hid.symm)
  · subst c
    simp [medianWitnessC] at hid
    exact Or.inr (Or.inr hid.symm)

private lemma in_strengthenedMedianWitnessClaims_ids {j : ClaimantId}
    (h :
      InClaims j
        (strengthenClaim 0 (3 / 4) (by norm_num)
          medianWitnessClaims)) :
    j = 0 ∨ j = 1 ∨ j = 2 := by
  rcases h with ⟨c, hc, hid⟩
  simp [medianWitnessClaims, medianWitnessA, medianWitnessB,
    medianWitnessC, strengthenClaim] at hc
  rcases hc with hc | hc | hc
  · subst c
    simp at hid
    exact Or.inl hid.symm
  · subst c
    simp at hid
    exact Or.inr (Or.inl hid.symm)
  · subst c
    simp at hid
    exact Or.inr (Or.inr hid.symm)

private lemma in_removedMedianWitnessClaims_ids {j : ClaimantId}
    (h : InClaims j (removeClaimGraph 0 medianWitnessClaims)) :
    j = 1 ∨ j = 2 := by
  rcases h with ⟨c, hc, hid⟩
  simp [medianWitnessClaims, medianWitnessA, medianWitnessB,
    medianWitnessC, removeClaimGraph] at hc
  rcases hc with hc | hc
  · subst c
    simp at hid
    exact Or.inl hid.symm
  · subst c
    simp at hid
    exact Or.inr hid.symm

lemma medianWitnessB_has_weaker :
    DecisionPipeline.HasStrictlyWeakerPeer medianWitnessClaims 1 := by
  refine ⟨0, ?_, ?_, ?_⟩ <;> native_decide

lemma medianWitnessA_weakest :
    DecisionPipeline.WeakestWithStrongerPeer medianWitnessClaims 0 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · intro j hj
    rcases in_medianWitnessClaims_ids hj with rfl | rfl | rfl <;>
      native_decide
  · refine ⟨1, ?_, ?_, ?_⟩ <;> native_decide

lemma medianWitnessB_weakest_after_strengthening :
    DecisionPipeline.WeakestWithStrongerPeer
      (strengthenClaim 0 (3 / 4) (by norm_num) medianWitnessClaims) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · intro j hj
    rcases in_strengthenedMedianWitnessClaims_ids hj with
      rfl | rfl | rfl <;> native_decide
  · refine ⟨0, ?_, ?_, ?_⟩ <;> native_decide

lemma medianWitnessB_weakest_after_removal :
    DecisionPipeline.WeakestWithStrongerPeer
      (removeClaimGraph 0 medianWitnessClaims) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · intro j hj
    rcases in_removedMedianWitnessClaims_ids hj with rfl | rfl <;>
      native_decide
  · refine ⟨2, ?_, ?_, ?_⟩ <;> native_decide

def medianWitnessObstructionGenerator :
    DecisionPipeline.ObstructionGenerator medianWitnessClaims where
  displaced := 0
  affected := 1
  strengthened_strength := 3 / 4
  strengthened_strength_pos := by norm_num
  distinct_claimants := by decide
  displaced_in_claims := by native_decide
  affected_in_claims := by native_decide
  affected_in_strengthened := by native_decide
  affected_in_removed := by native_decide
  strengthened_claims_distinct := by
    unfold ClaimsDistinct medianWitnessClaims medianWitnessA medianWitnessB
      medianWitnessC strengthenClaim
    show ([0, 1, 2] : List Nat).Nodup
    decide
  removed_claims_distinct := by
    unfold ClaimsDistinct
    simp [medianWitnessClaims, medianWitnessA, medianWitnessB,
      medianWitnessC, removeClaimGraph]
  strengthened_bound := by
    intro c hc hid
    rcases List.mem_cons.mp hc with hcA | htail
    · subst c
      simp [medianWitnessA] at hid ⊢
      norm_num
    · rcases List.mem_cons.mp htail with hcB | htail2
      · subst c
        simp [medianWitnessB] at hid
      · rcases List.mem_cons.mp htail2 with hcC | hnil
        · subst c
          simp [medianWitnessC] at hid
        · exact False.elim (List.not_mem_nil hnil)
  affected_strength_preserved := by native_decide
  affected_has_weaker := medianWitnessB_has_weaker
  displaced_weakest := medianWitnessA_weakest
  affected_weakest_after_strengthening :=
    medianWitnessB_weakest_after_strengthening
  affected_weakest_after_removal := medianWitnessB_weakest_after_removal

lemma peerRelativeNode_claimantSymmetric :
    DecisionPipeline.ClaimantSymmetric
      (P := GovernanceGraph) peerRelativeNode := by
  intro claims k j _hdist _hk _hj hsame
  change peerRelativeNode claims k = peerRelativeNode claims j
  simp [peerRelativeNode, hsame]

lemma peerRelativeNode_medianWitness_individuallyAdmissible :
    DecisionPipeline.IndividuallyAdmissible
      (P := GovernanceGraph) peerRelativeNode medianWitnessClaims := by
  intro c hc
  simp [medianWitnessClaims] at hc
  rcases hc with hc | hc | hc
  · subst c
    native_decide
  · subst c
    native_decide
  · subst c
    native_decide

lemma peerRelativeNode_medianWitness_scarcity_pressure :
    ∃ claims, ClaimsDistinct claims ∧
      DecisionPipeline.OverSubscribed claims ∧
        DecisionPipeline.IndividuallyAdmissible
          (P := GovernanceGraph) peerRelativeNode claims := by
  exact
    ⟨medianWitnessClaims, medianWitnessClaims_distinct,
      ⟨medianWitnessObstructionGenerator, True.intro⟩,
      peerRelativeNode_medianWitness_individuallyAdmissible⟩

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

private lemma countAtMost_eq_zero_of_forall_not_le
    {claims : List ClaimQ} {s : ℚ}
    (hnone : ∀ c ∈ claims, ¬ c.strength ≤ s) :
    countAtMost claims s = 0 := by
  induction claims with
  | nil =>
      simp [countAtMost]
  | cons c cs ih =>
      have hc : ¬ c.strength ≤ s := hnone c (by simp)
      have htail : ∀ d ∈ cs, ¬ d.strength ≤ s := by
        intro d hd
        exact hnone d (List.Mem.tail _ hd)
      simp [countAtMost, hc, ih htail]

private lemma countAtMost_eq_one_of_unique_atMost
    {claims : List ClaimQ} {d : ClaimantId} {s : ℚ}
    (hdmem : InClaims d claims)
    (hds : lookupStrength d claims = s)
    (hdist : ClaimsDistinct claims)
    (huniq : ∀ j, InClaims j claims →
      lookupStrength j claims ≤ s → j = d) :
    countAtMost claims s = 1 := by
  induction claims with
  | nil =>
      rcases hdmem with ⟨_, hmem, _⟩
      simp at hmem
  | cons c cs ih =>
      by_cases hc_le : c.strength ≤ s
      · have hcid : c.id = d := by
          apply huniq c.id
          · exact ⟨c, by simp, rfl⟩
          · simpa [lookupStrength] using hc_le
        have htail_none : ∀ e ∈ cs, ¬ e.strength ≤ s := by
          intro e he he_le
          have heid : e.id = d := by
            apply huniq e.id
            · exact ⟨e, List.Mem.tail _ he, rfl⟩
            · have hlookup :
                  lookupStrength e.id (c :: cs) = e.strength :=
                lookupStrength_eq_of_mem_distinct hdist
                  (List.Mem.tail _ he)
              simpa [hlookup] using he_le
          have hhead_not_tail : c.id ≠ e.id := by
            intro hsame
            exact ClaimsDistinct_head_not_in_tail hdist
              (by
                simp only [List.mem_map]
                exact ⟨e, he, hsame.symm⟩)
          exact hhead_not_tail (hcid.trans heid.symm)
        simp [countAtMost, hc_le,
          countAtMost_eq_zero_of_forall_not_le htail_none]
      · have hcid_ne : c.id ≠ d := by
          intro hcid
          have hlookup : lookupStrength d (c :: cs) = c.strength := by
            simpa [hcid] using
              lookupStrength_eq_of_mem_distinct hdist (by simp : c ∈ c :: cs)
          have : c.strength = s := by
            rw [← hlookup, hds]
          exact hc_le (by rw [this])
        have hdmem_tail : InClaims d cs := InClaims_tail hdmem hcid_ne
        have hds_tail : lookupStrength d cs = s := by
          simpa [lookupStrength, hcid_ne] using hds
        have hdist_tail : ClaimsDistinct cs := ClaimsDistinct_tail hdist
        have huniq_tail : ∀ j, InClaims j cs →
            lookupStrength j cs ≤ s → j = d := by
          intro j hj hle
          have hcj : c.id ≠ j := by
            intro hcj
            rcases hj with ⟨e, he, heid⟩
            exact ClaimsDistinct_head_not_in_tail hdist
              (by
                simp only [List.mem_map]
                exact ⟨e, he, heid.trans hcj.symm⟩)
          apply huniq j
          · rcases hj with ⟨e, he, heid⟩
            exact ⟨e, List.Mem.tail _ he, heid⟩
          · simpa [lookupStrength, hcj] using hle
        simp [countAtMost, hc_le,
          ih hdmem_tail hds_tail hdist_tail huniq_tail]

private lemma length_ge_one_of_inClaims
    {claims : List ClaimQ} {a : ClaimantId}
    (ha : InClaims a claims) : 1 ≤ claims.length := by
  cases claims with
  | nil =>
      rcases ha with ⟨_, hmem, _⟩
      simp at hmem
  | cons _ _ =>
      simp

private lemma length_ge_two_of_two_distinct_inClaims
    {claims : List ClaimQ} {a b : ClaimantId}
    (ha : InClaims a claims) (hb : InClaims b claims) (hab : a ≠ b) :
    2 ≤ claims.length := by
  induction claims with
  | nil =>
      rcases ha with ⟨_, hmem, _⟩
      simp at hmem
  | cons c cs ih =>
      by_cases hca : c.id = a
      · have hb_tail : InClaims b cs := InClaims_tail hb (by
          intro hcb
          exact hab (hca.symm.trans hcb))
        have hlen := length_ge_one_of_inClaims hb_tail
        simpa using Nat.succ_le_succ hlen
      · have ha_tail : InClaims a cs := InClaims_tail ha hca
        by_cases hcb : c.id = b
        · have hlen := length_ge_one_of_inClaims ha_tail
          simpa using Nat.succ_le_succ hlen
        · have hb_tail : InClaims b cs := InClaims_tail hb hcb
          have hlen := ih ha_tail hb_tail
          simpa using Nat.le.step hlen

private lemma length_ge_three_of_three_distinct_inClaims
    {claims : List ClaimQ} {a b c : ClaimantId}
    (ha : InClaims a claims) (hb : InClaims b claims)
    (hc : InClaims c claims) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    3 ≤ claims.length := by
  induction claims with
  | nil =>
      rcases ha with ⟨_, hmem, _⟩
      simp at hmem
  | cons x xs ih =>
      by_cases hxa : x.id = a
      · have hb_tail : InClaims b xs := InClaims_tail hb (by
          intro hxb
          exact hab (hxa.symm.trans hxb))
        have hc_tail : InClaims c xs := InClaims_tail hc (by
          intro hxc
          exact hac (hxa.symm.trans hxc))
        have hlen :=
          length_ge_two_of_two_distinct_inClaims hb_tail hc_tail hbc
        simpa using Nat.succ_le_succ hlen
      · have ha_tail : InClaims a xs := InClaims_tail ha hxa
        by_cases hxb : x.id = b
        · have hc_tail : InClaims c xs := InClaims_tail hc (by
            intro hxc
            exact hbc (hxb.symm.trans hxc))
          have hlen :=
            length_ge_two_of_two_distinct_inClaims ha_tail hc_tail hac
          simpa using Nat.succ_le_succ hlen
        · have hb_tail : InClaims b xs := InClaims_tail hb hxb
          by_cases hxc : x.id = c
          · have hlen :=
              length_ge_two_of_two_distinct_inClaims ha_tail hb_tail hab
            simpa using Nat.succ_le_succ hlen
          · have hc_tail : InClaims c xs := InClaims_tail hc hxc
            have hlen := ih ha_tail hb_tail hc_tail
            simpa using Nat.le.step hlen

private lemma obstructionGenerator_displaced_unique_min
    {claims : List ClaimQ} (_hdist : ClaimsDistinct claims)
    (hgen : DecisionPipeline.ObstructionGenerator claims) :
    ∀ j, InClaims j claims →
      lookupStrength j claims ≤ lookupStrength hgen.displaced claims →
        j = hgen.displaced := by
  intro j hj hle
  by_contra hne
  have hj_removed :
      InClaims j (removeClaimGraph hgen.displaced claims) :=
    inClaims_removeClaimGraph_of_ne hne hj
  have haffected_le_removed :
      lookupStrength hgen.affected
          (removeClaimGraph hgen.displaced claims) ≤
        lookupStrength j (removeClaimGraph hgen.displaced claims) :=
    hgen.affected_weakest_after_removal.2.1 j hj_removed
  have haffected_le_j :
      lookupStrength hgen.affected claims ≤ lookupStrength j claims := by
    have haj : hgen.affected ≠ hgen.displaced :=
      hgen.distinct_claimants.symm
    rw [lookupStrength_removeClaimGraph_of_ne (claims := claims) (j := hgen.affected)
        (k := hgen.displaced) haj,
      lookupStrength_removeClaimGraph_of_ne (claims := claims) (j := j)
        (k := hgen.displaced) hne] at haffected_le_removed
    exact haffected_le_removed
  rcases hgen.affected_has_weaker with
    ⟨w, _hwa, hwclaims, hw_lt_affected⟩
  have hdisplaced_le_w :
      lookupStrength hgen.displaced claims ≤ lookupStrength w claims :=
    hgen.displaced_weakest.2.1 w hwclaims
  have hdisplaced_lt_affected :
      lookupStrength hgen.displaced claims <
        lookupStrength hgen.affected claims := by
    exact lt_of_le_of_lt hdisplaced_le_w hw_lt_affected
  linarith

private lemma obstructionGenerator_claims_length_ge_three
    {claims : List ClaimQ} (hdist : ClaimsDistinct claims)
    (hgen : DecisionPipeline.ObstructionGenerator claims) :
    3 ≤ claims.length := by
  rcases hgen.affected_weakest_after_removal.2.2 with
    ⟨stronger, hstronger_ne_affected, hstronger_removed, _hstronger⟩
  rcases inClaims_removeClaimGraph_to_original hdist hstronger_removed with
    ⟨hstronger_claims, hstronger_ne_displaced⟩
  exact length_ge_three_of_three_distinct_inClaims
    hgen.displaced_in_claims hgen.affected_in_claims hstronger_claims
    hgen.distinct_claimants hstronger_ne_displaced.symm
    hstronger_ne_affected.symm

private lemma peerRelativeNode_denies_obstruction_displaced
    {claims : List ClaimQ} (hdist : ClaimsDistinct claims)
    (hgen : DecisionPipeline.ObstructionGenerator claims) :
    peerRelativeNode claims hgen.displaced = BinaryDecision.Deny := by
  let s := lookupStrength hgen.displaced claims
  have hcount :
      countAtMost claims s = 1 := by
    exact countAtMost_eq_one_of_unique_atMost
      hgen.displaced_in_claims rfl hdist
      (obstructionGenerator_displaced_unique_min hdist hgen)
  have hlen : 3 ≤ claims.length :=
    obstructionGenerator_claims_length_ge_three hdist hgen
  have hlt : ¬ 2 * countAtMost claims s ≥ claims.length := by
    rw [hcount]
    omega
  simp [peerRelativeNode, s, hlt]

lemma peerRelativeNode_finiteEstateCoupled :
    DecisionPipeline.FiniteEstateCoupled
      (P := GovernanceGraph) peerRelativeNode := by
  intro claims hdistinct hscarce _hadmissible
  rcases hscarce with ⟨hgen, _⟩
  exact ⟨hgen.displaced, hgen.displaced_in_claims,
    peerRelativeNode_denies_obstruction_displaced hdistinct hgen⟩

theorem peerRelativeNode_symmetricScarceCoupled :
    DecisionPipeline.SymmetricScarceCoupledAllocator
      (P := GovernanceGraph) peerRelativeNode where
  symmetry := peerRelativeNode_claimantSymmetric
  finite_estate := peerRelativeNode_finiteEstateCoupled
  scarcity_pressure := peerRelativeNode_medianWitness_scarcity_pressure

lemma peerRelativeNode_denies_medianWitness_displaced :
    peerRelativeNode medianWitnessClaims 0 = BinaryDecision.Deny := by
  native_decide

/-- Concrete median-rule coupled witness facts. This is the compiled fallback
form: the median rule is symmetric and has the scarce admissible witness used by
the widened theorem, and it denies the scarce claimant on that witness. -/
theorem peerRelativeNode_symmetricScarceCoupled_witness :
    DecisionPipeline.ClaimantSymmetric
        (P := GovernanceGraph) peerRelativeNode ∧
      (∃ claims, ClaimsDistinct claims ∧
        DecisionPipeline.OverSubscribed claims ∧
          DecisionPipeline.IndividuallyAdmissible
            (P := GovernanceGraph) peerRelativeNode claims ∧
            ∃ k, InClaims k claims ∧
              peerRelativeNode claims k = BinaryDecision.Deny) := by
  refine ⟨peerRelativeNode_claimantSymmetric, ?_⟩
  refine ⟨medianWitnessClaims, medianWitnessClaims_distinct,
    ⟨medianWitnessObstructionGenerator, True.intro⟩,
    peerRelativeNode_medianWitness_individuallyAdmissible, 0, ?_, ?_⟩
  · native_decide
  · exact peerRelativeNode_denies_medianWitness_displaced


end SymmetricScarceCoupledMedianWitness

end Legitimacy
