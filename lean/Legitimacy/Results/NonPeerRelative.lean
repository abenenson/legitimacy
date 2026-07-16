/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.Impossibility
import Mathlib.Tactic.NormNum

/-!
# Legitimacy.Results.NonPeerRelative — claimant-local governance and its limits

This module formalizes the "non-peer-relative" loophole around the
peer-relative impossibility theorem at the binary governance-graph layer.

The key result is not that arbitrary absolute-threshold graphs recover the
full four-axiom bundle. Under the library's existing axioms, non-peer-relative
graphs escape only in the claimant-constant case. More generally:

1. Non-peer-relative graphs admit claimant-local decision semantics.
2. Monotone non-peer-relative graphs are upward-closed claimant-local cuts.
3. Monotonicity + strategyproofness collapse those cuts to claimant-constant
   decisions.
4. Finite-estate constraints are unenforceable once individually permitted
   claims can jointly exceed the budget.
-/

set_option autoImplicit false

namespace Legitimacy

/-- A governance graph is non-peer-relative when a claimant's final decision is
determined entirely by that claimant's own reported strength, not by the rest
of the claims profile. We state this over distinct claim lists to match the
ambient binary-axiom semantics. -/
def GovernanceGraph.IsNonPeerRelative (G : GovernanceGraph) : Prop :=
  ∀ {claims claims' : List ClaimQ} {k : ClaimantId},
    InClaims k claims →
    InClaims k claims' →
    ClaimsDistinct claims →
    ClaimsDistinct claims' →
    lookupStrength k claims = lookupStrength k claims' →
    graphDecide G claims k = graphDecide G claims' k

/-- Canonical singleton profile for claimant `k` at strength `s`. -/
def singletonClaimProfile (k : ClaimantId) (s : ℚ) (hs : 0 < s) : List ClaimQ :=
  [⟨k, s, hs, []⟩]

/-- The claimant-local decision induced by a graph on singleton profiles. -/
def GovernanceGraph.localDecision (G : GovernanceGraph)
    (k : ClaimantId) (s : ℚ) (hs : 0 < s) : BinaryDecision :=
  graphDecide G (singletonClaimProfile k s hs) k

/-- A graph is threshold-structured when each claimant's acceptance region is an
upward-closed cut on positive rationals. -/
def ThresholdStructured (G : GovernanceGraph) : Prop :=
  ∃ accepts : ClaimantId → Set ℚ,
    (∀ k ⦃s t : ℚ⦄, 0 < s → s ≤ t → s ∈ accepts k → t ∈ accepts k) ∧
    (∀ (claims : List ClaimQ) (k : ClaimantId),
      InClaims k claims →
      ClaimsDistinct claims →
      (graphDecide G claims k = BinaryDecision.Permit ↔
        lookupStrength k claims ∈ accepts k))

/-- A graph is claimant-constant when each claimant's decision is fixed
independently of the claims profile. -/
def ClaimantConstant (G : GovernanceGraph) : Prop :=
  ∃ d : ClaimantId → BinaryDecision,
    ∀ (claims : List ClaimQ) (k : ClaimantId),
      InClaims k claims →
      ClaimsDistinct claims →
      graphDecide G claims k = d k

/-- Estate-feasibility for binary governance: every over-budget profile must deny
at least one claimant. -/
def RespectsFiniteEstate (G : GovernanceGraph) (E : ℚ) : Prop :=
  ∀ (claims : List ClaimQ),
    ClaimsDistinct claims →
    totalStrength claims > E →
    ∃ c ∈ claims, graphDecide G claims c.id = BinaryDecision.Deny

/-- Claimant-constant singleton graph. -/
def claimantConstGraph (d : ClaimantId → BinaryDecision) : GovernanceGraph :=
  [fun _ k => d k]

@[simp] theorem singletonClaimProfile_distinct (k : ClaimantId) (s : ℚ) (hs : 0 < s) :
    ClaimsDistinct (singletonClaimProfile k s hs) := by
  unfold singletonClaimProfile ClaimsDistinct
  simp

@[simp] theorem singletonClaimProfile_inClaims (k : ClaimantId) (s : ℚ) (hs : 0 < s) :
    InClaims k (singletonClaimProfile k s hs) := by
  refine ⟨⟨k, s, hs, []⟩, ?_, rfl⟩
  simp [singletonClaimProfile]

@[simp] theorem lookupStrength_singletonClaimProfile
    (k : ClaimantId) (s : ℚ) (hs : 0 < s) :
    lookupStrength k (singletonClaimProfile k s hs) = s := by
  unfold singletonClaimProfile
  simp [lookupStrength]

/-- Removing a claimant from a distinct profile preserves distinctness of the
remaining claimant IDs. -/
lemma ClaimsDistinct_removeClaimGraph {claims : List ClaimQ} {k : ClaimantId}
    (hdist : ClaimsDistinct claims) :
    ClaimsDistinct (removeClaimGraph k claims) := by
  have mem_removeClaimGraph_of_mem :
      ∀ {claims : List ClaimQ} {c : ClaimQ} {k : ClaimantId},
        c ∈ removeClaimGraph k claims → c ∈ claims := by
    intro claims c k hmem
    induction claims with
    | nil =>
        simp [removeClaimGraph] at hmem
    | cons c' cs ih =>
        by_cases hc'k : c'.id = k
        · simp [removeClaimGraph, hc'k] at hmem
          exact List.Mem.tail _ hmem
        · simp [removeClaimGraph, hc'k] at hmem
          cases hmem with
          | inl hhead => simp [hhead]
          | inr htail => exact List.Mem.tail _ (ih htail)
  induction claims with
  | nil =>
      simp [ClaimsDistinct, removeClaimGraph]
  | cons c cs ih =>
      have htail : ClaimsDistinct cs := ClaimsDistinct_tail hdist
      by_cases hck : c.id = k
      · simpa [removeClaimGraph, hck] using htail
      · have hhead :
            c.id ∉ (removeClaimGraph k cs).map Claim.id := by
            intro hmem
            have hmem' : c.id ∈ cs.map Claim.id := by
              simp only [List.mem_map] at hmem ⊢
              rcases hmem with ⟨c', hc'mem, hc'id⟩
              exact ⟨c', mem_removeClaimGraph_of_mem hc'mem, hc'id⟩
            exact ClaimsDistinct_head_not_in_tail hdist hmem'
        have ih' : ClaimsDistinct (removeClaimGraph k cs) := ih htail
        unfold ClaimsDistinct at ih' ⊢
        simp [removeClaimGraph, hck, hhead, ih']

/-- Looking up a different claimant is invariant under removing claimant `k`. -/
lemma lookupStrength_removeClaimGraph_of_ne {claims : List ClaimQ}
    {j k : ClaimantId} (hjk : j ≠ k) :
    lookupStrength j (removeClaimGraph k claims) = lookupStrength j claims := by
  induction claims with
  | nil =>
      simp [removeClaimGraph, lookupStrength]
  | cons c cs ih =>
      by_cases hck : c.id = k
      · have hcj : c.id ≠ j := by
          intro hcj
          exact hjk (hcj.symm.trans hck)
        have hkj' : k ≠ j := by
          intro hkj'
          exact hcj (hck.trans hkj')
        simp [removeClaimGraph, hck, lookupStrength, hkj']
      · by_cases hcj : c.id = j
        · have hjk' : j ≠ k := hjk
          simp [removeClaimGraph, lookupStrength, hcj, hjk']
        · simp [removeClaimGraph, hck, lookupStrength, hcj, ih]

/-- Removing claimant `k` preserves membership of any different claimant `j`. -/
lemma inClaims_removeClaimGraph_of_ne {claims : List ClaimQ}
    {j k : ClaimantId} (hjk : j ≠ k) :
    InClaims j claims → InClaims j (removeClaimGraph k claims) := by
  intro hmem
  induction claims with
  | nil =>
      exact False.elim (by
        obtain ⟨_, h, _⟩ := hmem
        simp at h)
  | cons c cs ih =>
      by_cases hck : c.id = k
      · simp [removeClaimGraph, hck]
        obtain ⟨c', hc'mem, hc'id⟩ := hmem
        cases hc'mem with
        | head =>
            exact False.elim (hjk (hc'id.symm.trans hck))
        | tail _ htail =>
            exact ⟨c', htail, hc'id⟩
      · obtain ⟨c', hc'mem, hc'id⟩ := hmem
        cases hc'mem with
        | head =>
            refine ⟨c, ?_, hc'id⟩
            simp [removeClaimGraph, hck]
        | tail _ htail =>
            obtain ⟨c'', hc''mem, hc''id⟩ := ih ⟨c', htail, hc'id⟩
            refine ⟨c'', ?_, hc''id⟩
            simp [removeClaimGraph, hck, hc''mem]

/-- In a distinct profile, looking up a claim already in the list returns that
claim's recorded strength. -/
lemma lookupStrength_eq_of_mem_distinct {claims : List ClaimQ}
    {c : ClaimQ} (hdist : ClaimsDistinct claims) (hmem : c ∈ claims) :
    lookupStrength c.id claims = c.strength := by
  induction claims with
  | nil =>
      exact False.elim (by simp at hmem)
  | cons c' cs ih =>
      cases hmem with
      | head =>
          simp [lookupStrength]
      | tail _ htail =>
          have htailDistinct : ClaimsDistinct cs := ClaimsDistinct_tail hdist
          have hneq : c'.id ≠ c.id := by
            intro heq
            apply ClaimsDistinct_head_not_in_tail hdist
            simp only [List.mem_map]
            exact ⟨c, htail, heq.symm⟩
          simp [lookupStrength, hneq, ih htailDistinct htail]

@[simp] theorem strengthen_singletonClaimProfile
    (k : ClaimantId) (s t : ℚ) (hs : 0 < s) (ht : 0 < t) :
    strengthenClaim k t ht (singletonClaimProfile k s hs) =
      singletonClaimProfile k t ht := by
  simp [singletonClaimProfile, strengthenClaim]

/-- Claimant-constant graphs are automatically non-peer-relative, because their
output ignores the rest of the profile entirely. -/
lemma claimantConstGraph_nonPeerRelative (d : ClaimantId → BinaryDecision) :
    (claimantConstGraph d).IsNonPeerRelative := by
  intro claims claims' k hk hk' _hdist _hdist' _hsame
  simp [claimantConstGraph, graphDecide]

/-- Claimant-constant graphs satisfy the full four-axiom bundle used by the
impossibility theorem. -/
lemma claimantConstGraph_allLegitimacyAxioms (d : ClaimantId → BinaryDecision) :
    AllLegitimacyAxioms (claimantConstGraph d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro claims k j hk hj hkj hdist hdeny
    simp [claimantConstGraph, graphDecide]
  · intro claims α hα j hj
    simp [claimantConstGraph, graphDecide]
  · intro claims k s' hs' j hk hdist hle hperm
    simpa [claimantConstGraph, graphDecide] using hperm
  · intro claims k s_r hs_r hk hdist hperm
    simpa [claimantConstGraph, graphDecide] using hperm

/-- Non-peer-relative graphs are determined by their singleton-profile local
decision. -/
theorem GovernanceGraph.decide_eq_localDecision
    {G : GovernanceGraph} (hnpr : G.IsNonPeerRelative)
    {claims : List ClaimQ} {k : ClaimantId}
    (hmem : InClaims k claims) (hdist : ClaimsDistinct claims) :
    graphDecide G claims k =
      G.localDecision k (lookupStrength k claims) (lookupStrength_pos_of_mem hmem) := by
  apply hnpr hmem
  · exact singletonClaimProfile_inClaims k (lookupStrength k claims)
      (lookupStrength_pos_of_mem hmem)
  · exact hdist
  · exact singletonClaimProfile_distinct k (lookupStrength k claims)
      (lookupStrength_pos_of_mem hmem)
  · simp [lookupStrength_singletonClaimProfile]

/-- For a non-peer-relative graph, any claimant's decision on a distinct
profile agrees with the decision on the corresponding singleton profile. -/
lemma GovernanceGraph.decide_eq_singleton_of_nonPeerRelative
    {G : GovernanceGraph} (hnpr : G.IsNonPeerRelative)
    {claims : List ClaimQ} {c : ClaimQ}
    (hdist : ClaimsDistinct claims) (hmem : c ∈ claims) :
    graphDecide G claims c.id = graphDecide G [c] c.id := by
  have hcIn : InClaims c.id claims := ⟨c, hmem, rfl⟩
  have hsingleIn : InClaims c.id [c] := ⟨c, by simp, rfl⟩
  have hsingleDistinct : ClaimsDistinct ([c] : List ClaimQ) := by
    unfold ClaimsDistinct
    simp
  have hsame :
      lookupStrength c.id claims = lookupStrength c.id ([c] : List ClaimQ) := by
    rw [lookupStrength_eq_of_mem_distinct hdist hmem]
    simp [lookupStrength]
  exact hnpr hcIn hsingleIn hdist hsingleDistinct hsame

/-- For a non-peer-relative graph, a claimant is permitted on a distinct
profile exactly when the corresponding claimant-local singleton decision
permits them. -/
lemma GovernanceGraph.permit_iff_localDecision_of_nonPeerRelative
    {G : GovernanceGraph} (hnpr : G.IsNonPeerRelative)
    {claims : List ClaimQ} {k : ClaimantId}
    (hmem : InClaims k claims) (hdist : ClaimsDistinct claims) :
    graphDecide G claims k = BinaryDecision.Permit ↔
      G.localDecision k (lookupStrength k claims) (lookupStrength_pos_of_mem hmem) =
        BinaryDecision.Permit := by
  rw [GovernanceGraph.decide_eq_localDecision hnpr hmem hdist]

/-- Graph monotonicity turns claimant-local singleton decisions into upward-closed
acceptance regions in the reported strength. -/
lemma GovernanceGraph.localDecision_monotone
    {G : GovernanceGraph} (hmon : GraphMonotonicity G)
    {k : ClaimantId} {s t : ℚ} (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t) :
    G.localDecision k s hs = BinaryDecision.Permit →
    G.localDecision k t ht = BinaryDecision.Permit := by
  intro hperm
  have hk : InClaims k (singletonClaimProfile k s hs) :=
    singletonClaimProfile_inClaims k s hs
  have hdist : ClaimsDistinct (singletonClaimProfile k s hs) :=
    singletonClaimProfile_distinct k s hs
  have h :=
    hmon (singletonClaimProfile k s hs) k t ht k hk hdist
      (by
        intro c hc hid
        have hc' : c = ⟨k, s, hs, []⟩ := by
          simp [singletonClaimProfile] at hc
          simpa using hc
        subst hc'
        simpa using hst)
      hperm
  simpa [GovernanceGraph.localDecision, strengthen_singletonClaimProfile] using h

/-- Graph strategyproofness makes a claimant-local permitted singleton decision
stable when the claimant reports a different positive strength. -/
lemma GovernanceGraph.localDecision_strategyproof
    {G : GovernanceGraph} (hsp : GraphStrategyproofness G)
    {k : ClaimantId} {s t : ℚ} (hs : 0 < s) (ht : 0 < t) :
    G.localDecision k t ht = BinaryDecision.Permit →
    G.localDecision k s hs = BinaryDecision.Permit := by
  intro hperm
  have hk : InClaims k (singletonClaimProfile k s hs) :=
    singletonClaimProfile_inClaims k s hs
  have hdist : ClaimsDistinct (singletonClaimProfile k s hs) :=
    singletonClaimProfile_distinct k s hs
  have h :=
    hsp (singletonClaimProfile k s hs) k t ht hk hdist
      (by
        simpa [GovernanceGraph.localDecision, strengthen_singletonClaimProfile] using hperm)
  simpa [GovernanceGraph.localDecision] using h

/-- Under graph monotonicity and strategyproofness, all claimant-local singleton
decisions for a fixed claimant coincide. -/
lemma GovernanceGraph.localDecision_eq_of_monotone_strategyproof
    {G : GovernanceGraph} (hmon : GraphMonotonicity G) (hsp : GraphStrategyproofness G)
    {k : ClaimantId} {s t : ℚ} (hs : 0 < s) (ht : 0 < t) :
    G.localDecision k s hs = G.localDecision k t ht := by
  by_cases hst : s ≤ t
  · cases hs' : G.localDecision k s hs <;> cases ht' : G.localDecision k t ht
    · rfl
    · have hcontra :=
          GovernanceGraph.localDecision_monotone hmon hs ht hst hs'
      rw [ht'] at hcontra
      exact False.elim (BinaryDecision.noConfusion hcontra)
    · have hcontra :=
          GovernanceGraph.localDecision_strategyproof hsp hs ht ht'
      rw [hs'] at hcontra
      exact False.elim (BinaryDecision.noConfusion hcontra)
    · rfl
  · have hts : t ≤ s := le_of_not_ge hst
    cases hs' : G.localDecision k s hs <;> cases ht' : G.localDecision k t ht
    · rfl
    · have hcontra :=
          GovernanceGraph.localDecision_strategyproof hsp ht hs hs'
      rw [ht'] at hcontra
      exact False.elim (BinaryDecision.noConfusion hcontra)
    · have hcontra :=
          GovernanceGraph.localDecision_monotone hmon ht hs hts ht'
      rw [hs'] at hcontra
      exact False.elim (BinaryDecision.noConfusion hcontra)
    · rfl

/-- Monotonicity plus strategyproofness make every claimant-local decision
equal to its value at the fixed positive reference strength `1`. -/
lemma GovernanceGraph.decide_eq_reference_localDecision
    {G : GovernanceGraph} (hnpr : G.IsNonPeerRelative)
    (hmon : GraphMonotonicity G) (hsp : GraphStrategyproofness G)
    {claims : List ClaimQ} {k : ClaimantId}
    (hmem : InClaims k claims) (hdist : ClaimsDistinct claims) :
    graphDecide G claims k = G.localDecision k 1 (by norm_num) := by
  trans G.localDecision k (lookupStrength k claims) (lookupStrength_pos_of_mem hmem)
  · exact GovernanceGraph.decide_eq_localDecision hnpr hmem hdist
  · exact GovernanceGraph.localDecision_eq_of_monotone_strategyproof hmon hsp
      (lookupStrength_pos_of_mem hmem) (by norm_num)

/-- Non-peer-relative graphs are graph-consistent, because removing a denied
claimant cannot affect any different claimant's looked-up strength. -/
lemma nonPeerRelative_consistent
    (G : GovernanceGraph) (hnpr : G.IsNonPeerRelative) :
    GraphConsistency G := by
  intro claims k j hk hj hkj hdist hdeny
  apply hnpr hj
  · exact inClaims_removeClaimGraph_of_ne hkj.symm hj
  · exact hdist
  · exact ClaimsDistinct_removeClaimGraph hdist
  · exact (lookupStrength_removeClaimGraph_of_ne hkj.symm).symm

/-- Non-peer-relative governance graphs escape the peer-relative impossibility
simply because claimant-constant graphs satisfy all four axioms. -/
theorem nonPeerRelative_escapes_impossibility :
    ∃ G : GovernanceGraph, G.IsNonPeerRelative ∧ AllLegitimacyAxioms G := by
  refine ⟨claimantConstGraph (fun _ => BinaryDecision.Permit), ?_, ?_⟩
  · exact claimantConstGraph_nonPeerRelative _
  · exact claimantConstGraph_allLegitimacyAxioms _

/-- Every monotone non-peer-relative graph induces upward-closed claimant-local
acceptance cuts, so it is threshold-structured. -/
theorem nonPeerRelative_is_threshold
    (G : GovernanceGraph) (hnpr : G.IsNonPeerRelative) (hmon : GraphMonotonicity G) :
    ThresholdStructured G := by
  refine ⟨fun k s => ∃ hs : 0 < s, G.localDecision k s hs = BinaryDecision.Permit, ?_, ?_⟩
  · intro k s t hs hst hsAccept
    rcases hsAccept with ⟨hs', hperm⟩
    exact ⟨lt_of_lt_of_le hs hst,
      GovernanceGraph.localDecision_monotone hmon hs' (lt_of_lt_of_le hs hst) hst hperm⟩
  · intro claims k hmem hdist
    constructor
    · intro hperm
      exact ⟨lookupStrength_pos_of_mem hmem,
        (GovernanceGraph.permit_iff_localDecision_of_nonPeerRelative
          hnpr hmem hdist).mp hperm⟩
    · rintro ⟨hs, hlocal⟩
      exact (GovernanceGraph.permit_iff_localDecision_of_nonPeerRelative
        hnpr hmem hdist).mpr hlocal

/-- Combining non-peer-relativity with monotonicity and strategyproofness
collapses the graph to claimant-constant behavior. -/
theorem nonPeerRelative_monotone_strategyproof_claimantConstant
    (G : GovernanceGraph) (hnpr : G.IsNonPeerRelative)
    (hmon : GraphMonotonicity G) (hsp : GraphStrategyproofness G) :
    ClaimantConstant G := by
  refine ⟨fun k => G.localDecision k 1 (by norm_num), ?_⟩
  intro claims k hmem hdist
  exact GovernanceGraph.decide_eq_reference_localDecision hnpr hmon hsp hmem hdist

/-- Finite-estate feasibility fails whenever a non-peer-relative graph
individually permits an over-budget family of distinct singleton claims. -/
theorem nonPeerRelative_cannot_allocate_finite_estate
    (G : GovernanceGraph) (hnpr : G.IsNonPeerRelative)
    (E : ℚ) (witness : List ClaimQ)
    (hdist : ClaimsDistinct witness)
    (hover : totalStrength witness > E)
    (hindividual : ∀ c ∈ witness, graphDecide G [c] c.id = BinaryDecision.Permit) :
    ¬ RespectsFiniteEstate G E := by
  intro hestate
  obtain ⟨c, hcmem, hcdeny⟩ := hestate witness hdist hover
  have hlocal :=
    GovernanceGraph.decide_eq_singleton_of_nonPeerRelative hnpr hdist hcmem
  have hpermit : graphDecide G witness c.id = BinaryDecision.Permit := by
    exact hlocal.trans (hindividual c hcmem)
  rw [hcdeny] at hpermit
  exact BinaryDecision.noConfusion hpermit

/-- Named escape collapse: a non-peer-relative graph satisfying the full
graph-diagnostic bundle collapses to claimant-constant behavior, and if it
individually accepts an over-budget family, it cannot enforce finite-estate
feasibility. This packages the two costs of the non-peer-relative escape in the
form used by the paper. -/
theorem nonPeerRelative_allAxioms_escape_collapse
    (G : GovernanceGraph) (hnpr : G.IsNonPeerRelative)
    (hall : AllLegitimacyAxioms G)
    (E : ℚ) (witness : List ClaimQ)
    (hdist : ClaimsDistinct witness)
    (hover : totalStrength witness > E)
    (hindividual : ∀ c ∈ witness,
      graphDecide G [c] c.id = BinaryDecision.Permit) :
    ClaimantConstant G ∧ ¬ RespectsFiniteEstate G E := by
  rcases hall with ⟨_, _, hmon, hsp⟩
  exact ⟨
    nonPeerRelative_monotone_strategyproof_claimantConstant G hnpr hmon hsp,
    nonPeerRelative_cannot_allocate_finite_estate
      G hnpr E witness hdist hover hindividual⟩

/-- The full non-peer-relative escape analysis at the binary graph layer:
there are non-peer-relative all-axiom graphs, monotone non-peer-relative graphs
are claimant-local threshold cuts, monotonicity plus strategyproofness force
claimant-constant behavior, and any over-budget family of individually accepted
claims witnesses failure of finite-estate feasibility. -/
theorem nonPeerRelative_escape_cost_packaged :
    (∃ G : GovernanceGraph, G.IsNonPeerRelative ∧ AllLegitimacyAxioms G) ∧
    (∀ G : GovernanceGraph,
      G.IsNonPeerRelative →
      GraphMonotonicity G →
      ThresholdStructured G) ∧
    (∀ G : GovernanceGraph,
      G.IsNonPeerRelative →
      GraphMonotonicity G →
      GraphStrategyproofness G →
      ClaimantConstant G) ∧
    (∀ (G : GovernanceGraph) (E : ℚ) (witness : List ClaimQ),
      G.IsNonPeerRelative →
      ClaimsDistinct witness →
      totalStrength witness > E →
      (∀ c ∈ witness, graphDecide G [c] c.id = BinaryDecision.Permit) →
      ¬ RespectsFiniteEstate G E) := by
  refine ⟨nonPeerRelative_escapes_impossibility, ?_, ?_, ?_⟩
  · intro G hnpr hmon
    exact nonPeerRelative_is_threshold G hnpr hmon
  · intro G hnpr hmon hsp
    exact nonPeerRelative_monotone_strategyproof_claimantConstant G hnpr hmon hsp
  · intro G E witness hnpr hdist hover hindividual
    exact nonPeerRelative_cannot_allocate_finite_estate G hnpr E witness hdist hover hindividual

end Legitimacy
