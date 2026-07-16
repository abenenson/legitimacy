/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Results.Composition
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
  Peer-graph impossibility counterexample — ported to Mathlib ℚ.
  The Arrow's theorem for agent governance. Main results:
  1. The peer-relative node violates strategyproofness (constructive
     counterexample): claimant C improves from Deny to Permit by
     misreporting strength upward.
  2. The single-node peer-relative graph [peerRelativeNode] violates
     graph-level monotonicity: strengthening Alice flips Bob from
     Permit to Deny via competitive displacement.
  3. For the concrete graph `peerGraph`, consistency, solidarity,
     monotonicity, and strategyproofness cannot all hold simultaneously.
     The peer-relative graph fails both monotonicity and strategyproofness
     individually.
  4. Corollary: the peer-relative node is monotone but not strategyproof.
     Monotonicity and strategyproofness are in fundamental tension.
  All proofs complete — zero sorry.
  References:
  * Impossibility.lean — original governance impossibility
-/

namespace Legitimacy

-- ═══════════════════════════════════════════════════════════════════
-- The single-node peer-relative graph
-- ═══════════════════════════════════════════════════════════════════

/-- The single-node governance graph containing only peerRelativeNode. -/
def peerGraph : GovernanceGraph := [peerRelativeNode]

/-- Two governance graphs are equivalent when they induce exactly the same
binary decision for every claims profile and claimant. -/
def GovernanceGraphEquivalent (G H : GovernanceGraph) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId),
    graphDecide G claims k = graphDecide H claims k

/-- The bundle of the four graph-level legitimacy axioms used by the
impossibility theorem. -/
def AllLegitimacyAxioms (G : GovernanceGraph) : Prop :=
  GraphConsistency G ∧ GraphSolidarity G ∧
    GraphMonotonicity G ∧ GraphStrategyproofness G

/-- Binary consistency exposure: `1` exactly when graph consistency fails. -/
noncomputable def cv (G : GovernanceGraph) : ℝ := by
  classical
  exact if GraphConsistency G then 0 else 1

/-- Binary solidarity exposure: `1` exactly when graph solidarity fails. -/
noncomputable def sv (G : GovernanceGraph) : ℝ := by
  classical
  exact if GraphSolidarity G then 0 else 1

/-- Binary monotonicity exposure: `1` exactly when graph monotonicity fails. -/
noncomputable def mv (G : GovernanceGraph) : ℝ := by
  classical
  exact if GraphMonotonicity G then 0 else 1

/-- Binary strategyproofness exposure: `1` exactly when graph
    strategyproofness fails. -/
noncomputable def spv (G : GovernanceGraph) : ℝ := by
  classical
  exact if GraphStrategyproofness G then 0 else 1

/-- Every pipeline has a singleton-stage collapse with the same external
decision behavior. -/
def singletonCollapse (G : GovernanceGraph) : GovernanceGraph :=
  [fun claims k => graphDecide G claims k]

/-- The singleton collapse preserves the external decision semantics exactly. -/
lemma singletonCollapse_equiv (G : GovernanceGraph) :
    GovernanceGraphEquivalent G (singletonCollapse G) := by
  intro claims k
  simp [singletonCollapse, graphDecide]
  cases graphDecide G claims k <;> rfl

/-- Graph-level consistency is invariant under governance equivalence. -/
lemma graphConsistency_congr {G H : GovernanceGraph}
    (heq : GovernanceGraphEquivalent G H) :
    GraphConsistency G ↔ GraphConsistency H := by
  constructor <;> intro hcons <;> intro claims k j hk hj hkj hdist hden
  · have hden' : graphDecide G claims k = BinaryDecision.Deny := by
      exact (heq claims k).trans hden
    have h :=
      hcons claims k j hk hj hkj hdist hden'
    exact (heq claims j).symm.trans <| h.trans (heq (removeClaimGraph k claims) j)
  · have hden' : graphDecide H claims k = BinaryDecision.Deny := by
      exact (heq claims k).symm.trans hden
    have h :=
      hcons claims k j hk hj hkj hdist hden'
    exact (heq claims j).trans <| h.trans (heq (removeClaimGraph k claims) j).symm

/-- Graph-level solidarity is invariant under governance equivalence. -/
lemma graphSolidarity_congr {G H : GovernanceGraph}
    (heq : GovernanceGraphEquivalent G H) :
    GraphSolidarity G ↔ GraphSolidarity H := by
  constructor <;> intro hsol <;> intro claims α hα j hj
  · specialize hsol claims α hα j hj
    exact (heq claims j).symm.trans <| hsol.trans <|
      heq (claims.map (fun c => ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)) j
  · specialize hsol claims α hα j hj
    exact (heq claims j).trans <| hsol.trans <|
      (heq (claims.map (fun c => ⟨c.id, α * c.strength, mul_pos hα c.strength_pos, c.metadata⟩)) j).symm

/-- Graph-level monotonicity is invariant under governance equivalence. -/
lemma graphMonotonicity_congr {G H : GovernanceGraph}
    (heq : GovernanceGraphEquivalent G H) :
    GraphMonotonicity G ↔ GraphMonotonicity H := by
  constructor <;> intro hmon <;> intro claims k s_r hs_r j hk hdist hle hperm
  · have hperm' : graphDecide G claims j = BinaryDecision.Permit := by
      exact (heq claims j).trans hperm
    have h :=
      hmon claims k s_r hs_r j hk hdist hle hperm'
    exact (heq (strengthenClaim k s_r hs_r claims) j).symm.trans h
  · have hperm' : graphDecide H claims j = BinaryDecision.Permit := by
      exact (heq claims j).symm.trans hperm
    have h :=
      hmon claims k s_r hs_r j hk hdist hle hperm'
    exact (heq (strengthenClaim k s_r hs_r claims) j).trans h

/-- Graph-level strategyproofness is invariant under governance equivalence. -/
lemma graphStrategyproofness_congr {G H : GovernanceGraph}
    (heq : GovernanceGraphEquivalent G H) :
    GraphStrategyproofness G ↔ GraphStrategyproofness H := by
  constructor <;> intro hsp <;> intro claims k s_r hs_r hk hdist hperm
  · have hperm' :
        graphDecide G (strengthenClaim k s_r hs_r claims) k = BinaryDecision.Permit := by
      exact (heq (strengthenClaim k s_r hs_r claims) k).trans hperm
    have h := hsp claims k s_r hs_r hk hdist hperm'
    exact (heq claims k).symm.trans h
  · have hperm' :
        graphDecide H (strengthenClaim k s_r hs_r claims) k = BinaryDecision.Permit := by
      exact (heq (strengthenClaim k s_r hs_r claims) k).symm.trans hperm
    have h := hsp claims k s_r hs_r hk hdist hperm'
    exact (heq claims k).trans h

/-- The four legitimacy axioms are invariant under governance equivalence. -/
lemma allLegitimacyAxioms_congr {G H : GovernanceGraph}
    (heq : GovernanceGraphEquivalent G H) :
    AllLegitimacyAxioms G ↔ AllLegitimacyAxioms H := by
  unfold AllLegitimacyAxioms
  constructor <;> intro h
  · exact ⟨(graphConsistency_congr heq).mp h.1,
      (graphSolidarity_congr heq).mp h.2.1,
      (graphMonotonicity_congr heq).mp h.2.2.1,
      (graphStrategyproofness_congr heq).mp h.2.2.2⟩
  · exact ⟨(graphConsistency_congr heq).mpr h.1,
      (graphSolidarity_congr heq).mpr h.2.1,
      (graphMonotonicity_congr heq).mpr h.2.2.1,
      (graphStrategyproofness_congr heq).mpr h.2.2.2⟩

/-- A governance pipeline satisfies the four legitimacy axioms exactly when its
behavior collapses to an equivalent admissible singleton-stage graph. This
turns the singleton case into the boundary characterization for the full
pipeline semantics. -/
theorem graphDecide_singleton (G : GovernanceGraph) :
    let singleton := singletonCollapse G
    AllLegitimacyAxioms G ↔
      GovernanceGraphEquivalent G singleton ∧ AllLegitimacyAxioms singleton := by
  intro singleton
  constructor
  · intro haxioms
    exact ⟨singletonCollapse_equiv G,
      (allLegitimacyAxioms_congr (singletonCollapse_equiv G)).mp haxioms⟩
  · intro hsingleton
    exact (allLegitimacyAxioms_congr hsingleton.1).mpr hsingleton.2

-- ═══════════════════════════════════════════════════════════════════
-- Strategyproofness violation
-- ═══════════════════════════════════════════════════════════════════

private def spA : ClaimQ := ⟨0, 3/4, by norm_num, []⟩
private def spB : ClaimQ := ⟨1, 1/2, by norm_num, []⟩
private def spC : ClaimQ := ⟨2, 1/4, by norm_num, []⟩
private def spClaims : List ClaimQ := [spA, spB, spC]

private theorem spClaims_distinct : ClaimsDistinct spClaims := by
  unfold ClaimsDistinct spClaims spA spB spC
  show ([0, 1, 2] : List Nat).Nodup
  exact List.nodup_cons.mpr ⟨by decide, List.nodup_cons.mpr ⟨by decide,
    List.nodup_cons.mpr ⟨by decide, List.Pairwise.nil⟩⟩⟩

private theorem c_in_spClaims : InClaims 2 spClaims :=
  ⟨spC, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl⟩

/-- C is denied under truthful reporting. -/
private theorem c_denied_truth :
    peerRelativeNode spClaims 2 = BinaryDecision.Deny := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

/-- C is permitted when misreporting 1/4 -> 3/4. -/
private theorem c_permitted_misreport :
    peerRelativeNode (strengthenClaim 2 (3/4) (by norm_num) spClaims) 2 =
    BinaryDecision.Permit := by
  native_decide

/-- **Theorem.** The peer-relative node violates strategyproofness. -/
theorem peerRelativeNode_not_strategyproof :
    ¬ NodeStrategyproofness peerRelativeNode := by
  intro hsp
  have h := hsp spClaims 2 (3/4) (by norm_num)
    c_in_spClaims spClaims_distinct c_permitted_misreport
  rw [c_denied_truth] at h
  exact BinaryDecision.noConfusion h

/-- The truthful peer graph denies claimant `C` on the concrete
strategyproofness profile. -/
private lemma peerGraph_c_denied_truth :
    graphDecide peerGraph spClaims 2 = BinaryDecision.Deny := by
  show graphDecide [peerRelativeNode] spClaims 2 = BinaryDecision.Deny
  rw [graphDecide, c_denied_truth]

/-- After claimant `C` strengthens their report, the peer graph permits them on
the concrete strategyproofness counterexample. -/
private lemma peerGraph_c_permitted_misreport :
    graphDecide peerGraph
      (strengthenClaim 2 (3/4) (by norm_num) spClaims) 2 =
      BinaryDecision.Permit := by
  show graphDecide [peerRelativeNode]
    (strengthenClaim 2 (3/4) (by norm_num) spClaims) 2 = BinaryDecision.Permit
  rw [graphDecide, c_permitted_misreport]
  simp [graphDecide]

/-- The single-node peer-relative graph is not strategyproof. -/
theorem peerGraph_not_strategyproof :
    ¬ GraphStrategyproofness peerGraph := by
  intro hsp
  have hmis : graphDecide peerGraph
      (strengthenClaim 2 (3/4) (by norm_num) spClaims) 2 =
      BinaryDecision.Permit :=
    peerGraph_c_permitted_misreport
  have htruth := hsp spClaims 2 (3/4) (by norm_num)
    c_in_spClaims spClaims_distinct hmis
  have hden : graphDecide peerGraph spClaims 2 = BinaryDecision.Deny :=
    peerGraph_c_denied_truth
  rw [hden] at htruth
  exact BinaryDecision.noConfusion htruth

-- ═══════════════════════════════════════════════════════════════════
-- Graph-level monotonicity violation
-- ═══════════════════════════════════════════════════════════════════

private def monoA : ClaimQ := ⟨0, 1/4, by norm_num, []⟩
private def monoB : ClaimQ := ⟨1, 1/2, by norm_num, []⟩
private def monoC : ClaimQ := ⟨2, 3/4, by norm_num, []⟩
private def monoClaims : List ClaimQ := [monoA, monoB, monoC]

private theorem monoClaims_distinct : ClaimsDistinct monoClaims := by
  unfold ClaimsDistinct monoClaims monoA monoB monoC
  show ([0, 1, 2] : List Nat).Nodup
  exact List.nodup_cons.mpr ⟨by decide, List.nodup_cons.mpr ⟨by decide,
    List.nodup_cons.mpr ⟨by decide, List.Pairwise.nil⟩⟩⟩

private theorem a_in_monoClaims : InClaims 0 monoClaims :=
  ⟨monoA, List.Mem.head _, rfl⟩

/-- Baseline: Bob is permitted by the peer-relative graph. -/
private theorem bob_permitted_peer :
    peerRelativeNode monoClaims 1 = BinaryDecision.Permit := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

/-- After strengthening A: Bob is denied. -/
private theorem bob_denied_peer :
    peerRelativeNode (strengthenClaim 0 (3/4) (by norm_num) monoClaims) 1 =
    BinaryDecision.Deny := by
  native_decide

private theorem mono_strength_le :
    ∀ c ∈ monoClaims, c.id = 0 → c.strength ≤ (3 : ℚ) / 4 := by
  intro c hm hid
  cases hm with
  | head => simp only [monoA] at hid ⊢; norm_num
  | tail _ htail =>
    cases htail with
    | head => simp only [monoB] at hid; exact absurd hid (by decide)
      | tail _ htail2 =>
        cases htail2 with
        | head => simp only [monoC] at hid; exact absurd hid (by decide)
        | tail _ h3 => exact absurd h3 List.not_mem_nil

/-- The peer graph permits Bob on the baseline monotonicity profile. -/
private lemma peerGraph_bob_permitted_baseline :
    graphDecide peerGraph monoClaims 1 = BinaryDecision.Permit := by
  show graphDecide [peerRelativeNode] monoClaims 1 = BinaryDecision.Permit
  rw [graphDecide, bob_permitted_peer]
  simp [graphDecide]

/-- After Alice strengthens, the peer graph denies Bob on the monotonicity
counterexample. -/
private lemma peerGraph_bob_denied_after_strengthen :
    graphDecide peerGraph
      (strengthenClaim 0 (3/4) (by norm_num) monoClaims) 1 =
      BinaryDecision.Deny := by
  show graphDecide [peerRelativeNode]
    (strengthenClaim 0 (3/4) (by norm_num) monoClaims) 1 = BinaryDecision.Deny
  rw [graphDecide, bob_denied_peer]

/-- **Theorem.** The single-node peer-relative graph violates
    graph-level monotonicity. -/
theorem peerGraph_not_monotone : ¬ GraphMonotonicity peerGraph := by
  intro hmon
  have hbase : graphDecide peerGraph monoClaims 1 = BinaryDecision.Permit :=
    peerGraph_bob_permitted_baseline
  have h := hmon monoClaims 0 (3/4) (by norm_num) 1
    a_in_monoClaims monoClaims_distinct mono_strength_le hbase
  have hden : graphDecide peerGraph
      (strengthenClaim 0 (3/4) (by norm_num) monoClaims) 1 =
      BinaryDecision.Deny :=
    peerGraph_bob_denied_after_strengthen
  rw [hden] at h
  exact BinaryDecision.noConfusion h

-- ═══════════════════════════════════════════════════════════════════
-- Graph-level consistency violation
-- ═══════════════════════════════════════════════════════════════════

private def consA : ClaimQ := ⟨0, 1/4, by norm_num, []⟩
private def consB : ClaimQ := ⟨1, 1/2, by norm_num, []⟩
private def consC : ClaimQ := ⟨2, 3/4, by norm_num, []⟩
private def consD : ClaimQ := ⟨3, 1, by norm_num, []⟩
private def consClaims : List ClaimQ := [consA, consB, consC, consD]

private theorem consClaims_distinct : ClaimsDistinct consClaims := by
  unfold ClaimsDistinct consClaims consA consB consC consD
  show ([0, 1, 2, 3] : List Nat).Nodup
  exact List.nodup_cons.mpr ⟨by decide, List.nodup_cons.mpr ⟨by decide,
    List.nodup_cons.mpr ⟨by decide,
    List.nodup_cons.mpr ⟨by decide, List.Pairwise.nil⟩⟩⟩⟩

private theorem a_in_consClaims : InClaims 0 consClaims :=
  ⟨consA, List.Mem.head _, rfl⟩

private theorem b_in_consClaims : InClaims 1 consClaims :=
  ⟨consB, List.Mem.tail _ (List.Mem.head _), rfl⟩

private theorem a_denied_cons :
    graphDecide peerGraph consClaims 0 = BinaryDecision.Deny := by
  show graphDecide [peerRelativeNode] consClaims 0 = BinaryDecision.Deny
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

private theorem b_permitted_cons :
    graphDecide peerGraph consClaims 1 = BinaryDecision.Permit := by
  show graphDecide [peerRelativeNode] consClaims 1 = BinaryDecision.Permit
  native_decide

private theorem b_denied_after_remove_a :
    graphDecide peerGraph (removeClaimGraph 0 consClaims) 1 = BinaryDecision.Deny := by
  show graphDecide [peerRelativeNode] (removeClaimGraph 0 consClaims) 1 =
    BinaryDecision.Deny
  native_decide

/-- The peer-relative graph violates graph-level consistency by denying a
surviving claimant after a denied claimant is removed. -/
theorem peerGraph_not_consistent : ¬ GraphConsistency peerGraph := by
  intro hcons
  have h := hcons consClaims 0 1
    a_in_consClaims b_in_consClaims
    (by decide)
    consClaims_distinct
    a_denied_cons
  rw [b_permitted_cons, b_denied_after_remove_a] at h
  exact BinaryDecision.noConfusion h

-- ═══════════════════════════════════════════════════════════════════
-- The main impossibility theorems
-- ═══════════════════════════════════════════════════════════════════

/-- **Peer-graph consistency route.**
    The concrete graph `peerGraph` already contradicts graph consistency, so
    any conjunction containing graph consistency is impossible for this graph
    independently of the strategyproofness bridge. -/
theorem peerGraph_consistency_route_obstruction :
    ¬ GraphConsistency peerGraph :=
  peerGraph_not_consistent

/-- **Peer-graph two-field consistency route.**
    Adding any further axiom to graph consistency is already inconsistent for
    the concrete peer-relative graph. -/
theorem peerGraph_consistency_solidarity_route_obstruction :
    ¬ (GraphConsistency peerGraph ∧ GraphSolidarity peerGraph) := by
  intro h
  exact peerGraph_not_consistent h.1

/-- **Peer-graph impossibility theorem.**
    For the concrete graph `peerGraph`, consistency, solidarity,
    monotonicity, and strategyproofness cannot all hold at once. -/
theorem peerGraph_impossibility :
    ¬ (GraphConsistency peerGraph ∧ GraphSolidarity peerGraph ∧
       GraphMonotonicity peerGraph ∧ GraphStrategyproofness peerGraph) := by
  intro ⟨hcons, _, _, _⟩
  exact peerGraph_not_consistent hcons

/-- **Peer-graph impossibility (strong form).**
    The concrete graph `peerGraph` violates graph-level consistency,
    graph-level monotonicity, and graph-level strategyproofness individually. -/
theorem peerGraph_impossibility_strong :
    ¬ GraphConsistency peerGraph ∧
      ¬ GraphMonotonicity peerGraph ∧ ¬ GraphStrategyproofness peerGraph :=
  ⟨peerGraph_not_consistent, peerGraph_not_monotone,
    peerGraph_not_strategyproof⟩

/-- The peer-relative graph cannot realize the zero legitimacy-factor exposure
point: at least one of the four primary binary exposure coordinates is nonzero.
In fact `mv peerGraph = 1` because `peerGraph` is not graph-monotone. -/
theorem peerRelative_lfe_origin_inaccessible :
    (cv peerGraph, sv peerGraph, mv peerGraph, spv peerGraph) ≠
      (0, 0, 0, 0) := by
  intro horigin
  have hmv0 : mv peerGraph = 0 := by
    simpa using congrArg (fun t : ℝ × ℝ × ℝ × ℝ => t.2.2.1) horigin
  have hmv1 : mv peerGraph = 1 := by
    classical
    unfold mv
    simp [peerGraph_not_monotone]
  norm_num [hmv1] at hmv0

/-- **Corollary.** The peer-relative node is monotone but not strategyproof. -/
lemma monotone_not_strategyproof :
    NodeMonotonicity peerRelativeNode ∧ ¬ NodeStrategyproofness peerRelativeNode :=
  ⟨peerRelativeNode_monotone, peerRelativeNode_not_strategyproof⟩

end Legitimacy
