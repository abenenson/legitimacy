/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Foundations.Graph
import Legitimacy.Diagnostics.Graph
import Mathlib.Tactic.NormNum

/-!
  Composition Inadmissibility Theorems — ported to Mathlib ℚ.

  Main results:

  1. **Binary composition inadmissibility**: there exist governance nodes
     A (threshold) and B (peer-relative), each individually node-level
     monotone, such that the composed graph A→B violates graph-level
     monotonicity. Counterexample: Alice(2/5), Bob(11/20), Carol(9/10).

  2. **Three-valued composition inadmissibility**: there exist three-valued
     governance nodes A (threshold3) and B (peer-relative3), each individually
     NodeMonotonicity3, such that the composed graph A→B violates
     GraphMonotonicity3. Escalate creates a competitive channel that
     does not exist in binary. Counterexample: Alice(1/4), Bob(3/8), Carol(2/5).

  All proofs complete. Concrete counterexamples verified
  by native_decide on decidable ℚ computations.

  References:
  * Composition.lean — original binary composition inadmissibility
  * EscalateComposition.lean — original three-valued composition inadmissibility
-/

namespace Legitimacy

-- ═══════════════════════════════════════════════════════════════════
-- Helper lemmas
-- ═══════════════════════════════════════════════════════════════════

/-- If every claim with id k has strength ≤ s', then lookupStrength k ≤ s'. -/
lemma lookupStrength_le_of_all_le {k : ClaimantId} {claims : List ClaimQ}
    {s' : ℚ} (hmem : InClaims k claims)
    (hle : ∀ c ∈ claims, c.id = k → c.strength ≤ s') :
    lookupStrength k claims ≤ s' := by
  induction claims with
  | nil => exact absurd hmem (by intro ⟨_, h, _⟩; exact List.not_mem_nil h)
  | cons c cs ih =>
    simp only [lookupStrength]
    split
    case isTrue heq => exact hle c (List.Mem.head _) heq
    case isFalse hne =>
      exact ih (InClaims_tail hmem hne) (fun c' hm hid => hle c' (List.Mem.tail _ hm) hid)

/-- lookupStrength after strengthenClaim returns the new strength. -/
lemma lookupStrength_after_strengthen {k : ClaimantId} {claims : List ClaimQ}
    {s' : ℚ} {hs' : 0 < s'}
    (hmem : InClaims k claims) (hdist : ClaimsDistinct claims) :
    lookupStrength k (strengthenClaim k s' hs' claims) = s' := by
  induction claims with
  | nil => exact absurd hmem (by intro ⟨_, h, _⟩; exact List.not_mem_nil h)
  | cons c cs ih =>
    simp only [strengthenClaim]
    split
    case isTrue heq =>
      show lookupStrength k (⟨c.id, s', hs', c.metadata⟩ :: cs) = s'
      simp only [lookupStrength, if_pos heq]
    case isFalse hne =>
      show lookupStrength k (c :: strengthenClaim k s' hs' cs) = s'
      simp only [lookupStrength, if_neg hne]
      exact ih (InClaims_tail hmem hne) (ClaimsDistinct_tail hdist)

-- ═══════════════════════════════════════════════════════════════════
-- Node A: threshold gate
-- ═══════════════════════════════════════════════════════════════════

/-- Threshold gate: permit iff claimant's strength exceeds τ. -/
def thresholdNode (τ : ℚ) : GovernanceNodeFn := fun claims k =>
  if lookupStrength k claims > τ then BinaryDecision.Permit
  else BinaryDecision.Deny

/-- A threshold gate is node-level monotone. -/
lemma thresholdNode_monotone (τ : ℚ) : NodeMonotonicity (thresholdNode τ) := by
  intro claims k s' hs' hmem hdist hle hperm
  simp only [thresholdNode] at hperm ⊢
  split at hperm
  case isTrue h_orig =>
    rw [lookupStrength_after_strengthen hmem hdist]
    have hsk_le := lookupStrength_le_of_all_le hmem hle
    exact if_pos (lt_of_lt_of_le h_orig hsk_le)
  case isFalse _ =>
    exact absurd hperm (by intro h; exact BinaryDecision.noConfusion h)

-- ═══════════════════════════════════════════════════════════════════
-- Node B: peer-relative gate
-- ═══════════════════════════════════════════════════════════════════

/-- Count claims with strength at most s. -/
def countAtMost (claims : List ClaimQ) (s : ℚ) : Nat :=
  match claims with
  | [] => 0
  | c :: cs => (if c.strength ≤ s then 1 else 0) + countAtMost cs s

/-- Peer-relative gate: permit iff at least half the claims have strength
    at most this claimant's. -/
def peerRelativeNode : GovernanceNodeFn := fun claims k =>
  let s := lookupStrength k claims
  if 2 * countAtMost claims s ≥ claims.length then BinaryDecision.Permit
  else BinaryDecision.Deny

-- ─── Lemmas for peer-relative monotonicity ───

/-- Strengthening a claim preserves the length of the claims profile. -/
lemma strengthenClaim_length {k : ClaimantId} {claims : List ClaimQ}
    {s' : ℚ} {hs' : 0 < s'} :
    (strengthenClaim k s' hs' claims).length = claims.length := by
  induction claims with
  | nil => rfl
  | cons c cs ih =>
    simp only [strengthenClaim]
    split
    case isTrue _ => simp [List.length]
    case isFalse _ => simp [List.length, ih]

/-- countAtMost is monotone in the threshold. -/
@[mono] theorem countAtMost_mono {claims : List ClaimQ} {s t : ℚ} (hle : s ≤ t) :
    countAtMost claims s ≤ countAtMost claims t := by
  induction claims with
  | nil => exact Nat.le_refl 0
  | cons c cs ih =>
    simp only [countAtMost]
    by_cases h : c.strength ≤ s
    · rw [if_pos h, if_pos (le_trans h hle)]
      exact Nat.add_le_add_left ih 1
    · rw [if_neg h]; simp only [Nat.zero_add]
      by_cases h2 : c.strength ≤ t
      · rw [if_pos h2]
        exact Nat.le_trans ih (Nat.le_add_left (countAtMost cs t) 1)
      · rw [if_neg h2]; simp only [Nat.zero_add]; exact ih

/-- After strengthenClaim, the count at the new threshold is at least
    the count at the old threshold on the original claims. -/
lemma countAtMost_strengthen_ge {k : ClaimantId} {claims : List ClaimQ}
    {s_k s' : ℚ} {hs' : 0 < s'} (hle : s_k ≤ s') :
    countAtMost (strengthenClaim k s' hs' claims) s' ≥
    countAtMost claims s_k := by
  induction claims with
  | nil => exact Nat.le_refl 0
  | cons c cs ih =>
    simp only [strengthenClaim, countAtMost]
    split
    case isTrue heq =>
      show (if s' ≤ s' then 1 else 0) + countAtMost cs s' ≥
           (if c.strength ≤ s_k then 1 else 0) + countAtMost cs s_k
      rw [if_pos (le_refl s')]
      by_cases h : c.strength ≤ s_k
      · rw [if_pos h]
        exact Nat.add_le_add_left (countAtMost_mono hle) 1
      · rw [if_neg h]; simp only [Nat.zero_add]
        exact Nat.le_trans (countAtMost_mono hle) (Nat.le_add_left _ 1)
    case isFalse hne =>
      show (if c.strength ≤ s' then 1 else 0) + countAtMost (strengthenClaim k s' hs' cs) s' ≥
           (if c.strength ≤ s_k then 1 else 0) + countAtMost cs s_k
      by_cases h : c.strength ≤ s_k
      · rw [if_pos h, if_pos (le_trans h hle)]
        exact Nat.add_le_add_left ih 1
      · rw [if_neg h]; simp only [Nat.zero_add]
        by_cases h2 : c.strength ≤ s'
        · rw [if_pos h2]
          exact Nat.le_trans ih (Nat.le_add_left _ 1)
        · rw [if_neg h2]; simp only [Nat.zero_add]; exact ih

/-- The peer-relative gate is node-level monotone. -/
theorem peerRelativeNode_monotone : NodeMonotonicity peerRelativeNode := by
  intro claims k s' hs' hmem hdist hle hperm
  simp only [peerRelativeNode] at hperm ⊢
  split at hperm
  case isTrue h_orig =>
    rw [lookupStrength_after_strengthen hmem hdist, strengthenClaim_length]
    have hsk_le : lookupStrength k claims ≤ s' := lookupStrength_le_of_all_le hmem hle
    have hge : countAtMost (strengthenClaim k s' hs' claims) s' ≥
               countAtMost claims (lookupStrength k claims) :=
      countAtMost_strengthen_ge hsk_le
    exact if_pos (Nat.le_trans h_orig (Nat.mul_le_mul_left 2 hge))
  case isFalse _ =>
    exact absurd hperm (by intro h; exact BinaryDecision.noConfusion h)

-- ═══════════════════════════════════════════════════════════════════
-- Binary Counterexample
-- ═══════════════════════════════════════════════════════════════════

private def alice : ClaimQ := ⟨0, 2/5, by norm_num, []⟩
private def bob   : ClaimQ := ⟨1, 11/20, by norm_num, []⟩
private def carol : ClaimQ := ⟨2, 9/10, by norm_num, []⟩

private def baseClaims : List ClaimQ := [alice, bob, carol]

private def composedGraph : GovernanceGraph :=
  [thresholdNode (1/2), peerRelativeNode]

private lemma baseClaims_distinct : ClaimsDistinct baseClaims := by
  unfold ClaimsDistinct baseClaims alice bob carol
  show ([0, 1, 2] : List Nat).Nodup
  exact List.nodup_cons.mpr ⟨by decide, List.nodup_cons.mpr ⟨by decide,
    List.nodup_cons.mpr ⟨by decide, List.Pairwise.nil⟩⟩⟩

private lemma alice_in_baseClaims : InClaims 0 baseClaims :=
  ⟨alice, List.Mem.head _, rfl⟩

private lemma baseClaims_alice_strengthened_bound :
    ∀ c ∈ baseClaims, c.id = 0 → c.strength ≤ 3 / 5 := by
  intro c hm hid
  cases hm with
  | head =>
      simp only [alice] at hid ⊢
      norm_num
  | tail _ htail =>
      cases htail with
      | head =>
          simp only [bob] at hid
          exact absurd hid (by decide)
      | tail _ htail2 =>
          cases htail2 with
          | head =>
              simp only [carol] at hid
              exact absurd hid (by decide)
          | tail _ hnil =>
              exact absurd hnil List.not_mem_nil

/-- Baseline: Bob permitted through composed graph. -/
private theorem bob_permitted_baseline :
    graphDecide composedGraph baseClaims 1 = BinaryDecision.Permit := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

/-- After strengthening Alice from 2/5 to 3/5: Bob denied. -/
private theorem bob_denied_after_strengthen :
    graphDecide composedGraph
      (strengthenClaim 0 (3/5) (by norm_num) baseClaims) 1 =
    BinaryDecision.Deny := by
  native_decide

/-- **Theorem (Binary Composition Inadmissibility).**
    There exist governance nodes A and B, each individually satisfying
    node-level monotonicity, such that the composed graph A→B violates
    graph-level monotonicity. -/
theorem composition_inadmissibility :
    ¬ GraphMonotonicity composedGraph := by
  intro hmon
  have h := hmon baseClaims 0 (3/5) (by norm_num) 1
    alice_in_baseClaims
    baseClaims_distinct
    baseClaims_alice_strengthened_bound
    bob_permitted_baseline
  exact absurd h (by
    rw [bob_denied_after_strengthen]
    intro heq; exact BinaryDecision.noConfusion heq)

-- ═══════════════════════════════════════════════════════════════════
-- Three-valued governance types
-- ═══════════════════════════════════════════════════════════════════

/-- Three-valued decision outcome. -/
inductive Decision3 where
  | Permit   : Decision3
  | Deny     : Decision3
  | Escalate : Decision3
  deriving Repr, DecidableEq

/-- A three-valued governance node. -/
def GovernanceNodeFn3 := List ClaimQ → ClaimantId → Decision3

/-- A three-valued governance graph. -/
def GovernanceGraph3 := List GovernanceNodeFn3

/-- Filter claims to only those escalated by a node. -/
def filterEscalated (node : GovernanceNodeFn3) (claims : List ClaimQ) : List ClaimQ :=
  claims.filter (fun c => node claims c.id == Decision3.Escalate)

/-- Evaluate a claimant through a three-valued pipeline. -/
def graphDecide3 (graph : GovernanceGraph3) (claims : List ClaimQ)
    (k : ClaimantId) : BinaryDecision :=
  match graph with
  | [] => BinaryDecision.Permit
  | node :: rest =>
    match node claims k with
    | Decision3.Deny => BinaryDecision.Deny
    | Decision3.Permit => BinaryDecision.Permit
    | Decision3.Escalate =>
      let escalated := filterEscalated node claims
      graphDecide3 rest escalated k

-- ═══════════════════════════════════════════════════════════════════
-- Three-valued axioms
-- ═══════════════════════════════════════════════════════════════════

/-- Decision order: Deny < Escalate < Permit. -/
@[simp] def Decision3.rank : Decision3 → Nat
  | Decision3.Deny     => 0
  | Decision3.Escalate => 1
  | Decision3.Permit   => 2

/-- The order on three-valued decisions induced by their rank
`Deny < Escalate < Permit`. -/
def Decision3.le (d1 d2 : Decision3) : Prop := d1.rank ≤ d2.rank

instance : LE Decision3 := ⟨Decision3.le⟩

instance (d1 d2 : Decision3) : Decidable (d1 ≤ d2) :=
  inferInstanceAs (Decidable (d1.rank ≤ d2.rank))

/-- Node-level monotonicity (three-valued). -/
def NodeMonotonicity3 (node : GovernanceNodeFn3) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId) (s' : ℚ) (hs' : 0 < s'),
    InClaims k claims →
    ClaimsDistinct claims →
    (∀ c ∈ claims, c.id = k → c.strength ≤ s') →
    node claims k ≤ node (strengthenClaim k s' hs' claims) k

/-- Graph-level monotonicity (three-valued). -/
def GraphMonotonicity3 (graph : GovernanceGraph3) : Prop :=
  ∀ (claims : List ClaimQ) (k : ClaimantId) (s' : ℚ) (hs' : 0 < s')
    (j : ClaimantId),
    InClaims k claims →
    ClaimsDistinct claims →
    (∀ c ∈ claims, c.id = k → c.strength ≤ s') →
    graphDecide3 graph claims j = BinaryDecision.Permit →
    graphDecide3 graph (strengthenClaim k s' hs' claims) j = BinaryDecision.Permit

-- ═══════════════════════════════════════════════════════════════════
-- Three-valued Node A: threshold3
-- ═══════════════════════════════════════════════════════════════════

/-- Three-valued threshold gate. -/
def thresholdNode3 (lo hi : ℚ) : GovernanceNodeFn3 := fun claims k =>
  let s := lookupStrength k claims
  if s > hi then Decision3.Permit
  else if s > lo then Decision3.Escalate
  else Decision3.Deny

/-- The three-valued threshold gate is node-level monotone. -/
lemma thresholdNode3_monotone (lo hi : ℚ) :
    NodeMonotonicity3 (thresholdNode3 lo hi) := by
  intro claims k s' hs' hmem hdist hle
  show (thresholdNode3 lo hi claims k).rank ≤
       (thresholdNode3 lo hi (strengthenClaim k s' hs' claims) k).rank
  simp only [thresholdNode3, lookupStrength_after_strengthen hmem hdist]
  have hsk_le : lookupStrength k claims ≤ s' := lookupStrength_le_of_all_le hmem hle
  by_cases h1 : lookupStrength k claims > hi
  · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 hsk_le)]
  · rw [if_neg h1]
    by_cases h2 : lookupStrength k claims > lo
    · rw [if_pos h2]
      by_cases h3 : s' > hi
      · rw [if_pos h3]; simp [Decision3.rank]
      · rw [if_neg h3, if_pos (lt_of_lt_of_le h2 hsk_le)]
    · rw [if_neg h2]
      by_cases h3 : s' > hi
      · rw [if_pos h3]; simp [Decision3.rank]
      · rw [if_neg h3]
        by_cases h4 : s' > lo
        · rw [if_pos h4]; simp [Decision3.rank]
        · rw [if_neg h4]

-- ═══════════════════════════════════════════════════════════════════
-- Three-valued Node B: peer-relative (wrapped)
-- ═══════════════════════════════════════════════════════════════════

/-- Peer-relative gate wrapped as a three-valued node. -/
def peerRelativeNode3 : GovernanceNodeFn3 := fun claims k =>
  match peerRelativeNode claims k with
  | BinaryDecision.Permit => Decision3.Permit
  | BinaryDecision.Deny   => Decision3.Deny

/-- The peer-relative node (wrapped) is three-valued monotone. -/
lemma peerRelativeNode3_monotone : NodeMonotonicity3 peerRelativeNode3 := by
  intro claims k s' hs' hmem hdist hle
  show (peerRelativeNode3 claims k).rank ≤
       (peerRelativeNode3 (strengthenClaim k s' hs' claims) k).rank
  simp only [peerRelativeNode3]
  have hbin := peerRelativeNode_monotone claims k s' hs' hmem hdist hle
  cases h : peerRelativeNode claims k with
  | Permit =>
    have h2 := hbin h
    simp only [h2, Decision3.rank]; omega
  | Deny =>
    cases h2 : peerRelativeNode (strengthenClaim k s' hs' claims) k with
    | Permit => simp [Decision3.rank]
    | Deny => simp [Decision3.rank]

-- ═══════════════════════════════════════════════════════════════════
-- Three-valued Counterexample
-- ═══════════════════════════════════════════════════════════════════

private def alice3 : ClaimQ := ⟨0, 1/4, by norm_num, []⟩
private def bob3   : ClaimQ := ⟨1, 3/8, by norm_num, []⟩
private def carol3 : ClaimQ := ⟨2, 2/5, by norm_num, []⟩

private def baseClaims3 : List ClaimQ := [alice3, bob3, carol3]

private def strengthenedBaseClaims3 : List ClaimQ :=
  strengthenClaim 0 (9/20) (by norm_num) baseClaims3

private def composedGraph3 : GovernanceGraph3 :=
  [thresholdNode3 (1/4) (1/2), peerRelativeNode3]

private lemma baseClaims3_distinct : ClaimsDistinct baseClaims3 := by
  unfold ClaimsDistinct baseClaims3 alice3 bob3 carol3
  show ([0, 1, 2] : List Nat).Nodup
  exact List.nodup_cons.mpr ⟨by decide, List.nodup_cons.mpr ⟨by decide,
    List.nodup_cons.mpr ⟨by decide, List.Pairwise.nil⟩⟩⟩

private lemma alice3_in_baseClaims3 : InClaims 0 baseClaims3 :=
  ⟨alice3, List.Mem.head _, rfl⟩

private lemma baseClaims3_alice_strengthened_bound :
    ∀ c ∈ baseClaims3, c.id = 0 → c.strength ≤ 9 / 20 := by
  intro c hm hid
  cases hm with
  | head =>
      simp only [alice3] at hid ⊢
      norm_num
  | tail _ htail =>
      cases htail with
      | head =>
          simp only [bob3] at hid
          exact absurd hid (by decide)
      | tail _ htail2 =>
          cases htail2 with
          | head =>
              simp only [carol3] at hid
              exact absurd hid (by decide)
          | tail _ hnil =>
              exact absurd hnil List.not_mem_nil

/-- Baseline: Bob permitted through three-valued composed graph. -/
private theorem bob3_permitted_baseline :
    graphDecide3 composedGraph3 baseClaims3 1 = BinaryDecision.Permit := by
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

/-- After strengthening Alice from 1/4 to 9/20: Bob denied. -/
private theorem bob3_denied_after_strengthen :
    graphDecide3 composedGraph3 strengthenedBaseClaims3 1 =
    BinaryDecision.Deny := by
  native_decide

/-- Node A (thresholdNode3 1/4 1/2) is individually monotone. -/
lemma nodeA_monotone : NodeMonotonicity3 (thresholdNode3 (1/4) (1/2)) :=
  thresholdNode3_monotone (1/4) (1/2)

/-- Node B (peerRelativeNode3) is individually monotone. -/
lemma nodeB_monotone : NodeMonotonicity3 peerRelativeNode3 :=
  peerRelativeNode3_monotone

/-- A first-stage three-valued policy exposes the same escalation surface as
    the concrete counterexample: Bob and Carol are escalated initially, Alice
    is not, and after Alice is strengthened all three enter the escalated
    downstream peer-relative pool. The monotonicity field makes the predicate
    non-vacuous as a governance-policy assumption rather than a raw truth
    table. -/
def EscalationPolicyWitness (node : GovernanceNodeFn3) : Prop :=
  NodeMonotonicity3 node ∧
  node baseClaims3 1 = Decision3.Escalate ∧
  node strengthenedBaseClaims3 1 = Decision3.Escalate ∧
  filterEscalated node baseClaims3 = [bob3, carol3] ∧
  filterEscalated node strengthenedBaseClaims3 = strengthenedBaseClaims3

/-- The threshold escalation policy used by the concrete theorem is a
    nontrivial inhabitant of `EscalationPolicyWitness`. -/
theorem thresholdNode3_escalationPolicyWitness :
    EscalationPolicyWitness (thresholdNode3 (1/4) (1/2)) := by
  refine ⟨thresholdNode3_monotone (1/4) (1/2), ?_, ?_, ?_, ?_⟩
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  all_goals native_decide

private theorem escalationPolicyWitness_base_permits_bob
    {node : GovernanceNodeFn3} (hnode : EscalationPolicyWitness node) :
    graphDecide3 [node, peerRelativeNode3] baseClaims3 1 =
      BinaryDecision.Permit := by
  rcases hnode with ⟨_, hBob, _, hfilter, _⟩
  simp [graphDecide3, hBob, hfilter, peerRelativeNode3, peerRelativeNode,
    lookupStrength, countAtMost, bob3, carol3]

private theorem escalationPolicyWitness_strengthened_denies_bob
    {node : GovernanceNodeFn3} (hnode : EscalationPolicyWitness node) :
    graphDecide3 [node, peerRelativeNode3] strengthenedBaseClaims3 1 =
      BinaryDecision.Deny := by
  rcases hnode with ⟨_, _, hBob, _, hfilter⟩
  simp [graphDecide3, hBob, hfilter]
  -- native_decide: finite concrete claim-profile, witness-membership, and diagnostic checks.
  native_decide

/-- Parametric three-valued escalation obstruction. Any monotone first-stage
    policy satisfying the witness escalation surface becomes inadmissible when
    composed with the peer-relative downstream gate: strengthening Alice adds a
    new escalated competitor to Bob's downstream comparison set and flips Bob
    from permit to deny. -/
theorem three_valued_escalationPolicyWitness_composition_inadmissibility
    (node : GovernanceNodeFn3) (hnode : EscalationPolicyWitness node) :
    ¬ GraphMonotonicity3 [node, peerRelativeNode3] := by
  intro hmon
  have h := hmon baseClaims3 0 (9/20) (by norm_num) 1
    alice3_in_baseClaims3
    baseClaims3_distinct
    baseClaims3_alice_strengthened_bound
    (escalationPolicyWitness_base_permits_bob hnode)
  change graphDecide3 [node, peerRelativeNode3] strengthenedBaseClaims3 1 =
    BinaryDecision.Permit at h
  exact absurd h (by
    rw [escalationPolicyWitness_strengthened_denies_bob hnode]
    intro heq; exact BinaryDecision.noConfusion heq)

/-- **Theorem (Three-Valued Composition Inadmissibility).**
    There exist three-valued governance nodes A and B, each individually
    satisfying NodeMonotonicity3, such that the composed graph A→B
    violates GraphMonotonicity3. Escalate creates a competitive channel
    that does not exist in binary. -/
theorem three_valued_composition_inadmissibility :
    ¬ GraphMonotonicity3 composedGraph3 := by
  simpa [composedGraph3] using
    three_valued_escalationPolicyWitness_composition_inadmissibility
      (thresholdNode3 (1/4) (1/2))
      thresholdNode3_escalationPolicyWitness

end Legitimacy
