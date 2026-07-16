/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Diagnostics.DecisionSystem

/-!
# Institution probe for governance graphs

This file records the institution-theoretic probe for the current governance
graph substrate.  The result is positive only for the automorphism fragment:
signatures share the existing first-party claimant sort `ClaimantId := Nat`,
and signature morphisms may relabel that claimant sort by a bijection.  The
current substrate does not yet expose richer schema morphisms, graph
homomorphisms, or categorical composition of governance systems.

For this fragment:

* `Sign` is `GovernanceSignature`, a schema selecting which graph-axiom
  sentences are in scope.
* `Sen Sigma` is `GovernanceSentence Sigma`, one of the scoped axiom labels.
* `Mod Sigma` is `GovernanceModel Sigma`, a `GovernanceGraph` fibered over the
  signature.
* `M |= phi` means the existing graph predicate named by `phi` holds of
  `M.graph`.

The nontrivial probe is claimant relabeling.  Sentence translation preserves
the axiom label; model reduction relabels the graph by the inverse claimant
bijection.  The satisfaction condition follows from invariance of the existing
graph diagnostics under this relabeling.
-/

set_option autoImplicit false

namespace Legitimacy

/-! ## Claimant relabeling on profiles and graphs -/

/-- Relabel the claimant id of a first-party claim. -/
def renameClaim (e : ClaimantId ≃ ClaimantId) (c : ClaimQ) : ClaimQ where
  id := e c.id
  strength := c.strength
  strength_pos := c.strength_pos
  metadata := c.metadata

/-- Relabel every claimant id in a claim profile. -/
def renameClaims (e : ClaimantId ≃ ClaimantId) (claims : List ClaimQ) : List ClaimQ :=
  claims.map (renameClaim e)

@[simp]
lemma renameClaim_id (e : ClaimantId ≃ ClaimantId) (c : ClaimQ) :
    (renameClaim e c).id = e c.id :=
  rfl

@[simp]
lemma renameClaim_strength (e : ClaimantId ≃ ClaimantId) (c : ClaimQ) :
    (renameClaim e c).strength = c.strength :=
  rfl

@[simp]
lemma renameClaim_symm_apply (e : ClaimantId ≃ ClaimantId) (c : ClaimQ) :
    renameClaim e.symm (renameClaim e c) = c := by
  cases c
  simp [renameClaim]

@[simp]
lemma renameClaim_apply_symm (e : ClaimantId ≃ ClaimantId) (c : ClaimQ) :
    renameClaim e (renameClaim e.symm c) = c := by
  simpa using renameClaim_symm_apply e.symm c

@[simp]
lemma renameClaims_symm_apply (e : ClaimantId ≃ ClaimantId)
    (claims : List ClaimQ) :
    renameClaims e.symm (renameClaims e claims) = claims := by
  simp [renameClaims, List.map_map, Function.comp_def]

@[simp]
lemma renameClaims_apply_symm (e : ClaimantId ≃ ClaimantId)
    (claims : List ClaimQ) :
    renameClaims e (renameClaims e.symm claims) = claims := by
  simpa using renameClaims_symm_apply e.symm claims

lemma inClaims_rename (e : ClaimantId ≃ ClaimantId)
    {claims : List ClaimQ} {k : ClaimantId} :
    InClaims (e k) (renameClaims e claims) ↔ InClaims k claims := by
  constructor
  · intro h
    obtain ⟨c, hc, hid⟩ := h
    refine ⟨renameClaim e.symm c, ?_, ?_⟩
    · have hmem :
          renameClaim e.symm c ∈ renameClaims e.symm (renameClaims e claims) :=
        List.mem_map.mpr ⟨c, hc, rfl⟩
      simpa using hmem
    · simpa [renameClaim] using congrArg e.symm hid
  · intro h
    obtain ⟨c, hc, hid⟩ := h
    refine ⟨renameClaim e c, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨c, hc, rfl⟩
    · simp [renameClaim, hid]

lemma claimsDistinct_rename (e : ClaimantId ≃ ClaimantId)
    {claims : List ClaimQ} :
    ClaimsDistinct claims → ClaimsDistinct (renameClaims e claims) := by
  intro h
  unfold ClaimsDistinct at h ⊢
  simpa [renameClaims, renameClaim, List.map_map] using h.map e.injective

lemma claimsDistinct_rename_iff (e : ClaimantId ≃ ClaimantId)
    (claims : List ClaimQ) :
    ClaimsDistinct (renameClaims e claims) ↔ ClaimsDistinct claims := by
  constructor
  · intro h
    have h' := claimsDistinct_rename e.symm (claims := renameClaims e claims) h
    simpa using h'
  · exact claimsDistinct_rename e

lemma removeClaimGraph_rename (e : ClaimantId ≃ ClaimantId)
    (k : ClaimantId) :
    ∀ claims : List ClaimQ,
      removeClaimGraph (e k) (renameClaims e claims) =
        renameClaims e (removeClaimGraph k claims)
  | [] => by simp [renameClaims, removeClaimGraph]
  | c :: cs => by
      by_cases h : c.id = k
      · simp [renameClaims, removeClaimGraph, renameClaim, h]
      · have h' : e c.id ≠ e k := by
          intro heq
          exact h (e.injective heq)
        simp [renameClaims, removeClaimGraph, renameClaim, h, h']
        exact removeClaimGraph_rename e k cs

lemma strengthenClaim_rename (e : ClaimantId ≃ ClaimantId)
    (k : ClaimantId) (s : ℚ) (hs : 0 < s) :
    ∀ claims : List ClaimQ,
      strengthenClaim (e k) s hs (renameClaims e claims) =
        renameClaims e (strengthenClaim k s hs claims)
  | [] => by simp [renameClaims, strengthenClaim]
  | c :: cs => by
      by_cases h : c.id = k
      · simp [renameClaims, strengthenClaim, renameClaim, h]
      · have h' : e c.id ≠ e k := by
          intro heq
          exact h (e.injective heq)
        simp [renameClaims, strengthenClaim, renameClaim, h, h']
        exact strengthenClaim_rename e k s hs cs

lemma scaleClaims_rename (e : ClaimantId ≃ ClaimantId)
    (claims : List ClaimQ) (alpha : ℚ) (halpha : 0 < alpha) :
    renameClaims e
        (claims.map
          (fun c => ⟨c.id, alpha * c.strength, mul_pos halpha c.strength_pos, c.metadata⟩)) =
      (renameClaims e claims).map
        (fun c => ⟨c.id, alpha * c.strength, mul_pos halpha c.strength_pos, c.metadata⟩) := by
  induction claims with
  | nil => simp [renameClaims]
  | cons c cs ih => simp [renameClaims, renameClaim]

/-- Relabel a governance node by reading the input profile and subject through
the inverse claimant bijection. -/
def relabelNode (e : ClaimantId ≃ ClaimantId)
    (node : GovernanceNodeFn) : GovernanceNodeFn :=
  fun claims k => node (renameClaims e.symm claims) (e.symm k)

/-- Relabel every node in a sequential governance graph. -/
def relabelGraph (e : ClaimantId ≃ ClaimantId)
    (graph : GovernanceGraph) : GovernanceGraph :=
  graph.map (relabelNode e)

private lemma filterPermitted_relabel_aux (e : ClaimantId ≃ ClaimantId)
    (node : GovernanceNodeFn) (profile : List ClaimQ) :
    ∀ claims : List ClaimQ,
      List.filter
          (fun c =>
            relabelNode e node (renameClaims e profile) c.id ==
              BinaryDecision.Permit)
          (renameClaims e claims) =
        renameClaims e
          (List.filter
            (fun c => node profile c.id == BinaryDecision.Permit) claims)
  | [] => by simp [renameClaims]
  | c :: cs => by
      cases hnode : node profile c.id
      · simp [renameClaims, renameClaim, relabelNode, hnode,
          List.map_map, Function.comp_def]
        simpa [renameClaims, renameClaim, relabelNode,
          List.map_map, Function.comp_def] using
          filterPermitted_relabel_aux e node profile cs
      · simp [renameClaims, renameClaim, relabelNode, hnode,
          List.map_map, Function.comp_def]
        simpa [renameClaims, renameClaim, relabelNode,
          List.map_map, Function.comp_def] using
          filterPermitted_relabel_aux e node profile cs

lemma filterPermitted_relabel (e : ClaimantId ≃ ClaimantId)
    (node : GovernanceNodeFn) :
    ∀ claims : List ClaimQ,
      filterPermitted (relabelNode e node) (renameClaims e claims) =
        renameClaims e (filterPermitted node claims)
  | claims => by
      exact filterPermitted_relabel_aux e node claims claims

lemma graphDecide_relabel (e : ClaimantId ≃ ClaimantId)
    (graph : GovernanceGraph) :
    ∀ (claims : List ClaimQ) (k : ClaimantId),
      graphDecide (relabelGraph e graph) (renameClaims e claims) (e k) =
        graphDecide graph claims k
  | claims, k => by
      induction graph generalizing claims with
      | nil => simp [relabelGraph, graphDecide]
      | cons node rest ih =>
          cases hnode : node claims k
          · simp [relabelGraph, graphDecide, relabelNode, hnode,
              filterPermitted_relabel e node claims]
            exact ih (filterPermitted node claims)
          · simp [relabelGraph, graphDecide, relabelNode, hnode]

lemma graphConsistency_relabel (e : ClaimantId ≃ ClaimantId)
    (graph : GovernanceGraph) :
    GraphConsistency (relabelGraph e graph) ↔ GraphConsistency graph := by
  constructor
  · intro hcons claims k j hk hj hkj hdist hden
    have hk' : InClaims (e k) (renameClaims e claims) :=
      (inClaims_rename e).mpr hk
    have hj' : InClaims (e j) (renameClaims e claims) :=
      (inClaims_rename e).mpr hj
    have hkj' : e k ≠ e j := by
      intro heq
      exact hkj (e.injective heq)
    have hdist' : ClaimsDistinct (renameClaims e claims) :=
      (claimsDistinct_rename_iff e claims).mpr hdist
    have hden' :
        graphDecide (relabelGraph e graph) (renameClaims e claims) (e k) =
          BinaryDecision.Deny := by
      simpa [graphDecide_relabel e graph claims k] using hden
    have h := hcons (renameClaims e claims) (e k) (e j)
      hk' hj' hkj' hdist' hden'
    simpa [graphDecide_relabel e graph claims j,
      removeClaimGraph_rename e k claims,
      graphDecide_relabel e graph (removeClaimGraph k claims) j] using h
  · intro hcons claims k j hk hj hkj hdist hden
    let claims0 := renameClaims e.symm claims
    let k0 := e.symm k
    let j0 := e.symm j
    have hk0 : InClaims k0 claims0 := by
      dsimp [claims0, k0]
      exact (inClaims_rename e.symm).mpr hk
    have hj0 : InClaims j0 claims0 := by
      dsimp [claims0, j0]
      exact (inClaims_rename e.symm).mpr hj
    have hkj0 : k0 ≠ j0 := by
      intro heq
      exact hkj (by simpa [k0, j0] using congrArg e heq)
    have hdist0 : ClaimsDistinct claims0 := by
      dsimp [claims0]
      exact (claimsDistinct_rename_iff e.symm claims).mpr hdist
    have hden0 :
        graphDecide graph claims0 k0 = BinaryDecision.Deny := by
      have hrel := graphDecide_relabel e graph claims0 k0
      have hrel' :
          graphDecide (relabelGraph e graph) claims k =
            graphDecide graph claims0 k0 := by
        simpa [claims0, k0] using hrel
      exact hrel'.symm.trans hden
    have h := hcons claims0 k0 j0 hk0 hj0 hkj0 hdist0 hden0
    have hleft := graphDecide_relabel e graph claims0 j0
    have hright := graphDecide_relabel e graph
      (removeClaimGraph k0 claims0) j0
    have hremove :
        renameClaims e (removeClaimGraph k0 claims0) =
          removeClaimGraph k claims := by
      dsimp [claims0, k0]
      simpa using (removeClaimGraph_rename e (e.symm k)
        (renameClaims e.symm claims)).symm
    calc
      graphDecide (relabelGraph e graph) claims j =
          graphDecide graph claims0 j0 := by
            simpa [claims0, j0] using hleft
      _ = graphDecide graph (removeClaimGraph k0 claims0) j0 := h
      _ = graphDecide (relabelGraph e graph) (removeClaimGraph k claims) j := by
            simpa [hremove, j0] using hright.symm

lemma graphSolidarity_relabel (e : ClaimantId ≃ ClaimantId)
    (graph : GovernanceGraph) :
    GraphSolidarity (relabelGraph e graph) ↔ GraphSolidarity graph := by
  constructor
  · intro hsol claims alpha halpha j hj
    have hj' : InClaims (e j) (renameClaims e claims) :=
      (inClaims_rename e).mpr hj
    have h := hsol (renameClaims e claims) alpha halpha (e j) hj'
    have hleft := graphDecide_relabel e graph claims j
    have hright := graphDecide_relabel e graph
      (claims.map
        (fun c => ⟨c.id, alpha * c.strength, mul_pos halpha c.strength_pos, c.metadata⟩)) j
    calc
      graphDecide graph claims j =
          graphDecide (relabelGraph e graph) (renameClaims e claims) (e j) :=
            hleft.symm
      _ =
          graphDecide (relabelGraph e graph)
            ((renameClaims e claims).map
              (fun c => ⟨c.id, alpha * c.strength, mul_pos halpha c.strength_pos, c.metadata⟩))
            (e j) := h
      _ =
          graphDecide (relabelGraph e graph)
            (renameClaims e
              (claims.map
                (fun c => ⟨c.id, alpha * c.strength, mul_pos halpha c.strength_pos, c.metadata⟩)))
            (e j) := by
              rw [(scaleClaims_rename e claims alpha halpha).symm]
      _ =
          graphDecide graph
            (claims.map
              (fun c => ⟨c.id, alpha * c.strength, mul_pos halpha c.strength_pos, c.metadata⟩))
            j := hright
  · intro hsol claims alpha halpha j hj
    let claims0 := renameClaims e.symm claims
    let j0 := e.symm j
    have hj0 : InClaims j0 claims0 := by
      dsimp [claims0, j0]
      exact (inClaims_rename e.symm).mpr hj
    have h := hsol claims0 alpha halpha j0 hj0
    have hleft := graphDecide_relabel e graph claims0 j0
    have hright := graphDecide_relabel e graph
      (claims0.map
        (fun c => ⟨c.id, alpha * c.strength, mul_pos halpha c.strength_pos, c.metadata⟩)) j0
    have hscale :
        renameClaims e
            (claims0.map
              (fun c => ⟨c.id, alpha * c.strength, mul_pos halpha c.strength_pos, c.metadata⟩)) =
          claims.map
            (fun c => ⟨c.id, alpha * c.strength, mul_pos halpha c.strength_pos, c.metadata⟩) := by
      dsimp [claims0]
      simp [scaleClaims_rename e (renameClaims e.symm claims) alpha halpha]
    calc
      graphDecide (relabelGraph e graph) claims j =
          graphDecide graph claims0 j0 := by
            simpa [claims0, j0] using hleft
      _ = graphDecide graph
            (claims0.map
              (fun c => ⟨c.id, alpha * c.strength, mul_pos halpha c.strength_pos, c.metadata⟩)) j0 := h
      _ = graphDecide (relabelGraph e graph)
            (claims.map
              (fun c => ⟨c.id, alpha * c.strength, mul_pos halpha c.strength_pos, c.metadata⟩)) j := by
            simpa [hscale, j0] using hright.symm

lemma graphMonotonicity_relabel (e : ClaimantId ≃ ClaimantId)
    (graph : GovernanceGraph) :
    GraphMonotonicity (relabelGraph e graph) ↔ GraphMonotonicity graph := by
  constructor
  · intro hmon claims k s hs j hk hdist hle hperm
    have hk' : InClaims (e k) (renameClaims e claims) :=
      (inClaims_rename e).mpr hk
    have hdist' : ClaimsDistinct (renameClaims e claims) :=
      (claimsDistinct_rename_iff e claims).mpr hdist
    have hle' :
        ∀ c ∈ renameClaims e claims, c.id = e k → c.strength ≤ s := by
      intro c hc hid
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
      exact hle c0 hc0 (e.injective hid)
    have hperm' :
        graphDecide (relabelGraph e graph) (renameClaims e claims) (e j) =
          BinaryDecision.Permit := by
      simpa [graphDecide_relabel e graph claims j] using hperm
    have h := hmon (renameClaims e claims) (e k) s hs (e j)
      hk' hdist' hle' hperm'
    simpa [strengthenClaim_rename e k s hs claims,
      graphDecide_relabel e graph (strengthenClaim k s hs claims) j] using h
  · intro hmon claims k s hs j hk hdist hle hperm
    let claims0 := renameClaims e.symm claims
    let k0 := e.symm k
    let j0 := e.symm j
    have hk0 : InClaims k0 claims0 := by
      dsimp [claims0, k0]
      exact (inClaims_rename e.symm).mpr hk
    have hdist0 : ClaimsDistinct claims0 := by
      dsimp [claims0]
      exact (claimsDistinct_rename_iff e.symm claims).mpr hdist
    have hle0 : ∀ c ∈ claims0, c.id = k0 → c.strength ≤ s := by
      intro c hc hid
      dsimp [claims0] at hc
      obtain ⟨c1, hc1, hc_eq⟩ := List.mem_map.mp hc
      subst hc_eq
      exact hle c1 hc1 (by simpa [k0] using congrArg e hid)
    have hperm0 :
        graphDecide graph claims0 j0 = BinaryDecision.Permit := by
      have hrel := graphDecide_relabel e graph claims0 j0
      have hrel' :
          graphDecide (relabelGraph e graph) claims j =
            graphDecide graph claims0 j0 := by
        simpa [claims0, j0] using hrel
      exact hrel'.symm.trans hperm
    have h := hmon claims0 k0 s hs j0 hk0 hdist0 hle0 hperm0
    have hright := graphDecide_relabel e graph (strengthenClaim k0 s hs claims0) j0
    have hstrength :
        renameClaims e (strengthenClaim k0 s hs claims0) =
          strengthenClaim k s hs claims := by
      dsimp [claims0, k0]
      simpa using (strengthenClaim_rename e (e.symm k) s hs
        (renameClaims e.symm claims)).symm
    calc
      graphDecide (relabelGraph e graph) (strengthenClaim k s hs claims) j =
          graphDecide graph (strengthenClaim k0 s hs claims0) j0 := by
            simpa [hstrength, j0] using hright
      _ = BinaryDecision.Permit := h

lemma graphStrategyproofness_relabel (e : ClaimantId ≃ ClaimantId)
    (graph : GovernanceGraph) :
    GraphStrategyproofness (relabelGraph e graph) ↔
      GraphStrategyproofness graph := by
  constructor
  · intro hsp claims k s hs hk hdist hperm
    have hk' : InClaims (e k) (renameClaims e claims) :=
      (inClaims_rename e).mpr hk
    have hdist' : ClaimsDistinct (renameClaims e claims) :=
      (claimsDistinct_rename_iff e claims).mpr hdist
    have hperm' :
        graphDecide (relabelGraph e graph)
            (strengthenClaim (e k) s hs (renameClaims e claims)) (e k) =
          BinaryDecision.Permit := by
      simpa [strengthenClaim_rename e k s hs claims,
        graphDecide_relabel e graph (strengthenClaim k s hs claims) k] using hperm
    have h := hsp (renameClaims e claims) (e k) s hs hk' hdist' hperm'
    simpa [graphDecide_relabel e graph claims k] using h
  · intro hsp claims k s hs hk hdist hperm
    let claims0 := renameClaims e.symm claims
    let k0 := e.symm k
    have hk0 : InClaims k0 claims0 := by
      dsimp [claims0, k0]
      exact (inClaims_rename e.symm).mpr hk
    have hdist0 : ClaimsDistinct claims0 := by
      dsimp [claims0]
      exact (claimsDistinct_rename_iff e.symm claims).mpr hdist
    have hperm0 :
        graphDecide graph (strengthenClaim k0 s hs claims0) k0 =
          BinaryDecision.Permit := by
      have hrel := graphDecide_relabel e graph (strengthenClaim k0 s hs claims0) k0
      have hstrength :
          renameClaims e (strengthenClaim k0 s hs claims0) =
            strengthenClaim k s hs claims := by
        dsimp [claims0, k0]
        simpa using (strengthenClaim_rename e (e.symm k) s hs
          (renameClaims e.symm claims)).symm
      have hrel' :
          graphDecide (relabelGraph e graph) (strengthenClaim k s hs claims) k =
            graphDecide graph (strengthenClaim k0 s hs claims0) k0 := by
        simpa [hstrength, k0] using hrel
      exact hrel'.symm.trans hperm
    have h := hsp claims0 k0 s hs hk0 hdist0 hperm0
    have hleft := graphDecide_relabel e graph claims0 k0
    simpa [claims0, k0] using hleft.trans h

/-! ## The governance institution fragment -/

/-- Axiom labels currently exposed by the first-party graph substrate. -/
inductive GovernanceAxiom where
  | consistency
  | solidarity
  | monotonicity
  | strategyproofness
  deriving DecidableEq, Repr

/-- Satisfaction of a graph-level axiom label by an existing governance graph. -/
def GovernanceAxiom.satisfies : GovernanceAxiom → GovernanceGraph → Prop
  | .consistency, graph => GraphConsistency graph
  | .solidarity, graph => GraphSolidarity graph
  | .monotonicity, graph => GraphMonotonicity graph
  | .strategyproofness, graph => GraphStrategyproofness graph

lemma GovernanceAxiom.satisfies_relabel
    (kind : GovernanceAxiom) (e : ClaimantId ≃ ClaimantId)
    (graph : GovernanceGraph) :
    kind.satisfies (relabelGraph e graph) ↔ kind.satisfies graph := by
  cases kind
  · exact graphConsistency_relabel e graph
  · exact graphSolidarity_relabel e graph
  · exact graphMonotonicity_relabel e graph
  · exact graphStrategyproofness_relabel e graph

/-- A governance signature is the current claimant sort plus an axiom
vocabulary selection.  This is intentionally not a richer schema category. -/
structure GovernanceSignature where
  includes : GovernanceAxiom → Prop

/-- The full current graph-axiom vocabulary as a signature. -/
def fullGovernanceSignature : GovernanceSignature where
  includes := fun _ => True

/-- A sentence over a governance signature is an included graph-axiom label. -/
structure GovernanceSentence (sigma : GovernanceSignature) where
  kind : GovernanceAxiom
  included : sigma.includes kind

/-- A model over a governance signature is currently just a governance graph
fibered over that signature. -/
structure GovernanceModel (_sigma : GovernanceSignature) where
  graph : GovernanceGraph

/-- Signature morphisms in the supported fragment: claimant automorphisms that
preserve the scoped axiom vocabulary. -/
structure GovernanceSignatureMorphism
    (sigma1 sigma2 : GovernanceSignature) where
  relabel : ClaimantId ≃ ClaimantId
  preserves_axiom : ∀ {kind : GovernanceAxiom},
    sigma1.includes kind → sigma2.includes kind

/-- Extensionality for supported signature morphisms.  The axiom-preservation
field is proof-valued, so the claimant relabeling determines the morphism. -/
theorem GovernanceSignatureMorphism.ext
    {sigma1 sigma2 : GovernanceSignature}
    {morphism1 morphism2 : GovernanceSignatureMorphism sigma1 sigma2}
    (h : ∀ claimant, morphism1.relabel claimant = morphism2.relabel claimant) :
    morphism1 = morphism2 := by
  cases morphism1 with
  | mk relabel1 preserves1 =>
      cases morphism2 with
      | mk relabel2 preserves2 =>
          simp only at h
          have hrel : relabel1 = relabel2 := Equiv.ext h
          subst hrel
          congr

/-- Identity signature morphism. -/
def GovernanceSignatureMorphism.id (sigma : GovernanceSignature) :
    GovernanceSignatureMorphism sigma sigma where
  relabel := Equiv.refl ClaimantId
  preserves_axiom := fun h => h

/-- Categorical composition of supported signature morphisms. -/
def GovernanceSignatureMorphism.trans {sigma1 sigma2 sigma3 : GovernanceSignature}
    (morphism12 : GovernanceSignatureMorphism sigma1 sigma2)
    (morphism23 : GovernanceSignatureMorphism sigma2 sigma3) :
    GovernanceSignatureMorphism sigma1 sigma3 where
  relabel := morphism12.relabel.trans morphism23.relabel
  preserves_axiom := fun h =>
    morphism23.preserves_axiom (morphism12.preserves_axiom h)

/-- Alias for categorical composition. -/
def GovernanceSignatureMorphism.comp {sigma1 sigma2 sigma3 : GovernanceSignature}
    (morphism12 : GovernanceSignatureMorphism sigma1 sigma2)
    (morphism23 : GovernanceSignatureMorphism sigma2 sigma3) :
    GovernanceSignatureMorphism sigma1 sigma3 :=
  morphism12.trans morphism23

@[simp]
theorem GovernanceSignatureMorphism.id_comp
    {sigma1 sigma2 : GovernanceSignature}
    (morphism : GovernanceSignatureMorphism sigma1 sigma2) :
    (GovernanceSignatureMorphism.id sigma1).trans morphism = morphism := by
  rfl

@[simp]
theorem GovernanceSignatureMorphism.comp_id
    {sigma1 sigma2 : GovernanceSignature}
    (morphism : GovernanceSignatureMorphism sigma1 sigma2) :
    morphism.trans (GovernanceSignatureMorphism.id sigma2) = morphism := by
  rfl

theorem GovernanceSignatureMorphism.assoc
    {sigma1 sigma2 sigma3 sigma4 : GovernanceSignature}
    (morphism12 : GovernanceSignatureMorphism sigma1 sigma2)
    (morphism23 : GovernanceSignatureMorphism sigma2 sigma3)
    (morphism34 : GovernanceSignatureMorphism sigma3 sigma4) :
    (morphism12.trans morphism23).trans morphism34 =
      morphism12.trans (morphism23.trans morphism34) := by
  rfl

/-- Translate a sentence along a supported signature morphism. -/
def GovernanceSentence.translate {sigma1 sigma2 : GovernanceSignature}
    (morphism : GovernanceSignatureMorphism sigma1 sigma2)
    (sentence : GovernanceSentence sigma1) : GovernanceSentence sigma2 where
  kind := sentence.kind
  included := morphism.preserves_axiom sentence.included

/-- Reduce a target-signature model along a claimant-relabeling signature
morphism by applying the inverse relabeling to graph semantics. -/
def GovernanceModel.reduce {sigma1 sigma2 : GovernanceSignature}
    (morphism : GovernanceSignatureMorphism sigma1 sigma2)
    (model : GovernanceModel sigma2) : GovernanceModel sigma1 where
  graph := relabelGraph morphism.relabel.symm model.graph

@[simp]
lemma renameClaim_refl (claim : ClaimQ) :
    renameClaim (Equiv.refl ClaimantId) claim = claim := by
  cases claim
  rfl

@[simp]
lemma renameClaims_refl (claims : List ClaimQ) :
    renameClaims (Equiv.refl ClaimantId) claims = claims := by
  induction claims with
  | nil => simp [renameClaims]
  | cons claim rest ih =>
      change renameClaim (Equiv.refl ClaimantId) claim ::
          renameClaims (Equiv.refl ClaimantId) rest = claim :: rest
      rw [renameClaim_refl, ih]

@[simp]
lemma relabelNode_refl (node : GovernanceNodeFn) :
    relabelNode (Equiv.refl ClaimantId) node = node := by
  funext claims claimant
  simp [relabelNode]

@[simp]
lemma relabelGraph_refl (graph : GovernanceGraph) :
    relabelGraph (Equiv.refl ClaimantId) graph = graph := by
  induction graph with
  | nil => simp [relabelGraph]
  | cons node rest ih =>
      calc
        relabelGraph (Equiv.refl ClaimantId) (node :: rest) =
            relabelNode (Equiv.refl ClaimantId) node ::
              relabelGraph (Equiv.refl ClaimantId) rest := rfl
        _ = node :: rest := by rw [relabelNode_refl, ih]

lemma renameClaims_trans (e f : ClaimantId ≃ ClaimantId)
    (claims : List ClaimQ) :
    renameClaims (e.trans f) claims =
      renameClaims f (renameClaims e claims) := by
  induction claims with
  | nil => simp [renameClaims]
  | cons claim rest ih =>
      change renameClaim (e.trans f) claim :: renameClaims (e.trans f) rest =
        renameClaim f (renameClaim e claim) :: renameClaims f (renameClaims e rest)
      rw [ih]
      cases claim
      rfl

lemma relabelNode_trans (e f : ClaimantId ≃ ClaimantId)
    (node : GovernanceNodeFn) :
    relabelNode (e.trans f) node = relabelNode f (relabelNode e node) := by
  funext claims claimant
  have hclaims :
      renameClaims (e.trans f).symm claims =
        renameClaims e.symm (renameClaims f.symm claims) := by
    simpa using renameClaims_trans f.symm e.symm claims
  simp [relabelNode, hclaims]

lemma relabelGraph_trans (e f : ClaimantId ≃ ClaimantId)
    (graph : GovernanceGraph) :
    relabelGraph (e.trans f) graph =
      relabelGraph f (relabelGraph e graph) := by
  induction graph with
  | nil => simp [relabelGraph]
  | cons node rest ih =>
      change relabelNode (e.trans f) node :: relabelGraph (e.trans f) rest =
        relabelNode f (relabelNode e node) ::
          relabelGraph f (relabelGraph e rest)
      rw [relabelNode_trans, ih]

@[simp]
theorem GovernanceSentence.translate_id
    {sigma : GovernanceSignature} (sentence : GovernanceSentence sigma) :
    sentence.translate (GovernanceSignatureMorphism.id sigma) = sentence := by
  cases sentence
  rfl

@[simp]
theorem GovernanceSentence.translate_comp
    {sigma1 sigma2 sigma3 : GovernanceSignature}
    (morphism12 : GovernanceSignatureMorphism sigma1 sigma2)
    (morphism23 : GovernanceSignatureMorphism sigma2 sigma3)
    (sentence : GovernanceSentence sigma1) :
    sentence.translate (morphism12.trans morphism23) =
      (sentence.translate morphism12).translate morphism23 := by
  cases sentence
  rfl

@[simp]
theorem GovernanceModel.reduce_id
    {sigma : GovernanceSignature} (model : GovernanceModel sigma) :
    model.reduce (GovernanceSignatureMorphism.id sigma) = model := by
  cases model
  simp [GovernanceModel.reduce, GovernanceSignatureMorphism.id]

theorem GovernanceModel.reduce_comp
    {sigma1 sigma2 sigma3 : GovernanceSignature}
    (morphism12 : GovernanceSignatureMorphism sigma1 sigma2)
    (morphism23 : GovernanceSignatureMorphism sigma2 sigma3)
    (model : GovernanceModel sigma3) :
    model.reduce (morphism12.trans morphism23) =
      (model.reduce morphism23).reduce morphism12 := by
  cases model with
  | mk graph =>
      simpa [GovernanceModel.reduce, GovernanceSignatureMorphism.trans] using
        relabelGraph_trans morphism23.relabel.symm morphism12.relabel.symm graph

namespace GovernanceSentence

/-- The sentence map of the supported `Sen` functor. -/
def Sen.map {sigma1 sigma2 : GovernanceSignature}
    (morphism : GovernanceSignatureMorphism sigma1 sigma2) :
    GovernanceSentence sigma1 → GovernanceSentence sigma2 :=
  fun sentence => sentence.translate morphism

/-- Identity component of the supported `Sen` functor. -/
def Sen.id (sigma : GovernanceSignature) :
    GovernanceSentence sigma → GovernanceSentence sigma :=
  Sen.map (GovernanceSignatureMorphism.id sigma)

@[simp]
theorem Sen.id_law {sigma : GovernanceSignature}
    (sentence : GovernanceSentence sigma) :
    Sen.id sigma sentence = sentence :=
  GovernanceSentence.translate_id sentence

@[simp]
theorem Sen.comp_law
    {sigma1 sigma2 sigma3 : GovernanceSignature}
    (morphism12 : GovernanceSignatureMorphism sigma1 sigma2)
    (morphism23 : GovernanceSignatureMorphism sigma2 sigma3)
    (sentence : GovernanceSentence sigma1) :
    Sen.map (morphism12.trans morphism23) sentence =
      Sen.map morphism23 (Sen.map morphism12 sentence) :=
  GovernanceSentence.translate_comp morphism12 morphism23 sentence

end GovernanceSentence

namespace GovernanceModel

/-- The contravariant model-reduction map of the supported `Mod` functor. -/
def Mod.map {sigma1 sigma2 : GovernanceSignature}
    (morphism : GovernanceSignatureMorphism sigma1 sigma2) :
    GovernanceModel sigma2 → GovernanceModel sigma1 :=
  fun model => model.reduce morphism

/-- Identity component of the supported contravariant `Mod` functor. -/
def Mod.id (sigma : GovernanceSignature) :
    GovernanceModel sigma → GovernanceModel sigma :=
  Mod.map (GovernanceSignatureMorphism.id sigma)

@[simp]
theorem Mod.id_law {sigma : GovernanceSignature}
    (model : GovernanceModel sigma) :
    Mod.id sigma model = model :=
  GovernanceModel.reduce_id model

theorem Mod.comp_law
    {sigma1 sigma2 sigma3 : GovernanceSignature}
    (morphism12 : GovernanceSignatureMorphism sigma1 sigma2)
    (morphism23 : GovernanceSignatureMorphism sigma2 sigma3)
    (model : GovernanceModel sigma3) :
    Mod.map (morphism12.trans morphism23) model =
      Mod.map morphism12 (Mod.map morphism23 model) :=
  GovernanceModel.reduce_comp morphism12 morphism23 model

end GovernanceModel

/-- Satisfaction for the governance institution fragment. -/
def GovernanceSatisfies {sigma : GovernanceSignature}
    (model : GovernanceModel sigma) (sentence : GovernanceSentence sigma) : Prop :=
  sentence.kind.satisfies model.graph

/-- A first-order category record for signatures, used here instead of importing
the full Mathlib category hierarchy. -/
structure SignCategory where
  Obj : Type
  Hom : Obj → Obj → Type
  id : (sigma : Obj) → Hom sigma sigma
  comp : {sigma1 sigma2 sigma3 : Obj} →
    Hom sigma1 sigma2 → Hom sigma2 sigma3 → Hom sigma1 sigma3
  id_comp : ∀ {sigma1 sigma2 : Obj} (morphism : Hom sigma1 sigma2),
    comp (id sigma1) morphism = morphism
  comp_id : ∀ {sigma1 sigma2 : Obj} (morphism : Hom sigma1 sigma2),
    comp morphism (id sigma2) = morphism
  assoc : ∀ {sigma1 sigma2 sigma3 sigma4 : Obj}
    (morphism12 : Hom sigma1 sigma2) (morphism23 : Hom sigma2 sigma3)
    (morphism34 : Hom sigma3 sigma4),
    comp (comp morphism12 morphism23) morphism34 =
      comp morphism12 (comp morphism23 morphism34)

/-- The category of governance signatures supported by the institution probe. -/
def governanceSignCategory : SignCategory where
  Obj := GovernanceSignature
  Hom := GovernanceSignatureMorphism
  id := GovernanceSignatureMorphism.id
  comp := fun morphism12 morphism23 => morphism12.trans morphism23
  id_comp := GovernanceSignatureMorphism.id_comp
  comp_id := GovernanceSignatureMorphism.comp_id
  assoc := GovernanceSignatureMorphism.assoc

/-- The Goguen-Burstall institution shape used by this probe. -/
structure GovernanceInstitution where
  Sign : Type
  Sen : Sign → Type
  Mod : Sign → Type
  Satisfies : {sigma : Sign} → Mod sigma → Sen sigma → Prop
  Hom : Sign → Sign → Type
  id : (sigma : Sign) → Hom sigma sigma
  comp : {sigma1 sigma2 sigma3 : Sign} →
    Hom sigma1 sigma2 → Hom sigma2 sigma3 → Hom sigma1 sigma3
  hom_id_comp : ∀ {sigma1 sigma2 : Sign} (morphism : Hom sigma1 sigma2),
    comp (id sigma1) morphism = morphism
  hom_comp_id : ∀ {sigma1 sigma2 : Sign} (morphism : Hom sigma1 sigma2),
    comp morphism (id sigma2) = morphism
  hom_assoc : ∀ {sigma1 sigma2 sigma3 sigma4 : Sign}
    (morphism12 : Hom sigma1 sigma2) (morphism23 : Hom sigma2 sigma3)
    (morphism34 : Hom sigma3 sigma4),
    comp (comp morphism12 morphism23) morphism34 =
      comp morphism12 (comp morphism23 morphism34)
  translate : {sigma1 sigma2 : Sign} → Hom sigma1 sigma2 → Sen sigma1 → Sen sigma2
  reduce : {sigma1 sigma2 : Sign} → Hom sigma1 sigma2 → Mod sigma2 → Mod sigma1
  translate_id :
    ∀ {sigma : Sign} (sentence : Sen sigma),
      translate (id sigma) sentence = sentence
  translate_comp :
    ∀ {sigma1 sigma2 sigma3 : Sign}
      (morphism12 : Hom sigma1 sigma2) (morphism23 : Hom sigma2 sigma3)
      (sentence : Sen sigma1),
      translate (comp morphism12 morphism23) sentence =
        translate morphism23 (translate morphism12 sentence)
  reduce_id :
    ∀ {sigma : Sign} (model : Mod sigma),
      reduce (id sigma) model = model
  reduce_comp :
    ∀ {sigma1 sigma2 sigma3 : Sign}
      (morphism12 : Hom sigma1 sigma2) (morphism23 : Hom sigma2 sigma3)
      (model : Mod sigma3),
      reduce (comp morphism12 morphism23) model =
        reduce morphism12 (reduce morphism23 model)
  satisfaction_condition :
    ∀ {sigma1 sigma2 : Sign} (morphism : Hom sigma1 sigma2)
      (model : Mod sigma2) (sentence : Sen sigma1),
      Satisfies model (translate morphism sentence) ↔
        Satisfies (reduce morphism model) sentence

theorem governance_satisfaction_condition
    {sigma1 sigma2 : GovernanceSignature}
    (morphism : GovernanceSignatureMorphism sigma1 sigma2)
    (model : GovernanceModel sigma2) (sentence : GovernanceSentence sigma1) :
    GovernanceSatisfies model (sentence.translate morphism) ↔
      GovernanceSatisfies (model.reduce morphism) sentence := by
  unfold GovernanceSatisfies GovernanceModel.reduce GovernanceSentence.translate
  exact (sentence.kind.satisfies_relabel morphism.relabel.symm model.graph).symm

/-- The institution fragment supported by the present governance graph
substrate. -/
def governanceInstitution : GovernanceInstitution where
  Sign := GovernanceSignature
  Sen := GovernanceSentence
  Mod := GovernanceModel
  Satisfies := GovernanceSatisfies
  Hom := GovernanceSignatureMorphism
  id := GovernanceSignatureMorphism.id
  comp := fun morphism12 morphism23 => morphism12.trans morphism23
  hom_id_comp := GovernanceSignatureMorphism.id_comp
  hom_comp_id := GovernanceSignatureMorphism.comp_id
  hom_assoc := GovernanceSignatureMorphism.assoc
  translate := fun morphism sentence => sentence.translate morphism
  reduce := fun morphism model => model.reduce morphism
  translate_id := GovernanceSentence.translate_id
  translate_comp := GovernanceSentence.translate_comp
  reduce_id := GovernanceModel.reduce_id
  reduce_comp := GovernanceModel.reduce_comp
  satisfaction_condition := governance_satisfaction_condition

/-! ## Probe test cases -/

theorem identity_signature_satisfaction
    {sigma : GovernanceSignature} (model : GovernanceModel sigma)
    (sentence : GovernanceSentence sigma) :
    GovernanceSatisfies model
        (sentence.translate (GovernanceSignatureMorphism.id sigma)) ↔
      GovernanceSatisfies
        (model.reduce (GovernanceSignatureMorphism.id sigma)) sentence := by
  exact governance_satisfaction_condition
    (GovernanceSignatureMorphism.id sigma) model sentence

/-- A claimant-relabeling morphism between signatures with the same axiom
vocabulary. -/
def claimantRelabelMorphism (sigma : GovernanceSignature)
    (e : ClaimantId ≃ ClaimantId) :
    GovernanceSignatureMorphism sigma sigma where
  relabel := e
  preserves_axiom := fun h => h

theorem claimant_relabel_satisfaction
    {sigma : GovernanceSignature} (e : ClaimantId ≃ ClaimantId)
    (model : GovernanceModel sigma) (sentence : GovernanceSentence sigma) :
    GovernanceSatisfies model (sentence.translate (claimantRelabelMorphism sigma e)) ↔
      GovernanceSatisfies
        (model.reduce (claimantRelabelMorphism sigma e)) sentence := by
  exact governance_satisfaction_condition
    (claimantRelabelMorphism sigma e) model sentence

/-- Universalized theorem for the supported fragment: every current
graph-axiom sentence is truth-preserved by any supported claimant relabeling. -/
theorem supported_governance_institution_truth_preservation :
    ∀ {sigma1 sigma2 : GovernanceSignature}
      (morphism : GovernanceSignatureMorphism sigma1 sigma2)
      (model : GovernanceModel sigma2) (sentence : GovernanceSentence sigma1),
      governanceInstitution.Satisfies model
          (governanceInstitution.translate morphism sentence) ↔
        governanceInstitution.Satisfies
          (governanceInstitution.reduce morphism model) sentence := by
  intro sigma1 sigma2 morphism model sentence
  exact governanceInstitution.satisfaction_condition morphism model sentence

theorem sentence_translation_identity_is_identity
    {sigma : GovernanceSignature} (sentence : GovernanceSentence sigma) :
    governanceInstitution.translate (governanceInstitution.id sigma) sentence =
      sentence := by
  rw [governanceInstitution.translate_id]

theorem model_reduction_identity_is_identity
    {sigma : GovernanceSignature} (model : GovernanceModel sigma) :
    governanceInstitution.reduce (governanceInstitution.id sigma) model =
      model := by
  rw [governanceInstitution.reduce_id]

theorem institution_morphism_id_left_neutral
    {sigma1 sigma2 : GovernanceSignature}
    (morphism : GovernanceSignatureMorphism sigma1 sigma2) :
    governanceInstitution.comp (governanceInstitution.id sigma1) morphism =
      morphism := by
  rw [governanceInstitution.hom_id_comp]

theorem institution_morphism_id_right_neutral
    {sigma1 sigma2 : GovernanceSignature}
    (morphism : GovernanceSignatureMorphism sigma1 sigma2) :
    governanceInstitution.comp morphism (governanceInstitution.id sigma2) =
      morphism := by
  rw [governanceInstitution.hom_comp_id]

theorem institution_morphism_composition_assoc
    {sigma1 sigma2 sigma3 sigma4 : GovernanceSignature}
    (morphism12 : GovernanceSignatureMorphism sigma1 sigma2)
    (morphism23 : GovernanceSignatureMorphism sigma2 sigma3)
    (morphism34 : GovernanceSignatureMorphism sigma3 sigma4) :
    governanceInstitution.comp
        (governanceInstitution.comp morphism12 morphism23) morphism34 =
      governanceInstitution.comp morphism12
        (governanceInstitution.comp morphism23 morphism34) := by
  rw [governanceInstitution.hom_assoc]

/-- Downstream consumer of the signature-category record: composition of
supported governance-signature morphisms associates through the record field. -/
theorem governance_signature_category_composition_assoc
    {sigma1 sigma2 sigma3 sigma4 : GovernanceSignature}
    (morphism12 : GovernanceSignatureMorphism sigma1 sigma2)
    (morphism23 : GovernanceSignatureMorphism sigma2 sigma3)
    (morphism34 : GovernanceSignatureMorphism sigma3 sigma4) :
    governanceSignCategory.comp
        (governanceSignCategory.comp morphism12 morphism23) morphism34 =
      governanceSignCategory.comp morphism12
        (governanceSignCategory.comp morphism23 morphism34) := by
  rw [governanceSignCategory.assoc]

/-- Downstream consumer of the institution record: sentence translation through
a composite supported signature morphism factors through the two components. -/
theorem sentence_translation_factors_through_composition
    {sigma1 sigma2 sigma3 : GovernanceSignature}
    (morphism12 : GovernanceSignatureMorphism sigma1 sigma2)
    (morphism23 : GovernanceSignatureMorphism sigma2 sigma3)
    (sentence : GovernanceSentence sigma1) :
    governanceInstitution.translate (morphism12.trans morphism23) sentence =
      governanceInstitution.translate morphism23
        (governanceInstitution.translate morphism12 sentence) := by
  rw [show morphism12.trans morphism23 =
      governanceInstitution.comp morphism12 morphism23 from rfl]
  rw [governanceInstitution.translate_comp]

/-- Downstream consumer of the institution record: model reduction through a
composite supported signature morphism factors contravariantly through the two
component reductions. -/
theorem model_reduction_factors_through_composition
    {sigma1 sigma2 sigma3 : GovernanceSignature}
    (morphism12 : GovernanceSignatureMorphism sigma1 sigma2)
    (morphism23 : GovernanceSignatureMorphism sigma2 sigma3)
    (model : GovernanceModel sigma3) :
    governanceInstitution.reduce (morphism12.trans morphism23) model =
      governanceInstitution.reduce morphism12
        (governanceInstitution.reduce morphism23 model) := by
  rw [show morphism12.trans morphism23 =
      governanceInstitution.comp morphism12 morphism23 from rfl]
  rw [governanceInstitution.reduce_comp]

/-- Satisfaction transfer across a composite supported signature morphism,
derived from the institution record's satisfaction condition and categorical
model-reduction law. -/
theorem composite_signature_satisfaction_transfer
    {sigma1 sigma2 sigma3 : GovernanceSignature}
    (morphism12 : GovernanceSignatureMorphism sigma1 sigma2)
    (morphism23 : GovernanceSignatureMorphism sigma2 sigma3)
    (model : GovernanceModel sigma3) (sentence : GovernanceSentence sigma1) :
    governanceInstitution.Satisfies model
        (governanceInstitution.translate (morphism12.trans morphism23) sentence) ↔
      governanceInstitution.Satisfies
        (governanceInstitution.reduce morphism12
          (governanceInstitution.reduce morphism23 model))
        sentence := by
  rw [sentence_translation_factors_through_composition morphism12 morphism23]
  rw [governanceInstitution.satisfaction_condition morphism23]
  rw [governanceInstitution.satisfaction_condition morphism12]

end Legitimacy
