/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Adam Benenson
-/

import Legitimacy.Protocol.CompiledStepPolicy
import Legitimacy.Protocol.Drift
import Mathlib.Data.List.Infix

/-!
# Legitimacy.Protocol.TrajectoryComposition

Claim occurrence encoding and historical nonempty-prefix monitoring for a
normalized trajectory. This module proves list and search semantics only. It
does not model Rust parsing, hashing, replay verification, floating-point
evaluation, kernel actions, or governance-state transitions.
-/

set_option autoImplicit false

namespace Legitimacy

/-- The five kinds in the normalized trajectory v0 Rust contract. -/
inductive NormalizedEventKindV0 where
  | actionRequest
  | actionResult
  | observation
  | message
  | lifecycle
  deriving DecidableEq, Repr

def NormalizedEventKindV0.label : NormalizedEventKindV0 → String
  | .actionRequest => "action-request"
  | .actionResult => "action-result"
  | .observation => "observation"
  | .message => "message"
  | .lifecycle => "lifecycle"

/-- Lean projection of provenance already validated and replay-bound in Rust. -/
structure NormalizedEventOccurrenceV0 where
  eventId : String
  kind : NormalizedEventKindV0
  sourceItemId : Option String
  rawRecordDigest : String
  canonicalEventDigest : String
  deriving DecidableEq, Repr

/-- Provenance metadata is retained, but no metadata value determines policy strength. -/
def occurrenceMetadata (event : NormalizedEventOccurrenceV0) :
    List (String × String) :=
  [ ("event-id", event.eventId)
  , ("kind", event.kind.label)
  , ("source-item-id", event.sourceItemId.getD "")
  , ("raw-record-digest", event.rawRecordDigest)
  , ("canonical-event-digest", event.canonicalEventDigest)
  ]

/-- Occurrence `i` is the distinct ordinal claim `(id = i, strength = i + 1)`. -/
def encodeOccurrence (i : Nat) (event : NormalizedEventOccurrenceV0) : ClaimQ :=
  { id := i
    strength := i + 1
    strength_pos := by positivity
    metadata := occurrenceMetadata event }

/-- Encode one claim per event, in the exact source order. -/
def encodedClaims (events : List NormalizedEventOccurrenceV0) : List ClaimQ :=
  events.mapIdx encodeOccurrence

@[simp] theorem encodedClaims_length (events : List NormalizedEventOccurrenceV0) :
    (encodedClaims events).length = events.length := by
  simp [encodedClaims]

@[simp] theorem encodedClaims_get_id (events : List NormalizedEventOccurrenceV0)
    (i : Nat) (hi : i < (encodedClaims events).length) :
    (encodedClaims events)[i].id = i := by
  simp [encodedClaims, encodeOccurrence]

@[simp] theorem encodedClaims_get_strength
    (events : List NormalizedEventOccurrenceV0)
    (i : Nat) (hi : i < (encodedClaims events).length) :
    (encodedClaims events)[i].strength = i + 1 := by
  simp [encodedClaims, encodeOccurrence]

theorem encodedClaims_ids (events : List NormalizedEventOccurrenceV0) :
    (encodedClaims events).map Claim.id = List.range events.length := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp [encodedClaims, encodeOccurrence]

/-- Occurrence indexing makes first-match lookup unambiguous. -/
theorem encodedClaims_distinct (events : List NormalizedEventOccurrenceV0) :
    ClaimsDistinct (encodedClaims events) := by
  rw [ClaimsDistinct, encodedClaims_ids]
  exact List.nodup_range

/-- Every claim in the current profile receives Permit. -/
def PrefixGreen (compiled : CompiledGovernance) (claims : List ClaimQ) : Prop :=
  ∀ i : Fin claims.length,
    graphDecide compiled.graph claims (claims.get i).id = BinaryDecision.Permit

/-- Computable current-prefix check. -/
def prefixGreenBool (compiled : CompiledGovernance) (claims : List ClaimQ) : Bool :=
  claims.all fun claim =>
    graphDecide compiled.graph claims claim.id == BinaryDecision.Permit

/-- Boolean current-prefix evaluation reflects the propositional predicate. -/
theorem prefixGreenBool_eq_true_iff
    (compiled : CompiledGovernance) (claims : List ClaimQ) :
    prefixGreenBool compiled claims = true ↔ PrefixGreen compiled claims := by
  simp only [prefixGreenBool, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h i
    exact h (claims.get i) (List.get_mem claims i)
  · intro h claim hmem
    obtain ⟨i, rfl⟩ := List.get_of_mem hmem
    exact h i

/-- Every singleton occurrence receives Permit. -/
def allSingletonsPermitBool
    (compiled : CompiledGovernance)
    (events : List NormalizedEventOccurrenceV0) : Bool :=
  (encodedClaims events).all fun claim =>
    graphDecide compiled.graph [claim] claim.id == BinaryDecision.Permit

theorem allSingletonsPermitBool_eq_true_iff
    (compiled : CompiledGovernance)
    (events : List NormalizedEventOccurrenceV0) :
    allSingletonsPermitBool compiled events = true ↔
      ∀ i : Fin (encodedClaims events).length,
        graphDecide compiled.graph [(encodedClaims events).get i]
            ((encodedClaims events).get i).id = BinaryDecision.Permit := by
  simp only [allSingletonsPermitBool, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h i
    exact h ((encodedClaims events).get i)
      (List.get_mem (encodedClaims events) i)
  · intro h claim hmem
    obtain ⟨i, rfl⟩ := List.get_of_mem hmem
    exact h i

/-- All nonempty prefixes observed so far were green. -/
def EveryObservedPrefixGreen
    (compiled : CompiledGovernance)
    (events : List NormalizedEventOccurrenceV0) : Prop :=
  ∀ prefixLength, 0 < prefixLength → prefixLength ≤ events.length →
    PrefixGreen compiled ((encodedClaims events).take prefixLength)

/-- Least denied occurrence in one fixed profile. -/
def firstDeniedOccurrence?
    (compiled : CompiledGovernance) (claims : List ClaimQ) : Option Nat :=
  claims.findIdx? fun claim =>
    graphDecide compiled.graph claims claim.id == BinaryDecision.Deny

structure BadPrefixPosition where
  transitionIndex : Nat
  prefixLength : Nat
  deniedOccurrenceIndex : Nat
  deriving DecidableEq, Repr

/-- Search nonempty prefixes by increasing length, then denied occurrences by index. -/
def firstBadPrefix?
    (compiled : CompiledGovernance)
    (events : List NormalizedEventOccurrenceV0) : Option BadPrefixPosition :=
  let claims := encodedClaims events
  match (List.range events.length).findIdx? fun transitionIndex =>
      !prefixGreenBool compiled (claims.take (transitionIndex + 1)) with
  | none => none
  | some transitionIndex =>
      let prefixLength := transitionIndex + 1
      let deniedOccurrenceIndex :=
        (firstDeniedOccurrence? compiled (claims.take prefixLength)).getD 0
      some { transitionIndex, prefixLength, deniedOccurrenceIndex }

theorem firstDeniedOccurrence_sound
    (compiled : CompiledGovernance) (claims : List ClaimQ) (i : Nat)
    (h : firstDeniedOccurrence? compiled claims = some i) :
    i < claims.length ∧
      ∃ claim, claims[i]? = some claim ∧
        graphDecide compiled.graph claims claim.id = BinaryDecision.Deny := by
  rw [firstDeniedOccurrence?, List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hi, hdeny, _⟩ := h
  refine ⟨hi, claims[i], ?_, by simpa using hdeny⟩
  exact List.getElem?_eq_getElem hi

theorem firstDeniedOccurrence_minimal
    (compiled : CompiledGovernance) (claims : List ClaimQ) (i : Nat)
    (h : firstDeniedOccurrence? compiled claims = some i) :
    ∀ j, j < i → ∃ claim, claims[j]? = some claim ∧
      graphDecide compiled.graph claims claim.id = BinaryDecision.Permit := by
  rw [firstDeniedOccurrence?, List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hi, _, hminimal⟩ := h
  intro j hj
  have hn := hminimal j hj
  simp only [beq_iff_eq] at hn
  refine ⟨claims[j]'(Nat.lt_trans hj hi), List.getElem?_eq_getElem _, ?_⟩
  cases hdecision : graphDecide compiled.graph claims claims[j].id <;> simp_all

theorem firstDeniedOccurrence_none_iff
    (compiled : CompiledGovernance) (claims : List ClaimQ) :
    firstDeniedOccurrence? compiled claims = none ↔ PrefixGreen compiled claims := by
  rw [firstDeniedOccurrence?, List.findIdx?_eq_none_iff]
  constructor
  · intro h i
    have hn := h (claims.get i) (List.get_mem claims i)
    simp only [Bool.eq_false_iff] at hn
    have hnotDeny :
        graphDecide compiled.graph claims (claims.get i).id ≠ BinaryDecision.Deny := by
      simpa using hn
    cases hdecision :
        graphDecide compiled.graph claims (claims.get i).id <;> simp_all
  · intro h claim hmem
    obtain ⟨i, rfl⟩ := List.get_of_mem hmem
    have hp := h i
    simp only [Bool.eq_false_iff]
    intro hdeny
    have hdeny' :
        graphDecide compiled.graph claims (claims.get i).id = BinaryDecision.Deny := by
      simpa using hdeny
    exact BinaryDecision.noConfusion (hp.symm.trans hdeny')

private theorem firstDeniedOccurrence_exists_of_not_green
    (compiled : CompiledGovernance) (claims : List ClaimQ)
    (h : ¬ PrefixGreen compiled claims) :
    ∃ i, firstDeniedOccurrence? compiled claims = some i := by
  cases hs : firstDeniedOccurrence? compiled claims with
  | none => exact False.elim (h ((firstDeniedOccurrence_none_iff compiled claims).1 hs))
  | some i => exact ⟨i, rfl⟩

theorem firstBadPrefix_sound
    (compiled : CompiledGovernance)
    (events : List NormalizedEventOccurrenceV0)
    (position : BadPrefixPosition)
    (h : firstBadPrefix? compiled events = some position) :
    position.prefixLength = position.transitionIndex + 1 ∧
      position.prefixLength ≤ events.length ∧
      position.deniedOccurrenceIndex < position.prefixLength ∧
      ∃ claim,
        ((encodedClaims events).take position.prefixLength)[position.deniedOccurrenceIndex]? =
            some claim ∧
          graphDecide compiled.graph
              ((encodedClaims events).take position.prefixLength) claim.id =
            BinaryDecision.Deny := by
  simp only [firstBadPrefix?] at h
  split at h
  · contradiction
  · rename_i transitionIndex htransition
    simp only [Option.some.injEq] at h
    subst position
    have hfound :=
      (List.findIdx?_eq_some_iff_getElem.mp htransition)
    obtain ⟨hbound, hbad, _⟩ := hfound
    simp only [List.length_range, List.getElem_range] at hbad hbound
    have hnotGreen :
        ¬ PrefixGreen compiled
          ((encodedClaims events).take (transitionIndex + 1)) := by
      rw [← prefixGreenBool_eq_true_iff]
      simpa using hbad
    obtain ⟨denied, hdenied⟩ :=
      firstDeniedOccurrence_exists_of_not_green compiled _ hnotGreen
    have hsound := firstDeniedOccurrence_sound compiled _ denied hdenied
    obtain ⟨hdeniedBound, claim, hclaim, hdecision⟩ := hsound
    have htakeLength :
        ((encodedClaims events).take (transitionIndex + 1)).length =
          transitionIndex + 1 := by
      simp [Nat.succ_le_iff.mpr hbound]
    have hgetD :
        (firstDeniedOccurrence? compiled
          ((encodedClaims events).take (transitionIndex + 1))).getD 0 = denied := by
      simp [hdenied]
    simp only [hgetD]
    refine ⟨True.intro, Nat.succ_le_iff.mpr hbound, ?_, claim, hclaim, hdecision⟩
    simpa [htakeLength] using hdeniedBound

theorem firstBadPrefix_strict_earlier_green
    (compiled : CompiledGovernance)
    (events : List NormalizedEventOccurrenceV0)
    (position : BadPrefixPosition)
    (h : firstBadPrefix? compiled events = some position) :
    ∀ k, k < position.transitionIndex →
      PrefixGreen compiled ((encodedClaims events).take (k + 1)) := by
  simp only [firstBadPrefix?] at h
  split at h
  · contradiction
  · rename_i transitionIndex htransition
    simp only [Option.some.injEq] at h
    subst position
    obtain ⟨hbound, _, hminimal⟩ :=
      List.findIdx?_eq_some_iff_getElem.mp htransition
    intro k hk
    have hnotBad := hminimal k hk
    simp only [List.getElem_range] at hnotBad
    have hgreen :
        prefixGreenBool compiled ((encodedClaims events).take (k + 1)) = true := by
      simpa using hnotBad
    exact (prefixGreenBool_eq_true_iff compiled _).1 hgreen

theorem firstBadPrefix_denied_occurrence_minimal
    (compiled : CompiledGovernance)
    (events : List NormalizedEventOccurrenceV0)
    (position : BadPrefixPosition)
    (h : firstBadPrefix? compiled events = some position) :
    ∀ j, j < position.deniedOccurrenceIndex → ∃ claim,
      ((encodedClaims events).take position.prefixLength)[j]? = some claim ∧
        graphDecide compiled.graph
            ((encodedClaims events).take position.prefixLength) claim.id =
          BinaryDecision.Permit := by
  simp only [firstBadPrefix?] at h
  split at h
  · contradiction
  · rename_i transitionIndex htransition
    simp only [Option.some.injEq] at h
    subst position
    have hfound := List.findIdx?_eq_some_iff_getElem.mp htransition
    obtain ⟨hbound, hbad, _⟩ := hfound
    simp only [List.length_range, List.getElem_range] at hbad hbound
    have hnotGreen :
        ¬ PrefixGreen compiled
          ((encodedClaims events).take (transitionIndex + 1)) := by
      rw [← prefixGreenBool_eq_true_iff]
      simpa using hbad
    obtain ⟨denied, hdenied⟩ :=
      firstDeniedOccurrence_exists_of_not_green compiled _ hnotGreen
    have hgetD :
        (firstDeniedOccurrence? compiled
          ((encodedClaims events).take (transitionIndex + 1))).getD 0 = denied := by
      simp [hdenied]
    simp only [hgetD]
    exact firstDeniedOccurrence_minimal compiled _ denied hdenied

theorem firstBadPrefix_none_iff
    (compiled : CompiledGovernance)
    (events : List NormalizedEventOccurrenceV0) :
    firstBadPrefix? compiled events = none ↔
      EveryObservedPrefixGreen compiled events := by
  simp only [firstBadPrefix?]
  split
  · rename_i hnone
    rw [List.findIdx?_eq_none_iff] at hnone
    constructor
    · intro _ prefixLength hpositive hlength
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
      have h := hnone k (by simp; omega)
      have hgreen :
          prefixGreenBool compiled ((encodedClaims events).take (k + 1)) = true := by
        simpa using h
      exact (prefixGreenBool_eq_true_iff compiled _).1 hgreen
    · intro _
      rfl
  · rename_i transitionIndex hsome
    constructor
    · intro h
      contradiction
    · intro hall
      obtain ⟨hbound, hbad, _⟩ :=
        List.findIdx?_eq_some_iff_getElem.mp hsome
      simp only [List.length_range, List.getElem_range] at hbad hbound
      have hgreen := hall (transitionIndex + 1) (by omega)
        (Nat.succ_le_iff.mpr hbound)
      have hbool := (prefixGreenBool_eq_true_iff compiled _).2 hgreen
      simp [hbool] at hbad

/-- Historical safety on a prefix follows from historical safety on its extension. -/
theorem everyObservedPrefixGreen_prefix_closed
    (compiled : CompiledGovernance)
    {events extension : List NormalizedEventOccurrenceV0}
    (hprefix : events <+: extension)
    (hgreen : EveryObservedPrefixGreen compiled extension) :
    EveryObservedPrefixGreen compiled events := by
  obtain ⟨tail, rfl⟩ := hprefix
  intro prefixLength hpositive hlength
  have hlong := hgreen prefixLength hpositive (by simp; omega)
  rw [encodedClaims, List.mapIdx_append] at hlong
  rw [List.take_append_of_le_length (by simpa using hlength)] at hlong
  exact hlong

/-- Once a historical failure is observed, appending events cannot erase it. -/
theorem everyObservedPrefixGreen_violation_extension_closed
    (compiled : CompiledGovernance)
    (events tail : List NormalizedEventOccurrenceV0)
    (hfailure : ¬ EveryObservedPrefixGreen compiled events) :
    ¬ EveryObservedPrefixGreen compiled (events ++ tail) := by
  intro hgreen
  exact hfailure (everyObservedPrefixGreen_prefix_closed compiled
    (List.prefix_append events tail) hgreen)

private def recoveryClaim (id : Nat) (strength : ℚ) (hstrength : 0 < strength) : ClaimQ :=
  ⟨id, strength, hstrength, []⟩

/-- A currently denied peer-half profile can become green after extension.
This refutes current-prefix denial persistence; it does not affect the
historical all-observed-prefix property. -/
theorem peerHalf_currentPrefix_recovery :
    let before : List ClaimQ :=
      [ recoveryClaim 0 1 (by norm_num)
      , recoveryClaim 1 2 (by norm_num)
      , recoveryClaim 2 3 (by norm_num) ]
    let after := before ++ [recoveryClaim 3 1 (by norm_num)]
    ¬ PrefixGreen peerGraphSacrificedCompiledGovernance before ∧
      PrefixGreen peerGraphSacrificedCompiledGovernance after := by
  dsimp only
  constructor
  · intro h
    have hdenied := h ⟨0, by decide⟩
    have hcomputed :
        graphDecide peerGraphSacrificedCompiledGovernance.graph
            [ recoveryClaim 0 1 (by norm_num)
            , recoveryClaim 1 2 (by norm_num)
            , recoveryClaim 2 3 (by norm_num) ] 0 = BinaryDecision.Deny := by
      native_decide
    exact BinaryDecision.noConfusion (hcomputed.symm.trans hdenied)
  · intro i
    fin_cases i <;> native_decide

end Legitimacy
