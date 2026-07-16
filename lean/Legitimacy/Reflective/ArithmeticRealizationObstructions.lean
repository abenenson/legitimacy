/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Legitimacy.Reflective.ArithmeticRealizationPrerequisites

/-!
# Arithmetic-realization obstructions

This module records first-order realization interfaces and obstruction
theorems for the depth-2 boxed internal-soundness premise.

## Main result

* `no_depth2Core_arithmeticSoundnessRealization`: a first-order-language
  arithmetic realization package whose represented soundness sentence reflects
  into the unboxed godel-loeb `Provable` target is impossible.
* `depth2Core_latticeAuditSoundFormula_not_provable`: the current modal
  substrate cannot prove the unboxed depth-2 internal-soundness sentence.
-/

set_option autoImplicit false

namespace Legitimacy
namespace Reflective
namespace ReflectiveGovernanceFixedPointSystem

open ModalLogic.GoedelLoeb
open ModalLogic.GoedelLoeb.ModalFormula
open FirstOrder

universe u

/--
First-order sentence-level interpretations of the modal connectives not fixed
by the atom interpretation.

Mathlib's pinned model-theory layer supplies first-order syntax and theories,
but not a PA proof predicate or a canonical arithmetized provability operator.
Those missing arithmetic choices are therefore explicit data rather than hidden
inside a generic source proposition.
-/
structure ArithmeticModalConnectives (L : FirstOrder.Language) where
  /-- Arithmetic sentence used for modal falsity. -/
  falsum : L.Sentence
  /-- Arithmetic sentence former used for modal implication. -/
  implication : L.Sentence → L.Sentence → L.Sentence
  /-- Arithmetic sentence former used for modal biconditional. -/
  biconditional : L.Sentence → L.Sentence → L.Sentence
  /-- Arithmetic sentence former used for modal necessity. -/
  necessity : L.Sentence → L.Sentence
  /-- Arithmetic sentence former used for quoted modal syntax. -/
  quote : L.Sentence → L.Sentence
  /-- Arithmetic sentence former used for the Kreisel fixed-point primitive. -/
  kreiselFixed : L.Sentence → L.Sentence

/--
Interpret a modal policy formula as a first-order sentence, once an
atom-to-sentence map and the arithmetic readings of modal connectives have
been supplied.
-/
def arithmeticInterpretModalFormula {L : FirstOrder.Language}
    (atomInterpretation : PolicyAtom Depth2State → L.Sentence)
    (connectives : ArithmeticModalConnectives L) :
    ModalFormula (PolicyAtom Depth2State) → L.Sentence
  | @ModalFormula.atom _ policyAtom => atomInterpretation policyAtom
  | @ModalFormula.bot _ => connectives.falsum
  | @ModalFormula.impl _ phi psi =>
      connectives.implication
        (arithmeticInterpretModalFormula atomInterpretation connectives phi)
        (arithmeticInterpretModalFormula atomInterpretation connectives psi)
  | @ModalFormula.iff _ phi psi =>
      connectives.biconditional
        (arithmeticInterpretModalFormula atomInterpretation connectives phi)
        (arithmeticInterpretModalFormula atomInterpretation connectives psi)
  | @ModalFormula.box _ phi =>
      connectives.necessity
        (arithmeticInterpretModalFormula atomInterpretation connectives phi)
  | @ModalFormula.quote _ phi =>
      connectives.quote
        (arithmeticInterpretModalFormula atomInterpretation connectives phi)
  | @ModalFormula.kreiselFixed _ phi =>
      connectives.kreiselFixed
        (arithmeticInterpretModalFormula atomInterpretation connectives phi)

/--
A genuinely first-order arithmetic realization package for the concrete
depth-2 unboxed soundness sentence.

The `arithmeticDerivation` field is the strongest proof-theoretic analogue
available in the pinned Mathlib model-theory API: theories are sets of
sentences, so deriving the represented sentence from the source theory is
recorded as membership in that theory. The package also carries the missing
atom-to-sentence interpretation that earlier audits identified as a necessary
precondition before any Σ₁-completeness question can even be posed.
-/
structure Depth2ArithmeticSoundnessRealization where
  /-- First-order language supplying the arithmetic source syntax. -/
  language : FirstOrder.Language
  /-- Source arithmetic theory over the chosen language. -/
  arithmeticTheory : language.Theory
  /-- Interpretation of each depth-2 policy atom as an arithmetic sentence. -/
  atomInterpretation : PolicyAtom Depth2State → language.Sentence
  /-- Interpretation of the non-atomic modal constructors as arithmetic syntax. -/
  modalConnectives : ArithmeticModalConnectives language
  /-- Arithmetic sentence claimed to represent the depth-2 audit soundness formula. -/
  arithmeticSoundnessSentence : language.Sentence
  /-- The arithmetic sentence is the interpretation of the concrete modal target. -/
  representsDepth2Soundness :
    arithmeticInterpretModalFormula atomInterpretation modalConnectives
      (depth2LatticeAuditSoundFormulaAt depth2Core) = arithmeticSoundnessSentence
  /-- The represented soundness sentence is available from the source theory. -/
  arithmeticDerivation : arithmeticSoundnessSentence ∈ arithmeticTheory
  /--
  Reflection from the represented first-order derivation back into the current
  modal proof predicate for the unboxed depth-2 soundness sentence.
  -/
  reflectsArithmeticDerivation :
    arithmeticInterpretModalFormula atomInterpretation modalConnectives
        (depth2LatticeAuditSoundFormulaAt depth2Core) = arithmeticSoundnessSentence →
      arithmeticSoundnessSentence ∈ arithmeticTheory →
        Provable (depth2LatticeAuditSoundFormulaAt depth2Core)

/--
Presburger is a concrete arithmetic source language available in the pinned
Mathlib dependency. This alias keeps the realization interface grounded in an
actual first-order arithmetic syntax rather than an unconstrained proposition.
-/
abbrev PresburgerDepth2ArithmeticTheory : Type :=
  FirstOrder.Language.presburger.Theory

/--
Ring-language arithmetic is also available in the pinned Mathlib dependency.
It supplies multiplication syntax, unlike Presburger arithmetic, but still no
canonical PA derivability predicate in this repository's current dependency
surface.
-/
abbrev RingDepth2ArithmeticTheory : Type :=
  FirstOrder.Language.ring.Theory

/-- The concrete depth-2 lattice audit formula is false in godel-loeb's
empty-frame soundness semantics. -/
theorem depth2Core_latticeAuditFormula_emptyEval_false :
    ¬ ModalFormula.emptyEval (depth2LatticeAuditFormulaAt depth2Core) := by
  change ¬ ModalFormula.emptyEval (encodeAuditCertifiesLattice depth2Core)
  simp [encodeAuditCertifiesLattice, encodeAuditCertifiesLatticeSupport,
    List.finRange, depth2Core, encodeAuditCertifies, ModalFormula.and,
    ModalFormula.neg, ModalFormula.emptyEval]

/-- The concrete unboxed depth-2 internal-soundness sentence is false in
godel-loeb's empty-frame soundness semantics. -/
theorem depth2Core_latticeAuditSoundFormula_emptyEval_false :
    ¬ ModalFormula.emptyEval (depth2LatticeAuditSoundFormulaAt depth2Core) := by
  intro hsound
  exact depth2Core_latticeAuditFormula_emptyEval_false (hsound trivial)

/--
The current modal substrate cannot prove the unboxed depth-2 audit formula.

This is an intrinsic proof-predicate obstruction, not a Kripke-frame
countermodel: `Provable.sound_empty` is a theorem about the constructors of
godel-loeb's canonical `Provable` predicate.
-/
theorem depth2Core_latticeAuditFormula_not_provable :
    ¬ Provable (depth2LatticeAuditFormulaAt depth2Core) := by
  intro hprov
  exact depth2Core_latticeAuditFormula_emptyEval_false
    (Provable.sound_empty hprov)

/--
The current modal substrate cannot prove the unboxed depth-2 internal-soundness
sentence.

Consequently the usual arithmetic-realization plan
`arithmetized proof -> Provable (□A -> A) -> Provable □(□A -> A)` cannot be the
positive discharge route for `depth2Core`.
-/
theorem depth2Core_latticeAuditSoundFormula_not_provable :
    ¬ Provable (depth2LatticeAuditSoundFormulaAt depth2Core) := by
  intro hprov
  exact depth2Core_latticeAuditSoundFormula_emptyEval_false
    (Provable.sound_empty hprov)

/--
No necessitation-shaped arithmetic realization can discharge the depth-2
boxed internal-soundness premise in the current modal substrate.

This rules out the strongest standard local bridge available in the present
Mathlib + godel-loeb scope: a concrete arithmetic proof reflected into
`Provable (□A -> A)` and then boxed by `Provable.nec`.
-/
theorem no_depth2Core_arithmeticSoundnessRealization :
    IsEmpty Depth2ArithmeticSoundnessRealization := by
  constructor
  intro R
  exact depth2Core_latticeAuditSoundFormula_not_provable
    (R.reflectsArithmeticDerivation R.representsDepth2Soundness R.arithmeticDerivation)

/--
If a first-order arithmetic soundness realization did exist, necessitation
would produce the requested `hinternal` premise. The previous theorem proves
that this bridge class is empty for the concrete depth-2 core.
-/
theorem depth2Core_hinternal_of_arithmeticSoundnessRealization
    (R : Depth2ArithmeticSoundnessRealization) :
    reflectiveBox (depth2LatticeAuditSoundFormulaAt depth2Core) := by
  exact Provable.nec
    (R.reflectsArithmeticDerivation R.representsDepth2Soundness R.arithmeticDerivation)

/-- Empty-frame soundness cannot refute any boxed formula: every box is true in
`ModalFormula.emptyEval`. -/
theorem emptyEval_box (phi : ModalFormula (PolicyAtom Depth2State)) :
    ModalFormula.emptyEval (□ₛphi) := by
  trivial

/--
The concrete boxed target is true in the empty-frame model, so
`Provable.sound_empty` cannot be used to refute the current `reflectiveBox`
target.
-/
theorem depth2Core_latticeAuditSoundFormula_box_emptyEval :
    ModalFormula.emptyEval (□ₛ(depth2LatticeAuditSoundFormulaAt depth2Core)) :=
  emptyEval_box (depth2LatticeAuditSoundFormulaAt depth2Core)

end ReflectiveGovernanceFixedPointSystem
end Reflective
end Legitimacy
