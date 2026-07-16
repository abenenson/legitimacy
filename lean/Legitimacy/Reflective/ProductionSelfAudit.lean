/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 OR MIT license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Legitimacy.Reflective.FixedPointSystem
import Legitimacy.Results.GovernanceAdmissibilityAudit.Fixtures

/-!
# Production governance-audit self certification

This module connects the reflective Loeb substrate to the Lean port of the
production governance-admissibility audit graph. The concrete graph is
`compilerAuditGraph`, evaluated by the production-shaped traversal, check
dispatcher, and nonvacuity semantics from
`Legitimacy.Results.GovernanceAdmissibilityAudit`.
-/

set_option autoImplicit false

namespace Legitimacy
namespace Reflective

open ModalLogic.GoedelLoeb
open ModalLogic.GoedelLoeb.ModalFormula

universe u

/-- Modal atoms naming production governance-admissibility audit facts. -/
inductive ProductionAuditAtom where
  | verdictLegitimate
  | checkPassed (check : AuditCheck)
  | traversalConfluent
  | nonvacuityAdmissible
  deriving Repr

instance : Inhabited ProductionAuditAtom where
  default := ProductionAuditAtom.verdictLegitimate

instance : DecidableEq ProductionAuditAtom
  | .verdictLegitimate, .verdictLegitimate => isTrue rfl
  | .verdictLegitimate, .checkPassed _ => isFalse (by intro h; cases h)
  | .verdictLegitimate, .traversalConfluent => isFalse (by intro h; cases h)
  | .verdictLegitimate, .nonvacuityAdmissible => isFalse (by intro h; cases h)
  | .checkPassed _, .verdictLegitimate => isFalse (by intro h; cases h)
  | .checkPassed left, .checkPassed right =>
      match decEq left right with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .checkPassed _, .traversalConfluent => isFalse (by intro h; cases h)
  | .checkPassed _, .nonvacuityAdmissible => isFalse (by intro h; cases h)
  | .traversalConfluent, .verdictLegitimate => isFalse (by intro h; cases h)
  | .traversalConfluent, .checkPassed _ => isFalse (by intro h; cases h)
  | .traversalConfluent, .traversalConfluent => isTrue rfl
  | .traversalConfluent, .nonvacuityAdmissible => isFalse (by intro h; cases h)
  | .nonvacuityAdmissible, .verdictLegitimate => isFalse (by intro h; cases h)
  | .nonvacuityAdmissible, .checkPassed _ => isFalse (by intro h; cases h)
  | .nonvacuityAdmissible, .traversalConfluent => isFalse (by intro h; cases h)
  | .nonvacuityAdmissible, .nonvacuityAdmissible => isTrue rfl

/-- Production semantics for one self-audit atom, evaluated by the audit graph
port rather than by the toy threshold encoding. -/
def ProductionAuditAtom.holds
    (subject : AuditSubject) : ProductionAuditAtom → Prop
  | .verdictLegitimate =>
      governanceAdmissibilityVerdict subject = AuditVerdict.legitimate
  | .checkPassed check =>
      auditCheckStatus subject check = .ok .passed
  | .traversalConfluent =>
      allAuditTraversalsConfluent subject (auditGraphClaims subject) = true
  | .nonvacuityAdmissible =>
      auditGraphNonvacuity subject.evalNode subject.graph
          (auditGraphClaims subject) =
        .ok (.admissible (auditGraphClaims subject).length)

/-- A small modal conjunction fold. The empty conjunction is object-language
truth. -/
def modalAndList {α : Type u} : List (ModalFormula α) → ModalFormula α
  | [] => ModalFormula.top
  | phi :: rest => ModalFormula.and phi (modalAndList rest)

/-- The production self-audit formula: final verdict, every canonical check,
traversal confluence, and the Rust-shaped nonvacuity witness. -/
def productionSelfAuditFormula : ModalFormula ProductionAuditAtom :=
  modalAndList
    (ModalFormula.atom ProductionAuditAtom.verdictLegitimate ::
      (auditCheckOrder.map fun check =>
        ModalFormula.atom (ProductionAuditAtom.checkPassed check)) ++
      [ ModalFormula.atom ProductionAuditAtom.traversalConfluent
      , ModalFormula.atom ProductionAuditAtom.nonvacuityAdmissible
      ])

/-- Modal internal soundness for the production self-audit formula. -/
def productionSelfAuditSoundFormula : ModalFormula ProductionAuditAtom :=
  □ₛ(productionSelfAuditFormula) ⟶ productionSelfAuditFormula

/-- Prop-level production self-audit certificate. This is deliberately separate
from the modal boxed formula. -/
def ProductionSelfAuditCertificateHolds (subject : AuditSubject) : Prop :=
  governanceAdmissibilityVerdict subject = AuditVerdict.legitimate ∧
    (∀ check ∈ auditCheckOrder, auditCheckStatus subject check = .ok .passed) ∧
      allAuditTraversalsConfluent subject (auditGraphClaims subject) = true ∧
        auditGraphNonvacuity subject.evalNode subject.graph
            (auditGraphClaims subject) =
          .ok (.admissible (auditGraphClaims subject).length)

/-- Semantics for the named production self-audit formula. The modal formula is
object-language syntax; this predicate pins the syntax to the production
self-audit formula and evaluates its content through the Prop-level production
audit certificate. -/
def productionFormulaSemantics
    (subject : AuditSubject) (phi : ModalFormula ProductionAuditAtom) : Prop :=
  phi = productionSelfAuditFormula ∧
    ProductionSelfAuditCertificateHolds subject

/-- The concrete production audit graph satisfies the Prop-level certificate. -/
theorem compilerProductionSelfAuditCertificateHolds :
    ProductionSelfAuditCertificateHolds compilerAuditGraph := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · native_decide
  · intro check _hmem
    fin_cases check <;> native_decide
  · native_decide
  · native_decide

/-- The modal atom formula is true under the production audit semantics. -/
theorem compilerProductionSelfAuditFormulaHolds :
    productionFormulaSemantics compilerAuditGraph productionSelfAuditFormula :=
  ⟨rfl, compilerProductionSelfAuditCertificateHolds⟩

/-- Subject-relative semantic certificate used to internalize the production
self-audit soundness box. The witness is the production audit content for the
same subject whose box is being constructed. -/
def productionSelfAuditSemanticCertificate (subject : AuditSubject) : Prop :=
  ProductionSelfAuditCertificateHolds subject ∧
    productionFormulaSemantics subject productionSelfAuditFormula

theorem compilerProductionSelfAuditSemanticCertificate :
    productionSelfAuditSemanticCertificate compilerAuditGraph :=
  ⟨compilerProductionSelfAuditCertificateHolds,
    compilerProductionSelfAuditFormulaHolds⟩

/-- K4 proof predicate indexed by the audited subject and extended only by
that subject's production self-audit internal-soundness certificate. -/
inductive ProductionAuditProvable :
    AuditSubject →
    ModalFormula ProductionAuditAtom → Prop
  | pl_taut {subject : AuditSubject} {phi : ModalFormula ProductionAuditAtom} :
      phi.PropTaut → ProductionAuditProvable subject phi
  | certifiedInternalSoundness {subject : AuditSubject} :
      ProductionSelfAuditCertificateHolds subject →
        productionFormulaSemantics subject productionSelfAuditFormula →
          ProductionAuditProvable subject (□ₛ(productionSelfAuditSoundFormula))
  | ax_K (subject : AuditSubject) (phi psi : ModalFormula ProductionAuditAtom) :
      ProductionAuditProvable subject
        (□ₛ(phi ⟶ psi) ⟶ (□ₛphi ⟶ □ₛpsi))
  | ax_four (subject : AuditSubject) (phi : ModalFormula ProductionAuditAtom) :
      ProductionAuditProvable subject (□ₛphi ⟶ □ₛ□ₛphi)
  | mp {subject : AuditSubject} {phi psi : ModalFormula ProductionAuditAtom} :
      ProductionAuditProvable subject (phi ⟶ psi) →
        ProductionAuditProvable subject phi → ProductionAuditProvable subject psi
  | nec {subject : AuditSubject} {phi : ModalFormula ProductionAuditAtom} :
      ProductionAuditProvable subject phi →
        ProductionAuditProvable subject (□ₛphi)

namespace ProductionAuditProvable

theorem ofProvable {phi : ModalFormula ProductionAuditAtom}
    {subject : AuditSubject} (h : Provable phi) :
    ProductionAuditProvable subject phi := by
  induction h with
  | pl_taut htaut => exact pl_taut htaut
  | ax_K phi psi => exact ax_K subject phi psi
  | ax_four phi => exact ax_four subject phi
  | mp _ _ ihImp ihPhi => exact mp ihImp ihPhi
  | nec _ ih => exact nec ih

lemma of_prop_taut {phi : ModalFormula ProductionAuditAtom}
    {subject : AuditSubject} (h : phi.PropTaut) :
    ProductionAuditProvable subject phi :=
  pl_taut h

lemma k (subject : AuditSubject) (phi psi : ModalFormula ProductionAuditAtom) :
    ProductionAuditProvable subject
      (□ₛ(phi ⟶ psi) ⟶ (□ₛphi ⟶ □ₛpsi)) :=
  ax_K subject phi psi

lemma four (subject : AuditSubject) (phi : ModalFormula ProductionAuditAtom) :
    ProductionAuditProvable subject (□ₛphi ⟶ □ₛ□ₛphi) :=
  ax_four subject phi

lemma imp_refl (phi : ModalFormula ProductionAuditAtom) :
    {subject : AuditSubject} → ProductionAuditProvable subject (phi ⟶ phi) :=
  fun {subject} => ofProvable (subject := subject) (Provable.imp_refl phi)

lemma iff_left {phi psi : ModalFormula ProductionAuditAtom}
    {subject : AuditSubject}
    (h : ProductionAuditProvable subject (phi ⟷ psi)) :
    ProductionAuditProvable subject (phi ⟶ psi) :=
  mp (ofProvable (subject := subject) (Provable.of_prop_taut (by
    intro val hIff
    exact hIff.mp))) h

lemma iff_right {phi psi : ModalFormula ProductionAuditAtom}
    {subject : AuditSubject}
    (h : ProductionAuditProvable subject (phi ⟷ psi)) :
    ProductionAuditProvable subject (psi ⟶ phi) :=
  mp (ofProvable (subject := subject) (Provable.of_prop_taut (by
    intro val hIff
    exact hIff.mpr))) h

lemma iff_intro {phi psi : ModalFormula ProductionAuditAtom}
    {subject : AuditSubject}
    (hLeft : ProductionAuditProvable subject (phi ⟶ psi))
    (hRight : ProductionAuditProvable subject (psi ⟶ phi)) :
    ProductionAuditProvable subject (phi ⟷ psi) := by
  refine mp (mp (of_prop_taut ?_) hLeft) hRight
  intro val hpq hqp
  exact Iff.intro hpq hqp

lemma imp_trans {phi psi chi : ModalFormula ProductionAuditAtom}
    {subject : AuditSubject}
    (hPhiPsi : ProductionAuditProvable subject (phi ⟶ psi))
    (hPsiChi : ProductionAuditProvable subject (psi ⟶ chi)) :
    ProductionAuditProvable subject (phi ⟶ chi) := by
  refine mp (mp (of_prop_taut ?_) hPhiPsi) hPsiChi
  intro val hpq hqr hp
  exact hqr (hpq hp)

lemma imp_box_combine
    {alpha beta gamma delta : ModalFormula ProductionAuditAtom}
    {subject : AuditSubject}
    (hAlphaBeta : ProductionAuditProvable subject (alpha ⟶ beta))
    (hAlphaGamma : ProductionAuditProvable subject (alpha ⟶ gamma))
    (hBetaGammaDelta :
      ProductionAuditProvable subject (beta ⟶ (gamma ⟶ delta))) :
    ProductionAuditProvable subject (alpha ⟶ delta) := by
  refine mp (mp (mp (of_prop_taut ?_) hAlphaBeta) hAlphaGamma) hBetaGammaDelta
  intro val hab hac hbgd ha
  exact hbgd (hab ha) (hac ha)

lemma imp_congr
    {alpha beta gamma delta : ModalFormula ProductionAuditAtom}
    {subject : AuditSubject}
    (hAlphaBeta : ProductionAuditProvable subject (alpha ⟷ beta))
    (hGammaDelta : ProductionAuditProvable subject (gamma ⟷ delta)) :
    ProductionAuditProvable subject ((alpha ⟶ gamma) ⟷ (beta ⟶ delta)) := by
  refine mp (mp (of_prop_taut ?_) hAlphaBeta) hGammaDelta
  intro val hab hgd
  constructor
  · intro hag hb
    exact hgd.mp (hag (hab.mpr hb))
  · intro hbd ha
    exact hgd.mpr (hbd (hab.mp ha))

/-- Loeb for the production-audit proof predicate. The proof mirrors the
upstream modal-axiomatic K4/diagonal derivation, with the concrete production
certificate available only through `certifiedInternalSoundness`. -/
theorem loeb {phi : ModalFormula ProductionAuditAtom}
    {subject : AuditSubject}
    (h : ProductionAuditProvable subject (□ₛphi ⟶ phi)) :
    ProductionAuditProvable subject phi := by
  classical
  letI : DecidableEq ProductionAuditAtom := inferInstance
  letI : Diagonalisable ProductionAuditAtom := inferInstance
  let psi :=
    @Diagonalisable.fixedpoint ProductionAuditAtom inferInstance inferInstance phi
  let hStructuralEvidence :=
    @Diagonalisable.structural ProductionAuditAtom inferInstance inferInstance
  have hStructural :
      ProductionAuditProvable subject
        (psi ⟷ (□ₛ(ModalLogic.GoedelLoeb.Substitution.code
              (hStructuralEvidence.template phi)) ⟶ phi)) := by
    dsimp [psi, hStructuralEvidence]
    exact ofProvable (subject := subject)
      (Provable.of_prop_taut
        (ModalFormula.fixedpoint_structural_prop_taut
          Diagonalisable.fixedpoint
          Diagonalisable.distinguishedAtom phi Diagonalisable.structural))
  have hCodeTemplate :
      ProductionAuditProvable subject
        (□ₛ(ModalLogic.GoedelLoeb.Substitution.code
              (hStructuralEvidence.template phi)) ⟷ □ₛpsi) := by
    dsimp [psi, hStructuralEvidence]
    exact ofProvable (subject := subject)
      (Provable.of_prop_taut
        (Diagonalisable.structural.box_code_fixedpoint phi))
  have hImpBridge :
      ProductionAuditProvable subject
        (((□ₛ(ModalLogic.GoedelLoeb.Substitution.code
              (hStructuralEvidence.template phi))) ⟶ phi) ⟷
          (□ₛpsi ⟶ phi)) :=
    imp_congr hCodeTemplate
      (iff_intro (imp_refl phi) (imp_refl phi))
  have hForward :
      ProductionAuditProvable subject (psi ⟶ (□ₛpsi ⟶ phi)) :=
    imp_trans (iff_left hStructural) (iff_left hImpBridge)
  have hBackward :
      ProductionAuditProvable subject ((□ₛpsi ⟶ phi) ⟶ psi) :=
    imp_trans (iff_right hImpBridge) (iff_right hStructural)
  have hDiag :
      ProductionAuditProvable subject (psi ⟷ (□ₛpsi ⟶ phi)) :=
    iff_intro hForward hBackward
  have hUnfold :
      ProductionAuditProvable subject (psi ⟶ (□ₛpsi ⟶ phi)) :=
    iff_left hDiag
  have hBoxUnfold :
      ProductionAuditProvable subject (□ₛ(psi ⟶ (□ₛpsi ⟶ phi))) :=
    nec hUnfold
  have hD2Unfold :
      ProductionAuditProvable subject
        (□ₛ(psi ⟶ (□ₛpsi ⟶ phi)) ⟶
          (□ₛpsi ⟶ □ₛ(□ₛpsi ⟶ phi))) :=
    k subject psi (□ₛpsi ⟶ phi)
  have hBoxImp :
      ProductionAuditProvable subject (□ₛpsi ⟶ □ₛ(□ₛpsi ⟶ phi)) :=
    mp hD2Unfold hBoxUnfold
  have hD2Target :
      ProductionAuditProvable subject
        (□ₛ(□ₛpsi ⟶ phi) ⟶ (□ₛ□ₛpsi ⟶ □ₛphi)) :=
    k subject (□ₛpsi) phi
  have hD3Psi : ProductionAuditProvable subject (□ₛpsi ⟶ □ₛ□ₛpsi) :=
    four subject psi
  have hBoxToBoxTarget :
      ProductionAuditProvable subject (□ₛpsi ⟶ □ₛphi) :=
    imp_box_combine hBoxImp hD3Psi hD2Target
  have hBoxToTarget : ProductionAuditProvable subject (□ₛpsi ⟶ phi) :=
    imp_trans hBoxToBoxTarget h
  have hFold : ProductionAuditProvable subject ((□ₛpsi ⟶ phi) ⟶ psi) :=
    iff_right hDiag
  have hPsi : ProductionAuditProvable subject psi :=
    mp hFold hBoxToTarget
  have hBoxPsi : ProductionAuditProvable subject (□ₛpsi) :=
    nec hPsi
  exact mp hBoxToTarget hBoxPsi

/-- Empty-frame soundness guard for the local proof predicate. -/
theorem emptyEval_sound {phi : ModalFormula ProductionAuditAtom}
    {subject : AuditSubject}
    (h : ProductionAuditProvable subject phi) :
    ModalFormula.emptyEval phi := by
  induction h with
  | pl_taut htaut =>
      exact (ModalFormula.propEval_emptyEval _).mp (htaut ModalFormula.emptyEval)
  | certifiedInternalSoundness _hcert _hsem =>
      simp [ModalFormula.emptyEval]
  | ax_K phi psi =>
      simp [ModalFormula.emptyEval]
  | ax_four phi =>
      simp [ModalFormula.emptyEval]
  | mp _ _ ihImp ihPhi =>
      exact ihImp ihPhi
  | nec _ih =>
      simp [ModalFormula.emptyEval]

theorem not_bot :
    {subject : AuditSubject} →
      ¬ ProductionAuditProvable subject
        (⊥ₛ : ModalFormula ProductionAuditAtom) := by
  intro subject h
  exact emptyEval_sound h

end ProductionAuditProvable

/-- Subject-relative raw modal box over the local proof predicate. -/
def productionReflectiveProvable
    (subject : AuditSubject) (phi : ModalFormula ProductionAuditAtom) : Prop :=
  ProductionAuditProvable subject (□ₛphi)

/-- Production reflective box. This is the exported box predicate: the modal
`□phi` proof and the semantic audit certificate must refer to the same audited
subject, so a failing subject cannot obtain the box by inhabiting an unrelated
certificate type. -/
def productionReflectiveBox
    (subject : AuditSubject) (phi : ModalFormula ProductionAuditAtom) : Prop :=
  productionReflectiveProvable subject phi ∧
    productionFormulaSemantics subject phi

/-- The concrete production evaluator constructs the boxed internal-soundness
premise; callers do not supply `hinternal`. -/
theorem compilerProductionSelfAuditInternalSoundnessBox :
    ProductionAuditProvable compilerAuditGraph
      (□ₛ(productionSelfAuditSoundFormula)) :=
  ProductionAuditProvable.certifiedInternalSoundness
    compilerProductionSelfAuditCertificateHolds
    compilerProductionSelfAuditFormulaHolds

/-- Subject-relative Loeb construction: a subject's concrete production
certificate is consumed to build its boxed self-audit formula. -/
theorem production_self_audit_boxed_by_loeb
    (subject : AuditSubject)
    (hcert : ProductionSelfAuditCertificateHolds subject) :
    productionReflectiveBox subject productionSelfAuditFormula := by
  let auditPhi := productionSelfAuditFormula
  have hsem : productionFormulaSemantics subject productionSelfAuditFormula :=
    ⟨rfl, hcert⟩
  have hBoxedInternal :
      ProductionAuditProvable subject (□ₛ(□ₛauditPhi ⟶ auditPhi)) := by
    simpa [productionSelfAuditSoundFormula, auditPhi]
      using ProductionAuditProvable.certifiedInternalSoundness hcert hsem
  have hK :
      ProductionAuditProvable subject
        (□ₛ(□ₛauditPhi ⟶ auditPhi) ⟶
          (□ₛ(□ₛauditPhi) ⟶ □ₛauditPhi)) :=
    ProductionAuditProvable.k subject (□ₛauditPhi) auditPhi
  have hBoxBoxToBox :
      ProductionAuditProvable subject (□ₛ(□ₛauditPhi) ⟶ □ₛauditPhi) :=
    ProductionAuditProvable.mp hK hBoxedInternal
  have hLoebBox : ProductionAuditProvable subject (□ₛauditPhi) :=
    ProductionAuditProvable.loeb hBoxBoxToBox
  exact ⟨by simpa [productionReflectiveProvable, auditPhi] using hLoebBox, hsem⟩

/-- Concrete positive box for the production compiler audit fixture. -/
theorem compiler_production_self_audit_boxed_by_loeb :
    productionReflectiveBox compilerAuditGraph productionSelfAuditFormula :=
  production_self_audit_boxed_by_loeb compilerAuditGraph
    compilerProductionSelfAuditCertificateHolds

/-- The exported production box is discriminating: at the self-audit formula it
exists exactly for subjects whose production certificate is true. -/
theorem production_self_audit_box_iff_certificate
    (subject : AuditSubject) :
    productionReflectiveBox subject productionSelfAuditFormula ↔
      ProductionSelfAuditCertificateHolds subject := by
  constructor
  · intro hbox
    exact hbox.2.2
  · intro hcert
    exact production_self_audit_boxed_by_loeb subject hcert

/-- The subject-relative box carries the production verdict. The conclusion is
extracted from `hbox`'s subject-matched semantic certificate. -/
theorem production_self_audit_box_implies_verdict
    (subject : AuditSubject)
    (hbox : productionReflectiveBox subject productionSelfAuditFormula) :
    governanceAdmissibilityVerdict subject = AuditVerdict.legitimate :=
  hbox.2.2.1

/-- Concrete self-audit certificate, with the modal box supplied by Loeb and
the semantic side supplied by the production evaluator. -/
theorem production_self_audit_certificate_holds_nonvacuously :
    productionReflectiveBox compilerAuditGraph productionSelfAuditFormula ∧
      ProductionSelfAuditCertificateHolds compilerAuditGraph ∧
        productionFormulaSemantics compilerAuditGraph productionSelfAuditFormula :=
  ⟨compiler_production_self_audit_boxed_by_loeb,
    compilerProductionSelfAuditCertificateHolds,
    compilerProductionSelfAuditFormulaHolds⟩

/-- Parametric iff form: for any subject, a Loeb-certified production
self-audit box entails the verdict through its semantic certificate, while a
true certificate builds the subject-relative box. -/
theorem production_kernel_self_audit_iff_loeb_certified :
    ∀ subject : AuditSubject,
      ProductionSelfAuditCertificateHolds subject →
        (governanceAdmissibilityVerdict subject = AuditVerdict.legitimate ↔
          productionReflectiveBox subject productionSelfAuditFormula) := by
  intro subject hcert
  constructor
  · intro _hverdict
    exact production_self_audit_boxed_by_loeb subject hcert
  · intro hbox
    exact production_self_audit_box_implies_verdict subject hbox

/-- The cyclic production-shaped fixture does not satisfy the self-audit
certificate, so the certificate predicate is not identically true. -/
theorem cyclicSkippedAuditGraph_self_audit_certificate_fails :
    ¬ ProductionSelfAuditCertificateHolds cyclicSkippedAuditGraph := by
  intro hcert
  have hundischarged :
      governanceAdmissibilityVerdict cyclicSkippedAuditGraph =
        AuditVerdict.undischarged AuditCheck.consistency :=
    cyclicSkippedAuditGraph_undischarged
  rw [hcert.1] at hundischarged
  cases hundischarged

/-- Prop-level failure of the modal formula semantics on the cyclic fixture. -/
theorem cyclicSkippedAuditGraph_self_audit_formula_fails :
    ¬ productionFormulaSemantics cyclicSkippedAuditGraph productionSelfAuditFormula := by
  intro hformula
  exact cyclicSkippedAuditGraph_self_audit_certificate_fails hformula.2

/-- Box-side failure companion: the cyclic skipped-check fixture cannot obtain
the subject-relative Loeb-certified production self-audit box. -/
theorem cyclicSkippedAuditGraph_self_audit_box_fails :
    ¬ productionReflectiveBox cyclicSkippedAuditGraph productionSelfAuditFormula := by
  intro hbox
  exact cyclicSkippedAuditGraph_self_audit_certificate_fails hbox.2.2

end Reflective
end Legitimacy
