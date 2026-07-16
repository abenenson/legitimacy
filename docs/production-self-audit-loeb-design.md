# Production Self-Audit Loeb Design

## Target

This dispatch connects the reflective Loeb substrate to the Lean port of the
production governance-admissibility audit graph, not to the old
`Results/SelfAudit.lean` toy threshold graph.

The concrete subject is `compilerAuditGraph` from
`Legitimacy.Results.GovernanceAdmissibilityAudit.Fixtures`. That fixture is the
manual Lean representation of the production compiler audit surface and is
evaluated by the production-shaped audit semantics:

- `syntheticClaimsForNodes` / `auditGraphClaims`
- acyclic traversal and cycle detection
- check dispatch through `auditCheckStatus`
- Rust-shaped nonvacuity through `auditGraphNonvacuity`
- final verdict through `governanceAdmissibilityVerdict`

## Obligation

The Prop-level self-audit obligation for a subject is
`ProductionSelfAuditCertificateHolds subject`. It requires:

1. the governance-admissibility verdict is `AuditVerdict.legitimate`;
2. every check in the canonical `auditCheckOrder` passes;
3. the traversal-confluence check over the production claim corpus succeeds;
4. the Rust-shaped nonvacuity port returns an admissible witness.

The modal target is `productionSelfAuditFormula`, a conjunction of atoms for
the production verdict, each canonical check pass, traversal confluence, and
the nonvacuity witness. Its theorem-facing semantic interpretation is
subject-relative: `productionFormulaSemantics subject
productionSelfAuditFormula` requires the exact modal syntax and evaluates its
content through `ProductionSelfAuditCertificateHolds subject`, whose fields call
the actual production audit functions.

The internal soundness formula is
`productionSelfAuditSoundFormula = □ productionSelfAuditFormula ⟶ productionSelfAuditFormula`.
This is materially different from the Prop-level certificate: it is a modal
soundness obligation for the production audit formula, while the certificate is
a concrete evaluation fact over the production audit graph.

## Constructing The Box

The existing global `Provable` substrate cannot construct boxed internal
soundness for a non-tautological production atom from a Lean computation. It
only has K4, necessitation, propositional tautologies, and Loeb. To avoid
leaving `hinternal` abstract, the implementation defines a local normal modal
proof predicate for the production self-audit graph:

`ProductionAuditProvable subject`.

It has the ordinary K4 rules and one additional rule:

`certifiedInternalSoundness :
  ProductionSelfAuditCertificateHolds subject ->
  productionFormulaSemantics subject productionSelfAuditFormula ->
  ProductionAuditProvable subject (□ productionSelfAuditSoundFormula)`.

The premise is no longer a subject-independent field supplied by callers. It
must be the certificate and semantic interpretation for the same subject whose
box is being constructed. The concrete compiler fixture supplies the named
theorem `compilerProductionSelfAuditSemanticCertificate`, proved by evaluating
the production audit graph, all checks, traversal confluence, and nonvacuity.
Consistency of this local proof predicate is guarded by an empty-frame soundness
theorem: the extra boxed axiom is valid in the empty modal frame, and `⊥` is
not.

Loeb is then derived for `ProductionAuditProvable` by the same K4/diagonal
argument used by the upstream `godel-loeb` substrate. The concrete theorem
`production_self_audit_boxed_by_loeb` consumes a subject's actual certificate,
constructs the boxed internal-soundness premise for that subject, and returns
`productionReflectiveBox subject productionSelfAuditFormula`.

## Certificate Gates

The concrete positive witness is `compilerProductionSelfAuditCertificateHolds`.
It proves the production audit graph satisfies the Prop-level certificate. The
nonvacuity component is not Boolean-only: it records the exact admissible
`auditGraphNonvacuity` verdict at the Prop level.

The exported certificate is discriminating, and the box is equivalent because
it bundles that certificate:
`production_self_audit_box_iff_certificate` proves
`productionReflectiveBox subject productionSelfAuditFormula` exactly when
`ProductionSelfAuditCertificateHolds subject`. The theorem
`production_self_audit_box_implies_verdict` extracts the legitimate verdict from
the supplied `hbox`'s semantic certificate, not from the modal proof conjunct
and not from the concrete compiler fixture.

The failing configuration is `cyclicSkippedAuditGraph`. The theorem
`cyclicSkippedAuditGraph_self_audit_certificate_fails` proves the Prop-level
self-audit certificate fails because the production verdict is
`AuditVerdict.undischarged AuditCheck.consistency`, not legitimate. This shows
the certificate predicate is not identically true. The box-side companion
`cyclicSkippedAuditGraph_self_audit_box_fails` proves the same failing fixture
cannot obtain the subject-relative production box because the bundled semantic
certificate fails.

## Non-Circularity

The modal formula names production audit facts and its semantics are evaluated
through the production audit graph. The boxed internal-soundness rule is
available only after the concrete production evaluator has established the
semantic certificate.

The honest characterization is that the production self-audit box is a faithful
Loeb-constructed re-presentation of the `native_decide` audit certificate. The
discriminating content of the exported results is the certificate established by
the production evaluator: the iff, verdict implication, and cyclic-failure
theorems all read the bundled semantic certificate. The modal/Löb conjunct is
non-vacuous because it is truth-gated through `certifiedInternalSoundness`, but
no exported result consumes that conjunct to strengthen the certificate's
content. The reflective layer does not earn the verdict; it reflects the
already-evaluated certificate in a subject-relative modal box.
