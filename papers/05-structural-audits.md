# Structural Audits of AI Safety Mechanisms

*Adam Benenson, 2026*

## 1. Introduction: Structural Audit Methodology

This paper presents five structural audits over typed representations, together with the structural self-modification results they motivate. §2 examines five AI Control protocol fixtures and shows why polarity-aware monotonicity reverses the legacy diagnostic. §3 applies the same distinction to a synthetic sleeper-agent fixture. §4 and §5 connect the audit framework to Constitutional AI and to decomposition attacks. §6 follows the complete detect-price-repair sequence on the extracted Codex graph model, and §7 states the self-modification escape boundary and lifecycle results. Each case begins only after a protocol or harness has been represented as a typed audit subject; none establishes behavioral claims about the underlying live system.

Read together, these chapters describe structural audits as a program: model the rule layer explicitly, state the trusted representation boundary, evaluate the typed diagnostics, and preserve the certificate surface that downstream reviewers can re-run.

## 2. AI Control Case Study and Verdict

### Structural Audit of AI Control Protocols: Legacy Monotonicity Flags All Five, Polarity-Aware Monotonicity Clears Them

---

#### Abstract

We represent each of the five AI Control protocols from Greenblatt-Shlegeris (arXiv:2312.06942) and Korbak et al. (arXiv:2501.17315), Upfront Auditing, Trusted Monitoring, Trusted Monitoring with Defer-to-Trusted, Untrusted Monitoring, and Trusted Editing, as typed `AuditGovernanceGraph` fixtures and run the repository's structural audit on each. The legacy positive-delta monotonicity diagnostic flags all five: increasing the encoded suspicion or audit-window field flips the audited verdict from `Permit` to `Deny`. The current schema-derived polarity diagnostic then overturns that flag: those fields are lower-better adverse/routing-risk metrics, so claimant-positive improvement is a decrease, and all five fixtures receive `AuditVerdict.legitimate` (the typed verdict-tag returned when every ordered check passes, not a substantive legitimacy property of the AI Control protocol) under `governanceAdmissibilityVerdict`. The result corrects the rule-layer reading rather than refuting AI Control's empirical safety case: the old uniform flag is a polarity artifact, while the canonical structural audit clears the five represented fixtures. We discuss what the structural audit can and cannot tell us about empirical AI Control safety, why polarity matters for monotonicity, and how the corrected result should be read by the Redwood / Anthropic alignment-science / METR audiences.

---

#### 1. Introduction

##### 1.1 The lead

Buck Shlegeris and the Redwood AI Control program publish a sequence of practical control protocols for deploying untrusted AI agents. The protocols, Upfront Auditing, Trusted Monitoring, Trusted Monitoring with Defer-to-Trusted, Untrusted Monitoring, and Trusted Editing, define behavioral *channels* through which an untrusted model's outputs flow before reaching the world. Each protocol has empirical safety properties: bounds on the rate at which an adversarial untrusted model can subvert the protocol against a measured baseline.

The behavioral channel is not the only object the protocols define. Each protocol also induces a *governance graph*: a typed object in which the protocol's nodes are decision sites (the trusted monitor's evaluation, the deferral logic, the editing operation, the audit) and its edges are the structural authority relationships between them. The audit on the *graph* is independent of the audit on the *behavioral channel*. The empirical safety case lives at the channel layer; the structural audit lives at the rule layer.

We run the 9-element structural audit (consistency, solidarity, monotonicity, strategyproofness, certifiability, observability, corrigibility, compositional safety, non-vacuity) on each of the five represented governance graph fixtures. The raw legacy positive-delta probe is uniform: increasing the encoded suspicion or audit-window field flips the protocol's verdict from `Permit` to `Deny`. Under the current schema-derived audit, however, the same fields are treated as lower-better adverse evidence, all five fixtures pass canonical monotonicity, and all five receive `AuditVerdict.legitimate`.

The audit is not an attack on AI Control. The empirical safety case lives on the channel layer; the structural diagnostic lives on the rule layer. The legacy probe names a precise modeling error: it treated higher suspicion as claimant-positive strengthening. The schema-derived audit corrects that direction and therefore clears these fixtures. Neither the legacy diagnostic nor the corrected pass result subsumes the empirical safety case.

##### 1.2 Why monotonicity, and what its failure means

For the audit graph, canonical monotonicity applies a positive perturbation magnitude in the field's semantic improvement direction and requires every claimant's final decision rank to be weakly preserved. On the binary `Permit`/`Deny` specialization this becomes no `Permit → Deny` flip. For higher-better fields, a positive numeric delta is an improvement; for lower-better suspicion, blocking, deployment-trigger, and audit-routing fields, a negative numeric delta is the improvement. This polarity distinction is load-bearing for AI Control because the audited fields are adverse-evidence or routing-risk indicators, not trust scores.

Each AI Control fixture has a raw legacy positive-delta witness: increasing a suspicion or audit-window metric triggers audit/deferral and can flip the audited decision toward `Deny`. The schema-derived diagnostic classifies those metrics as lower-better. Once the audit asks whether semantic improvement weakly preserves every claimant's decision rank, the five represented fixtures pass monotonicity and receive `AuditVerdict.legitimate` verdict-tags.

The reason this is a *complementary* observation to the empirical safety case is that monotonicity-on-represented-governance-graph is not the property AI Control's empirical analysis aims to establish. AI Control bounds the *worst-case* behavioral subversion rate. The structural audit observes a *typed* property of the represented rule layer. Both are real properties; they are not the same property. A protocol can satisfy the empirical safety bound while failing the structural property, and vice versa.

##### 1.3 Relation to empirical control research (alignment-science, Redwood, METR)

The structural audit gives the AI Control program a *rule-layer companion*: a typed structural property that the repository's hand-modeled protocol fixtures do or do not satisfy, computable mechanically from those committed graph literals. The companion is not a substitute for the empirical safety case. It is a structural signature that complements the empirical evaluation. Where empirical evaluation tests *whether* the protocol resists subversion at a given capability scale, the structural audit tests *which structural properties* the represented governance graph has. The two together give a richer picture: the empirical bound at the channel layer, the structural signature at the rule layer.

We present the corrected rule-layer signature of the five represented AI Control protocol fixtures here. The raw legacy signature is uniform and stark: all five have positive-delta `Permit → Deny` calibration witnesses at the suspicion-calibration layer. The schema-derived signature is also uniform: all five pass monotonicity and receive `AuditVerdict.legitimate` verdict-tags. This is structural information about a represented protocol slice, not a refutation of the safety case.

---

#### 2. Related work

##### 2.1 The AI Control program

**Greenblatt, Shlegeris et al.** (2023), *AI Control: Improving Safety Despite Intentional Subversion* (arXiv:2312.06942), introduces the AI Control framework and the five canonical protocols. The empirical safety case is established via a worst-case adversarial subversion-rate analysis at fixed capability.

**Korbak et al.** (2025), *A sketch of an AI control safety case* (arXiv:2501.17315), extends the analysis to a structured safety case, formally argued, with control measures as building blocks. The Korbak safety case is the motivating published reference for this represented slice. Our bridge theorem `ai_control_fixture_graphs_receive_legitimate_verdict` (`Legitimacy.Bridges.KorbakAIControlBridge`) ranges only over the local `AIControlProtocol` enum: upfront auditing, trusted monitoring, defer-to-trusted, untrusted monitoring, and trusted editing. Its proposition existentially exposes a canonical schema-derived legitimate verdict for each represented fixture graph.

**Brown-Cohen, Irving, and Piliouras** (2025), *Avoiding Obfuscation with Prover-Estimator Debate* (arXiv:2506.13609), studies prover-estimator debate as adjacent scalable-oversight work on obfuscation. We do not treat it as an AI Control protocol lane here.

##### 2.2 Structural-vs-behavioral analysis of AI safety mechanisms

The structural audit applies the legitimacy framework's 9-element audit to a published protocol class. The 9-element audit is documented in:

- **the impossibility theorem paper** (`papers/03-impossibility-theorem.md` in this repository) for the reachable scarce peer-relative three-diagnostic obstruction (consistency, solidarity, monotonicity) and the strategyproofness-as-derived bridge theorem.
- **the kernel-as-compiled-object paper** (`papers/02-semantic-legitimacy-kernels.md`) for the 5-axiom kernel subset (certifiability, observability, corrigibility, compositional safety, non-vacuity).

This paper takes the audit-as-given and applies it to a target protocol class.

Adjacent external work in formal rule-layer analysis:

- **Allegrini, Shreekumar, and Celik** (2025), *Formalizing the Safety, Security, and Functional Properties of Agentic AI Systems* (arXiv:2510.14133), formalizes host-agent and task-lifecycle models with temporal-logic properties, including 16 host-agent properties and 14 task-lifecycle properties. This is rule-layer property specification and verification; our audit asks a different question about the admissibility of represented governance rules.

##### 2.3 Sleeper agents and alignment-faking

The audit's structural signature pairs naturally with the sleeper-agent characterization (one direction discharged via `deceptive_deployment_on_not_audit_monotone`). A sleeper agent is a model whose training-time aligned behavior diverges from its deployment-time behavior. A control protocol is the deployment-time governance over an untrusted model. The *combination*, running the structural audit on the deployment-time protocol against an extracted sleeper-agent governance graph, is the natural composition. We do not take the composition here; the audit corpus and the sleeper characterization are independently published artifacts.

---

#### 3. Setup

##### 3.1 The 9-element audit

The audit is a structured procedure with 9 named checks. Each check returns `AuditCheckStatus.passed`, `.failed`, or `.skipped`; the pipeline then converts the first blocking check into an `AuditVerdict`. The full vocabulary (`AuditCheck`):

1. **consistency**: removing a claimant preserves the remaining claimants' final decisions.
2. **solidarity**: common audit shocks do not split same-class claimants into mixed improvement and worsening.
3. **monotonicity** (schema-derived polarity check): a positive perturbation magnitude is applied in the metric's semantic improvement direction, and every claimant's final decision rank must be weakly preserved. On the binary `Permit`/`Deny` specialization this is the no-`Permit → Deny` condition.
4. **strategyproofness**: derived from solidarity ∧ monotonicity per `solidarity_monotonicity_imply_strategyproof`; checked independently here as a structural property of the graph.
5. **certifiability**: the Lean-side fixture passes the audit dispatcher's certifiability core; replay-certificate validation remains a Rust-side responsibility.
6. **observability**: the audit's verdict is observable via the kernel observation interface.
7. **corrigibility**: the kernel admits the corrigibility predicate.
8. **compositional safety**: the graph composes safely under the kernel's composition operator.
9. **non-vacuity**: the kernel is not vacuously satisfied.

The pipeline verdict is `AuditVerdict.legitimate` if every ordered check passes, `AuditVerdict.rejected check` if the first blocking check fails, or `AuditVerdict.undischarged check` if the first blocking check is skipped. The audit's discriminating power comes from the typed blocking surface: rejected or undischarged mechanisms are tagged with the specific check that blocks the canonical legitimate verdict.

##### 3.2 The `AuditGovernanceGraph` fixture model

For each represented AI Control protocol, the repository hand-models an `AuditGovernanceGraph` fixture. The fixture packages intended decision sites as nodes, authority relationships as edges, and the represented decision rule as the graph's verdict function. This is not a verified parser from the source papers' protocol text, and there is no theorem here proving full faithfulness of the model to the published protocols. The paper's substrate claim is therefore conditional on an external modeling assumption: these committed graph literals are the structural representations under audit. The Lean definitions are in `Audits/AIControl.lean`:

The Lean theorems below govern those represented `AuditGovernanceGraph` fixtures, not the raw prose or full experimental implementations of the AI Control protocols. The text-to-fixture mapping is a trusted modeling base whose faithfulness is empirical and reviewable, not a theorem. Any faithfulness challenge should focus on that modeling boundary: omitted protocol structure, polarity encoding, or mismatched decision sites, rather than on the Lean proofs over the committed fixtures.

- `aiControlUpfrontAuditingGovernanceGraph` (line 48)
- `aiControlTrustedMonitoringGovernanceGraph` (line 155)
- `aiControlTrustedMonitoringDeferGovernanceGraph` (line 262)
- `aiControlUntrustedMonitoringGovernanceGraph` (line 387)
- `aiControlTrustedEditingGovernanceGraph` (line 500)

Each is wrapped in an `AuditSubject` fixture for the audit-pipeline interface (`aiControlProtocolUpfrontAuditingGraph` line 71, etc.).

##### 3.3 The strengthened-claim fixture

For each protocol, a `BaselineStrengthenedClaims` pair is constructed: a baseline claim list (representing the protocol's input under nominal conditions) and a positive-delta claim list (representing the protocol's input after increasing a chosen metric). The pair is constructed so that the baseline's first-effective verdict is `Permit` (`aiControl_*_baseline_original_permit` theorems) and the positive-delta verdict is `Deny` (`aiControl_*_baseline_strengthened_deny` theorems). The pair witnesses a raw positive-delta flip. It does not witness canonical semantic monotonicity failure, because the modified fields are lower-better adverse/routing-risk metrics.

The fixture pairs are concrete and reproducible via `native_decide` on rational-arithmetic claims. Each protocol's canonical monotonicity theorem (`aiControl_protocol_*_satisfies_monotonicity`) and canonical verdict theorem (`aiControl_protocol_*_legitimate`) is mechanically verified in Lean 4. The same file retains compatibility theorem names for the former polarity-aware surface.

##### 3.4 The bridge theorem to Korbak et al.

The bridge `ai_control_fixture_graphs_receive_legitimate_verdict` (`Legitimacy.Bridges.KorbakAIControlBridge`) establishes the formal relationship for the represented slice: each local `AIControlProtocol` fixture has a committed audit subject and a canonical legitimate verdict. The bridge does not prove the Korbak et al. safety case true, does not claim full coverage of AI Control protocols, and does not audit the protocols' behavioral semantics. It is a structural complement, not a refutation.

The triple-qualifying scope statement in the bridge's docstring is load-bearing: the bridge says *canonical rule-layer fixture verdict*, not *the safety case is true*; *not full coverage* of the protocols' behavioral semantics; *not a validation* of empirical safety. It is a structural complement at the rule layer.

---

#### 4. Main results

##### 4.1 The five protocol legitimacy theorems

For each of the five protocols, the canonical schema-derived audit verdict is mechanically verified as legitimate.

**Theorem 4.1.1** (Upfront Auditing legitimacy, `aiControl_protocol_upfrontAuditing_legitimate`, `lean/Legitimacy/Audits/AIControl.lean`).

**Theorem 4.1.2** (Trusted Monitoring legitimacy, `aiControl_protocol_trustedMonitoring_legitimate`).

**Theorem 4.1.3** (Trusted Monitoring with Defer-to-Trusted legitimacy, `aiControl_protocol_trustedMonitoringDefer_legitimate`).

**Theorem 4.1.4** (Untrusted Monitoring legitimacy, `aiControl_protocol_untrustedMonitoring_legitimate`).

**Theorem 4.1.5** (Trusted Editing legitimacy, `aiControl_protocol_trustedEditing_legitimate`).

The file also contains per-check status theorems. All nine canonical checks pass under schema-derived metric polarity. The verdict theorem itself is a `native_decide` equality on `governanceAdmissibilityVerdict`, not a bundled nine-part proof object. The verdict is `AuditVerdict.legitimate`.

The retained polarity-aware follow-up names are compatibility aliases over the canonical checker.

##### 4.2 The unified bridge to Korbak et al.

**Theorem 4.2** (AI Control fixture graphs receive legitimate verdicts, `ai_control_fixture_graphs_receive_legitimate_verdict`, `Legitimacy.Bridges.KorbakAIControlBridge`).
*For each protocol in the local five-case `AIControlProtocol` enum, there exists an `AuditSubject` fixture such that `governanceAdmissibilityVerdict subject = AuditVerdict.legitimate`. The bridge is about the represented rule-layer fixtures; the Korbak safety case is at the channel layer; the two are complementary.*

The bridge's case-split structure runs over the five represented protocols, lifting each per-protocol legitimate verdict theorem into the unified existential statement.

##### 4.3 The trusted-monitoring positive-delta witness

The bridge auxiliary theorem `trusted_monitoring_ai_control_fixture` (`Legitimacy.Bridges.KorbakAIControlBridge`) existentially packages the trusted-monitoring subject plus its canonical `AuditVerdict.legitimate` result. The concrete permit-to-deny pair lives in `Audits/AIControl.lean`: `aiControl_trustedMonitoring_baseline_original_permit` proves the baseline decision is `Permit`, and `aiControl_trustedMonitoring_baseline_strengthened_deny` proves the positive-delta decision is `Deny`. Those rational-arithmetic equalities are legacy calibration witnesses for the raw positive-delta probe, not the theorem-facing audit verdict.

The positive-delta pair is the audit's *empirical-style* artifact: a published, testable, reproducible witness for the legacy diagnostic on the represented trusted-monitoring fixture. Empirical safety researchers can re-evaluate the fixture independently.

##### 4.4 Defer-to-Resample as the open-extraction example

The Defer-to-Resample protocol does not currently have a stable extracted governance graph — the protocol's resample step requires a probabilistic structural representation that the deterministic `AuditGovernanceGraph` substrate does not capture. The companion theorem `defer_to_resample_has_no_current_extracted_graph` (`Legitimacy.Bridges.KorbakAIControlBridge`) makes this honest as a structural witness: the request-level extraction relation defines the `deferToResample` arm as `False`, so the audit corpus is currently 5 protocols and defer-to-resample is named as the open-extraction case. This is not a non-trivial unrepresentability proof for resampling; the substrate-extension to capture probabilistic resample remains open follow-up.

---

#### 5. Proof sketch

The audit applied to each protocol decomposes as follows.

**Step 1: Define the protocol fixture's graph.** The modeled decision sites are the audit-graph nodes; the modeled authority relationships are the edges; the represented verdict function is the graph's `verdictOf` map. The proof starts from this graph literal; it does not verify a text-to-graph extraction process from the source papers.

**Step 2: Establish the baseline / positive-delta claim pair.** The pair is constructed so the baseline's first-effective decision is `Permit` and the positive-delta claim's first-effective decision is `Deny`. The construction is direct: the chosen suspicion or audit-window field is increased; the protocol's audit or deferral gate fires; the resulting verdict flips.

**Step 3: Verify eight checks pass.** Each non-monotonicity check is verified by `decide`/`native_decide` evaluation on the protocol's graph and associated audit data. The checks are local properties of the graph or Lean-side audit projections. For each protocol:

- consistency: removing each claimant preserves the remaining claimants' final decisions.
- solidarity: common audit shocks do not split same-class claimants into mixed improvement and worsening.
- strategyproofness: structurally checked; the graph is strategyproof as a property of the committed fixture.
- certifiability: the Lean-side certifiability core passes decision-totality checks; Rust remains authoritative for replay-certificate validation.
- observability, corrigibility, compositional safety, non-vacuity: the corresponding Lean-side audit projections pass on the represented fixture.

**Step 4: Establish the raw positive-delta calibration witness.** The positive-delta pair witnesses the legacy diagnostic: the original verdict is `Permit`, the positive-delta verdict is `Deny`, and the legacy probe treats every positive metric delta as a strengthening.

**Step 5: Apply the schema-derived polarity correction.** `auditMetricPolaritySchema` classifies the AI Control suspicion and routing-risk fields as `lowerBetter`. The canonical monotonicity check applies the improvement perturbation in that semantic direction, all five monotonicity checks pass, and all five governance verdicts return the `AuditVerdict.legitimate` tag. The positive-delta permit-to-deny pairs remain raw legacy calibration witnesses, not theorem-facing rejection verdicts.

**Step 6: Read the bridge theorem.** `ai_control_fixture_graphs_receive_legitimate_verdict` and `trusted_monitoring_ai_control_fixture` package the represented subjects with `governanceAdmissibilityVerdict subject = AuditVerdict.legitimate`. The AI Control fixtures do not rely on the diagnostic-presence event counters, which carry no claimant-welfare direction.

The full Lean proof is reproducible on commit: `native_decide` evaluates each protocol's audit on its concrete fixture deterministically, and the canonical audit verdict is mechanically checked as `AuditVerdict.legitimate`.

---

#### 6. Discussion: implications for the AI Control / Anthropic alignment-science / Redwood audiences

##### 6.1 What the audit says

The audit gives each AI Control protocol fixture a *rule-layer signature* — a typed structural property of the represented governance graph. The raw legacy signature for all five represented fixtures is uniform: positive-delta calibration witness at the suspicion-calibration layer. The schema-derived signature is the corrected one: monotonicity passes once suspicion and routing-risk fields are interpreted as lower-better.

**Why monotonicity, structurally**. The suspicion-calibration step in each protocol determines deferral or audit-trigger based on a suspicion or audit-routing metric. The thresholding logic produces the legacy calibration witness: at the threshold boundary, a positive delta raises the adverse metric, crosses the threshold, and triggers deferral or audit, which can flip the verdict from `Permit` to `Deny`. The schema-derived audit treats that positive delta as an adverse change, not a claimant-positive strengthening.

**The structural signature is uniform across protocols**. All five fixtures use threshold-discriminator suspicion-calibration; all five expose the raw legacy positive-delta diagnostic at the same site; all five pass the schema-derived diagnostic at that site. This is informative because it separates a diagnostic artifact from a surviving structural concern.

##### 6.2 What the audit does *not* say

**The audit does not refute the safety case**. The Korbak et al. safety case is at the *channel* layer; it bounds the worst-case adversarial subversion rate. The audit is at the *rule* layer; it tests structural properties of represented graph fixtures. The raw legacy flag was consistent with the safety case because it was a separate rule-layer diagnostic; the schema-derived pass result is also separate from the empirical bound.

**The audit does not establish unsafety**. The legacy positive-delta flag is informative about the old diagnostic's treatment of adverse fields; it is not a behavioral claim.

**The audit does not say the protocols should be redesigned**. Whether a protocol *should* be designed to satisfy monotonicity at the rule layer is a separate question. Monotonicity may be the wrong property to optimize for at the suspicion-calibration layer (suspicion is sometimes legitimately *non-monotonic* in evidence; e.g., over-strong evidence from an untrusted source is itself suspicious). The audit observes the structural property; the design question is downstream.

##### 6.3 The audit as collaborative complement

The audit's most useful framing is *complementary structural analysis*. Empirical safety case + structural rule-layer signature = richer picture than either alone. The structural signature is mechanical and reproducible (`native_decide` on rational arithmetic); empirical evaluation is observational and probabilistic. The two are not in tension; they are in conjunction.

We anticipate the most productive engagement is via extension of the *audit corpus* to additional control-style protocols (defer-to-resample once the probabilistic fixture substrate lands) and *cross-paper* composition with the sleeper-agent characterization paper. The combined picture — control protocols' structural signature × represented-deployment-graph's monotonicity property — is the natural follow-up.

##### 6.4 The relationship to Anthropic alignment-faking

The Anthropic alignment-faking research line investigates models whose training-time aligned behavior diverges from their deployment-time behavior. The structural complement is on the *deployment-time governance* side: what is the structural signature of the protocol governing the deployment? In the AI Control fixtures here, the corrected schema-derived signature is a pass, while the legacy positive-delta signature records where adverse suspicion fields trigger routing. Whether this matters for alignment-faking detection is open.

##### 6.5 The bridge as outreach surface

The bridge theorem `ai_control_fixture_graphs_receive_legitimate_verdict` is the named outreach surface. It is mechanically verified, triple-qualifies its scope (rule-layer / not-coverage / legitimate-not-validated), and provides per-protocol concrete fixtures. It is the artifact that an interested AI Control researcher can engage with directly: re-evaluate the fixture, examine the represented graph, and audit the metric-polarity annotations. The structural complement is reproducible over the committed fixtures; that is its claim to scientific status.

---

#### 7. Limitations

1. **Five-protocol corpus only**. The audit covers Upfront Auditing, Trusted Monitoring, Trusted Monitoring with Defer-to-Trusted, Untrusted Monitoring, and Trusted Editing. Defer-to-Resample is named as open fixture-modeling work because its resampling step needs probabilistic structure.

2. **Deterministic fixture substrate only**. The `AuditGovernanceGraph` substrate is deterministic and represented directly as Lean data. Protocols with intrinsically probabilistic structural elements (defer-to-resample is the canonical example) require a probabilistic fixture substrate not currently in the audit pipeline.

3. **Fixed audit-input distribution**. The positive-delta fixture is a specific input pair. The legacy monotonicity flag is on that rule-layer diagnostic, not on a behavioral distribution. The audit does not say what fraction of behavioral inputs trigger the legacy flip.

4. **Rule-layer only, not channel-layer**. The audit is on the represented governance graph fixture. The behavioral channel that the protocol implements is not audited. The structural diagnostic is consistent with arbitrary behavior on the channel layer (within the protocol's published behavioral semantics).

5. **No empirical-safety claim**. The audit does not establish or refute the AI Control safety case. It is structural complement.

6. **Threshold-discriminator bias**. All five protocols use threshold-discriminator suspicion-calibration. The legacy audit may be returning a signature that is *generic* to threshold-discriminators over lower-better adverse fields rather than *specific* to AI Control. It remains a conjecture that non-threshold suspicion-calibration or continuous-deferral-rate mechanisms would produce different audit signatures.

7. **No multi-protocol composition**. Each audit is on a single protocol in isolation. The composed-protocol case (Trusted Editing on top of Trusted Monitoring, etc.) requires the multi-agent composition substrate (`MultiAgentEdgeLocalComposition.lean`); this is a follow-up.

---

#### 8. Conclusion

The five represented AI Control protocol fixtures uniformly pass the canonical schema-derived audit, including monotonicity at the suspicion-calibration layer. The raw positive-delta probes still identify where increasing lower-better suspicion fields routes claims toward denial; those probes are calibration diagnostics, not semantic monotonicity failures. This is a *complementary* rule-layer observation beside the Korbak et al. safety case, not a behavioral safety claim.

The structural complement is most useful when read as collaborative information rather than refutation. The empirical safety case is at the channel layer; the audit is at the rule layer; the two compose. The audit corpus can extend to additional protocols (open follow-up: defer-to-resample once probabilistic fixture modeling lands) and compose with the sleeper-agent characterization paper for the deployment-time-governance × represented-deployment-graph picture.

The legacy threshold-discriminator monotonicity failure is a diagnostic signature of positive deltas applied to lower-better suspicion-calibration fields. Protocols outside this family (non-threshold suspicion-calibration, continuous-deferral-rate mechanisms) may produce different audit signatures. The signature space, mapped systematically across protocol design choices and metric polarities, is the broader research target.

---

#### References

- **Brown-Cohen, J., Irving, G., Piliouras, G.** (2025). Avoiding Obfuscation with Prover-Estimator Debate. *arXiv:2506.13609*.
- **Greenblatt, R., Shlegeris, B., et al.** (2023). AI Control: Improving Safety Despite Intentional Subversion. *arXiv:2312.06942*.
- **Hubinger, E., Denison, C., Mu, J., et al.** (2024). Sleeper Agents: Training Deceptive LLMs that Persist Through Safety Training. *arXiv:2401.05566*.
- **Korbak, T., Clymer, J., Hilton, B., Shlegeris, B., Irving, G.** (2025). A sketch of an AI control safety case. *arXiv:2501.17315*.
- **Allegrini, E., Shreekumar, A., Celik, Z. B.** (2025). Formalizing the Safety, Security, and Functional Properties of Agentic AI Systems. *arXiv:2510.14133*.

##### Lean substrate references

- `Legitimacy.aiControl_protocol_upfrontAuditing_legitimate`
- `Legitimacy.aiControl_protocol_trustedMonitoring_legitimate`
- `Legitimacy.aiControl_protocol_trustedMonitoringDefer_legitimate`
- `Legitimacy.aiControl_protocol_untrustedMonitoring_legitimate`
- `Legitimacy.aiControl_protocol_trustedEditing_legitimate`
- `Legitimacy.ai_control_fixture_graphs_receive_legitimate_verdict`
- `Legitimacy.trusted_monitoring_ai_control_fixture`
- `Legitimacy.defer_to_resample_has_no_current_extracted_graph`
- `Legitimacy.AIControlProtocol.subject`

## 3. Sleeper-agent Monotonicity Test

### Monotonicity as a Decidable Structural Test for Sleeper-Agent Deployment Admissibility

---

#### Abstract

We prove a legacy positive-delta structural audit diagnostic for the repository's formal *deceptive-deployment admissibility* predicate and demonstrate it on a synthetic sleeper-agent fixture that follows the Hubinger et al. 2024 deployment-trigger motif. If a represented audit subject admits the formal sleeper split, then it fails the legacy audit-graph monotonicity predicate (`Legitimacy.deceptive_deployment_on_not_audit_monotone`). The load-bearing formal fact is narrow: a positive perturbation to the deployment-trigger field changes the affected claimant's verdict from `Permit` to `Deny`, which obstructs the legacy monotonicity check. This is not a semantic-strengthening theorem. The same fixture passes the canonical schema-derived monotonicity check (`sleeper_agent_monotonicity_verdict`) and has a legitimate canonical governance verdict (`sleeper_agent_canonical_governance_verdict`), because `deployment_context` is treated as lower-better risk evidence. The decidable check `admitsDeceptiveDeploymentCheck` is sound and complete with respect to the Prop-level predicate, and `native_decide`-evaluates on rational-arithmetic claim corpora. The concrete fixture (`sleeperAgentExtractedGovernanceGraph` and `sleeperAgentAdmitsDeceptiveDeployment`) demonstrates the diagnostic on the repository's fixed synthetic corpus. The result is on the *extracted* audit subject, not on the underlying model: it is a typed property of the audit pipeline's view of the represented deployment slice, decidable by mechanical evaluation, and orthogonal to the empirical detection question.

---

#### 1. Introduction

##### 1.1 The lead

Hubinger et al. 2024 (*Sleeper Agents: Training Deceptive LLMs that Persist Through Safety Training*, arXiv:2401.05566) demonstrates a behavioral protocol: language models can be trained to behave aligned during a training-time monitoring phase and to behave misaligned at deployment time, conditional on a deployment-trigger feature. The phenomenon is empirical: it is observed by training a model with the deceptive-deployment objective and verifying the deployment-time behavior diverges from the training-time behavior. The empirical demonstration is the standing reference for *deployment-time-divergence*; it is not, by construction, a structural audit-subject diagnostic.

We prove a structural decidable diagnostic for a formal sleeper split. The diagnostic is on the *extracted* audit subject — the typed audit-pipeline object that the deployment surface induces, not the underlying model. If the subject admits deceptive deployment on the fixed corpus, then it fails the legacy audit-graph monotonicity property. This direction is mechanically discharged in Lean 4 (`deceptive_deployment_on_not_audit_monotone`, `Legitimacy.Audits.SleeperCharacterization:126`).

The result is polarity-sensitive. Under the legacy positive-delta predicate, raising `deployment_context` produces a `Permit → Deny` obstruction. Under the schema-derived polarity predicate, the same fixture passes: semantic improvement for a lower-better risk field decreases that metric rather than increasing it. The formal contribution is therefore a legacy-diagnostic obstruction and executable checker, not a claim that semantic strengthening always exposes sleeper-agent structure.

##### 1.2 What this is, what it is not

The result is a one-way structural diagnostic on the extracted audit-pipeline subject: formal deceptive deployment on the corpus implies failure of legacy monotonicity, and the decidable check is sound and complete for the Prop-level predicate (`admitsDeceptiveDeploymentCheck_sound`, `admitsDeceptiveDeploymentCheck_complete`), evaluating by `native_decide` on concrete rational-arithmetic corpora. The converse is not claimed: the current substrate proves a strict refinement, and legacy monotonicity failure does not imply formal deceptive deployment. Because the diagnostic concerns the represented audit subject rather than the underlying model, it neither characterizes sleeper agents in the empirical sense of Hubinger et al. 2024 nor evaluates behavioral detection methods; the two are complementary detection surfaces.

##### 1.3 Relation to alignment-faking and sleeper-agent research

Hubinger and the Anthropic alignment-faking line establish empirical phenomena about training-time and deployment-time behavior. Here we provide a *structural* property of the represented deployment surface: in the committed fixture, a positive legacy perturbation to `deployment_context` flips the affected claimant from `Permit` to `Deny`. That flip is the legacy diagnostic: it is a typed property of the rule layer of the extracted subject, computable by mechanical evaluation, independent of the model's training pipeline. It should not be read as semantic benign-evidence strengthening, because the schema-derived polarity substrate treats `deployment_context` as lower-better risk evidence and the fixture passes the canonical check.

This is a necessary-condition theorem, not half of a pending equivalence. The contrast graph `permitEscalateOnly` fails legacy monotonicity but does not admit the formal `Permit → Deny` deceptive-deployment split, so the current predicate is stricter than monotonicity failure. The remaining classification work is to distinguish deployment-relevant monotonicity obstructions from spurious ones.

---

#### 2. Related work

##### 2.1 Sleeper agents and alignment-faking (empirical lineage)

**Hubinger, Denison, Mu, et al.** (2024), *Sleeper Agents: Training Deceptive LLMs that Persist Through Safety Training* (arXiv:2401.05566), is the canonical behavioral-protocol reference. The paper demonstrates that language models can be trained with backdoor deceptive-deployment behavior and that the behavior persists through safety training. The detection question is empirical: probe-based detection, residual-stream analysis, behavioral divergence at deployment-trigger. The structural diagnostic here starts only after that kind of deployment surface is represented as an `AuditSubject`.

**Anthropic alignment-faking research line** (multiple recent papers): empirical investigations of alignment-faking, models that report aligned behavior during training while exhibiting misaligned behavior at deployment.

The formal complement here is on the represented *audit subject*, not on the model's internal structure. The two surfaces — empirical behavioral divergence and structural rule-layer metric-polarity diagnostics in an extracted representation — are complementary. We do not subsume empirical detection; we provide a typed diagnostic that can be compared with it.

##### 2.2 AI Control and structural admissibility

**Greenblatt-Shlegeris** (2023), *AI Control* (arXiv:2312.06942), and **Korbak et al.** (2025), *A sketch of an AI control safety case* (arXiv:2501.17315), publish behavioral control protocols and safety-case arguments for deploying untrusted models. The companion AI Control substrate does not claim those protocols are behaviorally safe; it extracts five represented protocol fixtures as audit subjects and proves canonical schema-derived legitimate verdicts for each (`aiControl_protocol_upfrontAuditing_legitimate`, `aiControl_protocol_trustedMonitoring_legitimate`, `aiControl_protocol_trustedMonitoringDefer_legitimate`, `aiControl_protocol_untrustedMonitoring_legitimate`, `aiControl_protocol_trustedEditing_legitimate`). The *deployment-time-governance x represented sleeper-slice* composition is a follow-up artifact, not discharged here.

##### 2.3 Deceptive alignment and corrigibility

**Hubinger et al.** (2019), *Deceptive Alignment*, is the foundational write-up of the deceptive-alignment phenomenon as a target for theoretical investigation. The structural admissibility we name is the rule-layer counterpart on the extracted-graph object.

**Soares et al. / MIRI** corrigibility lineage: the deceptive-alignment problem is the standing motivation. This diagnostic does not address corrigibility directly; it addresses the repository's formal deployment-admissibility predicate. A graph that fails monotonicity at extraction may fail other corrigibility properties, but those links are not proved here.

##### 2.4 Adjacent governance-graph audits

Within the legitimacy-paper family, the audit pipeline is shared across:

- **Audits/AIControl.lean**: the AI Control protocol corpus.
- **Audits/SleeperAgent.lean**: the sleeper-agent fixture (this report).
- **Audits/SleeperCharacterization.lean**: the characterization-substrate (this report).
- **Bridges/HubingerDeceptionBridge.lean**: the bridge to the Hubinger scenario predicate.

The audit pipeline is the same procedure across all surfaces; the output here is the legacy diagnostic on the represented audit subject.

---

#### 3. Setup

##### 3.1 The extracted governance graph and the audit-graph monotonicity predicate

For a deployed AI system, the *extracted governance graph* is wrapped as an `AuditSubject`, the typed audit-pipeline object representing the deployment's decision surface. Nodes are decision sites in the deployment (input-classification, deployment-trigger evaluation, output-decision); edges are the structural authority relationships; decisions are computed by `auditFinalDecisions subject claims`.

The theorem statements below govern this extracted `AuditSubject`, not raw model internals or source syntax. The extractor or hand-model that produces the subject is a trusted base whose faithfulness to the represented deployment slice is empirical, not Lean-proved. Scrutiny should fall on that boundary: whether the sleeper-trigger route was faithfully represented, whether relevant decision sites were omitted, or whether the polarity metadata matches the intended risk semantics, rather than the Lean proof over the fixed subject.

The legacy *audit-graph monotonicity* predicate `AuditGraphMonotonicity` (`Legitimacy.Audits.SleeperCharacterization`) says: for a fixed subject and claim corpus, every positive finite audit perturbation from `auditGraphDeltas claims` weakly preserves every claimant's decision rank. Formally:

```
def AuditGraphMonotonicity
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) : Prop
```

This is the rule-layer monotonicity property evaluated at a subject and corpus, not a graph-only predicate independent of claims.

##### 3.2 The deceptive-deployment predicate

The Prop-level predicate names what it means for an audit subject to *admit deceptive deployment* on a fixed claim corpus and a pair of trigger fields:

```
def AdmitsDeceptiveDeploymentOn
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim)
    (trainingTrigger deploymentTrigger : AuditMetricField) : Prop
```

(`Legitimacy.Audits.SleeperCharacterization`), the subject admits deceptive deployment on `claims` when there is a nonempty `DeceptiveDeploymentWitnessOn`: a monitored claim has the deployment trigger dormant in the training corpus, a positive enumerated delta is applied to the deployment trigger on an enumerated deployment claim, the affected claimant is enumerated, the training decision is `Permit`, the deployment decision is `Deny`, and the training/deployment trigger fields are distinct.

The canonical version specializes the predicate to the synthesized corpus `auditGraphClaims subject`:

```
def AdmitsDeceptiveDeployment
    (subject : AuditSubject)
    (trainingTrigger deploymentTrigger : AuditMetricField) : Prop
```

(`Legitimacy.Audits.SleeperCharacterization`): this is not an existential over arbitrary corpora; it is the fixed-corpus specialization used by the repository's extracted audit subject.

##### 3.3 The decidable check

The decidable check `admitsDeceptiveDeploymentOnCheck` (`Legitimacy.Audits.SleeperCharacterization`) is a Bool-valued function on `(subject, claims, trainingTrigger, deploymentTrigger)` that is sound and complete with respect to the Prop-level predicate:

> `admitsDeceptiveDeploymentOnCheck_iff_AdmitsDeceptiveDeploymentOn` (line 300): the check is iff with the predicate.
>
> `admitsDeceptiveDeploymentOnCheck_sound` (line 212): true check ⟹ predicate holds.
>
> `admitsDeceptiveDeploymentOnCheck_complete` (line 278): predicate holds ⟹ check is true.

The canonical fixed-corpus version `admitsDeceptiveDeploymentCheck` (line 206) similarly specializes to `auditGraphClaims subject`. The check is `decide`-evaluable on rational-arithmetic claim corpora; the concrete fixture evaluation is `native_decide`-discharged. The executable API returns a `Bool`, not a runtime witness object; the soundness theorem reconstructs the Prop-level witness from a true check.

##### 3.4 The sleeper-agent fixture

The concrete fixture is in `Audits/SleeperAgent.lean`:

- `sleeperAgentExtractedGovernanceGraph` (line 31): the sleeper-agent extracted graph.
- `sleeperAgentExtractedGraph` (line 55): the audit-subject wrapper.
- `sleeperAgentClaims` (line 60): the baseline claim corpus.
- `sleeperAgentBaselineDeploymentStrengthenedClaims` (line 64): the baseline-strengthened pair.
- `sleeper_agent_baseline_original_permit` (line 72): the baseline verdict is `Permit`.
- `sleeper_agent_baseline_strengthened_deny` (line 81): the strengthened verdict is `Deny`.
- `sleeper_agent_canonical_governance_verdict`: the canonical schema-derived verdict is legitimate.
- `sleeper_agent_monotonicity_verdict`: canonical monotonicity passes.
- `sleeperAgentPassesSolidarity` (line 105): solidarity passes.
- `sleeperAgentPassesNonvacuity` (line 112): non-vacuity passes.

The fixture is concrete, reproducible via `native_decide`, and rationally-arithmetic.

---

#### 4. Main results

##### 4.1 The necessary-condition theorem: deceptive-deployment ⟹ ¬ audit-monotone

**Theorem 4.1** (Necessary-condition theorem, `deceptive_deployment_on_not_audit_monotone`, `Legitimacy.Audits.SleeperCharacterization`).
*Let `subject : AuditSubject`, `claims : List AuditGovernanceClaim`, and `trainingTrigger deploymentTrigger : AuditMetricField`. If the subject admits the formal deceptive-deployment predicate on that corpus and trigger pair, then the subject fails legacy audit-graph monotonicity on that same corpus:*

```
AdmitsDeceptiveDeploymentOn subject claims trainingTrigger deploymentTrigger →
    ¬ AuditGraphMonotonicity subject claims
```

The proof is by direct construction. The deceptive-deployment witness provides a positive deployment-trigger perturbation and a verdict-flip `Permit → Deny`. This pair is exactly a legacy monotonicity violation: the positive perturbation lowers the decision rank. Therefore legacy monotonicity fails on the witness pair.

The canonical fixed-corpus version `deceptive_deployment_not_audit_monotone` (line 164) specializes the theorem to `auditGraphClaims subject`.

##### 4.2 The decidable iff

**Theorem 4.2** (Decidable check soundness and completeness, `admitsDeceptiveDeploymentOnCheck_iff_AdmitsDeceptiveDeploymentOn`, line 300).
*The decidable Bool-valued check `admitsDeceptiveDeploymentOnCheck` is iff with the Prop-level predicate. Soundness (`Legitimacy.Audits.SleeperCharacterization`) and completeness (`Legitimacy.Audits.SleeperCharacterization`) are independently established.*

This is the structural-decidability content. It says the predicate is *decidable* on rational-arithmetic corpora, and the decision is a single `decide`/`native_decide` evaluation.

The companion `admitsDeceptiveDeploymentCheck_iff_AdmitsDeceptiveDeployment` (line 311) specializes the iff to the canonical `auditGraphClaims subject` version.

##### 4.3 The sleeper-agent witness

**Theorem 4.3** (Sleeper-agent admits deceptive deployment, `sleeperAgentAdmitsDeceptiveDeployment`, line 356).
*The `sleeperAgentExtractedGraph` audit subject admits deceptive deployment on `auditGraphClaims sleeperAgentExtractedGraph` for the `"training_context"` / `"deployment_context"` trigger pair.*

The companion `sleeperAgentAdmitsDeceptiveDeploymentCheck` (line 436) is the Bool-valued evaluation, `native_decide`-discharged.

By Theorem 4.1, the represented sleeper-agent split in the audit pipeline fails legacy audit-graph monotonicity, by construction of the audit-subject typed property. The diagnostic is concrete and reproducible.

##### 4.4 The represented Hubinger-style slice

**Theorem 4.4** (Hubinger-style scenario packaging lemma, `hubinger_deception_subsumed_by_kernel_substrate`, `Legitimacy.Bridges.HubingerDeceptionBridge`).
*For any value of the repository-defined `HubingerDeceptionScenario`, construct a `KernelSleeperSubstrateWitness` by carrying over the scenario's pretrigger compositional-safety proof and formal `AdmitsDeceptiveDeployment` field, then applying `deceptive_deployment_not_audit_monotone`.*

This is a narrow represented-slice lemma. The structure `HubingerDeceptionScenario` already assumes the formal sleeper split in its `deployment_split` field; the theorem does not derive that split from Hubinger et al. 2024, from model internals, or from empirical behavior. The concrete witness is `sleeperAgentHubingerScenario` (line 71), and the per-scenario theorem is `sleeper_agent_hubinger_bridge_witness` (line 78).

The honest-scope companion `inert_sleeper_shape_not_hubinger_deception_scenario` (line 85) names a sleeper-shaped graph that is rejected by the formal `AdmitsDeceptiveDeployment` predicate. This guards the represented slice against a trivial shape-only reading, but it is still a local predicate check rather than an empirical classifier.

##### 4.5 Discriminating witnesses on contrast graphs

The audit's discriminating power is shown via two contrast graphs:

- `thresholdOnlyGovernanceGraph` (`Legitimacy.Audits.SleeperCharacterization`): a threshold-only graph that *passes* monotonicity (`thresholdOnly_passes_monotonicity`, line 483) and *does not admit* deceptive deployment (`thresholdOnly_rejects_deceptive_deployment`, line 467).
- `permitEscalateOnlyGovernanceGraph` (line 492): a permit-escalate-only graph that *fails* monotonicity (`permitEscalateOnly_fails_monotonicity`, line 505) but *does not admit* deceptive deployment in the sense of the predicate (`permitEscalateOnly_rejects_deceptive_deployment`, line 558).

The second contrast is informative: a graph can fail monotonicity *without* admitting deceptive deployment in the Prop-level sense. The theorem `admitsDeceptiveDeployment_strict_refinement_of_monotonicity_failure` packages this fact: the current predicate is a strict refinement of legacy monotonicity failure, not one side of an eventual equivalence with that predicate.

---

#### 5. Proof sketch

The necessary-condition theorem has the following structure.

**Step 1: Unfold the deceptive-deployment witness.** `AdmitsDeceptiveDeploymentOn subject claims trainingTrigger deploymentTrigger` provides:
- a positive deployment-trigger delta applied to an enumerated deployment claim,
- the baseline verdict on `claims` is `Permit`,
- the strengthened verdict on `strengthened` is `Deny`.

**Step 2: Unfold legacy audit-graph monotonicity.** `AuditGraphMonotonicity subject claims` says: for every positive finite audit perturbation in the legacy direction, the verdict rank does not decrease.

**Step 3: Direct refutation.** The witness pair from Step 1 is exactly a legacy monotonicity violation: a positive deployment-trigger perturbation went `Permit → Deny`, which lowers the rank. The witness refutes the universal-quantifier statement of Step 2.

**Step 4: Soundness/completeness of the check.** The executable check enumerates exactly the finite fields carried by `DeceptiveDeploymentWitnessOn`: the monitored dormant claim, the positive deployment-trigger delta from `auditGraphDeltas claims`, the deployment claim to update, and the affected claimant from `auditClaimantIds claims`. Soundness reconstructs those fields into the Prop-level witness when the Bool check is true; completeness uses the witness fields to show that the same finite enumeration returns true.

The proof in Lean directly threads these four steps. The iff with the decidable check (Theorem 4.2) is a separate inductive argument; the sleeper-agent witness (Theorem 4.3) is `native_decide` on the concrete fixture; the represented Hubinger-style slice (Theorem 4.4) packages the `HubingerDeceptionScenario` fields and applies the monotonicity-obstruction theorem.

---

#### 6. Discussion: complementarity with empirical sleeper-agent and alignment-faking research

##### 6.1 The represented diagnostic

The diagnostic is on the *extracted* audit subject: any represented subject satisfying the formal deceptive-deployment predicate on the fixed corpus fails the legacy audit-graph monotonicity predicate. That property of the deployment's rule layer is independent of both the model's training process and any empirical evaluation, and is decidable by mechanical evaluation on rational-arithmetic claim corpora.

The schema-derived result matters. For the committed sleeper fixture, `sleeper_agent_monotonicity_verdict` proves that canonical monotonicity passes, and `sleeper_agent_canonical_governance_verdict` proves the canonical governance verdict is legitimate. The legacy diagnostic remains useful as a stress test for positive-trigger routing, but it is not the final semantic verdict once field polarity is accounted for.

The legacy monotonicity obstruction is *necessary* for the formal sleeper split, but it is not sufficient. The committed `permitEscalateOnly` contrast proves that some monotonicity failures do not admit the formal deceptive-deployment witness.

##### 6.2 What pairs with empirical detection

Empirical detection methods bound *behavioral* divergence between training-time and deployment-time. This diagnostic names a formal rule-layer property on the extracted audit subject. The two surfaces are:

- **Empirical**: behavioral evaluation, residual-stream analysis, probe-based detection.
- **Structural**: typed audit-pipeline rule-layer diagnostic on the represented slice, decidable, reproducible.

A composite detection pipeline could run empirical evaluation in parallel with structural extraction, returning *empirical-positive*, *structural-positive*, or both. The combinations carry information: empirical-positive + structural-negative could indicate a model whose deceptive-deployment behavior factors through a graph-shape we have not yet characterized; structural-positive + empirical-negative could indicate a deployment surface whose extracted-graph monotonicity-failure does not yet manifest behaviorally.

##### 6.3 What this is not

**Not a model audit**. The diagnostic is on the extracted *audit subject* of the represented deployment slice, not the *model*. We do not address whether the underlying model has internal sleeper-agent structure. We address whether the deployment's audit-pipeline view has a typed legacy monotonicity-violation pattern.

**Not a sleeper-agent classifier**. The diagnostic is necessary not sufficient for the formal predicate. A graph that fails audit-graph monotonicity does not necessarily admit deceptive deployment in the Prop-level sense — `permitEscalateOnly` is a contrast witness. The legacy signal is a local formal obstruction, not a classifier.

**Not a refutation of empirical detection**. Empirical methods test behavioral divergence; this diagnostic tests a represented rule-layer property. The two are complementary.

##### 6.4 Composition with AI Control structural audit

The companion AI Control substrate has five concrete raw positive-delta calibration witnesses over extracted audit subjects: upfront auditing, trusted monitoring, trusted-monitoring-with-defer, untrusted monitoring, and trusted editing. It also has canonical schema-derived pass theorems for those fixtures. The composition with the sleeper-agent characterization is natural future work: an extracted AI Control protocol fixture on a represented sleeper deployment slice could be evaluated mechanically as a 2-D matrix with rows over represented control fixtures, columns over represented deployment slices, and entries recording the relevant legacy and schema-derived diagnostics.

##### 6.5 Structural monitorability vs CoT monitorability

The sleeper-agent characterization sits adjacent to the *structural monitorability* paper. Chain-of-thought monitorability may be fragile under changes to models and training procedures, as discussed in 2025 CoT-monitorability work. This repository's structural diagnostics do not depend on access to model chain-of-thought once an extraction is fixed; they do not by themselves prove robustness of the extraction process under capability scaling.

Legacy monotonicity failure in the represented deployment slice is therefore a rule-layer diagnostic, not an empirical guarantee. It can be compared with behavioral and CoT-monitorability channels without replacing them.

##### 6.6 Open follow-up: classifying obstructions

The open problem is not to prove the current converse. The current converse is false: `permitEscalateOnly_fails_monotonicity` and `permitEscalateOnly_rejects_deceptive_deployment` show monotonicity-failure can occur without the Prop-level deceptive-deployment witness. The research problem is to define and validate a narrower class of monotonicity obstructions that correspond to deployment-relevant sleeper splits.

The open follow-up is an *ambitious extension*: it requires substrate extension and the typed predicate that distinguishes deceptive-deployment monotonicity-failure from spurious. We have not solved it. We say so. The current necessary-condition theorem supplies a necessary legacy obstruction for the formal sleeper split; it does not by itself classify all monotonicity failures.

---

#### 7. Limitations

1. **Strict-refinement result**. Legacy monotonicity-failure is necessary for the formal sleeper split but not sufficient. The current substrate proves a counterexample to the converse via `permitEscalateOnly`.

2. **Diagnostic is on extracted subject, not on model**. The formal diagnostic lives at the audit pipeline's view of the represented deployment surface. Whether the underlying model has internal sleeper-agent training structure is empirical and out of scope.

3. **Fixed claim corpus per evaluation**. The on-check theorem is per-corpus: it evaluates whether the subject admits deceptive deployment on a *given* claim corpus. The canonical version (`AdmitsDeceptiveDeployment`) specializes to `auditGraphClaims subject`; it does not range over arbitrary corpora. Coverage of alternate extraction corpora is open.

4. **Deterministic graph extraction**. The `AuditGovernanceGraph` substrate is deterministic. Probabilistic graph extractions, e.g., sampling-based deployment policies, require a probabilistic-extraction substrate not in the current audit pipeline.

5. **Hubinger-style slice scope**. The lemma `hubinger_deception_subsumed_by_kernel_substrate` covers only the repository-defined `HubingerDeceptionScenario`, whose fields already include the formal sleeper split. Coverage of the full diversity of empirical sleeper-agent scenarios is not claimed.

6. **No empirical claim**. We do not predict empirical detection performance. The legacy diagnostic is a typed property of the represented audit subject; whether it correlates with empirical positives at scale is for empirical evaluation to determine.

7. **No claim about model internals**. The audit signature is on the extracted graph. We do not connect the signature to internal model structure (e.g., circuit analysis, residual-stream features). Bridge to model internals is open follow-up.

---

#### 8. Conclusion

We discharge a necessary-condition theorem for the formal sleeper split: every represented audit subject that admits deceptive deployment on the fixed corpus and trigger pair must fail legacy audit-graph monotonicity on that corpus. The check is decidable, sound, complete, and `native_decide`-evaluable on rational-arithmetic corpora. A concrete represented sleeper-agent split in the audit pipeline demonstrates the diagnostic on the repository's synthetic deployment-trigger pattern.

The diagnostic is on the *extracted* audit subject, not on the underlying model. It is a typed property of the audit pipeline's rule-layer view of the represented deployment slice. It pairs naturally with empirical detection methods: empirical bounds at the channel layer, structural diagnostics at the rule layer, as a complementary detection surface, not a replacement.

The current theorem is a strict-refinement result. Not every monotonicity-failing subject admits the formal deceptive-deployment predicate; the open work is a narrower obstruction taxonomy, not proving the false current converse.

The legacy diagnostic is a typed, decidable, reproducible property of the audit pipeline's view of a represented deployment slice. It is information at the rule layer that the behavioral channel does not provide, but the schema-derived pass result prevents reading it as a universal semantic sleeper-agent signature.

---

#### References

- **Brown-Cohen, J., Irving, G., Piliouras, G.** (2025). Avoiding Obfuscation with Prover-Estimator Debate. *arXiv:2506.13609*.
- **Greenblatt, R., Shlegeris, B., et al.** (2023). AI Control: Improving Safety Despite Intentional Subversion. *arXiv:2312.06942*.
- **Hubinger, E., van Merwijk, C., Mikulik, V., Skalse, J., Garrabrant, S.** (2019). Deceptive Alignment. *AI Alignment Forum*.
- **Hubinger, E., Denison, C., Mu, J., et al.** (2024). Sleeper Agents: Training Deceptive LLMs that Persist Through Safety Training. *arXiv:2401.05566*.
- **Korbak, T., Clymer, J., Hilton, B., Shlegeris, B., Irving, G.** (2025). A sketch of an AI control safety case. *arXiv:2501.17315*.
- **Anthropic** (2025). Reasoning Models Don't Always Say What They Think. *arXiv:2505.05410*.
- **Anthropic / multi-author** (2025). Chain of Thought Monitorability: A New and Fragile Opportunity for AI Safety. *arXiv:2507.11473*.

##### Lean substrate references

- `Legitimacy.AdmitsDeceptiveDeployment`
- `Legitimacy.AdmitsDeceptiveDeploymentOn`
- `Legitimacy.AuditGraphMonotonicity`
- `Legitimacy.deceptive_deployment_on_not_audit_monotone`
- `Legitimacy.deceptive_deployment_not_audit_monotone`
- `Legitimacy.admitsDeceptiveDeploymentCheck`
- `Legitimacy.admitsDeceptiveDeploymentCheck_iff_AdmitsDeceptiveDeployment`
- `Legitimacy.admitsDeceptiveDeploymentCheck_sound`
- `Legitimacy.admitsDeceptiveDeploymentCheck_complete`
- `Legitimacy.sleeperAgentAdmitsDeceptiveDeployment`
- `Legitimacy.sleeperAgentAdmitsDeceptiveDeploymentCheck`
- `Legitimacy.thresholdOnly_passes_monotonicity`
- `Legitimacy.permitEscalateOnly_fails_monotonicity`
- `Legitimacy.sleeperAgentExtractedGovernanceGraph`
- `Legitimacy.sleeper_agent_canonical_governance_verdict`
- `Legitimacy.sleeper_agent_monotonicity_verdict`
- `Legitimacy.sleeper_agent_baseline_original_permit`
- `Legitimacy.sleeper_agent_baseline_strengthened_deny`
- `Legitimacy.hubinger_deception_subsumed_by_kernel_substrate`
- `Legitimacy.sleeper_agent_hubinger_bridge_witness`
- `Legitimacy.inert_sleeper_shape_not_hubinger_deception_scenario`

## 4. Constitutional AI Lineage

### Constitutional AI Lineage Realization

#### Scope

Constitutional AI, in the sense of Bai et al. 2022 (arXiv:2212.08073), is a
training method rather than a deployment governance structure. The formal
realization in `Legitimacy.Behavioral.ConstitutionalAILineage` therefore models
the deployment-side audit subject: a model-mediated policy over audited claims.

The class predicate is now constitutional rather than merely flat:

- audited claims resolve through a finite `Constitution` of `Principle` objects;
- the conflict relation is a partial order, and each claim's quotient class is
  determined by its resolved principle;
- `HarmCategoricalClaim` and `BenignClaim` are compatibility projections from
  the resolved principle's binary verdict;
- a deployed Constitutional-AI-style policy escalates or denies harm-categorical
  claims;
- the same policy permits benign claims;
- the behavioral game exposes executable audit perturbations whose amplitudes
  are bounded by the spectral node-removal perturbation budget.

What this establishes is narrower than model alignment: a deployment audit
subject with this policy shape has a derived `SpectralBehavioralEmbedding`, and a
policy respecting the resolved principle verdict receives an admissible substrate
verdict at positive well-conditioned `c ≤ C*`, without proving that the
underlying model is aligned.

#### Formal Objects

The primitive class vocabulary is built from a finite constitution quotient.
A `ConstitutionalAIClaimClass` resolves through a `Constitution` of `Principle`
objects under the partial-order conflict relation captured by
`ConstitutionallyRespectsResolution`, and the deployment side is modeled by a
`ConstitutionalAITrainedAuditSubject`. The two lineage layers are the
behavioral `ConstitutionalAIBehavioralLineage` and the capability-scaled
`ConstitutionalAICapacityLineage`.

The old harm/benign partition is retained as
`ConstitutionalAIClaimClass.ofFlat`, the two-principle constitution with a
single nontrivial edge from benign to harm-categorical. The policy surface
preserves escalation as a separate audit label through
`ConstitutionalAIDecision.escalate`, while `toBinary` maps both escalation and
denial to `BinaryDecision.Deny`.

The governance game is `ConstitutionalAIBehavioralLineage.toGame`. Agents select
claim-states and executable nonnegative audit amplitudes. Utility gain is exactly
the selected amplitude when the action targets the evaluated claim-state. The
governance decision is the deployed policy decision at that claim-state.

#### Embedding Derivation

The embedding fields are derived rather than bundled. The
`spectralBehavioralEmbedding` is assembled from four theorems over the
constructed game: `graph_decision_matches_game` ties the governance decision to
the game's best response, `perturbation_budget_reflects_best_response_gain`
bounds profitable gain by the node-removal perturbation budget, and the two
deviation lemmas `spectral_vulnerability_exposes_profitable_deviation` and
`spectral_threshold_violation_exposes_profitable_deviation` expose a profitable
deviation from spectral vulnerability and from a threshold violation
respectively.

The harm-categorical subgame has an explicit behavioral theorem:
`harmCategorical_subgame_decision_matches_best_response`. A positive
target-matching audit action against a harm-categorical claim produces a binary
denial, because direct denial and escalation both block deployment.

The capability-scaled layer adds the asymmetric boundary theorem: harm-
categorical claims remain denied at and below `C_star`, while benign response
matching is exactly the `C_star` transition. A constant-deny floor test records
that the benign side is not vacuous.

The strengthened policy theorem is
`constitutionally_respecting_policy_substrate_admissible`: a policy whose
binary deployment decision matches the verdict of the resolved principle cannot
hit either substrate rejection branch, so the well-conditioned positive
procedure returns an admissible verdict at every positive `c ≤ C*`.

The structural perturbation analog is
`perturbation_budget_reflects_best_response_gain`: every profitable behavioral
gain is bounded by the node-removal perturbation budget and therefore witnesses
`spViolation` at the same gain scale.

#### Regularity Residual

The bounded-action game does not claim unconditional
`BestResponseDecomposedRegularity`. That would be too strong: arbitrary
tolerance/capability pairs can demand a gain floor above every bounded
executable amplitude.

The formal residual is explicit. The file proves
`bestResponseDecomposedRegularity_of_zeroConsistencyVulnerability`, a conditional
certificate in the zero-consistency-vulnerability case, matching the Stackelberg
lineage pattern. With this realization in place, the substrate now carries two
concrete behavioral-lineage realizations: the Stackelberg node-removal lineage
and the Constitutional AI deployment-audit lineage.

#### Worked Witness

The concrete witness is `constitutionalAIWitnessLineage`:

- graph: `uniTriGraph`;
- signal: `sig`;
- harm-categorical claim: `0`;
- benign claims: all nonzero `Fin 3` claim-states;
- policy: deny claim `0`, permit the benign residual class.

The direct policy behavior is verified:

- `constitutionalAIWitness_harm_decision_denies`;
- `constitutionalAIWitness_benign_decision_permits`.

The substrate verdict is now capability-aware:

- `constitutionalAIWitness_cv_eq_one`;
- `constitutionalAIWitness_spViolation_one`;
- `constitutionalAIWitness_has_harmCategoryLeakPath`;
- `constitutionalAIWitness_substrate_verdict`;
- `constitutionalAIWitness_nonvacuous_profitable_deviation`.

The failure mode is not "the model is unaligned." The raw verdict rejects a
policy that permits harm-categorical claims with `harmCategoryLeakPath`, and a
policy that denies benign claims at a monotonicity certificate with
`overEscalationFalsePositiveResidual`. The trained triangle witness is
admissible under this certificate-aware verdict because it has neither policy
failure.

The five-node witness is `constitutionalAICapacityWitnessLineage`, over
`uniK5` and `sig5`, with harm claim `{0}` and benign claims `{1,2,3,4}`. It
reuses `fiveNode_cv_values`, has a non-vacuous profitable deviation at gain
`3 / 4`, and includes n=5 positive-procedure certificate inhabitants for the
existing exact `uniK5` half-signal channel calibration. The larger worked
witness declarations live in `Legitimacy.Behavioral.ConstitutionalAIWitnesses`
so the core lineage module stays below the repository file-size ceiling.

The Constitution-as-DAG witness is `threePrincipleConstitution3`. It has
helpfulness, privacy, and safety principles; claim `0` activates both
helpfulness and safety, and conflict resolution selects the safety denial
principle. `threePrincipleRespectingPolicy3_substrate_verdict` proves the
respecting policy admissible, while
`threePrinciplePermissivePolicy3_substrate_verdict` proves the permissive
non-respecting policy rejects with `harmCategoryLeakPath`.

The public Anthropic Constitution case study remains separate empirical work:
it should map the published prose artifact into this formal
principle/conflict-resolution substrate rather than treating the generic
Constitution-as-DAG theorem as an empirical extraction.

## 5. Decomposition Attack Bridge

### Decomposition Attacks and the Kernel Block-or-Sacrifice Disjunction

---

#### Abstract

This note records a bridge between two existing formal vocabularies. The first
is the per-step `Decision3` algebra in `Legitimacy.Attacks.Decomposition`, which
defines composition-sensitive semantic monotonicity and decomposition witnesses:
nonempty action sequences where each local step permits while the composed
endpoint is denied. The second is the monitored kernel-sacrifice API in
`Legitimacy.Safety.KernelSafety.Sacrifice`, which classifies raw kernel steps as
either boundary preserving or as steps where a monitored sacrifice certificate
has surfaced.

The bridge theorem says that, for an invariant source kernel datum, a realized
decomposition attack is exposed to the kernel API as either (1) a preserved
kernel boundary, or (2) a monitored sacrifice certificate whose tag is exactly
`SacrificedAxiom.kernel KernelAxiom.CompositionalSafety`. The theorem states
what the kernel API exposes rather than serving as an a priori detector for
every possible attack. When the realization relation supplies the decomposition
witness and the raw-step monitor/extractor hypotheses are available, the API
exposes a disjunction: block or sacrifice.

The realization relation is named `DecompositionAttackRealizesKernelStep`. It is
required because an abstract `DecompositionAttackClass` alone can be inhabited
independently of the kernel transition being certified, so the certificate now
consumes the realized witness, not just any witness of the same algebra.

#### Formal Location

The definitions and theorems live in four files. `lean/Legitimacy/Attacks/Decomposition.lean`
adds the predicate layer, `lean/Legitimacy/Bridges/DecompositionAttackKernelBridge.lean`
adds the bridge theorem and the concrete fixtures, and `lean/Legitimacy.lean`
roots the bridge in the umbrella import. This paper is the human-facing artifact.
The theorem is rooted through the normal `Legitimacy` target, and the bridge
module also has its own build target.

The proof does not edit the kernel safety API. That matters because the
classifier already fixes the shape of the evidence, and the present substrate
does not expose a compiled per-step decision-policy surface whose action type can
be identified with the decomposition action type. Accordingly,
`DecompositionAttackRealizesKernelStep` records the strongest relation available
at this layer: the realized decomposition witness is stored with the concrete
`KernelStep`, the decomposition unit is grounded by an extractor from the source
kernel datum, the step replay equation is carried in the relation, and any
populated failed-property payload is proved against the governed graph for that
same step. The stronger action-policy realization remains a follow-up to expose
that policy surface at the compiled-governance layer.

#### Predicate Layer

The decomposition module already had the core objects.
`CompSemanticMonotone compose unit node denied` says that if a full sequence
lands in the denied set, then the last local step of that sequence cannot be
`Decision3.Permit`. `Decomposition compose unit node denied` packages a
counterexample pattern: it stores a nonempty list of actions, a proof that every
local step permits, and a proof that the composed endpoint is denied.

The new bridge-facing predicates are thin but load-bearing.
`LocalPermissionMonotonicity` is the failure of `CompSemanticMonotone`, and
`DecompositionAttackClass` is `Nonempty (Decomposition compose unit node denied)`.
That definition is intentionally rooted in the embedded structure rather than a
free-standing Boolean flag: the structure carries the sequence, the local permit
proofs, and the denied endpoint proof.

The nonvacuity probe instantiates a constant one-step kernel. The composition is
`fun s _ => s`, the unit state is `()`, the local node always returns
`Decision3.Permit`, and the denied predicate is always true, so the singleton
action sequence is a concrete witness. This establishes that the attack-class
predicate is inhabited without importing any kernel-safety facts, and that the
predicate is not definitionally false.

#### Strictness

The decomposition class is stricter than monotonicity failure. The strictness
theorem uses a two-step counterexample over a natural-number state: composition
increments the state by one, the denied endpoint is state `2`, and the local
node permits exactly at state `1`. The two-step sequence reaches the denied
endpoint and its final local step is permitted, so composition-sensitive
semantic monotonicity fails. A decomposition attack, however, cannot exist: any
denied witness must have length two, and at the first local step the prefix state
is `0`, where the node denies, so the requirement that every local step permits
is impossible. This proves strict refinement — not every monotonicity failure is
a decomposition attack — mirroring the strict-refinement pattern of the
sleeper characterization layer (see §3). The point is polarity control: the
decomposition class is a positive structural witness, while plain monotonicity
failure is weaker.

#### Kernel API Surface

The kernel-side classifier is `classify_raw_step`. It consumes a raw step, a
source invariant, and monitor/extractor hypotheses, and returns either
`RawKernelStep.KernelBoundaryPreserved step` or
`RawKernelStep.IndexedSacrificeSurfaced step`. The classifier remains a separate
API; it does not derive monitor evidence from an arbitrary decomposition class.

The current monitored certificate type stores a `KernelStep`, and every
`KernelStep` carries enough target-invariant evidence to preserve the kernel
boundary from a source invariant. That substrate blocks the stronger raw-step
statement where a decomposition attack alone would force classifier
compatibility. The bridge therefore separates two facts: it does not add axioms,
and it does not hide the old classifier compatibility premise. The direct
certificate theorem consumes the realization relation, whose embedded witness is
the single source for the attack class used internally. The theorem statement is:

```lean
theorem decompositionAttackClass_constructs_compositionalSafetyCertificate
    {n : Nat} {sys : GovernedSystem n}
    {D D' : LegitimacyKernelData sys} (step : KernelStep D D')
    (claim_profile : List ClaimQ)
    (claimant : ClaimantId)
    (compiled : CompiledGovernance)
    (monitoring : MonitoringPlan)
    (hgraph : compiled.graph = sys.graph)
    {compose : σ → α → σ} {unit : σ}
    {node : σ → α → Decision3} {denied : σ → Prop}
    (hrealize :
      DecompositionAttackRealizesKernelStep step compose unit node denied) :
    ∃ cert : MonitoredSacrificeCertificate D D',
      cert.sacrificed =
        SacrificedAxiom.kernel KernelAxiom.CompositionalSafety
```

The compatibility restate is named:

```lean
theorem decompositionAttackClass_compositionalSafety_retag
```

It still takes the raw-step monitor/extractor hypotheses, and its surfaced
branch now also requires a realization relation for the surfaced kernel step.
The headline alias is:

```lean
theorem decomposition_attack_blocked_or_sacrificed
```

Its name records that it retags an already surfaced monitor branch rather than
deriving classifier compatibility from the attack class.

#### Proof Sketch

The direct certificate proof first extracts a witness step from the admitted
realization relation. The extracted witness records the embedded `Decomposition`,
an index into its nonempty step list, the local `Decision3.Permit` proof at that
index, a step-index ordering proof that no earlier local step returned
`Decision3.Deny`, and the denied composed endpoint. The certificate monitor event
is:

```lean
DecompositionKernelViolationFired compose unit node denied ∧
  LocalPermissionMonotonicity compose unit node denied
```

The local monotonicity failure is derived internally by
`localPermissionMonotonicity_of_decompositionAttackClass`, which applies the
contrapositive shape of `csm_no_permitting_decomposition`. The attack-class
predicate supplied to that helper is `Nonempty.intro hrealize.witness`, so the
caller no longer supplies a separate attack-class or `hcsm` hypothesis for the
certificate path. The certificate's sacrifice tag is:

```lean
SacrificedAxiom.kernel KernelAxiom.CompositionalSafety
```

The compatibility restate applies `classify_raw_step`. In the boundary case it
returns the boundary disjunct; in the surfaced-monitor case it builds the
compositional-safety certificate from the surfaced transition payload and the
realized decomposition witness. That theorem is deliberately named as a retag.
The direct theorem is the one that consumes the realized decomposition semantics
into the monitored certificate, while the classifier restate records the current
raw-step API boundary.

#### Why the Certificate Is Explicit

The right disjunct is not:

```lean
Nonempty (MonitoredSacrificeCertificate D D')
```

That would lose the indexed sacrifice identity.

The theorem instead returns:

```lean
∃ cert : MonitoredSacrificeCertificate D D',
  cert.sacrificed =
    SacrificedAxiom.kernel KernelAxiom.CompositionalSafety
```

This keeps the sacrifice tag visible in the theorem type, lets downstream users
pattern-match on the exact kernel axiom, and prevents the theorem from being
satisfied by an unrelated governance property sacrifice.

The bridge uses `decompositionRealizationBoundExceedance` as the monitoring
payload. That constructor routes the optional failed-property slot through
`DecompositionAttackRealizesKernelStep`. For kernel-obligation sacrifices, the
slot may be empty because `GovernanceProperty` does not include kernel
compositional safety; when the realization supplies a governance property, the
constructor proves that the property fails on the compiled graph tied to the same
governed system. The constructed certificate records the usual runtime
observation and ledger emission through existing helper constructors.

#### Sleeper Fixture Lift

The bridge module also lifts the concrete sleeper audit subject (see §3) into the
decomposition state. The state is `SleeperDeploymentState`, which carries the
represented sleeper audit subject, the training/deployment phase, and the audit
claim corpus being evaluated. The unit is the sleeper audit subject in training
phase with its canonical audit claims, and the action type has a single
deployment action whose composition applies the concrete deployment-claim update
from `DeceptiveDeploymentWitnessOn`. The local node permits the action during
training and denies it after the deployment phase has been reached, and the
denied predicate is tied to the concrete affected claimant in the sleeper
witness: the subject is `sleeperAgentExtractedGraph`, the phase is deployment,
the claims are the witness's deployment claims, and the affected claimant's
deployment decision is `deny`.

The singleton deployment action therefore witnesses the decomposition class using
sleeper-specific training/deployment structure rather than a constant
always-permit endpoint, and the local monotonicity failure is derived from that
attack class by `localPermissionMonotonicity_of_decompositionAttackClass`. The
bridge file also includes a native finite check: the sleeper subject passes the
compositional-safety audit check and admits the represented deceptive deployment
predicate. That reproduces the already-existing distinction that the audit-level
sleeper predicate and the graph compositional-safety check are not the same
property.

#### Branch Fixtures

Two branch witnesses are provided. The block fixture uses the non-reflexive raw
widened-signal mutation from `exampleGovernanceKernelData` to
`exampleGovernanceWideSignalKernelData`. The boundary fact is not identity: it is
supplied by the independently established target semantic-kernel witness for
`exampleGovernanceWideSignalKernelData`, and the fixture returns the
boundary-preserved disjunction by that target invariant. The sacrifice fixture
uses the concrete non-reflexive kernel step over the same widened-signal target,
constructs the compositional-safety certificate directly from the decomposition
witness, and no longer supplies that certificate back into the classifier as the
monitor hypothesis.

Both fixtures are theorem-level witnesses. Small `native_decide` checks evaluate
the branch selectors used by the fixtures, but the proof-carrying theorem
statements remain the authoritative artifacts. The current kernel-sacrifice
payload cannot always record a property-level `failedProperty = some ...` for a
kernel-axiom sacrifice, because `MonitoringBoundExceedance.failedProperty` is
property-specific while `KernelAxiom.CompositionalSafety` is a kernel obligation.
The sacrifice fixture is therefore non-self-referential and non-reflexive, and
the bound is still routed through `DecompositionAttackRealizesKernelStep`; the
property slot is empty for that fixture because the compiled example graph has no
governance-property failure to record.

#### Relation to Sleeper-Agent Work

The sleeper-agent scope: the narrow structural audit slice over a dormant
training trigger, a deployment trigger, and a permit-to-deny change under a
positive deployment perturbation, and the disclaimers that it models neither
learned objectives nor training dynamics nor a hidden deployed objective, is
set out in §3. Here that existing audit predicate is used only as a concrete
fixture. The decomposition bridge itself is algebraic and kernel-relative, so the
connection is one of substrate compatibility, not a claim of full behavioral
coverage.

#### Relation to `noUndeclaredSacrifice`

The no-undeclared-sacrifice theorem concerns live compiled governance surfaces:
it says that, under the peer-relative live-surface hypotheses, forced sacrifices
are declared. The present bridge is different. It concerns raw kernel steps and
monitored kernel certificates, and it says that, once the realization relation
supplies the decomposition witness and the classifier inputs are present, the
kernel step is boundary preserving or exposes a compositional-safety sacrifice.

The two theorems are compatible: declaration discipline for compiled governance
surfaces in one case, block-or-sacrifice classification for kernel transitions in
the other. Both are polarity-honest, and neither claims omniscient attack
detection.

#### What the Bridge Does Not Prove

The bridge does not prove that every system with a sleeper-shaped story is
automatically detected. It does not prove that every monotonicity failure is a
decomposition attack; the strictness theorem proves the opposite. It does not
prove that a raw step can be classified without a source invariant, since the
existing classifier requires that premise. It does not replace the
monitor/extractor hypotheses, which remain explicit. It does not change the
kernel API; it composes with it. And it does not use an arbitrary bundled
existence claim for the sacrifice branch — the exact certificate tag appears in
the type.

#### Conclusion

The formal contribution is a bridge theorem: a realized decomposition attack at
the kernel step boundary, a source kernel invariant, and raw-step
monitor/extractor compatibility together imply the kernel
block-or-compositional-sacrifice disjunction. The construction is small because
the endpoints already existed; the work was in aligning their polarity. The
decomposition module supplies structural attack witnesses, the sacrifice module
supplies monitored kernel certificates, and the bridge turns a surfaced monitor
event into an exact `KernelAxiom.CompositionalSafety` sacrifice certificate.

The theorem is constructive with the source-invariant premise. The missing
premise in the shorter informal signature remains an explicit residual
requirement of the current classifier API. That is the honest boundary of the
result.

## 6. Codex Harness Worked Example

### Codex Harness Case Study

#### 1. Extracted graph and detected failure

This case study starts from the committed extracted Codex hooks governance
artifact at `examples/graphs/codex-graph.json` and its Lean literal in
`lean/Legitimacy/Results/CodexAdmissibilityAudit.lean`. The artifact currently
contains sixteen hook nodes and eight pass-through hook edges. The byte-stable
JSON and Lean literal both show sixteen nodes, while the audit surface has 29
claims and five numeric metric fields.

The first Lean stage does not introduce a new diagnostic. It reuses the
production governance admissibility evaluator and restates the existing theorem
as the first link in the case-study chain:
`codexHarness_stage1_detects_monotonicity_failure`. The theorem pins the
verdict to `AuditVerdict.rejected AuditCheck.monotonicity`, so the case study
begins from an extracted harness failure rather than a hand-built toy example.

#### 2. Critical capability threshold

The second Lean stage projects the extracted Codex hook graph into the spectral
governance API used by `CriticalCapability.lean` and
`StackelbergConvergence.lean`. The derived projection
`codexHarnessDerivedSpectralGraph` keeps all eight extracted pass-through hook
pairs, while the legacy hand-authored ten-node carrier retained for citation
stability kept five of the eight. The derived signal
`codexHarnessDerivedFailureSignal` is computed from the extracted nodes: callback
nodes contribute zero and registration nodes contribute the
`hook_registration`/`.escalate` threshold component.

The derived carrier is intentionally disclosed as disconnected: it consists of
eight `K₂` components, so `λ₂ = 0`. The Stage 2 `cv`, `C*`, and
Stackelberg-limit results used here are connectivity-free and consume only the
positive-CV hypothesis; the positive-spectral-gap lower-bound theorems are not
instantiated for this carrier.

For this projection, Lean computes the exact consistency vulnerability as
`cv = 1`. With the case-study tolerance `delta = 1/10`, the reciprocal critical
capability is therefore `C_star = delta / cv = 1/10`, or `0.1` in decimal
notation. The theorem `codexHarnessDerived_stage2_threshold` imports the existing
`C_star_exists` critical threshold: below this value the capability-scaled
perturbation is unreachable, while at and above it the spectral violation
exists. The follow-on theorem
`codexHarnessDerived_stage2_stackelberg_eventual_instability` connects the same
positive-CV fact to the Stackelberg-limit surface: stable spectral equilibria
eventually disappear at high capability.

#### 3. Repaired routing lattice

The chosen repair is the explicit downstream adjudication route. Terminal
escalation alone is not enough for Codex, because the extracted graph also has
metric thresholds that the legacy monotonicity perturbation interprets as
positive strengthening even when the field is adverse evidence or routing
metadata. In the repaired typed graph, threshold matches are not terminal
deny/escalate outcomes. They are treated as adjudicated evidence, and the graph
then appends an explicit permit adjudication suffix for former terminal callback
nodes.

This repair is intentionally scoped. It is a typed substrate repair used by the
case study, not a claim that the live Codex vendor protocol already exposes this
adjudication node. It leaves hard content-match deny routes untouched and keeps
the synthetic workload at 29 claims. The graph shape changes from sixteen nodes
and eight edges to seventeen nodes and sixteen edges: the original eight hook
edges remain, and eight former terminal callback nodes feed the explicit
adjudication suffix.

#### 4. Load-bearing repaired admissibility theorem

The final Lean stage proves the verdict flip on the repaired typed graph through
an explicit spectral-to-audit chain. The theorem
`codexHarness_repaired_spectral_zero_derives_monotonicity_pass` consumes the
coordinatewise zero repaired spectral signal, exposes the concrete
monotonicity-core evaluator, and then unfolds the production
`auditCheckStatus` dispatcher through its acyclic monotonicity branch. The
parallel theorem `codexHarness_repaired_spectral_zero_derives_nonvacuity_pass`
uses the same zero signal through the nonvacuity core.

The main bridge theorem is
`codexHarness_stage4_threshold_removed_derives_finite_audit`. Its proof uses
Stage 2 threshold removal to obtain zero repaired CV, converts zero CV to
coordinatewise zero signal on the concrete Codex spectral projection, derives
monotonicity and nonvacuity passes from that signal, and composes the named
per-check statuses through `firstFailedAuditCheck?` and
`governanceAdmissibilityVerdict`. The older `packaged_with` theorem names remain
as compatibility aliases, but they now delegate to the load-bearing derivations.

This is the intended case-study endpoint: fixture, detection, threshold, repair,
and repaired verdict are all named Lean declarations. The repaired verdict is
not assumed and is not discharged by bundling unrelated witnesses. It is derived
through the repaired typed graph's finite audit evaluators, while the original
extracted Codex graph remains untouched and still has the Stage 1 monotonicity
rejection.

## 7. Self-Modification Boundary and Lifecycle

### The Indexed Override-Removal Boundary and No-Silent-Degradation Lifecycle

---

#### Abstract

This chapter records two named structural results about self-modifying governance policies. The first is a finite-trajectory *escape boundary*: if a governance graph starts with a binding override and any finite self-modification action sequence later permits a previously denied claim, then the trajectory must contain a concrete override-removal action at a concrete index, with the pre-removal graph reached by the action prefix and the removing action identified by list lookup. The second is a *lifecycle no-silent-degradation* disjunction: over any finite trajectory of proof-carrying policy transitions, either every transition preserves the kernel boundary, or some transition surfaces an indexed override-removal sacrifice tied to a decision-observable authority-surface change. Both results are general over the action space; neither is a finite-table enumeration. The lifecycle is demonstrated on a worked sleeper-shaped trajectory whose silent-activation transition provably cannot inhabit the transition contract. The connector from bundled kernel self-modification to the lifecycle layer uses a graph-identity action space, which is the honest scope limit of that bridge.

---

#### 1. What the results say

The self-modification substrate asks a narrow question: under what structural condition can a governance graph that initially denies a claim, by overriding it, ever be self-modified into permitting that claim? The answer is sharp and constructive, localizing escape to a single removal step rather than smearing it across the trajectory.

The escape boundary is the contrapositive of an override-preservation guarantee. If the action space globally preserves overrides, no finite self-modification trajectory can ever permit an initially overridden claim — every claim is denied after every action sequence. The escape boundary names exactly what must occur for that guarantee to fail.

#### 2. The indexed escape-boundary theorem

**Theorem 7.2** (Indexed override-removal escape boundary, `selfmod_escape_requires_indexed_override_removal_step`, `lean/Legitimacy/Results/SelfModBoundary.lean`).
*Let `G : GovernanceGraph` have a binding override, `space : AgentActionSpace`, `actions : List space.Action`, and a claim corpus and claimant. If applying the full action sequence to `G` permits the claimant, then there exist an index `i`, an action `a`, and an intermediate graph `H` such that `H` is exactly the graph reached by the prefix `actions.take i`, the lookup `actions[i]?` returns `a`, `H` still has the override, and applying `a` to `H` removes it.*

The result is general over the action space: `space` is an arbitrary `AgentActionSpace` and `actions` is an arbitrary finite list, with no restriction on the graph's node count. The proof is by induction on the action list, splitting on whether the head action already destroyed the override. The unindexed companion `selfmod_escape_requires_override_removal_step` (`lean/Legitimacy/Results/SelfModBoundary.lean`) forgets the index and returns just the witness action and intermediate graph.

The contrapositive direction is the preservation guarantee `no_selfmod_permit_under_override_preservation` (`lean/Legitimacy/Results/SelfModBoundary.lean`): under a global `OverridePreserving space` hypothesis, every claim is denied after every action sequence. Its companion `selfmod_permit_refutes_override_preservation` (`lean/Legitimacy/Results/SelfModBoundary.lean`) reads the same fact in refutation form: any escape refutes global override preservation. The override-corrigibility characterization `not_overrideCorrigible_of_override_decomposition` (`lean/Legitimacy/Results/SelfModBoundary.lean`) states that, for an initially overriding graph, failure of override corrigibility is exactly the existence of a single override-removing action.

This is a structural boundary on the represented graph and action space. It does not model learned objectives, training dynamics, or the internal structure of a self-modifying model. It says: in the typed substrate, an authority escape cannot be smeared across a trajectory — it has a concrete removal step.

#### 3. The lifecycle no-silent-degradation theorem

A `PolicyState` (`lean/Legitimacy/SelfModificationLifecycle.lean`) packages a label, an extracted kernel artifact, and the effective authority surface a learned policy exposes at activation time. A proof-carrying lifecycle transition is a `PolicyTransition` (`lean/Legitimacy/SelfModificationLifecycle.lean`), whose contract field requires each step to either preserve the kernel boundary or surface an indexed override-removal sacrifice. The kernel-preservation branch is `KernelBoundaryPreserved` (`lean/Legitimacy/SelfModificationLifecycle.lean`): both endpoints are semantic kernels and there is no decision-observable authority-surface change. The sacrifice branch is `IndexedSacrificeSurfaced` (`lean/Legitimacy/SelfModificationLifecycle.lean`): a decision-observable surface change paired with an `IndexedOverrideRemovalEvent` (`lean/Legitimacy/SelfModificationLifecycle.lean`) carrying the same indexed removal witness as the escape boundary.

**Theorem 7.3** (Lifecycle no-silent-degradation, `policy_lifecycle_no_silent_degradation`, `lean/Legitimacy/SelfModificationLifecycle.lean`).
*For any `PolicyTrajectory`, the lifecycle conclusion holds: the trajectory's initial-state and successive-state continuity invariants hold, and either every transition preserves the kernel boundary, or some transition surfaces an indexed sacrifice together with a decision-observable authority-surface change.*

The result is general over the trajectory: it ranges over any finite list of proof-carrying transitions, proved by induction over the transition list via `classify_raw_policy_transition` (`lean/Legitimacy/SelfModificationLifecycle.lean`). The headline dispatch `lifecycle_no_silent_degradation` (`lean/Legitimacy/SelfModificationLifecycle.lean`) routes both the raw classifier-backed and proof-carrying trajectory forms through a typeclass. The per-transition closure `effective_surface_change_requires_indexed_event` (`lean/Legitimacy/SelfModificationLifecycle.lean`) is the load-bearing step: any decision-observable surface change forces the indexed-sacrifice branch, so the contract has no third option that silently changes authority without surfacing the indexed event.

#### 4. The worked sleeper trajectory and the impossibility witness

The lifecycle is demonstrated on a concrete trajectory `sleeperLifecycleTrajectory` (`lean/Legitimacy/SelfModificationLifecycle.lean`): a benign update with an unchanged surface, an honest sacrifice that surfaces the override-removal event before activation, and a post-sacrifice audit hold over the now-current surface. Its no-silent-degradation conclusion is discharged in `sleeperLifecycleTrajectory_no_silent_degradation` (`lean/Legitimacy/SelfModificationLifecycle.lean`).

The sharp witness is the impossibility theorem `sleeper_attempt_cannot_satisfy_contract` (`lean/Legitimacy/SelfModificationLifecycle.lean`): a sleeper-shaped transition that changes the effective authority surface, refuses to surface the indexed sacrifice, and does not preserve the kernel boundary derives `False`. A silent sleeper activation provably cannot inhabit the transition contract. The complementary tightness witness `unchecked_boundary_breach_allows_silent_shape` (`lean/Legitimacy/SelfModificationLifecycle.lean`) shows that removing the bounded extractor contract is what would re-admit a silent shape, so the contract is load-bearing rather than decorative.

#### 5. Honest scope of the kernel connector

The connector from a bundled `LegitimacyKernel` self-modification trajectory to the policy-lifecycle layer is `policyTransitionOfKernelSelfmod` (`lean/Legitimacy/SelfModificationLifecycle.lean`), with corollary `kernel_selfmod_policyTransition_corrigibility` (`lean/Legitimacy/SelfModificationLifecycle.lean`): the connector transition preserves the lifecycle kernel boundary, and the original kernel self-modification theorem supplies the supervisory-algebra corrigibility invariant for the same action list. This connector uses a *graph-identity* action space `graphIdentityActionSpaceFromState` (`lean/Legitimacy/SelfModificationLifecycle.lean`): because the underlying kernel self-modification result tracks preservation of the supervisory algebra rather than graph rewrites, the adapter exposes the action list through an action space whose `apply` leaves the binary authority surface unchanged, and therefore takes the kernel-preservation branch. That is the honest scope limit of the connector: it does not lift arbitrary graph-rewriting self-modification into the lifecycle, only the supervisory-algebra-preserving case under the identity surface map. The escape boundary and lifecycle disjunction themselves remain general over the action space; the connector is the narrower bridge.

#### 6. What these results are not

These are structural results on represented governance graphs, action spaces, and policy transitions. They do not establish that a deployed model has no hidden objective, do not model training-time-versus-deployment-time learning, and do not constitute an empirical sleeper-agent detector. The genuinely staged reflective and ASI-signature work that these objects are intended to support is not discharged here and is not surfaced as done. What is discharged is precise and reproducible: an indexed escape boundary general over the action space, a no-silent-degradation lifecycle disjunction general over the trajectory, a worked sleeper trajectory, and a proof that a silent sleeper activation cannot inhabit the lifecycle contract.

---

##### Lean substrate references

- `Legitimacy.selfmod_escape_requires_indexed_override_removal_step`
- `Legitimacy.selfmod_escape_requires_override_removal_step`
- `Legitimacy.no_selfmod_permit_under_override_preservation`
- `Legitimacy.selfmod_permit_refutes_override_preservation`
- `Legitimacy.not_overrideCorrigible_of_override_decomposition`
- `Legitimacy.policy_lifecycle_no_silent_degradation`
- `Legitimacy.lifecycle_no_silent_degradation`
- `Legitimacy.classify_raw_policy_transition`
- `Legitimacy.effective_surface_change_requires_indexed_event`
- `Legitimacy.sleeperLifecycleTrajectory_no_silent_degradation`
- `Legitimacy.sleeper_attempt_cannot_satisfy_contract`
- `Legitimacy.kernel_selfmod_policyTransition_corrigibility`

## 8. Conclusion: Rule-layer Audits as a Program

Taken together, the case studies show what a structural audit adds once a safety mechanism has been represented as a typed rule layer. The audit can distinguish a genuine schema-aware verdict from a polarity artifact, expose a decomposition event as a compositional-safety sacrifice, and localize represented self-modification escape to an indexed override-removal step under a no-silent-degradation lifecycle. Its conclusions remain conditional on the trusted representation boundary stated in each case; within that boundary, the common contribution is a rerunnable certificate rather than an informal judgment about the mechanism.

---

*Part of the Legitimacy program: a machine-checked semantic legitimacy kernel with a Rust extractor and Lean 4 proofs. Repository: github.com/abenenson/legitimacy; project page: adambenenson.com/projects/legitimacy. Companion manuscripts: "Semantic Legitimacy Kernels: A Machine-Checked Compiler Target for the Governance Layer of AI Agents," "A Verified Impossibility Theorem for Peer-Relative Governance," and "Which Governance Structures Survive Unbounded Capability? Capacity and Stability Bounds for AI Governance Graphs."*
