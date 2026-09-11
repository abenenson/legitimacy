# The Legitimacy Program in Context: Social Choice, Guaranteed-Safe AI, and the Verification Trilemma

*Adam Benenson, 2026*

## 1. Introduction: Positioning the Program

The Legitimacy program sits on the formal-methods side of AI safety: it supplies a typed rule-layer audit and theorem surface, not a universal account of alignment verification. Five comparisons locate that contribution. The prior-art chapter names the voting-theory, social-choice, verification, and alignment lineages. The GS-AI chapter identifies the legitimacy kernel as one static-snapshot verifier-target instance. The verification-trilemma chapter records the current bounded-domain result: decision-definedness is the only independently variable clause proved so far, soundness follows from decision-definedness, unrestricted generality is definitionally unavailable, and polynomial-time tractability remains open. The two-`C*` chapter separates related capacity notions. The three-axis chapter places the reachable scarce peer-relative governance-rule impossibility, under transparent-prefix and non-denying-suffix scope, between Arrow-style aggregation and Balinski-Young-style allocation.

Together, these comparisons distinguish the program's theorem object from its nearest neighbors while keeping its scope explicit.

## 2. Prior Art and Adjacent Programs

### 2.1 The organizing frame: four axes of AI-governance impossibility

AI-governance impossibility results now form a growing line rather than a single "first" claim. The following four axes organize several relevant lineages; they are a selective map, not an exhaustive taxonomy or a claim of priority over agent-governance impossibility work.

- The **preference-aggregation axis** imports Arrow-style social-choice impossibility into preference and reward space. Eckersley (2019) imports Arrow-style social-choice impossibility into AI value alignment in utility space; Conitzer et al. (2024), Ge-Halpern et al. (2024, NeurIPS 2024), and Qiu (2024; JAIR; Best Paper at NeurIPS 2024 Pluralistic Alignment Workshop) extend that lineage into preference and reward space and prove Arrow-like representational impossibilities in their respective formal settings.
- The **agreement-complexity axis** proves alignment lower bounds through agreement and communication complexity. Nayebi's "Intrinsic Barriers" (2025, AAAI 2026) is distinct in proof technique.
- The **accountability-allocation axis** proves an impossibility on accountability allocation in human-agent collectives above an autonomy threshold. Tibebu's "The Accountability Horizon" (2026) is the representative result. The RLHF trilemma paper (Sahoo et al., 2025) formalizes a distinct impossibility inside preference-learning pipelines.
- The **governance-rule structural-admissibility axis** is legitimacy's distinct contribution in this public-literature map: a formally verified Arrow-template graph-diagnostic impossibility on the structural admissibility of the deployed governance rule itself, for reachable scarce peer-relative decisive stages under transparent-prefix and non-denying-suffix scope, with strategyproofness derived by `solidarity_monotonicity_imply_strategyproof`, coupled to a byte-stable extractor and a spectral scaling theory (`C*`, RG flow, `SpectralWellConnected`).

The four public-literature axes are not in competition. They map to different objects: preferences and rewards (Eckersley / Conitzer et al. / Ge-Halpern et al. / Qiu), agreement under information constraints (Nayebi), accountability allocation across a collective (Tibebu), and the structural admissibility of the deployed governance rule itself (legitimacy). Reading them as a coherent program is more accurate than reading any one as the canonical theorem.

This literature-map axis is consistent with `papers/03-impossibility-theorem.md` §6.6.8, but it is a different coordinate system from the internal follow-on axis there: inside Legitimacy's own follow-on program, the shipped governance-rule theorem is **Axis 1: Allocation**, while the paper's **Axis 4: Extraction** is a future extraction-transformation program. The literature-map axis here and the internal follow-on axis there should not be conflated.

Tibebu's priority claim also needs a diplomatic correction. Tibebu frames *The Accountability Horizon* as the first impossibility theorem in AI governance; our reading of the published record places Eckersley (2019), Nayebi (2025), and the RLHF trilemma paper (Sahoo et al., 2025, submitted November 23, 2025) as antecedent contributions with non-trivial formal structure. No stable public bibliographic record was located for the possible Oswald (2026) allocation-under-uncertainty antecedent, so the public citation set does not rely on that item.

### 2.2 The preference-aggregation neighbors: reward-space and feedback-aggregation work

Ge-Halpern et al. (2024, NeurIPS 2024), "Axioms for AI Alignment from Human Feedback," study alignment in reward space: given pairwise human feedback, what reward aggregation rules satisfy desirable reward-space axioms, and which reward-learning procedures fail them. This project is doing a different job. We do not inspect reward-model aggregation; we inspect the governance structure that controls actions, permissions, promotions, overrides, and allocation decisions once a system is deployed. Their object is a feedback-to-reward rule. Our object is a governance rule or governance graph. The difference shows up in composition, the operational failure mode in real agent stacks: a system can have locally sensible reward or approval components and still become unsafe when prompts, hooks, configs, and tool gates are composed.

Conitzer et al. (2024), "Social Choice Should Guide AI Alignment in Dealing with Diverse Human Feedback," is the broader agenda-setting neighbor. It argues that social choice should inform how alignment systems aggregate diverse human feedback. Legitimacy accepts that premise but works one layer above it: even if a preference-learning or constitutional-input process is well aggregated, the deployed governance rule that admits actions and allocates authority can still violate consistency, solidarity, or cross-claimant monotonicity.

### 2.3 The social-choice and mechanism-design lineage: where the axioms come from

Prior formal work around Arrow's theorem matters here. Wiedijk's Mizar formalization, Nipkow's Isabelle/HOL formalization, and first-order-logic formalizations by Grandi and Endriss show that social-choice impossibility results are legitimate proof-assistant targets. The Handbook of Computational Social Choice (Brandt et al., 2016) is the standard broader reference for the computational-social-choice substrate. Andrew Souther and Benjamin Davidson's `lean-social-choice` (`github.com/asouther4/lean-social-choice`) is a public Lean formalization of Arrow's theorem and related social-choice results for classical preference-aggregation rules; it has no associated paper, DOI, or arXiv record, but it is a real, public Lean development and the closest Lean prior art for this work. Legitimacy sits inside that tradition but changes the object from social welfare functions to governance graphs and couples the theorem to an operational extractor. The claim is accordingly a new theorem-object pair and a new deployment interface, not the invention of formal social-choice verification.

The social-choice and mechanism-design ancestry of the three graph-diagnostic primitives plus one derived strategyproofness deserves explicit naming. Arrow's 1950 paper "A Difficulty in the Concept of Social Welfare" and the 1951 monograph *Social Choice and Individual Values* establish the impossibility-theorem template that this work inherits at the level of proof shape. Young's *Equity: In Theory and Practice* (Princeton, 1994) is a source for the allocation-rule consistency tradition and for homogeneity in apportionment; Thomson's "On the Axiomatics of Resource Allocation" (2012) reinterprets the consistency principle through reduced problems and is the canonical modern restatement of why consistency is the right cross-population invariance. Maskin's 2007 Nobel lecture "Mechanism Design: How to Implement Social Goals" and the implementation-theory line of which Maskin monotonicity is the centerpiece make explicit that monotonicity has a classical implementability role; the legitimacy paper's monotonicity axiom should not be read as ad hoc. Muller and Satterthwaite's 1977 result on the equivalence of strong positive association and strategyproofness, and Dasgupta-Hammond-Maskin's 1979 "The Implementation of Social Choice Rules", together establish that strategyproofness is derivable from monotonicity in the classical setting; the legitimacy paper's `solidarity_monotonicity_imply_strategyproof` is the analog on governance graphs. None of these antecedents are competitors; they are the lineage this work builds on. Citing them at the axiom-introduction layer is the difference between a paper that claims to invent fairness and a paper that builds on a well-understood axiomatic substrate.

Mechanism-design impossibilities should be cited only as background for the sacrifice framing. Myerson-Satterthwaite (1983) is the canonical bilateral-trade example: it says no mechanism can jointly achieve a natural package of efficiency, incentive, participation, and budget-balance desiderata under the standard private-information model. Legitimacy does not reduce to that theorem; the useful analogy is the discipline of naming which desideratum must be given up. Fairness impossibility in machine learning is an important precedent in the same spirit. Chouldechova and Kleinberg-Mullainathan-Raghavan normalized the idea that impossibility theorems can be practically useful, because they force teams to surface which desideratum is being traded away. Legitimacy makes the same move for agent governance. The Declared Sacrifice Protocol is the governance-layer analogue of taking impossibility seriously instead of pretending better optimization will make it disappear.

Fernandez's [*Fair Atomic Governance*](https://doi.org/10.5281/zenodo.19643928) and [*Irreducible Multi-Scale Governance*](https://doi.org/10.5281/zenodo.19643950), both publicly deposited on April 18, 2026, are close agent-governance antecedents. The first studies identity fragmentation and actor fairness under independent per-agent admission; the second argues for four necessary governance layers under finite local observation and state assumptions. These precede Legitimacy's public formal package. Their predicates differ from consistency under claimant removal, solidarity, own-claim monotonicity and the kernel's five obligations. Neither inspected v1 text connects its obstruction to a canonical spectral carrier and shared capability limit. The comparison establishes related theorem objects, not a certification of their proofs or an exhaustive novelty claim for this program.

### 2.4 The verification-trilemma and guaranteed-safe-AI superstructure

Agarwal's 2026 "On the Formal Limits of Alignment Verification" is the cleanest verification-trilemma neighbor: no verification procedure can simultaneously be sound, fully general over the input domain, and polynomial-time tractable. Legitimacy now states a framework-specific positioning directly in Lean as `legitimacy_audit_diagonal_positioning`: for finite distributions whose support is inside a `BoundedExtractorContract`, the audit is sound and decision-defined; for an unrestricted malformed extractor input, the audit is intentionally undefined. This is not a claimed escape from Agarwal's trilemma and not yet a proof of Agarwal-style polynomial-time tractability or full-domain correctness. It is a typed admission of the current substrate's bounded-domain shape: decision-definedness is the substantive contingent theorem, soundness rides along by `audit_decision_defined_implies_soundness`, and non-generality is forced by `audit_defined_on_all_distributions_impossible`.

Dalrymple et al. (2024), "Towards Guaranteed Safe AI," is broader than this program and should be read as a superstructure rather than a competitor. Their world-model / safety-spec / verifier framing is a natural home for a concrete governance verifier like Legitimacy. The difference matters because they provide the general verifier architecture, while this project instantiates one particular verifier target: governance graphs with reachable scarce peer-relative stages and Arrow-lineage structural failure modes. Bengio's June 2025 "Introducing LawZero" announcement and the accompanying paper "Superintelligent Agents Pose Catastrophic Risks: Can Scientist AI Offer a Safer Path?" (Bengio et al., 2025) operationalize the guaranteed-safe-AI program through a non-agentic Bayesian "Scientist AI" oracle that gates an untrusted agent against a safety predicate. The legitimacy stack supplies typed governance graph and kernel objects that can serve as candidate safety-specification targets for a GS-AI-style architecture. We do not claim membership in the LawZero program, and we do not claim that the current fixture certificates verify those fixtures as safe. `Legitimacy.Bridges.GuaranteedSafeAIBridge` makes the component fit concrete: it instantiates Dalrymple's three-component framework with `worldModel = StaticGovernanceWorldModel`, `safetySpec = SemanticLegitimacySafetySpec` (per-agent semantic legitimacy kernels), and `verifier = GSAIKernelizationVerifier`. The populated verifier side supplies auditable rejection evidence for extracted-fixture graph models, such as the Codex-hooks certificate that transitively invokes `codexHooksGovernanceAdmissibilityRejectsMonotonicity` by `native_decide` on a concrete 16-node / 8-edge governance graph with 29 claims. The instantiation covers the static-snapshot subset of GS AI's world-model component and shows executable audit evidence in that slice; full dynamic-environment GS AI would require additional substrate (in particular, environment dynamics over the kernel-trajectory lifecycle).

### 2.5 The inner-alignment, ELK, and deceptive-alignment complement

Inner-alignment and deceptive-alignment work is adjacent but operates on a different level. Hubinger et al. (2019), "Risks from Learned Optimization in Advanced Machine Learning Systems," introduces mesa-optimization and the deceptive-alignment hypothesis. Hubinger et al.'s "Sleeper Agents: Training Deceptive LLMs that Persist Through Safety Training" (2024) and Greenblatt et al.'s "Alignment Faking in Large Language Models" (2024) are empirical demonstrations that deceptive policies are trainable and persistent. Christiano, Cotra, and Xu's *Eliciting Latent Knowledge* (ARC, 2021) frames the corresponding interpretability problem: when the supervisor cannot independently verify, can we extract honest reports of what the agent knows? Langosco et al.'s "Goal Misgeneralization in Deep Reinforcement Learning" (2021, ICML 2022) and Berglund et al.'s "Taken out of Context: On Measuring Situational Awareness in LLMs" (2023) show that goal-pursuit and self-context-awareness can vary across the training/deployment boundary. The legitimacy stack does not solve any of these problems. It supplies a structural complement: the `BoundedExtractorContract` requires that the audited governance graph be byte-stable-equivalent to the agent's actual decision surface, so a backdoor or mesa-objective that produces different decisions on the audit-input distribution is forced into either (a) an extractor-contract violation or (b) observational equivalence on that distribution. The detection-completeness boundary is honest: legitimacy can detect inner-alignment failures that change observable governance behavior on the audit-relevant inputs, and cannot detect inner-alignment failures that are observationally equivalent to base on those inputs.

`Legitimacy.Bridges.HubingerDeceptionBridge` pins that complement to the represented sleeper-agent slice only: a dormant training trigger, a deployment trigger, and a concrete monitored-claim perturbation that converts permit into deny. The bridge theorem records a raw audit monotonicity obstruction under the legacy positive-field semantics; the polarity-aware audit classifies the same represented sleeper graph as passing monotonicity and as legitimate. It does not formalize mesa-objectives or deceptive alignment in general.

The capacity-aware ELK bridge is deliberately narrower than a general solution to ELK. `Legitimacy.Bridges.CapacityAwareELK` counts the five witness-bearing hidden-authority certificate classes from `ELKCorrespondence` only after they are represented by an injective, zero-error `CapabilityResponseBlockCode` over a positive extraction window. The resulting theorem, `hidden_authority_certificate_rate_bounded`, imports the existing binary-output log-rate converse and says that such a compliant extractor cannot emit distinct certificate classes at any log-rate strictly above one binary decision per deterministic channel use. This is a Shannon-style finite block-code converse over the current substrate; it is not a claim that `C*` is a numeric ELK-reporting capacity, nor a stochastic reporter theorem.

`Legitimacy.Bridges.ChristianoELKStructuralBridge` states the structural half of the same ELK positioning: every minimal hidden-authority certificate already represented in the kernelization substrate has a witness-bearing `ELKDiscrepancy` match, while the `unsupportedWorldModelShift` constructor is an explicit outside-the-slice drop-test. The ELK bridge family is a structural correspondence plus a Shannon-style finite block-code converse over the current substrate, not full ELK.

### 2.6 Enforcement and runtime-governance systems: legitimacy is upstream

Reward hacking and enforcement-layer systems are adjacent but not substitutes. Skalse et al. formalize reward hacking itself; DrAttack-style decomposition failures motivate the attack-surface discussion; Type-Checked Compliance (Rashie and Rashi, 2026), the Agent Control Protocol (Fernandez, 2026), and the Policy Compiler for Secure Agentic Systems (Palumbo et al., 2026) enforce rules once given. The recent runtime-governance line: Wang, Poskitt, and Sun's "AgentSpec: Customizable Runtime Enforcement for Safe and Reliable LLM Agents" (2025, ICSE 2026), Mazzocchetti's "Cryptographic Runtime Governance for Autonomous AI Systems: The Aegis Architecture" (2026), Allegrini, Shreekumar, and Celik's "Formalizing the Safety, Security, and Functional Properties of Agentic AI Systems" (2025), Kaptein, Khan, and Podstavnychy's "Runtime Governance for AI Agents: Policies on Paths" (2026), and Bhardwaj's "Agent Behavioral Contracts: Formal Specification and Runtime Enforcement for Reliable Autonomous AI Agents" (2026), all give expressive runtime DSLs, behavioral contracts, or temporal-logic property languages for agent enforcement. Legitimacy adds a structural question: which combinations of governance guarantees can the rule satisfy? The order matters: perfect action checking on a structurally bad policy still gives you high-confidence enforcement of the wrong governance logic. The legitimacy stack and these enforcement systems are complements: legitimacy says what a structurally admissible governance rule must satisfy, and a runtime-enforcement DSL takes such a rule and binds the agent to it at execution time.

Two further comparisons make the shared territory explicit. Liu Yanglet, Wang and Capponi's [*No Certificate, No Execution*](https://arxiv.org/abs/2605.24462) separates proposed traces, certification and execution. Zexun Wang's [*Proof-Carrying Agent Actions*](https://arxiv.org/abs/2606.04104) organizes portable action certificates around admission, assumptions, approval and outcome evidence, distinguishing approval from enforceability. Both place authority checks before action. Legitimacy's distinguishing question concerns the governance rule's joint obligations and modeled stability; its execution theorems also require explicit host and observation contracts. Certificates and pre-action checks are shared architectural ideas, not exclusive contributions of this repository.

Bracale Syrnikov et al. (2026), in "Institutional AI: Governing LLM Collusion in Multi-Agent Cournot Markets via Public Governance Graphs," propose a runtime mechanism that operationalizes governance graphs as public, immutable manifests interpreted by an Oracle/Controller and reinforced by a cryptographically keyed governance log. Their empirical evaluation on multi-agent Cournot collusion (N=90 runs across six model configurations) shows the institutional regime reduces severe-collusion incidence from 50% to 5.6% while a prompt-only constitutional regime yields no reliable improvement. Legitimacy and Bracale Syrnikov et al. share vocabulary (the "public governance graph" headline noun) and the core reframing of alignment as mechanism design in institution-space rather than purely preference engineering in agent-space. They differ structurally: Bracale Syrnikov et al. validate empirically that governance-graph-based runtime enforcement reduces a specific coordination harm; legitimacy provides a formal checklist and substrate for testing such mechanisms once translated into Legitimacy's graph/kernel interface, including the canonical nine-element audit, kernel-level certifiability / observability / corrigibility / compositional safety / non-vacuity, and the declared-sacrifice protocol. The two contributions are complementary: Bracale Syrnikov et al. provide the empirical case that institutional governance binds under optimisation pressure; legitimacy provides the formal apparatus to test whether a translated governance mechanism is structurally legitimate.

### 2.7 AI control protocols as governance graphs

AI control protocols are themselves governance graphs in the legitimacy sense. Greenblatt et al.'s "AI Control: Improving Safety Despite Intentional Subversion" (2023), Griffin et al.'s "Games for AI Control: Models of Safety Evaluations of AI Deployment Protocols" (2024), and Korbak et al.'s "A Sketch of an AI Control Safety Case" (2025) study trusted-monitor / defer-to-trusted / defer-to-resample protocols and the safety-case argument structure that supports them. A control protocol is a finite decision rule that maps `(action, suspicion-level)` to permit / escalate / deny — an object the legitimacy audit suite is structurally able to consume. The relationship is structural-complement: AI control gives behavioral-safety bounds against intentional subversion, legitimacy gives structural-coherence bounds on represented governance rules. The current repository answers this only for five committed rule-layer fixtures, where the schema-derived verdict is `AuditVerdict.legitimate`; deployment-grade extraction and behavioral/evaluation embedding for real protocol implementations remain follow-up work.

`Legitimacy.Bridges.KorbakAIControlBridge` formalizes only the committed fixture slice: upfront auditing, trusted monitoring, defer-to-trusted, untrusted monitoring, and trusted editing extract as `AuditSubject`s and have concrete audit-verdict certificates. The raw positive-delta permit-to-deny pairs are legacy calibration witnesses, not theorem-facing rejected verdicts, and defer-to-resample remains an explicit outside-the-current-slice drop-test. Under schema-derived polarity, the represented fixtures receive `AuditVerdict.legitimate`. Read precisely: the raw monotonicity flags are *substrate-extraction diagnostics over the represented audit-fixture corpus*, not substantive claims that the named AI Control protocols are illegitimate as deployed; the substantive question, whether real protocol implementations satisfy or fail the four graph-diagnostic axioms, requires a deployment-grade extractor that the current synthetic structural-probe fixtures do not yet supply.

### 2.8 Multi-agent composition and non-compositionality

Spera's 2026 non-compositionality result (companion paper alongside it) is the closest negative-side neighbor for multi-agent safety composition. Its Theorem 9.2 shows that two individually safe agents can jointly reach forbidden goals through emergent conjunctive dependencies, motivating coalition gates, capability scoping, and minimal unsafe antichain analysis. Legitimacy now splits the conditional positive side into two typed layers. The T1 theorem `multi_agent_kernel_edge_local_composition_safe` is the edge-local two-channel result: semantic endpoint kernels plus authority-lattice compatibility, noninterference-or-declared, monotone escalation, compatible sacrifice indices, and bridge preservation exclude boundary-level forbidden violations while preserving per-agent forbidden-property exclusion. The T1.2 theorem `multi_agent_kernel_joint_capability_composition_safe` is the content-linked hypergraph layer: `JointCapability` carries one action drawn from each distinct participant id's own `kernel.actionSpace.Action`, and `JointCapabilityReaches` fires only when a forbidden property's joint predicate accepts that typed action bundle while every solo trajectory predicate stays false. The distinct-id condition is load-bearing: duplicate participant listings do not increase joint arity, and the Bool tracking fixture now proves the sixth premise is inhabited by `exampleJointCapabilityCompatible`, with `example_joint_capability_compatible_exists` and `exampleJointCapabilityT12_nonvacuous` instantiating the nontrivial compatibility and theorem premises. The earlier T1.1 theorem name is retained with the strengthened content-link signature rather than as an old-arity wrapper, because the behavioral joint-discharge hypothesis is now load-bearing. The canonical worked fixture uses a nontrivial Bool-action kernel: agent A contributes `true`, agent B contributes `false`, the actions are formally distinguishable, and the solo predicate is a real agent-id predicate rather than `False`. That Bool fixture is a compatibility inhabitant; its reachable Bool joint property is retained to show the behavioral joint-discharge hypothesis is substantive. A separate three-agent Bool fixture pins the higher-arity hidden-hyperedge case, while the dormant non-semantic-agent fixture records that the headline theorem's global `h_kernel` hypothesis is not derivable from old-five edge-local compatibility alone. The edge-local theorem remains the two-channel diagnostic slice; T1.2 is a conditional content-linked composition theorem over the available finite kernel substrate, not a general defeat of Spera-style non-compositionality.

Schneider et al.'s [*Securing Multi-Tool AI Agent Chains With Dynamic, Real-Time Compositional Policies*](https://arxiv.org/abs/2607.03423) supplies a constructive enforcement neighbor: restrictive policy composition, accumulated data classification and runtime revocation. Its monotonicity concerns restrictions tightening as tools or exposure accumulate; Legitimacy's allocation diagnostic instead concerns changes in claimant strength. The new [executed-composition example](../docs/executed-composition-v1.md) complements this runtime line with a machine-checked repair for the same forbidden property in a specified synthetic host. It does not originate chain-aware enforcement or remove the need to establish observation and execution contracts in a real integration.

### 2.9 Constitutional AI and rule-layer behavioral shaping

Constitutional AI and rule-layer behavioral shaping are upstream-different but worth naming. Bai et al.'s "Constitutional AI: Harmlessness from AI Feedback" (2022) trains a harmless assistant using AI-generated feedback against an explicit principle list; Sharma et al.'s "Constitutional Classifiers: Defending against Universal Jailbreaks across Thousands of Hours of Red Teaming" (2025) hardens model behavior against adversarial inputs through classifier-based runtime monitoring trained from a constitution-derived data pipeline. The intuition is correct: alignment needs an explicit rule layer, not just behavioral shaping. The constitution, however, is prose — a natural-language list of principles. The legitimacy stack is what a compiled, typed, machine-checked constitution looks like at the governance-graph level. The two are not in tension. A constitution-derived classifier or a constitution-trained policy can be evaluated by the legitimacy audit on the resulting decision surface; the audit asks the structural question the constitutional approach does not natively pose.

### 2.10 Assistance games, corrigibility, and multi-principal aggregation

Multi-principal assistance and corrigibility are the closest assistance-games and shutdown-problem neighbors. Fickinger et al.'s "Multi-Principal Assistance Games" (2020) studies a robot acting on behalf of N humans with potentially different preferences and proposes a social-choice method combining preference inference with welfare optimization — closer to a peer-relative aggregation problem than the single-principal CIRL line. Soares et al.'s "Corrigibility" (MIRI technical report / AAAI-2015 workshop) frames the shutdown problem as a utility-function constraint: design utility functions that make an agent accept shutdown without incentivizing it to either prevent or invite the signal. Nayebi's "Core Safety Values for Provably Corrigible Agents" (2025; AAAI 2026 Machine Ethics Workshop W37) gives the current positive single-principal frontier: Theorem 1 proves the single-round off-switch-game corrigibility shape, and Theorem 3 extends that single-principal setup to multi-step self-spawning agents with bounded safety-violation probability under learned heads and suboptimal planning. The module `Legitimacy.Protocol.MultiPrincipalCorrigibility` adds a narrower exact-planning multi-principal complement under the `Legitimacy.Corrigibility` namespace: `single_state_multi_principal_aggregate_corrigibility_lift` lifts step-0 principal corrigibility to a peer-relative aggregate principal on a single governed-kernel/policy-lifecycle slice when semantic Bool-kernel grounding, nonempty authority-lattice compatibility, and progeny-witness preservation all hold. This is not a claim to solve corrigibility under arbitrary principal disagreement, nor a formalization of Nayebi's epsilon/suboptimal-planning probability bound or self-spawning probability theorem; it is a typed multi-principal aggregation layer that identifies the remaining varying-state multi-step extension as future work. Legitimacy operates one level up: the `LegitimacyKernel` bundles a corrigibility witness: every Stackelberg-bounded trajectory drawn from the kernel's own action space preserves the supervisory algebra by construction, and the un-bundled discriminator lives in `Protocol/ObservationalBridge.lean` as `GovernanceSelectsCorrigibility`. Soares et al. explicitly include preservation of corrigibility through self-modification and the creation of subsystems or new agents ([2015 paper, §§1.1–1.2](https://intelligence.org/files/Corrigibility.pdf)). Legitimacy's narrower complement is its typed multi-principal authority aggregation and supervisory-algebra contracts under the stated assumptions; lifecycle and progeny corrigibility are already part of the earlier research agenda. Different formal objects, related questions; both belong in the lineage map. The multi-principal *aggregation* side of the same lineage is carried by `Results/MultiPrincipal.lean`: `majorityQuorumRule_fails_arrow_triple` transports Arrow's unanimity / independence / non-dictatorship triple to a concrete majority-quorum governance-aggregation witness over three principals, and `multi_principal_pairwise_achievability_with_majorityQuorum_obstruction` packages the pairwise-achievability complement around that witness: each two-axiom relaxation is realized by an explicit rule, while the displayed majority-quorum witness cannot realize all three. That result is positioned against the Arrow / Young lineage in the three-axis chapter (§3.4); the kernel the aggregator governs, not the transported impossibility, is the novel object.

Critch and Krueger's *AI Research Considerations for Human Existential Safety* (ARCHES, 2020) catalogs 29 research directions for technical AI safety and introduces "prepotence", globally transformative + difficult to turn off, as an organizing predicate. Multi-stakeholder delegation appears as one of the 29 directions, framed as an open research question. The legitimacy stack is the formalization of one ARCHES research direction: reachable scarce peer-relative multi-claimant governance with a typed admissibility theorem and a coupled extractor. The positioning is "we built one of the directions ARCHES catalogs," not "we replace the survey."

### 2.11 Finite-size scaling and the renormalization-group reading

The RG part of the paper also needs to be positioned honestly. The finite-size-scaling literature around Cardy, Baldwin's `n`-od Sharkovsky result, Chen-Wang-Lao-style finite-size corrections in network renormalization, Villegas-Gabrielli-Caldarelli on Laplacian RG, and Lee-Oveis Gharan-Trevisan on spectral bottlenecks all push toward a size-indexed reading of small-system basin structure. That is why the paper now frames the `n=5` depth-3 equality as scale-local by design, adds the `n=7` divergence between RG-basin and spectral-hybrid classifiers, and treats `SpectralWellConnected` as a candidate finite-family separator for the current probe archetypes rather than overclaiming one universal equality theorem.

### 2.12 References

Full bibliographic records for every work cited above — the public-record AI-governance impossibility results, the social-choice and mechanism-design lineage, the guaranteed-safe-AI and verifier-target program, the inner-alignment / ELK / deceptive-alignment line, the enforcement and runtime-governance systems, and the assistance-games and corrigibility neighbors — are maintained in `papers/CITATION.bib`. Two lineage items remain deliberately uncited there:

- An Oswald 2026 allocation-under-uncertainty antecedent has been identified as a possible lineage point, but no stable public arXiv, DOI, SSRN, or proceedings record was located for it; the paper therefore cites no such reference.
- Andrew Souther / Benjamin Davidson's `lean-social-choice` (`github.com/asouther4/lean-social-choice`) is a public Lean formalization of Arrow's theorem for classical preference-aggregation rules, with no associated arXiv, DOI, or proceedings record; the paper cites it as the closest Lean prior art and distinguishes on object (governance graphs vs voting rules) rather than on existence.

## 3. ELK / ARC Alignment Program Positioning

The ELK and ARC positioning is preserved in the prior-art chapter above, especially the paragraphs on Eliciting Latent Knowledge, the capacity-aware ELK bridge, the structural ELK bridge, and ARCHES. This consolidation keeps those paragraphs with the broader prior-art source text rather than duplicating them here.

## 4. GS-AI Verifier Positioning

### The Legitimacy Kernel as a Static-Snapshot Verifier Target for Guaranteed Safe AI

---

#### Abstract

The *Guaranteed Safe AI* (GS-AI) architecture (Dalrymple, Skalse, Bengio, Russell, Tegmark et al. 2024, arXiv:2405.06624) posits a verifier slot that any concrete safety specification can fill: a typed structure with the discriminative power to certify a system against an explicit safety property. We exhibit the legitimacy kernel as a concrete verifier-target instance on the static governance-snapshot slice and prove the structural reduction supported by that substrate. Our `KernelizationExtractorContract` (a function-shaped contract with `cleanSound`/`certSound` branch-soundness obligations and a 5-constructor `HiddenAuthorityCertificate` failure vocabulary) matches the verifier-target signature; the headline bridge `legitimacy_substrate_is_static_gs_ai_snapshot_instance` (`Bridges/GuaranteedSafeAIBridge.lean`) packages `legitimacyAsStaticGSAISnapshot` as a `GuaranteedSafeAIInstance` with the audit-pipeline certifying structure intact. This is explicitly a static-snapshot verifier-target instance with harness audit evidence packaged alongside the kernelization contract surface. It does not evaluate dynamic deployment traces or prove full per-harness end-to-end verifier construction; those remain named follow-up artifacts. The reduction is *deliberately one-way*: `safety_spec_reduces_to_kernel_audit` (`Legitimacy.SafetySpecReduction`) reduces a declared rule-layer artifact's safety spec to the kernel-audit, with halt-branch operational independence and a no-silent-degradation witness. A certificate bundle over static fixture evidence for four agent-harness fixtures (Codex hooks, Claude Agent SDK, CrewAI hooks, OpenClaw) is provided via `gs_ai_fixture_certificates_cover_rejected_leaderboard_harnesses`, establishing the kernel as one concrete static-snapshot verifier instance — not the architecture's only possible filling, but a typed, auditable, mechanically-verified one. We discuss what this static slice supplies to the GS-AI architecture's verifier slot, what it does not supply, and how it composes with the capacity-converse on the same governance graph.

---

#### 1. Introduction

##### 1.1 The lead

Dalrymple, Skalse, Bengio, Russell, Tegmark et al. (2024) propose *Towards Guaranteed Safe AI*, an architectural program in which AI systems are deployed under the supervision of a *verifier* whose job is to certify outputs against an explicit safety specification. The architecture is deliberately abstract: the verifier slot is parametric over the choice of safety specification. The program asks what *concrete* verifiers can fill the slot with the discriminative power needed.

We provide one concrete static-snapshot instance: the legitimacy kernel over a finite governance snapshot. The kernel is a typed structure on a directed governance graph; its `KernelizationExtractorContract` is the function-shaped verifier interface; its `HiddenAuthorityCertificate` is the 5-constructor failure vocabulary that names *which kind* of certificate-failure occurred when the verifier rejects. The bridge theorem `legitimacy_substrate_is_static_gs_ai_snapshot_instance` packages the kernel as a `GuaranteedSafeAIInstance` only on that static slice; the bundle theorem `gs_ai_fixture_certificates_cover_rejected_leaderboard_harnesses` covers static fixture evidence for four agent-harness fixtures (Codex hooks, Claude Agent SDK, CrewAI, OpenClaw).

The instance fills the verifier slot for static governance snapshots, rather than refuting, replacing, or critiquing the GS-AI architecture. The architecture provides the verifier-slot abstraction; the legitimacy kernel provides the typed concrete instance with audit-pipeline certifying structure in this narrower scope, stopping short of dynamic deployment verification.

##### 1.2 What we supply, what we inherit

**Supplied to the GS-AI architecture**: a typed concrete verifier with mechanically-verified Lean-4 proofs of branch-soundness obligations, a 5-constructor failure vocabulary, audit-pipeline reproducibility via `native_decide` on rational-arithmetic claim corpora, and a one-way safety-spec reduction with halt-branch operational independence. A nonempty certificate bundle over static fixture evidence for four agent-harness fixtures.

**Inherited from the GS-AI architecture**: the verifier-slot abstraction, the architecture-as-program framing, the named amplifier surface (Dalrymple, Bengio, Russell, Tegmark, ARIA Safeguarded AI), and the obligation to state which structural ceilings a verifier instance actually inherits. The capacity-converse ceiling from the companion paper applies to deterministic verifier protocols that factor through the capability-response channel and satisfy the target-use obligations: target-saturation/target-floor plus a positive log-rate message family. Other verifier-target instances inherit that ceiling only after a separate channel-embedding proof discharges those obligations; probabilistic, list-decoding, variable-length, or channel-bypassing verifiers are out of scope.

##### 1.3 Relation to LawZero, Scientist AI, and GS-AI

The GS-AI architecture's verifier slot needs concrete fillings. The legitimacy kernel is one such static-snapshot filling: typed, auditable, mechanically verified, with explicit branch-soundness obligations and a typed failure vocabulary. It is one concrete instance in the static governance-snapshot slice, among the multiple verifier-target instances the architectural slot admits.

What this gives an alignment researcher engaging with the GS-AI program is a worked example: what does it look like, structurally, to fill the verifier slot? The kernel shows: a typed contract on a governance object, audit-pipeline certifying structure, a failure vocabulary that names *which kind* of certificate-failure fired, and a static fixture certificate bundle across multiple agent harnesses. The instance is reproducible; the proofs are mechanically verified; the concrete fixtures are committed.

This is collaboration register. We exhibit a concrete verifier-target; the architecture engages on structural certification questions instance by instance. The companion capacity-converse paper supplies one such ceiling only for deterministic, target-saturating, positive-rate verifier protocols embedded in the capability-response channel; applying it to any new verifier-target requires the separate channel-embedding proof.

---

#### 2. Related work

##### 2.1 The GS-AI program and verifier-target architectures

**Dalrymple, Skalse, Bengio, Russell, Tegmark et al.** (2024), *Towards Guaranteed Safe AI* (arXiv:2405.06624), introduces the architectural program. The verifier slot is the central abstraction; concrete fillings are the open research target.

**Bengio, et al.** (2025), *Superintelligent Agents Pose Catastrophic Risks: Can Scientist AI Offer a Safer Path?* (arXiv:2502.15657), develops the architecture program along the LawZero / Scientist AI register. The verifier-target signature is parametric over the choice of safety specification; the legitimacy kernel is one concrete instance.

**ARIA Safeguarded AI** (UK government program, 2024 onward) develops applied verifier-target architectures for safety-critical deployments. The legitimacy kernel could potentially serve as a typed substrate for ARIA verifier-target instances; this is collaboration-channel follow-up.

##### 2.2 Other verifier-target instances and competing approaches

**Allegrini et al.** (2025), *Temporal-Logic Properties for Agentic AI* (arXiv:2510.14133), publishes runtime DSL specs (AgentSpec, ACP, PCAS) for safety properties. These are *enforcement* on the rule layer; they fill a different slot in the architecture (runtime enforcement vs verifier-target). We address that relationship here; the layering is enforcement (Allegrini) over rule-constitutionality (legitimacy).

**Korbak et al.** (2025), *AI Control Safety Case* (arXiv:2501.17315), publishes structured safety cases for AI Control protocols. Their work is at the channel layer (behavioral safety case); our verifier-target is at the rule layer (structural certificate). Compositional with the corrected schema-derived AI Control structural audit, where the five represented protocol fixtures clear monotonicity once suspicion and routing-risk fields are read as lower-better metrics.

**Agarwal** (2026), *On the Formal Limits of Alignment Verification* (arXiv:2603.08761), proves a verification trilemma: no procedure can simultaneously satisfy soundness, generality, and tractability. The legitimacy kernel as verifier-target instance has only a bounded-domain analogue of that question: decision-defined on the typed finite substrate, sound because decision-definedness entails soundness in this substrate, and definitionally non-general outside the typed contract. The companion positioning paper makes that precise, while treating Agarwal-style polynomial-time tractability as future work rather than a theorem clause.

##### 2.3 Adjacent kernelization-honesty work

The `KernelizationExtractorContract` and the 5-constructor `HiddenAuthorityCertificate` vocabulary are documented in the kernel-as-compiled-object paper (`papers/02-semantic-legitimacy-kernels.md` in this repository). The structural connection to ARC's Eliciting Latent Knowledge (ELK), Christiano-Cotra-Xu 2021 *Eliciting Latent Knowledge*, is on the failure vocabulary side: the 5-certificate kinds mirror ELK's diagrammatic deviation classes. The companion ELK paper treats this structural cousin directly; here we use the kernelization machinery as the GS-AI verifier-target instance.

---

#### 3. Setup

##### 3.1 The GS-AI verifier-target signature

The `GuaranteedSafeAIInstance` structure (`Bridges/GuaranteedSafeAIBridge.lean`) packages a verifier-target into a typed Lean-4 object. The instance comprises:

- A semantic safety specification (`SemanticLegitimacySafetySpec`,
  `Legitimacy.Bridges.GuaranteedSafeAIBridge`).
- An extractor contract that maps system inputs to typed certificates.
- A branch-soundness obligation: when the contract returns *clean*, the system is genuinely safe; when it returns a typed certificate, the certificate genuinely names a structural failure.
- A failure-vocabulary 5-constructor type covering the classes of structural failure.

The signature is the architectural slot the GS-AI program calls for. Filling it requires producing a typed concrete instance with mechanically-verified branch-soundness.

##### 3.2 The legitimacy kernel as instance

The legitimacy kernel fills the slot via:

- The `KernelizationExtractorContract` (in `Kernelization.lean`), a function-shaped contract with `cleanSound`/`certSound` branch-soundness obligations.
- The 5-constructor `HiddenAuthorityCertificate`, the typed failure vocabulary.
- The audit-pipeline as the operationalization of the contract, a mechanical procedure for evaluating the contract on a governance graph.

The packaging is `legitimacyAsStaticGSAISnapshot` (`lean/Legitimacy/Bridges/GuaranteedSafeAIBridge.lean`), the kernel as a `GuaranteedSafeAIInstance` whose world model is `StaticGovernanceWorldModel`.

##### 3.3 The harness-certificate bundle

The empirical witness covers four agent harnesses:

- Codex hooks: `codexHooksMonotonicityGSAICertificate`
  (`Legitimacy.Bridges.GuaranteedSafeAIBridge`).
- Claude Agent SDK: `claudeAgentSDKMonotonicityGSAICertificate`
  (`Legitimacy.Bridges.GuaranteedSafeAIBridge`).
- CrewAI hooks: `crewAIHooksMonotonicityGSAICertificate`
  (`Legitimacy.Bridges.GuaranteedSafeAIBridge`).
- OpenClaw: `openClawNonvacuityGSAICheckCertificate`
  (`Legitimacy.Bridges.GuaranteedSafeAIBridge`).

Each is a concrete certificate witness produced by the audit-pipeline on the harness's extracted governance graph. The bundle theorem `gs_ai_fixture_certificates_cover_rejected_leaderboard_harnesses` (`Legitimacy.Bridges.GuaranteedSafeAIBridge`) establishes that the four harnesses are jointly covered.

These certificates are theorem-backed only after the harness has been represented as an extracted governance graph. The Rust/source-to-graph extractor remains part of the trusted base: its faithfulness to the raw harness source is supported by fixtures and reproducibility evidence, not by the GS-AI bridge theorem. Scrutiny should therefore fall on extraction faithfulness separately from the Lean certificate coverage over the extracted graphs.

##### 3.4 The safety-spec reduction theorem

The reduction `safety_spec_reduces_to_kernel_audit` (`Legitimacy.SafetySpecReduction`) gives the formal one-way relationship: a declared rule-layer artifact's safety spec reduces to a kernel-audit obligation. The reduction is *deliberately one-way* — it does not claim full equivalence, only the implication direction the types support.

The supporting theorems:

- `noSilentRuleLayerDegradation` (`Legitimacy.SafetySpecReduction`), the predicate that the rule-layer spec does not silently degrade.
- `noSilentRuleLayerDegradation_halt_witness` (`Legitimacy.SafetySpecReduction`), a halt-branch operational-independence witness.
- `noSilentRuleLayerDegradation_not_audit_obligation_wrapper` (`Legitimacy.SafetySpecReduction`), the honest-scope qualifier that the predicate is not the audit's full obligation.
- `safetySpecReductionWorkedExample` (`Legitimacy.SafetySpecReduction`), a concrete worked example.

The honesty-of-reduction is load-bearing: the reduction is one-way, the audit is one obligation among others, and the degradation predicate is on the *declared* rule-layer artifact, not on arbitrary deployments.

---

#### 4. Main results

##### 4.1 The headline bridge

**Theorem 4.1** (Legitimacy substrate as static GS-AI snapshot instance, `legitimacy_substrate_is_static_gs_ai_snapshot_instance`, `lean/Legitimacy/Bridges/GuaranteedSafeAIBridge.lean`).
*The legitimacy kernel substrate is a concrete `GuaranteedSafeAIInstance` on the static governance-snapshot slice. The instance comprises the `KernelizationExtractorContract` as the verifier interface, the 5-constructor `HiddenAuthorityCertificate` as the typed failure vocabulary, and the audit-pipeline as the operationalization. Branch-soundness obligations are supplied explicitly to the contract-surface intro theorem; the four-harness fixture bundle witnesses non-vacuity.*

The proof is by direct construction: the kernel's `KernelizationExtractorContract` satisfies the verifier-target signature via the function-shaped contract; the audit-pipeline supplies the operationalization; the per-harness static evidence objects supply the nonempty certificate bundle; the bundle theorem composes them.

##### 4.2 The four-harness coverage bundle

**Theorem 4.2** (Four-harness coverage, `gs_ai_fixture_certificates_cover_rejected_leaderboard_harnesses`, `Legitimacy.Bridges.GuaranteedSafeAIBridge`).
*The four canonical agent-harness fixtures (Codex hooks, Claude Agent SDK, CrewAI hooks, OpenClaw) are each covered by a concrete `GSAIHarnessCertificate`. The certificates are produced by the audit-pipeline on the harness's extracted governance graph.*

The four-harness coverage is the empirical-witness side. Each certificate is a concrete object: a typed structural fact about the harness's audit signature.

##### 4.3 The safety-spec reduction

**Theorem 4.3** (Safety-spec reduction, `safety_spec_reduces_to_kernel_audit`, `Legitimacy.SafetySpecReduction`).
*A declared rule-layer artifact's safety spec reduces to the kernel-audit obligation. The reduction is one-way: the kernel-audit's success implies the safety spec's success on the declared artifact, with halt-branch operational independence and no silent rule-layer degradation.*

The reduction theorem is the bridge between the safety-specification language (the declared spec) and the kernel-audit language (the operational audit). The one-way direction is the type-supported reduction; the reverse direction is honestly disclosed as a separate research question.

##### 4.4 Compositional context: capacity-converse on the verifier

The legitimacy kernel inherits the structural ceiling of the capacity-converse paper only when it is analyzed as a deterministic verifier protocol that factors through the capability-response channel and satisfies the theorem's target-use obligations: target-saturation/target-floor plus a positive log-rate message family. In that scoped setting, above `C* = δ / cv(G, s)`, positive-rate all-message certification has a failed deployment message. The capacity-converse and the verifier-target instance are *compatible*: the legitimacy kernel is a candidate for this analysis once the channel embedding is supplied, and it does not claim to violate the ceiling.

The compatibility is not a limitation specific to the legitimacy kernel; it is the structural ceiling that any GS-AI verifier-target instance inherits after satisfying the same deterministic channel-embedding, target-saturation, and positive-rate obligations. Probabilistic, list-decoding, variable-length, and channel-bypassing verifiers remain outside this theorem, as in the precise scope statement of `papers/04-spectral-scaling.md` §3.

##### 4.5 The two-agent worked example

The supporting witness `compatibleTwoAgentStaticGovernanceWorld_semantic` provides a concrete two-agent worked example for the static-snapshot verifier-target instance. The example is mechanically verified and serves as a sanity-check fixture for the bridge theorem.

---

#### 5. Proof sketch

The proof of the headline bridge `legitimacy_substrate_is_static_gs_ai_snapshot_instance` decomposes into four steps.

**Step 1: Construct the verifier interface.** The `KernelizationExtractorContract` from `Kernelization.lean` is a function-shaped contract: given a system input, it returns either *clean* (the system is genuinely safe on the audit's rule layer) or a `HiddenAuthorityCertificate` (a typed failure witness). The function shape matches the verifier-target signature.

**Step 2: Name the branch-soundness obligations.** The contract's `cleanSound` obligation (when the contract returns *clean*, the rule-layer is genuinely structurally satisfied) and `certSound` obligation (when the contract returns a certificate, the certificate genuinely names a structural failure) are mechanically discharged in the kernelization module. The bridge's `contractSurface_intro` theorem takes those two branches as explicit named hypotheses instead of hiding their use inside a bundle constructor.

**Step 3: Operationalize via the audit-pipeline.** The audit-pipeline (`Audits/`) provides the operational evaluation of the contract on a concrete governance graph. Each check returns `AuditCheckStatus.passed`, `.failed`, or `.skipped`; the pipeline verdict is `AuditVerdict.legitimate` if every ordered check passes, `.rejected check` if the first blocking check fails, or `.undischarged check` if the first blocking check is skipped. That typed verdict surface is the witness shape the verifier-target signature requires.

**Step 4: Compose the harness-certificate bundle.** The four-harness coverage theorem `gs_ai_fixture_certificates_cover_rejected_leaderboard_harnesses` is a finite case-split over the four harness-fixture witnesses, each per-harness certificate being a concrete audit-pipeline output. The bundle theorem packages the four into a single `GSAIHarnessCertificateBundle`.

The proof of the safety-spec reduction `safety_spec_reduces_to_kernel_audit` is by direct construction: the safety-spec language is a typed predicate on the declared rule-layer artifact; the kernel-audit is the operational evaluation; the reduction is the implication direction supported by the types. The halt-branch operational-independence witness `noSilentRuleLayerDegradation_halt_witness` is mechanically discharged by exhibiting a halt-branch artifact that passes the predicate.

---

#### 6. Discussion: implications for the GS-AI / LawZero / Scientist AI audience

##### 6.1 What the verifier-target instance supplies

The legitimacy kernel as concrete verifier-target supplies:

- **A typed contract** with mechanically-verified branch-soundness obligations. The contract is not behavioral; it is a typed function on the system's extracted governance graph.
- **A 5-constructor failure vocabulary**. The certificate-failure vocabulary names *which kind* of structural failure occurred: unmodeled-edge, bypass-path, hidden-override, source-evidence-gap, semantic-bridge-failure. This typing is informative — it tells the verifier-target user not only *that* the system failed but *what kind* of failure occurred.
- **Audit-pipeline reproducibility**. The contract is operationalized by a `native_decide`-evaluable audit pipeline on rational-arithmetic claim corpora. The verdicts are mechanically reproducible; the typed rejection signatures are committed and re-evaluable.
- **Static fixture certificate bundle across four agent harnesses**. The Codex hooks, Claude Agent SDK, CrewAI hooks, and OpenClaw fixtures show the verifier-target instance is non-vacuous on committed static evidence: it produces typed certificates on extracted graph fixtures.

##### 6.2 What the verifier-target instance inherits

The instance inherits:

- **The structural ceiling of the capacity-converse**. Above `C*` on the governance graph, a deterministic verifier protocol embedded into the capability-response channel and satisfying target-saturation/target-floor plus positive log-rate obligations cannot sustain all-message zero-error certification; some deployment message fails. The legitimacy kernel inherits this ceiling only as such a target-saturating embedded verifier, after the channel embedding is supplied. Probabilistic, list-decoding, variable-length, and channel-bypassing verifiers are out of scope.
- **The verification-trilemma boundary**. The Agarwal 2026 verification trilemma says soundness × generality × tractability cannot all hold simultaneously. The legitimacy kernel as verifier-target instance proves a bounded-domain analogue, not a three-way independent choice: decision-definedness on the typed finite substrate is the contingent clause; soundness is entailed by decision-definedness; unrestricted generality is definitionally unavailable; and the theorem does not assert a polynomial-time complexity predicate.
- **The honest-scope obligation**. The verifier-target instance does not claim to verify *all* safety properties; it claims to verify the structural rule-layer property of the extracted governance graph. The honest scope is mandatory; the instance is one concrete filling, not the architecture's complete answer.

##### 6.3 Composition with the AI Control structural audit

The structural-audits companion (paper 05) applies the audit pipeline to the five represented AI Control protocol fixtures and now reports the corrected schema-derived polarity framing: the legacy positive-delta diagnostic flags monotonicity, but the canonical diagnostic passes all five and returns `AuditVerdict.legitimate` verdict-tags under `governanceAdmissibilityVerdict`. The composition with the GS-AI verifier-target instance is direct: the AI Control fixtures' extracted governance graphs run through the legitimacy kernel as a GS-AI verifier-target. The composition gives a worked example of the verifier-target instance on a published protocol class without treating the legacy monotonicity artifact as a behavioral safety-case refutation.

##### 6.4 Relationship to LawZero / Scientist AI

The Bengio LawZero / Scientist AI program develops the verifier-target architecture along the cognitive-architecture register. The legitimacy kernel as verifier-target instance is structurally compatible: the kernel can be used as the typed certifying structure for a Scientist AI deployment. The compatibility is at the architectural-instance level; the cognitive-architecture-specific fillings are open follow-up.

##### 6.5 The collaboration channel

The most useful framing for engagement with the GS-AI / LawZero / ARIA Safeguarded AI program is *collaboration*: the architecture supplies the verifier-target slot, the legitimacy kernel supplies one typed concrete instance, and the structural-ceiling work supplies constraints only after an instance satisfies the relevant hypotheses. For the capacity-converse, that means a deterministic, target-saturating, positive-rate capability-response embedding; for the asymptotic Stackelberg limit, it means the fixed-graph dynamic-stability hypotheses. Multiple verifier-target instances are wanted by the architecture's program; the kernel is one such, with audit-pipeline reproducibility and a four-harness static fixture certificate bundle.

---

#### 7. Limitations

1. **Static-snapshot scope**. The bridge is not a dynamic trace evaluator. It packages a `StaticGovernanceWorldModel` and concrete extracted-graph audit evidence; it does not prove safety for arbitrary deployment environment dynamics or full per-harness end-to-end verifier construction.

2. **One-way reduction**. The safety-spec reduction is deliberately one-way. The reverse direction, that every kernel-audit-passing artifact's safety spec is satisfied, is not claimed. The scope qualifier is on the reduction theorem itself.

3. **Four-harness coverage**. The harness-certificate bundle covers four canonical fixtures (Codex hooks, Claude Agent SDK, CrewAI hooks, OpenClaw). Coverage of additional harnesses is open.

4. **Audit-pipeline as operationalization**. The verifier-target instance is operationalized by the audit-pipeline on `AuditGovernanceGraph` substrate. Probabilistic extractions, list-output verifiers, dynamic trace evaluation, and other operationalizations are out of scope.

5. **Inherited structural ceilings**. The instance inherits the capacity-converse ceiling only under the deterministic, target-saturating, positive-rate capability-response embedding described above, and it inherits the bounded-domain verification-trilemma boundary on its typed finite audit substrate. These are structural ceilings for verifier-target instances that satisfy their respective hypotheses, not automatic limits on every possible verifier architecture.

6. **No empirical safety-bound claim**. We do not claim that a system passing the legitimacy-kernel verifier-target is empirically safe. The instance verifies the structural rule-layer property of the extracted governance graph; empirical safety is a separate claim.

7. **No comparative claim**. We do not claim the legitimacy kernel is the *best* verifier-target instance for the GS-AI architecture. We claim it is *one* concrete static-snapshot instance with named structural properties. Comparative analysis is open follow-up.

8. **Collaboration-register scope**. The bridge is presented as collaboration with the GS-AI / LawZero / Scientist AI program. We do not claim the architecture's program is solved; we claim one concrete static-snapshot filling exists. The architecture's open questions remain open.

---

#### 8. Conclusion

The legitimacy kernel is a concrete static-snapshot verifier-target instance for the *Guaranteed Safe AI* architecture. The kernel's `KernelizationExtractorContract` is a function-shaped contract with mechanically-verified branch-soundness; its 5-constructor `HiddenAuthorityCertificate` is the typed failure vocabulary; its audit-pipeline is the operationalization; the four-harness fixture bundle is static evidence for non-vacuity. The headline bridge `legitimacy_substrate_is_static_gs_ai_snapshot_instance` packages the kernel as a typed `GuaranteedSafeAIInstance`; the safety-spec reduction `safety_spec_reduces_to_kernel_audit` gives the deliberately one-way reduction with halt-branch operational independence.

The instance is *one concrete filling* of the architectural verifier-slot, not the architecture's only filling, and not an answer to all of the architecture's open questions. It supplies a typed verifier-target with reproducible audit-pipeline witnesses; it inherits the capacity-converse ceiling only when treated as a deterministic, target-saturating, positive-rate verifier embedded in the capability-response channel, and it inherits the bounded-domain verification-trilemma boundary. The verifier-target program advances by accumulating concrete instances and structural ceilings; the legitimacy kernel is one such instance.

Compositional with the corrected schema-derived AI Control structural audit, the verifier-target instance produces typed certificates on the represented AI Control protocol graphs and reads their current structural signature as a canonical pass, not as a channel-layer safety-case refutation. With the capacity-converse paper, the structural ceiling is named explicitly for deterministic verifier protocols that factor through the capability-response channel and satisfy target-saturation/target-floor plus positive-rate obligations; other verifier-targets need a separate embedding proof before the ceiling transfers. With the asymptotic Stackelberg limit, the dynamic-stability ceiling is named. Together, the verifier-target instance, the scoped structural ceiling, and the dynamic-stability characterization form a typed structural picture of what this GS-AI verifier-slot filling can do and what it cannot.

---

#### References

- **Agarwal, A.** (2026). On the Formal Limits of Alignment Verification. *arXiv:2603.08761*.
- **Allegrini, et al.** (2025). Temporal-Logic Properties for Agentic AI. *arXiv:2510.14133*.
- **Bengio, Y., et al.** (2025). Superintelligent Agents Pose Catastrophic Risks: Can Scientist AI Offer a Safer Path?. *arXiv:2502.15657*.
- **Christiano, P., Cotra, A., Xu, M.** (2021). Eliciting Latent Knowledge: How to Tell if Your Eyes Deceive You. *ARC technical report*.
- **Dalrymple, D., Skalse, J., Bengio, Y., Russell, S., Tegmark, M., et al.** (2024). Towards Guaranteed Safe AI. *arXiv:2405.06624*.
- **Greenblatt, R., Shlegeris, B., et al.** (2023). AI Control: Improving Safety Despite Intentional Subversion. *arXiv:2312.06942*.
- **Korbak, T., et al.** (2025). An AI Control Safety Case. *arXiv:2501.17315*.

##### Lean substrate references

- `Legitimacy.legitimacy_substrate_is_static_gs_ai_snapshot_instance`
- `Legitimacy.legitimacyAsStaticGSAISnapshot`
- `Legitimacy.gs_ai_fixture_certificates_cover_rejected_leaderboard_harnesses`
- `Legitimacy.codexHooksMonotonicityGSAICertificate`
- `Legitimacy.claudeAgentSDKMonotonicityGSAICertificate`
- `Legitimacy.crewAIHooksMonotonicityGSAICertificate`
- `Legitimacy.openClawNonvacuityGSAICheckCertificate`
- `Legitimacy.compatibleTwoAgentStaticGovernanceWorld_semantic`
- `Legitimacy.SemanticLegitimacySafetySpec`
- `Legitimacy.Safety.safety_spec_reduces_to_kernel_audit`
- `Legitimacy.Safety.noSilentRuleLayerDegradation`
- `Legitimacy.Safety.noSilentRuleLayerDegradation_halt_witness`
- `Legitimacy.Safety.noSilentRuleLayerDegradation_not_audit_obligation_wrapper`
- `Legitimacy.Safety.safetySpecReductionWorkedExample`

## 5. Verification Trilemma

### Bounded-Domain Audit Positioning Under the Verification Trilemma

---

#### Abstract

Agarwal 2026 (*On the Formal Limits of Alignment Verification*, arXiv:2603.08761) proves a verification trilemma: no verification procedure can simultaneously satisfy soundness, generality (definedness on all finite distributions), and tractability. We use Agarwal as motivation for a narrower Lean 4 positioning question, not as a literal three-way frontier that the current audit instantiates. In this substrate only decision-definedness is independently variable: `trilemma_decision_defined_independent` is the substantive independence witness, `audit_decision_defined_implies_soundness` makes soundness an entailed consequence of decision-definedness, and `audit_defined_on_all_distributions_impossible` makes unrestricted generality definitionally unavailable because the malformed unrestricted input is outside every well-formed finite contract. The diagonal-positioning theorem `legitimacy_audit_diagonal_positioning` (`Legitimacy.VerificationTrilemma`) establishes bounded-domain audit definedness on the typed finite substrate and undefinedness off it. This is not a proof of Agarwal-style polynomial-time tractability; executable `native_decide` termination on the finite rational-arithmetic corpus is evidence about the implemented finite substrate, not a complexity predicate in the theorem. The projection tests `compiler_audit_trilemma_without_*_clause` pin the conjunction shape, while the two obstruction theorems bound the analogy rather than serving as equal legs of a trilemma. The scope qualifier — *audit on the bounded-extractor admissibility class, not unrestricted finite distributions* — is structural, not concessionary. We discuss what this bounded-domain positioning means for collaboration with the formal-verification alignment community and how it composes with the GS-AI verifier-target instance and the capacity-converse.

---

#### 1. Introduction

##### 1.1 The lead

Verification frameworks for AI safety face the structural obstruction named by Agarwal 2026's *On the Formal Limits of Alignment Verification*: no verification procedure can simultaneously satisfy

- **soundness**: the procedure does not certify unsafe systems as safe,
- **generality**: the procedure is defined on all finite input distributions,
- **tractability**: the procedure runs in feasible time.

That result motivates the question this chapter asks, but the Lean theorem here is a degenerate bounded-domain analogue rather than a pick-two theorem. The current substrate replaces Agarwal's tractability predicate with `AuditDecisionDefined`, and only that replacement clause has an independence witness.

The proven structure is: decision-definedness is contingent, soundness is entailed, and unrestricted generality is forced to fail. `trilemma_decision_defined_independent` shows that decision-definedness can fail on `unrestrictedMalformedDistribution`; `audit_decision_defined_implies_soundness` shows that any decision-defined audit distribution is already sound; and `audit_defined_on_all_distributions_impossible` shows that all-distribution definedness is impossible for this theorem-facing audit because the unrestricted malformed input lies outside every well-formed finite contract. The committed corpus is executable by `native_decide`, but that executable finite-substrate evidence is not Agarwal's polynomial-time tractability predicate.

The positioning is structural. The audit's scope is the bounded-extractor admissibility class — a precisely-defined typed predicate, not an ad-hoc restriction. Inputs outside the class are *out of scope* by the audit's typed signature, not by an informal exclusion. Unrestricted generality fails by structure, not by a chosen sacrifice among three independent desiderata.

The positioning lemma therefore says something narrower and stronger than a rhetorical trilemma claim: the audit is decision-defined on its finite typed contract and undefined off it, with soundness following from definedness and non-generality forced by the contract.

##### 1.2 Relation to formal-verification alignment work

The Agarwal trilemma is the motivation, not the literal theorem shape proved here. The legitimacy audit is definitionally non-general by its typed contract, and soundness is not an independently retained clause: it follows from decision-definedness inside the current `LegitimacyAudit` type. We make precise which finite typed substrate is decision-defined, which executable finite-substrate evidence exists short of a polynomial-time tractability theorem, and why the two obstruction theorems limit the analogy.

The audit is defined on *bounded-extractor admissibility* finite distributions, the typed sub-class for which it is constructed, and undefined on unrestricted ones. The structural point is that this class is the audit's signature rather than an arbitrary restriction. The theorem therefore does not say "the audit picked soundness over generality"; it says the audit is bounded-domain by type, with decision-definedness the real movable clause.

This is the citation handshake. Agarwal supplies the external obstruction; the legitimacy audit supplies a bounded-domain theorem with one contingent clause and two entailed-or-forced facts. Future verification frameworks can be positioned similarly only after checking which predicates are genuinely independent, which are entailed by the substrate, which are definitionally impossible, and whether a separate polynomial-time tractability predicate has been proved.

---

#### 2. Related work

##### 2.1 The Agarwal verification trilemma

**Agarwal, A.** (2026), *On the Formal Limits of Alignment Verification* (arXiv:2603.08761), establishes the trilemma. The argument is structural: any procedure that is sound, general (defined on all finite distributions), and tractable would solve verification in feasible time on arbitrary inputs, which contradicts known computational lower bounds. The trilemma is:

```
Sound ∧ DefinedOnAllFiniteDistributions ∧ Tractable → ⊥
```

(in a sense to be made precise). Our diagonal-positioning theorem answers a narrower bounded-domain question after replacing tractability with `AuditDecisionDefined`; it is not a proof that the legitimacy audit retains two independently chosen clauses of Agarwal's three.

##### 2.2 Alternative verification-framework positionings

The trilemma is a motivation for positioning, but comparisons must respect each framework's actual predicates and independence structure.

**Allegrini et al.** (2025), *Temporal-Logic Properties for Agentic AI* (arXiv:2510.14133), is a runtime-enforcement DSL. Their positioning is different: they enforce at runtime, which sidesteps offline-tractability questions; their generality is on the property-language, not on input distributions. The two frameworks are not directly comparable by simply placing them on Agarwal's axes; they live in different audit-vs-enforcement layers.

**Korbak et al.** (2025), *A sketch of an AI control safety case* (arXiv:2501.17315), uses structured safety cases for behavioral control protocols. Their positioning is *behavioral* (channel-layer), not the *structural* audit-subject diagnostic used by this repository's extracted AI Control fixtures. The trilemma applies to structural verification; the AI Control safety case itself is not directly subject to the rule-layer trilemma.

**Dalrymple et al.** (2024), *Towards Guaranteed Safe AI* (arXiv:2405.06624), the GS-AI architectural program, is parametric over the verifier-target choice. The trilemma applies to each verifier-target instance; the architecture itself does not fix the instance-level predicate structure.

##### 2.3 Adjacent positioning work

The diagonal-positioning theorem is in the spirit of Brouwer-fixed-point-style structural lemmas in verification: a precise bounded-domain locator under a structural constraint. The closest external lineage is obstruction-aware verification positioning, with Agarwal supplying the motivating formal limit; the current result is not a pick-two analysis.

---

#### 3. Setup

##### 3.1 The verification-trilemma object

The trilemma's three predicates on a verification audit `audit : LegitimacyAudit` and an input distribution `D : InputDistribution` are:

- **Soundness**: `AuditSound audit D` (`Legitimacy.VerificationTrilemma`): every supported input in `D` extracts to a semantic kernel, and the audit subject satisfies `ExtractedGraphAdmissibilityContract` (`governanceAdmissibilityVerdict subject = AuditVerdict.legitimate`).
- **Decision definedness**: `AuditDecisionDefined audit D` (`Legitimacy.VerificationTrilemma`): the audit's decision is well-defined on `D` (every input in `D`'s support is in the audit's domain).
- **Defined on all distributions**: `AuditDefinedOnAllDistributions audit` (`Legitimacy.VerificationTrilemma`): the audit's decision is well-defined on *every* finite input distribution.

At Agarwal's level, the trilemma rules out simultaneously satisfying soundness, full-domain generality, and polynomial-time tractability. In this Lean module, the theorem-facing analogue replaces the tractability predicate with `AuditDecisionDefined`: a concrete verdict exists on the typed finite substrate. The legitimacy audit's positioning is on bounded-domain decision-definedness; soundness is entailed by that definedness in this substrate, and full-domain generality is definitionally unavailable.

##### 3.2 The legitimacy audit

The legitimacy audit's typed signature is in `VerificationTrilemma.lean`:

- `LegitimacyAudit` (`Legitimacy.VerificationTrilemma`), the audit object, an extracted governance graph satisfying the bounded-extractor admissibility audit.
- `legitimacyAudit` (`Legitimacy.VerificationTrilemma`), the audit-as-extracted-graph.
- `AuditRelevantInputs` (`Legitimacy.VerificationTrilemma`), the predicate naming inputs in the audit's domain.
- `IsAuditDefined` (`Legitimacy.VerificationTrilemma`), the predicate naming inputs on which the audit's decision is defined.
- `auditDecision?` (`Legitimacy.VerificationTrilemma`), the executable theorem-facing decision surface.

The audit is decision-defined on the bounded-extractor admissibility class, and in this substrate `AuditDecisionDefined` entails `AuditSound`. It is *not* defined on the unrestricted-malformed class. Polynomial-time tractability for the broader Agarwal predicate is future work.

This soundness is over the extracted audit object, not arbitrary raw source syntax. The source-to-graph extraction boundary remains a trusted base: the theorem positions the bounded-extractor admissibility class once the audit object exists, while extractor faithfulness to source is empirical evidence outside the Lean proof. Scrutiny should therefore distinguish challenges to extractor coverage or source faithfulness from attacks on the trilemma positioning theorem itself.

##### 3.3 The unrestricted-malformed witness

The unrestricted-malformed witness `unrestrictedMalformedExtractorInput` (`Legitimacy.VerificationTrilemma`) is a structurally-malformed input that lies outside the bounded-extractor admissibility class. The associated distribution `unrestrictedMalformedDistribution` (`Legitimacy.VerificationTrilemma`) is a finite distribution including this input. The theorem `unrestricted_distribution_not_relevant` (`Legitimacy.VerificationTrilemma`) confirms the witness lies outside the audit's relevant-input class.

The witness is the structural reason the legitimacy audit fails `AuditDefinedOnAllDistributions`: there exists a finite distribution including the witness on which the audit is *not* decision-defined. The audit's failure of generality is not an informal exclusion; it is a structural consequence of the typed audit's signature.

##### 3.4 The compiler-audit distribution

The compiler-audit case `compilerAuditTrilemmaDistribution` (`Legitimacy.VerificationTrilemma`) is the parallel theorem-facing distribution for the compiler-audit case. The compiler-audit-side theorems (`compiler_audit_trilemma_soundness_witness`, `Legitimacy.VerificationTrilemma`; `trilemma_definedness_failure_witness`, `Legitimacy.VerificationTrilemma`; `compiler_audit_diagonal_positioning`, `Legitimacy.VerificationTrilemma`) parallel the legitimacy-audit-side theorems for the meta-audit (audit on the audit pipeline itself).

---

#### 4. Main results

##### 4.1 The legitimacy audit diagonal positioning

**Theorem 4.1** (Legitimacy audit diagonal positioning, `legitimacy_audit_diagonal_positioning`, `Legitimacy.VerificationTrilemma`).
*The legitimacy audit is decision-defined on the bounded-extractor admissibility class, with soundness following there, and is decision-undefined on at least one unrestricted finite distribution. Therefore the audit fails `AuditDefinedOnAllDistributions`; the independently variable positive clause is decision-definedness on the typed scope.*

This is the headline positioning. It establishes the precise theorem-backed bounded-domain structure: decision-defined-on-the-typed-finite-substrate is the contingent positive clause, soundness follows from decision-definedness in this substrate, and full generality is structurally unavailable because of the unrestricted-malformed witness. The separate polynomial-time tractability predicate is not formalized here.

The *honest restate* of the theorem is named in the substrate as `legitimacy_audit_diagonal_positioning` after an earlier framing `legitimacy_audit_realizes_lin_diagonal` was found to be too strong. The restatement drops the maximalist claim that the audit realizes the Agarwal/Lin diagonal and asserts instead that the audit has bounded-domain decision-definedness, entailed soundness, and forced non-generality.

##### 4.2 The compiler-audit diagonal positioning

**Theorem 4.2** (Compiler audit diagonal positioning, `compiler_audit_diagonal_positioning`, `Legitimacy.VerificationTrilemma`).
*The compiler audit (the audit on the audit pipeline itself) has the same bounded-domain structure: decision-defined on the typed scope with soundness following there, and decision-undefined on at least one unrestricted finite distribution.*

The meta-audit's positioning is parallel to the legitimacy audit's. The compiler-audit-side has the same bounded-domain structure; the substrate's self-audit is internally consistent with the obstruction-qualified framing.

##### 4.3 Projection tests and independence

The three `compiler_audit_trilemma_without_*_clause` theorems are projection smoke tests: they remove one conjunct from `compiler_audit_diagonal_positioning` and confirm the resulting weaker statement still has the expected theorem shape. They are useful regression pins, not independence certificates:

- `compiler_audit_trilemma_without_soundness_clause` (`Legitimacy.VerificationTrilemma`), projection to decision-definedness plus failure of all-distribution definedness.
- `compiler_audit_trilemma_without_decision_defined_clause` (`Legitimacy.VerificationTrilemma`), projection to soundness plus failure of all-distribution definedness.
- `compiler_audit_trilemma_without_all_distributions_clause` (`Legitimacy.VerificationTrilemma`), projection to soundness plus decision-definedness.

The genuine independent clause currently proved is decision-definedness. `trilemma_decision_defined_independent` exhibits the compiler audit on `unrestrictedMalformedDistribution`: `AuditSound` still holds, `¬ AuditDefinedOnAllDistributions` still holds, and `AuditDecisionDefined` fails because `compiler_audit_malformed_distribution_decision_none` evaluates the decision surface to `none`. The other two clauses are not independently variable in the current `LegitimacyAudit` type. `audit_decision_defined_implies_soundness` proves that any decision-defined audit distribution is already sound, and `audit_defined_on_all_distributions_impossible` proves that every theorem-facing audit rejects all-distribution definedness because the unrestricted malformed input is outside every well-formed finite contract.

##### 4.4 The unrestricted-distribution witness

**Theorem 4.4** (Unrestricted distribution not relevant, `unrestricted_distribution_not_relevant`, `Legitimacy.VerificationTrilemma`).
*The `unrestrictedMalformedDistribution` includes an input outside the audit's `AuditRelevantInputs` class.*

This is the structural witness for failure of all-distribution definedness. The audit is not decision-defined on the witness because the witness is not in the audit's relevant-input class; the failure of generality is by-structure.

---

#### 5. Proof sketch

The diagonal-positioning theorem decomposes as the conjunction of:

**Step 1: Soundness on the typed scope.** `AuditSound legitimacyAudit D` for any `D` in the bounded-extractor admissibility class. In the current substrate this is not an independent clause: `audit_decision_defined_implies_soundness` proves that decision-defined audit distributions are already sound.

**Step 2: Decision-definedness on the typed scope.** `AuditDecisionDefined legitimacyAudit D` for any `D` in the bounded-extractor admissibility class. The audit's executable decision surface (`auditDecision?`) is total on the relevant-input class.

**Step 3: Failure of all-distribution definedness.** There exists a finite distribution `D₀` (specifically `unrestrictedMalformedDistribution`) on which the audit's decision is *not* defined. This is the unrestricted-malformed witness.

**Step 4: Composition.** The first two steps positively establish bounded-domain decision-definedness and its entailed soundness on the typed scope; the third negatively establishes forced failure of all-distribution definedness.

The projection tests proceed by conjunction elimination. The direct construction is the decision-definedness independence witness: the malformed finite distribution consumes the concrete `none` evaluation, so removing that witness breaks the proof. The absence of soundness and all-distributions independence witnesses is itself proved by the obstruction theorems above.

---

#### 6. Discussion: implications for the formal-verification alignment audience

##### 6.1 The trilemma as bounded-domain positioning motivation

Agarwal's trilemma is a structural constraint on verification frameworks, but the current Lean substrate does not instantiate a genuine three-way pick-two choice. For the legitimacy audit, unrestricted generality is definitionally unavailable by the typed contract; soundness is entailed by decision-definedness; and only decision-definedness has a proved independence witness.

The result is therefore bounded-domain positioning, not a taxonomy claim. The legitimacy audit is decision-defined on the typed finite substrate and undefined off it; runtime-enforcement DSLs (Allegrini et al. 2025) may have different predicates and obstruction structure, but that comparison is not formalized here.

##### 6.2 The structural justification for restricted generality

The legitimacy audit's restricted generality is the audit's typed signature rather than a concession. The bounded-extractor admissibility class is a precisely-defined typed predicate; inputs outside the class are out of scope by the audit's signature, not by informal exclusion. The structural justification rests with the type-checker, not the audit-author's argument.

This matters for the trilemma framing. A handshake citation can say: "the legitimacy audit is decision-defined on its typed finite substrate and definitionally non-general outside it; soundness follows from decision-definedness in this substrate." The trilemma constraint is acknowledged as motivation; the scope qualifier is structural; polynomial-time tractability remains a separate future-work predicate; the verification framework is positioned without implying a three-way chosen sacrifice.

##### 6.3 The compiler-audit parallel

The compiler-audit (the audit on the audit pipeline itself) has the same bounded-domain structure. This is internal-consistency: the substrate's self-audit fits the same obstruction-qualified constraint as the audit on first-order systems.

##### 6.4 Composition with the GS-AI verifier-target instance

Section 4 exhibits the legitimacy kernel as a GS-AI verifier-target instance. The positioning lemma here applies to the verifier-target instance, but only in the obstruction-qualified sense proved here: the legitimacy-kernel-as-verifier-target is decision-defined on its typed finite contract, sound by entailment, and definitionally non-general outside that contract. This is the trilemma's contribution to the GS-AI architecture's program: each concrete verifier-target instance should state its actual predicates and independence structure, and polynomial-time tractability is a separate obligation when claimed.

##### 6.5 Composition with the capacity-converse

The capacity-converse is the structural ceiling for deterministic verifier protocols that factor through the capability-response channel and satisfy the target-use obligations: target-saturation/target-floor plus a positive log-rate message family. The verification-trilemma boundary is orthogonal: it constrains which predicates a verifier can satisfy, but the current audit's predicates are not three independent clauses. The two compose only after the verifier-target instance supplies the channel embedding and target-use evidence required by the capacity theorem. The legitimacy-kernel instance is therefore a candidate for the capacity analysis under that embedding discipline, while probabilistic, list-decoding, variable-length, or channel-bypassing verifiers remain outside the theorem.

##### 6.6 Future verification-framework positionings

The diagonal-positioning lemma's discipline generalizes. Future verification frameworks can be characterized by their actual predicate structure: which predicates are independently variable, which are entailed, which are definitionally impossible, on which typed scope, and whether tractability has been proved as a separate complexity predicate. The legitimacy audit's positioning is one worked example; the broader comparative analysis is open work.

---

#### 7. Limitations

1. **Trilemma framing**. The positioning lemma is motivated by Agarwal's trilemma, but the current Lean substrate proves a degenerate bounded-domain analogue with one contingent clause and two entailed-or-forced facts. Other formal-limits frameworks (potentially in different formalizations) are not addressed here.

2. **Diagonal-positioning honest restate**. The earlier name `legitimacy_audit_realizes_lin_diagonal` was found to be too strong (the audit does not *realize* the diagonal in a maximalist sense; it proves bounded-domain decision-definedness with entailed soundness and forced non-generality). The honest-restate name `legitimacy_audit_diagonal_positioning` is what we use throughout.

3. **Bounded-extractor admissibility class scope**. The audit's typed scope is the bounded-extractor admissibility class. Generalization to broader scope classes (full-domain correctness, polynomial-time tractability with full-domain) is open follow-up; the maximalist-scope theorem is research-frontier.

4. **No comparative analysis**. We do not here compare the legitimacy audit's positioning to other verification frameworks (Allegrini, Korbak, Dalrymple verifier-target instances). The comparative analysis is open follow-up.

5. **Single-distribution witness**. The failure of all-distribution definedness is witnessed by a single distribution `unrestrictedMalformedDistribution`. Coverage of the broader space of unrestricted distributions is not the structural claim; one witness suffices.

6. **No outreach claim**. We do not claim the diagonal-positioning is the canonical positioning for the legitimacy audit in any external venue. The positioning is a technical comparison; outreach is subject to author approval.

---

#### 8. Conclusion

The legitimacy audit proves a bounded-domain analogue motivated by Agarwal 2026's verification trilemma, not a literal sound/general/tractable positioning. The diagonal-positioning theorem `legitimacy_audit_diagonal_positioning` establishes the positioning structurally: decision-definedness holds on the bounded-extractor admissibility class and fails on at least one unrestricted finite distribution (the structural witness `unrestrictedMalformedDistribution`); soundness follows from decision-definedness by `audit_decision_defined_implies_soundness`; and all-distribution definedness is impossible by `audit_defined_on_all_distributions_impossible`. The projection tests pin the conjunction shape, and `trilemma_decision_defined_independent` is the genuine independence witness.

The lemma converts the trilemma citation into bounded-domain audit positioning: the legitimacy audit is decision-defined on its typed finite contract and undefined off it. The scope restriction is structural (the typed signature of the audit), not concessionary (an informal exclusion). Polynomial-time tractability remains future verification-trilemma substrate work.

The positioning composes with the GS-AI verifier-target instance and with the capacity-converse. The compounded picture: a verifier is characterized by any capacity-converse ceiling it actually inherits through a deterministic, target-saturating, positive-rate capability-response embedding, and by the actual predicate structure of its audit domain, including which predicates are contingent, entailed, or definitionally forced.

Future work: comparative obstruction-qualified analysis across verification frameworks, the maximalist-scope theorem (Agarwal-equivalent re-derivation with full-domain correctness and polynomial-time tractability), and the structural relationship between bounded-domain audit positioning and behavioral safety bounds.

---

#### References

- **Agarwal, A.** (2026). On the Formal Limits of Alignment Verification. *arXiv:2603.08761*.
- **Allegrini, et al.** (2025). Temporal-Logic Properties for Agentic AI. *arXiv:2510.14133*.
- **Brewer, E.** (2000). Towards Robust Distributed Systems. *PODC keynote*.
- **Dalrymple, D., Skalse, J., Bengio, Y., Russell, S., Tegmark, M., et al.** (2024). Towards Guaranteed Safe AI. *arXiv:2405.06624*.
- **Gilbert, S., Lynch, N.** (2002). Brewer's Conjecture and the Feasibility of Consistent, Available, Partition-Tolerant Web Services. *ACM SIGACT News*.
- **Korbak, T., Clymer, J., Hilton, B., Shlegeris, B., Irving, G.** (2025). A sketch of an AI control safety case. *arXiv:2501.17315*.

##### Lean substrate references

- `Legitimacy.legitimacy_audit_diagonal_positioning`
- `Legitimacy.compiler_audit_diagonal_positioning`
- `Legitimacy.compiler_audit_trilemma_soundness_witness`
- `Legitimacy.trilemma_definedness_failure_witness`
- `Legitimacy.compiler_audit_trilemma_without_soundness_clause`
- `Legitimacy.compiler_audit_trilemma_without_decision_defined_clause`
- `Legitimacy.compiler_audit_trilemma_without_all_distributions_clause`
- `Legitimacy.audit_decision_defined_implies_soundness`
- `Legitimacy.audit_defined_on_all_distributions_impossible`
- `Legitimacy.compiler_audit_malformed_distribution_decision_none`
- `Legitimacy.trilemma_decision_defined_independent`
- `Legitimacy.unrestricted_distribution_not_relevant`
- `Legitimacy.AuditSound`
- `Legitimacy.AuditDecisionDefined`
- `Legitimacy.AuditDefinedOnAllDistributions`
- `Legitimacy.unrestrictedMalformedDistribution`
- `Legitimacy.compilerAuditTrilemmaDistribution`

## 6. Two C* Notions

### Two `C*` Notions Meet: A Cross-Talk Between Information-Theoretic Alignment-Bottleneck and Spectral Governance-Capacity

---

#### Abstract

Two recent works on alignment use the symbol `C*` for distinct, non-equivalent objects. Cao (2025) (*The Alignment Bottleneck*, arXiv:2509.15932) defines `C̄_tot|S = E_S[min{C_cog|S, C_art|S}]`, an information-theoretic *channel* capacity over a two-stage human-feedback channel `U → H → Y`. Our legitimacy substrate defines `C* = δ / cv(G, s)` (`Legitimacy.Spectral.Capacity.CriticalCapability:40`), a *graph-spectral* threshold on a directed governance graph with strength signal `s` and effectiveness floor `δ`. Same letter, orthogonal axes: theirs is information-theoretic on the human-feedback channel; ours is spectral on the governance graph perturbation budget. The two are not the same object, and neither is a special case of the other. We make the cross-talk precise: pluralistic alignment (Cao's frame) hits a feedback-channel capacity wall; structural alignment (our frame) hits a governance-graph capacity wall for deterministic, target-saturating, positive-rate protocols embedded in the capability-response channel; these distinct constraints can *compose* once both models are supplied. The cross-talk establishes the orthogonality, names that scoped compositional structure, and sets up the open question of joint analysis under both ceilings simultaneously. We discuss what the cross-talk supplies that either lineage individually does not, and how the joint analysis could proceed.

---

#### 1. Introduction

##### 1.1 The lead

The symbol `C*` appears in two recent alignment works on different objects:

- **Cao (2025)**, *The Alignment Bottleneck* (arXiv:2509.15932): `C̄_tot|S = E_S[min{C_cog|S, C_art|S}]`, the expected min over user contexts `S` of cognitive vs artifact channel capacities on the two-stage feedback channel `U → H → Y`.
- **Our legitimacy substrate**: `C* = δ / cv(G, s)` (`Legitimacy.Spectral.Capacity.CriticalCapability:40`), the graph-spectral threshold on the directed governance graph `G`, signal `s`, effectiveness floor `δ`.

The notational coincidence is not a content coincidence. The two objects are structurally distinct:

- Cao (2025)'s capacity is on a *channel* (with input-distribution structure, source coding, feedback noise).
- Ours is on a *graph* (with vertex strength signals, spectral perturbation budget, threshold structure).

Cao (2025)'s `C̄_tot|S` answers "what is the capacity of the human-feedback channel for transmitting alignment signal?" Our `C*` answers "above what capability threshold does the governance graph fail to spectrally support stable equilibria / deterministic, target-saturating, positive-rate zero-error verification through the capability-response channel?"

The two are not the same; neither is a special case of the other. They are orthogonal capacities on orthogonal axes.

##### 1.2 The compositional structure

The cross-talk we make precise: *pluralistic* alignment hits Cao (2025)'s feedback-channel wall; *structural* alignment hits our governance-graph wall for deterministic, target-saturating, positive-rate capability-response embeddings; the two compose only when both models are present. In that joint analysis, a deployment faces:

- A *feedback-channel ceiling*: the alignment-relevant signal that can be transmitted from users through human feedback to the system is bounded by Cao (2025)'s `C̄_tot|S`.
- A *governance-graph ceiling*: for deterministic verifier protocols embedded in the capability-response channel and satisfying target-saturation/target-floor plus positive-rate obligations, the alignment-relevant capability that can sustain all-message zero-error certification through the governance graph is bounded by our `C*`.

Either wall is sufficient for failure in its own scoped model. Both can be simultaneously operative for a deployment only after the feedback-channel model and the deterministic, target-saturating, positive-rate governance-channel embedding have both been supplied. The compositional structure says these are *non-redundant* constraints: satisfying the feedback-channel wall does not discharge the governance-graph embedding obligations, and satisfying the scoped governance-graph ceiling does not replace the feedback-channel analysis.

##### 1.3 What the cross-talk supplies

For a researcher tracking either lineage individually, the cross-talk supplies:

- **For the information-theoretic alignment audience**: a structural cousin to Cao (2025)'s feedback-channel bound, on a different but related object (the governance graph). The cross-talk says the information-theoretic side is one of *two* compositional ceilings, not the only one.
- **For the structural-alignment audience**: a feedback-channel companion to our spectral threshold. The cross-talk says the structural side has an information-theoretic complement, with simultaneous operation only in a supplied joint model.
- **For the alignment-research synthesist**: a precise notational and conceptual map distinguishing two objects that share a symbol but not a content.

The cross-talk positions the two lineages against each other precisely, without refuting either.

---

#### 2. The two `C*` notions

##### 2.1 Cao (2025): information-theoretic channel capacity

**Cao (2025)**, *The Alignment Bottleneck* (arXiv:2509.15932), considers alignment as transmission of intent from users to a system through human feedback. The channel structure is two-stage:

```
U → H → Y
```

where:
- `U` is the user-context space (population of users with diverse preferences),
- `H` is the human-feedback space (feedback signals over user-output pairs),
- `Y` is the system-output space (the system's responses).

The cognitive channel `U → H` has Shannon capacity `C_cog` (or `C_cog|S` conditional on context `S`). The artifact channel `H → Y` has capacity `C_art` (or `C_art|S`). The two-stage capacity is bounded by `min{C_cog|S, C_art|S}` per context, with the expected total capacity being:

```
C̄_tot|S = E_S[min{C_cog|S, C_art|S}]
```

This is an *information-theoretic* capacity on the *human-feedback channel*. It bounds how much alignment-relevant information can be transmitted from users to the system per unit of feedback. The bound applies via Fano-Packing (lower bound on alignment error rate as a function of `C̄_tot|S`) and PAC-Bayes (upper bound on alignment performance from the channel capacity).

The structural objects on which the bound lives: the channel input-distribution, the cognitive coding, the artifact decoding, the population of user contexts.

##### 2.2 Our `C*`: graph-spectral threshold

Our `C*` is on a different object. The structural objects: a directed governance graph `G`, a strength signal `s : Fin n → ℚ`, an effectiveness floor `δ > 0`. The graph's *consistency vulnerability* `cv(G, s)` is the worst-case verdict perturbation under denied-claimant removal, a measure of how badly removing one node degrades the graph's certification. The threshold:

```
C*(G, s, δ) = δ / cv(G, s)
```

This is a *spectral* threshold on the *graph object*. It bounds the capability above which deterministic alignment-verification protocols embedded into the capability-response channel cannot sustain target-saturating, positive-rate, all-message zero-error block coding (the capacity-converse) — a spectral perturbation-budget threshold rather than a channel capacity in Shannon's sense.

The structural objects on which the threshold lives: the directed governance graph, the strength signal, the spectral structure (eigenvalues of the directed-graph Laplacian-style operator), the effectiveness floor.

##### 2.3 The orthogonality

The two `C*` objects share a symbol but not:

- **Domain**: feedback-channel-input-distribution vs governance-graph-spectral-data.
- **Range**: a real-valued Shannon capacity vs a rational-valued spectral threshold.
- **Operational meaning**: bounds on alignment-error-rate transmission through human feedback vs bounds on deterministic, target-saturating, positive-rate zero-error verification through the capability-response channel.
- **Mathematical machinery**: Shannon information theory + Fano packing + PAC-Bayes vs spectral graph theory + rational-arithmetic threshold + perturbation budget.

The two are orthogonal capacities. Neither is a special case of the other. The Shannon-capacity bound on the feedback channel does not imply or contradict the spectral threshold on the governance graph; the two operate on disjoint structural objects.

This is the orthogonality observation. It is *the* contribution of this short cross-talk.

---

#### 3. The compositional structure

##### 3.1 Two walls, both operational

A deployment of an alignment-verification system faces two walls simultaneously in the joint model:

1. **Feedback-channel wall**: the alignment-relevant information transmittable from users through human feedback is bounded by `C̄_tot|S`. Above this bound, alignment-error-rate is lower-bounded structurally.
2. **Governance-graph wall**: for deterministic verifier protocols that factor through the capability-response channel and satisfy target-saturation/target-floor plus positive-rate obligations, the alignment-relevant capability that can sustain all-message zero-error verification through the governance graph is bounded by `C*`. Above this bound, some positive-rate deployment message fails. Probabilistic, list-decoding, variable-length, and channel-bypassing verifiers are outside this statement unless a separate embedding theorem brings them into scope.

Either wall is sufficient for failure in its own formal model. A system can fail by hitting the feedback-channel wall (insufficient information transmitted) without hitting the scoped governance-graph wall, and vice versa. The two walls are non-redundant: each can fail while the other remains satisfied within the joint model's assumptions.

##### 3.2 Composition as joint analysis

For a *deployed* system, the joint analysis is:

```
Successful zero-error verification in the combined model requires both a feedback-channel condition and, for deterministic target-saturating positive-rate protocols embedded in the capability-response channel, the governance-graph condition:
  (1) feedback-channel: C̄_tot|S sufficient for transmitting alignment signal; AND
  (2) governance-graph: κ < C*(G, s, δ).
```

Both are necessary for the joint scoped analysis. Failure of the feedback-channel condition obstructs the feedback-side certification problem; failure of the governance-graph condition obstructs deterministic, target-saturating, positive-rate all-message certification through the capability-response channel. The compositional ceiling for that combined model is `min{feedback-channel-implied-capability-bound, C*}`, whichever scoped wall is hit first as capability scales.

This is the compositional structure. It is non-trivial: a deployment that satisfies one ceiling can still fail the other.

##### 3.3 The structural picture

For an alignment-research synthesist, the compositional structure gives a richer picture than either lineage alone:

- Information-theoretic alignment work bounds *what can be transmitted* from users through human feedback to the system.
- Structural alignment work bounds deterministic, target-saturating, positive-rate all-message verification through the governance graph's capability-response channel at the deployment surface.

A deployed system needs both:
- Sufficient feedback-channel capacity to transmit alignment signal (Cao (2025) side).
- Sufficient scoped governance-graph capacity for deterministic, target-saturating, positive-rate all-message verification at the deployment surface (our side).

Joint failure modes are realistic under those assumptions: a system with sufficient feedback transmission can fail at the verifier-target due to the scoped governance-graph spectral threshold; a system with sufficient scoped governance graph can fail upstream due to feedback-channel transmission limits.

---

#### 4. What the cross-talk does and does not say

##### 4.1 What it says

- **Notational map**: the `C*` notation in the two lineages refers to distinct objects. We make the distinction precise.
- **Orthogonality**: the two objects are orthogonal capacities on orthogonal axes. Neither subsumes the other.
- **Composition**: the two ceilings operate simultaneously only after the deployment has both a feedback-channel model and a deterministic, target-saturating, positive-rate capability-response embedding. Failure of either scoped condition is sufficient for failure in that combined model.
- **Open question**: joint analysis under both ceilings, characterizing the failure-mode taxonomy when both walls are operational, is research-frontier.

##### 4.2 What it does not say

- **Not a refutation of Cao (2025).** Their feedback-channel bound is a real result on a real object. Our `C*` is on a different object; the existence of our threshold does not invalidate theirs.
- **Not a claim of bridge**. We do not bridge the two `C*` notions formally. The negative bridge result shows the substrate's *internal* Shannon-vs-spectral bridge is non-trivial; the *external* Shannon-vs-spectral relationship is similarly non-trivial. The cross-talk says the two are orthogonal; it does not characterize an algebraic agreement class.
- **Not a complete compositional analysis**. The joint analysis under both ceilings simultaneously is open work. The cross-talk establishes the structure; the analysis is research-frontier.

##### 4.3 The honest scope

This is a *short cross-talk*. It is not a long-form joint-analysis paper. It supplies the precise notational and conceptual map distinguishing the two `C*` notions and the compositional structure under which they jointly operate. Long-form joint analysis is open follow-up.

---

#### 5. Implications for the alignment-research community

##### 5.1 For information-theoretic alignment researchers

If you cite Cao (2025)'s `C̄_tot|S` as the alignment-bottleneck capacity, you should know that there is a structural cousin on a different object: our `C*`. The two are orthogonal; both are operational. Joint analysis is a research-frontier question.

##### 5.2 For structural-alignment researchers

If you cite our `C*` as the spectral governance threshold, you should know that there is an information-theoretic cousin on a different object: Cao (2025)'s `C̄_tot|S`. The two are orthogonal; both are operational. Joint analysis is a research-frontier question.

##### 5.3 For the alignment-research synthesist

The two `C*` notions are *non-confusable* at the structural-object level (channel input-distribution vs graph-spectral-data) but *notationally collisional* in the literature. The cross-talk supplies the disambiguation: same letter, different objects, different axes, joint operational structure.

##### 5.4 The publication-strategy note

We do not here recommend that either lineage rename their `C*`. The notational collision is regrettable but at this point structurally entrenched. The disambiguation lives in the explicit naming: *information-theoretic alignment-bottleneck `C̄_tot|S`* (Cao 2025) vs *graph-spectral governance-capacity `C*(G, s, δ)`* (our substrate). The full names are the resolution; the symbol-level collision is acknowledged.

---

#### 6. Limitations

1. **Cross-talk only, no joint analysis**. We do not formally analyze deployments under both ceilings simultaneously. Joint analysis is open.

2. **No Cao (2025) internal-formalization claim**. We do not formalize Cao (2025)'s results in our Lean substrate. The Cao side is referenced as published external work.

3. **No bridge-existence claim**. We claim orthogonality; we do not characterize agreement / disagreement classes for any algebraic bridge between the two notions.

4. **Two-lineage focus**. The cross-talk is between Cao (2025) and our substrate. Other capacity-style alignment works (Nayebi 2025 *Intrinsic Barriers*, Tibebu 2026 *Accountability Horizon*, Agarwal 2026 verification trilemma) are distinct again; their relationship to either of these two `C*` notions is open.

5. **Notational scope only**. The cross-talk is a notational and conceptual map. It is not a quantitative comparison of bound strengths.

6. **No empirical claim**. Whether real-world AI-deployment scenarios are bottlenecked primarily by the feedback-channel wall, primarily by the governance-graph wall, or by both is empirical and out of scope.

---

#### 7. Conclusion

The symbol `C*` in alignment work refers to two distinct, non-equivalent objects. Cao (2025)'s `C̄_tot|S = E_S[min{C_cog|S, C_art|S}]` is the information-theoretic capacity of the human-feedback channel `U → H → Y`. Our `C* = δ / cv(G, s)` is the graph-spectral threshold on directed governance graphs. The two share a letter but not a content; they are orthogonal capacities on orthogonal axes.

The compositional structure gives a richer deployment-analysis picture than either lineage alone: a deployed alignment-verification system faces the feedback-channel wall and, when its governance verifier is a deterministic target-saturating positive-rate capability-response embedding, the governance-graph wall, with failure of either applicable wall sufficient for verification failure. Joint analysis under both ceilings is research-frontier; this short cross-talk establishes the structure and supplies the notational disambiguation.

The contribution is precision in the notational and conceptual map. We do not refute Cao (2025); we do not claim bridges that do not exist; we observe the orthogonality and the compositional structure. Long-form joint analysis is open work.

---

#### References

- **Cover, T. M., Thomas, J. A.** (2006). *Elements of Information Theory*. Wiley-Interscience, 2nd edition.
- **Csiszár, I., Körner, J.** (2011). *Information Theory: Coding Theorems for Discrete Memoryless Systems*. Cambridge University Press, 2nd edition.
- **Cao, W.** (2025). The Alignment Bottleneck. *arXiv:2509.15932*.
- **Nayebi, A.** (2025). Intrinsic Barriers and Practical Pathways for Human-AI Alignment: An Agreement-Based Complexity Analysis. *arXiv:2502.05934*. AAAI 2026 oral.
- **Shannon, C. E.** (1948). A Mathematical Theory of Communication. *Bell System Technical Journal*, 27(3): 379-423; 27(4): 623-656.
- **Tibebu, H.** (2026). The Accountability Horizon: An Impossibility Theorem for Governing Human-Agent Collectives. *arXiv:2604.07778*.
- **Agarwal, A.** (2026). On the Formal Limits of Alignment Verification. *arXiv:2603.08761*.

##### Lean substrate references

- `Legitimacy.C_star`
- `Legitimacy.GovGraph.cv`
- `Legitimacy.GovGraph.capacity`
- `Legitimacy.GovernanceChannel.low_noise_noisyThreshold_capacity_certificate`
- `Legitimacy.GovGraph.governance_capacity_alignment_threshold` (the deterministic-channel converse, distinct from Cao (2025)'s feedback-channel `C̄_tot|S`)
- `Legitimacy.GovernanceChannel.fixed_noisyThreshold_capacity_not_concrete_C_star_bridge` (the internal-substrate negative bridge)

## 7. Three-axis Triangulation

### A Third Axis of Impossibility: Triangulating Legitimacy Against Arrow Social-Choice and Balinski-Young Apportionment

---

#### Abstract

Three impossibility theorems in mechanism-design sit on structurally distinct axes: Arrow 1951's preference-aggregation impossibility, Balinski-Young 1982's discrete-allocation impossibility, and our governance-rule structural-admissibility impossibility (`Legitimacy.reachable_peer_relative_decisive_stage_obstructs_diagnostics`), which we triangulate against the other two. Arrow's theorem is on preference profiles with universality + non-dictatorship + IIA + Pareto, where the impossibility names *no aggregation rule* meeting all axioms. Balinski-Young's theorem is on integer apportionment with quota + monotonicity, where the impossibility names *no allocation rule* meeting both. Our theorem is on directed governance pipelines with Young-lineage graph-diagnostic axioms (consistency, solidarity, monotonicity), where the impossibility names *no reachable scarce peer-relative decisive stage*, under a transparent prefix and non-denying suffix, meeting all three. The older complete first-effective binary-surface theorem (`Legitimacy.binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction`) is retained as the special case that factors through the reachable-stage statement. The three axes are: preference-aggregation (Arrow), discrete-allocation (Balinski-Young), governance-rule structural-admissibility (legitimacy). Each impossibility has its own object class, axiom set, and structural property. We argue that the third axis — governance-rule structural admissibility — has field-level, rule-layer mechanism-design implications: it lives on a *typed governance object* (the directed graph), not on preference profiles or integer allocations, and the axioms operate on the *rule layer* of the deployment, not on the user-utility or aggregation-output layers. We make the triangulation precise and discuss what each axis supplies that the others do not.

---

#### 1. Introduction

##### 1.1 The lead

Three impossibility theorems in formal mechanism-design occupy distinct structural axes:

- **Arrow 1951**: no preference-aggregation rule on individual preference profiles satisfies universality + non-dictatorship + Independence of Irrelevant Alternatives (IIA) + Pareto efficiency.
- **Balinski-Young 1982**: no apportionment rule on integer allocations satisfies quota + monotonicity (in the sense that strengthening a state's vote count cannot reduce its allocation).
- **Our theorem (2026)**: no reachable scarce peer-relative decisive stage in a directed governance pipeline, under a transparent prefix and non-denying suffix, satisfies consistency + solidarity + monotonicity (the Young-lineage graph-diagnostic axioms).

The three theorems are structurally distinct. Each lives on a different object class, with a different axiom set, and a different structural property that distinguishes it from the others. The triangulation we make precise: each impossibility defines a candidate axis; the three axes together form a coordinate system for mechanism-design impossibility theorems.

The third axis (governance-rule structural admissibility) is our candidate third axis. The first two axes are classical; the third is the legitimacy-lineage's contribution. We add a third axis that is structurally distinct from the classical two, without subsuming them.

##### 1.2 What each axis supplies

**Arrow's axis (preference-aggregation)**: bounds what *rule for aggregating individual preferences into a social ranking* can satisfy reasonable axioms. The object is a profile of individual preferences; the structural-property is whether the aggregation rule reflects all preferences (universality, non-dictatorship), respects pairwise consistency (IIA), and respects unanimity (Pareto).

**Balinski-Young's axis (discrete-allocation)**: bounds what *rule for converting vote shares into integer allocations* can satisfy reasonable axioms. The object is a vote-count profile and an integer-allocation target; the structural-property is whether the allocation rule respects quota (each state's allocation is within ±1 of its proportional share) and monotonicity (vote-count strengthening cannot reduce allocation).

**Our axis (governance-rule structural admissibility)**: bounds what *directed governance pipeline with a reachable peer-relative decisive stage under a transparent prefix and non-denying suffix* can satisfy structural axioms. The object is a directed governance graph with strength signals; the structural-property is whether the pipeline's verdict respects consistency (removing a denied claimant does not change any other claimant's decision), solidarity (scaling all claim strengths by the same positive factor preserves every decision), and monotonicity (strengthening a claim does not flip any claimant from `Permit` to `Deny`).

The three axes operate on three different objects: preference profiles, integer allocations, directed governance graphs, with three different axiom sets. The impossibility on each axis is structural: the axioms cannot be jointly satisfied on the object class.

##### 1.3 Relation to the mechanism-design and AI-alignment crossover

The triangulation is informative for an alignment researcher tracking mechanism-design impossibility theorems. Arrow's theorem is canonical for utility-aggregation alignment lineages (RLHF aggregates user preferences); Balinski-Young is canonical for resource-allocation alignment (compute-allocation between models, attention-allocation between tasks); Legitimacy extends that foundation to *governance-rule* alignment, where the typed rule layer of the deployment is structurally constrained.

The three axes together give a richer picture than any one alone. Alignment work that aggregates preferences faces Arrow's axis. Alignment work that allocates discrete resources faces Balinski-Young's axis. Alignment work that deploys typed governance rules at the rule layer faces ours. Frontier AI-safety deployments face all three: they aggregate user-preferences (Arrow), allocate resources (Balinski-Young), and deploy governance rules (legitimacy). The compounded picture: three orthogonal impossibility constraints, each operating on a distinct structural axis.

---

#### 2. Related work

##### 2.1 The Arrow social-choice lineage

**Arrow, K. J.** (1951), *Social Choice and Individual Values*, Yale University Press. The foundational impossibility: no preference-aggregation rule satisfies universality + non-dictatorship + IIA + Pareto on a set of three or more candidates with rankings provided by individuals.

**Sen, A.** (1970), *Collective Choice and Social Welfare*. Sen's extensions and the impossibility of a Paretian liberal.

**Gibbard-Satterthwaite** (1973, 1975), the strategyproofness extension of Arrow's theorem.

The Arrow lineage is preference-aggregation-shaped: the object is a profile of individual preferences; the structural-property is the aggregation rule. Our graph-diagnostic axis is graph-shaped, not preference-shaped. The substrate also carries a *second*, more literal contact with this lineage: a direct transport of Arrow's unanimity / independence / non-dictatorship triple onto multi-principal governance aggregation, with a mechanically-checked counterexample rule and an explicit pairwise-achievability frontier (`Legitimacy.majorityQuorumRule_fails_arrow_triple`, `Legitimacy.multi_principal_pairwise_achievability_with_majorityQuorum_obstruction`). That transport is the subject of §3.4; it is honest lineage inheritance, not a new impossibility; the novel object remains the typed kernel the aggregation rule governs.

##### 2.2 The Balinski-Young apportionment lineage

**Balinski, M., Young, H. P.** (1982), *Fair Representation: Meeting the Ideal of One Man, One Vote*. The foundational apportionment impossibility: no allocation rule satisfies quota + monotonicity (the *population paradox*).

**Young, H. P.** (1994), *Equity: In Theory and Practice*. Young's broader axiomatic-foundations work.

The Balinski-Young lineage is allocation-shaped: the object is a vote-count profile + integer allocation target; the structural-property is the allocation rule. Our axis is graph-shaped, not allocation-shaped.

##### 2.3 Adjacent AI-alignment lineages

**Eckersley, P.** (2019), *Impossibility and Uncertainty Theorems in AI Value Alignment*. Adjacent impossibility-style work in AI alignment.

**Conitzer, V., Procaccia, A.**, social-choice-for-AI-alignment lineage.

**Halpern, J. Y., Pass, R.**, game-theoretic foundations applicable to AI alignment.

**Nayebi, A.** (2025), *Intrinsic Barriers and Practical Pathways for Human-AI Alignment: An Agreement-Based Complexity Analysis* (arXiv:2502.05934, AAAI 2026 oral), multi-agent overhead lower bound.

**Tibebu, H.** (2026), *The Accountability Horizon*, accountability-incompleteness phase transition.

These adjacent lineages bring impossibility theorems into AI-alignment territory. Our axis (governance-rule structural admissibility) is distinct from these: it is on the *rule layer* of the typed governance object, not on preference aggregation or accountability surfaces.

##### 2.4 The legitimacy-paper-family

The foundational impossibility is in the long-form paper (`papers/03-impossibility-theorem.md`), with the priority note preserved there as an appendix. The three-axis triangulation is the *positioning* paper that places our axis relative to the classical lineages.

---

#### 3. Setup: the three impossibility theorems

##### 3.1 Arrow's theorem (preference-aggregation axis)

**Theorem (Arrow 1951)**. Let `N ≥ 2` be the number of voters and `M ≥ 3` the number of candidates. No social-welfare function `F : (Profile of preferences over candidates) → (Social ranking over candidates)` satisfies all four:

- **Universality**: `F` is defined on every preference profile.
- **Non-dictatorship**: no voter's preference always determines the social ranking.
- **IIA**: the social ranking of candidates `{a, b}` depends only on individual rankings of `{a, b}`, not on rankings of other candidates.
- **Pareto efficiency**: if every voter ranks `a > b`, then `F` ranks `a > b`.

The structural object is *preference profiles*; the structural-property is the aggregation rule.

##### 3.2 Balinski-Young's theorem (discrete-allocation axis)

**Theorem (Balinski-Young 1982)**. No allocation rule on integer apportionments simultaneously satisfies:

- **Quota**: each state's allocation is within ±1 of its proportional share.
- **Monotonicity** (the population paradox): when a state's vote count strengthens (relative to others), its allocation cannot decrease.

The structural object is *integer allocations on vote-count profiles*; the structural-property is the allocation rule.

##### 3.3 Our theorem (governance-rule structural-admissibility axis)

**Theorem (Legitimacy 2026)**. For any `[DecisionPipeline P]`, any reachable scarce peer-relative decisive stage under a transparent prefix and non-denying suffix obstructs the simultaneous satisfaction of:

- **Consistency**: removing a denied claimant does not change any other claimant's decision.
- **Solidarity**: scaling all claim strengths by the same positive factor preserves every decision.
- **Monotonicity**: strengthening a claim does not flip any claimant from `Permit` to `Deny`.

(This is `reachable_peer_relative_decisive_stage_obstructs_diagnostics` in the substrate. The older complete first-effective binary-surface theorem, `binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction`, is the retained special case: the complete first-effective hypotheses are repackaged into the reachable-stage statement by `complete_first_effective_obstructs_diagnostics_via_reachable`.)

Strategyproofness is *derived* from solidarity ∧ monotonicity at the typeclass level (`decisionSystem_solidarity_monotonicity_imply_strategyproof`), so the impossibility is *three-axiom + bridge* rather than four-axiom-independent.

The structural object is *directed governance graphs with reachable decisive stages*; the structural-property is the pipeline's verdict at the rule layer.

##### 3.4 The direct Arrow-template transport (multi-principal aggregation)

The graph-diagnostic axis in §3.3 inherits Arrow's *proof shape* but states its impossibility over Young-lineage axioms on a directed-graph object. The substrate also carries a second, more literal contact with the Arrow lineage: a direct transport of the classical unanimity / independence / non-dictatorship triple onto a multi-principal governance *aggregation* rule, with the impossibility and its tight complement both mechanically checked.

**Theorem (multi-principal Arrow obstruction).** On a 3-principal / 3-property aggregation surface, the majority-quorum aggregation rule is unanimous and non-dictatorial but fails independence on an explicit counterexample, so it cannot jointly satisfy unanimity, independence, and non-dictatorship. This is `majorityQuorumRule_fails_arrow_triple` (`Results/MultiPrincipal.lean`), discharged by a concrete `majorityQuorumRule` witness rather than by an abstract diagonal argument.

**Theorem (pairwise-achievability frontier).** Each *pair* among the three axioms is jointly realizable by an explicit governance-aggregation rule: a dictatorship rule realizes unanimity ∧ independence, the majority-quorum rule realizes unanimity ∧ non-dictatorship, and a constant rule realizes independence ∧ non-dictatorship, while the majority-quorum witness cannot realize all three at once. This is `multi_principal_pairwise_achievability_with_majorityQuorum_obstruction` (`Results/MultiPrincipal.lean`): every two-axiom relaxation is witnessed by a rule that satisfies it, and the displayed triple obstruction is the majority-quorum one.

Two scope sentences fix what this is and is not. The result is a faithful transport of an Arrow/Young-lineage obstruction onto the governance-aggregation surface, with the pairwise frontier supplying the tightness that the classical statement carries by its own independence witnesses; the contribution is the typed governance object and its kernel, not a new impossibility theorem in social-choice theory. It is stated at a fixed `Fin 3` principal/property arity with explicit finite rules and does not yet claim a general-`n` aggregation-rule classification; the value here is that the multi-principal aggregation layer sits *on top of* the `LegitimacyKernel` object, so the frontier maps exactly which two-axiom relaxations a deployed aggregator may keep before the kernel must declare its sacrifice.

This transport and the graph-diagnostic axis of §3.3 are distinct contacts with Arrow's work: §3.3 reuses the proof *shape* on a graph object with Young-lineage axioms; §3.4 reuses the *axioms themselves* on a multi-principal aggregation rule. Neither contact is the headline: the positive kernel object remains the headline, with both Arrow contacts serving as forcing arguments that show what a legitimate aggregator over that kernel must give up.

---

#### 4. The triangulation

##### 4.1 Axis-by-axis comparison

| Axis | Object | Axiom set | Structural property |
|------|--------|-----------|---------------------|
| Arrow (1951) | Preference profiles | Universality + Non-dictatorship + IIA + Pareto | Aggregation rule |
| Balinski-Young (1982) | Integer allocations | Quota + Monotonicity | Allocation rule |
| Legitimacy (2026) | Directed governance graphs | Consistency + Solidarity + Monotonicity (+ bridge to Strategyproofness) | Pipeline verdict / rule-layer admissibility |

The three axes are structurally distinct:

- **Object difference**: preference profiles ≠ integer allocations ≠ directed governance graphs. The objects do not embed into one another by simple structural inclusion.
- **Axiom difference**: the axioms are on different surfaces. Arrow's IIA is on pairwise consistency of aggregation; Balinski-Young's quota is on proportional-share-bounding; our consistency is on denied-claimant removal invariance at the rule layer.
- **Structural property difference**: aggregation rule vs allocation rule vs pipeline verdict. The three structural properties are not inter-translatable.

##### 4.2 Why the third axis has field-level implications

We argue that the third axis has rule-layer mechanism-design implications because:

1. **Object novelty**: directed governance graphs with strength signals at the rule layer is a typed object distinct from preference profiles and integer allocations. It is not a special case of either.
2. **Axiom-set novelty**: the Young-lineage graph-diagnostic axioms (consistency, solidarity, monotonicity) operate on the rule layer of the governance graph. They are graph-diagnostic, not aggregation-rule-diagnostic or allocation-rule-diagnostic.
3. **Bridge theorem novelty**: strategyproofness is *derived* from solidarity ∧ monotonicity at the typeclass level. This is a structural derivation, not a separate axiom. The bridge is formalized in `decisionSystem_solidarity_monotonicity_imply_strategyproof`.
4. **AI-deployment relevance**: the rule-layer governance object is the deployment surface for AI-system rule-layer governance. The classical axes do not address this surface directly.

##### 4.3 The compounded structural picture

A frontier AI-safety deployment faces all three axes simultaneously:

- **Arrow's axis**: when aggregating user preferences (RLHF) or aggregating evaluator opinions (debate), the deployment is constrained by Arrow-type impossibilities.
- **Balinski-Young's axis**: when allocating discrete resources (compute, attention, evaluator-bandwidth), the deployment is constrained by Balinski-Young-type impossibilities.
- **Our axis**: when deploying typed governance rules at the rule layer (audit pipelines, control protocols, deployment-graph extractions), the deployment is constrained by our governance-rule structural-admissibility impossibility.

The three axes operate on disjoint structural objects but compound in the deployment context. Failing on any axis triggers the corresponding-axis failure mode.

---

#### 5. Why the triangulation is informative, not redundant

##### 5.1 Each axis is load-bearing on its own

The classical axes are foundational for their object classes. Arrow's theorem reshaped social-choice theory; Balinski-Young's theorem reshaped apportionment theory. We argue that the governance-rule theorem extends that foundation to a new typed object: reachable scarce peer-relative governance pipelines whose rule layer must expose which structural diagnostic it sacrifices.

The triangulation claims that the three axes are structurally distinct and jointly relevant, not that one axis subsumes another.

##### 5.2 The three axes are non-redundant in deployment

For an AI-safety deployment, the three axes operate on different structural objects. A deployment can fail on one axis while satisfying the other two. The non-redundancy is:

- An RLHF system can satisfy our governance-rule axiom set (the rule-layer is structurally well-formed) and Balinski-Young's axiom set (the allocation rule is sensible) while still hitting Arrow-type impossibility on user-preference aggregation.
- A compute-allocation system can satisfy our governance-rule axiom set and Arrow's axiom set while still hitting Balinski-Young-type impossibility on discrete allocation.
- A typed governance rule can satisfy Arrow's and Balinski-Young's axiom sets at the upstream-aggregation and downstream-allocation layers while still hitting our impossibility at the rule layer.

The three axes are *non-redundant* failure modes.

##### 5.3 What the triangulation does not say

**Not a unification claim**. We do not claim the three axes can be unified into a single impossibility theorem. They are structurally distinct on distinct objects.

**Not a hierarchy claim**. We do not claim the third axis subsumes or is subsumed by the first two. The three are comparable structural axes on their respective object classes.

**Not a comprehensive classification of mechanism-design impossibilities**. The three axes are notable; other impossibilities (Sen's Paretian liberal, Gibbard-Satterthwaite, Eckersley's AI-alignment impossibility, Nayebi's multi-agent overhead) live on their own axes. The triangulation is a structural-positioning move, not a comprehensive taxonomy.

---

#### 6. Discussion: implications for mechanism-design + AI-alignment crossover

##### 6.1 The third axis as alignment-relevant

For mechanism-design + AI-alignment researchers, the third axis (governance-rule structural admissibility) is the alignment-relevant cousin of the classical lineages. The rule layer of typed governance deployments is the structural object on which our impossibility lives. Frontier AI-safety deployments deploy typed governance rules; the impossibility on these rules is structurally relevant.

The two classical axes are also relevant: RLHF aggregates user preferences (Arrow's axis); resource allocation is everywhere (Balinski-Young's axis), but they do not directly address the *rule layer*. Our third axis is the structural complement.

##### 6.2 The compounded ceiling

A deployment faces all three axes' ceilings simultaneously:

- Arrow's ceiling on preference-aggregation rule.
- Balinski-Young's ceiling on resource-allocation rule.
- Our ceiling on governance-rule structural admissibility.

The compounded ceiling is the joint constraint. A deployment satisfies this joint constraint only if it (a) handles user-preference aggregation in an Arrow-aware way, (b) handles resource allocation in a Balinski-Young-aware way, and (c) handles governance-rule structural admissibility in a way our impossibility theorem permits.

##### 6.3 Composition with the structural-mechanism-design lineage

**Conitzer-Procaccia, Halpern, Sandholm**: structural-mechanism-design for AI applications. Their work primarily lives on the Arrow/Balinski-Young axes; our work extends to the third axis. The combined picture: structural-mechanism-design across all three axes.

**Nayebi 2025**: multi-agent overhead lower bound. The Nayebi axis is a *fourth* axis we do not address here (multi-agent coordination overhead); the multi-agent companion paper considers the multi-agent extension to our third axis.

**Tibebu 2026**: accountability-incompleteness phase transition. A *fifth* axis (accountability) we do not address here.

The triangulation is a starting point, not a comprehensive taxonomy. Other axes (multi-agent, accountability, capability-scaling) are separately addressable.

##### 6.4 The independence-witness discipline

The three-axis triangulation operates in conjunction with our axiom-tightness discipline (`feedback_axiom_tightness_bars`). The three axioms in our impossibility (consistency, solidarity, monotonicity) each have an independence witness, a concrete graph satisfying two of the three but not the third. The independence witnesses are mechanically verified in `Impossibility/AxiomIndependence.lean`. The Hasse classification of axiom-mask implications is in `diagnostic_axioms_mask_only_nontrivial_implication`.

The three independent witnesses establish that each axiom is load-bearing. The Hasse classification confirms no fourth axiom is structurally implied.

The independence-witness discipline is parallel to Arrow's and Balinski-Young's classical arguments: each classical impossibility theorem comes with witness mechanisms confirming axiom-independence. Our axis follows the same discipline.

---

#### 7. Limitations

1. **Three axes, not comprehensive**. The triangulation covers three notable mechanism-design impossibility axes. Other axes (Nayebi multi-agent, Tibebu accountability, Eckersley AI-alignment) are not addressed in this triangulation.

2. **No unification claim**. We do not unify the three axes into a single impossibility theorem. They are structurally distinct.

3. **Object-class non-embedding**. We assert (but do not formalize) that the three object classes (preference profiles, integer allocations, directed governance graphs) do not embed into one another by simple structural inclusion. A formal non-embedding theorem is open follow-up.

4. **Independence-witness discipline at three-axiom level**. Our impossibility's three axioms have independence witnesses; we do not here formalize the analogous independence-witness discipline for Arrow's four axioms or Balinski-Young's two axioms in our substrate. The classical arguments are taken as given.

5. **Strategyproofness as derived**. Our impossibility derives strategyproofness from solidarity ∧ monotonicity, so the impossibility is three-axiom + bridge. This is a structural feature of our axis, not a feature of the classical axes.

6. **No comprehensive crossover analysis**. The implications-for-AI-alignment discussion is informal. A comprehensive analysis of how AI-alignment deployments compound the three axes' ceilings is open follow-up.

---

#### 8. Conclusion

Three impossibility theorems in mechanism-design occupy structurally distinct axes: Arrow 1951 on preference aggregation, Balinski-Young 1982 on discrete allocation, and our 2026 theorem on governance-rule structural admissibility. The three axes operate on different object classes (preference profiles, integer allocations, directed governance graphs), with different axiom sets, and different structural properties.

The third axis has field-level implications: governance-rule structural admissibility on directed graphs with rule-layer axioms is a typed object distinct from the classical axes. It is the alignment-relevant cousin of the classical lineages, addressing the rule layer of typed governance deployments.

The triangulation is a coordinate system, not a unification. The three axes operate non-redundantly; a frontier AI-safety deployment faces all three ceilings simultaneously. The compounded picture is the joint constraint: aggregation-rule × allocation-rule × governance-rule structural admissibility.

For mechanism-design + AI-alignment crossover researchers, the triangulation supplies the precise positioning of our axis relative to the classical lineages. Future work: comprehensive multi-axis analysis incorporating Nayebi multi-agent, Tibebu accountability, and Eckersley AI-alignment as additional axes; formal non-embedding theorem between the object classes; comprehensive crossover analysis of how AI-alignment deployments compound the axes' ceilings.

---

#### References

- **Arrow, K. J.** (1951). *Social Choice and Individual Values*. Yale University Press.
- **Balinski, M., Young, H. P.** (1982). *Fair Representation: Meeting the Ideal of One Man, One Vote*. Yale University Press.
- **Conitzer, V., Procaccia, A.** (multiple). Social-choice for AI alignment.
- **Eckersley, P.** (2019). Impossibility and Uncertainty Theorems in AI Value Alignment. *Workshop on Cooperative AI*.
- **Gibbard, A.** (1973). Manipulation of Voting Schemes: A General Result. *Econometrica*, 41(4): 587-601.
- **Halpern, J. Y., Pass, R.** (multiple). Game-theoretic foundations for AI alignment.
- **Nayebi, A.** (2025). Intrinsic Barriers and Practical Pathways for Human-AI Alignment: An Agreement-Based Complexity Analysis. *arXiv:2502.05934*. AAAI 2026 oral.
- **Satterthwaite, M.** (1975). Strategy-Proofness and Arrow's Conditions. *Journal of Economic Theory*, 10(2): 187-217.
- **Sen, A.** (1970). The Impossibility of a Paretian Liberal. *Journal of Political Economy*, 78(1): 152-157.
- **Tibebu, H.** (2026). The Accountability Horizon: An Impossibility Theorem for Governing Human-Agent Collectives. *arXiv:2604.07778*.
- **Young, H. P.** (1994). *Equity: In Theory and Practice*. Princeton University Press.

##### Lean substrate references

- `Legitimacy.reachable_peer_relative_decisive_stage_obstructs_diagnostics`
- `Legitimacy.complete_first_effective_obstructs_diagnostics_via_reachable`
- `Legitimacy.binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction`
- `Legitimacy.peerRelativeHead_complete_impossibility`
- `Legitimacy.weakestWithStrongerPeerNode_structural`
- `Legitimacy.representedPeer_obstructs_diagnostics`
- `Legitimacy.peerRelativeNode_not_structural`
- `Legitimacy.decisionSystem_solidarity_monotonicity_imply_strategyproof`
- `Legitimacy.solidarity_monotonicity_imply_strategyproof`
- `Legitimacy.majorityQuorumRule_fails_arrow_triple` (direct multi-principal Arrow obstruction; `Results/MultiPrincipal.lean`).
- `Legitimacy.multi_principal_pairwise_achievability_with_majorityQuorum_obstruction` (pairwise-achievability frontier for the three Arrow axioms; `Results/MultiPrincipal.lean`).
- The three independence witnesses in `Impossibility/AxiomIndependence.lean` (`shortListGraph`, `bobAbsoluteGraph`, `bobRelativeGraph`).
- The Hasse classification `diagnostic_axioms_mask_only_nontrivial_implication`.
- The four collapse theorems for the non-peer-relative escape in `Results/NonPeerRelative.lean`.

##### Companion artifacts

- `papers/03-impossibility-theorem.md`, long-form formalization paper.

## 8. Conclusion: Where This Program Sits

The positioning is deliberately bounded. The program contributes a typed governance-rule substrate, mechanically checked theorem surfaces, executable audit fixtures, and structural ceilings. The adjacent literatures remain adjacent because they study different objects: preferences, resource allocations, behavioral safety cases, verifier architectures, or information-theoretic bottlenecks. The program sits in the AI safety formal-methods space as a rule-layer structural audit and theorem program with the scope qualifiers stated in the chapters above.

---

*Part of the Legitimacy program: a machine-checked semantic legitimacy kernel with a Rust extractor and Lean 4 proofs. Repository: github.com/abenenson/legitimacy; project page: adambenenson.com/projects/legitimacy. Companion manuscripts: "Semantic Legitimacy Kernels: A Machine-Checked Compiler Target for the Governance Layer of AI Agents," "A Verified Impossibility Theorem for Peer-Relative Governance," and "Which Governance Structures Survive Unbounded Capability? Capacity and Stability Bounds for AI Governance Graphs."*
