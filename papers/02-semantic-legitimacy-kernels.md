# Semantic Legitimacy Kernels: A Machine-Checked Compiler Target for the Governance Layer of AI Agents

*Adam Benenson, 2026*

---

## Abstract
We do not judge a program memory-safe from a few tests; we compile it against a type system. Yet AI agents now govern what runs, what is remembered, when review is required, and which instruction wins, while their rules are still certified largely through finite evaluation. We propose a comparable compiler target for the governance rule itself. A semantic legitimacy kernel bundles five separately load-bearing runtime obligations with graph diagnostics, a scaling witness, and an explicit bridge contract; a concrete Lean instance proves that the class is inhabited. Two machine-checked theorems give the object operational force. An obstructed rule may go live only after declaring its forced sacrifices, and a governed trajectory either preserves the kernel invariant or emits an indexed sacrifice certificate. A companion impossibility explains why the declaration is necessary: a pipeline that transparently reaches a scarce, structurally peer-relative allocator and preserves its permits downstream cannot keep the full diagnostic package. On a constructed canonical claimant-interaction lift, a shared-substrate theorem then prices that obstruction as a finite, computable capability ceiling. All proofs are checked in Lean 4 with no `sorry`, `admit`, or first-party `axiom`. We reuse classical Arrow/Young/Thomson diagnostics; the novelty is the typed compiler target and bridge contract. A bounded, unverified Rust extractor turns real agent harnesses into graph models, so current rejections are theorem-backed statements about those extracted graphs rather than verdicts on live products.
## Highlights

> **Object of the paper.** A semantic legitimacy kernel is a typed artifact for a governance rule: runtime obligations + graph diagnostics + scaling witness + bridge contract. It is the spine; everything else in the framework either targets it or forces a property of it.

> **Inhabited, not merely defined.** The five runtime obligations are carried by a concrete kernel instance in the Lean model (`permitKernel`), so the object class is non-empty by construction, not by stipulation. `permitKernel` is a minimal non-emptiness witness: it discharges corrigibility on a zero-action-capability surface and compositional safety on an edge-free DAG; richer inhabitants such as `boundaryExitKernel` (an edged causal DAG) and a unit-capability threshold kernel relax each triviality on its own axis.

> **Evidence tier.** Formal object and definitional decomposition over the Lean model; Rust extraction and source-derived graphs are artifact evidence unless promoted by a separate source-to-graph theorem.

**Real-harness audit panel.** Verdicts are theorem-backed statements about the extracted graph models; source-to-graph faithfulness is the declared trusted base (§6).

| Harness surface | Extracted graph | Verdict | Lean anchor |
| --- | --- | --- | --- |
| OpenAI Codex hooks | 16 nodes / 8 edges | rejected: monotonicity | `codexHooksGovernanceAdmissibilityRejectsMonotonicity` |
| Claude Agent SDK hooks | 22 nodes / 8 edges | rejected: monotonicity | `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity` |
| CrewAI hooks | 5 nodes / 1 edge | rejected: monotonicity | `crewAIHooksGovernanceAdmissibilityRejectsMonotonicity` |
| AutoGen approval gate | 1 node / 0 edges | legitimate | `autoGenGovernanceAdmissibilityReviewRequiredLegitimate` |

```{=latex}
\begin{tcolorbox}[figurebox,title=\textbf{Figure 1.} From rule to kernel]
\ttfamily\small
policy / source / fixture $\to$ bounded extractor $\to$ governance graph $\to$\\
runtime obligations + graph diagnostics + scaling witness $\to$\\
semantic legitimacy kernel $\to$ declared sacrifices + monitors\\
\end{tcolorbox}
```

> **Artifact, data, and companion papers.** This paper is one of the Legitimacy program's manuscripts. The machine-checked artifact (Lean 4 theorem stack + Rust audit pipeline), the companion papers, and the claim ledger are in the project repository, github.com/abenenson/legitimacy; project page: adambenenson.com/projects/legitimacy. Verification code anchor: `v1.0.0`. Dual license: MIT OR Apache-2.0.

## 1. Introduction

Agentic AI systems need rule-layer checks in addition to behavior tests. This paper defines one such checkable object: the semantic legitimacy kernel.

The central question for many deployed AI systems is no longer only "did the model produce a good answer?" Many deployed systems now make decisions with lasting effects: they remember facts, call tools, route work, escalate to reviewers, refuse requests, and grant or withhold autonomy. Each of those is a governance decision. The system is deciding who gets a limited resource: tool access, memory, review time, priority, or authority.

This is the object paper, and the kernel is the spine of the framework. The kernel is the positive artifact: a typed bundle that an actual governance rule either inhabits or fails to inhabit. The companion results are organized around it. Paper 03 establishes the forcing impossibility for kernels over pipelines that transparently reach a scarce, structurally peer-relative allocator and preserve its permits downstream; Paper 04 studies the spectral scaling companion as a standalone capacity result. This paper defines the object that both of those target, and shows it is inhabited. The argument has four load-bearing pieces: the decomposition makes the bridge explicit, the inhabitant makes the class non-empty, the forcing theorem makes the sacrifice ledger mandatory, and the artifact makes the object checkable.

Throughout this paper, the running example is the Claude Agent SDK tool-use permission gate. The claimants are proposed tool invocations, users or developers requesting them, and governance layers that can approve, deny, or require review. The estate is the limited permission and review capacity available at that moment. A kernel asks whether the rule that grants, denies, or escalates those tool calls remains coherent when denied requests are removed, request-strength signals are uniformly rescaled by a positive factor, or one request receives stronger supporting evidence.

Once a system does that, ordinary behavioral alignment is necessary but incomplete. A governance decision can fail in two ways. The first is an output failure: it produces a bad outcome. The second is a legitimacy failure: it produces an acceptable-looking outcome through a rule that would not survive inspection, a rule whose verdict changes for one claimant when an already denied claimant is removed (a consistency failure), whose verdicts change when all claim strengths are scaled by the same positive factor (a solidarity failure), whose reward for a stronger claim is a `Permit → Deny` flip for some claimant (a monotonicity failure), or whose individually permitted steps compose into a forbidden global action (a composition-safety failure).

This paper defines a checkable object for that second failure mode: the semantic legitimacy kernel. Think of it as a compiler target for governance rules. We do not ask whether a program "seems memory safe" after running a few tests; we compile it against a type system and reject programs that violate the language's safety discipline. A finite eval suite can show how a policy behaved on tested cases. It does not show whether the underlying rule behaves coherently across related cases. We should compile the governance rule itself against a typed legitimacy target and reject, monitor, or explicitly sacrifice obligations before the rule governs durable state.

The kernel starts after the system has fixed the governance vocabulary. A claimant is a party with standing in the rule. A valid claim is an admissible request or reason. A priority class says which claims are treated as peers. An estate is the scarce permission, memory, authority, or review capacity being allocated. Reduction operators remove irrelevant claims; shock models change shared capacity; claim orderings say when one claim has strengthened. In the Claude Agent SDK gate, those fields distinguish a shell command request, its policy basis, the review tier it belongs to, the available approval path, and the perturbations an audit may apply. The rule either behaves coherently across that declared family of related cases, or it does not.

| Claim | Evidence + Boundary | Formal anchor |
| --- | --- | --- |
| Semantic kernel decomposes into runtime kernel + bridge | Lean theorem; decomposition, not derivation | `isSemanticLegitimacyKernel_`\linebreak`iff_runtime_and_bridge` |
| Runtime kernel has five obligations | Lean object; does not solve value selection | `IsLegitimacyKernel` |
| The kernel class is inhabited | Lean instance; concrete bundle over a permit system; minimal non-emptiness witness | `permitKernel` |
| Bridge carries diagnostic and spectral layers | Unfolded Lean theorem; needs explicit bridge fields | `semanticKernel_iff_runtime_`\linebreak`diagnostic_spectral_layers_unfolded` |
| Bounded extraction can target the kernel | Lean contract + Rust artifact; not arbitrary source semantics | `BoundedExtractorContract` |
| Source-derived case outputs are inspectable | Rust snapshots + parity tests; source-to-graph faithfulness is trusted base unless promoted | extractor reports |

> **Kernel decomposition, informal.** A semantic legitimacy kernel is exactly a runtime kernel plus an explicit semantic bridge. The runtime kernel carries certifiability, observability, corrigibility, compositional safety, and non-vacuity. The bridge carries the graph-diagnostic and scaling obligations. In the Claude Agent SDK gate, this means a clean hook interface is only the runtime half; the bridge must also say how the permission graph behaves under denied-request removal, uniform positive strength scaling, claim strengthening, and capability scaling. Runtime checks alone do not imply the graph or scaling layers.

> **One umbrella, one footprint.** The public spine anchors — including the kernel object, spectral and scaling results, reachable peer-relative obstruction, no-undeclared-sacrifice gate, semantic decomposition, wider-frontier rows, and stateful safety stack — are tied together with concrete premise witnesses by a single umbrella theorem (`spineFootprint`) so that an axiom-footprint check cannot quietly cover only a selected subset of the spine. The kernel decomposition and the forcing obstruction sit in the same footprint by design.

### 1.1 Scope and Limitations

> **Scope and limitations.** A semantic legitimacy kernel does not solve value specification, decide which claimants deserve standing, replace runtime safety, red-teaming, security review, interpretability, or behavioral evaluation, or prove that arbitrary source code compiles to a Lean-certified kernel. It defines the typed rule-layer artifact that such work should target: a checkable object for governance rules that allocate durable authority, memory, tool access, review capacity, or permission among competing claims.

## 2. From Alignment Behavior to Institutional Rule

Most alignment methods begin downstream of the governance question. RLHF, constitutional prompting, process supervision, red-teaming, and guardrail enforcement all shape or inspect behavior. These methods are valuable, but they do not by themselves answer whether the rule selecting, permitting, escalating, refusing, or preserving an action is entitled to govern.

That distinction matters because agentic AI systems now contain institutional machinery:

- memory systems decide which observations become durable beliefs;
- tool gateways decide which proposed actions become executions;
- orchestration systems decide which subagents receive autonomy;
- approval chains decide when user, developer, system, and organizational policies override one another;
- review systems allocate scarce human or automated oversight.

Each of these is a claims problem. There are claimants, scarce goods, admissible reasons, priority classes, and perturbations under which the rule's reasons should remain stable. A memory consolidation policy should not make a hypothesis durable only because an irrelevant weaker hypothesis was present. When a valid action's supporting evidence strengthens, a tool approval rule should not become less permissive toward it. An oversight allocator should not respond to a common capacity reduction by accidentally increasing one peer's review budget while making others absorb the loss.

These are not unusual edge cases. They are the ordinary pathologies of allocation under composition. Social choice, apportionment theory, and mechanism design have long treated such pathologies as structural. AI governance should import that discipline at the rule layer, not only at the preference-aggregation layer.

For readers whose work is RLHF, Constitutional AI, debate, or AI Control: those methods shape and check the policy. This program audits the scaffolding around the policy — the rule layer that allocates authority, memory, tool access, and review among competing claims — a layer most safety cases currently assume rather than check. The two layers are complementary, and the boundary is deliberate: behavioral evidence cannot stand in for rule-layer coherence, and rule-layer coherence does not certify behavior.

The framing is conditional, not universal. If powerful agent systems are to govern without silent legitimacy degradation under composition, scaling, or self-modification pressure, they need some explicit layer that distinguishes merely executable control from legitimate authority. Compilation is the proposed name for that layer.

## 3. The Kernel Target

A semantic legitimacy kernel is a compiled artifact that packages what the governance rule must carry in order to be auditable. In the current formalization, the runtime layer has five obligations, and they are not a wish-list: each is separately load-bearing, the bundle is non-vacuous, and the whole bundle is inhabited by a concrete instance (`permitKernel`) so that the object class is demonstrably non-empty.

First, the rule must be certifiable: governed decisions need checkable witnesses. Second, the rule must be observable: governance state and decision-relevant structure must survive audit. The strengthened observable-determinacy form is semantic rather than merely operational: the formalization requires audit path-independence, so legal audit traversals can be rearranged by independent local swaps without changing the observable final-decision surface.[^02-anchor-1] Third, the rule must be corrigible: authorized supervision must preserve the governance substrate while permitting intervention. Fourth, the rule must be compositionally safe: safe governed targets must preserve safety along modeled causal consequences inside the declared boundary. This boundary-relative obligation does not itself quantify over the kernel's action alphabet or establish safety for arbitrary sequences of permitted actions. Fifth, the rule must be non-vacuous: the governed system must actually govern rather than collapse into empty graphs, permanent refusal, permanent escalation, or deadlock. Each obligation is separately load-bearing: a concrete witness shows that any one can fail while the other four hold, so none is redundant scaffolding (witnesses `independent_certifiable`, `independent_observable`, `independent_corrigible`, `independent_compositional_safety`, `independent_nonvacuous`).

Those five obligations are necessary but not sufficient. Runtime well-formedness alone does not imply legitimacy across denied-claimant removal, positive claim-strength scaling, or strengthened claims. The semantic target therefore strengthens the runtime kernel with graph diagnostics and a scaling witness. The graph-diagnostic layer tests whether the governance rule behaves coherently under changes that should not alter its justificatory structure. The spectral layer exposes how consistency vulnerability and capability pressure scale with the graph's topology.

For the Claude Agent SDK gate, certifiability means the permission verdict carries an inspectable reason, observability means the relevant hook state survives audit, corrigibility means authorized review can intervene without corrupting the rule, compositional safety requires the represented causal boundary to satisfy that safety-preservation condition, and non-vacuity means the gate governs a nonempty claim set with a genuine permit witness while avoiding permanent refusal, permanent escalation, and deadlock. Non-vacuity does not by itself require decision selectivity. Connecting an actual sequence of tool calls to a forbidden outcome requires a separate execution argument; the [finite executed-composition experiment](../docs/executed-composition-v1.md) supplies one for its two-principal sequential model, rather than deriving arbitrary action-sequence safety from the five-axiom bundle.

The kernel is not a scalar score but a product object:

```text
semantic legitimacy kernel
  = runtime obligations
  + graph-diagnostic obligations
  + spectral/scaling witness
  + explicit bridge contract
```

The bridge contract is load-bearing. It prevents a common overclaim: a clean runtime interface does not magically imply social-choice-style diagnostics or spectral robustness. Those layers must be carried explicitly.

## 4. The Forcing Theorem

Why should governance need a kernel at all? Because the kernel's own diagnostic desiderata do not generally coexist, which is precisely what makes the kernel the right object. The impossibility forces the kernel rather than sitting beside it as a competing result. It tells a legitimate rule, on the surfaces where it actually allocates, that it cannot silently keep everything, and must instead declare what it gives up. The kernel records that declaration.

The formal obstruction applies when a real permission pipeline transparently reaches a structural scarce peer-relative allocator and its suffix preserves permits. In the Claude Agent SDK gate, this is the situation where a tool-use request is evaluated against other active requests or review demands, not only against its own local features. On that covered class, the bundled graph-level legitimacy properties cannot all hold.

The exact formal scope is stated in the companion theorem: the pipeline has a transparent prefix, a nontrivial symmetric scarce allocator that is actually reached, and a suffix that preserves the permits granted at that stage. Transparent pass-through stages include logging, observation, or normalization nodes that permit every claimant and therefore do not alter the decision surface. The complete first-effective peer-relative surface theorem is the special case where this reached stage is the first effective surface and the downstream tail is complete in the older sense.

The paper-facing diagnostic core has three graph-diagnostic properties from the Arrow-Young-Thomson tradition named above. Consistency says that removing a denied tool request should not change any other request's verdict. Solidarity says that scaling every claim strength by the same positive factor should preserve every verdict. Monotonicity says that strengthening one valid tool request should not flip any claimant from `Permit` to `Deny`; the obstruction witness is a peer-relative displacement case where another request is denied. In the binary semantics formalized here, solidarity plus monotonicity implies the relevant strategyproofness predicate, so strategyproofness is a bridge-derived consequence rather than an independent fourth diagnostic.

This theorem should be read neither too weakly nor too strongly. It is stronger than a toy counterexample, because it is quantified over a reachable behavioral class and machine-checked: the obstruction needs only claimant symmetry, finite-estate coupling, and a scarce admissible witness, and that class provably contains the canonical median-rule gate, with each field necessary by countermodel. The sharper conclusion, that consistency and monotonicity must each fail, holds on a narrower rank-pinned structural subclass, and the two tiers are formally separated by a max-rule witness that inhabits the broad class while remaining consistent. It is also stronger than a syntactic-position-zero result, because it covers peer-relative stages that occur after transparent governance scaffolding. The older complete first-effective result remains as a machine-checked special case. It has an explicit DAG bridge: if a governed DAG system has a `DAGToBinaryModelMap` to such a binary representative, the impossibility transfers back to the governed system's graph. It is weaker than the slogan "any governance graph containing a peer-relative stage is impossible" — that slogan is false, because an upstream deny-all gate can make a peer-relative stage unreachable, satisfying the graph diagnostics without ever invoking it. The theorem's force lies in its named boundary.

The consequence is the compiler view, and it is what the kernel exists to carry. If a genuinely reached scarce peer-relative decisive stage, under the transparent-prefix and non-denying-suffix scope above, cannot keep the full diagnostic package, then the system must not pretend that an informal constitution, a reward score, or a finite eval suite has settled legitimacy. The rule must compile to the obligations it actually preserves and expose the obligations it sacrifices. The kernel is the object that records both. This forcing relation is one face of the kernel, not the headline: the kernel is the positive bundle; the impossibility is the reason the bundle must include an explicit sacrifice ledger rather than an implicit promise.

The full development of the forcing theorem — including the typeclass-quantified pipeline form, the DAG-to-pipeline model-map contract, the formal independence of the three diagnostics, and the non-peer-relative escape collapse — lives in the companion paper *A Verified Impossibility Theorem for Peer-Relative Governance* and in `lean/Legitimacy/Impossibility/`.

## 4.1 Two Honesty Theorems: No Undeclared Sacrifice, No Silent Degradation

Two machine-checked safety results turn the obstruction into an operational discipline, and they are what make the forcing relation actionable for the kernel. First, the deployment-honesty theorem says that a live obstructed artifact may run only if the forced sacrifices are declared.[^02-anchor-2] It goes past merely cataloguing paradoxes to define what honest deployment means for the obstructed class: a complete peer-relative surface cannot enter live status without its forced sacrifices declared.

Second, the trajectory-honesty theorem says that each governed trajectory either preserves the kernel invariant or exposes an indexed sacrifice certificate.[^02-anchor-3] The same invariant-or-certificate shape extends to covered stateful schedules, with intervention-aware, nondeterministic, and fair infinite-prefix variants.[^02-anchor-4] The result is deliberately scoped: it is a no-silent-degradation theorem for certified governance trajectories and schedules whose steps are explicitly governed or monitored, not a universal alignment theorem.

The two results are complementary, and they bracket the kernel's life cycle. No-undeclared-sacrifice governs entry into live deployment: the compiled rule may sacrifice a diagnostic, but it must say so. Kernel reachability and stateful schedule safety govern motion after deployment: the execution may leave the invariant-preserving branch, but it must carry an indexed certificate rather than silently degrading. Together they define the operational meaning of running honestly: the kernel that the impossibility forces a rule to declare is the same kernel whose preservation the trajectory theorems then track.

A worked peer-relative fixture instantiates deployment honesty and trajectory honesty on the same concrete surface.[^02-anchor-5] The canonical singleton peer-relative graph has empty prefix and empty complete tail; a live compiled artifact over that graph is forced to declare consistency and monotonicity, while the emitted consistency certificate is replayed as an index-zero monitored sacrifice step whose reachability conclusion is supplied by the trajectory theorem. The paired runtime test rejects a peer-relative surface with an empty sacrifice ledger before activation.[^02-anchor-6]

## 5. What the Compiler Emits

A legitimacy compiler should not produce a single moralized label. It should emit a structured governance artifact: which runtime obligations were discharged, which graph diagnostics passed or failed, which vulnerability quantities were measured, which evidence tier supports the result, and which future observations should trigger revision.

This broad output surface is the strongest reason to prefer the kernel framing over a sacrifice-forward framing. The kernel is the object; declared sacrifice is one field inside it. It contains the runtime witnesses, diagnostic verdicts, spectral/scaling quantities, protocol state, extraction provenance, and monitoring conditions that make a governance rule inspectable.

Declared sacrifice is one important output of this compiler, not the whole paradigm. Impossibility theorems are productive when they force design honesty. A governance rule may have good reasons to give up a property: monotonicity to maintain a scarce capacity constraint, solidarity because a priority class is intentionally lexicographic, or consistency because context coupling is part of a security boundary. But then the tradeoff should be declared, bounded, and monitored.

A tradeoff declaration should say:

- which property is sacrificed;
- which theorem or diagnostic makes the sacrifice necessary or observed;
- what magnitude or exposure bound is accepted;
- what evidence tier supports the claim;
- what monitor detects violations beyond the bound;
- what event triggers revision or recompilation.

The same compiler should also emit positive evidence: nondegenerate kernel witnesses, composition-safety proofs or counterexamples, protocol reachability facts, spectral vulnerability bounds, and extraction provenance. This matters because the goal is not to shame every system into declaring failure. The goal is to move governance from narrative compliance to typed evidence.

This changes the engineering culture around AI governance. Today, many systems use cohort-relative thresholds, approval chains, ranking rules, fallback policies, and override layers whose structural tradeoffs are not named. A legitimacy compiler makes those tradeoffs and invariants inspectable. It asks for the same discipline we expect from mature engineering: know which invariant you preserved, which invariant you gave up, why, and how you will detect drift beyond the declared envelope.

## 6. Evidence That the Object Is Buildable: Lean Substrate, Rust Extractor, Real-Harness Audits

The object is not rhetorical and not merely defined. It is inhabited: the Lean development carries a concrete kernel instance, and the repository contains three kinds of evidence around it: Lean theorems, a bounded extraction contract, and a Rust audit pipeline.

First, the Lean development formalizes the kernel, its concrete inhabitant, the diagnostic obstruction, the DAG-to-binary model-map bridge, the semantic bridge, bounded extraction contracts, constructive kernel examples, composition counterexamples, protocol state transitions, spectral quantities, and selected adversarial stability theorems. The kernel class is shown non-empty by exhibiting `permitKernel`, a bundle that discharges all five axioms over a concrete permit system, so the five obligations are jointly satisfiable rather than merely jointly stated. The methodological point is that the formalization separates runtime obligations, graph diagnostics, spectral structure, protocol state, extraction contracts, and empirical Rust behavior.[^02-anchor-8]

Second, the Rust artifact implements an executable governance-audit pipeline. It parses typed policy files and source-derived governance surfaces into graphs, runs diagnostic checks, computes factor exposures and spectral quantities, emits runtime outcome re-verification certificates and audit reports, and tests byte-stable extraction snapshots. The audit covers three surface types and treats each separately. Typed TOML policy models constitute a *modeled* governance surface. Open-source agent harnesses are walked end-to-end against pinned upstream commits: the Codex Rust harness and the MIT-licensed Claude Agent SDK. The proprietary Claude Code product appears as metadata only, since its source is not redistributed. The artifact boundary is explicit: Rust extraction over arbitrary source code is heuristic and is not presently proved sound in Lean; Rust protocol states store checked verdict data rather than Lean-equivalent proof witnesses. The formal claim is a bounded extractor contract. The implementation claim is deterministic, versioned, provenance-rich, byte-stable evidence over committed fixture surfaces. Source-to-graph faithfulness remains part of the unverified trusted base. The Lean theorems govern the extracted `GovernanceGraph` model; the extractor's correspondence with raw syntax is supported empirically rather than proved in Lean.

Third, current audits show why this object matters. Automatic source-extraction rows over contemporary agent-governance surfaces find monotonicity and non-vacuity failures in several synthetic structural probes, with one observed-runtime lane showing a different profile. The current extracted Codex, Claude Agent SDK, and CrewAI hook fixtures include theorem-backed monotonicity rejections over the extracted graphs (`codexHooksGovernanceAdmissibilityRejectsMonotonicity`; `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity`; `crewAIHooksGovernanceAdmissibilityRejectsMonotonicity`).[^02-anchor-7] Consistency and solidarity failures appear only in specification-level examples, not in the automatically extracted graphs; they are exploratory-tier evidence, not theorem-backed. The AutoGen singleton fixture and the AI-Control protocol fixtures pass with a `legitimate` verdict, so the audit discriminates rather than rejecting every surface it touches. The strongest reading is not "every system fails." The stronger reading is more useful: evidence tiers matter, extraction scope matters, and governance artifacts need typed diagnostics precisely because informal inspection misses structural failures and stale tooling can overclaim.

[^02-anchor-1]: Lean: `governance_audit_diamond`; `observable_determinacy_under_adjacent_swap`.

[^02-anchor-2]: Lean: `Legitimacy.Safety.noUndeclaredSacrifice` (the compatibility iff); operator-facing deployment gate `Legitimacy.Safety.noUndeclaredSacrificeImplication` (the README spine entry).

[^02-anchor-3]: Lean: `Legitimacy.Safety.kernelReachabilitySafety`.

[^02-anchor-4]: Lean: `Legitimacy.Safety.stateful_agent_schedule_safety`.

[^02-anchor-5]: Lean: `Legitimacy.Safety.peerSurfaceWorkedExample_noUndeclaredDeployment_and_reachableSacrifice`.

[^02-anchor-6]: Rust: `protocol_compile_rejects_peer_relative_surface_without_forced_sacrifices`.

[^02-anchor-7]: Lean: `codexHooksGovernanceAdmissibilityRejectsMonotonicity`; `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity`; `crewAIHooksGovernanceAdmissibilityRejectsMonotonicity`.

[^02-anchor-8]: Formal anchors: Kernel modules (`LegitimacyKernel`, inhabited by `permitKernel`); Diagnostics modules; Spectral modules; Extract/Soundness; Results/GovernanceAdmissibilityAudit; public spine umbrella `Legitimacy.spineFootprint`.

That honesty is part of the contribution. A field that wants rigorous governance must be willing to say when a claim is theorem-backed, fixture-backed, observed-runtime-backed, specification-backed, or merely a hypothesis.

## 7. Alternative Views and Objections

One alternative view is that alignment should remain behavior-first: if a system behaves well under sufficiently broad evaluations, the rule layer is secondary. The reply is that evals sample behavior, while legitimacy concerns the rule family. A governance rule can pass observed cases and still fail under denied-claimant removal, positive claim-strength scaling, strengthened claims, or composition. Those failures are invisible until the perturbation occurs, and by then the rule may already control durable state.

A second view is that natural-language constitutions are enough. They are legible to humans and flexible under context. The reply is that prose is valuable for deliberation but insufficient as a proof object. It does not define claimant types, reduction operators, priority classes, or admissible shock models with the precision needed for audit. Constitutional AI gets the instinct right by making principles explicit. A semantic legitimacy kernel pushes the same instinct to its engineering conclusion: the constitution should compile.

A third view is that formal legitimacy will be too brittle for real systems. The reply is that the compiler need not formalize all morality. It formalizes declared local justice properties of specific governance rules. When the formal target is too strict, the right output is not failure theatre but a typed account of what remains true, what fails, what is bounded, and what must be monitored.

A fourth view is that tradeoff declarations could normalize avoidable harms. The reply is that silent tradeoffs already exist wherever a system makes structural choices without naming them. A certificate is not permission to harm; it is an accountability object. It gives reviewers a concrete bound, monitor, and revision trigger to contest.

A fifth view treats the paper as only a theorem or systems artifact rather than as a conceptual contribution. The reply is that the paper's primary contribution is a typed object: the semantic legitimacy kernel and its audit interface for rule-layer governance verification. The decomposition is definitional by design: its work is making the bridge fields explicit rather than implied; the inhabitant proves the class is non-empty; the forcing theorem proves why the object must carry an explicit sacrifice ledger; the artifact shows it is operationally checkable. Conceptual framing and theorem-backed object are not exclusive contributions. The formal object is the load-bearing claim.

## 8. Research Agenda

The kernel definition suggests several concrete research tasks.

First, develop typed policy languages for agentic governance. These languages should express claimants, valid claims, estates, priority classes, reductions, shock models, claim-strength orderings, supervisory actions, and recompilation triggers.

Second, build verified kernel checkers. A checker should distinguish runtime well-formedness from graph-diagnostic legitimacy and from spectral scaling behavior. It should also produce machine-readable witnesses, vulnerability bounds, tradeoff declarations, monitoring plans, and recompilation triggers rather than a single pass/fail score.

Third, connect extraction to formal semantics. The near-term practical path is bounded extraction: parse a constrained source or policy surface, emit a canonical graph, and prove or test fidelity over named artifact classes. The longer-term path is a verified extractor or a restricted governance DSL whose operational semantics are formalized directly.

Fourth, standardize evidence tiers for governance audits. Synthetic structural probes, observed runtime corpora, reviewed reconstructions, specification-level models, formal parity fixtures, and full semantic proofs should not be collapsed into one credibility bucket.

Fifth, study adversarial governance. Agentic systems govern actors who adapt. A static kernel is the beginning, not the end. Mechanism design, strategic robustness, decomposition attacks, stateful adversaries, and recompilation protocols should become first-class parts of the legitimacy stack.

## 9. Conclusion

AI systems are becoming institutions in miniature. They allocate authority, memory, permission, risk, and oversight across time. When they do, alignment cannot be only a behavioral predicate. It must include legitimacy: whether the rule governing durable state is entitled to govern.

The practical proposal is simple. Make the constitution explicit. Give it a type system. Compile it to the kernel. The kernel is the positive object; if the rule cannot satisfy the full semantic legitimacy target, the forcing argument says so, and the kernel must declare the sacrifice and monitor the risk. This is not a retreat from alignment. It is a move to the layer where many alignment failures are born.

The constitution needs a compiler, and the kernel is what it compiles to.

## References

[LegitimacyCompanions2026] Benenson, A. A Verified Impossibility Theorem for Peer-Relative Governance; Which Governance Structures Survive Unbounded Capability? Capacity and Stability Bounds for AI Governance Graphs. Companion papers in the legitimacy repository, verification code anchor `v1.0.0`, 2026.

[Arrow1951] Arrow, K. J. Social Choice and Individual Values. Yale University Press, 1951.

[Young1994] Young, H. P. Equity: In Theory and Practice. Princeton University Press, 1994.

[Thomson2019] Thomson, W. How to Divide When There Isn't Enough: From Aristotle, the Talmud, and Maimonides to the Axiomatics of Resource Allocation. Cambridge University Press, 2019.

[Bai2022] Bai, Y., et al. Constitutional AI: Harmlessness from AI Feedback. arXiv:2212.08073, 2022.

[Burns2023] Burns, C., Izmailov, P., Kirchner, J. H., et al. Weak-to-Strong Generalization: Eliciting Strong Capabilities With Weak Supervision. arXiv:2312.09390, 2023.
