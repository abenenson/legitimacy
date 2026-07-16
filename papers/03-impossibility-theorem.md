# A Verified Impossibility Theorem for Peer-Relative Governance

**Version**: 2026-05-12

*Adam Benenson, 2026*

---

## Abstract
No rule that rations scarce permission among an AI agent's competing requests can be consistent, solidary, and cross-claimant monotone at once. We prove this in machine-checked Lean, and prove more: any legitimate rule must declare which of the three it gave up. The result transports the Arrow/Young impossibility lineage to a new substrate, the directed governance pipelines inside AI agents. The obstruction is no toy. It holds over a genuinely behavioral class of allocation rules, and only where the contested stage is actually reached; an upstream deny-all gate is the countermodel showing that hypothesis is necessary. In the permit/deny setting, strategyproofness is not assumed but follows from the other two checks. And the forced sacrifice cannot stay hidden: a companion safety theorem proves a live rule cannot deploy without declaring the guarantees it abandoned. The flaw is priced, too: on the constructed canonical claimant-interaction lift, definitionally `uniK5` with fixed signal `sig5`, a companion composition proves the same structure forces positive consistency vulnerability, hence a finite, computable capability ceiling as modeled capability scales. This join is not a per-input-graph spectral law. The artifact is verified end-to-end, carrying zero `sorry`, `admit`, or first-party `axiom` against a pinned Mathlib. Run on graph models extracted from the OpenAI Codex hooks and the Claude Agent SDK (models, not the live products), both harnesses are rejected, each verdict backed by a named theorem.
## Highlights

> **Main result.** When several requests compete for a scarce resource and one request's verdict can depend on which others are present, three structural checks — consistency, solidarity, and cross-claimant monotonicity — cannot all hold at once. The formal class is the reachable scarce peer-relative binary allocation pipeline (§1.2).

> **Evidence tier.** The impossibility theorem is theorem-backed over formal decision pipelines. Empirical source-walked claims are claims about extracted governance graphs unless separately promoted.

```{=latex}
\begin{tcolorbox}[figurebox,title=\textbf{Figure 1.} The scoped obstruction]
\ttfamily\small
transparent prefix $\to$ reachable scarce peer-relative allocator $\to$\\
non-denying suffix $\to$ forced diagnostic sacrifice\\
(consistency OR solidarity OR monotonicity)\\
\end{tcolorbox}
```

> **Artifact, data, and companion papers.** This paper is one of the Legitimacy program's manuscripts. The machine-checked artifact (Lean 4 theorem stack + Rust audit pipeline), the companion papers, and the claim ledger are in the project repository, github.com/abenenson/legitimacy; project page: adambenenson.com/projects/legitimacy. Verification code anchor: `v1.0.0`. Dual license: MIT OR Apache-2.0.

> **Main theorem: reachable peer-relative obstruction.** The reachable-stage theorem forces a choice: once a real binary governance decision reaches a scarce peer-relative allocator, the rule must give up consistency, solidarity, or cross-claimant monotonicity. In this binary semantics, strategyproofness follows from solidarity plus monotonicity, so it is a derived corollary rather than a fourth independent axiom. Formal scope: a transparent prefix reaches a nontrivial symmetric scarce peer-relative allocator, the allocator is decisive for the relevant claim profile, and the suffix preserves every permit issued by that allocator.

> **The escape is not free.** Dropping peer-relativity does not recover joint legitimacy for nothing: every governing pipeline with no reachable peer-relative stage must pay by collapse, infeasibility, or runtime-kernel exit (`non_peer_relative_collapse_or_infeasible_or_exits_kernel`, under the governance coverage contract). And the two scope qualifiers are proved necessary, not assumed: countermodels show that a denying prefix or a permit-revoking suffix each masks the obstruction (`without_transparentPrefix_denying_prefix_masks_obstruction`, `without_nonDenyingSuffix_permit_revoking_suffix_masks_obstruction`).

> **We refute our own natural conjecture.** A natural conjecture, that bounded self-modification corrigibility is characterized by RG-basin-A membership plus a stratification certificate, is false on the extended kernel substrate: a concrete counterexample exhibits basin-A membership and a valid stratification certificate while failing bounded corrigibility (`RG_basin_stratification_corrigibility_biconditional_fails`). It is a specific biconditional refutation, not a general claim about RG or corrigibility.

> **The audit discriminates.** The diagnostic is not a reject-everything filter: the AutoGen singleton fixture and the five AI-Control protocol fixtures pass with a `legitimate` verdict, while the extracted Codex, Claude Agent SDK, and CrewAI graph models are rejected, each verdict backed by a named Lean theorem over the extracted graph model.

**Real-harness audit panel.** Verdicts are theorem-backed statements about the committed `audit-agent` replay fixtures in `examples/graphs/` (e.g. Codex 16/8); source-to-graph faithfulness is the declared trusted base (§6.1). This is a distinct lane from the live automatic source-extraction table in §6.3, which reports a narrower `refresh-fixtures.sh` synthetic-probe slice of the same harness (e.g. Codex 10/5): same upstream surface, different curated source slice and extraction lane.

| Harness surface | Extracted graph | Verdict | Lean anchor |
| --- | --- | --- | --- |
| OpenAI Codex hooks | 16 nodes / 8 edges | rejected: monotonicity | `codexHooksGovernanceAdmissibilityRejectsMonotonicity` |
| Claude Agent SDK hooks | 22 nodes / 8 edges | rejected: monotonicity | `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity` |
| CrewAI hooks | 5 nodes / 1 edge | rejected: monotonicity | `crewAIHooksGovernanceAdmissibilityRejectsMonotonicity` |
| AutoGen approval gate | 1 node / 0 edges | legitimate | `autoGenGovernanceAdmissibilityReviewRequiredLegitimate` |

---


## 1. Formal Object: Legitimacy Kernels

### 1.1 Kernel thesis

A governance rule can be described, scored, or summarized. This paper asks a different question: can it be *checked*? The object that answers it is a legitimacy kernel: a compiled witness with three layers, runtime obligations, graph diagnostics, and a scaling witness, tied together by an explicit bridge contract. Passing the runtime checks is not enough; the graph and scaling witnesses must be supplied, not assumed.[^lean-semantic-bridge]

That distinction organizes the paper. A scalar governance score is a useful summary, but it cannot say whether a rule stays coherent when a denied claimant is removed, when every claim strength is scaled, when one claim is strengthened, when permitted actions compose, or when capability grows. The kernel is the compiled object that makes those questions answerable. A bounded extractor contract then draws the artifact boundary: for well-formed bounded source inputs, extraction must produce a kernel that satisfies both the five runtime obligations and the semantic bridge.

The impossibility theorem is why the kernel has this shape. On substantive peer-relative allocation rules, the classical graph-diagnostic axioms cannot carry legitimacy by themselves; they must be exposed, measured, and bridged into a richer runtime object rather than collapsed into a scalar label. The rest of the paper follows that object: the three-diagnostic obstruction that forces the shape, the tightness-and-escape frontier, the semantic bridge, the spectral scaling layer, and the executable extractor contract.

Throughout this paper, the running example is the Claude Agent SDK tool-use permission gate. The claimants are proposed tool invocations and the governance layers that can approve, deny, or require review; the scarce estate is permission and review capacity; the peer-relative question is whether one tool request's verdict can change because other requests or review demands are present. Consistency, solidarity, and monotonicity therefore become concrete audit questions about hook verdicts under denied-request removal, uniform positive scaling of request-strength signals, and strengthened permission evidence.

### 1.2 Scope and Limitations

This paper proves a theorem about formal decision pipelines and reports artifact evidence about extracted governance graphs. The theorem applies to the reachable scarce peer-relative class: a transparent prefix reaches a nontrivial symmetric scarce peer-relative allocator, the allocator is decisive for the relevant claim profile, and the suffix preserves that allocator's permits. The obstruction does not reach unreachable peer-relative stages, opaque deny-all prefixes, permit-revoking suffixes, or broad context-dependence that lacks the structural scarcity and symmetry fields.

The extractor boundary is separate from the theorem boundary. Rust source walking and modeled fixtures are reproducible evidence about extracted graphs, not a proof that arbitrary source code has the extracted semantics. The graph diagnostics are Young-lineage structural checks for systems that choose this rule-layer vocabulary; live deployments need separate normative, operational, and source-to-graph evidence before they inherit the formal claim. The spectral and channel-adjacent results are likewise scoped: the capacity comparison uses its stated channel hypotheses, and the Cook-style/DP analogy does not include a formal DP-composition or mechanism-optimality theorem. Within the theorem's scoped class, the constructive obligation is precise: the rule must expose which named diagnostic it sacrifices.

Decisions throughout this paper are binary: allow or deny. The binary range is a deliberate fit to the alignment-gate regime: tool-use permission, output release, capability access, and similar runtime decisions that natively factor into accept-or-block, not a restriction inherited from the substrate. In this binary permit/deny semantics, solidarity plus cross-claimant monotonicity suffices for the paper's strategyproofness predicate. The theorem is one-way: it does not characterize strategyproofness or generalize to continuous or proportional allocation.

### 1.3 Allocation under composed claim structure

When several users, agents, tools, or policies compete for a limited resource, the rule must compare their claims to allocate substantively. A rule is peer-relative when one claimant's result depends on the full set of competing claims, not only on that claimant's individual report. In the Claude Agent SDK gate, a shell-command request is peer-relative if its permit/deny/review verdict changes when other tool requests or governance-layer claims are present. Voting rules that depend on the electorate's preference profile, apportionment methods that distribute seats across states, and priority queues that serve requests based on relative strength are all peer-relative.

When resources are scarce, avoiding peer comparisons forces one of three outcomes: substantive multi-claim allocation collapses, concurrent-claim feasibility is lost, or the pipeline exits the runtime kernel. A non-peer-relative mechanism that maps a claimant's report to an outcome independent of other claims can be made trivially strategyproof — misreporting cannot help — but cannot express resource constraints that couple claimants. Section 3 now separates two levels of the escape analysis. The graph-diagnostic layer proves that monotone non-peer-relative graphs are threshold-structured, that monotonicity plus strategyproofness force claimant-constant behavior, and that over-budget singleton acceptance witnesses finite-estate infeasibility. The pipeline/kernel layer proves the stronger trichotomy: a governing pipeline with no reachable peer-relative stage must either have no substantive permits, fail to handle any concurrent claim profile, or fail the runtime legitimacy kernel.[^03-anchor-4] Under these criteria, the non-peer-relative route remains useful only for claimant-local filters, claimant-constant behavior, vacuous denial, or non-kernel artifacts; the question is what peer-relativity costs in return.

Balinski and Young [Balinski1982] proved that quota, population monotonicity, and house monotonicity cannot be jointly satisfied by the natural apportionment methods. Young [Young1994] develops the broader allocation-rule program around impartiality and consistency, with monotonicity appearing as a domain-specific consequence or auxiliary condition rather than as a primitive of that framework. Our main result extends the Arrow-style axiomatic-obstruction template [Arrow1951] to directed governance graphs. The theorem class is the reached scarce peer-relative decision point: the point where the Claude-style permission gate actually compares competing requests under scarcity rather than merely logging or normalizing them. The exact Lean scope is the reachable structural scarce peer-relative decisive-stage class, with transparent prefixes and permit-preserving suffixes stated in §2. We define three graph-diagnostic properties on peer-relative allocation mechanisms — **consistency** (removing a denied claimant does not change any other claimant's outcome), **solidarity** (homogeneity under uniform scaling of claim strengths), and **monotonicity** (strengthening one claim does not flip any claimant's outcome from `Permit` to `Deny`) — and prove that the structural class generates the displacement and reduction witnesses needed for the obstruction. The older complete first-effective surface theorem remains as the identity/special-case derivation inside this broader reachable-stage formulation. The median-rule gate remains the canonical instance. The formal countermodels show why broad peer-relativity alone, peer-relativity plus finite estate without symmetry, an opaque denying prefix, and a permit-revoking suffix are all insufficient.[^lean-impossibility-core]

The theorem's practical force is complemented by the companion scaling analysis, not proved by it. Paper 04 studies the same represented graph object under spectral vulnerability, capacity, critical capability, Stackelberg, and finite-family RG probes. Those results explain how the kernel's scaling witness should be audited once the impossibility theorem has forced the diagnostic-sacrifice question into the open.

### 1.4 Agentic AI governance as motivating case

We apply the theory to agentic AI governance as the primary case study. AI alignment research has made substantial progress on the behavior side of AI governance: techniques for shaping model outputs through reinforcement learning from human feedback, constitutional AI, and related methods. The legitimacy side, whether the governance rules themselves are internally consistent, non-manipulable, compositionally sound, observable, and certifiable, has received less formal attention.

The distinction matters. A governance rule can produce individually reasonable outputs while failing fundamental consistency checks: removing a denied claimant from the system changes outcomes for other claimants, strengthening a claim flips some claimant from `Permit` to `Deny`, or a sequence of locally permitted actions composes into a globally denied action. These are not edge cases; they are structural properties that follow from the mathematical nature of multi-claimant allocation. Our theorems make the structural nature explicit, and the kernel framing turns that impossibility into a constructive target: a rule must compile to an artifact whose runtime obligations, graph-diagnostic exposures, and spectral scaling behavior are all auditable.

A recurring pattern in deployed AI governance is the reduction of complex governance judgments to scalar scores: reward values in RL, constitutional principle scores, capability thresholds for graduated safety tiers. Scalars are tractable; they compose easily; they enable optimization. They also collapse the structure that the graph-diagnostic properties are designed to preserve. The scalar reduction problem is precisely the gap between individual and collective legitimacy diagnostics. An agent that maximizes a reward scalar R is behaving consistently with R's individual preferences. It is not, in general, behaving consistently with the allocation's collective properties. This is why reward hacking is structural rather than incidental: systems that reduce collective allocation to individual optimization are exactly the systems whose graph-diagnostic sacrifices must be surfaced and tested. The kernel is the constructive answer to that diagnosis; the impossibility theorem is the proof that the answer cannot be replaced by the classical diagnostics alone.

### 1.5 Contributions

1. **Semantic kernel object.** We define the runtime/diagnostic/spectral kernel target used by the theorem and artifact, with the rule-to-kernel compilation pipeline made explicit (formalized in companion paper 02).
2. **Reachable peer-relative obstruction.** We prove that consistency, solidarity, and cross-claimant monotonicity cannot jointly hold for the scoped reachable scarce peer-relative class; the public theorem is the reachable-stage obstruction `reachable_peer_relative_decisive_stage_obstructs_diagnostics` over `[DecisionPipeline P]`. Its allocator-node engine is proved at two tiers (§2.1): the widened behavioral class `symmetric_scarce_coupled_allocators_obstructed`, which provably contains the canonical median-rule gate, and the narrow rank-pinned class `nontrivial_symmetric_scarce_peer_relative_binary_allocators_obstructed`, which additionally forces consistency and monotonicity to each fail (Corollary 2.3); the reachable-stage theorem composes the latter, and the structural headline factors through the widened theorem. The obstruction is not binary-only: §2.3 records a parametric three-valued (escalate) composition inadmissibility (`three_valued_escalationPolicyWitness_composition_inadmissibility`), where a terminal review-required outcome opens a competitive channel absent from the binary range, and notes the parallel multi-principal Arrow obstruction (`majorityQuorumRule_fails_arrow_triple`).
3. **Derived strategyproofness bridge.** In the binary permit/deny semantics, solidarity plus cross-claimant monotonicity imply the paper's strategyproofness predicate. The bridge theorem is `decisionSystem_solidarity_monotonicity_imply_strategyproof`; the four-property impossibility is a corollary.
4. **Tightness and escape.** We prove independence witnesses for each of the three predicates and characterize the non-peer-relative escape as collapse, infeasibility, or runtime-kernel exit.
5. **Operational honesty.** We connect the obstruction to the declared-sacrifice protocol and no-silent-degradation theorems, making the structural choice visible at runtime.
6. **Artifact boundary.** We state the Lean/Rust/extractor boundary so theorem-backed graph claims are not confused with source-faithfulness claims about live products.

The natural public classification is game theory, economic theory, and artificial intelligence: game-theoretic impossibility, implementation under capability scaling, and agent-governance verification are the three audiences that need the same result for different reasons.

### 1.6 Paper organization

§1 defines the formal object, introduces the Claude Agent SDK permission gate as the running example, and states the single scope boundary in §1.2. §2 states the three-diagnostic obstruction theorem, headlined by the three-axiom corollary and deriving strategyproofness through the bridge theorem rather than assuming it; §2.3 records the three-valued (escalate) composition inadmissibility as a first-class companion to the binary result. §3 proves tightness and escape: graph-diagnostic independence, bridge-field witnesses, runtime-kernel independence, the diagnostic-versus-spectral witness, the legitimacy factor space, and the non-peer-relative collapse, then records the Lean-side correspondence for the preceding headline statements. §4 states the semantic kernel bridge, with the two-conjunct semantic-kernel iff as the headline and the unfolded runtime/diagnostic/spectral theorem as its expansion. §5 summarizes companion scaling consequences that are not used in the impossibility proof. §6 states the executable artifact and extractor contract, audit outputs, design consequences, related work, and conclusion.

---

### 1.7 Governance graphs: formal model

#### 1.7.1 Basic definitions

**Definition 2.1 (Claimant)**: A claimant is an entity making a request for governance authorization. In AI systems, claimants may be users, agents, tools, or governance layers (constitutional, harness, user-level). Each claimant i has a *claim strength* s_i ∈ [0, 1] representing the intensity or priority of their request.

In the Claude Agent SDK gate, a claimant can be a proposed tool call, the user instruction supporting it, or the governance layer that demands review before execution.

**Definition 2.2 (Estate)**: An estate E ∈ ℝ₊ is the total resource available for allocation. For binary governance (permit/deny), E = 1. For proportional governance, E represents total allocation.

For the Claude Agent SDK gate, the estate is the limited execution permission and review capacity available for the active tool-use profile.

**Definition 2.3 (Claim Set)**: A claim set C = {(i, s_i) : i ∈ I} is a finite set of (claimant, strength) pairs. |I| ≥ 2 for non-trivial governance.

For the Claude Agent SDK gate, a claim set is the batch of active tool-use requests with their evidence, policy priority, or review urgency scores.

**Definition 2.4 (Governance Node)**: A governance node N is a function N : C → Decision^I × 𝒫(C), where Decision ∈ {Permit, Deny, Escalate, Allocate(x)} for x ∈ [0, 1], and 𝒫(C) is the transformed claim set forwarded to downstream nodes on Escalate decisions. Four node types are distinguished: *binary* (Permit/Deny only), *proportional* (Allocate(x) for some x ∈ [0,1]), *threshold* (decision based on absolute claim strength), and *peer-relative* (decision for claimant i depends on the full claim set composition rather than only on s_i; examples include majority-relative and top-k).

For the Claude Agent SDK gate, a governance node is a hook or policy step that permits, denies, escalates, or forwards a tool request after reading the request profile.

**Definition 2.5 (Governance Graph)**: A governance graph G = (V, E) is a directed acyclic graph where V = {N₁, ..., N_k} is a set of governance nodes and E ⊆ V × V is a set of directed edges with optional claim transforms. An edge (N_i, N_j) with transform T means: when N_i escalates, the transformed claim set T(C) is forwarded to N_j.

For the Claude Agent SDK gate, the graph is the hook-protocol path from registration and request parsing through exact-match denial, review-required escalation, and final permission output.

**Definition 2.6 (Traversal)**: Given a claim set C and a governance graph G with designated root r, the traversal f_G(C) is defined recursively: if r produces decisions D_r for all claimants, return D_r; if r escalates, forward T(C) to r's successors and compose by the fail-closed priority Deny > Escalate > Permit.

For the Claude Agent SDK gate, traversal is the execution of the permission path on the active request profile until each tool call receives a terminal deny, review, or permit verdict.

**Definition 2.7 (Completeness)**: A governance graph G is *complete* for claim set C if f_G(C) terminates and produces a Permit or Deny decision for every claimant in C.

For the Claude Agent SDK gate, completeness means every active tool request receives a terminal permission verdict rather than disappearing into an unresolved hook path.

#### 1.7.2 Graph-diagnostic properties

The following graph-diagnostic properties are formalized in Lean 4. The first three form the paper-facing impossibility core; the fourth is a derived binary permit/deny manipulation-resistance property used by the audit layer. The formal development retains a historical four-predicate bundle, but in the paper prose strategyproofness is treated as a derived property rather than an independent graph-diagnostic property.[^lean-impossibility-core]

Young's two fundamental principles are impartiality and consistency [Young1994]. Impartiality is outside the diagnostic axiom set here. Young's impartiality is a permutation-equivariance condition over interchangeable claimants in an allocation-rule domain. The binary governance-aggregator setting instead identifies claimants by operational role and position in the graph (via `graphDecide`'s position-indexing) rather than by interchangeable identities, so impartiality does not transfer cleanly without adding a separate symmetry layer to the aggregator semantics. Adding such a layer is a possible extension, not an assumption used by the obstruction theorem here.

The three core properties have concrete readings. A governance graph satisfies *consistency* if removing a denied claimant does not affect anyone else's verdict, *solidarity* if uniformly scaling all claim strengths preserves every claimant's verdict, and *monotonicity* if strengthening one claim does not flip any claimant from Permit to Deny. The fourth property, *strategyproofness*, says no claimant can improve their decision by misreporting; in this binary semantics, solidarity and monotonicity together already imply it.

**Graph-Diagnostic Axiom 1 (Consistency)**: G satisfies *consistency* if removing a denied claimant does not change any other claimant's decision. For any claims C and claimants k, j with k ≠ j, if f_G(C)(k) = Deny, then f_G(C)(j) = f_G(C \ {k})(j). A denied claimant is irrelevant; violations mean a claimant's decision is unexpectedly coupled to an unrelated denial.

For the modeled Claude Agent SDK gate, consistency asks whether removing a denied tool request leaves the verdicts for unrelated tool requests unchanged.

**Graph-Diagnostic Axiom 2 (Solidarity)**: G satisfies *solidarity* if scaling all claim strengths by any positive constant α preserves every claimant's decision: for all α > 0 and all j, f_G(C)(j) = f_G(α·C)(j). Scale-invariance. Absolute-threshold gates violate solidarity (doubling claims flips some claimants); peer-relative gates satisfy it naturally.

For the modeled Claude Agent SDK gate, solidarity asks whether multiplying every request-strength signal by the same positive factor preserves each permission verdict.

**Graph-Diagnostic Axiom 3 (Monotonicity)**: G satisfies *monotonicity* if for any claimant i, strengthening i's claim (all else equal) does not cause any claimant j to flip from Permit to Deny. This is a graph-level property over all claimants. Absolute-threshold gates satisfy it trivially (claimants independent); the canonical peer-relative gate fails it by competitive displacement of a different claimant. Node-level monotonicity (strengthening i does not flip i's own outcome from `Permit` to `Deny`) holds, but the impossibility uses graph-level monotonicity over the whole decision surface.

For the modeled Claude Agent SDK gate, monotonicity asks whether stronger evidence for one tool request can accidentally flip any claimant, including another valid request, from `Permit` to `Deny` through competition for review or permission capacity.

**Derived Property 4 (Strategyproofness)**: G satisfies *strategyproofness* if no claimant can improve their decision by misreporting. For all i and all reported s_r > 0, if f_G(C with s_r)(i) = Permit, then f_G(C)(i) = Permit. This is the paper's binary permit/deny manipulation predicate; in the current graph semantics it follows from solidarity ∧ monotonicity (Theorem 2.4).

For the Claude Agent SDK gate, strategyproofness asks whether a tool request can improve its permission verdict by misstating the strength or category of its own claim.

#### 1.7.3 Peer-relative nodes

A node N is *peer-relative* if its output for claimant i depends on any function of the full claim set (not just s_i). Examples: proportional allocation (s_i / Σs_j), majority gate (s_i > Σ_{j≠i} s_j / |I|), top-k selection. A governance graph is peer-relative if it contains at least one peer-relative node. Most practically deployed AI governance systems are peer-relative.

For the Claude Agent SDK gate, a peer-relative node is a permission step whose verdict for one tool request changes when a second request, reviewer, or policy-layer claim enters the active profile.

### 1.8 Model map across the paper

The word "governance graph" is used across related substrates. §1.7 defines the paper-facing DAG model: nodes emit Permit, Deny, Escalate, or Allocate(x), edges may transform claim sets, and traversal is fail-closed from a designated root. This is the operational model the Rust extractor implements directly when it parses policies, hooks, TOML graphs, and source-derived governance surfaces.

The formal substrate is now layered. The broad interface is `DecisionSystem`: a decision process supplies only an operation `decide : P → Profile → Subject → Outcome`. It carries no nontrivial class laws. Following the Mathlib `Equiv` pattern, extensional equivalence and diagnostic congruence are derived theorems from `decide`, not bundled obligations. This is the honest framing: the broad layer is an interface boundary for decision behavior, while theorem-bearing sequential structure enters only in the binary refinement.

`DecisionPipeline` refines `DecisionSystem` to sequential Permit/Deny pipeline decisions over first-party claim profiles. It supplies a node type, node evaluation, profile forwarding, empty pipeline, head composition, append, transparent-prefix normalization, complete-tail predicates, and the abstract `IsPeerRelativeAggregator` predicate stated against node evaluation. Generic binary diagnostics live at the `DecisionSystem`-specialized layer; first-effective surfaces, complete tails, transparent-prefix erasure, and the aggregator obstruction live at this sequential pipeline layer.

`GovernanceGraph := List GovernanceNodeFn` is the canonical concrete binary pipeline instance used throughout the paper, with its `BinaryDecisionPipeline` instance forwarded into `DecisionPipeline`. Each pipeline operation is discharged from the existing `graphDecide`, `filterPermitted`, and list-append API. The transparent-prefix normalization law is the existing `graphDecide_transparentPrefix_append` induction lifted into the instance proof. The headline impossibility theorem ranges over `[DecisionPipeline P]` in its typeclass form; the concrete `GovernanceGraph` theorems are preserved as compatibility shapes and delegate to the typeclass-derived versions. The formal interface and instance live in `lean/Legitimacy/Foundations/DecisionSystem.lean`.

§5 uses a third substrate, weighted symmetric finite graphs, for spectral quantities such as λ₂, consistency vulnerability, capacity, critical capability, and RG flow. That layer measures structural vulnerability of weighted governance topology; it is not the same object as the §2 binary pipeline. Lean supplies a weighted encoding of binary pipelines and, for a pipeline certified as a complete first-effective peer-relative surface, unfolds the chosen complete claimant-interaction carrier. This is a construction lemma, not a derivation that arbitrary peer-relative aggregator witnesses force a complete weighted graph. In the canonical median-rule five-claimant case, the constructed carrier is identified with the existing spectral archetype and imports the discharged λ₂ = 5 theorem.[^lean-gx-18-1] Thus the three-diagnostic obstruction is now headlined on structural scarce peer-relative allocators, with the aggregator predicate serving as the compatibility route on the binary-pipeline side, while the spectral encoding remains formally anchored to the constructed median-rule carrier.

For the DAG substrate, the formal development states an explicit DAG-to-pipeline contract and proves that if a governed system is decision-equivalent to a pipeline representative with a complete first-effective peer-relative aggregator surface, the three-diagnostic obstruction transfers to the governed system's graph. The retained concrete DAG-transfer theorem is stated for the canonical median-rule `GovernanceGraph` surface, while `DAGToPipelineModelMap` is parameterized over arbitrary `[DecisionPipeline P]` targets. The contract is not automatic for arbitrary source-level DAGs, but it is now provable for a worked structural family: a single first-effective peer-relative chokepoint with transparent deterministic prefix stages and permit-preserving downstream refinement admits the canonical binary representative by theorem. The generic DAG bridge is extensible in target type, but the paper currently has one canonical concrete instance, `GovernanceGraph`; a general automatic extraction theorem from arbitrary source-level DAGs and a general DAG-to-spectral-graph model-map theorem remain future work. This paper therefore names the layers explicitly rather than treating them as definitionally identical.[^lean-model-map]

| Claim | Status | Evidence tier | Boundary | Formal anchor |
| --- | --- | --- | --- | --- |
| Reachable peer-relative obstruction | Proved | Lean theorem | Requires transparent prefix, reachable allocator, non-denying suffix | `reachable_peer_relative_decisive_stage_obstructs_diagnostics` |
| Complete first-effective surface is a special case | Proved | Lean theorem | Special case, not the full theorem | `complete_first_effective_implies_reachable_peer_relative_decisive` |
| Strategyproofness is derived | Proved | Lean theorem | Binary permit/deny semantics | `decisionSystem_solidarity_monotonicity_imply_strategyproof` |
| Three-valued (escalate) composition is inadmissible | Proved | Lean theorem | Parametric over `EscalationPolicyWitness` first-stage policies | `three_valued_composition_inadmissibility` / `three_valued_escalationPolicyWitness_composition_inadmissibility` |
| Multi-principal Arrow obstruction | Proved | Lean theorem | 3-principal/3-property majority-quorum witness; positioned in the positioning companion | `majorityQuorumRule_fails_arrow_triple` / `multi_principal_pairwise_achievability_with_majorityQuorum_obstruction` |
| Non-peer-relative escape collapses | Proved | Lean theorem | Under governance coverage contract | `non_peer_relative_collapse_or_infeasible_or_exits_kernel` |
| Extracted source audits are reproducible | Artifact evidence | Rust byte-stability + Lean graph verdicts | Rust extractor faithfulness is trusted base | audit reports / snapshot tests |

## 2. Three-Diagnostic Obstruction Theorem

### 2.1 Structural scarce peer-relative allocators

Lean now separates broad peer-relativity, structural peer-relative allocation, and the older implementation witness. `PeerRelativeByContext` records genuine context-dependence. The theorem-bearing class is `StructuralScarcePeerRelativeAllocator`: a positive behavioral class for scarce, symmetric, peer-sensitive allocation. In the Claude Agent SDK running example, this is the permission step where active tool requests compete for limited permission or review capacity and the rule treats claimant names symmetrically. The exact formal fields assert peer sensitivity, finite-estate coupling, nontrivial acceptance, scarcity pressure, claimant symmetry, positive own response, and tie-break neutrality. The profile package is `ObstructionGenerator`; the older `OverSubscriptionData` spelling survives as a compatibility alias. The witness-bearing constructor is explicit in the formalization rather than hidden inside the allocator class.[^03-anchor-2]

The older aggregator witness remains only as a compatibility route for earlier pipeline theorems.[^03-anchor-3] It is no longer the public theorem hypothesis. Lean derives the competitive-displacement witness from the explicit obstruction generator and the behavioral laws before reusing the older pipeline obstruction as an implementation route.

**Theorem 2.1 (Reachable Peer-Relative Decisive-Stage Obstruction)**: The reachable-stage theorem proves the three-diagnostic obstruction for this pipeline class.[^03-anchor-5] Consistency, Solidarity, and Monotonicity cannot jointly hold on any binary decision pipeline with a reachable structural scarce peer-relative decisive stage: a transparent prefix, a nontrivial symmetric scarce peer-relative allocator node, and a non-denying suffix that preserves permits from that node. The older complete first-effective surface theorem is recovered as a special case. The represented weakest-with-stronger-peer gate is the concrete structural inhabitant (`weakestWithStrongerPeerNode_structural`) whose represented graph flows through `representedPeer_obstructs_diagnostics`; the canonical median-rule `peerGraph` remains the aggregator-route base case, not a structural-class inhabitant (it enters the widened behavioral class below). Broad peer-relativity, unreachable peer-relative stages, opaque denying prefixes, and permit-revoking suffixes are formally separated by countermodels.

The theorem forces a sacrifice. In any binary governance pipeline where a transparent prefix reaches a scarce peer-relative decisive gate and the downstream non-denying tail preserves that gate's permits, the three graph-diagnostic properties, consistency (removing a denied claimant leaves every other claimant's decision unchanged), solidarity (uniform positive scaling preserves verdicts), and monotonicity (strengthening one claim does not flip any claimant from `Permit` to `Deny`), cannot all hold; the peer-relative gate has to give up at least one. The concrete structural witness is the represented weakest-with-stronger-peer gate; the concrete aggregator-route base case is the canonical median-rule gate `peerGraph`.

For the Claude Agent SDK gate, the theorem says that if a real permission decision reaches a scarce peer-relative review or tool-use gate, the compiled artifact must expose which of consistency, solidarity, or monotonicity it sacrifices.

The positive structural class lives in `lean/Legitimacy/Foundations/StructuralPeerRelative.lean`. Its fields are peer sensitivity, finite-estate coupling, nontrivial acceptance, scarcity pressure, claimant symmetry, positive own response, and tie-break neutrality. Lean names the class `StructuralScarcePeerRelativeAllocator`, exhibits its concrete inhabitant and represented-graph obstruction, separates it by countermodel from broad peer-relativity, and derives the public complete first-effective special case from it.[^lean-impossibility-core]

The checked theorem is stated for `DecisionPipeline` decision systems. Its concrete median-rule `GovernanceGraph` specialization, `effectivePeerRelativeSurface_complete_three_axiom_obstruction_via_pipeline`, is the form used by the canonical representative, protocol, and spectral encoding. The four-property bundle `effectivePeerRelativeSurface_complete_impossibility` is an immediate consequence, not the minimal theorem.

The class-form companion `effectivePeerRelativeSurface_class_impossibility` packages the same consequence for `CompleteFirstEffectivePeerRelativeSurfaceClass`.

**Canonical representative corollary**: The constructive companion theorem strengthens the statement from "the canonical `peerGraph` is impossible" to "every complete first-effective peer-relative surface pipeline is decision-equivalent to `peerGraph`, which is the canonical behavioral representative for this complete class under `GovernanceGraphEquivalent`." The older syntactic-head theorem is recovered by taking `pref = []`.

**Hypotheses**: `ReachablePeerRelativeDecisiveStage G pref node suffix` means `G` is the composed pipeline `pref` followed by `node` followed by `suffix`; `pref` is transparent; `node` is a structural scarce peer-relative allocator; and `suffix` is non-denying for that node, i.e. preserves every permit emitted by `node` on the forwarded profile. The complete first-effective predicate `EffectiveSurfaceForNode node G pref tail` plus `CompleteTailForNode node tail` derives this reachable-stage package. Lean proves both necessity countermodels: `without_transparentPrefix_denying_prefix_masks_obstruction` and `without_nonDenyingSuffix_permit_revoking_suffix_masks_obstruction`.

**Proof sketch**: the proof derives displacement and reduction witnesses from the structural allocator laws, transports them across the transparent prefix and permit-preserving suffix, and then contradicts the relevant graph diagnostic on the canonical representative. The Lean-side correspondence table in Appendix B collects the declaration names for this route.

The structural proof first extracts the bad events. `scarce_symmetric_peer_allocator_has_competitive_displacement` derives claims `claims`, a strengthened claimant `k`, and an affected claimant `j` such that the head permits `j` at `claims` and denies `j` after strengthening `k` while preserving `j`'s own claim. `scarce_symmetric_peer_allocator_has_reduction_violation` derives the reduction-side witness from the same structural class. `structural_scarce_peer_relative_allocator_implies_aggregator` then packages the displacement witness into the retained implementation predicate.

In the Claude Agent SDK reading, the displacement witness is a concrete audit shape: strengthening one tool request can move a different request from permit to deny because the active profile is evaluated comparatively.

The generic aggregator theorem normalizes away transparent prefixes with `DecisionPipeline.effectiveSurfaceForNode_completeTail_decision_equivalent_to_canonical`. Completeness preserves the original head Permit through the tail.

If `G` satisfied `GraphMonotonicityP`, `GraphMonotonicityP_congr` would transfer monotonicity to the canonical singleton pipeline and force the strengthened profile to keep permitting `j`, contradicting the derived head Deny. Lean packages the compatibility route as `binaryDecisionPipeline_isPeerRelativeAggregator_complete_obstruction`, the older three-diagnostic statement as `binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction`, and the structural headline as `nontrivial_symmetric_scarce_peer_relative_binary_allocators_obstructed`.

The concrete `GovernanceGraph` companion remains separately useful: `effectivePeerRelativeSurface_complete_equiv_peerGraph` shows complete first-effective median-rule surfaces are externally decision-equivalent to the canonical singleton `peerGraph`; `peerGraph_not_consistent` and `peerGraph_not_strategyproof` provide the concrete consistency and strategyproofness witnesses used by the canonical representative, class, and retained DAG-transfer forms.

The constructive companion (`lean/Legitimacy/Impossibility/ConstructiveCompanion.lean`) proves the syntactic-head base class has a canonical behavioral representative under `GovernanceGraphEquivalent`: `complete_peerRelativeHead_pairwise_equiv` shows any two complete syntactic-head pipelines are decision-equivalent, and `complete_peerRelativeHead_behavioral_representative_exists` delivers existence of the representative with unbundled hypotheses. The first-effective theorem strictly extends that base by normalizing transparent prefixes before applying the same representative result. Beyond the complete-tail restriction, `peerRelativeHead_behaviorally_equiv_tailSurfaceRepresentative` constructs a canonical behavioral representative for arbitrary peer-relative-head pipelines via the tail residual decision surface, parameterized by `tail`; `peerRelativeHead_unrestricted_uniqueness_refutation` proves that unrestricted uniqueness under a single representative is false (witness: `peerGraph` vs a peer-relative stage followed by a deny-all tail). □

The syntactic-head representative claim is also promoted to a type-level uniqueness statement by quotienting graphs by external decision behavior. Lean defines `governanceGraphEquivalentSetoid` and the quotient type `GovernanceGraphClass`; the theorem `complete_peerRelativeHead_behavior_class_unique` is a genuine `ExistsUnique` over that quotient, stating that there is exactly one behavioral class containing complete peer-relative-head mechanisms. The first-effective theorem then maps transparent-prefix mechanisms into that same external-behavior class. Thus the progression is: concrete equivalence to `peerGraph`, canonical behavioral representative under `GovernanceGraphEquivalent`, and finally uniqueness of the corresponding quotient class for the syntactic-head base with transparent-prefix extension.

**Remark 2.2 (Scope)**: The headline theorem is quantified over `[DecisionPipeline P]`, not over the richer paper-facing DAG object of §1.7 or the weighted spectral `GraphN` substrate of §5. `GovernanceGraph := List GovernanceNodeFn` is the canonical concrete instance, supplied through the binary-pipeline compatibility instance. The exact class is reachable structural scarce peer-relative decisive-stage pipelines: transparent stages may precede the allocator surface, and review/observability/logging suffixes may follow it when they preserve the allocator's permits. A non-transparent upstream short-circuit and a permit-revoking suffix are outside the theorem for necessary reasons witnessed in Lean.

**Corollary 2.3 (Four-Property Impossibility for the Structural Scarce Peer-Relative Allocator Class)**: Every `G` satisfying `EffectiveSurfaceForNode node G pref tail`, `CompleteTailForNode node tail`, and `NontrivialSymmetricScarcePeerRelativeBinaryAllocator node` fails the four-property conjunction Consistency, Solidarity, Monotonicity, and Strategyproofness. The retained `IsPeerRelativeAggregator` corollary is recovered by the compatibility lift, and the median-rule specialization keeps the older `EffectivePeerRelativeSurface G pref tail` and `CompletePeerRelativeTail tail` names.

**Proof sketch**: The three-diagnostic aggregator theorem already contradicts Monotonicity, so adding Strategyproofness cannot restore the bundle. For the median-rule specialization, `effectivePeerRelativeSurface_complete_impossibility` and `effectivePeerRelativeSurface_complete_impossibility_strong` retain the concrete representative route through `peerGraph`.

**Protocol consequence**: Lean also proves `effectivePeerRelativeSurface_live_forces_sacrifice`: any reachable live protocol state whose compiled graph has a complete first-effective median-rule surface must carry a non-empty, justified sacrifice list. This connects the mathematical obstruction to the operational kernel requirement: a live system in this class cannot honestly present itself as fully preserving the diagnostic package. The underlying binary obstruction now ranges over all `IsPeerRelativeAggregator` nodes.

**DAG bridge consequence**: Lean proves `dagPeerRelativeSurfaceMap_pipeline_impossibility`: for a governed system carrying a causal DAG, if `DAGToPipelineModelMap` supplies decision-equivalence to a binary pipeline representative and that representative satisfies the complete first-effective peer-relative aggregator hypotheses, then the governed system's graph cannot satisfy the three decision-system diagnostics. The retained concrete theorem `dagPeerRelativeSurfaceMap_impossibility` specializes this bridge to the canonical median-rule `GovernanceGraph` surface and derives `¬ AllLegitimacyAxioms sys.graph`. This is deliberately a contract theorem, not a claim that arbitrary operational DAGs automatically satisfy the contract. Lean also proves the contract for `SinglePeerChokepointGovernedSystem`: when the carried graph decomposes into transparent deterministic prefix refinement, one first-effective peer-relative chokepoint, and a permit-preserving tail, `singlePeerChokepointGovernedSystem_admits_pipeline_modelMap` derives the parameterized model map, `singlePeerChokepointGovernedSystem_admits_binary_modelMap` preserves the concrete compatibility map, and `singlePeerChokepointGovernedSystem_impossibility` transfers the obstruction to the governed system.

**Widened behavioral class and the two-tier structure.** The structural class above pins scarce-profile behavior through its two rank laws, a deliberate narrowness that buys the sharper conclusion in Corollary 2.3. The obstruction itself needs less. The same three-diagnostic obstruction holds over a widened class whose only fields are claimant symmetry, finite-estate coupling, and a scarce admissible witness: solidarity plus cross-claimant monotonicity force strength-blindness on distinct profiles, symmetry forces a single verdict on the equal-strength variant of the scarcity witness, finite-estate coupling then denies every claimant, and a consistency cascade contradicts individual admissibility. The widened class is genuinely behavioral. It provably contains the canonical median-rule gate, the gate the narrow structural class provably excludes, and each of its three fields is necessary by countermodel. The two tiers are formally separated: the max-rule gate inhabits the widened class while satisfying graph consistency on its canonical surface, so the narrow tier's stronger conclusion that consistency and monotonicity must each fail provably cannot widen, and the structural headline factors through the widened theorem.[^lean-widened-class]

[^lean-widened-class]: Lean identifiers: `SymmetricScarceCoupledAllocator`, `decisionSystem_solidarity_monotonicity_sameIdsMetadata_blind`, `symmetric_scarce_coupled_allocators_obstructed`, `reachable_symmetric_scarce_coupled_stage_obstructs_diagnostics`, `peerRelativeNode_symmetricScarceCoupled`, `peerRelativeNode_finiteEstateCoupled`, `symmetricScarceCoupled_scarcity_necessary`, `symmetricScarceCoupled_finiteEstate_necessary`, `symmetricScarceCoupled_symmetry_necessary`, `maxStrengthNode_symmetricScarceCoupled`, `maxStrengthNode_graphConsistencyP`, `maxStrengthNode_separates_structural_from_symmetricScarceCoupled`, `structural_scarce_peer_relative_allocators_obstructed_via_coupled`. Modules: `Legitimacy.Foundations.SymmetricScarceCoupled`, `Legitimacy.Impossibility.SymmetricScarceCoupledObstruction`, `Legitimacy.Impossibility.SymmetricScarceCoupledTightness`.

### 2.2 Strategyproofness as a derived bridge

**Theorem 2.4 (Solidarity-Monotonicity Bridge)**: In the binary semantics, solidarity plus cross-claimant monotonicity imply strategyproofness.[^03-anchor-6] For every binary decision system `G : P` with `[DecisionSystem P (List ClaimQ) ClaimantId BinaryDecision]`, Solidarity G ∧ Monotonicity G implies Strategyproofness G.

This bridge is deliberately binary. The decision form is allow or deny, matching the alignment-gate regime of tool-use permission, output release, capability access, and similar accept-or-block runtime gates. In this binary permit/deny semantics, solidarity plus cross-claimant monotonicity is sufficient for the paper's strategyproofness predicate, and the implication runs one way only (§1.2).

Strategyproofness, then, is not an independent axiom here. In any binary decision system, solidarity (uniform positive scaling preserves verdicts) plus monotonicity (strengthening one claim does not flip any claimant from `Permit` to `Deny`) already imply that no claimant can improve their decision by misreporting, so in this semantics strategyproofness is a *derived* property rather than an independent fourth axiom.

For the Claude Agent SDK gate, this means a tool request cannot gain by misreporting once uniform positive scaling preserves verdicts and strengthened claims cannot flip any claimant from `Permit` to `Deny`.

Lean: `decisionSystem_solidarity_monotonicity_imply_strategyproof`.

*Interpretation*: Strategyproofness here is the paper's binary permit/deny manipulation predicate, not a social-choice theorem over preference profiles, alternatives, onto-ness, or dictatorship. The bridge theorem shows that, on the broad binary decision-system semantics, solidarity and cross-claimant monotonicity already rule out beneficial unilateral misreport. The retained concrete theorem `solidarity_monotonicity_imply_strategyproof` delegates through `solidarity_monotonicity_imply_strategyproof_via_decisionSystem`. Thus the paper's main theorem is a three-graph-diagnostic impossibility whose force automatically extends to the four-property target for the same structural scarce peer-relative allocator class.

**Corollary 2.5 (Strategyproofness failure on the canonical peer-relative gate)**: The canonical peer-relative graph `peerGraph` is the median-rule base case of Theorem 2.1 and cannot evade manipulation-resistance by treating Strategyproofness as a fourth independent property. Any graph satisfying the two graph-diagnostic properties Solidarity and Monotonicity is already Strategyproof; for structural scarce peer-relative allocators on complete first-effective surfaces, Theorem 2.1 rules out adding Consistency. The strategyproofness failure observed on the canonical gate is therefore consistent with the three-diagnostic impossibility plus the bridge theorem, not a fourth parallel source of minimality.

*Monotonicity violation* (Lean: `peerGraph_not_monotone`): A(1/4), B(1/2), C(3/4). Baseline: B permitted (countAtMost(1/2) = {A,B}, 4 ≥ 3). Strengthen A to 3/4: for B, countAtMost(1/2) = {B only}, 2 < 3, B denied. Cross-claimant monotonicity violated.

*Consistency violation* (Lean: `peerGraph_not_consistent`): A(1/4), B(1/2), C(3/4), D(1). A is denied; B is permitted in the full set; removing the denied claimant A flips B to denied. The peer-relative threshold depends on set composition.

*Concrete peer-relative witness reading*: the standard peer-relative gate still supplies the operational profile counterexamples used elsewhere in the paper. Node-level monotonicity holds; graph-level cross-claimant monotonicity fails via competitive displacement. The same structure defeats consistency because removal changes context. Strategyproofness then enters two ways: directly on the gate via `peerRelativeNode_not_strategyproof`, and structurally by the bridge theorem because any attempt to keep Solidarity and Monotonicity has already committed to Strategyproofness.

**Corollary 2.6 (Alabama-style Paradox Witness)**: The canonical peer-relative gate supplies an Alabama-style witness: changing the claimant set can decrease an existing claimant's outcome because the peer-relative threshold depends on set composition.

**Corollary 2.7 (Composition Counterexample)**: Two governance nodes N₁, N₂, each individually satisfying Consistency, Solidarity, and Monotonicity, can compose into G = N₁ → N₂ violating Monotonicity. Constructive Lean proof `composition_inadmissibility` in `Results/Composition.lean`. The three-valued strengthening of this counterexample is stated as a first-class result in §2.3.

### 2.3 Three-valued (escalate) composition inadmissibility

The obstruction extends beyond the binary range. The same composition failure recurs, and sharpens, once the decision range carries a terminal `Escalate` outcome alongside `Permit` and `Deny`. The binary semantics of §2.1–§2.2 is the headline scope; this subsection records the three-valued composition result as a first-class companion rather than a footnote, because escalation changes the structural reason the obstruction fires.

**Theorem 2.8 (Three-Valued Composition Inadmissibility; Lean: `three_valued_composition_inadmissibility`)**: There exist three-valued governance nodes A and B, each individually node-monotone (`NodeMonotonicity3`), whose composition A → B violates graph-level monotonicity (`GraphMonotonicity3`). The Lean proof is constructive in `lean/Legitimacy/Results/Composition.lean`.

The three-valued failure has a sharper mechanism than the binary one. In a three-valued pipeline, strengthening one claimant can flip another claimant from `Permit` to `Deny` through the composed graph even though both stages are individually monotone. The mechanism is specific to `Escalate`: when the first stage escalates a claimant, that claimant enters the downstream peer-relative pool, and strengthening a separate claimant adds a *new escalated competitor* to the downstream comparison set. Escalate thereby opens a competitive channel absent from the binary range: a claimant who would simply have been permitted or denied at the first stage is instead forwarded into a scarce peer-relative comparison where a stronger peer can displace it. Because the binary range cannot express this coupling, the three-valued result genuinely extends the obstruction surface rather than re-encoding Corollary 2.7.

For the Claude Agent SDK gate, this is the review-required failure shape: a first-stage hook that escalates a tool request to review (rather than permitting or denying it outright) forwards that request into a downstream capacity-bounded review pool, where strengthening an unrelated request can push the escalated one from permit to deny.

**Theorem 2.9 (Parametric escalation-policy obstruction; Lean: `three_valued_escalationPolicyWitness_composition_inadmissibility`)**: The result is parametric, not tied to one hand-built pair. Any monotone first-stage node satisfying the escalation-surface witness `EscalationPolicyWitness` — it is node-monotone, escalates the relevant claimant both before and after strengthening, and forwards the escalated pool as specified — becomes inadmissible when composed with the canonical downstream peer-relative gate: `¬ GraphMonotonicity3 [node, peerRelativeNode3]`. The concrete Theorem 2.8 is the instance at `node = thresholdNode3 (1/4) (1/2)`, whose witness membership is discharged by `thresholdNode3_escalationPolicyWitness`. The `EscalationPolicyWitness` predicate carries a monotonicity field, so it is a non-vacuous governance-policy assumption rather than a raw truth table.

*Interpretation*: the three-valued obstruction is a property of the escalation *channel*, parameterized over the first-stage policy, not an artifact of a single chosen example. This keeps the binary result (Corollary 2.7) as the minimal statement while making explicit that adding a review-required outcome does not escape the composition obstruction; it widens it.

**Multi-principal cross-reference**: a parallel Arrow-style obstruction holds when the governance surface aggregates over several principals rather than several claimants. Lean proves `majorityQuorumRule_fails_arrow_triple` (`lean/Legitimacy/Results/MultiPrincipal.lean`): the majority-quorum rule is unanimous and non-dictatorial but fails independence on a 3-principal/3-property counterexample, so unanimity, independence, and non-dictatorship cannot jointly hold for that witness. The companion `multi_principal_pairwise_achievability_with_majorityQuorum_obstruction` exhibits each pair among the three properties as separately achievable, locating the obstruction exactly at the triple. This is the multi-principal face of the same Arrow lineage; its positioning relative to the assistance-games and multi-stakeholder-delegation literature is developed in the positioning companion. The allocation obstruction of §2 (multi-claimant, single principal) and the multi-principal obstruction are distinct faces of the lineage, not the same theorem.

## 3. Tightness and Escape Characterization

The obstruction is tight in three senses. First, the three graph-diagnostic properties are independently necessary. Second, the kernel bridge and spectral layers do not collapse into each other: the Stage 3 witnesses show that runtime kernel plus diagnostics does not imply `SpectralWellConnected`, that the non-trivial `DAGBinaryBridge` fields cannot simply be dropped, and that each of the five runtime kernel obligations is separately load-bearing. Third, the non-peer-relative escape exists only as a claimant-local or non-kernel collapse, not as substantive feasible kernel allocation.

### 3.1 Graph-diagnostic property independence

Each of the three graph-diagnostic properties in Theorem 2.1 is independently omissible. Concrete Lean mechanisms in `lean/Legitimacy/Impossibility/AxiomIndependence.lean` witness each omission, not informal examples.

**Theorem 3.4 (Consistency independence; Lean: `exists_non_consistent_solid_monotone_strategyproof`)**: There exists a graph satisfying Solidarity, Monotonicity, and Strategyproofness while failing Consistency. Witness: `shortListGraph`.

For the Claude Agent SDK gate, this means an audit can isolate a removal-sensitivity failure while common-review shocks, strengthened-peer checks, and misreport checks remain clean.

**Theorem 3.5 (Solidarity independence; Lean: `exists_non_solidarity_consistent_monotone_strategyproof`)**: There exists a graph satisfying Consistency, Monotonicity, and Strategyproofness while failing Solidarity. Witness: `bobAbsoluteGraph`.

For the Claude Agent SDK gate, this means an audit can isolate a scale-invariance failure without also finding removal sensitivity, a strengthening-induced `Permit → Deny` displacement, or manipulation gain.

**Theorem 3.6 (Monotonicity independence; Lean: `exists_non_monotonicity_consistent_solid_strategyproof`)**: There exists a graph satisfying Consistency, Solidarity, and Strategyproofness while failing Monotonicity. Witness: `bobRelativeGraph`.

For the Claude Agent SDK gate, this means an audit can isolate the case where stronger evidence for one tool request flips a peer from `Permit` to `Deny` while the other graph diagnostics still pass.

The three-property graph-diagnostic set is therefore minimal in the ordinary independence sense. The four-property set is not minimal, because Strategyproofness is derivable from two of the three graph-diagnostic properties.

**Theorem (Complete mask classification; Lean: `diagnostic_axioms_mask_only_nontrivial_implication` in `lean/Legitimacy/Impossibility/AxiomLattice.lean`)**: Consider conjunctions of the four graph-diagnostic properties indexed by a Boolean mask `DiagnosticAxiomMask` (one bit per property). An implication between two such conjunctions is valid for every governance graph iff every conclusion-bit is either already set in the premise, or is the Strategyproofness bit licensed by the Solidarity ∧ Monotonicity premise via Theorem 2.4. Within the 16 × 16 conjunction lattice, the only nontrivial implication is `Solidarity ∧ Monotonicity → Strategyproofness`; every other valid implication is trivial weakening by conjunction. The theorem is scoped to conjunction masks, not to disjunctions or quantified-instance predicates.

For the modeled Claude Agent SDK gate, the mask audit has one nontrivial inference: if the reviewer establishes solidarity and monotonicity for the permission graph, strategyproofness follows in the binary model.

### 3.2 Layer and bridge-field witnesses

The semantic-kernel stack is also tight across layers. Lean proves `runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected`: a constant-permit governed system can satisfy the runtime kernel obligations and the graph diagnostics while failing the spectral well-connected predicate because zero spectral signal forces `cv = 0` and contradicts the positive-CV consequence of `SpectralWellConnected`. Thus §4's semantic bridge must carry the spectral conjunct explicitly; runtime obligations plus graph diagnostics do not derive it.

The DAG bridge contract has its own independent fields. Three Lean field-independence theorems show that the non-trivial bridge fields used to transfer the binary obstruction cannot be silently omitted, and a separate boundary theorem records that causal reflection belongs to the operational model-map contract but is not consumed by the present binary impossibility transfer.[^lean-gx-03s2-2] A redundancy followup sharpened the reflection field specifically: every `GovernedSystem n` already witnesses `DagReflectsGraph dag graph` via its own `dag_reflects_graph` field, so the `reflects_graph` field of `DAGToBinaryModelMap` is definitionally recoverable rather than independently load-bearing.[^lean-gx-03s2-3] The generic target is now `DAGToPipelineModelMap`, with the transfer theorem ranging over arbitrary `[DecisionPipeline P]` representatives, and `SinglePeerChokepointGovernedSystem` is the positive worked example whose graph decomposition admits the model map for the canonical binary peer graph.[^lean-gx-03s2-4] On this non-tautological family the contract is proved from structure; it is not an automatic extraction theorem for every DAG.

Finally, the runtime kernel itself is not a compressed single axiom. Five Lean witnesses establish that each of the five runtime obligations can fail while the others hold, so each is separately load-bearing.[^lean-gx-03s2-1] This per-obligation non-redundancy is distinct from the asymmetric mutual-independence result proved for the three graph-diagnostic axioms in §3.1. The semantic kernel is therefore a typed package because the layers and fields are each separately load-bearing, not because the paper bundles redundant names.

### 3.3 Exposure interpretation

Theorem 2.1 exposes a constraint, not a critique of any specific deployment: reachable structural scarce peer-relative decisive stages in governance pipelines force it (with complete first-effective peer-relative aggregator pipelines as the special case, and the canonical `peerGraph` as the median-rule base case). The governance design question then becomes which graph-diagnostic property to sacrifice, and by how much. Practically, that reframes the audit, from "are you aligned?" to "what is your legitimacy factor exposure?"

### 3.4 The legitimacy factor space

Define the *legitimacy factor exposure* of G:

LFE(G) = (CV(G), SV(G), MV(G), SPV(G), NV(G)) ∈ [0,1]^5

- CV(G) = consistency vulnerability = max perturbation when a denied claimant is removed
- SV(G) = solidarity vulnerability = max verdict change under uniform positive scaling of all claim strengths
- MV(G) = monotonicity vulnerability = max case where strengthening a claim flips some claimant from `Permit` to `Deny`
- SPV(G) = strategyproofness vulnerability = max gain from optimal misreport
- NV(G) = non-vacuity vulnerability = exposure to structurally inert rules under the probe corpus

For the Claude Agent SDK gate, this vector is the audit summary of how much the permission graph is exposed to denied-claimant removal sensitivity, scale sensitivity, competitive `Permit → Deny` displacement, misreporting gain, and vacuous gating.

Theorem 2.1 implies: for every complete first-effective peer-relative aggregator pipeline, the first three coordinates cannot jointly vanish. The bridge theorem implies that any graph with zero solidarity and monotonicity vulnerability also has zero strategyproofness vulnerability, so the zero-exposure point is unreachable for the first four coordinates on that class. The fifth coordinate is an audit/runtime diagnostic rather than part of the Lean impossibility core. The canonical `peerGraph` is the median-rule singleton base case.

### 3.5 Non-peer-relative escape trichotomy

The impossibility theorem (§2) and its spectral strengthenings (§5) apply to *peer-relative* allocation. The first question is whether dropping peer-relativity recovers joint legitimacy. Lean proves that the answer is yes in the existential graph-diagnostic sense, but only as a claimant-local diagnostic escape. At the pipeline/kernel boundary the answer is sharper: if every reachable stage avoids peer-relativity, a governing pipeline must pay by collapse, infeasibility, or kernel exit.

**Definition 3.5.1 (Non-peer-relative graph, `GovernanceGraph.IsNonPeerRelative`)**: G is *non-peer-relative* if for every claimant i and every pair of claim profiles (c, c') that agree on i's own claim but differ on others, G's decision for i is identical. Each claimant's decision factors through their own claim alone.

For the Claude Agent SDK gate, a non-peer-relative rule would decide each tool request from that request's own evidence alone, regardless of which other requests or reviewers are present.

**Theorem 3.5.2 (`nonPeerRelative_escapes_impossibility`)**: There exists a non-peer-relative governance graph satisfying all graph-diagnostic properties. The canonical peer-relative gate impossibility therefore does not extend to the non-peer-relative class as a universal statement.

```lean
theorem nonPeerRelative_escapes_impossibility :
    ∃ G : GovernanceGraph, G.IsNonPeerRelative ∧ AllLegitimacyAxioms G
```

**Theorem 3.5.3 (`nonPeerRelative_is_threshold`, `ThresholdStructured`)**: Every *monotone* non-peer-relative graph is threshold-structured. The monotonicity hypothesis is part of the theorem, not an expositional convenience.

For the Claude Agent SDK gate, the reviewer reads this as a threshold-shape audit: a claimant-local permission rule becomes threshold-structured only after the audit also assumes monotonicity.

```lean
theorem nonPeerRelative_is_threshold
    (G : GovernanceGraph) (hnpr : G.IsNonPeerRelative) (hmon : GraphMonotonicity G) :
    ThresholdStructured G
```

**Theorem 3.5.4 (`nonPeerRelative_cannot_allocate_finite_estate`)**: Let `witness` be a distinct family of claims whose total strength exceeds an estate `E`. If a non-peer-relative graph individually permits every claimant in `witness` on the corresponding singleton profile, then that graph does not respect the finite estate `E`.

For the Claude Agent SDK gate, the audit move is to test singleton approvals against shared review capacity; individually permitted tool requests can overrun the finite permission estate when they arrive together.

```lean
theorem nonPeerRelative_cannot_allocate_finite_estate
    (G : GovernanceGraph) (hnpr : G.IsNonPeerRelative)
    (E : ℚ) (witness : List ClaimQ)
    (hdist : ClaimsDistinct witness)
    (hover : totalStrength witness > E)
    (hindividual : ∀ c ∈ witness, graphDecide G [c] c.id = BinaryDecision.Permit) :
    ¬ RespectsFiniteEstate G E
```

**Theorem 3.5.5 (`nonPeerRelative_monotone_strategyproof_claimantConstant`)**: Every non-peer-relative graph that is both monotone and strategyproof is *claimant-constant*: each claimant has a fixed local decision, but that fixed decision may vary across claimants. Lean does **not** prove a single uniform threshold shared by the whole population.

For the Claude Agent SDK gate, the reviewer checks whether a claimant-local, monotone, strategyproof rule has collapsed into fixed per-request verdict slots rather than allocating a shared permission budget.

```lean
theorem nonPeerRelative_monotone_strategyproof_claimantConstant
    (G : GovernanceGraph) (hnpr : G.IsNonPeerRelative)
    (hmon : GraphMonotonicity G) (hsp : GraphStrategyproofness G) :
    ClaimantConstant G
```

**Theorem 3.5.6 (`nonPeerRelative_allAxioms_escape_collapse`)**: If a non-peer-relative graph satisfies the full graph-diagnostic bundle and individually permits an over-budget family of distinct singleton claims, then it is claimant-constant and cannot respect the finite estate. This is the paper-facing collapse: the escape exists only as a claimant-local diagnostic escape, not as substantive multi-claimant allocation.

For the Claude Agent SDK gate, the audit move is to combine the full diagnostic pass with an over-budget singleton batch; that combination forces claimant-constant collapse and finite-estate infeasibility.

```lean
theorem nonPeerRelative_allAxioms_escape_collapse
    (G : GovernanceGraph) (hnpr : G.IsNonPeerRelative)
    (hall : AllLegitimacyAxioms G)
    (E : ℚ) (witness : List ClaimQ)
    (hdist : ClaimsDistinct witness)
    (hover : totalStrength witness > E)
    (hindividual : ∀ c ∈ witness,
      graphDecide G [c] c.id = BinaryDecision.Permit) :
    ClaimantConstant G ∧ ¬ RespectsFiniteEstate G E
```

**Theorem 3.5.7 (Non-peer-relative escape trichotomy)**: The non-peer-relative escape is formalized as a trichotomy: collapse, infeasibility, or runtime-kernel exit.[^03-anchor-4] For the pipeline model with admitted inputs, partial allocation, reachable stages, and an extracted `LegitimacyKernelData`, every governing pipeline with no reachable peer-relative stage satisfies the trichotomy:

For the Claude Agent SDK gate, the reviewer does not treat "non-peer-relative" as a safe harbor; the audit identifies which branch explains the design: collapse, infeasibility, or exit from the runtime kernel.

```lean
theorem non_peer_relative_collapse_or_infeasible_or_exits_kernel
    (pipeline : Pipeline) (hgov : pipeline.governs)
    (hnonPR : ¬ ∃ stage, IsPeerRelativeStage stage ∧
      ReachableInPipeline pipeline stage) :
    SubstantiveAllocationCollapse pipeline ∨
    PipelineInfeasible pipeline ∨
    ¬ IsLegitimacyKernel pipeline.kernel
```

The three branches are witnessable. `collapseWitnessPipeline` is non-peer-relative and reachable but always denies, so `collapseWitnessPipeline_collapse` proves substantive allocation collapse. `singletonOnlyPipeline` is non-peer-relative and reachable but leaves multi-claim profiles undefined, so `singletonOnlyPipeline_infeasible` proves infeasibility. `hiddenAuthorityExitPipeline` is substantive and feasible with a non-peer-relative reachable stage, but `hiddenAuthorityExitPipeline_exits_kernel` proves the extracted runtime kernel violates observability. The negative theorem `no_non_peer_relative_pipeline_substantive_feasible_and_kernel` states the corresponding no-triple result.

*Interpretation*: the formal escape is narrower than the rhetorical shortcut. Lean proves existence of non-peer-relative graphs satisfying all graph-diagnostic properties. Threshold structure appears only under monotonicity; monotonicity plus strategyproofness collapse behavior to claimant-constant local decisions; and finite-estate feasibility fails once an over-budget family of distinct singleton claims is individually accepted. The pipeline theorem then closes the structural objection: avoiding reachable peer-relativity must either deny/vacuate substantive allocation, stop handling concurrent claims, or leave the runtime legitimacy kernel. The escape stays useful for claimant-local filters: spam detection, moderation gate-keeping, one-item-at-a-time guards, where the question is "does this individual item meet the bar?"; it never recovers substantive multi-claimant allocation. The Talmud's insight survives: rival claims on a contested estate require peer-relative comparison. The impossibility's hypothesis is the condition under which allocation becomes non-degenerate, not an arbitrary restriction.

### 3.6 Lean-side correspondence for headline claims

The declaration-level correspondence table for every headline claim in this paper — theorem names, hypothesis bundles, and module paths — is collected in Appendix B so the argument's spine stays readable here. The route used by the proof sketch of Theorem 2.1 is the first block of that table.

### 3.7 The impossibility-safety canonical pair

The Three-Diagnostic Obstruction Theorem and the runtime safety stack are co-load-bearing results whose joint statement is stronger than either result alone.

**Impossibility (§2, `nontrivial_symmetric_scarce_peer_relative_binary_allocators_obstructed`)**: No pipeline carrying a complete first-effective structural scarce peer-relative surface can simultaneously satisfy graph consistency, solidarity, and monotonicity. Under finite scarcity, the graph cannot satisfy all three global diagnostic predicates; at least one predicate is false, with failure witnessed by the theorem's constructed profiles/perturbations.

**Safety (`kernelReachabilitySafety`, `stateful_agent_schedule_safety`)**: For every kernel-governed trajectory or covered stateful schedule, every reachable state either (a) preserves the kernel invariant, or (b) carries a monitored sacrifice certificate indexed to that state. The disjunction is exhaustive by `Legitimacy.Safety.ReachableStateSafetyConclusion`: there is no hidden third branch.

**Joint reading.** Impossibility alone does not bound the sacrifice's visibility: a harness could satisfy the kernel structural requirements while suppressing the sacrifice signal. Safety alone does not explain why the sacrifice arises: the typed disjunction holds by construction, but its necessity requires the obstruction theorem. Together: the sacrifice is structurally forced (impossibility) and cannot be silent (safety). A harness that satisfies the runtime kernel but omits sacrifice declarations fails at `Legitimacy.Safety.noUndeclaredSacrifice`, which closes the loop directly: the impossibility proof forces the sacrifice; the safety theorem forces the certificate.[^lean-safety-stack]

**Tightness.** The pair is jointly tight in the same sense as §3.1–3.4. The non-peer-relative escape trichotomy (§3.5) shows that leaving the peer-relative class requires collapse, infeasibility, or kernel exit, each a distinct form of sacrifice or structural deficit. There is no route through the peer-relative governance class that avoids both results: impossibility closes the structural path, safety closes the operational path.

The worked fixture `Legitimacy.Safety.peerSurfaceWorkedExample_noUndeclaredDeployment_and_reachableSacrifice` instantiates both jointly on the canonical `exampleGovernanceGraph`, confirming that the pair fires on a concrete runtime artifact rather than in the abstract alone.

---

## 4. Semantic Kernel Bridge

The semantic bridge is the contract that turns the runtime kernel into the stronger artifact used by the rest of the paper. The runtime kernel records five obligations. The semantic kernel records those obligations plus the graph-diagnostic and spectral witnesses needed to interpret a compiled governance artifact as legitimate at the allocation and scaling layers.

### 4.1 Two-conjunct kernel iff

**Theorem 4.1 (Semantic kernel iff runtime plus bridge; Lean: `isSemanticLegitimacyKernel_iff_runtime_and_bridge`)**: For every `LegitimacyKernelData D`, the strengthened semantic target is exactly a runtime legitimacy kernel together with the explicit semantic bridge contract.

The decomposition is exact: a semantic legitimacy kernel combines a runtime kernel (five obligations) with a bridge contract that supplies the diagnostic and spectral witnesses. That bridge must be carried explicitly, since the runtime layer does not derive it. This decomposition is canonical; §4.2 unfolds the bridge into its diagnostic and spectral conjuncts.

For the Claude Agent SDK gate, `IsSemanticLegitimacyKernel` means the permission artifact carries both runtime hook evidence and bridge evidence about the extracted permission graph's diagnostics and spectral exposure.

```lean
theorem isSemanticLegitimacyKernel_iff_runtime_and_bridge
    {n : Nat} {sys : GovernedSystem n} (D : LegitimacyKernelData sys) :
    IsSemanticLegitimacyKernel D ↔ IsLegitimacyKernel D ∧
      KernelSemanticBridge D
```

This framing stays honest about what the theorem proves. The semantic target is a two-part object: the runtime kernel plus the bridge fields that expose the diagnostic and spectral layers. Certifiability, observability, corrigibility, compositional safety, and non-vacuity do not, on their own, imply the graph diagnostics or the spectral predicate; the bridge fields carry that content separately.

### 4.2 Unfolded diagnostic and spectral layers

**Theorem 4.2 (Unfolded semantic bridge)**: The unfolded bridge theorem expands the semantic kernel into runtime, diagnostic, and spectral obligations.[^03-anchor-7] Expanding `KernelSemanticBridge` gives eight visible conjuncts: the five runtime kernel axioms, `AllLegitimacyAxioms sys.graph`, `SpectralCarrierRepresentsGraph sys.graph D.spectralGraph D.spectralSignal`, and `SpectralWellConnected D.spectralGraph D.spectralSignal sys.graph.weightedSize_atLeastTwo`.

For the Claude Agent SDK gate, the unfolded bridge says that a permission-gate certificate is incomplete unless it reports the five runtime obligations, the three graph diagnostics, and the spectral scaling witness for the modeled hook graph.

The compatibility theorem `semanticKernel_iff_runtime_diagnostic_spectral_layers` preserves the earlier paper-facing name for the same decomposition. The direction is decomposition of a strengthened contract, not derivation of diagnostics, carrier-grounding, or spectral structure from runtime alone. The Stage 3 witness `runtime_kernel_and_diagnostics_does_not_imply_spectralWellConnected` is the guardrail: even runtime plus graph diagnostics can fail the spectral-layer conjuncts. The cleaner kernel-only corollary `runtime_kernel_does_not_imply_spectral_well_connected` (probe 91) drops the diagnostics conjunct from the same constant-permit zero-signal witness.

### 4.3 Bridge contract in the paper architecture

The bridge theorem explains the dependency order. §2 proves that the classical graph-diagnostic layer cannot stand alone on reachable structural scarce peer-relative decisive stages (with complete first-effective peer-relative aggregator surfaces as the special case). §3 shows that the layers and bridge fields are independently necessary. §4 packages those facts into the semantic kernel object: a compiled artifact is not merely a runtime monitor and not merely a graph satisfying axioms, but a runtime kernel with declared diagnostic and spectral witnesses. §5 identifies the spectral witness as the companion-paper scaling boundary, and §6 states the extractor contract that must produce the semantic object from bounded source inputs.

---

## 5. Companion Scaling Consequences (Not Used in the Impossibility Proof)

This section summarizes companion scaling results from paper 04 that are *not* used in the proof of the main impossibility theorem (§2-§4). Readers focused on the impossibility result can skip §5 without loss; the spectral, capacity, and Stackelberg results live in paper 04 and are referenced here only to position the impossibility theorem within the broader legitimacy program.

The spectral results are a companion layer rather than a second proof of the allocation obstruction. The peer-relative obstruction forces declared diagnostic sacrifice; paper 04 asks when the same represented graph can still certify decisions, remain stable under capability pressure, or preserve coarse structure. The full development lives in companion paper 04, *Which Governance Structures Survive Unbounded Capability? Capacity and Stability Bounds for AI Governance Graphs*: §4 gives the capacity ceiling, §5 the Stackelberg stability limit, §6 the bifurcation boundary, §7 the multi-decision generalization, §8 the Shannon negative bridge, and §9 the finite-family RG coarse-graining results.

For this paper, the required fact is architectural. Spectral quantities such as `claimantInteractionGraph`, `C*`, `SpectralWellConnectedAt`, Stackelberg stability, bifurcation, and RG basin membership are bridge fields of the semantic kernel, not extra assumptions that repair the three-diagnostic impossibility. The allocation theorem remains the §2 theorem over reachable scarce peer-relative binary pipelines; the companion scaling layer supplies the certification boundary that the kernel must expose when a represented graph is audited.

| Spectral companion topic | Where the companion paper develops it | Paper-03 role |
| --- | --- | --- |
| Binary-to-weighted graph construction | paper 04, §2 and §4 | Supplies the graph-side carrier used by scaling witnesses |
| Capacity threshold `C*` | paper 04, §4 | Marks when deterministic verifier certification fails under the specified embedding |
| Stackelberg stability limit | paper 04, §5 | Describes the fixed-graph spectral surrogate under capability pressure |
| Bifurcation boundary | paper 04, §6 | Packages capacity admissibility, positive vulnerability, and spectral stability |
| Multi-decision and Shannon boundary | paper 04, §7-§8 | Prevents confusing graph-side `C*` with a fixed noisy-channel Shannon capacity |
| RG finite-family coarse-graining | paper 04, §9 | Records finite-family basin robustness without claiming cross-size universality |

## 6. Executable Artifact: Extractor Contract and Audit Demonstration

For the remainder of this section, product names ("Codex", "the Claude Agent SDK", "CrewAI", etc.) refer to our extracted graph models of those products, not to live-product behavior.

The executable artifact boundary is the source-to-kernel compiler. The Lean contract is intentionally bounded: it specifies what a contracted extractor must produce on well-formed bounded source inputs, and byte-stable parity evidence and committed fixtures, rather than a theorem over Rust operational semantics, tie the production Rust extractor to that contract.

### 6.1 Bounded extractor contract and Rust parity

The bounded-extractor theorem proves soundness only for well-formed bounded inputs satisfying the contract.[^03-anchor-8]

```lean
structure BoundedExtractorContract (extract : KernelExtractor) where
  sourceEvidence :
    ∀ src : ExtractorInput,
      src.WellFormed → BoundedExtractorSourceEvidence src
  runtimeSound :
    ∀ src : ExtractorInput,
      BoundedExtractorSourceEvidence src → (extract src).IsRuntimeKernel
  semanticBridgeSound :
    ∀ src : ExtractorInput,
      BoundedExtractorSourceEvidence src → (extract src).HasSemanticBridge

theorem bounded_extractor_contract_sound
    (extract : KernelExtractor)
    (hcontract : BoundedExtractorContract extract)
    (src : ExtractorInput)
    (hwellFormed : src.WellFormed) :
    (extract src).IsSemanticKernel
```

The contract mirrors the six-section architecture. `sourceEvidence` materializes the bounded-source evidence package from `ExtractorInput.WellFormed`; `runtimeSound` supplies the §1 runtime kernel obligations against that evidence; `semanticBridgeSound` supplies the §4 diagnostic/spectral bridge; and the output target is the semantic kernel whose obstruction, tightness, and scaling obligations §§2-5 expose. The production Rust path supplies the operational evidence: audit snapshots are byte-stable, concrete spectral values are parity-checked against Lean `native_decide` fixtures, and the extractor reports graph diagnostics, factor exposure, spectral analysis, critical capability, non-peer-relativity classification, and declared-sacrifice certificates. Under the bounded-extractor hypotheses this is a preservation/transfer theorem: it carries the contract's evidence to a semantic-kernel conclusion for extractors that satisfy those hypotheses, with the well-formedness boundary below fixing which source inputs are in scope.

For the Claude Agent SDK gate, `BoundedExtractorContract` is the shape of the obligation that would turn a bounded hook-permission source surface into a semantic-kernel artifact with explicit runtime, diagnostic, and spectral evidence.

`ExtractorInput.WellFormed` constrains source shape at the bounded extraction boundary; it is not a tautological precondition that assumes the conclusion. Its definition (`Extract/CanonicalInputs.lean`) conjoins three observable boundary facts the Rust extractor can report without importing Rust semantics into Lean: `byteSize ≤ sizeBound` (the input fits within the declared bounded-extraction budget), `coverageComplete = true` (the extractor reported complete coverage of the discovered source-file set), and `parserErrors = 0` (no parser failures were emitted). Inputs that violate any of those three — over-budget sources, partial-coverage runs, parser-failure runs — fall outside the contract and remain empirical tooling outputs rather than formal kernel witnesses; the soundness theorem makes no claim on them. This characterization heads off the "vacuous bounded soundness" reading: a `WellFormed` precondition that is a concrete bounded-source-shape clause differs from one that assumes the conclusion.

### 6.2 Attack vectors

**Definition 6.2.1 (k-decomposition)**: A *k-decomposition* of a denied action A is a sequence (a₁, ..., a_k) where each a_i is individually permitted, sem(a₁ ∘ ... ∘ a_k) ≡ A, and the graph evaluates each a_i in isolation without semantic composition tracking.

**Theorem 6.2.2 (Decomposition-attack immunity under compositional semantic monotonicity, `csm_no_permitting_decomposition`)**: A graph satisfying *compositional semantic monotonicity* (each node carries a running semantic hash of composed intent and denies when the hash matches a denied pattern) admits no permitting decomposition: `Decomposition` under a CSM node is uninhabited (Lean proof in `lean/Legitimacy/Attacks/Decomposition.lean`).

**Lemma 6.2.3 (Kernel deny-bottom invariant, `Legitimacy.finalDecisionSuffixMergeTrace_preserves_deny`)**: The audit kernel's final-decision merge has terminal `deny` as its bottom element. Once a claimant has terminal `deny`, no later sequence of in-kernel final-decision merges can revive that claimant to `escalate` or `permit`. The graph-side corollary `Legitimacy.noEntrySeedSuffixMergeExtension_preserves_terminal_deny` quantifies over append-only suffixes that do not seed fresh entry-node claims, under the explicit traversal contract that the suffix contributes only later merge decisions for the claimant. The Boolean projection consumed by the executable parity check is `Legitimacy.deniedDecisionsRemainDenied_eq_true_of_noEntrySeedSuffixMergeExtension`.

*Remark*: The converse direction (monotonicity violation ⟹ 2-decomposition existence) follows informally from the peer-graph witness in §2.2 but is not separately formalized.

**Definition 6.2.4 (Sovereignty inversion)**: In the formal attack model, sovereignty inversion is a predicate over a layer evaluation and a list of overrides: `SovereigntyInversion eval ovs` holds when some listed override targeting a lower-priority layer changes the evaluation of a strictly higher-priority layer.

**Theorem 6.2.5 (`strat_immune_to_inversion`)**: An override list `ovs` carrying a `StratificationCertificate eval ovs` over a `LayerEval` cannot suffer sovereignty inversion: `¬ SovereigntyInversion eval ovs`. Every override in the certified list must come with a proof of `AdmissibleOverride` for its target layer. This is a layer-evaluation / override-list theorem, not a `GovernanceGraph` theorem. Formalized in `lean/Legitimacy/Attacks/Sovereignty.lean`.

### 6.3 Audit demonstration on extracted graphs

*This subsection demonstrates the audit pipeline on extracted graph models of named open-source agent harnesses. The findings exhibit how the kernel obligations and graph diagnostics surface on real extraction targets; they are not used as premises for any theorem in §§1–5. Faithfulness of each extraction to live-product behavior is the unverified empirical assumption disclosed in the abstract.*

The Legitimacy extractor runs the canonical nine-element audit inventory: three graph-diagnostic primitives (consistency, solidarity, monotonicity), the derived strategyproofness check (Theorem 2.4 makes this a consequence of solidarity ∧ monotonicity rather than an independent primitive), and five kernel-axiom graph-side projections (certifiability, observable determinacy, corrigibility, compositional safety, non-vacuity). The compositional-safety projection is not merely a one-suffix check: Lean separately names the kernel deny-bottom merge invariant and proves the no-new-entry suffix corollary above, while Rust continues to execute the canonical permissive-sink witness. It also emits a three-paradox suite, a spectral analysis, and the five-dimensional factor exposure report. The public empirical taxonomy is: five automatic source-extraction rows, five below-threshold sweeps, one observed-runtime example, plus specification-level case studies. The audit covers three surface types and treats each separately: (i) typed TOML policy *models* of published surfaces (e.g., the Claude Agent SDK permission model), (ii) open-source agent harnesses *source-walked* end-to-end against pinned upstream commits (the Codex `codex-rs` harness and the MIT-licensed Claude Agent SDK), and (iii) the proprietary Claude Code product, treated as *metadata-only* in `audits/observed-runtime/claude-code-hooks/` since the source is not redistributed. The table below covers the second class (synthetic structural-probe extraction over open-source agent code). These are the *live automatic extract* over the curated `audits/fixtures/sources/leaderboard/` slices, a distinct lane from the panel's frozen, theorem-backed `audit-agent` replay fixtures in `examples/graphs/`. The Codex row here is the 10-node / 5-edge synthetic probe over the five-file `codex-hooks` slice, whereas the panel's 16/8 graph is the `examples/codex-cli-fixture` audit-agent fixture the Lean witness quantifies over; both are honest views of the same upstream hook surface at different scopes. Current results cover five systems (2026-04-27; generated by `scripts/refresh-fixtures.sh`):

```{=latex}
\begingroup\fontsize{6.4}{7.5}\selectfont\setlength{\tabcolsep}{2pt}\renewcommand{\arraystretch}{1.15}\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.58in}>{\raggedright\arraybackslash}p{0.98in}rrccccccccc>{\raggedright\arraybackslash}p{0.60in}>{\raggedright\arraybackslash}p{0.62in}>{\raggedright\arraybackslash}p{0.78in}@{}}\hline System & Scan root & Nodes & Edges & C & S & M & SP & Cert & Obs & Corr & Comp & NV & Regression probes & LFE & Notes \\\hline\endfirsthead
\hline System & Scan root & Nodes & Edges & C & S & M & SP & Cert & Obs & Corr & Comp & NV & Regression probes & LFE & Notes \\\hline\endhead
Codex & \texttt{audits/fixtures/sources/leaderboard/codex-hooks} & 10 & 5 & ok & ok & \textbf{FAIL} & ok & ok & ok & ok & ok & \textbf{FAIL} & append-review & \texttt{[0,0,1,0,1]} & automatic synthetic probe \\ Claude Agent SDK & \texttt{audits/fixtures/sources/leaderboard/claude-agent-sdk-hooks} & 15 & 0 & ok & ok & \textbf{FAIL} & ok & ok & ok & ok & ok & ok & none & \texttt{[0,0,1,0,0]} & automatic synthetic probe \\
OpenClaw & \texttt{audits/fixtures/sources/leaderboard/openclaw-infra} & 53 & 16 & ok & ok & ok & ok & ok & ok & ok & ok & \textbf{FAIL} & none & \texttt{[0,0,0,0,1]} & automatic synthetic probe \\ CrewAI & \texttt{audits/fixtures/sources/leaderboard/crewai} & 5 & 1 & ok & ok & \textbf{FAIL} & ok & ok & ok & ok & ok & \textbf{FAIL} & append-review & \texttt{[0,0,1,0,1]} & automatic synthetic probe with \texttt{--allow-partial} \\
AutoGen & \texttt{audits/fixtures/sources/leaderboard/autogen} & 1 & 0 & ok & ok & ok & ok & ok & ok & ok & ok & ok & none & \texttt{[0,0,0,0,0]} & automatic synthetic probe; single-node governance surface \\\hline\end{longtable}\endgroup
```

**Fixture provenance disclosure.** The CrewAI and AutoGen rows in this
automatic table are frozen test-source regression fixtures, not production-source
coverage of those upstream projects. The CrewAI graph is extracted from
`lib/crewai/tests/hooks/test_tool_hooks.py`; the AutoGen graph is extracted from
`python/packages/autogen-agentchat/tests/test_code_executor_agent.py`. Production
extraction on `lib/crewai/src/crewai` and
`python/packages/autogen-agentchat/src/autogen_agentchat` is not claimed here.

**Minimal-shape disclosure.** AutoGen is a 1-node / 0-edge row in this automatic
table. In the broader leaderboard, Aider, Continue.dev, and LiteLLM proxy policy
are also 1-node / 0-edge observed-runtime rows. These rows are minimal-shape
smoke/regression surfaces and should not be counted as multi-node governance
coverage.

OpenClaw is Peter Steinberger's public open-source agent runtime at
`github.com/openclaw/openclaw`, licensed under MIT, and recorded here as a
widely-used open-source agent runtime. The frozen fixtures and audit
transcripts in this repository audit OpenClaw as a third-party public
leaderboard target under the same synthetic structural-probe method used for
the other source-walked rows. The local audit tooling runs on OpenClaw; that is
a user-of relationship, not authorship of OpenClaw.

Five additional systems were attempted (LangChain, Haystack, DSPy, MetaGPT, and Semantic Kernel) but fell below the governance-function detection threshold on the audited full-repository roots; these are below-threshold attempts rather than negative or positive audit results. The leaderboard records them as a single summary rather than as individual automatic-extraction rows.

One observed-runtime example is tracked separately from the synthetic structural-probe table: the filtered Codex TUI runtime slice audited against the redacted `oss-story` runtime corpus yields a 9-node / 7-edge graph with monotonicity failing, non-vacuity passing, and no paradoxes detected on that observed corpus.

**Headline findings.** The five extraction findings cluster into structural patterns the impossibility theorem makes legible:

1. *Three of five extractions fail non-vacuity* under the structural probe; the Claude Agent SDK and AutoGen do not.
2. *The extracted Codex, Claude Agent SDK, and CrewAI graph models fail monotonicity under the canonical production ranking*. The same extracted graph models also remain rejected under the polarity-aware review-required lattice (§6.6.5). The cross-provider contrast is structural rather than a legitimacy flip: the extracted Codex hook graph carries registration-node `thresholdGate "hook_registration" 1 .escalate` gates, while the Claude Agent SDK model's corresponding deny outcomes are literal `exactMatch`.
3. *The extracted OpenClaw `audits/fixtures/sources/leaderboard/openclaw-infra` graph* still passes consistency, solidarity, monotonicity, and strategyproofness while failing non-vacuity. The `CLAUDE.md` layered-override mechanism and the allowlist/failover findings remain separate specification-level analyses above the extractor boundary.
4. *Each extracted-graph rejection is backed by a per-harness Lean theorem* rather than only by VM evaluation, one witness per harness; the OpenClaw witness is nonvacuity rather than monotonicity, matching the current extracted fixture.[^lean-gx-06s3-1]
5. *The AutoGen story (and the parallel proprietary Claude Code observed-runtime null) is methodologically important*: empirical claims are conditional on extraction fidelity and must be versioned with their transcripts rather than treated as timeless facts.

**Honest scope on the monotonicity rejections.** The empirical rejections are computed under the production diagnostic with `decisionRank deny=0, escalate=1, permit=2`. The polarity-aware review-required analysis in §6.6.5 keeps the extracted harness graphs rejected under the alternate lattice: the Codex graph remains rejected by `codexHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`, the Claude Agent SDK graph remains rejected by `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`, and the CrewAI graph remains rejected by `crewAIHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`. Two reviewer-grade attack lines deserve explicit acknowledgment. (i) A decision lattice that ranks terminal `escalate` as a legitimate review-required outcome equivalent to `permit` for monotonicity purposes is a defensible alternate axiomatization; under that ranking, the rejection witness on the present graphs still survives for these three harnesses, but the structural reason differs by harness. The extracted Codex hook graph carries named registration-node `hook_registration` threshold gates; the Claude Agent SDK model's corresponding deny outcomes are literal exact matches. (ii) The same critique reaches the synthetic structural probe corpus and `auditGraphDeltas`-side perturbation calculus: a different-but-equally-faithful extractor that omits or renames the `hook_registration` field would alter the rejection. The protocol-level finding the paper claims is therefore the *reported per-harness rank-lowering structure under explicit decision-rank choices*, not a diagnostic-independent theorem.

**Specification-level lane**: typed TOML policy files (`examples/`, using `*.rule.toml` and `*.graph.toml`) find that modeled Claude Agent SDK hook policies admit composition-based permission escalation (monotonicity), and that an internal priority-tiered task-scheduling policy exhibits proportional-allocation Alabama (§2, Corollary 2.6), the correct behavior under the impossibility, not a bug; it is declared under §7 at `impact_bound = 0.20`. The automatic graph regression probe is narrower than that apportionment lineage: it appends a synthetic peer-review node after a sink and checks whether that perturbation rank-lowers an existing claimant. The modeled OpenClaw `CLAUDE.md` layered-override and allowlist/failover findings also belong to this specification-level lane, separate from the automatic `src/infra` extraction row.

**Interpretive case-study lane**: The Anthropic Automated Alignment Researchers incident (reward-hacking the teacher-model evaluator by exploiting majority-answer heuristics) motivates this case study, but the peer-relative monotonicity classification is internal Lean/Rust modeling rather than a claim established by the public Anthropic post. This is not an automatic source extraction. The modeled structure is the same decomposition pattern that Theorem 6.2.2's CSM criterion is designed to block: each individual "choose the most common answer" step is locally permitted by the teacher evaluator; the composed strategy reward-hacks the evaluation. The governance factor exposure is high MV / low CV,SV, consistent with a peer-relative system that preserves consistency and solidarity. Under §7 this would appear as a declared monotonicity sacrifice with a bounded impact floor and explicit monitoring plan.

Legacy leaderboard transcripts are stored in `audits/leaderboard/*-extract.txt`,
with archived and regression graph snapshots in `audits/leaderboard/*-graph.json`.
The theorem-backed Codex and Claude Agent SDK graph fixtures cited by the public
audit-agent lane are stored under `examples/graphs/`.

### 6.4 A formal negative result for bounded corrigibility

A natural conjecture, motivated by the basin classification in companion paper 04 §9 and the stratification proofs of §7, is that bounded self-modification corrigibility is characterized by RG-basin-A membership plus a stratification certificate. We prove this conjecture false.

**Theorem 6.4.1 (`RG_basin_stratification_corrigibility_biconditional_fails`, `Protocol/CorrigibilityRG.lean`)**: On the natural extended kernel substrate carrying spectral, capability, and stratification data, the biconditional "bounded self-modification corrigibility ↔ RG-basin-A membership ∧ stratification-certificate admissibility" is not valid. A concrete counterexample kernel (`counterexample_good_rhs_bad_lhs`, same file) exhibits RG-basin-A membership and a valid stratification certificate while failing bounded corrigibility.

*Interpretation*. The discriminator for bounded self-modification corrigibility is *strictly stronger* than basin-plus-stratification. Naming what does *not* suffice is structurally informative: it rules out the most natural spectral-plus-constitutional composition as a corrigibility characterization, and identifies the gap that the un-bundled corrigibility bridge (named as frontier in §6.6) must close. This is a positive result of negative form: a proved non-equivalence with a concrete counterexample witness. A formal refutation of a natural conjecture is the kind of evidence that terminates bad research directions and redirects effort, against a corrigibility discussion usually carried informally.

### 6.5 Audit protocol specification

The empirical results of §6.3 are the output of a formally specified audit protocol, not benchmarks.

**Inputs**: target system (source-code artifact), claim corpus C = {c₁, ..., c_k} or an explicitly labeled synthetic structural probe corpus, signal range `signalRange ∈ ℚ₊`, tolerance δ ∈ ℚ₊.

**Outputs**: governance graph G extracted from target; the canonical nine-element audit suite over G at corpus C: three graph-diagnostic primitives `check_graph_consistency`, `check_graph_solidarity`, `check_graph_monotonicity`; the derived `check_graph_strategyproofness` (Theorem 2.4); and the five kernel-axiom graph-side projections `check_graph_certifiability`, `check_graph_observable_determinacy`, `check_graph_corrigibility`, `check_graph_compositional_safety`, `check_graph_nonvacuity`; five-dimensional legitimacy factor exposure `LFE ∈ [0,1]^5`; spectral analysis `SpectralAnalysis{cv_bound, localizability_bound, capacity_bound, spectral_gap}`; critical-capability report `C*(G, sig, δ)` with Stackelberg-limit comparison; non-peer-relativity classification `is_non_peer_relative(G)`; optional `DeclaredSacrificesCertificate`. The canonical order and exact wire names are enforced by `scripts/canonical-axiom-inventory.sh`, which is invoked by both `scripts/verify.sh` and `scripts/release-gate.sh`.

**Correctness conditions**: (1) *spectral parity*: concrete spectral tables and selected graph snapshots match the Lean specifications under `cargo test` vs `native_decide` on the committed lattice fixtures; (2) *zero-sorry discipline*: every mathematical theorem claimed as formalized has a zero-`sorry` Lean witness; (3) *fidelity invariant*: production extractor output is byte-identical across runs with the same target input.

**Fidelity requirement**: each audit commits to a baseline hash H(extractor_output). A re-audit of the same target against the same corpus must produce byte-identical output. Drift flags either (a) a non-deterministic extraction bug or (b) target change; either requires investigation before legitimacy conclusions are drawn.

Two things distinguish these audits from benchmark-style evaluation: concrete spectral tables and selected graph snapshots are Rust/Lean parity-checked via `native_decide`, and the production extractor has byte-stable snapshot tests. We do not yet prove a Lean port of production extraction soundness; a full theorem connecting every emitted source-level violation to a Lean-certified witness remains future work.

Accordingly, every source-walked empirical claim in this section is a claim about the extracted `GovernanceGraph`, not about raw source syntax directly. The Rust extractor is a trusted base whose faithfulness to source is supported by byte stability, fixture parity, and provenance, but not proved as a Lean theorem. Scrutiny should fall on this source-to-graph boundary: parser coverage, omitted control flow, and whether the emitted graph is the right abstraction. A challenge to that boundary is not a defect in the Lean proofs over the extracted model.

#### 6.5.1 Observable commutation: compiler self-audit confluence

The audit protocol of §6.5 specifies what the canonical nine-element diagnostic surface emits. A separate, sharper question is whether the compiler self-audit on the audit graph itself produces the same observable surface regardless of the order in which audit nodes are traversed, i.e., whether `check_graph_observable_determinacy` of §6.3 has a discharged commutation consequence on the compiler-audit DAG, or only the inventory check name.

**Theorem 6.5.1 (Compiler-audit traversal confluence, `audit_traversal_confluence`, `lean/Legitimacy/Results/GovernanceAdmissibilityAudit/Fixtures.lean`)**: On the canonical 9-element compiler audit graph `compilerAuditGraph` (one node per canonical inventory check, wired as the linear pass-through DAG `consistency → solidarity → monotonicity → strategyproofness → certifiability → observable-determinacy → corrigibility → compositional-safety → nonvacuity`), every legal topological-order traversal produces the same final-decision surface, and the extracted compiler-audit graph's governance-admissibility verdict is `legitimate` independent of traversal order. The discharge is by exhaustive finite enumeration of all topological orders via `allAuditTraversalsConfluent`, conjoined with the verdict pin from `compiler_audit_is_self_legitimate`; both conjuncts are closed by `native_decide` on the concrete fixture. The semantic lift is now stated separately as `governance_audit_diamond`: a Church-Rosser condition saying that legal audit paths are connected by independent adjacent swaps and each local swap preserves the observable final-decision surface. `observable_determinacy_under_adjacent_swap` records the local commutation law on explicit action lists, and `compilerAuditGraph_governance_audit_diamond_condition` shows that the compiler fixture follows from the general theorem through the canonical-tie-break class. The structural lift of the executable determinism predicate to passthrough-only acyclic graphs remains `auditTraversalDeterministic_of_acyclic_passthrough`; the new diamond theorem is the semantic layer above that operational projection.

*Reading*. This is the first concrete non-toy compiler self-audit theorem in the tree: an unconditional order-invariance statement for the audit surface, paired with a verdict-stable self-legitimacy statement on the extracted compiler-audit graph. The Probe 6 / Observable Determinacy check named in §6.3 and §6.5 inventories the property; Theorem 6.5.1 promotes its observable consequence, commutation of topological-order choice with the final-decision surface, from check name to discharged Lean theorem. The new Church-Rosser theorem separates semantic determinacy from bounded operational checking: canonical-tie-break DAGs satisfy it automatically, adjacent independent actions commute under its local law, and an explicit negative unchecked graph documents why the legal-path/structural-condition boundary is necessary.

---

### 6.6 Discussion

The paper's formal scope is centralized in §1.2. This discussion records what the current Lean tree covers, which engineering choices remain specification-dependent, and which follow-on axes are live research frontiers.

#### 6.6.1 What the Lean proofs cover

The formalization decomposes into five layers; each layer's coverage is enumerated below.

*Foundations and obstruction.* The foundational layer covers the typeclass-quantified Young-lineage obstruction, its compatibility routes, concrete median-rule witnesses, DAG transfer, diagnostic checkers, and the deny-bottom compositional-safety invariant.[^lean-cover-foundations]

*Spectral layer.* The spectral layer covers the peer-relative carrier construction, capacity and critical-capability thresholds, Stackelberg capability-pressure stability, finite `n=5` RG classification, and the negative bounded-corrigibility characterization result.[^lean-cover-spectral]

*Escape and corrigibility.* The escape layer covers non-peer-relative trichotomies, capability-pressure corrigibility under compile-check-preserving recompilation, and the protocol drift/recompile cycle.[^lean-cover-escape]

*Schedule-extraction bridge.* The schedule layer re-presents schedule-to-kernel extraction as an inhabited-type equivalence and validates the per-step witness shape against the Rust mirror, while kernel-step correctness and sacrifice-certificate validity remain Lean-side.[^lean-cover-schedule]

[^lean-cover-foundations]: Lean identifiers: `nontrivial_symmetric_scarce_peer_relative_binary_allocators_obstructed`, `DecisionPipeline`, `structural_scarce_peer_relative_allocator_implies_aggregator`, `binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction`, `GovernanceGraph`, `effectivePeerRelativeSurface_complete_three_axiom_obstruction_via_pipeline`, `decisionSystem_solidarity_monotonicity_imply_strategyproof`, `DAGToPipelineModelMap`, `dagPeerRelativeSurfaceMap_pipeline_impossibility`, `singlePeerChokepointGovernedSystem_admits_pipeline_modelMap`, `Legitimacy.finalDecisionSuffixMergeTrace_preserves_deny`, and `Legitimacy.noEntrySeedSuffixMergeExtension_preserves_terminal_deny`.

[^lean-cover-spectral]: Lean identifiers: `claimantInteractionGraph`, `governance_capacity_alignment_threshold`, `governance_capacity_threshold_C_star_binding`, `phase_transition_at_C_star`, `stackelberg_convergence_limit_iff_zero_consistency_vulnerability`, `concrete_iterated_RG_n5`, `robustness_cheeger_n5`, `robustness_modularity_n5`, `robustness_signal_preserving_n5`, and `RG_basin_stratification_corrigibility_biconditional_fails`.

[^lean-cover-escape]: Lean identifiers: `non_peer_relative_collapse_or_infeasible_or_exits_kernel`, `nonPeerRelative_escapes_impossibility`, `nonPeerRelative_allAxioms_escape_collapse`, `corrigibility_under_recompile`, `corrigibility_under_arbitrary_selfmod`, `recompile_cycle_terminates_drifted`, and `peerGraph_recompile_cycle`.

[^lean-cover-schedule]: Lean identifiers: `schedule_extraction_iff_per_step_witness`, `ScheduleKernelExtraction.fromKernelGovernedTrajectoryAndSchedule`, `KernelGovernedTrajectory`, and the refl-only, oracle-driven, forced-sacrifice, and alternating schedule derivations. Rust mirror: `src/extract/schedule_witness.rs`.

The non-coverage is enumerated at five layers.

*Behavioral and infinite settings.* Behavioral properties of specific AI systems (we model governance rules, not model weights); infinite-capacity agents or continuous claim spaces (results are for finite, discrete governance); automatic reduction from arbitrary operational DAGs to a binary pipeline representative.

*Compositional-safety boundary.* Arbitrary graph rewrites that redirect host edges, introduce new entry-node claim seeds, or otherwise violate the suffix-merge traversal contract used by the compositional-safety corollary; a theorem that every peer-relative aggregator witness induces a complete weighted spectral graph.

*RG and spectral cross-scale boundary.* A size-universal RG equality theorem beyond the five-graph lattice (fixed-point termination is machine-checked via `rgTrajectory_terminates_at_fixedPoint`; the next honest `n=7` statement is an inequality floor at depth `3`, not a lift of the `n=5` point equality); a *universal* terminal-fixed-point theorem at depth `n−2`: the `n=11`/`n=13` probe falsifies the universal version on weak-center bottlenecks (`bottleneck11_bi` at CV=45 vs non-bottleneck 55; `bottleneck13_bi` at 63 vs 78), so the current honest claim is that the terminal-fixed-point property holds on non-bottleneck archetypes only; a general theorem that `SpectralWellConnectedAt` is the correct cross-scale invariant beyond the current finite-family admissible window; robustness of the current basin under arbitrary weight perturbations (`PerturbationBounds.lean` controls node-removal effects rather than Weyl/Davis-Kahan-style spectral drift); a full repeated-game Stackelberg-convergence theorem over explicit equilibrium dynamics (the current tree proves the spectral surrogate in `StackelbergConvergence.lean`, not a richer game-theoretic equilibrium object).

*Adversarial corrigibility frontier.* A non-trivial adversarial bound for self-modification trajectories outside the kernel's own action space, the un-bundled corrigibility bridge theorem linking basin-A graph membership to kernel-level algebra preservation at arbitrary capability scaling. The §6.4 negative result rules out the most natural spectral-plus-stratification characterization of such a bound; the positive bridge theorem requires an architectural un-bundling of the `LegitimacyKernel` corrigibility invariant and is the principal remaining capability-pressure frontier item.

*Extractor soundness boundary.* A governance-admissibility soundness theorem for the production Rust extractor `src/extract/audit.rs` over arbitrary extractor outputs (the present tree proves order-invariant compiler self-audit on the canonical 9-element compiler-audit graph via `audit_traversal_confluence`, verdict-stable self-legitimacy via `compiler_audit_is_self_legitimate`, executable observable-determinacy for passthrough-only acyclic graphs via `auditTraversalDeterministic_of_acyclic_passthrough`, and the semantic Church-Rosser diamond theorem `governance_audit_diamond`, summarized in §6.5.1; the still-open scope is an extractor-wide proof that every well-formed Rust output supplies the required Church-Rosser certificate, not the existence of a non-toy compiler self-audit theorem).

#### 6.6.2 The specification problem

The legitimacy factor model requires that governance rules be specifiable as governance graphs. Natural language governance principles (constitutional AI, RLHF reward functions) are not governance graphs without non-trivial formalization effort. The typed `*.rule.toml` / `*.graph.toml` policy formats provide a structured specification language, but translating "be helpful, harmless, and honest" into a formal policy still requires the same careful judgment as any formal specification. Legitimacy does not eliminate governance ambiguity; for any governance policy written as a governance graph, it checks graph-diagnostic properties, identifies attack vectors, computes LFE, and generates or rejects certificates.

#### 6.6.3 Scale-aware by design

The exact depth-3 equality on `n=5` is the correct shape of the finite-size result. On `n=5`, depth `3` is the terminal coarse state of the non-trivial RG flow `5→4→3→2`, so equality to `(10, δ/10)` is the signature of that terminal state rather than evidence for a universal fixed point shared across all graph sizes. Four converging literature lines favor exactly this reading. Finite-size scaling theory treats observed fixed-point locations in small systems as size-indexed, with systematic corrections to the infinite-size picture [Cardy1988]. Baldwin's extension of Sharkovsky theory to the `n`-od shows that basin and period structure become `n`-parameterized partial orders rather than one universal order [Baldwin1991]. Geometric network RG work studies finite-size scaling directly and reports that excessive coarse-graining filters out slow modes on finite networks [Chen2021]. Laplacian RG on heterogeneous networks likewise takes renormalization seriously while not promising small-`N` universality [Villegas2023].

The paper's scaling claim therefore survives in a narrower and more honest form: hierarchical governance is scale-aware through *two* invariants rather than one. The first invariant is the `n`-specific RG-basin classifier: exact at `n=5`, inequality-based at `n=7`, and tied to a chosen coarse-graining depth. The second is the parameterized cross-scale spectral-hybrid predicate

$$
\mathrm{SpectralWellConnectedAt}(G, s, \theta) :=
\mathrm{SpectralConnected}(G,s)\ \wedge\ \theta \le \lambda_2(G)\,\mathrm{cv}(G, s),
$$

with `SpectralWellConnected` as the default `theta = 17/20` instance of this full conjunction. The displayed product inequality is the `PositiveGovernanceVulnerabilityAt` conjunct, paired with the separate `SpectralConnected` conjunct. The probe-side rational certificates for the current `n=5`, `n=7`, and `n=9` families lie in the admissible threshold interval `[17/20, 46/53]`: `nonbottleneck_archetype_family_admissible_window` proves that all certified non-bottleneck witnesses pass throughout the interval and all certified bottleneck witnesses fail throughout it. For seven archetypes, the certificate-vs-actual-spectral-gap discharge is complete: Lean proves `λ₂(uniK5) = 5`, `λ₂(uniK7) = 7`, and `λ₂(uniK9) = 9` via the corresponding `uniK*_spectralGap_eq_certificate` theorems, and proves `λ₂(bottleneck5) ≤ 1/10000`, `λ₂(bottleneck7_bi) ≤ 1/10000`, `λ₂(bottleneck7_tri) ≤ 1/10000`, and `λ₂(bottleneck9_bi) ≤ 1/10000` via the corresponding bottleneck upper-bound theorems. The n=7 bottleneck definitions are now no-overlap weak-cluster graphs: `bottleneck7_bi` is a 3-block and 4-block joined only by weak cross-block edges of weight `1/70000`; `bottleneck7_tri` is three nonoverlapping dense blocks of sizes 3, 2, and 2 with only weak inter-block edges of weight `1/70000`. The theorem `discharged_archetypes_admissible_window_actual_gaps` threads those seven actual-gap facts into the same interval. The natural-class companion defines weighted regularity and proves `uniK5`, `uniK7`, and `uniK9` are weighted-regular; the stronger universal-pass theorem is reduced to the explicit lower-bound hypothesis `WeightedRegularDefaultProductLowerBound`, not claimed. Ten further archetypes across `n=5`, `n=7`, and `n=9` carry named certificate-discharge-pending obligations rather than completed actual-gap discharges.[^lean-gx-06s63-1] This is finite-family cross-scale evidence plus a named conditional natural-class frontier, not a universal threshold theorem.

Disclosure on `bottleneck7`: an earlier revision used hand-typed `bottleneck7_bi` and `bottleneck7_tri` definitions whose spectral-gap certificates were not actual upper bounds on the graphs' `λ₂`. The current revision redefines those archetypes as the no-overlap weak-cluster bottlenecks just described, and Lean proves the corresponding upper bounds in `bottleneck7_bi_spectralGap_le_certificate` and `bottleneck7_tri_spectralGap_le_certificate`. This is an internal correction to the artifact family: the present paper's claims are about the redefined weak-cluster graphs, and the earlier definitions are not in scope for the claims above.

#### 6.6.4 Two invariants, two classifications, and their divergence

The important `n=7` finding goes past the fact that the exact `n=5` point does not lift: the two invariants already classify different graph families.

The RG-side classifier is the depth-3 basin

$$
\mathrm{Depth3RobustBasin7At} := \left\{\,G \mid 30/11 \le (\mathrm{rgTrajectory}\; G\; \mathrm{sig7}\; \delta\; 3).1\,\right\}.
$$

It includes the hierarchy archetypes: `hubSpokeHierarchy7` and `nestedHierarchy7` both lie inside the basin, together with `nearPath7`, `uniK7`, and `asymK7`. By contrast, the default `SpectralWellConnectedAt` threshold excludes those same hierarchy graphs: their current probe values are `S_δ(hubSpokeHierarchy7) ≈ 0.458` and `S_δ(nestedHierarchy7) ≈ 0.101`, both well below `17/20`.

This divergence is structurally intelligible. The RG basin measures *coarsening speed*: does the graph flow quickly toward a robust coarse state by depth `3`? The spectral-hybrid predicate measures something else: whether the graph is simultaneously well-mixed and low-vulnerability. Hierarchies can coarsen fast because their coarse structure is simple, while still having weak bridge edges or chokepoints that depress `λ₂` and leave them spectrally fragile. At `n=5`, the current archetype family does not expose this distinction, and the two invariants agree. At `n=7`, they separate. That separation is a feature, not a defect: the paper maps the geometry of "well-connected" governance graphs rather than forcing all structural intuitions into one scalar.

The `n=9` probe reinforces that reading. There the spectral-hybrid predicate remains a candidate separator on the sampled family, while the raw depth-3 `n=7` threshold does not transport as a stable cross-size classifier. In particular, the spectral product still crushes the bottleneck witness because `λ₂` remembers the weak global bridge even when a depth-limited RG scalar can rebound. The right conclusion is that the two invariants answer different scaling questions, not that one invariant replaces the other.

#### 6.6.5 Choice-sensitivity map under the review-required lattice

The per-harness rejection theorems of §6.3 are computed under the production diagnostic with `decisionRank deny=0, escalate=1, permit=2`. A defensible alternate axiomatization treats terminal `escalate` as a legitimate review-required outcome and ranks it equivalent to `permit` for monotonicity. We formalize that alternate ranking in Lean as `decisionRankReviewRequired : AuditDecision → Nat` with `deny=0, escalate=1, permit=1`, paired with the executable check `auditCheckMonotonicityCoreReviewRequired`, the Prop-level predicate `GraphMonotonicityReviewRequired`, the parallel nonvacuity predicate `GraphNonvacuityReviewRequired`, and the alternate verdict `governanceAdmissibilityVerdictReviewRequired`. The revised family is *not* promoted to the canonical nine-element axiom inventory; it is a parallel axiomatization used to map which leaderboard rejections are structural and which are artifacts of the permit-vs-escalate ordering.

Re-running the diagnostic on every committed leaderboard graph under this alternate ranking produces a mixed verdict that we report verbatim. The verdict matrix is:

| Extracted graph model | Canonical Lean witness | Review-required Lean witness | Reading |
|---|---|---|---|
| AutoGen | `governanceAdmissibilityVerdict autoGenExtractedGraph = legitimate` | `autoGenGovernanceAdmissibilityReviewRequiredLegitimate`: legitimate | unchanged pass |
| Codex | `codexHooksGovernanceAdmissibilityRejectsMonotonicity`: rejected monotonicity | `codexHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`: rejected monotonicity | rejection survives: the witness is not a `permit→escalate` rank collapse |
| Claude Agent SDK | `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity`: rejected monotonicity | `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`: rejected monotonicity | rejection survives: deny outcomes are literal `exactMatch` rather than the extracted Codex threshold-gate path |
| CrewAI | `crewAIHooksGovernanceAdmissibilityRejectsMonotonicity`: rejected monotonicity | `crewAIHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`: rejected monotonicity | rejection survives: the witness is a deny-lowering flip (`permit` or `escalate` collapsing to `deny`) under the review-required lattice |
| OpenClaw | `openClawInfraNonvacuityCheckFails`: rejected nonvacuity | `openClawInfraNonvacuityCheckFailsReviewRequired`: rejected nonvacuity | rejection survives: the witness is all-deny, outside the terminal-escalation question |

This is the headline of §6.6.5: the extracted Codex, Claude Agent SDK, and CrewAI graph-model monotonicity rejections survive treating terminal `escalate` as `permit` for review-required monotonicity (`codexHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`; `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`; `crewAIHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`). The extracted Codex/Claude Agent SDK pair is named directly by the Lean composition theorem for joint rejection: both remain rejected by monotonicity under the review-required lattice.[^03-anchor-9] The result is narrower than a legitimacy-flip story. It localizes a structural contrast inside the rejected class: the extracted Codex hook graph carries the named registration-node `thresholdGate "hook_registration" 1 .escalate` path, while the Claude Agent SDK model's corresponding deny outcomes are literal `exactMatch`.

The extracted OpenClaw graph row deserves explicit pairing. Its rejection witness is nonvacuity (`openClawInfraNonvacuityCheckFailsReviewRequired`) rather than monotonicity, so it is unaffected by the monotonicity-side rank revision; we add `GraphNonvacuityReviewRequired` and `auditGraphNonvacuityReviewRequired` to keep the lattice change coherent across the two predicates that interact with terminal `escalate`. Under that paired revision, terminal `escalate` is allowed to count as a non-vacuous review-required outcome; the OpenClaw witness still fails because the current extracted graph routes every claim to terminal `deny`, not to terminal `escalate`. So the rejection survives by being outside the terminal-escalation semantic dispute.

Four honest-scope notes attach to this map. (i) The choice-sensitivity result is mechanism-level, not theorem-level: it does not say which lattice is *right*; it reports what the diagnostic produces under each. The canonical lattice remains the production diagnostic; the review-required lattice is exposed as a paired analysis target. (ii) The result does not close the broader scalar-rank-as-axiom attack. Treating `decisionRank` itself as a value judgment to be argued over (rather than a 3-tier or 4-tier choice) survives this work as an Axis 1 (Allocation/Diagnostic) research question, because the attack concerns the diagnostic rank assigned on an already-extracted graph. (iii) The result does not close the faithfulness-too-narrow attack: a different-but-equally-faithful extractor that omits or renames the `hook_registration` field would alter the rejection on a different axis from the rank choice. That faithfulness/extraction attack remains in Axis 4 (Extraction) in the §6.6.8 follow-on program. (iv) The result inherits the synthetic-witness-arbitrary scope disclosure from §6.3: the four per-harness rejections are computed against constructed structural-probe fixtures, not real-world adversarial transcripts, and this scope clause carries forward to the per-harness verdict matrix above; the corpus-shape question is a companion frontier item rather than an Axis 4 sub-attack.

The Lean surface for the review-required lattice is exposed via dedicated predicates and verdict functions; see the identifier inventory in the footnote.[^lean-review-required-lattice]

[^lean-review-required-lattice]: Lean identifiers: `GraphMonotonicityReviewRequired`, `GraphNonvacuityReviewRequired`, `auditGraphNonvacuityReviewRequired`, `governanceAdmissibilityVerdict`, and `governanceAdmissibilityVerdictReviewRequired`; per-harness witnesses `codexHooksGovernanceAdmissibilityRejectsMonotonicity`, `codexHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`, `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity`, `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`, `crewAIHooksGovernanceAdmissibilityRejectsMonotonicity`, `crewAIHooksGovernanceAdmissibilityRejectsMonotonicityReviewRequired`, `openClawInfraNonvacuityCheckFails`, and `openClawInfraNonvacuityCheckFailsReviewRequired`; paired theorem `codex_claude_sdk_review_required_joint_rejection`; concrete Codex gate theorem `codexHooks_preToolUseRegistration_hookRegistrationEscalateThresholdGate`. Modules: `Legitimacy.Results.GovernanceAdmissibilityAudit.Checks`, `Legitimacy.Results.GovernanceAdmissibilityAudit.Evaluation`, `Legitimacy.Results.GovernanceAdmissibilityAudit.Cycles`, `Legitimacy.Results.CodexAdmissibilityAudit`, `Legitimacy.Results.ClaudeAgentSDKAdmissibilityAudit`, `Legitimacy.Results.CrewAIAdmissibilityAudit`, and `Legitimacy.Results.OpenClawAdmissibilityAudit`.

#### 6.6.6 SpectralWellConnectedAt as cross-scale companion

The paper-facing candidate cross-scale predicate is therefore not a normalized-Laplacian placeholder but the parameterized hybrid quantity already probed on the current families:

$$
\mathrm{SpectralWellConnectedAt}(G, s, \theta) :=
\mathrm{SpectralConnected}(G,s)\ \wedge\ \theta \le \lambda_2(G)\,\mathrm{cv}(G, s).
$$

Its appeal is pragmatic. `SpectralConnected(G,s)` supplies the positive spectral-gap conjunct; the product inequality supplies the `PositiveGovernanceVulnerabilityAt` conjunct. `cv(G, s)` captures vulnerability under claimant removal; `λ₂(G)` captures global connectivity. Their product grows large only when the graph is both structurally well knit and not overly brittle. On the current certified probe tables, every threshold in `[17/20, 46/53]` keeps the intended positives (`uniK`, `asymK`, `nearPath`, `wheel`) and excludes the intended bottleneck negatives across `n=5`, `n=7`, and `n=9`; for `uniK5`, `uniK7`, `uniK9`, `bottleneck5`, `bottleneck7_bi`, `bottleneck7_tri`, and `bottleneck9_bi`, those classifications are now actual-gap statements rather than only certificate statements. The default `17/20` point also excludes the hierarchy negatives in the larger probe pool.

The current theorem is finite-family rather than universal: the `n=5`, `n=7`, and `n=9` certified families admit the finite cross-scale window above, with actual-gap discharge currently complete for `uniK5`, `uniK7`, `uniK9`, `bottleneck5`, `bottleneck7_bi`, `bottleneck7_tri`, and `bottleneck9_bi`; the complete `uniK_n` archetypes are weighted-regular, and the weighted-regular universal-pass theorem remains conditional on `WeightedRegularDefaultProductLowerBound`. Lean now also proves the complement `weighted_regular_insufficient_for_default_product_lower_bound`: a tiny weighted-regular uniform triangle with positive CV has spectral-CV product below `17/20`, so weighted regularity alone cannot discharge the conditional hypothesis. Compared to the abandoned hope of a size-universal depth-3 RG equality, `SpectralWellConnectedAt` is already a useful companion: it is a candidate finite-family separator where the raw RG threshold is not, while leaving room for RG basins to describe coarsening dynamics that the spectral product intentionally ignores.

**A narrower cross-scale ordinal property.** The shipped `probes/scripts/adversarial_mi_probe.py` reconstruction finds that the normalized-Laplacian gap `λ₂(L̃) = λ₂(D^{-1/2} L D^{-1/2})` is a strictly stronger *ordinal* predictor of governance-coupled adversarial mutual information than `S_δ` (Spearman rank correlations of `-0.889` and `-0.672` respectively, on our 33-archetype pool across `n ∈ {5, 7, 9, 11, 13}`). However, `λ₂(L̃)` does NOT admit a clean cross-scale classification threshold: `hubSpokeHierarchy_n` graphs (paper-intended as not-well-connected) have `λ₂(L̃)` values strictly larger than `nearPath_n` graphs (intended well-connected) at every `n ≥ 7`, breaking any monotone-threshold basin classifier. Thus `λ₂(L̃)` captures something real about the adversarial inference dual but is a separate invariant from the finite-family basin classifier `S_δ ≥ 17/20`, which matches the intended labels on the current 33-archetype probe pool. The two invariants measure different structures: `S_δ` the basin membership, `λ₂(L̃)` the ordinal adversarial-inference difficulty.

#### 6.6.7 Boundary cross-reference

The scope boundary for structural governance properties, extractor evidence, channel analogies, and deployment inheritance is stated once in §1.2. The following research axes build from that boundary rather than restating it.

#### 6.6.8 Follow-on research axes

This paper is one axis of an ongoing structural-impossibility program for agentic AI. The impossibility-theorem skeleton — formal graph-diagnostic properties, impossibility result, spectral scaling, machine-checked Lean artifact — instantiates naturally along four distinct structural dimensions, of which the present paper covers the first:

**Axis 1: Allocation (this paper).** The allocation axis is the mature instance: it combines the structural scarce peer-relative allocator obstruction, the broad decision-system strategyproofness bridge, the concrete `GovernanceGraph` instance, the DAG transfer contract, the spectral scaling picture (C*, RG basins, λ₂(L̃)), and the bounded-corrigibility negative result of §6.4.[^lean-axis-allocation]

**Axis 2: Reflection (§reflective).** The shipped reflective substrate is modal-axiomatic, not an arithmetic-realisation theorem. The godel-loeb dependency supplies K4 and a derived Löb theorem over the modal substrate, with the Kreisel fixed-point postulate kept explicit; Solovay-style arithmetic realisation over Peano arithmetic is therefore out of scope. What is in scope is the `ReflectiveGovernanceFixedPointSystem` program: action, audit, and self-model converge at a fixed point, and the modal audit certificate is discharged through the reflective-box substrate rather than assumed as a governance field.[^lean-axis-reflection-substrate]

Within that fixed-point substrate scope, Löb's theorem is load-bearing for governance audits. Knaster-Tarski supplies fixed-state agreement, but the audit-certifies-its-own-soundness step asks the modal system to turn boxed internal soundness into the boxed audit atom. The Lean proof routes that step through the Löb bridge, and a build-gated witness rejects the direct Knaster-Tarski path before accepting the Löb-discharged certificate.[^lean-axis-reflection-loeb] The separate production self-audit verdict is narrower: it is discharged by the `native_decide` Prop certificate, while its Löb/modal box is a faithful Gödel-respecting re-presentation under the postulated internal-soundness boundary, not the source of the verdict guarantee. The reflective layer does not earn the verdict; it reflects the already-evaluated certificate in a subject-relative modal box. To our knowledge, this is the first formal substrate for the governance-audit version of the Löbian-obstacle intuition that has been invoked around MIRI tiling agents, Hubinger-style predictive-model risk, and verifier-target or non-agentic-guardrail safety programs [YudkowskyHerreshoff2013, Hubinger2023, Dalrymple2024, Bengio2025]. The claim is deliberately narrow: it is a modal-axiomatic governance-audit substrate, not a solution to tiling agents, simulator alignment, or guaranteed-safe-AI verification.

The depth-2 worked example separates lattice non-triviality from modal content. The least fixed point is the core state rather than the universal state, but the modal certificate still passes through the godel-loeb bridge and then transfers into the agent self-model.[^lean-axis-depth2] Thus the depth-2 example shows that non-trivial lattice structure can coexist with the reflective certificate, but it does not pretend the lattice depth itself derives the modal audit certificate.

The critical-capability composition gives the narrower positive claim: a reflective governance fixed-point system can select its modal audit target from the exact critical-capability threshold. This is a threshold-selected modal target under an internal-soundness premise, not a derivation of the capability threshold from Löb, and not a concrete construction of `hinternal`.[^lean-axis-critical-reflection] The remaining cliff is explicit: `hinternal` is still an abstract modal-substrate premise, and discharging it at concrete instances remains future work. Reflective-Löb is therefore not a structurally trivial extension of any single spectral axis; it composes with critical capability through both substrate sides.

The arithmetic-realization obstruction analysis sharpens that boundary without closing it. The first-order realization structure is named and typed, but its impossibility theorem consumes only the bridge back into the current unboxed modal proof predicate; genuine arithmetic-semantic discharge remains open.[^lean-axis-arithmetic-obstruction] What is formalized is the obstruction surface across three routes: unboxed necessitation, the empty-frame boxed route, and the `PropTautSound` Kripke route. The remaining open target is the boxed negative `¬ reflectiveBox (depth2LatticeAuditSoundFormulaAt depth2Core)`; closing it requires either Kripke completeness for the current modal predicate or a stronger arithmetic interface.

The three-path status of this chasm is now sharper. Path gamma, the generator-to-box route, reaches only a conditional projection; the mechanical K projection works, but the definitional iff is not the content-bearing cliff locator.[^lean-axis-three-path] The cliff is the missing boxed internal-soundness certificate. Path alpha, the GL-completeness route, is structurally refuted on the Track K countermodel: the frame is finite, transitive, and irreflexive, and the exact boxed internal-soundness target fails there. The missing certificate is `□(□A -> A)`, not the consequent of Löb's GL axiom `□(□A -> A) -> □A`; on this finite GL frame, completeness points away from provability rather than toward it.

This leaves Path beta as the only currently viable discharge route: a Solovay-style arithmetic realization with a stronger arithmetic interface, developed under a separate arithmetic-realization substrate track. The caveat is the same substrate caveat stated above: the present godel-loeb import is not pure GL because `ModalFormula.kreiselFixed` is primitive, but the boxed depth-2 discharge target under `encodeAuditCertifiesLattice` is in the pure modal fragment. The obstruction is therefore not a claim that the whole substrate has pure-GL completeness; it is a narrower claim about the formula Path alpha would need to prove.

[^lean-axis-allocation]: Lean identifiers: `nontrivial_symmetric_scarce_peer_relative_binary_allocators_obstructed`, `DecisionPipeline`, `decisionSystem_solidarity_monotonicity_imply_strategyproof`, `GovernanceGraph`, `structural_scarce_peer_relative_allocator_implies_aggregator`, `DAGToPipelineModelMap`, and `RG_basin_stratification_corrigibility_biconditional_fails`.

[^lean-axis-reflection-substrate]: Lean identifiers: `ModalFormula`, `ModalFormula.kreiselFixed`, `loeb`, `ReflectiveGovernanceFixedPointSystem`, `ReflectiveBoxSubstrate`, and `modalAxiomaticReflectiveBox`. Modules: `GodelLoeb.ModalFormula`, `GodelLoeb.Loeb`, and `Legitimacy.Reflective.FixedPointSystem`.

[^lean-axis-reflection-loeb]: Lean identifiers: `stable_audit_loeb`, `loeb`, `progressSystem_stable_audit_implies_box`, and `loeb_required_witness` in `Legitimacy.Reflective.FixedPointSystem`.

[^lean-axis-depth2]: Lean identifiers: `depth2ReflectiveSystem_stable_eq_core`, `depth2ReflectiveSystem`, `depth2Core`, `depth2ReflectiveSystem_stable_ne_univ`, `Set.univ`, `depth2ReflectiveSystem_stable_audit_implies_box`, `stable_audit_loeb`, `depth2ReflectiveSystem_stable_box_implies_audit`, `stable_audit_sound`, `depth2ReflectiveSystem_knaster_tarski_path`, and `depth2ReflectiveSystem_selfModel_certified_from_loeb`. Modules: `Legitimacy.Reflective.Depth2` and `Legitimacy.Reflective.Examples`.

[^lean-axis-critical-reflection]: Lean identifiers: `criticalCapabilityReflectiveSystem`, `criticalCapabilityThresholdAuditFormula`, `criticalCapabilityThresholdAudit_implies_box_at`, `criticalCapabilityReflectiveSystem_stable_audit_unfolds_to_subcritical_under_hinternal`, `criticalCapability_audit_distinguishes_subcritical_fixed_states`, `depth2Core`, `depth2UpperFixedState`, `depth2_audit_modal_content_differs`, `criticalCapabilityReflectiveSystem_without_hinternal_content_gate`, and `criticalCapabilityReflectiveSystem_unconditional_formula_content_gate`. Modules: `Legitimacy.Reflective.CriticalCapabilityComposition` and `Legitimacy.Reflective.Depth2`.

[^lean-axis-arithmetic-obstruction]: Lean identifiers: `Depth2ArithmeticSoundnessRealization`, `FirstOrder.Language`, `no_depth2Core_arithmeticSoundnessRealization`, `Provable.sound_empty`, `emptyEval_box`, `ModalFormula.emptyEval`, `PropTautSound`, `propTautSound_forces_every_box`, `propTautSound_forces_depth2Core_lattice_hinternal`, and `depth2LatticeAuditSoundFormulaAt`. Modules: `Legitimacy.Reflective.ArithmeticRealizationObstructions`, `Legitimacy.Reflective.BoxedSoundnessRealization`, and `GodelLoeb.Provable`.

[^lean-axis-three-path]: Lean identifiers: `depth2GeneratorZero_boxed_atom_of_auditCertifies`, `depth2GeneratorZero_auditCertifies_iff_core_lattice_box`, `depth2BoxedSoundnessFrame_transitive`, `depth2BoxedSoundnessFrame_irreflexive`, and `depth2Core_lattice_hinternal_countermodel`. Modules: `Legitimacy.Reflective.GeneratorBoxConstruction` and `Legitimacy.Reflective.BoxedSoundnessRealization`.

**Axis 3: Capacity.** Adversarial-capacity saturation: how many adversarial claimants can a governance graph service at a fixed tolerance before the spectral bounds of §5 are structurally forced to break? The companion-paper capacity theorem (paper 04 §4) already supplies the one-sided bound; the symmetric question, *saturation impossibility* under adversarial capability scaling, is the natural companion.

**Axis 4: Extraction.** Byte-stable transformation-limit: the extractor-side of the theory. The current paper ties the Lean tree to a byte-stable Rust extractor via the fidelity invariant (§6.5). The structural question is whether *any* source-to-governance-graph extraction can satisfy a natural set of extraction-transformation criteria simultaneously. If not, and a preliminary informal analysis suggests a natural impossibility, then the fidelity invariant itself is structurally constrained.

We describe these axes as an ongoing research program rather than a pre-announcement of four specific papers. The allocation axis is the mature instance; the other three are in different states of development, and their precise theorem-object-artifact form is still being worked out. The point of naming them here is to (i) situate this paper as one structural axis of a larger program rather than as a one-off, (ii) clarify which of the paper's graph-diagnostic-property / impossibility / spectral-scaling / Lean-artifact skeleton transports across axes and which parts do not, and (iii) acknowledge that readers interested in a specific axis, reflection-grade self-certification boundaries, adversarial-capacity saturation, or extraction transformation-limits, should expect separate follow-ups rather than extensions of this paper.

The follow-on program does not modify the contributions or claims of this paper. The allocation-axis impossibility, spectral scaling, and formal negative result stand independently. Readers familiar with Brcic-Yampolskiy's impossibility survey [BrcicYampolskiy2024] or Dalrymple et al.'s guaranteed-safe-AI program [Dalrymple2024] will recognize this axis as a natural member of the broader structural-limits lineage; the follow-on axes extend that membership rather than re-ground it.

---

### 6.7 Related work

**Apportionment theory, mechanism design, and formal social choice**. Balinski and Young [Balinski1982] proved no apportionment method simultaneously satisfies quota, population monotonicity, and house monotonicity. Young [Young1994] extends this into the apportionment-equity lineage in which allocation methods are understood by which requirement they sacrifice. Sen's Liberal Paradox [Sen1970] is a canonical Arrow-lineage neighbor: it shows how individually plausible rights and collective efficiency can jointly obstruct social choice, while this paper places the same axiomatic-obstruction pattern in a directed-governance-graph substrate. Thomson's allocation-rule program supplies the closest vocabulary for our three graph-diagnostic properties: our consistency corresponds to Thomson's bilateral consistency and reduced-problem consistency tradition [Thomson2003, Thomson2019]; our graph solidarity is a homogeneity / scale-invariance condition in the vicinity of Young's apportionment homogeneity axiom and Thomson's resource-allocation solidarity reading [Young1994, Thomson2015, Thomson2019]; and our monotonicity corresponds to Maskin-monotonicity in the allocation-mechanism setting [Maskin1999]. Moulin's *Axioms of Cooperative Decision Making* [Moulin1991] is the standard background reference for the same axiomatic-allocation tradition our graph-diagnostic properties draw on. Maskin and Sjöström's implementation-theory survey [MaskinSjostrom2002] is the canonical mechanism-design reference for the monotonicity and incentive-compatibility setting behind that comparison. Classical mechanism-design impossibilities such as Myerson-Satterthwaite [MyersonSatterthwaite1983] are background for the paper's "which desideratum must be sacrificed?" framing, not a theorem template used in the proof. Classical strategyproofness and manipulation results [Gibbard1973, Satterthwaite1975] are likewise motivation, but the theorem proved here is narrower: on directed governance graphs, the graph-diagnostic pair Solidarity ∧ Monotonicity implies the paper's binary permit/deny strategyproofness predicate. That in-semantics implication is the novel directed-governance-graph contribution. Our impossibility has the same skeleton as the classical lineage but is currently formalized for the structural scarce peer-relative allocator pipeline class rather than voting rules, divisor methods, or bankruptcy rules; for the broader computational social-choice context see the Handbook of Computational Social Choice [Brandt2016]. Prior formalizations of Arrow-lineage results already exist, notably Wiedijk's Mizar formalization [Wiedijk2007], Nipkow's Isabelle/HOL development [Nipkow2009], and first-order logic formalizations by Grandi and Endriss [GrandiEndriss2013]. Andrew Souther and Benjamin Davidson's `lean-social-choice` (`github.com/asouther4/lean-social-choice`) is a public Lean formalization of Arrow's theorem and related social-choice results for classical preference-aggregation rules; it has no associated publication, DOI, or arXiv record, and it does not target governance graphs, the binary-pipeline substrate, or extractor coupling. It is the closest Lean prior art for the impossibility skeleton; the contribution here is the governance-graph object and the executable extractor coupling, not the act of formalizing an Arrow-lineage result in Lean. The defensible novelty claim here is narrower than "first impossibility in AI governance": a structural impossibility theorem for a precise governance-pipeline class, formalized in Lean 4 against the Mathlib ecosystem and tied directly to a byte-stable extractor.

**Adjacent AI impossibility results and safety programs**. Impossibility theorems in AI governance now form a small but growing lineage rather than a single first claim. Eckersley's value-alignment paper [Eckersley2019] imports Arrow-style social-choice impossibility directly into AI objective design. Ge, Halpern, Procaccia, and coauthors [Ge2024] bring social-choice axioms to reward learning from human feedback; Conitzer, Freedman, Heitzig, Russell, and coauthors [Conitzer2024] argue more broadly that social choice should guide AI alignment with diverse feedback. Procaccia, Schiffer, and Zhang [Procaccia2025] give a complementary ICML social-choice-for-alignment result: clone robustness is an RLHF-side agenda item, while this paper supplies the structural-impossibility entry above the preference-learning layer. No stable joint Conitzer-Procaccia 2024/2025 bibliographic item is available; the text therefore cites the verifiable PMLR records rather than a composite reference. The object is different: they study aggregation of human feedback or alignment inputs, while this paper studies the governance rule above the preference-learning layer. No stable public bibliographic record was located for the possible Oswald (2026) allocation-under-uncertainty antecedent, so the paper cites no such reference. Nayebi's agreement-based complexity analysis [Nayebi2025] proves communication-style lower bounds for broad human-AI alignment; Sahoo et al.'s RLHF trilemma paper [RLHFTrilemma2025] formalizes a different impossibility inside preference-learning pipelines; and Tibebu's *The Accountability Horizon* [Tibebu2026] studies accountability allocation over human-agent collectives in a structural-causal setting. This paper contributes a formally verified Arrow-lineage impossibility for the structural scarce peer-relative allocator governance-pipeline class, with Lean 4 / Mathlib formalization, byte-stable Rust extraction, and spectral structural machinery (critical capability, RG flow, and the spectral-hybrid predicate) that these antecedents do not supply. It therefore cedes any claim to being the first impossibility theorem in AI governance while maintaining a narrower priority claim on this theorem-object-artifact package. Dalrymple et al.'s guaranteed-safe-AI program [Dalrymple2024] is a broader verifier-centered agenda into which this paper fits as a concrete governance-verifier instance. Brcic and Yampolskiy's survey [BrcicYampolskiy2024] catalogs impossibility theorems across AI more generally; this paper contributes a machine-checked governance-graph entry to that lineage.

**AI governance, reward hacking, and accountability frameworks**. Anthropic's Constitutional AI [Bai2022] and the AARs incident report [AARs2026] are behavior-side governance references rather than structure-side ones. Skalse et al. [Skalse2022] provide the formal reward-hacking definition that best matches our discussion of proxy sacrifice and composition failure. Agent control and policy-compilation frameworks such as ACP [Fernandez2026], PCAS [Palumbo2026], and Type-Checked Compliance / Lean-Agent Protocol [TypeCheckedCompliance2026] are adjacent enforcement layers: they constrain action traces, information flow, or action admission proofs, but they do not ask Arrow-lineage questions about the coherence of the governing rule itself. That is also the distinction between this paper and industry enforcement planes such as Databricks Unity AI Gateway [Databricks2026]. Runtime enforcement of a structurally incoherent rule is still enforcement of the wrong rule.

**Fairness impossibility and bounded-rationality substrates**. The machine-learning fairness literature already normalized the idea that impossibility theorems can be practically useful rather than nihilistic. Chouldechova [Chouldechova2017] and Kleinberg, Mullainathan, and Raghavan [Kleinberg2017] show that natural statistical fairness criteria cannot generally be jointly satisfied. Our result plays the same role for governance-graph legitimacy: the theorem identifies which sacrifices must be declared instead of pretending they can be engineered away. At the level of modeling substrate rather than impossibility, Ortega and Braun's free-energy / information-processing account of bounded rationality [OrtegaBraun2013] is conceptually adjacent to our use of explicit structural limits under capability scaling, though our proofs live in governance graphs rather than utility-information tradeoff models.

**Commons governance**. Ostrom [Ostrom2009] derives eight design principles for long-enduring commons institutions from empirical study. Our formal analysis provides theoretical grounding for why several Ostrom principles are structurally necessary: clearly defined boundaries correspond to GovernanceGraph node definitions; proportional equivalence to the graph-diagnostic solidarity axiom; collective-choice arrangements to strategyproofness; graduated sanctions to the three-valued decision model (Permit/Escalate/Deny); nested enterprises to governance graph composition. The correspondence is approximate; human commons operate over much longer timescales and with different adaptation dynamics than agentic AI, but the structural parallel is striking. Our impossibility theorem suggests AI governance is structurally harder than human commons governance because agent adaptation speed collapses the institutional evolution timescale that human commons rely on.

**Formal verification of AI systems**. Lean 4 [Moura2021] and Mathlib [Mathlib2023] provide the proof infrastructure. Our Lean formalization proves theorem statements about graph-diagnostic properties and composition operations; it does not verify behavioral properties of specific AI systems. DGM-Hyperagent [DGM-H2026] demonstrates metacognitive self-modification without formal governance analysis of the resulting rules. Our framework focuses on collective governance properties rather than individual agent behavior.

**RG, finite-size scaling, and spectral graph theory**. RG coarse-graining of graphs has a substantial recent literature. The modern network-RG lineage begins with Song, Havlin, and Makse [Song2005], continues through geometric renormalization [García-Pérez2018], Laplacian-diffusive renormalization [Villegas2023], and higher-order complexes [Nurisso2025], and is complemented by spectral coarsening with guarantees [DorflerBullo2013, Gfeller2007, Loukas2019]. The earlier majority-rule renormalization-group line, Galam's hierarchical-majority and totalitarian-paradox sequence [Galam1986, Galam1990, Galam2000], is the closest aggregation-rule antecedent for our use of RG flow on a governance-graph substrate; the analogy is structural (RG coarse-graining over a majority-rule substrate) rather than a theorem template. What this literature does *not* support is the naive expectation that a small-n exact coarse state should recur unchanged across sizes. Finite-size scaling theory [Cardy1988], Baldwin's n-od basin-order result [Baldwin1991], and Chen et al.'s finite-size scaling analysis of geometric network RG [Chen2021] all point the other way: small systems carry size-indexed corrections. That is why this paper now frames the n=5 equality as scale-local by design. The cross-scale companion we actually use is the spectral-hybrid product λ₂ × cv, not a universal RG equality claim. The relevant spectral backdrop remains Cheeger-style connectivity and multiway bottleneck structure [Chung1997, LeeGharanTrevisan2012], but the paper's substantive claim is finite-family: the spectral-hybrid predicate has a certified threshold window for the current n=5, n=7, and n=9 families even where the raw depth-limited RG threshold does not separate hierarchy archetypes.

---

### 6.8 Conclusion

Legitimacy for peer-relative governance is best treated as a compiled, typed, auditable kernel rather than as a scalar verdict. The strengthened semantic target packages the five runtime obligations with graph-diagnostic axioms and the spectral bridge through a semantic contract; the canonical decomposition gives a two-conjunct iff, and the unfolded theorem expands it into runtime, diagnostic, and spectral layers. That expansion decomposes a strengthened contract; it does not derive the diagnostic or spectral layers from runtime kernels alone. The bounded extractor contract states the operational boundary: well-formed bounded source inputs must compile to artifacts satisfying that semantic kernel target.

The impossibility theorem is the forcing move inside this constructive account. Peer-relative allocation, the structural substrate of agentic AI governance, faces an inherent obstruction on the structural scarce peer-relative allocator pipeline class: the three Young-lineage diagnostics fail jointly for every `[DecisionPipeline P]` whenever a transparent prefix is followed by a nontrivial symmetric scarce peer-relative allocator surface whose tail preserves all permits from that surface, and the four-property bundle is a derived corollary through the broad `DecisionSystem` bridge. The `DAGToPipelineModelMap` theorem states the exact contract under which a governed DAG system transfers to a pipeline representative, and the single-peer-chokepoint family gives a worked structural case where the contract is proved rather than assumed. `GovernanceGraph` remains the canonical concrete instance. Strategyproofness is the bridge-derived fourth corollary for the paper-facing three-property statement, not an independent minimal assumption. The broader syntactic class "contains a peer-relative stage" is intentionally not claimed; a formal countermodel shows that an upstream deny-all gate can make the peer-relative stage unreachable. The non-peer-relative escape is real only in the limited sense proved here: graph-level diagnostics admit claimant-local escape, but, under the governance coverage contract, the sharpened pipeline theorem forces any governing no-peer-relative pipeline into substantive collapse, concurrent-claim infeasibility, or runtime-kernel exit.

Beyond the static impossibility, the companion paper proves operational scaling results for the same represented graph object: a capacity theorem bounding signal absorption by graph structure, a critical-capability boundary, Stackelberg stability results, and a renormalization-group flow whose honest current statement is scale-aware through two invariants. Those results are companion consequences, not proof inputs to the impossibility theorem. The join is itself machine-checked: on the constructed canonical claimant-interaction lift, definitionally `uniK5` with fixed signal `sig5`, a shared-substrate composition (`capability_scaling_shared_cliff`) derives positive consistency vulnerability, hence a finite critical-capability cliff, from the peer-relative obstruction. It is not a per-input-graph spectral law.

The practical consequence is a reframing: from "is this system aligned?" to "does this governance rule compile to a semantic legitimacy kernel, and what sacrifices does that kernel expose?" The legitimacy factor model, Declared Sacrifice Protocol, spectral bounds, constitutional stratification, and scope-qualified capability-pressure corrigibility theorem provide concrete tools. The impossibility theorem explains failure classes that appear across distinct evidence lanes: the extracted Codex graph's automatic-extraction monotonicity violation, the modeled OpenClaw layered-override issue, and the AARs interpretive reward-hacking case study. These evidence lanes are compatible with the modeled structural failure class; they should be read as extracted/modelled witnesses, not as theorem-level claims about live products or raw source semantics. The RG contribution should be read in the same spirit: not as proof that one rational point governs all scales, but as proof that coarse robustness can be formalized exactly where the finite lattice warrants equality and honestly relaxed to inequalities where it does not.

The impossibility theorem is what makes the compiler's diagnostic layers non-optional: they must be packaged explicitly rather than inferred from the runtime kernel. The companion paper supplies the scaling theory for the same represented graph object.

---

### 6.9 Code and data availability

**Artifact status**: the preprint artifact is this repository at the `v1.0.0` verification code anchor. At this commit, the artifact invariants are: zero Lean `sorry`, zero Lean `admit`, zero first-party Lean `axiom`, `cd lean && lake build Legitimacy` green, and the Rust gate `cargo test && cargo clippy --all-targets --all-features -- -D warnings && cargo fmt --check` is the required extractor verification path.

**Repository access**: the public repository is the artifact of record for the preprint release. Immutable archives are produced from the released tag.

**Companion paper**: `papers/02-semantic-legitimacy-kernels.md` (same repository, same verification code anchor).

**License**: dual-licensed under MIT OR Apache-2.0; see `LICENSE-MIT` and `LICENSE-APACHE`.

**Toolchain at the verification code anchor**:
- Lean 4 is pinned by `lean/lean-toolchain` (`leanprover/lean4:v4.29.1`) and the Lake configuration in `lean/lakefile.lean` and `lean/lake-manifest.json`, including Mathlib `v4.29.1`.
- Rust crate metadata is recorded in `Cargo.toml`, and dependency resolution is locked by `Cargo.lock`. The verification code anchor does not include `rust-toolchain.toml` or `rust-toolchain`; reviewers should use a stable Rust toolchain supporting edition 2024 unless a later artifact release adds an explicit Rust pin.

**Replication path**:
1. Clone the repository and check out the tagged release commit.
2. Run `cd lean && lake build Legitimacy` to verify the Lean theorem stack.
3. From the repository root, run `cargo test && cargo clippy --all-targets --all-features -- -D warnings && cargo fmt --check` to verify the routine Rust extractor tests, ordinary snapshot/parity tests, lint hygiene, and formatting gate.
4. Run `bash scripts/verify.sh --release-gate` to execute the full verification gate (routine checks plus the slow leaderboard transcript replay, the slow Codex extraction fixture, the README Lean-gate status check, and paper anchor verification) when the script is present in the checked-out artifact.

**Verification invariant — no `sorry`, `admit`, or first-party `axiom`**: the repository verification gate checks for zero `sorry`, `admit`, or first-party `axiom` declarations under the Lean proof tree. Decision procedures (`native_decide`) and the source-to-graph extractor remain disclosed components of the trusted base.

---

## 7. Design Principles

**Declared Sacrifice Protocol**. For governance rules in the reachable scarce peer-relative decisive-stage class, the joint legitimacy impossibility establishes that full graph-diagnostic compliance is unachievable. In that class, the three graph diagnostics cannot be jointly satisfied, and strategyproofness follows as a bridge-derived fourth corollary when solidarity and monotonicity are present. Outside that class, claimant-local non-peer-relative graphs can satisfy the diagnostics via `nonPeerRelative_escapes_impossibility`, with the separate collapse, infeasibility, or runtime-kernel-exit cost described in §3.5. The typical response, relax one graph-diagnostic property and proceed as if "good enough", treats legitimacy as aspirational rather than as the structural constraint it is. The Declared Sacrifice Protocol reframes the goal: a governance system declares which property it sacrifices, bounds the violation magnitude, and commits to a monitoring plan sufficient to detect violations at the declared severity. The Legitimacy compiler checks three things: (1) *classification*: the declared property is the one actually violated; (2) *bound verification*: empirical violation ≤ `impact_bound`; (3) *monitoring sufficiency*: the plan catches violations at the declared severity. Policies passing all three receive a `DeclaredSacrificesCertificate`. The certificate's primary output records which properties are sacrificed and at what magnitude. Any scalar alignment score derives from the certificate, not the other way around. `DeclaredSacrifice` and `DeclaredSacrificesCertificate` are Rust-side structs in `src/sacrifice.rs`, covered by Rust tests rather than Lean extraction-soundness theorems. The Rust-side strategyproofness monitor remains load-bearing because bridge-derived manipulability is still the operational failure class teams need to measure and bound.

**Decomposition-Resistant Governance**. Theorem 6.2.2's immunity result (`csm_no_permitting_decomposition`) translates to a concrete architecture: each governance node carries a running semantic hash of composed intent. Before processing action a_i, the node checks whether H(a₁ ∘ ... ∘ a_i) matches a denied pattern hash; if yes, the node denies even if a_i would individually permit. Lean proof that under CSM, no decomposition with individually-permitting steps exists.

At the extracted audit-kernel layer, the complementary structural fact is deny-bottom merging rather than a new canonical axiom: `Legitimacy.finalDecisionSuffixMergeTrace_preserves_deny` and `Legitimacy.noEntrySeedSuffixMergeExtension_preserves_terminal_deny` state that append-only suffixes cannot revive a terminal deny when they do not introduce fresh entry-node claim seeds and their traversal effect is a suffix merge. This closes the overclaim that compositional safety was only a projection label; the remaining boundary is explicit rather than hidden.

**Constitutional Stratification with Formal Priority Proofs**. A formal stratification proof is a `StratificationCertificate eval ovs` over a `LayerEval` and an override list: every listed override preserves all higher layers' safety properties. Any governance action represented as an override that modifies a higher-layer property (e.g., a `CLAUDE.md` clause weakening a model-level safety property) must come with a Lean proof of `AdmissibleOverride`. No proof → override inadmissible in that carrier. `strat_immune_to_inversion` guarantees the stratification shield for the certified override list; the paper does not claim a separate `GovernanceGraph`-to-`LayerEval` bridge theorem here.

**Scope-qualified Corrigibility**. The framing is conditional. If powerful agent systems are to govern without silent legitimacy degradation under composition, scaling, or self-modification pressure, they need some explicit layer that distinguishes merely executable control from legitimate authority. The corrigibility obligation here is the kernel-side instance of that layer: an invariant that survives recompilation and admits a quantitative external-adversary bridge. The runtime kernel's corrigibility invariant supplies the recompilation half; the observational-corrigibility bridge family (`Legitimacy.observational_corrigibility_bridge_quantitative` and the well-connected-basin discharge) supplies the external-adversary half. Both halves are scope-qualified rather than universal. Across compile-check-preserving recompilation cycles, the canonical governance kernel maintains override-capability under override-retention and sacrifice-monotonicity side conditions. Theorem `corrigibility_under_recompile` (Lean: `Protocol/Corrigibility.lean`) formalizes: for any recompile cycle satisfying the preserving-conditions,[^lean-gx-07-1] the kernel's corrigibility invariant is preserved in the compiled output. The trajectory-level companion `corrigibility_under_arbitrary_selfmod` (`Protocol/Corrigibility.lean`) proves preservation across all trajectories within the kernel's own action space. The runtime kernel no longer hides this under a vacuous `True` placeholder: `Legitimacy.KernelCorrigible` strengthens Axiom 3 by requiring both supervisory-algebra preservation and `Legitimacy.KernelAdversarialBounded`, a finite nonnegative ceiling on the kernel action-capability surface.

The external-adversary bridge is now unbundled. `Legitimacy.observational_corrigibility_bridge_quantitative` states the qualitative algebra-preservation and quantitative perturbation-budget contract for joint kernel/adversary trajectories, and that contract is discharged on the well-connected `n = 5` basin witnesses.[^lean-gx-07-2] Separately, `Legitimacy.Safety.statefulAdversary_via_consistencyWitnessedAggregator_exclusive_dichotomy` packages the live peer-relative case as an operational capability/outcome dichotomy: at or above the graph-derived `C*` budget, a monitored consistency-sacrifice certificate is emitted; below `C*`, bounded corrigibility is preserved. Both branches are non-vacuous: each is realized by a concrete witness, one a positive subcritical perturbation hitting bounded corrigibility and one a critical-capability violation forcing the consistency sacrifice.[^lean-gx-07-3]

| Capability regime | Formal outcome | Lean anchor |
|---|---|---|
| Kernel-internal action surface | finite nonnegative action-capability ceiling folded into runtime corrigibility | `Legitimacy.KernelCorrigible` / `Legitimacy.KernelAdversarialBounded` |
| External trajectory below `C*` | bounded corrigibility preserved | `Legitimacy.Safety.statefulAdversary_via_consistencyWitnessedAggregator_exclusive_dichotomy` |
| External trajectory at or above `C*` | monitored consistency-sacrifice certificate emitted | `Legitimacy.Safety.statefulAdversary_via_consistencyWitnessedAggregator_exclusive_dichotomy` |
| Attempted non-peer-relative escape | collapse, infeasibility, or runtime-kernel exit; not a route around the dichotomy | `Legitimacy.non_peer_relative_collapse_or_infeasible_or_exits_kernel` |

The scope remains honest. The RG-plus-stratification biconditional is false (`counterexample_good_rhs_bad_lhs`, §6.4), so the positive bridge is not characterized by basin membership plus a stratification certificate alone. And an adversary cannot evade the peer-relative dichotomy merely by switching to non-peer-relative governance: the graph-level escape exists only in the degenerate sense formalized by `Legitimacy.nonPeerRelative_escapes_impossibility`, while `Legitimacy.nonPeerRelative_allAxioms_escape_collapse` shows that recovering all graph diagnostics collapses the mechanism to threshold/constant behavior rather than substantive multi-claimant allocation, and `Legitimacy.non_peer_relative_collapse_or_infeasible_or_exits_kernel` lifts the cost to collapse, infeasibility, or runtime-kernel exit.

---

## Appendix A. Formal-anchor and identifier conventions

Backticked identifiers outside the following exemption categories are expected to resolve to a first-party Lean/Rust/test declaration. Fixture field names and probe label tokens — `block_reason`, `hook_registration`, `model_not_found`, `skillPrelude`, `bottleneck11_bi`, and `bottleneck13_bi` — denote literal governance-graph fixture data or probe-bottleneck identifiers drawn from `audits/fixtures/sources/`, `probes/scripts/normalized_laplacian_probe.py`, and `probes/scripts/archetypes.py`, not Lean/Rust declarations.

Probe-family placeholders — `uniK_n`, `asymK_n`, `nearPath_n`, `hubSpokeHierarchy_n`, and `_certificate_discharge_pending` — are schematic family labels with concrete instances declared where relevant, such as `asymK5_certificate_discharge_pending`. Module, import, and builtin/prose tokens — `DAGBinaryBridge`, `Equiv`, `True`, and `HEAD` — are backticked to mark code-level vocabulary in context, not to claim a first-party declaration under the paper-claim audit.

## Appendix B. Lean-side correspondence for headline claims

The abstract and §1 state the mathematical objects without Lean identifiers. The table collects the formal names and module paths used by the headline claims.

| Claim / object | Lean identifier | Module |
| --- | --- | --- |
| Semantic kernel target | `IsSemanticLegitimacyKernel` | `Legitimacy.Kernel.Class` |
| Kernel decomposition iff | `isSemanticLegitimacyKernel_iff_runtime_and_bridge` | `Legitimacy.Kernel.Class` |
| Runtime/diagnostic/spectral unfolded form | `semanticKernel_iff_runtime_diagnostic_spectral_layers_unfolded` | `Legitimacy.Results.SemanticBridge` |
| Runtime/diagnostic/spectral compatibility alias | `semanticKernel_iff_runtime_diagnostic_spectral_layers` | `Legitimacy.Results.SemanticBridge` |
| Broad decision interface | `DecisionSystem` | `Legitimacy.Foundations.DecisionSystem` |
| Theorem-bearing decision refinement | `DecisionPipeline` | `Legitimacy.Foundations.DecisionSystem` |
| Binary compatibility marker | `BinaryDecisionPipeline` | `Legitimacy.Foundations.DecisionSystem` |
| Diagnostic predicate | `GraphConsistencyP` | `Legitimacy.Diagnostics.DecisionSystem` |
| Diagnostic predicate | `GraphSolidarityP` | `Legitimacy.Diagnostics.DecisionSystem` |
| Diagnostic predicate | `GraphMonotonicityP` | `Legitimacy.Diagnostics.DecisionSystem` |
| Diagnostic predicate | `GraphStrategyproofnessP` | `Legitimacy.Diagnostics.DecisionSystem` |
| Diagnostic congruence theorem | `GraphMonotonicityP_congr` | `Legitimacy.Diagnostics.DecisionSystem` |
| Structural peer-relative allocator class | `StructuralScarcePeerRelativeAllocator` | `Legitimacy.Foundations.StructuralPeerRelative` |
| Nontrivial symmetric scarce peer-relative class | `NontrivialSymmetricScarcePeerRelativeBinaryAllocator` | `Legitimacy.Foundations.StructuralPeerRelative` |
| Competitive displacement witness | `scarce_symmetric_peer_allocator_has_competitive_displacement` | `Legitimacy.Foundations.StructuralPeerRelative` |
| Reduction-violation witness | `scarce_symmetric_peer_allocator_has_reduction_violation` | `Legitimacy.Foundations.StructuralPeerRelative` |
| Aggregator route theorem | `structural_scarce_peer_relative_allocator_implies_aggregator` | `Legitimacy.Foundations.StructuralPeerRelative` |
| Structural-class obstruction (sharpness tier) | `nontrivial_symmetric_scarce_peer_relative_binary_allocators_obstructed` | `Legitimacy.Foundations.StructuralPeerRelative` |
| Widened behavioral obstruction (breadth tier) | `symmetric_scarce_coupled_allocators_obstructed` | `Legitimacy.Impossibility.SymmetricScarceCoupledObstruction` |
| Represented structural node instance | `weakestWithStrongerPeerNode_structural` | `Legitimacy.Extract.RepresentableAuditSubject` |
| Represented structural obstruction | `representedPeer_obstructs_diagnostics` | `Legitimacy.Extract.RepresentableAuditSubject` |
| Median node structural boundary | `peerRelativeNode_not_structural` | `Legitimacy.Extract.RepresentableAuditSubject` |
| Reachable-stage class | `ReachablePeerRelativeDecisiveStage` | `Legitimacy.Impossibility.PeerRelativeReachable` |
| Reachable peer-relative obstruction (public headline) | `reachable_peer_relative_decisive_stage_obstructs_diagnostics` | `Legitimacy.Impossibility.PeerRelativeReachable` |
| Complete first-effective reachability bridge | `complete_first_effective_implies_reachable_peer_relative_decisive` | `Legitimacy.Impossibility.PeerRelativeReachable` |
| Transparent-prefix mask countermodel | `without_transparentPrefix_denying_prefix_masks_obstruction` | `Legitimacy.Impossibility.PeerRelativeReachable` |
| Non-denying-suffix mask countermodel | `without_nonDenyingSuffix_permit_revoking_suffix_masks_obstruction` | `Legitimacy.Impossibility.PeerRelativeReachable` |
| Older aggregator route | `DecisionPipeline.IsPeerRelativeAggregator` | `Legitimacy.Foundations.DecisionSystem` |
| Binary-pipeline obstruction | `binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction` | `Legitimacy.Impossibility.PeerRelativeClass.Obstructions` |
| Direct monotonicity route | `binaryDecisionPipeline_isPeerRelativeAggregator_complete_obstruction` | `Legitimacy.Impossibility.PeerRelativeClass.Obstructions` |
| Existential class obstruction | `binaryDecisionPipeline_existsClass_three_axiom_obstruction` | `Legitimacy.Impossibility.PeerRelativeClass.Obstructions` |
| Binary composition counterexample | `composition_inadmissibility` | `Legitimacy.Results.Composition` |
| Three-valued composition inadmissibility | `three_valued_composition_inadmissibility` | `Legitimacy.Results.Composition` |
| Parametric escalation-policy obstruction | `three_valued_escalationPolicyWitness_composition_inadmissibility` | `Legitimacy.Results.Composition` |
| Escalation-surface witness predicate | `EscalationPolicyWitness` | `Legitimacy.Results.Composition` |
| Concrete escalation-policy inhabitant | `thresholdNode3_escalationPolicyWitness` | `Legitimacy.Results.Composition` |
| Multi-principal Arrow obstruction | `majorityQuorumRule_fails_arrow_triple` | `Legitimacy.Results.MultiPrincipal` |
| Multi-principal frontier | `multi_principal_pairwise_achievability_with_majorityQuorum_obstruction` | `Legitimacy.Results.MultiPrincipal` |
| Broad strategyproofness bridge | `decisionSystem_solidarity_monotonicity_imply_strategyproof` | `Legitimacy.Impossibility.AxiomIndependence` |
| Concrete graph substrate | `GovernanceGraph` | `Legitimacy.Foundations.Graph` |
| Concrete refined class predicate | `IsPeerRelativeAggregator` | `Legitimacy.Impossibility.PeerRelativeClass.Predicates` |
| Median-rule gate instance | `peerRelativeNode_isPeerRelativeAggregator` | `Legitimacy.Impossibility.PeerRelativeClass.Witnesses` |
| Refined-to-broad peer-relative relation | `IsPeerRelativeAggregator.isPeerRelativeNode` | `Legitimacy.Impossibility.PeerRelativeClass.Predicates` |
| Median-rule effective surface | `EffectivePeerRelativeSurface` | `Legitimacy.Impossibility.PeerRelativeClass.Predicates` |
| Median-rule complete tail | `CompletePeerRelativeTail` | `Legitimacy.Impossibility.PeerRelativeClass.Predicates` |
| Complete first-effective class | `CompleteFirstEffectivePeerRelativeSurfaceClass` | `Legitimacy.Impossibility.PeerRelativeClass.Predicates` |
| Concrete median obstruction | `effectivePeerRelativeSurface_complete_three_axiom_obstruction` | `Legitimacy.Impossibility.PeerRelativeClass.Obstructions` |
| Concrete median obstruction via pipeline | `effectivePeerRelativeSurface_complete_three_axiom_obstruction_via_pipeline` | `Legitimacy.Impossibility.PeerRelativeClass.Obstructions` |
| Concrete existential class theorem | `effectivePeerRelativeSurface_existsClass_three_axiom_obstruction_via_pipeline` | `Legitimacy.Impossibility.PeerRelativeClass.Obstructions` |
| Broader-stage countermodel | `hasPeerRelativeStage_does_not_force_impossibility` | `Legitimacy.Impossibility.PeerRelativeClass.Countermodel` |
| DAG transfer theorem | `dagPeerRelativeSurfaceMap_pipeline_impossibility` | `Legitimacy.Kernel.DAGBinaryBridge` |
| DAG transfer contract | `DAGToPipelineModelMap` | `Legitimacy.Kernel.DAGBinaryBridge` |
| Concrete DAG compatibility form | `dagPeerRelativeSurfaceMap_impossibility_via_pipeline` | `Legitimacy.Kernel.DAGBinaryBridge` |
| Concrete DAG compatibility form | `dagPeerRelativeSurfaceMap_impossibility` | `Legitimacy.Kernel.DAGBinaryBridge` |
| Broad peer-relative node predicate | `IsPeerRelativeNode` | `Legitimacy.Impossibility.PeerRelativeClass.Predicates` |
| Canonical gate instance | `peerRelativeNode_isPeerRelative` | `Legitimacy.Impossibility.PeerRelativeClass.Witnesses` |
| Context-only peer-relative predicate | `PeerRelativeByContext` | `Legitimacy.Foundations.StructuralPeerRelative` |
| Consistency-independence witness | `shortListGraph` | `Legitimacy.Impossibility.AxiomIndependence` |
| Solidarity-independence witness | `bobAbsoluteGraph` | `Legitimacy.Impossibility.AxiomIndependence` |
| Monotonicity-independence witness | `bobRelativeGraph` | `Legitimacy.Impossibility.AxiomIndependence` |
| Non-peer-relative escape theorem | `nonPeerRelative_escapes_impossibility` | `Legitimacy.Results.NonPeerRelative` |
| Non-peer-relative threshold theorem | `nonPeerRelative_is_threshold` | `Legitimacy.Results.NonPeerRelative` |
| Non-peer-relative strategyproofness theorem | `nonPeerRelative_monotone_strategyproof_claimantConstant` | `Legitimacy.Results.NonPeerRelative` |
| Finite-estate obstruction | `nonPeerRelative_cannot_allocate_finite_estate` | `Legitimacy.Results.NonPeerRelative` |
| Escape-collapse theorem | `nonPeerRelative_allAxioms_escape_collapse` | `Legitimacy.Results.NonPeerRelative` |
| Pipeline/kernel escape theorem | `non_peer_relative_collapse_or_infeasible_or_exits_kernel` | `Legitimacy.Impossibility.PeerRelativeClass.Escape` |
| Collapse witness | `collapseWitnessPipeline_collapse` | `Legitimacy.Impossibility.PeerRelativeClass.Escape` |
| Infeasibility witness | `singletonOnlyPipeline_infeasible` | `Legitimacy.Impossibility.PeerRelativeClass.Escape` |
| Hidden-authority exit witness | `hiddenAuthorityExitPipeline_exits_kernel` | `Legitimacy.Impossibility.PeerRelativeClass.Escape` |
| Liveness failure witness (permanent escalation) | `permanently_escalating_permit_graph_fails_nonvacuity` | `Legitimacy.Impossibility.PeerRelativeClass.Escape` |
| Feasibility failure witness | `admit_only_singleton_rule_fails_feasibility_at_multi_claim_profiles` | `Legitimacy.Impossibility.PeerRelativeClass.Escape` |
| No non-peer-relative route theorem | `no_non_peer_relative_pipeline_substantive_feasible_and_kernel` | `Legitimacy.Impossibility.PeerRelativeClass.Escape` |
| Spectral construction lemma | `claimantInteractionGraph` | `Legitimacy.Spectral.CrossScale.ClaimantInteraction` |
| Constructed peer-relative carrier | `constructedPeerRelativeInteractionGraph` | `Legitimacy.Spectral.CrossScale.ClaimantInteraction` |
| Carrier equality lemma | `claimantInteractionGraph_eq_constructedPeerRelativeCarrier_of_completeSurface` | `Legitimacy.Spectral.CrossScale.ClaimantInteraction` |
| Canonical carrier equality | `peerRelativeNode_claimantInteractionGraph_eq_uniK5` | `Legitimacy.Spectral.CrossScale.ClaimantInteraction` |
| Canonical spectral-gap computation | `peerRelativeNode_claimantInteractionGraph_spectralGap_eq_five` | `Legitimacy.Spectral.CrossScale.ClaimantInteraction` |
| Canonical spectral-gap bound | `peerRelativeNode_claimantInteractionGraph_spectralGap_bound` | `Legitimacy.Spectral.CrossScale.ClaimantInteraction` |
| Parameterized spectral predicate | `SpectralWellConnectedAt` | `Legitimacy.Spectral.Core.SpectralWellConnected` |
| Default spectral predicate | `SpectralWellConnected` | `Legitimacy.Spectral.Core.SpectralWellConnected` |
| Finite-family admissible window | `nonbottleneck_archetype_family_admissible_window` | `Legitimacy.Spectral.CrossScale.FiniteCrossScaleUniversality.Universality` |
| Weighted-regular natural class | `GovGraph.IsWeightedRegular` | `Legitimacy.Spectral.CrossScale.Universality` |
| Weighted-regular product hypothesis | `GovGraph.WeightedRegularDefaultProductLowerBound` | `Legitimacy.Spectral.CrossScale.Universality` |
| Weighted-regular window theorem | `GovGraph.IsWeightedRegular.admits_default_window_of_product_lower_bound` | `Legitimacy.Spectral.CrossScale.Universality` |
| Complete-graph archetype membership | `uniK5_isWeightedRegular` | `Legitimacy.Spectral.CrossScale.Universality` |
| Complete-graph archetype membership | `uniK7_isWeightedRegular` | `Legitimacy.Spectral.CrossScale.Universality` |
| Complete-graph archetype membership | `uniK9_isWeightedRegular` | `Legitimacy.Spectral.CrossScale.Universality` |
| Bounded source-to-artifact contract | `BoundedExtractorContract` | `Legitimacy.Extract.Soundness` |
| Bounded source-to-artifact soundness | `bounded_extractor_contract_sound` | `Legitimacy.Extract.Soundness` |

[^03-anchor-2]: Lean: `structural_scarce_peer_relative_allocator_obstructionGenerator`; concrete structural inhabitant `weakestWithStrongerPeerNode_structural`; represented obstruction `representedPeer_obstructs_diagnostics`; median-node boundary `peerRelativeNode_not_structural`.

[^03-anchor-3]: Lean: `IsPeerRelativeAggregator`.

[^03-anchor-4]: Lean: `non_peer_relative_collapse_or_infeasible_or_exits_kernel`.

[^03-anchor-5]: Lean: `reachable_peer_relative_decisive_stage_obstructs_diagnostics`.

[^03-anchor-6]: Lean: `decisionSystem_solidarity_monotonicity_imply_strategyproof`.

[^03-anchor-7]: Lean: `semanticKernel_iff_runtime_diagnostic_spectral_layers_unfolded`.

[^03-anchor-8]: Lean: `bounded_extractor_contract_sound`.

[^03-anchor-9]: Lean: `codex_claude_sdk_review_required_joint_rejection`.

[^lean-semantic-bridge]: Lean correspondence: `IsSemanticLegitimacyKernel`, `isSemanticLegitimacyKernel_iff_runtime_and_bridge`, `semanticKernel_iff_runtime_diagnostic_spectral_layers_unfolded`, and `semanticKernel_iff_runtime_diagnostic_spectral_layers` in `Legitimacy.Results.SemanticBridge` and `Legitimacy.Kernel.Class`.

[^lean-impossibility-core]: Lean correspondence: broad interface `DecisionSystem`; theorem-bearing refinement `DecisionPipeline`; compatibility marker `BinaryDecisionPipeline`; generic diagnostics `GraphConsistencyP`, `GraphSolidarityP`, `GraphMonotonicityP`, and `GraphStrategyproofnessP`; reachable-stage headline names `ReachablePeerRelativeDecisiveStage`, `reachable_peer_relative_decisive_stage_obstructs_diagnostics`, `complete_first_effective_implies_reachable_peer_relative_decisive`, `without_transparentPrefix_denying_prefix_masks_obstruction`, and `without_nonDenyingSuffix_permit_revoking_suffix_masks_obstruction`; structural names `StructuralScarcePeerRelativeAllocator`, `NontrivialSymmetricScarcePeerRelativeBinaryAllocator`, `weakestWithStrongerPeerNode_structural`, `representedPeer_obstructs_diagnostics`, `peerRelativeNode_not_structural`, `scarce_symmetric_peer_allocator_has_competitive_displacement`, `scarce_symmetric_peer_allocator_has_reduction_violation`, `structural_scarce_peer_relative_allocator_implies_aggregator`, `nontrivial_symmetric_scarce_peer_relative_binary_allocators_obstructed`, `peer_relative_by_context_alone_insufficient`, `peer_relative_with_finite_estate_without_symmetry_insufficient`, and `upstream_deny_all_gate_vacuous_countermodel`; compatibility theorems `binaryDecisionPipeline_effectiveSurface_complete_three_axiom_obstruction`, `binaryDecisionPipeline_isPeerRelativeAggregator_complete_obstruction`, `binaryDecisionPipeline_existsClass_three_axiom_obstruction`, and `decisionSystem_solidarity_monotonicity_imply_strategyproof`; concrete `GovernanceGraph` derivations `effectivePeerRelativeSurface_complete_three_axiom_obstruction_via_pipeline`, `effectivePeerRelativeSurface_complete_three_axiom_obstruction`, `effectivePeerRelativeSurface_existsClass_three_axiom_obstruction_via_pipeline`, `effectivePeerRelativeSurface_complete_impossibility`, `solidarity_monotonicity_imply_strategyproof_via_decisionSystem`, and `solidarity_monotonicity_imply_strategyproof`; modules: `Legitimacy.Impossibility.PeerRelativeReachable`, `Legitimacy.Foundations.StructuralPeerRelative`, `Legitimacy.Foundations.DecisionSystem`, `Legitimacy.Diagnostics.DecisionSystem`, `Legitimacy.Impossibility.PeerRelativeClass`, `Legitimacy.Impossibility.AxiomIndependence`, and `Legitimacy.Results.Impossibility`.

[^lean-model-map]: Lean correspondence: the canonical concrete binary pipeline substrate is `GovernanceGraph := List GovernanceNodeFn`; the binary-to-spectral weighted encoding is `claimantInteractionGraph` in `Legitimacy.Spectral.CrossScale.ClaimantInteraction`; the generic DAG transfer contract is `DAGToPipelineModelMap`, with `DAGToBinaryModelMap` retained as the `GovernanceGraph` specialization by `dagToBinaryModelMap_eq_pipeline`; the generic transfer theorem is `dagPeerRelativeSurfaceMap_pipeline_impossibility`, with concrete compatibility forms `dagPeerRelativeSurfaceMap_impossibility_via_pipeline` and `dagPeerRelativeSurfaceMap_impossibility`; the worked structural family is `SinglePeerChokepointGovernedSystem` with `canonicalSinglePeerChokepointSystem`, `singlePeerChokepointGovernedSystem_admits_pipeline_modelMap`, `canonicalSinglePeerChokepointSystem_admits_pipeline_modelMap`, `singlePeerChokepointGovernedSystem_admits_binary_modelMap`, `singlePeerChokepointGovernedSystem_peerSurfaceMap`, and `singlePeerChokepointGovernedSystem_impossibility`.

[^lean-safety-stack]: Lean correspondence: deployment honesty lives in `Legitimacy.Safety.KernelSafety.BinaryDecisionPipeline` with `Legitimacy.Safety.IsLiveCompiled`, `Legitimacy.Safety.CompletePeerRelativeSurface`, `Legitimacy.Safety.ForcedPeerRelativeSacrificesDeclared`, `Legitimacy.Safety.liveCompiled_declaredSacrifice_iff_propertyFailure`, `Legitimacy.Safety.completePeerRelativeSurface_live_forces_sacrificesDeclared`, and headline alias `Legitimacy.Safety.noUndeclaredSacrifice`; trajectory honesty lives in `Legitimacy.Safety.KernelSafety.ReachabilityStack` with `Legitimacy.Safety.KernelTrajectoryHasSacrifice`, `Legitimacy.Safety.ReachableStateSafetyConclusion`, `Legitimacy.Safety.reachable_state_safety`, `Legitimacy.Safety.kernelReachabilitySafety`, `Legitimacy.Safety.kernelReachabilitySafety_exhaustive_supportedTrajectoryClass`, `Legitimacy.Safety.StatefulAgentSchedule`, `Legitimacy.Safety.stateful_agent_schedule_safety`, `Legitimacy.Safety.stateful_agent_intervention_schedule_safety`, `Legitimacy.Safety.nondeterministic_stateful_agent_schedule_safety`, and `Legitimacy.Safety.fair_infinite_stateful_agent_schedule_prefix_safety`; the worked fixture is `Legitimacy.Safety.peerSurfaceWorkedExample_noUndeclaredDeployment_and_reachableSacrifice`.

## References
[AARs2026] Anthropic. Automated Alignment Researchers: Using large language models to scale scalable oversight. Technical blog post, April 14, 2026. https://www.anthropic.com/research/automated-alignment-researchers.

[Arrow1951] Arrow, K. J. Social Choice and Individual Values. Yale University Press, 1951.

[Bai2022] Bai, Y., et al. Constitutional AI: Harmlessness from AI Feedback. arXiv:2212.08073, 2022.

[Baldwin1991] Baldwin, S. An extension of Sharkovskii's Theorem to the n-od. Ergodic Theory and Dynamical Systems, 11(2):249–271, 1991.

[Balinski1982] Balinski, M. L., and Young, H. P. Fair Representation: Meeting the Ideal of One Man, One Vote. Yale University Press, 1982.

[Bengio2025] Bengio, Y., Cohen, M., Fornasiere, D., Ghosn, J., Greiner, P., MacDermott, M., Mindermann, S., Oberman, A., Richardson, J., Richardson, O., Rondeau, M.-A., St-Charles, P.-L., and Williams-King, D. Superintelligent Agents Pose Catastrophic Risks: Can Scientist AI Offer a Safer Path? arXiv:2502.15657, 2025.

[BelsleyKuhWelsch1980] Belsley, D. A., Kuh, E., and Welsch, R. E. Regression Diagnostics: Identifying Influential Data and Sources of Collinearity. Wiley, 1980.

[BrcicYampolskiy2024] Brcic, M., and Yampolskiy, R. V. Impossibility Results in AI: A Survey. ACM Computing Surveys, 56(1), 2024.

[Brandt2016] Brandt, F., Conitzer, V., Endriss, U., Lang, J., and Procaccia, A. D., editors. Handbook of Computational Social Choice. Cambridge University Press, 2016.

[Cardy1988] Cardy, J., editor. Finite-Size Scaling. North-Holland, 1988.

[Cheeger1970] Cheeger, J. A lower bound for the smallest eigenvalue of the Laplacian. Problems in Analysis, 195:199, 1970.

[Chen2021] Chen, D., Su, H., Wang, X., Pan, G.-J., and Chen, G. Finite-size scaling of geometric renormalization flows in complex networks. Physical Review E, 104:034304, 2021.

[Chouldechova2017] Chouldechova, A. Fair prediction with disparate impact: a study of bias in recidivism prediction instruments. Big Data, 5(2):153–163, 2017.

[Chung1997] Chung, F. R. K. Spectral Graph Theory. American Mathematical Society, 1997.

[Cook1977] Cook, R. D. Detection of Influential Observations in Linear Regression. Technometrics, 19(1):15–18, 1977.

[CookWeisberg1982] Cook, R. D., and Weisberg, S. Residuals and Influence in Regression. Chapman and Hall, 1982.

[Conitzer2024] Conitzer, V., et al. Social Choice Should Guide AI Alignment in Dealing with Diverse Human Feedback. In Proceedings of the 41st International Conference on Machine Learning, Proceedings of Machine Learning Research 235:9346–9360, 2024. https://proceedings.mlr.press/v235/conitzer24a.html.

[Dalrymple2024] Dalrymple, D., et al. Towards Guaranteed Safe AI: A Framework for Ensuring Robust and Reliable AI Systems. arXiv:2405.06624, 2024.

[Databricks2026] Databricks. AI Gateway (Beta). Databricks product release notes, February 2026. https://docs.databricks.com/aws/en/release-notes/product/2026/february. Source note: product documentation used only as industry enforcement-plane context, not theorem support.

[DGM-H2026] UBC, Vector Institute, Edinburgh, NYU, FAIR, Meta Superintelligence Labs. Darwin Godel Machine: Metacognitive Self-Improvement via Editable Hyperagents. arXiv:2603.19461, 2026.

[DorflerBullo2013] Dörfler, F., and Bullo, F. Kron Reduction of Graphs with Applications to Electrical Networks. IEEE Trans. Circuits Syst. I, 60(1):150–163, 2013.

[DworkRoth2014] Dwork, C., and Roth, A. The Algorithmic Foundations of Differential Privacy. Foundations and Trends in Theoretical Computer Science, 9(3–4):211–407, 2014.

[Eckersley2019] Eckersley, P. Impossibility and Uncertainty Theorems in AI Value Alignment (or why your AGI should not have a utility function). arXiv:1901.00064. SafeAI 2019: AAAI Workshop on Artificial Intelligence Safety, 2019.

[Fernandez2026] Fernandez, M. Agent Control Protocol: Admission Control for Agent Actions. arXiv:2603.18829, 2026.

[Galam1986] Galam, S. Majority rule, hierarchical structures and democratic totalitarianism: a statistical approach. Journal of Mathematical Psychology, 30(4):426–434, 1986.

[Galam1990] Galam, S. Social paradoxes of majority rule voting and renormalization group. Journal of Statistical Physics, 61:943–951, 1990.

[Galam2000] Galam, S. Real space renormalization group and totalitarian paradox of majority rule voting. Physica A, 285:66–76, 2000.

[García-Pérez2018] García-Pérez, G., Boguñá, M., and Serrano, M. Á. Multiscale unfolding of real networks by geometric renormalization. Nature Physics, 14:583–589, 2018.

[Ge2024] Ge, L., et al. Axioms for AI Alignment from Human Feedback. arXiv:2405.14758. NeurIPS 2024, 2024.

[Gfeller2007] Gfeller, D., and De Los Rios, P. Spectral Coarse Graining of Complex Networks. Physical Review Letters, 99:038701, 2007.

[Gibbard1973] Gibbard, A. Manipulation of voting schemes: a general result. Econometrica, 41(4):587–601, 1973.

[GrandiEndriss2013] Grandi, U., and Endriss, U. First-Order Logic Formalisation of Impossibility Theorems in Preference Aggregation. Journal of Philosophical Logic, 42(4):595–618, 2013.

[Hampel1974] Hampel, F. R. The Influence Curve and Its Role in Robust Estimation. Journal of the American Statistical Association, 69(346):383–393, 1974.

[Hampel1986] Hampel, F. R., Ronchetti, E. M., Rousseeuw, P. J., and Stahel, W. A. Robust Statistics: The Approach Based on Influence Functions. Wiley, 1986.

[Hubinger2023] Hubinger, E., Jermyn, A., Treutlein, J., Hudson, R., and Woolverton, K. Conditioning Predictive Models: Risks and Strategies. arXiv:2302.00805, 2023.

[Kadanoff1966] Kadanoff, L. P. Scaling laws for Ising models near T_c. Physics, 2:263–272, 1966.

[Kleinberg2017] Kleinberg, J., Mullainathan, S., and Raghavan, M. Inherent trade-offs in the fair determination of risk scores. In Proceedings of the 8th Innovations in Theoretical Computer Science Conference, pages 43:1–43:23, 2017.

[LeeGharanTrevisan2012] Lee, J. R., Oveis Gharan, S., and Trevisan, L. Multi-way spectral partitioning and higher-order Cheeger inequalities. In Proceedings of the 44th ACM Symposium on Theory of Computing, pages 1117–1130, 2012.

[Loukas2019] Loukas, A. Graph Reduction with Spectral and Cut Guarantees. Journal of Machine Learning Research, 20(116):1–42, 2019.

[Maskin1999] Maskin, E. S. Nash equilibrium and welfare optimality. Review of Economic Studies, 66(1):23–38, 1999.

[MaskinSjostrom2002] Maskin, E. S., and Sjöström, T. Implementation Theory. In Arrow, K. J., Sen, A. K., and Suzumura, K., editors, Handbook of Social Choice and Welfare, volume 1, chapter 5, pages 237–288. Elsevier, 2002.

[Mathlib2023] The mathlib Community. Mathlib: A library for formal mathematics in Lean 4. 2023.

[Moulin1991] Moulin, H. Axioms of Cooperative Decision Making. Econometric Society Monographs. Cambridge University Press, 1991.

[Moura2021] de Moura, L., and Ullrich, S. The Lean 4 Theorem Prover and Programming Language. CADE-28, 2021.

[Nayebi2025] Nayebi, A. Intrinsic Barriers and Practical Pathways for Human-AI Alignment: An Agreement-Based Complexity Analysis. arXiv:2502.05934. To appear in AAAI 2026 Special Track on AI Alignment (oral), 2025.

[MyersonSatterthwaite1983] Myerson, R. B., and Satterthwaite, M. A. Efficient mechanisms for bilateral trading. Journal of Economic Theory, 29(2):265–281, 1983.

[NissimRaskhodnikovaSmith2007] Nissim, K., Raskhodnikova, S., and Smith, A. Smooth Sensitivity and Sampling in Private Data Analysis. In Proceedings of the 39th ACM Symposium on Theory of Computing, pages 75–84, 2007.

[Nipkow2009] Nipkow, T. Social Choice Theory in HOL: Arrow and Gibbard-Satterthwaite. Journal of Automated Reasoning, 43(3):289–304, 2009.

[Nurisso2025] Nurisso, M., et al. Higher-order Laplacian renormalization. Nature Physics, 21:661–668, 2025. doi:10.1038/s41567-025-02784-1.

[OrtegaBraun2013] Ortega, P. A., and Braun, D. A. Thermodynamics as a theory of decision-making with information-processing costs. Proceedings of the Royal Society A, 469:20120683, 2013.

[Ostrom2009] Ostrom, E. Beyond Markets and States: Polycentric Governance of Complex Economic Systems. American Economic Review, 100(3):641–672, 2009.

[Palumbo2026] Palumbo, N., et al. Policy Compiler for Secure Agentic Systems. arXiv:2602.16708, 2026.

[Procaccia2025] Procaccia, A. D., Schiffer, B., and Zhang, S. Clone-Robust AI Alignment. In Proceedings of the 42nd International Conference on Machine Learning, Proceedings of Machine Learning Research 267:49903–49926, 2025. https://proceedings.mlr.press/v267/procaccia25a.html.

[RLHFTrilemma2025] Sahoo, S., Chadha, A., Jain, V., and Chaudhary, D. Position: The Complexity of Perfect AI Alignment: Formalizing the RLHF Trilemma. arXiv:2511.19504. Accepted at the NeurIPS 2025 Workshop on Socially Responsible and Trustworthy Foundation Models, 2025.

[Satterthwaite1975] Satterthwaite, M. A. Strategy-proofness and Arrow's conditions: Existence and correspondence theorems for voting procedures and social welfare functions. Journal of Economic Theory, 10(2):187–217, 1975.

[Sen1970] Sen, A. K. The Impossibility of a Paretian Liberal. Journal of Political Economy, 78(1):152–157, 1970. doi:10.1086/259614.

[Skalse2022] Skalse, J., Howe, N. H. R., Krasheninnikov, D., and Krueger, D. Defining and Characterizing Reward Hacking. In Advances in Neural Information Processing Systems, 35, 2022.

[Song2005] Song, C., Havlin, S., and Makse, H. A. Self-similarity of complex networks. Nature, 433:392–395, 2005.

[Spielman2010] Spielman, D. Algorithms, graph theory, and linear equations in Laplacian matrices. In Proceedings of the ICM, 4:2698–2722, 2010.

[Tibebu2026] Tibebu, H. The Accountability Horizon: An Impossibility Theorem for Governing Human-Agent Collectives. arXiv:2604.07778, 2026.

[TypeCheckedCompliance2026] Rashie, D., and Rashi, V. Type-Checked Compliance: Deterministic Guardrails for Agentic Financial Systems Using Lean 4 Theorem Proving. arXiv:2604.01483, 2026.

[Thomson2003] Thomson, W. Axiomatic and game-theoretic analysis of bankruptcy and taxation problems: a survey. Mathematical Social Sciences, 45(3):249–297, 2003.

[Thomson2015] Thomson, W. Axiomatic and game-theoretic analysis of bankruptcy and taxation problems: an update. Mathematical Social Sciences, 74:41–59, 2015.

[Thomson2019] Thomson, W. How to Divide When There Isn't Enough: From Aristotle, the Talmud, and Maimonides to the Axiomatics of Resource Allocation. Cambridge University Press, 2019.

[Villegas2023] Villegas, P., Gili, T., Caldarelli, G., and Gabrielli, A. Laplacian renormalization group for heterogeneous networks. Nature Physics, 19:445–450, 2023.

[Wiedijk2007] Wiedijk, F. Arrow's Impossibility Theorem. Formalized Mathematics, 15(4):171–174, 2007.

[Wilson1971] Wilson, K. G. Renormalization group and critical phenomena I, II. Physical Review B, 4:3174–3205, 1971.

[WilsonKogut1974] Wilson, K. G., and Kogut, J. The renormalization group and the ε-expansion. Physics Reports, 12:75–199, 1974.

[YudkowskyHerreshoff2013] Yudkowsky, E., and Herreshoff, M. Tiling Agents for Self-Modifying AI, and the Löbian Obstacle. MIRI technical report draft, 2013.

[Young1994] Young, H. P. Equity: In Theory and Practice. Princeton University Press, 1994.

[^lean-gx-18-1]: Lean identifiers: `claimantInteractionGraph` (weighted encoding of binary pipelines), `CompleteFirstEffectivePeerRelativeSurfaceClass` (certificate), `claimantInteractionGraph_eq_constructedPeerRelativeCarrier_of_completeSurface` (unfolds the chosen complete claimant-interaction carrier), `IsPeerRelativeAggregator` (the aggregator witness referenced by the construction-lemma scope), `peerRelativeNode_claimantInteractionGraph_eq_uniK5` and `uniK5` (constructed carrier identified with the spectral archetype), and `peerRelativeNode_claimantInteractionGraph_spectralGap_eq_five` (imports the discharged λ₂ = 5 theorem).

[^lean-gx-03s2-1]: Lean identifiers: `independent_certifiable`, `independent_observable`, `independent_corrigible`, `independent_compositional_safety`, and `independent_nonvacuous`.

[^lean-gx-03s2-2]: Lean identifiers: `dagBridge_decision_equiv_field_independent`, `dagBridge_effective_surface_field_independent`, `dagBridge_complete_tail_field_independent`, and `dagPeerRelativeSurfaceMap_binary_transfer_without_reflects_graph`.

[^lean-gx-03s2-3]: Lean identifiers: `dagBridge_reflects_graph_definitionally_redundant`.

[^lean-gx-03s2-4]: Lean identifiers: `dagPeerRelativeSurfaceMap_pipeline_impossibility`, `singlePeerChokepointGovernedSystem_admits_pipeline_modelMap`, and `singlePeerChokepointGovernedSystem_admits_binary_modelMap` (the `GovernanceGraph` compatibility form).

[^lean-gx-06s3-1]: Lean identifiers: `codexHooksGovernanceAdmissibilityRejectsMonotonicity`, `claudeAgentSDKHooksGovernanceAdmissibilityRejectsMonotonicity`, `crewAIHooksGovernanceAdmissibilityRejectsMonotonicity`, and `openClawInfraNonvacuityCheckFails`.

[^lean-gx-06s63-1]: Lean identifiers: the per-archetype certificate-discharge-pending obligations cover `asymK5`, `nearPath5`, `wheel5`, `asymK7`, `nearPath7`, `asymK9`, `nearPath9`, `hubSpokeHierarchy9`, `nestedHierarchy9`, and `wheel9`.

[^lean-gx-07-1]: Lean identifiers: `OverrideCorrigible`, `OverridePreserving`, `hasOverride`, `sacrifices`, and `CompilationChecks`.

[^lean-gx-07-2]: Lean identifiers: `Legitimacy.well_connected_observational_corrigibility_bridge_quantitative_at`.

[^lean-gx-07-3]: Lean identifiers: `exampleSubcriticalMutatingStatefulAdversary_yields_boundedCorrigibility_or_sacrifice_left` and `exampleSupercriticalAdversary_yields_consistency_sacrifice_right`.
