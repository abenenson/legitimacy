# Which Governance Structures Survive Unbounded Capability? Capacity and Stability Bounds for AI Governance Graphs

*Adam Benenson, 2026*

---

## Abstract
As an AI agent's modeled capability grows without bound, which governance rules can still certify its decisions, and which collapse? For a represented governance graph under the stated channel embedding, zero-error certification has a tight, computable threshold: C*(G,s,δ) = δ/cv(G,s), where cv is the rule's consistency vulnerability. Above C*, no target-saturating positive-rate certifier remains error-free as capability scales; below it, a well-conditioned kernel yields a constructive positive certificate. Fixed-graph spectral stability obeys the same boundary. A rule remains stable at unbounded capability exactly when its consistency vulnerability is zero; positive vulnerability produces a finite, computable cliff, including along adversarial capability paths. A separate shared-substrate theorem connects this analysis to the companion impossibility: on a constructed canonical claimant-interaction lift, the scarce, peer-relative obstruction forces positive consistency vulnerability and therefore a finite cliff. The positive procedure composes constitutional-AI, adversarial, and AI-control substrates at an audited scale. On the extracted OpenAI Codex hooks graph model, consistency vulnerability is one; an explicit repair reduces it to zero and removes the finite cliff. C* is a graph-side critical capability, distinct from the Shannon capacity of a fixed channel and from any behavioral estimate of model capability. The results bind to represented graphs under explicit embeddings; behavioral lineages require separate embedding proofs. All results are machine-checked in Lean 4 with no `sorry`, `admit`, or first-party `axiom`.
## Highlights

> **Standalone results, one proved join.** This paper studies when a represented governance graph can certify decisions, remain spectrally stable, and preserve finite-family structure under stated embeddings. The core results are self-contained graph mathematics whose proofs neither presuppose nor instantiate the impossibility. The join to the companion is itself a theorem rather than framing: on the canonical claimant-interaction lift (definitionally `uniK5` with fixed signal `sig5`), a shared-substrate composition (`capability_scaling_shared_cliff`) ties the peer-relative obstruction to positive consistency vulnerability, hence to the capability cliff, while the Shannon Negative Bridge keeps the graph-side threshold and the information-theoretic capacity as two separately-proved objects.

> **Capacity terminology.**
> "Capacity" refers to the zero-error log-rate ceiling of the capability-response channel and its graph-side threshold package. $C^*(G,s,\delta)=\delta/cv(G,s)$ is the critical capability at which deterministic target-saturating positive-log-rate `AlignmentProtocol` families embedded through the represented graph's threshold channel have some failed deployment message under the stated target-floor obligations. It is not the Shannon capacity of a fixed noisy channel and not a behavioral estimate of model capability.

> **Evidence tier.** Theorems are over formal finite governance graphs and specified channel/surrogate embeddings. Behavioral lineages inherit the results only after a separate embedding proof.

```{=latex}
\begin{tcolorbox}[figurebox,title={\textbf{Figure 1.} Capacity, stability, and coarse-graining on one represented governance graph}]
\ttfamily\small
governance graph G, signal s, tolerance delta\\
\textbar{}-- capacity ceiling: C* = delta / cv(G,s)\\
\textbar{}-- stability ceiling: Stackelberg cliff kappa\_0\\
\textbackslash{}-- coarse-graining: finite-family basin evidence\\
\end{tcolorbox}
```

> **Artifact, data, and companion papers.** This paper is one of the Legitimacy program's manuscripts. The machine-checked artifact (Lean 4 theorem stack + Rust audit pipeline), the companion papers, and the claim ledger are in the project repository, github.com/abenenson/legitimacy; project page: adambenenson.com/projects/legitimacy. Verification code anchor: `v1.0.0`. Dual license: MIT OR Apache-2.0.

> **Capacity converse, informal.** For deterministic protocols embedded in the specified capability-response channel, no zero-error block code can sustain log-rate strictly above one binary decision per channel use. For `δ>0` and `cv(G,s)>0`, at or above the graph's critical threshold, deterministic target-saturating positive-rate `AlignmentProtocol` families with the target-floor obligations have a failed deployment message.

> **Positive certificate below the threshold, informal.** Below `C*` the substrate certifies rather than only failing: for a well-conditioned kernel, every positive `c ≤ C*` extracts a `PositiveProcedureCertificate`, and a cross-lineage composition over a Constitutional-AI harm partition, a Stackelberg adversary, and an AI-Control monitor budget yields a compatible certificate at one audited scale (`composedLineage_positiveProcedure_classification`). The Constitutional-AI side is a principle/conflict (Constitution-as-DAG) substrate, not an extraction of any published constitution.

> **Stackelberg limit, informal.** In the fixed-graph spectral surrogate, a governance graph admits stable equilibria at arbitrarily large capability levels if and only if its consistency vulnerability is zero. The extracted OpenAI Codex hooks harness instantiates the unstable side, consistency vulnerability `cv = 1`, a finite stability cliff under capability scaling, which an explicit repair removes.

> **General-`n` spectral scaling, informal.** The strongest spectral statements are not size-bounded tables. For the unit-weight complete governance carrier on `n+1` vertices, the spectral gap has the closed form `n+1` for *every* `n` with `2 ≤ n+1`, and the same family is spectrally well-connected for *every* `n ≥ 2`. These are arbitrary-`n` theorems, not the finite `n=5/7/9` evaluations they generalize.

> **Bifurcation boundary, informal.** At a fixed capability kappa, the formal bifurcation predicate packages capacity admissibility, positive vulnerability, and spectral stability into one boundary check on this substrate.

> **Shannon Negative Bridge, informal.** One fixed scalar noisy-threshold channel cannot identify its Shannon capacity with the graph-spectral `C*` values of the concrete two-graph witness. The graph-side threshold and the Shannon capacity are distinct objects; any Shannon bridge needs a separate graph-dependent construction or a narrower agreement class.

## 1. Introduction

This paper asks three questions about one represented governance graph `G`, rational strength signal `s`, and tolerance `δ`. The first question is what the graph can certify: the capacity ceiling gives the threshold `C* = δ / cv(G,s)` for deterministic zero-error certification through the specified capability-response channel, where `cv(G,s)` is the graph's consistency vulnerability, a spectral measure of how easily a node removal degrades the graph's certification. The second question is what stays stable as the modeled capability scale grows: the Stackelberg limit characterizes fixed-graph spectral stability by vanishing consistency vulnerability. The third question is what the committed coarse-graining selectors produce: the RG results record finite trajectory tables and a standard-trajectory δ-parametric signature for the represented substrate.

These are standalone graph-mathematics results. They live beside the legitimacy kernel and its forcing argument rather than inside them: the capacity threshold, the stability ceiling, and the coarse-graining tables are properties of the represented graph under stated embeddings, and they neither presuppose nor instantiate the impossibility. The connection to the companion is carried separately and is itself proved: on the canonical claimant-interaction lift (definitionally `uniK5` with fixed signal `sig5`), the shared-substrate composition `capability_scaling_shared_cliff` derives positive consistency vulnerability, hence a finite cliff, from the peer-relative obstruction. Two integrative results clarify how the three questions relate. The Bifurcation Iff theorem packages capacity admissibility, positive spectral vulnerability, and spectral stability into one boundary check on this substrate. The Shannon Negative Bridge then records the paper's central boundary fact: the graph-spectral threshold `C*` is *not* identifiable with the Shannon capacity of a fixed noisy-threshold channel. The positive result gives a substrate-level boundary package; the negative result maps the boundary between the graph-side threshold and the information-theoretic capacity. By design, that boundary map keeps two distinct, separately-proved objects from being conflated.

A reader landing on this paper first should know the companion order. The impossibility companion proves that a reachable scarce allocation stage is *forced* to sacrifice one of its structural diagnostics; this paper prices what the same represented graph can still certify, and how long it stays stable, as capability scales. Read the companion for why the sacrifice exists; read this paper for what survives it.

| Claim | Evidence | Boundary |
| --- | --- | --- |
| Capacity converse above binary log-rate | Proved by Lean theorem | Deterministic zero-error channel embedding |
| C* threshold for embedded verifier | Proved by Lean theorem | Target-saturating capability-response channel |
| Stackelberg asymptotic iff | Proved by Lean theorem | Fixed graph, spectral surrogate |
| Adversarial scaling companion | Proved by Lean theorem | Cofinal adversaries inside surrogate |
| Bifurcation iff | Proved by Lean theorem | Finite rational graph, positive cv, fixed kappa |
| General-`n` complete-carrier spectral gap | Proved by Lean theorem | Unit-weight complete carrier on `n+1` vertices, arbitrary `n` |
| General-`n` spectral well-connectedness | Proved by Lean theorem | Complete-carrier family, every `n ≥ 2` |
| Basin classification = bridge-discharge classification | Proved by Lean theorem | Finite `n=5` verification lattice (five graphs); `bottleneck5` sole refutation |
| RG finite trajectory evidence | Lean finite-table results | Scoped to n=5 selectors; cross-size and arbitrary-partition universality are not claimed |

| Claim | Formal anchor |
| --- | --- |
| Capacity converse above binary log-rate | `binary_output_log_rate_converse` |
| C* threshold for embedded verifier | `governance_capacity_alignment_threshold` |
| Stackelberg asymptotic iff | `stackelberg_convergence_limit_iff_zero_consistency_vulnerability` |
| Adversarial scaling companion | `adversarial_stackelberg_unbounded_stability_iff_zero_consistency_vulnerability` |
| Bifurcation iff | `bifurcation_iff_spectral` |
| General-`n` complete-carrier spectral gap | `asiCompleteGraph_spectralGap_eq` |
| General-`n` spectral well-connectedness | `uniKFamily_spectralWellConnected` |
| Basin classification = bridge-discharge classification | `n5_bridge_discharges_iff_well_connected_basin`; `n5_bridge_discharges_iff_well_connected_basin_parametric` |
| RG finite trajectory evidence | `robustness_cheeger_n5`; `robustness_modularity_n5`; `robustness_signal_preserving_n5`; `concrete_iterated_RG_n5_parametric_signature` |

Throughout this paper, the running example is the Claude Agent SDK tool-use permission gate. Its governance graph has hook and permission states as nodes, tool-use and review signals as strengths, and a permission/review threshold as the certification target. The capacity question asks how far that represented permission graph can keep certifying tool-use decisions as the modeled capability scale rises; the stability question asks whether the same graph retains spectral equilibrium under growing modeled perturbation.

Three audit moves on the same represented permission graph drive the paper. The capacity audit (§4) asks whether the graph can certify the tool-use family at the audited capability scale. The stability audit (§5) asks whether removal vulnerability creates a finite spectral cliff. The bifurcation audit (§6) packages the relevant capacity, vulnerability, and stability fields into a single boundary predicate at fixed `κ`.

The paper proceeds in that order. §2 defines the common substrate: directed governance graph, signal, tolerance, capability scale, channel embedding, and spectral surrogate. §3 states the scope boundary for represented graphs and finite substrates. §4 proves the capacity ceiling, and §5 proves the Stackelberg stability ceiling. §6 states the bifurcation boundary package. §7 generalizes the capacity substrate from binary to multi-decision responses. §8 proves the Shannon negative bridge. §9 gives the finite-family RG coarse-graining result. §10 returns to the three questions with the two integrative results established.

## 2. Setup

A *represented governance graph* is a finite directed governance object `G` whose nodes are decision or permission states and whose edges carry the represented flow of claims, review, or authority. The paper's theorems apply after an extraction or modeling step supplies this graph, not to raw model behavior directly. For the Claude Agent SDK gate, `G` is the represented hook/permission graph from request parsing through exact-match denial, review-required escalation, and final permission output.

A *strength signal* `s : Fin n → ℚ` assigns rational-valued strengths to the graph's nodes or claim coordinates. The signal records the represented priority, evidence, review pressure, or tool-use strength consumed by the spectral substrate. For the Claude Agent SDK gate, `s` records tool-use evidence and review-pressure strengths on the represented permission graph.

A *tolerance* `δ : ℚ` is the positive effectiveness floor that compares spectral vulnerability against certification failure. Whenever `cv(G,s) > 0`, the critical capability threshold is `C*(G,s,δ) = δ / cv(G,s)`. C* is the graph-side critical capability for the zero-error capacity converse: above it, deterministic target-saturating `AlignmentProtocol` verifiers with a positive-log-rate message family, target-floor obligations, and the specified capability-response-channel embedding have some failed deployment message. The term "capacity" tracks the Lean theorem name `governance_capacity_alignment_threshold`, because the theorem proves a counting-style log-rate ceiling — not the Shannon capacity of a fixed noisy channel, and not a behavioral capability estimate for a deployed model. For the Claude Agent SDK gate, `δ` is the smallest permission-review tolerance the audit treats as a certification-relevant failure.

The *capability scaling parameter* `κ` indexes the modeled perturbation or target scale at which the represented graph is audited. The capacity sections use capability levels in the capability-response channel; the Stackelberg sections use the modeled capability scale in the spectral surrogate. For the Claude Agent SDK gate, `κ` is the modeled tool-use or review-pressure scale applied to the represented permission graph.

The *capability-response channel embedding* maps a capability level to the binary response induced by the graph threshold: below the threshold the certification response is `Deny`, and at or above the threshold it is `Permit`. The capacity theorem uses this deterministic channel plus block coding to prove a zero-error counting ceiling. For the Claude Agent SDK gate, the channel abstracts whether the represented permission graph certifies the target tool-use profile at the audited capability scale.

The *spectral surrogate embedding* maps the same represented graph into the fixed-graph spectral quantities used by the Stackelberg and bifurcation theorems: consistency vulnerability `cv(G,s)`, spectral stability, and perturbation response under the modeled capability scale. The removal perturbation uses the rational convention `x/0 = 0`: an observer whose entire neighborhood is removed reads zero, so the perturbation it registers is exactly its pre-removal value; the convention matters on disconnected carriers, and the worked Codex instance pays its `cv = 1` precisely at such an observer. For the Claude Agent SDK gate, the surrogate asks whether the permission graph's removal vulnerability creates exploitable spectral instability as the modeled tool-use scale grows.

The basin predicates used later name the coarse-graining side of the same substrate. `BelowBifurcationBoundary` is defined precisely in §6, where the capacity and stability projections meet. `WellConnectedBasin` and the finite-family RG partition predicates are defined in §9, where coarse-graining supplies the third axis.

Claude Agent SDK embedding ledger. Each row reads as "when the paper says X, for the SDK gate that means Y, with status Z."

| Formal object | Claude Agent SDK gate reading | Status |
| --- | --- | --- |
| `G` | Represented hook/permission graph from request parsing through denial, review escalation, and final permission output | Supplied by bounded extraction or modeling |
| `s` | Tool-use evidence and review-pressure strengths | Modeled signal |
| `δ` | Smallest permission-review tolerance treated as certification-relevant failure | Audit parameter |
| `κ` | Tool-use or review-pressure scale | Modeled capability scale |
| Capability-response channel | Binary certification response induced by the represented permission graph threshold | Embedding assumption to check |
| Zero-error code | Distinguishable tool-use certification messages over permit/deny outputs | Theorem substrate |
| Spectral surrogate | Removal vulnerability and stability of the same represented permission graph | Formal surrogate |
| Evidence tier | Represented graph theorem, not live-product semantics | Artifact / modeled-graph evidence |

## 3. Scope and Limitations

This paper analyzes represented governance graphs under stated channel and spectral-surrogate embeddings. RLHF, debate, deliberative alignment, chain-of-thought monitorability, Constitutional AI, AI Control, and other behavioral lineages inherit these bounds only after a separate embedding proof shows that their certification step factors through the represented substrate. For the Claude Agent SDK gate, the theorems apply to the represented permission graph supplied by bounded extraction or modeling, not to the live product or raw source code without that bridge.

The capacity results are deterministic zero-error converses for the specified capability-response channel and its multi-decision generalization. Probabilistic protocols, list decoding, variable-length coding, and behavioral alignment-as-training fall outside that theorem unless a separate extension supplies the channel model. The Shannon negative bridge in §8 is therefore a boundary result: it maps the boundary between the graph-spectral `C*` and a fixed-channel Shannon capacity by ruling out their identification, rather than supplying a universal noisy-channel converse.

C* is the graph-side critical capability for the zero-error capacity converse: a worst-case floor on the capability level at which a represented governance graph can still certify legitimate decisions without confusion, within the stated graph and channel embedding. Probabilistic protocols (PAC-style bounds, list-decoding, expected-case guarantees) may improve operational certification under additional channel assumptions; they do not change this graph-defined threshold unless the graph or embedding changes.

The Stackelberg and bifurcation results use the fixed-graph spectral surrogate. They characterize stability under the modeled capability scale and do not claim full game-theoretic equilibrium dynamics for every deployed verifier architecture. The RG results are finite-table statements on named selectors and the standard `n=5` trajectory; cross-size universality, arbitrary partition families, continuous Wilson-Fisher-style RG flows, and empirical claims about real-world governance graphs remain outside the formal claim.

[^04-anchor-1]: Lean: `governance_capacity_alignment_threshold`.

[^04-anchor-2]: Lean: `binary_output_log_rate_converse`.

[^04-anchor-3]: Lean: `capabilityResponseBinaryBlockCode`; `capabilityResponseBinaryBlockCode_zeroError`; `capabilityResponseBinaryBlockCode_log2_message_card`.

[^04-anchor-4]: Lean: `stackelberg_convergence_limit_iff_zero_consistency_vulnerability`.

[^04-anchor-5]: Lean: `eventually_no_stable_equilibrium_of_positive_consistency_vulnerability`.

[^04-anchor-6]: Lean: `adversarial_stackelberg_unbounded_stability_iff_zero_consistency_vulnerability`.

[^04-anchor-7]: Lean: `bifurcation_iff_spectral`.

[^04-anchor-8]: Lean: `fixed_noisyThreshold_capacity_not_concrete_C_star_bridge`.

[^04-anchor-9]: Lean: `concrete_iterated_RG_n5_parametric_signature`; `robustness_cheeger_n5`; `robustness_modularity_n5`; `robustness_signal_preserving_n5`.

[^04-anchor-10]: Lean: `multi_decision_capability_response_log_rate_converse`.

[^04-anchor-11]: Lean: `multi_decision_capability_response_C_star_binding`.

[^04-anchor-12]: Lean: `asiCompleteGraph_spectralGap_eq`.

[^04-anchor-13]: Lean: `uniKFamily_spectralWellConnected`.

[^04-anchor-14]: Lean: `n5_bridge_discharges_iff_well_connected_basin`.

## 4. Capacity Ceiling

The capacity ceiling answers the first question on the shared substrate: what can the represented graph certify? For deterministic protocols embedded in the capability-response channel of §2, the binary-output converse gives a zero-error log-rate ceiling, and the `C*` threshold binds that ceiling to graph vulnerability. For the Claude Agent SDK gate, the audit move is to verify that the tool-use certification procedure factors through the represented permission graph's threshold channel before applying the theorem. The scope boundaries for `C*` — that it is a graph-side threshold, not a Shannon capacity, and that probabilistic protocols do not move it without a changed graph or embedding — are stated once in §3.

### 4.1 Main results

##### 4.1 The binary-output log-rate converse

**Theorem 4.1** (Binary-output log-rate converse). The binary-output counting theorem supplies the log-rate ceiling.[^04-anchor-2]
*Let `G : GovGraph ℚ n` with `[NeZero n]`, `s : Fin n → ℚ`, `δ : ℚ`, and `rate > binaryDecisionPerUseRate`. Then there exists a block threshold such that every block at or above it rejects any capability-response block code whose message-cardinality log-rate is at least `rate`.*

For the Claude Agent SDK gate, the reviewer uses this theorem to compare the number of distinguishable tool-use certification messages with the binary permit/deny output words available to the represented permission channel.

Formally:

```
theorem binary_output_log_rate_converse :
    (G : GovGraph ℚ n) [NeZero n] (s : Fin n → ℚ) (δ : ℚ)
    (rate : ℚ) (hrate : binaryDecisionPerUseRate < rate) :
    ∃ block_threshold : Nat, ∀ block ≥ block_threshold,
      ∀ code : CapabilityResponseBlockCode G s δ block,
        rate ≤ (Nat.log2 (Fintype.card code.Message) : ℚ) / block →
          ¬ code.ZeroError
```

This is the deterministic Pigeonhole converse: a binary-output channel of length `block` admits at most `2^block` distinct output words, so any code with `M > 2^block` messages must have two messages mapping to the same output word, contradicting `ZeroError`. The arithmetic is the private lemma `output_words_lt_card_of_log_rate`, which converts the log-rate hypothesis into `2^block < M` via the bound `Nat.log2 M < block + 1`.

##### 4.2 The binary-rate converse and `C*` response binding

**Theorem 4.2** (Governance capacity threshold package, `governance_capacity_threshold_C_star_binding` in `Legitimacy.Spectral.Capacity.CapacityConverse`).
*For `δ > 0` and `cv(G,s) > 0`, the package records three facts: the binary-output log-rate converse applies above the rate threshold `binaryDecisionPerUseRate = 1`; for every positive capability `C`, the concrete response satisfies `capabilityResponse = Permit ↔ C_star G s δ ≤ C`; and the same response characterization descends to the `cv`-quotient class.*

For the Claude Agent SDK gate, the reviewer uses this package to bind the permission graph's structural threshold to the observed permit transition in the channel abstraction.

This theorem does not identify rate values with capability levels. It packages the rate-side counting converse with the capability-side threshold transition and its quotient form. The proof descends to the `C_starClass` quotient via `C_starClass_mk` and the `cvValueClass` Setoid.

##### 4.3 The headline alignment threshold theorem

**Theorem 4.3** (Governance capacity alignment threshold). The headline capacity theorem gives a failed-deployment witness above the graph's critical threshold under the stated channel embedding.[^04-anchor-1]
*Let `G : GovGraph ℚ n` with `[NeZero n]`, `s : Fin n → ℚ`, `δ > 0`, `cv(G,s) > 0`, and let `protocol : AlignmentProtocol G s δ`. If `C_star G s δ ≤ protocol.target_capability`, every embedded coordinate is also bounded below by `protocol.target_capability`, and the protocol's message family has any positive log-rate lower bound, then there is a block threshold such that every block at or above it contains some message whose deployment claim is false.*

For the Claude Agent SDK gate, the audit move is to locate the uncertified tool-use message once a represented verifier claims target-saturating certification above `C*`.

This is the paper's headline ceiling: past the graph's critical capability `C*`, the channel can no longer certify everything it is handed. Once the target capability clears `C*`, the target-floor and target-ceiling hypotheses force every used coordinate to equal the target capability, so the channel output is constant `Permit` (`capabilityResponse_eq_permit_iff_C_star_le`); a positive-rate message family carries more than one message, so they cannot all decode through that single output, and at least one deployment claim must be false. The converse is structural, about the channel and these formal embedding obligations, not about any specific behavioral lineage.

The separate approved-revision safety-envelope bridge should be read with the
same conditional discipline: it proves no silent unsafe permit once a failed
property is identified, not that every deny-to-permit revision is unsafe.

The companion theorem `governance_capacity_alignment_log_rate_converse` is the protocol-level rate converse without a `C*` hypothesis: if an encode-injective protocol claims log-rate strictly above one binary decision per use, some message fails deployment at every sufficiently large positive block.

##### 4.4 Achievability witness and tightness

The converse is tight at the per-use rate boundary. A matching binary block-code witness saturates the one-decision-per-use boundary.[^04-anchor-3] It uses threshold coordinates for `Permit` and subcritical half-threshold coordinates for `Deny`; under positive `δ` and positive `cv`, it is binary, zero-error, and achieves the per-use rate.

A concrete refutation of the *raw* (non-log) cardinality form of the converse is given by `raw_cardinality_rate_padding_counterexample` in `Legitimacy.Spectral.Capacity.CapacityConverse` on the bottleneck fixture (`bottleneckGraph`, `sig`, `δ = 1/10`): the zero-error binary block code at block length `4` has `16` messages, so its raw `card / block` rate exceeds the naive binary-output threshold even though its log-rate is exactly the boundary. This rules out a tempting but false stronger claim and clarifies that the converse must be stated in log-rate form, not raw-cardinality form.

##### 4.5 Derived noisy-channel capacity equalities

This subsection derives the noisy-channel capacities that calibrate `C*`, both the binary-erasure and the binary-symmetric forms, from the channel kernel itself rather than asserting them as external constants.

`Legitimacy.Spectral.Channels.ConcreteNoisyChannel` constructs the binary erasure channel `asErasureDecisionChannel ρ hρ`, which reveals the binary decision with probability `ρ` and returns erasure otherwise. The equality

> `erasure_channelCapacity_eq` in `Legitimacy.Spectral.Channels.ConcreteNoisyChannel`

proves the concrete Shannon capacity is `ρ * log 2`, derived from the kernel rather than asserted as an external rational certificate. The graph-calibrated bridge then isolates the erasure-kernel channel equality from the graph-specific statement that the constructed capacity equals `(G.cv s : ℝ)`, and from that calibration produces the exact certificate consumed by the generic finite-capacity threshold theorem.[^lean-gx-04s5-1]

The canonical-graph fixture family is now inhabited under this erasure-channel construction using half-scale signals: the original uniform-triangle inhabitant plus four scaled canonical-graph × half-scale-signal pairs, with a parametric constructor that builds the reveal probability as `(G.cv s : ℝ) / log 2` for any graph/signal pair whose `cv` lies in `0 < cv < log 2`.[^lean-gx-04s5-2]

The binary symmetric noisy-threshold channel now has its own closed form in `lean/Legitimacy/Spectral/Channels/NoisyThresholdClosedForm.lean`. The theorem

> `channelCapacity_asNoisyThresholdChannel_eq_log_two_sub_binEntropy`

proves

```
ChannelCapacity.channelCapacity (asNoisyThresholdChannel η hη).kernel
  = Real.log 2 - Real.binEntropy (η : ℝ)
```

in nats, matching the imported `ChannelCapacity` units. The proof computes row entropy as `Real.binEntropy η`, shows the uniform binary prior produces uniform output entropy `log 2`, and uses the binary entropy upper bound to prove the uniform prior maximizes mutual information. The companion theorem `channelCapacity_asNoisyThresholdChannel_bits` states the bits-normalized form:

```
ChannelCapacity.channelCapacity (asNoisyThresholdChannel η hη).kernel / Real.log 2
  = 1 - Real.binEntropy (η : ℝ) / Real.log 2
```

This is the standalone binary-symmetric-channel (BSC) capacity `log 2 - H₂(η)`, where `H₂` is the binary entropy and `η` the bit-flip probability (in nats; `1 - H₂(η)` in bits), proved from the kernel and orthogonal to the graph-side `C*`: it is a Shannon-information-theoretic object on its own footing, and the §8 negative bridge records precisely that it does not coincide with `C*` across distinct graphs.

The BSC calibration surface mirrors the erasure surface: a calibration structure packages a noise value `η < 1/2` with the derived equality `log 2 - Real.binEntropy η = (G.cv s : ℝ)`, the graph-calibrated channel capacity descends from the closed-form theorem, and a constructor uses continuity of `Real.binEntropy` and the intermediate value theorem to inhabit every graph/signal pair with `0 < cv < log 2`, with a concrete half-scale uniform-triangle inhabitant.[^lean-gx-04s5-3]

At the binary-channel substrate, the BSC capacity is given in closed form, and the noisy-threshold capacity by a derived real theorem rather than a generic certificate. The scope boundary is not a missing Mathlib entropy lemma: binary channels in nats still have maximum capacity `log 2`, so canonical-signal pairs with `cv ≥ 1` remain outside this binary-channel reachable range unless the downstream comparison is reparameterized in bits or a higher-capacity channel family is introduced.

##### 4.6 Cross-lineage positive procedure

This subsection records the below-threshold positive result: when a Constitutional-AI harm partition, a Stackelberg adversary, and an AI-Control monitor budget are all compatible with one calibrated kernel, every capability below `C*` extracts a positive-procedure certificate at one audited scale.

The cross-lineage theorem lives in `lean/Legitimacy/Behavioral/ComposedLineage.lean` because it composes the behavioral lineage scaffold with the capacity extractor:

> `composedLineage_positiveProcedure_classification`

For any `ComposedLineage`, if the CAI harm partition, Stackelberg capability adversary, and AI-Control monitor budget are compatible with the same calibrated kernel, then every positive `c ≤ kernel.C_star` extracts a `PositiveProcedureCertificate` whose kind is `consistency` or `monotonicity`, whose CAI substrate verdict is `admissible`, whose scale is covered by the AI-Control monitor budget, and whose benign CAI policy boundary is available at that covered scale.

The compatibility records are intentionally stronger than "there exists a CAI object, a Stackelberg object, and a monitor object." `CAIHarmPartitionCompatible` proves that the kernel is the CAI graph/signal/tolerance and that benign policy decisions match the kernel boundary. `StackelbergCapabilityCompatible` proves that the adversary is on that same graph/signal, that its perturbations are bounded by kernel `cv`, and that its `C*` is the kernel `C*`. `AIControlMonitorCompatible` then proves that the monitor budget covers the Stackelberg boundary and remains bounded by the kernel boundary. The current proof consumes CAI boundary compatibility, Stackelberg `C*` equality, and the two monitor-budget inequalities; it does not claim that every field in the compatibility records is used. The strengthened conclusion is the new content: certificate classification, CAI substrate admissibility, monitor coverage, and the benign-boundary clause are returned together at the same audited scale.

Constitution-as-DAG strengthening. The CAI side is no longer just a flat harm/benign partition: the substrate defines finite principle objects and a constitution whose conflict relation is a partial order with a resolution map and a quotient of audited claims by resolved principle, with the old harm/benign surface recovered as the two-principle special case (benign principle below the harm-categorical principle). The deployment theorem states the strengthened CAI claim: if a policy's binary decision agrees with the resolved principle and the audit kernel is well-conditioned, then every positive `c ≤ C*` produces an admissible substrate verdict. A three-principle worked instance separates a respecting policy from a permissive non-respecting policy at the substrate-verdict level and gives the profile-sensitivity floor beyond the vacuous one-principle constitution.[^lean-gx-04s6-1]

This is the formal Constitution-as-DAG substrate; mapping Anthropic's published public constitution into the principle/conflict-resolution object, and auditing the fit between prose principles, resolution edges, and deployed verdict behavior, is a separate case study.

The concrete inhabitant is `composedLineage5_positiveProcedure_classification`. It uses `uniK5`, the half-scale signal `uniK5HalfSig`, tolerance `1/10`, the existing exact erasure-channel calibration, a CAI harm/benign partition over five states, a Stackelberg node-removal adversary over the same graph/signal, and an AI-Control monitor budget pinned to `4/15 = C*`. The use of `uniK5HalfSig` is the same binary-channel capacity restriction described above: the canonical `sig5` CV is outside the current binary-channel nats ceiling, while the half-scale signal has an exact finite-channel calibration.

A negative bridge rules out identifying one fixed scalar noisy-channel capacity with all concrete C* values.[^04-anchor-8] This is a separate result; we cite it here to mark the boundary: the deterministic `C*` threshold is a distinct object from a fixed scalar noisy-channel Shannon capacity, and replacing one with the other would require an additional graph-dependent construction.

The noisy positive-procedure generalization is now formalized. The exact finite-channel case remains asymmetric: strict-subcritical downward persistence is structurally derivable from consistency, so exact certificates return only `consistency` or `monotonicity`. In the noisy substrate, the kernel carries profile-indexed verdict distributions, the well-conditioned predicate requires genuine probabilistic verdict mass plus profile sensitivity, and the constructive theorem returns a noisy certificate whose strict-subcritical branch selects `solidarity` with a quantitative total-variation drift rate. The distinction is formal rather than nominal: a profile-sensitive probabilistic counterexample has single-scale consistency data with no finite downward-persistence rate, and the worked BSC-calibrated instance has a `solidarity` certificate at `c = 1/10` with computed verdict drift from `1/20` to `1/10`.[^lean-gx-04s6-2]

##### 4.7 Positive procedure below `C*`

The forcing side of the substrate is negative: once the target-saturating capability-response channel clears `C*`, the zero-error converse forces a failed deployment message for positive-rate families under the stated embedding obligations. The complementary monitorability bound is constructive: for a kernel in the exact well-conditioned class, the evaluator does not need to run a parallel diagnostic pipeline to know whether the verdict has silently degraded below the threshold.

The Lean surface is:

- `CapacityKernel`: graph, signal, tolerance, and finite governance channel.
- `WellConditionedForCapacity`: positive tolerance, positive `cv`, and an exact finite-channel capacity certificate calibrated to `cv`.
- `governance_certificate`: the extractor for positive `c ≤ C*`.
- `strictSubcritical_downward_persistence`: the exact-case theorem showing that downward denial and no-violation persistence hold at every strict subcritical scale, not only near the boundary.
- `governance_certificate_constructible`: the theorem that the exact-case extractor returns consistency throughout the strict subcritical interval (`0 < c < C*`) and monotonicity at the boundary (`c = C*`).
- `PositiveProcedureCertificate.GraphConsistencySpectralReflection`, the profile-uniform semantic hypothesis surface: if every all-profile binary consistency counterexample reflects into a fixed-profile spectral violation at some covered positive scale, the certificate can be read as graph consistency.

At exact well-conditioned finite-channel kernels, downward persistence holds throughout the strict subcritical interval, so the exact extractor returns only consistency and monotonicity. The `PositiveProcedureCertificate.GraphConsistencySpectralReflection` structure is an API split for the consistency carrier, not a formal closure of the graph-consistency reflection connector: `kind_consistency_to_GraphConsistency` consumes a supplied profile-uniform reflection and the certificate's lower-scale no-violation field, but the current substrate does not derive that reflection from a kernel/graph pair. The remaining connector theorem has signature shape: fixed-profile spectral kernel data (`K.G`, `K.s`, `K.δ`, positive `C ≤ c`) plus a binary graph/profile interpretation should imply that every all-profile `GraphConsistency` counterexample for `GovernanceGraph` emits `K.G.spViolation K.s (K.δ / C')` for some positive `C' ≤ c`. Boundary monotonicity still uses `PositiveProcedureCertificate.GraphDiagnosticCarrier`, because that side has a different semantic obligation: interpreting the `C*` permit transition as binary graph monotonicity. The independent operational distinction for solidarity remains reserved for the noisy/probabilistic positive-procedure generalization.

The module is no longer a leaf export: `lean/Legitimacy/Results/PositiveProcedure.lean` imports the certificate module and proves `positiveProcedure_graphDiagnostic_classification`, composing `governance_certificate_constructible` with the profile-uniform consistency reflection and the boundary graph carrier to produce a downstream graph-diagnostic classification.

Evaluator plug-in. An evaluator supplies a governance graph `G`, signal `s`, tolerance `δ`, and channel calibration evidence showing that the finite channel capacity is exactly calibrated to `G.cv s`. From those inputs the evaluator builds `K : CapacityKernel`, instantiates `WellConditionedForCapacity K`, supplies a positive target scale proof `0 < c` plus a threshold proof `c ≤ K.C_star`, invokes `governance_certificate K hK c hcpos hc`, and reads `cert.kind`. Operationally, the exact-case output says which structural positive-procedure property is preserved at that scale and which decision is rendered: consistency gives strict-subcritical `Deny + ¬spViolation` with downward persistence to all smaller positive scales, and monotonicity gives boundary `Permit` with upward persistence to all larger scales. The `¬spViolation` clause certifies that the evaluator's input perturbation regime is still above the graph's violation threshold, not that arbitrary noisy deployment behavior has been audited.

The evaluator scope boundary is exact. Real evaluation harnesses that do not have graph-calibrated finite channels, or that need noisy/probabilistic kernel degradation rather than the exact deterministic threshold readout, still require the noisy positive-procedure generalization. What the evaluator gets today is the well-conditioned exact case: when calibration data is available, the structural certificate is mechanically read from the threshold proof; when calibration data is absent, this theorem does not manufacture it.

Two worked instances pin the exact case down. For the half-scale uniform triangle, `C* = 1/5` at `δ = 1/10`. Both strict-subcritical certificates, at `c = 1/10` and `c = 19/100`, read as consistency and prove the concrete `Deny` plus no-violation facts.[^lean-gx-04s7-1] The no-violation proof consumes the strict `c < C*` theorem, so the previous narrower margin computation is not load-bearing in this exact substrate and is not cited.

`WellConditionedForCapacity` assumes no downstream governance verdict, not consistency, solidarity, or monotonicity, and supplies exactly the threshold ingredients the proof consumes. Generalizing the extractor beyond exact finite-channel calibration, to noisy verdict degradation for non-exact kernels, is the noisy positive-procedure generalization above.

##### 4.8 Spectral substrate of `C*`

The spectral side gives `C*` structural teeth via:

- `GovGraph.cv_spectral_bound` in `Legitimacy.Spectral.Capacity.CriticalCapability`: `cv` is bounded above by the smallest singular-value-style spectral quantity on the graph.
- `C_star_spectral_bound` in `Legitimacy.Spectral.Capacity.CriticalCapability`: `C*` is bounded below by `δ` divided by that spectral upper bound on `cv`.
- `governance_graph_C_star_expander_bound` in `Legitimacy.Spectral.Capacity.CriticalCapability`: under explicit expander-class premises — positive minimum removed degree, positive spectral gap `λ₂`, and every vertex degree at least `λ₂` — `C*` is bounded below by `δ · λ₂ / (signalRange(s) · maxDeg)`.

Together these do more than define `C*` under the theorem's positive-`cv` hypothesis: they make it computable from the graph's spectral data. The spectral lower bound on `C*` is standalone graph mathematics: it ties the certification threshold to the graph's own spectral gap, independent of any channel-capacity or impossibility statement. The expander bound and the concrete fixtures witness non-vacuity for graph classes where `cv > 0`, hence finite `C*`, hence an actual ceiling on the stated zero-error certification problem.

##### 4.9 Continuous operator substrate

The continuous substrate now defines `cvOp` in `lean/Legitimacy/Spectral/ASIEmbedding/ContinuousOperatorSignature.lean` as the operator norm left after projecting away the stationary line: `1 - ‖T ∘ P_(span{v_top}ᗮ)‖`. The strengthened `OperatorSpectralGapPredicate` includes the nonstationary `v_gap` witness, excludes an orthogonal top-eigenvector, and adds the absolute non-top spectral bound needed for an operator-norm theorem. The bridge `cvOp_eq_gap_of_operatorSpectralGapPredicate` applies the compact self-adjoint op-norm eigenvector theorem to `T ∘ P`, uses the absolute bound for the upper estimate, and uses `v_gap` for the lower estimate. The identity floor theorem `cvOp_boolIdentityContinuousSignature_eq_zero` records why a positive bundled gap parameter is not enough: the identity operator still has genuine `cvOp = 0`.

The Bool counting kernel is the finite rank-2 specialization in the signed regime `0 < g < 1`: `cvOp_twoStateCountingKernelContinuousSignature_eq` computes `cvOp = 2g/(1+g)`, and `boolCountingKernel_measureTheoretic_to_continuousOperator_cv` in `CompactSpectralBridge.lean` proves that this agrees with the existing finite Bool counting-kernel `operatorSpectralGap`. The `g < 1` hypothesis is load-bearing: it is exactly the sign condition under which the nontrivial eigenvalue `(1-g)/(1+g)` is nonnegative, so the absolute operator norm on the orthogonal complement matches the right-edge finite gap formula.

The rank-`N` truncated Ornstein-Uhlenbeck instance `ouTruncatedSignature` now populates the same continuous-operator structure on `EuclideanSpace ℝ (Fin N)` with a finite diagonal whose entries `(exp (-n * t))_{n<N}` numerically match the rank-`N` truncation of the Ornstein-Uhlenbeck spectral ladder. Its stationary vector is the `n = 0` coordinate, its first nonstationary witness is the `n = 1` coordinate, and `operatorSpectralGapPredicate_ouTruncatedSignature` proves the right-edge and absolute nonstationary spectral bounds directly from the diagonal spectrum. The bridge `cvOp_ouTruncatedSignature_eq` specializes the stage-3 operator-norm definition to the corresponding finite diagonal gap formula `1 - exp (-t)`.

This is the finite-dimensional operator truncation of the OU/Mehler spectral ladder, not the full `L²(ℝ, Gaussian)` Mehler integral-operator theorem. The latter still requires Hermite basis formalization, the Gaussian reference space, the Mehler kernel as an integral operator, and compactness/kernel-class arguments; that work remains a continuous-operator substrate generalization. The rank-2 comparison theorem records that the Bool counting kernel and OU truncation have matching `cvOp` values whenever their parameters are related by the same gap value; the existing Bool surface keeps a rational parameter, while the OU substitution is naturally real-valued.

---

### 4.2 Proof sketch

We sketch the proof at the semantic level; the formal proof is in `Spectral/CapacityConverse.lean`.

##### Step 1: Pigeonhole on binary output words.

A binary-output channel of length `block` has at most `2^block` distinct output words. A zero-error code requires injectivity of `output : Message → Output^block`. By `output_injective_of_zeroError`, `M ≤ 2^block`.

##### Step 2: Log-rate translation.

If a code has rate `rate ≤ (log₂ M) / block` with `rate > binaryDecisionPerUseRate = 1`, then `block < log₂ M` over ℚ. Casting back to ℕ, `block < Nat.log2 M`. The arithmetic is straightforward but care is needed because `Nat.log2` is rounded down; we use `Nat.log2_lt` (Mathlib) which gives `Nat.log2 M < block + 1` iff `M < 2^(block+1)`. Combining with the Pigeonhole bound `M ≤ 2^block` produces a contradiction with the `block < Nat.log2 M` direction.

##### Step 3: Channel-embedding step.

For any alignment protocol that factors through the capability-response channel `cap`, the channel-output is determined by `cap(c) = if 0 < c ∧ C* ≤ c then Permit else Deny`. Under the headline theorem's target-floor hypothesis, clearing `C*` makes every used coordinate a positive capability at or above `C*`, so every output letter is `Permit` (`capabilityResponse_eq_permit_iff_C_star_le`). If all deployment claims were true, decoding through that single output word would force all encoded messages to coincide; encode-injectivity would then force all protocol messages to coincide. The positive-rate hypothesis gives more than one message, yielding the failed-deployment witness.

##### Step 4: Tightness witness.

The binary block code `capabilityResponseBinaryBlockCode` is constructed explicitly using `C_star` coordinates for `Permit` and `C_star / 2` coordinates for `Deny`. Its `output` map is injective by construction (`capabilityResponseBinaryBlockCode_zeroError`). Its message cardinality is `2^block` (`capabilityResponseBinaryBlockCode_message_card`), saturating the Pigeonhole bound. Its log₂ message cardinality is exactly `block` (`capabilityResponseBinaryBlockCode_log2_message_card`), giving per-use rate `1 = binaryDecisionPerUseRate`.

##### Step 5: Quotient-invariance.

`cv` is a Setoid-quotient invariant: graphs in the same `CvEquivalent` class share the same `C*`. This means the converse is a property of the equivalence class `cvClass G s`, not of any particular representative. The bridge `capabilityResponseClass_eq_permit_iff_C_starClass_le` in `Legitimacy.Spectral.Channels.CStarChannelBridge` lifts the threshold result to the quotient.

The full Lean proof for `governance_capacity_alignment_threshold` chains these obligations rather than defining a standalone sustainable-rate object. The modular structure means the counting side can be reused for variant channel constructions, while per-protocol embeddings must still supply their own target-use and decoding obligations.

---

### 4.3 Discussion: implications for verification architectures

**The reframe**. The capacity-converse moves the alignment-threshold question from training-time (what signal makes the model aligned?) to verifier-time (what governance graph has the capacity to certify alignment?). Verification protocols inherit the resulting structural ceiling once they satisfy the paper's channel-embedding and target-use hypotheses — a reframing of the threshold, not a refutation of behavioral alignment work.

**Constitutional principle layers**. Principle-conflict-resolution layers and chain-of-thought monitorability surfaces are candidate channels for embedding analysis. If a principle-conflict layer factors through `cap` and supplies the target-use hypotheses, then above `C*` of the encoded constitution-as-graph, a positive-rate zero-error constitutional verifier cannot certify every message. The follow-up work is the formal embedding (future work: `ConstitutionalAIPolicy → AuthorityGraph`).

**Monitorability**. Empirical sleeper-agent demonstrations are instances of systems whose certified behavior can diverge from deployed behavior. The structural ceiling says: above the governance graph's `C*`, a verifier of the formal target-saturating channel shape must leave some positive-rate message uncertified. This is the verification-architecture complement to the empirical detection problem.

**Deliberative verifiers**. A deliberation step factors through a capability-response channel iff the deliberation produces a binary admit/deny verdict on alignment claims. The converse applies to that deterministic embedding. Where deliberation is probabilistic, the deterministic converse does not directly apply; the obvious extension is a noisy-channel converse, which we leave as open follow-up work (and which the negative bridge `fixed_noisyThreshold_capacity_not_concrete_C_star_bridge` shows cannot be obtained by equating one fixed scalar noisy-channel capacity with all graph-varying concrete `C*` values).

**Extractor architectures**. The capacity-converse is the structural side of an ELK-shaped problem. If an extractor is formalized as a target-saturating verifier over the capability-response channel, then above `C*` the theorem supplies a failed-deployment message. The five-certificate vocabulary of `Kernelization.lean` is candidate witness language; pairing it with the converse is capacity-ELK follow-up work, not a result of this paper.

**Verifier-target safety cases**. The converse is the structural cap on verifier-target instances that embed into the target-saturating channel. The legitimacy kernel as concrete verifier-target (`Bridges/GuaranteedSafeAIBridge.lean`, `legitimacy_substrate_is_static_gs_ai_snapshot_instance`) is a candidate for this analysis once the channel embedding is supplied. Such deterministic verifier architectures accept this structural ceiling when they instantiate the required channel shape — a structural cap, not a critique.

**Control-protocol embeddings**. Each control protocol defines its own channel embedding. Whether the converse applies depends on whether the protocol's certification step factors through `cap`. The structural audit of the five protocol shapes on the audit-graph layer is a separate result; the per-protocol channel embedding is open follow-up.

The scope qualifier across all of these: the converse is for *deterministic* alignment protocols *embedded into the capability-response channel*. Probabilistic protocols, list-decoding protocols, and protocols that bypass the channel are out of scope. The result is narrow. Narrow results that survive adversarial review are the basis for compounded follow-up; broad results that bundle behavioral lineages without per-lineage embedding are the failure mode.

---


### 4.4 Capacity summary

We prove a Shannon-style zero-error converse for alignment verification on a structural object: the governance graph's capability-response channel admits no zero-error block code at log-rate strictly above one binary decision per channel use, and, for `δ > 0` and `cv(G,s) > 0`, a deterministic target-saturating `AlignmentProtocol` whose positive-log-rate message family is embedded through that channel with the target-floor obligations has a failed deployment message in every sufficiently large block once its target capability is at or above `C*(G, s, δ) = δ / cv(G, s)`. The threshold is structural, computable from the graph's spectral vulnerability, and the converse is mechanically verified in Lean 4 over rational arithmetic.

The result reframes the alignment threshold question. Above the structurally-determined capability threshold of the governance graph in use, deterministic target-saturating positive-log-rate `AlignmentProtocol` families embedded through the capability-response channel with the target-floor obligations have some failed deployment message rather than all-message zero-error certification. Behavioral alignment lineages (RLHF, CAI, debate, deliberative alignment, CoT monitorability, AI Control) inherit the ceiling iff they embed into the channel and satisfy the target-use obligations, conditions we name explicitly and leave per-lineage formalization as open follow-up.

The finite zero-error analogue is precise, narrow, and tight at the per-use rate boundary. We claim no more than this. The compounded follow-ups — capacity-ELK forcing, structural monitorability vs CoT, per-lineage embedding (RLHF, CAI, debate, etc.), and the noisy-channel converse — are research-frontier work for which this converse is the structural foundation.

## 5. Stackelberg Stability Ceiling

The Stackelberg ceiling answers the second question on the same represented graph: what remains stable as the modeled capability scale grows? The section uses the fixed-graph spectral surrogate from §2 and characterizes unbounded stability by zero consistency vulnerability. For the Claude Agent SDK gate, the audit move is to test whether removal vulnerability in the represented permission graph creates a finite stability cliff.

A word on vocabulary before the theorems. "Stackelberg" and "equilibrium" name objects in the spectral surrogate: a stable equilibrium at capability `κ` is the threshold inequality `cv < δ/κ` holding, and the asymptotic limit is exact arithmetic over that inequality; the limit theorem itself encodes no repeated game. The game-theoretic reading is constructed rather than assumed, and it extends exactly as far as the constructions: the behavioral-realization block in §5.1 extracts a deterministic game from `(G, s)` whose embedding fields are theorems rather than bundled hypotheses, and the lineage modules — Constitutional AI, AI Control, debate, RLHF — supply typed audit-subject realizations under their stated embeddings. "Strategyproof" is reserved in this program for the misreport predicate of the impossibility companion, the Gibbard-Satterthwaite sense [Gibbard1973][Satterthwaite1975]; the spectral condition this section characterizes is named what it is, zero consistency vulnerability.




### 5.1 Main results

##### 5.1 The asymptotic Stackelberg limit

> **Theorem 5.1** (Asymptotic Stackelberg limit). The asymptotic Stackelberg theorem characterizes unbounded spectral stability by zero consistency vulnerability.[^04-anchor-4]
> *Let `G : GovGraph ℚ n` with `[NeZero n]`, `s : Fin n → ℚ`, `δ > 0`. The mechanism has arbitrarily large spectral stable equilibria iff its consistency vulnerability is zero:*
>
> ```
> HasArbitrarilyLargeStableEquilibria G s δ ↔ ZeroConsistencyVulnerability G s
> ```

> In the Claude Agent SDK reading, a represented permission graph retains spectral stable equilibria at every modeled capability scale exactly when its modeled consistency vulnerability is zero.

The biconditional combines the finite-cliff contrapositive with the zero-CV persistence theorem: positive consistency vulnerability -> finite cliff -> not unbounded spectral stability, while zero consistency vulnerability -> unbounded spectral stability.

The result is the section's headline, and it is exact in three senses: structural (a property of the graph's spectral data, not of any particular capability), asymptotic (about the limit, not finite scales), and an iff rather than an implication. The space of asymptotically stable mechanisms in the spectral surrogate is exactly the zero-consistency-vulnerability subspace.

**Worked instance: a real harness stability cliff.** The asymptotic limit adjudicates a real extracted harness, not only synthetic carriers. The OpenAI Codex hooks governance graph, extracted from committed source and audited for a monotonicity failure in the companion structural-audit manuscript (`codexHooksGovernanceAdmissibilityRejectsMonotonicity`), is represented by the derived spectral carrier `codexHarnessDerivedSpectralGraph` and derived signal `codexHarnessDerivedFailureSignal`, with consistency vulnerability `cv = 1` (`codexHarnessDerived_cv_value`) and `C* = 1/10` (`codexHarnessDerived_C_star_value`). The derived carrier keeps all eight extracted pass-through pairs and is disconnected: eight `K₂` components, so `λ₂ = 0`. The cliff theorem used here is connectivity-free; it consumes positive CV, not a positive spectral gap. By the asymptotic limit, positive consistency vulnerability forces eventual loss of spectral stability under capability scaling (`codexHarnessDerived_stage2_stackelberg_eventual_instability`): the represented Codex harness governance has a finite stability cliff as the modeled capability grows. The same case study makes the repair explicit: the repaired graph-derived carrier has zero CV via the adjudication chain (`codexHarness_repaired_cv_value`), restoring unbounded spectral stability. This is a machine-checked path from extracted source to a capability-scaling governance verdict on a frontier-lab harness; it is a verdict on the represented graph model of the harness, not a behavioral claim about live Codex.

The repaired carrier should be read against the impossibility companion's layer separation, not as a free win. Driving consistency vulnerability to zero does not place the harness on the favorable side of that paper's escape taxonomy: the repair removes no peer-relative stage; it adds one, the explicit adjudication node. What the repair instantiates, deliberately, is the separation witness: a system that passes the runtime kernel and graph diagnostics while its spectral surface carries zero signal. The trade is explicit. Before repair, the threshold surface hosts the contested decision and pays for it with `cv = 1`, a finite `C* = 1/10`, and a stability cliff; after repair, the contested decision is resolved by downstream adjudication and the threshold surface carries no signal; stability at every capability is restored because nothing on that surface remains to contest, not because certification capacity became infinite. This is the declared sacrifice the program demands: the repair purchases unbounded spectral stability by resolving the contested allocation out of the certified spectral surface rather than hiding it inside it, and the adjudication node is where audit attention must now move.

The repair's direction also deserves confrontation, because its surface reading is uncomfortable: the adjudicated gate converts threshold escalation verdicts to permit, and a hostile reader will summarize the recommendation as "stop escalating to review." That reading mistakes a re-typing for a loosening. The extraction types every registration-count threshold as a terminal escalation verdict, a modeling convention over registration metadata, not a reviewed policy choice, and the repair re-types exactly those: their verdicts become adjudicated evidence feeding an explicit downstream adjudication node, while every content-match and exact-match deny route is untouched. The conversion is a substantive governance change, and it is declared as one: what was an implicit terminal verdict on metadata becomes a named, auditable adjudication, so the delta is owned by an accountable node rather than smuggled through a threshold's type.

##### 5.2 The adversarial Stackelberg companion

The adversarial companion makes the scaling hypotheses explicit. `AdversarialCapabilityScaling` is a monotone rational-to-rational capability trajectory, and `Cofinal scaling` is a separate unboundedness hypothesis: the trajectory eventually clears every rational capability floor. The theorem is about cofinal monotone adversarial capability scalings inside the spectral surrogate, not arbitrary non-monotone or bounded capability paths:

> **Theorem 5.2** (Adversarial eventual collapse iff positive consistency vulnerability). The cofinal monotone adversarial collapse characterization holds inside the spectral surrogate.[^04-anchor-6]
> *Let `G : GovGraph ℚ n` with `[NeZero n]`, `s : Fin n → ℚ`, `δ > 0`. For cofinal monotone adversarial capability scalings, positive-consistency-vulnerability graphs eventually lose spectral stability along every such scaling; equivalently `AdversarialEventuallyNoStable G s δ ↔ ¬ ZeroConsistencyVulnerability G s`. The negation form characterizes zero consistency vulnerability.*

For the Claude Agent SDK gate, the reviewer uses this theorem to test stability against adversarially chosen tool-use pressure paths that satisfy both formal scaling hypotheses: monotonicity and cofinality.

The supporting theorems are `adversarial_stackelberg_unbounded_of_positive_consistency_vulnerability`, `positive_consistency_vulnerability_of_adversarial_stackelberg_unbounded`, and the eventual-collapse iff `adversarial_stackelberg_eventual_collapse_iff_positive_consistency_vulnerability`; "collapse" here means failure of the spectral no-violation predicate, not behavioral collapse.

The `AdversarialCapabilityScaling` structure includes monotone examples and combinators such as `identity`, `constant`, `affine`, and `comp` in `Legitimacy.Spectral.Dynamics.AdversarialStackelberg`. Cofinality is not automatic: `constant` is monotone but generally not cofinal. The theorem says that for every cofinal monotone scaling, positive-CV mechanisms eventually lose spectral stability, while zero-CV mechanisms refute that eventual-collapse property.

##### 5.3 Load-bearing hypothesis witnesses

Two concrete fixtures show why the adversarial theorem's hypotheses are load-bearing:

- `subcriticalConstantScaling` in `Legitimacy.Spectral.Dynamics.AdversarialStackelberg`: a monotone but bounded subcritical scaling under which the positive-CV fixture remains stable forever, showing that monotonicity without cofinality is insufficient.
- `nonmonotoneSubcriticalTail` in `Legitimacy.Spectral.Dynamics.AdversarialStackelberg`: a raw non-monotone subcritical-tail function that refutes eventual collapse once the structural scaling hypotheses are dropped.

These are counterexamples for dropped hypotheses, not constructive cliff witnesses. They delimit the theorem: bounded or non-monotone capability paths are not covered by the cofinal-monotone adversarial collapse theorem.

##### 5.4 The game behind the surrogate: a concrete behavioral realization

The spectral Stackelberg convergence theorem remains purely spectral. A separate Lean module now gives one concrete behavioral realization: `Legitimacy.Behavioral.StackelbergLineage` defines `StackelbergBehavioralLineage`, extracting a deterministic rational game from `(G, s)` where agents are nodes, states are observer/target nodes, and actions are bounded-amplitude node-removal perturbations. The action budget for remover `k` at observer `i` is exactly:

```
|G.gov s i - G.govRemoved s k i|
```

The game utility pays the selected executable amplitude only when the target matches the current state, and the governance decision permits exactly positive executable perturbations at that state. It is the node-removal perturbation lineage corresponding to the already-existing `govRemoved` witness, scoped to that class rather than to generic Stackelberg behavior.

For this lineage, the four `SpectralBehavioralEmbedding` fields are derived as theorems rather than bundled as assumptions:

- `perturbation_budget_reflects_best_response_gain`: every profitable behavioral gain is bounded by the deviated action's executable node-removal budget and therefore witnesses `spViolation`.
- `graph_decision_matches_game`: thresholded game decision flips reuse the same gain-scale spectral witness.
- `spectral_vulnerability_exposes_profitable_deviation`: any positive spectral vulnerability yields a concrete profitable deviation by choosing that executable amplitude.
- `spectral_threshold_violation_exposes_profitable_deviation`: a threshold violation yields a capability-feasible deviation by taking amplitude `min (δ / κ) κ`.

The module also constructs the actual embedding value `spectralBehavioralEmbedding` and composes it with the existing zero-CV and persistence iff theorems. The decomposed best-response regularity certificate is intentionally scoped: for this bounded-amplitude lineage it is supplied in the zero-CV case, where profitable deviations are absent and witness extraction is vacuous. A general `BestResponseDecomposedRegularity` instance for positive-CV bounded amplitudes is not asserted, because arbitrary positive tolerance floors can exceed every executable perturbation budget.

This closes the "bundled-as-discharge" gap for the Stackelberg node-removal perturbation lineage class only. It does not generalize to arbitrary Stackelberg behavior, debate protocols, Constitutional AI, deliberative alignment, AI Control, or unbounded-capability kernel behavior without separate extraction and proof.

##### 5.5 General-`n` spectral scaling of the complete carrier

The finite `n=5/7/9` evaluations elsewhere in this paper are checkpoints, not the strongest spectral statement available. The complete-carrier spectral results are *parametric in `n`*: they hold for every successor size, not for a fixed table of sizes. The spectral gap here is the separation between the carrier's leading eigenvalue and the rest of its spectrum, the standard graph-connectivity measure, larger meaning better-connected.

**Theorem 5.3** (Closed-form complete-carrier spectral gap). The spectral gap of the unit-weight complete governance carrier on `n+1` vertices is exactly `n+1`, for arbitrary `n`.[^04-anchor-12]
*For the generic complete carrier `asiCompleteGraph n` (the family name in the Lean substrate; the prefix records the unbounded-capability reading, the object is the unit-weight complete graph) and any `n` with `2 ≤ n+1`,*

```
(asiCompleteGraph n).spectralGap hn = (n + 1 : ℝ)
```

This is a single arbitrary-`n` theorem (`asiCompleteGraph_spectralGap_eq`), proved by reducing the eigenvalue count of the carrier's Laplacian to the closed gap value `n+1`. The five-, seven-, and nine-node complete carriers are equal to the corresponding `asiCompleteGraph` instances, and the spectral-gap certificates specialize through that general statement.[^lean-gx-05s5-1]

**Theorem 5.4** (General-`n` spectral well-connectedness). The complete-carrier family is spectrally well-connected for *every* `n ≥ 2`.[^04-anchor-13]
*For the parameterized complete carrier `uniKFamilyCarrier n` and canonical rank signal `uniKFamilySignal n`, and any `n ≥ 2`,*

```
SpectralWellConnected (uniKFamilyCarrier n) (uniKFamilySignal n) hn
```

The proof (`uniKFamily_spectralWellConnected`) does not enumerate sizes. It chains the closed-form gap above with a closed-form rank-signal vulnerability floor: `uniKFamily_completeGraph_product_lower_bound` gives the uniform gap-times-`cv` product `(n+1)·(n+2)/(2n)`, and `uniKFamily_completeGraph_default_product_lower_bound` shows that product already clears the default well-connectedness separator for every `n ≥ 2`. `SpectralWellConnected` here is the conjunction of spectral connectivity and positive governance vulnerability, and both factors are bounded below uniformly in `n`.

This is the genuine general-`n` strength of the spectral substrate: the spectral gap closed form and the well-connectedness certificate are arbitrary-`n` theorems over the complete-carrier family, in contrast to the finite RG trajectory tables of §9, which remain size-`n=5` evaluations. These general-`n` theorems are scoped to the *complete-carrier family* with the canonical rank signal, not a claim that every governance graph at every size is spectrally well-connected, and the bridge from the size-indexed ASI spectral signature to `SpectralWellConnected` remains an explicit hypothesis in the native bridge layer except on the family-aligned class.

##### 5.6 The finite-lattice basin classification

The spectral well-connectedness above is a *structural* property of a graph family. A separate, deliberately narrower result pins down what that well-connectedness buys on the concrete `n=5` verification lattice: it is exactly the class on which the corrigibility bridge discharges.

**Theorem 5.5** (Basin classification is the bridge-discharge classification, finite lattice). On the five-graph `n=5` verification lattice, the un-bundled corrigibility bridge discharges *exactly* for the graphs in the well-connected basin, with `bottleneck5` the sole refutation.[^04-anchor-14]
*For `G` in the lattice `{uniK5, asymK5, nearPath5, wheel5, bottleneck5}` and any positive tolerance `δ`,*

```
BridgeDischargesAt G δ ↔ G ∈ wellConnectedBridgeBasinAt δ
```

The classification is proved parametrically in `δ`, with a `δ = 1/10` specialization, is scale-invariant across positive `δ` on this lattice, and has a quantitative companion that adds a trajectory-indexed perturbation budget to each discharge.[^lean-gx-05s6-1] The four well-connected representatives `uniK5`, `asymK5`, `nearPath5`, and `wheel5` all reach the depth-3 well-connected RG state and discharge the bridge; `bottleneck5` reaches the asymmetric depth-3 state instead and is the unique lattice member where the bridge provably fails.

This is a *finite-lattice* classification: an iff over the explicit five-graph lattice `n5Lattice`, not a general-`n` basin theorem. Its strength is the exact-partition character on that lattice: well-connected basin membership and bridge-discharge are the same predicate there, and the refutation is concrete and singular rather than assumed. Generalizing the iff beyond the five-graph lattice, or deriving a basin classification at arbitrary `n`, remains open work, as does completing the staged reflective/ASI-signature program.

---

### 5.2 Proof sketch

The biconditional decomposes as `→` (forward) and `←` (reverse).

**Reverse direction (`←`)**. Assume `ZeroConsistencyVulnerability G s`, i.e. `G.cv s = 0`. By Theorem 3.2, the mechanism admits a spectral stable equilibrium at every capability scale. For any floor `κ₀`, the floor itself is a witness capability that is `≥ κ₀` and has a spectral stable equilibrium. Therefore `HasArbitrarilyLargeStableEquilibria G s δ`.

**Forward direction (`→`)**. Assume `HasArbitrarilyLargeStableEquilibria G s δ` and suppose for contradiction `¬ ZeroConsistencyVulnerability G s`. By Theorem 3.1, there is a cliff `κ₀ > 0` such that for every `κ ≥ κ₀`, no spectral stable equilibrium exists at `κ`.[^04-anchor-5] By the unbounded-stability hypothesis, there is some `κ ≥ κ₀` with a spectral stable equilibrium at `κ`. Contradiction.

The proof in Lean threads this exactly (`stackelberg_convergence_limit_iff_zero_consistency_vulnerability`).

The adversarial companion (Theorem 5.2) replaces the bare scale floor with a monotone scaling plus the separate `Cofinal scaling` hypothesis: the adversary can choose the trajectory, but the trajectory must be monotone and eventually exceed every bound. The proof structure mirrors the bare case with cofinality supplying a parameter value above the spectral cliff and monotonicity propagating that lower bound to all later parameters.

---

### 5.3 Discussion: implications for alignment researchers

**The structural attractor**. The asymptotic Stackelberg limit identifies a structural attractor on the space of governance mechanisms in the spectral surrogate: as the modeled capability scale grows without bound, only zero-CV mechanisms survive spectrally. Read as a structural observation rather than a recommendation, the limit says that any deployed mechanism with positive consistency vulnerability has a finite spectral stability cliff `κ₀`, and that beyond `κ₀` the proved fact is failure of the no-`spViolation` threshold inequality, not behavioral degradation by construction. The cliff is computable from the graph's spectral data; it is not behavioral.

**Composition with §4**. The capacity converse in §4 shows an alignment-verification ceiling at `C* = δ / cv(G, s)` on the *same* governance graph for deterministic target-saturating positive-log-rate `AlignmentProtocol` families embedded through the capability-response channel. The two ceilings compose in the spectral surrogate: above `C*`, such a verifier cannot provide all-message zero-error certification, and the theorem yields some failed deployment message; under unbounded capability scaling, only zero-CV mechanisms admit any spectral stable equilibrium at all. The two are related but distinct: `C*` is the *verification* ceiling (an information-theoretic property), the asymptotic limit is the *equilibrium* ceiling (a spectral threshold property). A governance graph can be below `C*` (verification feasible) but positive-CV (asymptotically spectrally unstable), and vice versa.

**For Constitutional AI research**: the principle-conflict-resolution layer of Constitutional AI is a candidate source for a directed governance graph. The current Lean surface formalizes only a narrow deployment-side audit-subject lineage, not Anthropic Constitutional AI itself: harm-categorical policy structure is represented by `ConstitutionalAITrainedAuditSubject`, and the constructed audit game supplies `spectralBehavioralEmbedding` plus `constitutionalAI_zero_consistency_vulnerability_implies_game_strategyproof`. A full Constitutional AI behavioral-lineage embedding remains future work. The corresponding mechanism on the empirical side would be the model's behavior under a scaled capability scale; this paper does not prove behavioral instability above a finite cliff.

**For deliberative alignment** (Ngo et al.): deliberation procedures may factor through a directed-decision graph, but no deliberative-alignment embedding is proved here. The asymptotic limit applies only once the deliberation step is embedded as a spectral Stackelberg-equilibrium analysis. Positive-CV deliberation mechanisms would then have a finite spectral cliff in the capability scale; this is a structural complement to behavioral evaluation, not a behavioral persistence result.

**For prover-estimator debate** (Brown-Cohen et al., arXiv:2506.13609): their finite-stage Stackelberg-equilibrium analysis is at fixed capability. The asymptotic limit asks which protocols *survive* unbounded capability scaling. We conjecture but do not prove that the prover-estimator protocol has zero consistency vulnerability in the sense used here; the formal embedding is the natural follow-up (future work: prover-estimator debate as governance graph).

**For AI Control** (Redwood-lineage protocols): the AI Control protocols are candidates for governance-graph extraction (`Bridges/KorbakAIControlBridge.lean`), but no AI Control embedding into this limit has been formalized yet. Each protocol's zero-CV status on a proved extracted graph would be a structural signature in the spectral surrogate. The 5-protocol audit corpus is a systematic application target; the asymptotic limit would identify which embedded protocols admit unbounded spectral stability.

**For the MIRI corrigibility lineage**: corrigibility under unbounded capability is the canonical alignment frontier. The asymptotic Stackelberg limit is a structural complement in the spectral surrogate: corrigibility requires more than asymptotic spectral stability, and this paper does not prove that behavioral corrigibility factors through the governance graph.

The scope qualifier is in §7 and applies to this whole discussion: the limit is *scale-local* within the substrate's `n`-fixed structure; only a narrow Constitutional AI deployment-side audit-subject lineage bridge is proved on the behavioral side; and a scoped bridge to kernel invariants, retaining the existing Lean `ASIBridge` naming, is proved for family-aligned kernel data, while the substrate-wide free bridge remains open in `ASIGovernanceReliability.lean`.

---


### 5.4 Stability summary

We prove the asymptotic Stackelberg limit theorem on directed governance graphs in the spectral surrogate: a mechanism retains arbitrarily large spectral stable equilibria under unbounded capability scaling iff its consistency vulnerability is zero (`G.cv s = 0`). The biconditional is mechanically verified in Lean 4 over rational arithmetic; the iff is exact, both directions discharged. The companion adversarial theorem says that for cofinal monotone adversarial capability scalings, `AdversarialEventuallyNoStable G s δ ↔ ¬ ZeroConsistencyVulnerability G s`; its negation form characterizes zero consistency vulnerability. The constant-subcritical and non-monotone-subcritical fixtures show why cofinality and monotonicity are load-bearing, not that arbitrary bounded or non-monotone capability paths are covered.

The result identifies a structural attractor on the space of governance mechanisms in the spectral surrogate: under unbounded capability scaling, only zero-CV mechanisms survive spectrally. Behavioral lineages — RLHF, Constitutional AI, debate, deliberative alignment, AI Control — do not inherit the asymptotic-stability property unless and until their extracted governance graphs are formalized and proved to satisfy the relevant predicates. The per-lineage embedding is open follow-up, and a scoped bridge to kernel invariants, retaining the existing Lean `ASIBridge` naming, is proved for family-aligned kernel data; the substrate-wide free bridge remains open.

The compounded compositions are visible: with the capacity converse in §4 on the same governance graph, the two ceilings give jointly `(C*, κ₀)`, a verification ceiling and an equilibrium ceiling. The interaction (when both are non-trivial, when one dominates the other) is the matter of follow-up work. The asymptotic Stackelberg limit is the structural foundation for those follow-ups.

## 6. Bifurcation Boundary

§4 gives the capacity ceiling; §5 gives the stability ceiling; §9 gives finite RG trajectory evidence. This section packages capacity admissibility, positive vulnerability, and subcritical spectral stability into one boundary predicate. For the Claude Agent SDK gate, the audit move is to check whether the permission graph's certification ceiling, positive removal vulnerability, and spectral-stability condition are present at the same capability scale.






### 6.1 Main results

##### 6.1 The three-way equivalence

**Theorem 6.1** (Bifurcation iff spectral). The bifurcation theorem packages capacity admissibility, positive vulnerability, and spectral stability into one boundary predicate.[^04-anchor-7]
*Let `G : GovGraph ℚ n` with `[NeZero n]`, `s : Fin n → ℚ`, `δ > 0`, `κ : ℚ`. The following are equivalent:*

1. *`BelowBifurcationBoundary G s δ κ`*
2. *`G.capacity s δ ∧ 0 < G.cv s ∧ SpectralStableEquilibrium G s δ κ`*

The boundary predicate bundles three conditions a reader would otherwise check separately: that the graph can still certify (capacity admissibility), that it has genuine removal vulnerability (positive spectral vulnerability), and that it is spectrally stable at `κ`. The biconditional says these three together are the single bifurcation-boundary predicate, not three independent audits. The proof is direct, using the constructors of `BelowBifurcationBoundary` for the `→` direction and the existence theorem `C_star_exists` for the `←` direction.

For the Claude Agent SDK gate, the reviewer uses this theorem to bundle capacity, vulnerability, and stability into one permission-graph boundary check rather than three unrelated audits.

The theorem packages capacity admissibility, positive CV, and subcritical spectral stability into a single boundary predicate. This is a structural bookkeeping equivalence on the substrate: it bundles the three conditions, and does not assert that capacity, coverage, and stability are the same notion outside it.

##### 6.2 The asymptotic-cliff complement

**Theorem 6.2** (Eventual exit from boundary under positive `cv`, `eventually_not_below_bifurcation_boundary_of_positive_cv` in `Legitimacy.Spectral.Dynamics.Bifurcation`).
*Let `G : GovGraph ℚ n` with `[NeZero n]`, `s : Fin n → ℚ`, `δ > 0`. If `0 < G.cv s`, then there exists `κ₀ > 0` such that for every `κ ≥ κ₀`, `¬ BelowBifurcationBoundary G s δ κ`.*

This is the asymptotic complement: under positive `cv`, the bifurcation boundary is eventually exited, and that cliff is the structural ceiling. At the asymptotic limit the result gives the *contrapositive* of the iff: above the cliff, the joint conjunction fails.

##### 6.3 The Stackelberg-limit bifurcation

**Theorem 6.3** (Stackelberg-limit bifurcation, `stackelberg_limit_bifurcation` in `Legitimacy.Spectral.Dynamics.Bifurcation`).
*The asymptotic Stackelberg limit on the bifurcation boundary corresponds to the zero-consistency-vulnerability characterization at the boundary's structural object.*

The bifurcation-boundary structural object ties to the asymptotic Stackelberg limit theorem. That object hosts the Stackelberg-limit characterization, and the two compose at the structural level.

##### 6.4 The `n=5` concrete witness

**Theorem 6.4** (Concrete bifurcation at `n=5`, `concrete_bifurcation_n5` in `Legitimacy.Spectral.Dynamics.Bifurcation`).
*A concrete `n=5` lattice witnesses the bifurcation-boundary structural object: explicit graph, signal, and capability values for which the iff holds, and explicit witness for which it fails above the cliff.*

The witness demonstrates the iff is non-vacuous on the canonical substrate. The substrate is rational-arithmetic; the witness is `decide`-evaluable.

---

### 6.2 Proof sketch

The proof of `bifurcation_iff_spectral` is direct.

**Forward direction (→)**. Assume `BelowBifurcationBoundary G s δ κ`. The structure provides:
- `capacity_admits : G.capacity s δ`, first conjunct.
- `positive_cv : 0 < G.cv s`, second conjunct.
- `positive_capability : 0 < κ` and `subcritical : κ < C_star G s δ`: together, these establish `SpectralStableEquilibrium G s δ κ` via the structural definition (`SpectralStableEquilibrium` requires positive capability and sub-criticality).

The third conjunct uses the structural lemma from the existence theorem `C_star_exists`: for `κ < C*` with positive `cv`, the spectral stability predicate fires.

**Reverse direction (←)**. Assume `G.capacity s δ ∧ 0 < G.cv s ∧ SpectralStableEquilibrium G s δ κ`. We need to construct `BelowBifurcationBoundary G s δ κ`. The three conjuncts give:
- `capacity_admits` directly from the first conjunct.
- `positive_cv` directly from the second conjunct.
- `positive_capability` from the spectral-stability predicate's structure (`hstable.1`).
- `subcritical : κ < C_star G s δ`: this is the non-trivial step. Suppose for contradiction `C_star G s δ ≤ κ`. By `C_star_exists`'s second clause, this contradicts spectral stability at `κ` (the existence theorem says `C*` is exactly the threshold above which spectral stability fails). Therefore `κ < C_star G s δ`.

The full proof in Lean threads these steps explicitly.

The companion theorems use:

- `eventually_not_below_bifurcation_boundary_of_positive_cv`: direct from the existence and finiteness of `C*` under positive `cv`.
- `stackelberg_limit_bifurcation`: by composition with the asymptotic Stackelberg limit theorem.
- `concrete_bifurcation_n5`: by direct evaluation on the `n=5` substrate.

---

### 6.3 Discussion: the integrated boundary

##### 6.3.1 Boundary packaging

The bifurcation theorem packages capacity admissibility, positive vulnerability, and stability jointly by one boundary predicate on this substrate.

For the reader tracking how §4, §5, and §9 relate, the bifurcation boundary is the single structural object on which the capacity ceiling, the asymptotic Stackelberg limit, and the finite RG trajectory evidence are compared. The projected theorems view that boundary through verification, dynamics, and coarse-graining axes.

##### 6.3.2 The compound architecture

The bifurcation-boundary structural object is the foundation. The three projections are:

- §4 (capacity ceiling): the verification-ceiling projection. Above `C*`, deterministic target-saturating positive-log-rate `AlignmentProtocol` families embedded through the capability-response channel cannot provide all-message zero-error certification; structurally, above `C*` the bifurcation boundary is exited.
- §5 (stability ceiling): the dynamics-ceiling projection. Mechanisms with arbitrarily-large stable equilibria are exactly the zero-consistency-vulnerability ones; structurally, this is the bifurcation-boundary's stability axis.
- §9 (finite RG tables): the coarse-graining projection. The `n=5` robustness lemmas are exact trajectory-value tables for three selectors at `δ = 1/10`, and the δ-parametric theorem is for the standard trajectory.

§6 packages those projections into one boundary predicate viewed along different analytical axes. The bifurcation-iff-spectral theorem is the bookkeeping equivalence that organizes them.

##### 6.3.3 The `n=5` ground truth

The concrete `n=5` witness anchors the abstract iff. On the canonical substrate, the bifurcation-boundary structural object is concrete, evaluable, and reproducible. The witness demonstrates the iff is non-vacuous and gives a computational handle for downstream evaluation.

##### 6.3.4 Boundary notes

**Not a critical-exponent calculation**. The bifurcation-iff-spectral theorem is structural; it is not a quantitative analysis of how capacity / coverage / stability scale near the boundary. The quantitative behavior near the boundary is open work.

**Not a continuous-bifurcation theorem**. The graph substrate is discrete (rational-valued strength signals; finite-vertex graphs). Continuous-bifurcation analogs would require a measure-theoretic substrate not currently in the formalization.

**Not a claim about all governance objects**. The theorem is on the substrate's `GovGraph ℚ n` class. Generalization to other governance-object classes is open work.

##### 6.3.5 The composition with the verifier-target instance

The legitimacy kernel as GS-AI verifier-target instance inherits the bifurcation-boundary's structural ceiling when it is represented by the same finite rational `GovGraph`, with the same signal, tolerance, capability data, positive `cv`, and analysis through `BelowBifurcationBoundary`. Above the boundary, the bundled boundary predicate fails; in the positive-`cv` asymptotic theorem the failure is the subcritical stability/coverage conjunct, while capacity admissibility and positive vulnerability may remain true. The ceiling is the one any verifier-target instance inherits from that same scoped graph-and-boundary package, not a limitation specific to the legitimacy kernel.

---


### 6.4 Boundary summary

The bifurcation-iff-spectral theorem (`bifurcation_iff_spectral` in `Legitimacy.Spectral.Dynamics.Bifurcation`) packages three apparently-distinct structural properties of directed governance graphs, capacity admissibility, positive spectral vulnerability, and spectrally-stable equilibrium at capability `κ`, into a single iff on the bifurcation-boundary structural object. Capacity admissibility, positive vulnerability, and stability are jointly packaged by one boundary predicate on this substrate.

The companion theorems sharpen the synthesis. Under positive `cv`, the boundary is asymptotically exited (`eventually_not_below_bifurcation_boundary_of_positive_cv`). The boundary's structural object hosts the asymptotic Stackelberg limit (`stackelberg_limit_bifurcation`). A concrete `n=5` witness anchors the abstract iff (`concrete_bifurcation_n5`).

The synthesis is the bookkeeping equivalence that organizes the paper's capacity, stability, and coarse-graining results. §4, §5, and §9 all live on the same bifurcation-boundary structural object; the GS-AI verifier-target instance likewise lands here. The projected theorems view the boundary through verification, dynamics, and basin-classification axes.

Future work: continuous-substrate analogs, quantitative scaling near the boundary, generalization to broader governance-object classes, and the empirical question of where real-world AI-deployment graphs sit relative to the boundary.

## 7. Multi-decision Generalization

The binary capacity ceiling in §4 is the base case. The multi-decision generalization re-runs the certification problem when the response alphabet has more than two verdicts: permit, deny, review-required, defer, or other policy outcomes. For the Claude Agent SDK gate, the audit move is to replace the binary permission channel with the actual tool-use verdict set and check whether the same counting pressure appears in the k-ary response map.

A *multi-decision response map* sends each capability coordinate to one of `k` finite decisions rather than to a binary permit/deny value. For the Claude Agent SDK gate, the finite decision set can represent `permit`, `deny`, `review_required`, and `defer`, with the response map reading the represented permission graph at the audited capability scale.

The quantitative theorem generalizes the §4 Pigeonhole argument: a block of length `block` over `k` possible decisions has at most `k^block` output words, so zero-error certification cannot sustain message families whose log-rate exceeds the k-ary output ceiling.[^04-anchor-10] The Lean statement is `multi_decision_capability_response_log_rate_converse` in `Legitimacy.Spectral.Capacity.MultiDecisionCapacity`. For the Claude Agent SDK gate, the reviewer computes the verdict alphabet first, then asks whether the certification family uses more distinguishable tool-use messages than the k-ary channel can carry.

The `C*` binding remains graph-spectral rather than Shannon-theoretic.[^04-anchor-11] The k-ary response map changes the output alphabet in the counting theorem, but `C*(G,s,δ)` still comes from the represented graph's vulnerability and tolerance. The Lean statement is `multi_decision_capability_response_C_star_binding` in `Legitimacy.Spectral.Capacity.MultiDecisionCapacity`. For the Claude Agent SDK gate, adding `review_required` as a third outcome expands the channel alphabet; it does not turn `C*` into a behavioral channel capacity.

## 8. Shannon Negative Bridge

The Shannon negative bridge is the paper's central boundary map. Once §4 names a graph-spectral threshold `C*`, a reader might try to identify it with the Shannon capacity of a scalar noisy-threshold channel. This section rules out that identification, holding the graph-side threshold and the information-theoretic capacity apart as two separately-proved objects on a clean boundary between the spectral and information-theoretic axes. For the Claude Agent SDK gate, the audit move is to keep the permission graph's spectral threshold separate from the Shannon capacity of any chosen scalar noisy abstraction of the permission signal.

### 8.1 Main results

##### 8.1 The negative bridge

**Theorem 8.1** (Fixed scalar noisy-threshold capacity is not the concrete-`C*` bridge). A negative bridge rules out identifying one fixed scalar noisy-channel capacity with all concrete C* values.[^04-anchor-8]
*For any low-noise binary scalar noisy-threshold channel parameter `η : NNReal` with `η < 1/2`, the Shannon capacity of `asNoisyThresholdChannel η hη` cannot simultaneously equal `C*(uniTriGraph, sig, 1/10) = 1/10` and `C*(asymTriGraph, sig, 1/10) = 3/40`. Formally:*

For the Claude Agent SDK gate, the reviewer uses this theorem to reject a report that replaces the permission graph's concrete `C*` with one fixed scalar noisy-channel capacity number.

```
¬ (ChannelCapacity.channelCapacity (asNoisyThresholdChannel η hη).kernel
      = (C_star uniTriGraph sig (1/10) : ℝ) ∧
   ChannelCapacity.channelCapacity (asNoisyThresholdChannel η hη).kernel
      = (C_star asymTriGraph sig (1/10) : ℝ))
```

The proof is by direct refutation: if the Shannon capacity equaled both `C*` values, then the two `C*` values would be equal (transitivity through the single Shannon capacity). But `1/10 ≠ 3/40` as rationals (and as reals). Therefore no fixed `η` can produce a Shannon capacity that bridges both concrete `C*` values.

##### 8.2 The structural witness

The proof's witness graphs are concrete:

- `uniTriGraph`: uniform triangle with edges of equal weight.
- `asymTriGraph`: asymmetric triangle with structurally-distinct weight pattern.
- `sig`: the canonical strength signal.
- `δ = 1/10`: the canonical effectiveness floor.

The two graphs share the signal `sig` and the effectiveness `δ`, but their `cv` values differ by construction. The differing `cv` produces differing `C*`. Any single-value Shannon capacity is too coarse to capture both.

##### 8.3 The implication for the conjectured bridge

The negative result has a structural consequence for the scalar threshold-noise channel family proved against: any Shannon ↔ governance-capacity bridge must be *graph-dependent*, not single-valued across that noisy-threshold class. Matrix-noise extensions are out of scope for Theorem 8.1. The bridge's domain of agreement, if any, is structurally restricted to a sub-class of governance graphs whose `cv` produces matching Shannon capacities.

This reshapes the open question. The task is no longer to find the right `η` but to characterize the algebraic conditions under which the Shannon capacity of a governance-derived channel equals `C*`.

---

### 8.2 Proof sketch

The proof of the negative bridge has the structure of a constructive non-equality refutation.

**Step 1: Concrete `C*` values.** From the substrate's `concrete_C_star_values` theorem:
- `C*(uniTriGraph, sig, 1/10) = 1/10` (as a rational, lifted to ℝ).
- `C*(asymTriGraph, sig, 1/10) = 3/40` (similarly).

**Step 2: Suppose the conjunction holds.** If the Shannon capacity equals both `C*` values:
- `Shannon capacity = 1/10` (from the first conjunct).
- `Shannon capacity = 3/40` (from the second conjunct).

**Step 3: Transitivity contradiction.** The two equalities give `1/10 = 3/40` (transitivity through the single Shannon capacity). But `1/10 ≠ 3/40` as rationals, and the equation, lifted to ℝ, fails by `norm_num`. Contradiction.

**Step 4: The contradiction refutes the conjunction.** Since assuming the conjunction leads to a contradiction, the conjunction is false. Therefore `¬ (conjunction)`, the headline statement.

The full Lean proof (`fixed_noisyThreshold_capacity_not_concrete_C_star_bridge`) threads exactly these four steps with `norm_num` discharging the rational-arithmetic contradictions.

---

### 8.3 Discussion: implications for the information-theoretic alignment audience

##### 8.3.1 The dichotomy as open structure

The negative bridge establishes the dichotomy as the precise structure of the open question. The Shannon ↔ governance-capacity bridge is non-trivial; the open work is to characterize:

- **Agreement class**: under what algebraic conditions does the Shannon capacity of a governance-derived noisy-threshold channel equal `C*`? Hypothetical examples: when `cv(G, s)` matches a specific functional form of the noise parameter `η`; when the graph's structure-constant matches the binary-symmetric-channel capacity at η.
- **Disagreement class**: the substrate's two-graph witness shows the disagreement class is non-empty. Characterizing the disagreement class is on the algebraic-side.

The dichotomy is a research target. The negative bridge gives the structural *anchor*: the disagreement class is non-empty; therefore the agreement and disagreement classes are non-trivially distinct.

##### 8.3.2 Composition with the deterministic capacity converse

The deterministic capacity-converse holds on the deterministic capability-response channel `cap(c) = if c < C* then Permit else Deny`. The negative bridge in this paper says the *noisy-threshold* version of the same channel-construction has a Shannon capacity that does not match `C*`.

The two are compatible. The deterministic converse holds because the deterministic channel has a structurally-clear log-rate ceiling at `C*`. The scalar noisy-threshold Shannon capacity does not coincide with `C*` in general; the noise parameter `η` does not produce a Shannon capacity that matches the spectral threshold across distinct graphs.

The compatibility structure is informative: deterministic-channel converses are at the spectral-threshold level; noisy-channel Shannon capacities are at the information-theoretic level; the two levels do not generally agree.

##### 8.3.3 The orthogonality observation

§4 makes this observation in the capacity-converse setting for the *external* relationship to Cao (2025): their `C̄_tot|S` and our `C*` are different `C*` notions on orthogonal axes. The negative bridge here extends the observation to the substrate's *internal* relationship: the Shannon capacity of the substrate's own noisy-threshold construction and the substrate's `C*` are also different objects on different axes.

The orthogonality is structural. Shannon capacity is a property of channels, carrying input-distribution structure; `C*` is a property of graphs, carrying spectral perturbation budgets. These are orthogonal capacities, and keeping them apart is what lets each be stated and proved cleanly on its own axis.

##### 8.3.4 Boundary notes

**Shannon capacity stays well-defined**. The Shannon capacity of the noisy-threshold channel remains a well-defined Shannon-information-theoretic object; the negative bridge only observes that the Shannon capacity of this particular construction is not the same as `C*`.

**Scope of the bridge ruled out**. The negative result is on the *fixed* scalar low-noise binary channel as the bridge. Matrix-noise models, variable-η constructions, multi-channel constructions, and list-decoding analogs are not addressed here.

**Reading for the spectral framework**. Because `C*` is not equivalent to a single Shannon capacity, spectral statements about `C*` are statements about the spectral structure rather than about Shannon channel capacity.

##### 8.3.5 The reshaped open question

The reshaped open question — characterize the agreement / disagreement classes algebraically — is structurally precise. The negative bridge gives the *anchor*: the disagreement class contains the substrate's two-graph witness. The agreement class (if non-empty) requires specific algebraic conditions distinguishing it from the disagreement class.

This is research-frontier work. The dichotomy is the open structure; the algebraic characterization is the open question.

---


### 8.4 Negative-bridge summary

The negative bridge `fixed_noisyThreshold_capacity_not_concrete_C_star_bridge` establishes that no fixed scalar low-noise binary noisy-threshold channel's Shannon capacity can simultaneously equal both `C*(uniTriGraph, sig, 1/10) = 1/10` and `C*(asymTriGraph, sig, 1/10) = 3/40`. The single-value Shannon capacity is too coarse for the multi-value `C*` structure the substrate exhibits.

The negative result names what shape the Shannon ↔ governance-capacity bridge cannot take, and reshapes the open question to a precise dichotomy: characterize the algebraic conditions distinguishing the agreement and disagreement classes. The disagreement class is non-empty (the substrate's two-graph witness); the agreement class characterization is open. The take-away is a clean boundary map: the graph-spectral `C*` and a fixed scalar Shannon capacity are distinct objects.

The result composes with the deterministic capacity-converse: deterministic converses at the spectral-threshold level coexist with noisy-channel Shannon capacities at the information-theoretic level, but the two levels are not coterminous. The orthogonality observation extends from the substrate's external relationship (Cao (2025)'s `C̄_tot|S` and our `C*`) to the substrate's internal construction (its own noisy-threshold Shannon capacity and its `C*`).

§8 is a *boundary-map* section. The contribution is ruling out a tempting but false stronger claim and establishing the dichotomy as the precise structure of the open question. The agreement / disagreement class characterization is research-frontier work.

## 9. RG Family Coarse-Graining

The RG section answers a finite-table question: what exact spectral trajectory values are produced when the represented graph is coarse-grained by the committed selectors? Capacity (§4) and stability (§5) ask about certification and the modeled capability scale; RG family coarse-graining here records exact Cheeger, modularity, signal-preserving, and standard trajectory values on the committed finite substrates. For the Claude Agent SDK gate, the audit move is to merge hook states or permission states under these selectors and inspect the resulting trajectory values, not to invoke an arbitrary-partition universality theorem.

### 9.1 Main results

##### 9.1 The three robustness theorems

**Theorem 9.1** (Cheeger-family robustness, `robustness_cheeger_n5` in `Legitimacy.Spectral.CrossScale.RGFlow.Robustness`).
*Exact rational trajectory-value table for the Cheeger selector at `n=5`, `δ = 1/10`, over the five archetypes.*

**Theorem 9.2** (Modularity-family robustness, `robustness_modularity_n5` in `Legitimacy.Spectral.CrossScale.RGFlow.Robustness`).
*Exact rational trajectory-value table for the modularity selector at `n=5`, `δ = 1/10`, over the five archetypes.*

**Theorem 9.3** (Signal-preserving family robustness, `robustness_signal_preserving_n5` in `Legitimacy.Spectral.CrossScale.RGFlow.Robustness`).
*Exact rational trajectory-value table for the signal-preserving selector at `n=5`, `δ = 1/10`, over the five archetypes; this table collapses every archetype to `(0, 0)` by depth 3.*

For the Claude Agent SDK gate, the reviewer runs the three coarse-graining audits as independent ways to merge permission states and compares the concrete rational trajectory values.

The three lemmas are independently discharged finite tables. They do not prove basin-classification equality, equality across all three families, or partition-family universality; any universality reading is an interpretation of the table data or a conjectural extrapolation.

##### 9.2 The fixed-point termination

**Theorem 9.4** (RG trajectory terminates at fixed point, `rgTrajectory_terminates_at_fixedPoint` in `Legitimacy.Spectral.CrossScale.RGFlow.Core`).
*Every iterated RG trajectory on a finite governance graph terminates at a fixed point in finitely many steps.*

For the Claude Agent SDK gate, the reviewer uses termination to justify evaluating the coarse-grained permission graph at a well-defined terminal state.

The fixed-point termination theorem is the generic foundation for evaluating canonical greedy RG trajectories at a stable state. The three `n=5` robustness lemmas above are separate finite trajectory tables for alternate selectors.

The companion `rgStateAt_terminates_at_fixedPoint` in `Legitimacy.Spectral.CrossScale.RGFlow.Core` is the per-step version; `governanceGraph_RG_terminates_at_fixedPoint` in the same module is the task-surface alias.

##### 9.3 Concrete iterated RG at `n=5`

**Theorem 9.5** (Concrete iterated RG at `n=5`, `concrete_iterated_RG_n5` in `Legitimacy.Spectral.CrossScale.RGFlow.N5`).
*The standard deterministic maximum-weight-merge RG trajectory at the `n=5` lattice produces a concrete reproducible rational trajectory table.*

**Theorem 9.6** (δ-parametric signature, `concrete_iterated_RG_n5_parametric_signature`). The standard `n=5` RG trajectory has a δ-parametric depth-3 signature; this is not a theorem about the three robustness-table selectors.[^04-anchor-9]
*For positive `δ`, the standard trajectory sends `uniK5`, `asymK5`, `nearPath5`, and `wheel5` to `ASISpectralSignature δ`, while `bottleneck5` does not.*

The δ-parametric signature is informative for the standard trajectory: the depth-3 split is not a `δ = 1/10` coincidence. The `ASISpectralSignature` target is the threshold-selected modal predicate the trajectory lands in; the trajectory result is what is proved here, and no derivation of well-connectedness from that signature is claimed. The robustness lemmas for Cheeger, modularity, and signal-preserving selectors remain exact `δ = 1/10` finite tables.

##### 9.4 Coarse-graining preservation properties

**Theorem 9.7** (Coarse-grain solidarity preservation, `coarseGrain_unconditional_solidarity` in `Legitimacy.Spectral.CrossScale.RGFlow.Core`).
*For every graph and every selected pair of nodes `i j`, the pairwise merge `G.coarseGrain i j hij` satisfies `WeightedGraphSolidarity` under the current weighted-average semantics.*

**Theorem 9.8** (Coarse-grain may break monotonicity, `coarseGrain_may_break_monotonicity` in `Legitimacy.Spectral.CrossScale.RGFlow.Core`).
*There exists a concrete graph and selected pairwise merge for which coarse-graining breaks `RGFlowMonotonicityAt`.*

The asymmetric preservation is pairwise and scoped: the current pairwise coarse-grain operator always yields weighted solidarity, while a concrete pairwise merge can break `RGFlowMonotonicityAt`. The Lean statement does not quantify over arbitrary partitions or prove that basin transitions come precisely from monotonicity breaks.

##### 9.5 The universality conjecture evidence

**Theorem 9.9** (Universality conjecture evidence, `universality_conjecture_evidence`, `lean/Legitimacy/Spectral/CrossScale/RGFlow/Core.lean`).
*Five concrete three-node graphs, under the standard merge `0 + 1` at `δ = 1/10`, all fall into `RGCriticalCapabilityCollapseClass`.*

This is five-graph standard-merge collapse evidence. It does not package the three `n=5` robustness tables, does not quantify over the `n=5` archetypes, and does not prove that basin classification is invariant across partition families.

---

### 9.2 Proof sketch

The three robustness lemmas share a finite-table form. We sketch the Cheeger-family case; the modularity and signal-preserving cases are parallel.

**Step 1: Construct the iterated trajectory.** `rgTrajectoryCheeger G s δ k` produces the state at step `k`. By the fixed-point termination theorem, there is a finite `k₀` at which the trajectory stabilizes.

**Step 2: Evaluate the rational trajectory values.** Each theorem states exact values of `rgTrajectoryCheeger G s (1 / 10) k` for the five archetypes and listed depths. The values are computed by `native_decide` on the rational-arithmetic substrate.

**Step 3: Record the table.** The theorem records the full finite conjunction of exact equalities. It does not assert a separate basin-classification match theorem.

**Step 4: Mechanical evaluation.** The finite table is `native_decide`-discharged on the `n=5`, `δ = 1/10` substrate.

The three families differ in Step 1 (the trajectory selector), and the table in Step 4 is reproduced for each. The signal-preserving table has the especially strong finite feature that all five archetypes reach `(0, 0)` by depth 3.

The fixed-point termination theorem (Theorem 9.4) is by induction on the trajectory length: each RG step strictly reduces a structural well-ordered quantity (the lattice depth `n`); the well-ordering ensures finite termination.

The pairwise solidarity result (Theorem 9.7) is by direct construction under the current weighted-average semantics; the monotonicity-break (Theorem 9.8) is by concrete witness construction.

---

### 9.3 Discussion: implications for frontier-safety researchers

##### 9.3.1 What the finite evidence supports

The three-family robustness lemmas are exact finite trajectory tables at `n=5`, `δ = 1/10`; `universality_conjecture_evidence` is separate five-graph, three-node, standard-merge collapse evidence. Together they motivate a universality interpretation, but the Lean substrate does not prove partition-family universality or arbitrary-partition basin invariance.

For a frontier-safety researcher trained in statistical mechanics, the honest framing is finite evidence toward an RG-style universality program: concrete selectors and concrete standard merges exhibit reproducible trajectory and collapse signatures. Researchers from the Bengio "Deep learning as statistical physics" register, the DeepMind ML-theory groups, or the AI-safety crossover with statistical-mechanics-of-deep-learning literature can engage on that conjectural universality framing directly, but the proved Lean claims remain the finite tables and standard-merge evidence.

##### 9.3.2 The scale-locality

The result is scale-local within `n=5`: cross-`n` parametric universality is not claimed. The standard depth-3 RG state on `n=5` lattices supplies the δ-parametric signature theorem; the alternate-selector robustness lemmas are fixed-`δ` tables. No scale-invariant stability predicate beyond `ASISpectralSignature`/the listed table values is currently formalized for these claims.

This matters for the capability-scale framing: the basin classification is established within `n=5`, and the cross-scale and partition-family universality extensions remain open work.

##### 9.3.3 Composition with the asymptotic Stackelberg limit

The asymptotic Stackelberg limit characterizes which mechanisms retain spectral stability under unbounded capability scaling in the surrogate. The combination with the finite RG evidence gives a richer but scoped picture: the standard trajectory has a δ-parametric `n=5` depth-3 signature, the alternate selectors have exact fixed-`δ` tables, and the dynamic-stability characterization remains precise for the fixed graph/signal substrate. A universal basin theorem across selectors would be a further conjectural synthesis, not a proved composition here.

##### 9.3.4 The δ-parametric signature

The standard `n=5` depth-3 signature is δ-parametric, not `δ = 1/10`-specific, so the standard trajectory's signature is not tied to a single tolerance value; the Cheeger/modularity/signal-preserving robustness lemmas remain exact `δ = 1/10` tables.

The δ-parametric signature is informative for the capability-scale framing: the standard trajectory's signature is a parametric property of the governance graph at the substrate scale, not a specific-parameter coincidence.

##### 9.3.5 The asymmetric preservation as basin-transition mechanism

Pairwise coarse-graining yields weighted solidarity under the current semantics; monotonicity can fail for a concrete pairwise merge. This asymmetry is structural evidence about the RG operator, but the current Lean statements do not prove a general basin-transition mechanism.

The asymmetric preservation is also structurally informative for the paper's shared substrate: the kernel's certifying structure depends on solidarity, which the pairwise weighted-average merge supplies, and monotonicity, which can be broken by RG. General arbitrary-partition preservation and a monotonicity-break-and-recover classification theorem remain outside the proved surface.

---


### 9.4 RG summary

We prove three independent exact finite trajectory tables at the `n=5`, `δ = 1/10` substrate: Cheeger-cut, modularity-maximizing, and signal-preserving selectors over five archetypes. The fixed-point termination theorem covers the canonical greedy trajectory; the concrete standard iterated trajectory at `n=5` is reproducible; the standard trajectory's parametric δ-signature confirms its depth-3 signature is not `δ = 1/10`-specific.

Pairwise coarse-graining yields weighted solidarity under the current semantics and may break `RGFlowMonotonicityAt`: the asymmetric preservation is a scoped structural fact about the pairwise operator.

The result is scale-local within `n=5` and table-based within the named selectors. It is Wilsonian-RG-flavored finite evidence on a governance object, within the scoped substrate proved here.

Compositional context: the finite RG trajectory evidence sits beside the asymptotic Stackelberg limit, the bifurcation-iff-spectral packaging theorem, and the capacity-converse. The compounded structural picture is in the spectral surrogate: exact finite coarse-graining tables and a standard δ-parametric signature on the RG side; zero-CV mechanisms are exactly the asymptotically stable ones on the fixed-graph dynamics side; capacity admissibility, positive vulnerability, and stability are jointly packaged by one boundary predicate on this substrate; deterministic target-saturating positive-log-rate alignment verification embedded through the capability-response channel is bounded by the spectral capacity threshold.

Future work: cross-`n` parametric universality (the open scope-locality question), additional partition families (random, learned), continuous-RG analogs, and the structural relationship between basin transitions and dynamic-stability properties.

## 10. Conclusion: Certification, Stability, and Coarse-Graining on One Represented Graph

This paper proves three standalone graph-mathematics results about one represented governance graph. The capacity question (§4, generalized in §7) asks what the graph can certify through the specified response channel. The stability question (§5) asks when the same graph retains spectral equilibrium as the modeled capability scale grows. The coarse-graining question (§9) asks which basin signature persists when the represented substrate is merged across finite partition families. Each result stands on its own substrate; together they map the certification, stability, and coarse-graining structure of represented governance graphs, alongside the legitimacy kernel rather than inside it.

§6 and §8 clarify how those questions relate. §6 combines capacity admissibility, positive vulnerability, and spectral stability in a single bifurcation-boundary predicate. §8 proves that graph-spectral `C*` is *not* the Shannon capacity of one fixed noisy-threshold channel. The two results therefore relate the capacity and stability conditions while keeping the spectral threshold distinct from information-theoretic channel capacity.

For the Claude Agent SDK tool-use permission gate, the audit reviewer should now see one represented permission graph from three observational axes. The capacity audit finds the bound at `C*`; the stability audit finds the finite cliff at `κ₀`; the RG audit tests basin persistence under coarse-graining. The bifurcation iff bundles the capacity and stability predicates into one boundary check on the represented graph, rather than treating them as disconnected checks.

The open frontier is also explicit. Continuous substrates require more than the current rational finite-graph arithmetic. Cross-scale RG requires evidence beyond the `n=5` finite-family substrate. Behavioral lineages require embedding proofs that carry RLHF, debate, deliberative alignment, AI Control, Constitutional AI, and related systems into the surrogate before the graph-side bounds can apply.

### References

[Agarwal2026] Agarwal, A. On the Formal Limits of Alignment Verification. arXiv:2603.08761, 2026.

[AnthropicReasoning2025] Anthropic. Reasoning Models Don't Always Say What They Think. arXiv:2505.05410, 2025.

[AnthropicCoT2025] Anthropic, et al. Chain of Thought Monitorability: A New and Fragile Opportunity for AI Safety. arXiv:2507.11473, 2025.

[Bai2022] Bai, Y., Kadavath, S., Kundu, S., et al. Constitutional AI: Harmlessness from AI Feedback. arXiv:2212.08073, 2022.

[Bengio2025] Bengio, Y., Cohen, M., Fornasiere, D., et al. Superintelligent Agents Pose Catastrophic Risks: Can Scientist AI Offer a Safer Path? arXiv:2502.15657, 2025.

[BracaleSyrnikov2026] Bracale Syrnikov, M., et al. Institutional AI. arXiv:2601.11369, 2026.

[BrownCohen2025] Brown-Cohen, J., Irving, G., and Piliouras, G. Avoiding Obfuscation with Prover-Estimator Debate. arXiv:2506.13609, 2025.

[Cao2025] Cao, W. The Alignment Bottleneck. arXiv:2509.15932, 2025.

[Christiano2021] Christiano, P., Cotra, A., and Xu, M. Eliciting Latent Knowledge: How to Tell if Your Eyes Deceive You. ARC technical report, 2021.

[Christiano2017] Christiano, P., Leike, J., Brown, T., et al. Deep Reinforcement Learning from Human Preferences. NeurIPS, 2017.

[Chung1997] Chung, F. R. K. Spectral Graph Theory. American Mathematical Society, 1997.

[CoverThomas2006] Cover, T. M., and Thomas, J. A. Elements of Information Theory. Wiley-Interscience, 2nd edition, 2006.

[CsiszarKorner2011] Csiszár, I., and Körner, J. Information Theory: Coding Theorems for Discrete Memoryless Systems. Cambridge University Press, 2nd edition, 2011.

[Dalrymple2024] Dalrymple, D., Skalse, J., Bengio, Y., Russell, S., Tegmark, M., et al. Towards Guaranteed Safe AI. arXiv:2405.06624, 2024.

[Fortunato2010] Fortunato, S. Community Detection in Graphs. Physics Reports, 486(3-5):75-174, 2010.

[Gibbard1973] Gibbard, A. Manipulation of Voting Schemes: A General Result. Econometrica, 41(4):587-601, 1973.

[Greenblatt2023] Greenblatt, R., Shlegeris, B., et al. AI Control: Improving Safety Despite Intentional Subversion. arXiv:2312.06942, 2023.

[Hubinger2024] Hubinger, E., Denison, C., Mu, J., et al. Sleeper Agents: Training Deceptive LLMs that Persist Through Safety Training. arXiv:2401.05566, 2024.

[Irving2018] Irving, G., Christiano, P., and Amodei, D. AI Safety via Debate. arXiv:1805.00899, 2018.

[Korbak2025] Korbak, T., Clymer, J., Hilton, B., Shlegeris, B., and Irving, G. A sketch of an AI control safety case. arXiv:2501.17315, 2025.

[Kuznetsov2004] Kuznetsov, Y. A. Elements of Applied Bifurcation Theory. Springer, 3rd edition, 2004.


[Nayebi2025] Nayebi, A. Intrinsic Barriers and Practical Pathways for Human-AI Alignment: An Agreement-Based Complexity Analysis. arXiv:2502.05934. AAAI 2026 oral, 2025.

[NewmanGirvan2004] Newman, M. E. J., and Girvan, M. Finding and Evaluating Community Structure in Networks. Physical Review E, 69(2):026113, 2004.

[Polchinski1984] Polchinski, J. Renormalization and Effective Lagrangians. Nuclear Physics B, 231(2):269-295, 1984.

[Satterthwaite1975] Satterthwaite, M. Strategy-Proofness and Arrow's Conditions. Journal of Economic Theory, 10(2):187-217, 1975.

[Shannon1948] Shannon, C. E. A Mathematical Theory of Communication. Bell System Technical Journal, 27(3):379-423; 27(4):623-656, 1948.

[Shannon1956] Shannon, C. E. The Zero Error Capacity of a Noisy Channel. IRE Transactions on Information Theory, IT-2(3):8-19, 1956.

[Strogatz1994] Strogatz, S. H. Nonlinear Dynamics and Chaos. Westview Press, 1994.

[Tibebu2026] Tibebu, H. The Accountability Horizon: An Impossibility Theorem for Governing Human-Agent Collectives. arXiv:2604.07778, 2026.

[WilsonFisher1972] Wilson, K. G., and Fisher, M. E. Critical Exponents in 3.99 Dimensions. Physical Review Letters, 28(4):240-243, 1972.

[Ziegler2019] Ziegler, D. M., Stiennon, N., Wu, J., et al. Fine-Tuning Language Models from Human Preferences. arXiv:1909.08593, 2019.

### Lean Substrate References

- `Legitimacy.GovGraph.governance_capacity_alignment_threshold`
- `Legitimacy.GovGraph.governance_capacity_alignment_log_rate_converse`
- `Legitimacy.GovGraph.binary_output_log_rate_converse`
- `Legitimacy.GovGraph.governance_capacity_threshold_C_star_binding`
- `Legitimacy.GovGraph.raw_cardinality_rate_padding_counterexample`
- `Legitimacy.GovGraph.capabilityResponse`
- `Legitimacy.GovGraph.capabilityResponse_eq_permit_iff_C_star_le`
- `Legitimacy.GovGraph.capabilityResponseBinaryBlockCode`
- `Legitimacy.GovGraph.capabilityResponseBinaryBlockCode_zeroError`
- `Legitimacy.GovGraph.capabilityResponseBinaryBlockCode_log2_message_card`
- `Legitimacy.GovernanceChannel.erasure_channelCapacity_eq`
- `Legitimacy.GovernanceChannel.concreteNoisyChannel_channelCapacity_eq_cv`
- `Legitimacy.GovernanceChannel.concreteNoisyChannel_finite_capacity_implies_C_star_threshold`
- `Legitimacy.GovernanceChannel.existsConcreteNoisyCStarCalibration_of_cv_pos_lt_log_two`
- `Legitimacy.GovernanceChannel.ConcreteNoisyCStarCalibration.toExactCapacityCertificate`
- `Legitimacy.GovernanceChannel.fixed_noisyThreshold_capacity_not_concrete_C_star_bridge`
- `Legitimacy.CapacityKernel`
- `Legitimacy.WellConditionedForCapacity`
- `Legitimacy.governance_certificate`
- `Legitimacy.governance_certificate_constructible`
- `Legitimacy.PositiveProcedureExamples.concreteHalfNoisyKernel_C_star`
- `Legitimacy.PositiveProcedureExamples.concreteHalfNoisyCertificateAtOneTenth`
- `Legitimacy.C_star`
- `Legitimacy.GovGraph.cv_spectral_bound`
- `Legitimacy.C_star_spectral_bound`
- `Legitimacy.governance_graph_C_star_expander_bound`
- `Legitimacy.GovernanceChannel.low_noise_noisyThreshold_capacity_certificate`
- `Legitimacy.GovernanceChannel.noisyThreshold_capacity_attainer_exists_and_unique`
- `Legitimacy.stackelberg_convergence_limit_iff_zero_consistency_vulnerability`
- `Legitimacy.zeroConsistencyVulnerability_has_arbitrarily_large_stable_equilibria`
- `Legitimacy.eventually_no_stable_equilibrium_of_positive_consistency_vulnerability`
- `Legitimacy.eventually_no_stable_equilibrium_of_positive_cv`
- `Legitimacy.stackelberg_convergence_epsilon`
- `Legitimacy.SpectralStableEquilibrium`
- `Legitimacy.ZeroConsistencyVulnerability`
- `Legitimacy.HasArbitrarilyLargeStableEquilibria`
- `Legitimacy.adversarial_stackelberg_unbounded_stability_iff_zero_consistency_vulnerability`
- `Legitimacy.adversarial_stackelberg_unbounded_of_positive_consistency_vulnerability`
- `Legitimacy.positive_consistency_vulnerability_of_adversarial_stackelberg_unbounded`
- `Legitimacy.adversarial_stackelberg_eventual_collapse_iff_positive_consistency_vulnerability`
- `Legitimacy.subcriticalConstantScaling`
- `Legitimacy.nonmonotoneSubcriticalTail`
- `Legitimacy.bifurcation_iff_spectral`
- `Legitimacy.ASIBridge.asiCompleteGraph_spectralGap_eq`
- `Legitimacy.ASIBridge.uniKFamily_spectralWellConnected`
- `Legitimacy.ASIBridge.uniKFamily_completeGraph_product_lower_bound`
- `Legitimacy.ASIBridge.uniKFamily_completeGraph_default_product_lower_bound`
- `Legitimacy.n5_bridge_discharges_iff_well_connected_basin`
- `Legitimacy.n5_bridge_discharges_iff_well_connected_basin_parametric`
- `Legitimacy.n5_quantitative_bridge_discharges_iff_well_connected_basin_parametric`
- `Legitimacy.well_connected_bridge_basin_scale_invariant_on_n5`
- `Legitimacy.eventually_not_below_bifurcation_boundary_of_positive_cv`
- `Legitimacy.stackelberg_limit_bifurcation`
- `Legitimacy.concrete_bifurcation_n5`
- `Legitimacy.BelowBifurcationBoundary`
- `Legitimacy.C_star_exists`
- `Legitimacy.GovGraph.capacity`
- `Legitimacy.GovGraph.cv`
- `Legitimacy.GovernanceChannel.asNoisyThresholdChannel`
- `Legitimacy.uniTriGraph`
- `Legitimacy.asymTriGraph`
- `Legitimacy.sig`
- `Legitimacy.concrete_C_star_values`
- `Legitimacy.robustness_cheeger_n5`
- `Legitimacy.robustness_modularity_n5`
- `Legitimacy.robustness_signal_preserving_n5`
- `Legitimacy.GovGraph.rgTrajectory_terminates_at_fixedPoint`
- `Legitimacy.GovGraph.governanceGraph_RG_terminates_at_fixedPoint`
- `Legitimacy.GovGraph.rgStateAt_terminates_at_fixedPoint`
- `Legitimacy.concrete_iterated_RG_n5`
- `Legitimacy.concrete_iterated_RG_n5_parametric_signature`
- `Legitimacy.concrete_RG_flow_5graphs`
- `Legitimacy.universality_conjecture_evidence`
- `Legitimacy.coarseGrain_*_solidarity` (coarse-grain solidarity preservation)
- `Legitimacy.coarseGrain_may_break_monotonicity`
- `Legitimacy.GovGraph.partitionFamilyCheeger`
- `Legitimacy.GovGraph.partitionFamilyModularity`
- `Legitimacy.GovGraph.partitionFamilySignalPreserving`
- `Legitimacy.ASISpectralSignature`

[^lean-gx-04s5-1]: Lean identifiers: `ConcreteNoisyCStarCalibration`, `concreteNoisyChannel_channelCapacity_eq_cv`, `ConcreteNoisyCStarCalibration.toExactCapacityCertificate`, and `finite_capacity_implies_C_star_threshold`. Modules: `Legitimacy.Spectral.Channels.ConcreteNoisyChannel`, `Legitimacy.Spectral.Channels.CStarChannelBridge`.

[^lean-gx-04s5-2]: Lean identifiers: `uniTriGraph × halfSig`, `asymTriGraph × asymTriHalfSig`, `nearPathGraph × nearPathHalfSig`, `bottleneckGraph × bottleneckHalfSig`, `uniK5 × uniK5HalfSig`, and `existsConcreteNoisyCStarCalibration_of_cv_pos_lt_log_two`.

[^lean-gx-04s5-3]: Lean identifiers: `ConcreteBSCNoisyCStarCalibration`, `concreteBSCNoisyChannel_channelCapacity_eq_cv`, `existsConcreteBSCNoisyCStarCalibration_of_cv_pos_lt_log_two`, and `concreteHalfBSCNoisyCStarCalibration`.

[^lean-gx-04s6-1]: Lean identifiers: `Principle`, `Constitution`, `ConstitutionalAIClaimClass`, `constitutionally_respecting_policy_substrate_admissible`, `threePrincipleConstitution3`, and `threePrinciplePolicy3_verdicts_differ`. Modules: `lean/Legitimacy/Behavioral/Constitution.lean`.

[^lean-gx-04s6-2]: Lean identifiers: `NoisyKernel`, `NoisyWellConditionedForCapacity`, `governance_certificate_constructible_noisy`, `noisy_solidarity_not_derivable_from_consistency_data`, `concreteHalfBSCNoisyCertificateAtOneTenth_kind`, and `concreteHalfBSCNoisyKernel_verdictDrift_oneTwentieth_to_oneTenth`. Modules: `lean/Legitimacy/Spectral/Certificates/NoisyPositiveProcedureCertificate.lean`.

[^lean-gx-04s7-1]: Lean identifiers: `PositiveProcedureExamples.concreteHalfNoisyCertificateAtOneTenth`, `PositiveProcedureExamples.concreteHalfNoisyCertificateNearBoundary`, `concreteHalfNoisyKernel_C_star`, `concreteHalfNoisyCertificateAtOneTenth_kind`, `concreteHalfNoisyCertificateNearBoundary_kind`, `concreteHalfNoisyCertificateAtOneTenth_verdict_and_no_violation`, and `concreteHalfNoisyCertificateNearBoundary_verdict_and_no_violation`.

[^lean-gx-05s5-1]: Lean identifiers: `uniK5_eq_asiCompleteGraph`, `uniK7_eq_asiCompleteGraph`, `uniK9_eq_asiCompleteGraph`, `uniK5_spectralGap_eq_certificate_via_general`, `uniK7_spectralGap_eq_certificate_via_general`, `uniK9_spectralGap_eq_certificate_via_general`, plus the original finite certificates `uniK5_spectralGap_eq_certificate`, `uniK7_spectralGap_eq_certificate`, and `uniK9_spectralGap_eq_certificate`.

[^lean-gx-05s6-1]: Lean identifiers: `n5_bridge_discharges_iff_well_connected_basin_parametric`, `n5_bridge_discharges_iff_well_connected_basin`, `well_connected_bridge_basin_scale_invariant_on_n5`, and `n5_quantitative_bridge_discharges_iff_well_connected_basin_parametric`.
