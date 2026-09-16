# Legitimacy: Checkable Rules for AI Agents

[![Canonical verification](https://github.com/abenenson/legitimacy/actions/workflows/ci.yml/badge.svg?branch=master&event=push)](https://github.com/abenenson/legitimacy/actions/workflows/ci.yml?query=branch%3Amaster+event%3Apush)

As AI systems become more capable, alignment increasingly concerns the
organization of power. An agent entrusted with allocating resources, delegating
work or setting the terms of another agent's actions is making decisions about
authority. When agents act together, the consequences depend on how their
decisions interact and on the rules that give those decisions force.

Institutional design offers a way to think about this problem. Cooperation
within a group can coexist with disregard for people outside it. Individually
reasonable decisions can produce an unacceptable collective outcome. A rule
that works under ordinary conditions can become vulnerable when participants
gain the ability to exploit it. Trustworthy autonomy therefore requires ways
to justify decisions, examine their consequences, resolve competing claims and
preserve the ability to change course.

**Legitimacy studies the rules that could make such autonomy possible.** It
brings together social choice, formal verification and models of strategic
behavior to ask how governance can remain coherent and correctable as
capabilities grow toward superintelligence. The governing rules are themselves
objects of scrutiny: the project asks what they guarantee, how those guarantees
interact, and what happens when a system reaches their limits.

The mathematical results give this question a concrete shape. In the models
studied here, a rule's remaining sensitivity to changes in its governing
structure imposes a finite limit on stability as capability grows. Separate
results show why certain rules for allocating scarce resources must give up
some otherwise desirable guarantees. The constructive task is to make those
tradeoffs explicit while preserving useful action, checking evidence and
means of correction.

The project's central object is a **semantic legitimacy kernel**: a mathematical
specification connecting a governing rule to evidence about its decisions,
its correction mechanisms and its interactions with other rules. It gives
claims about trustworthy governance an explicit form that can be inspected,
challenged and, within the stated models, proved. The repository develops this
program through Lean proofs and executable Rust experiments. The first example
shows why judging each agent's actions separately can miss what they do together.

## Where to start

| If you want to understand… | Start with… |
| --- | --- |
| What approved actions can do together, and how a repair works | [The executable experiment and its limits](docs/executed-composition-v1.md) |
| Whether a rule can remain stable as modeled capability grows | [Capacity and stability](papers/04-spectral-scaling.md) |
| Which tradeoffs are unavoidable when requests compete for scarce authority | [The verified impossibility theorem](papers/03-impossibility-theorem.md) |
| How guarantees, evidence and declared tradeoffs fit into a checkable object | [The legitimacy kernel](papers/02-semantic-legitimacy-kernels.md) |
| What is proved, what is executed, and what remains to validate | [Read the evidence in five minutes](docs/claim-ledger.md#read-the-evidence-in-five-minutes) |
| What the framework-specific graph audits show | [Worked results and passing controls](docs/formal-overview.md#worked-extractions-the-obstruction-on-real-agent-graphs) |
| Where each part of the codebase lives | [Lean and Rust module map](docs/lean-module-architecture.md) |
| How the contribution differs from earlier work | [The research comparison](papers/06-positioning.md) |

The [formal overview](docs/formal-overview.md) carries the detailed argument,
worked audit results, [exact theorem anchors](docs/formal-overview.md#theorem-spine)
and additional CLI workflows. The [paper index](papers/README.md) maps the six
manuscripts section by section.

## Approved separately, unsafe together

Suppose a policy forbids publishing both fragments of a protected record. Two
agents are each allowed to publish their own fragment. Check each request on its
own and both pass; execute both and the combined result violates the policy.

The [composition experiment](docs/executed-composition-v1.md) makes this failure
and its repair runnable. Its guard remembers what has already reached the public
output. After the first fragment is public, it blocks publication of the second
while still allowing delivery to a private vault or publication of a harmless
summary. The forbidden outcome stays the same. Useful work remains possible.

The proofs connect actual deliveries to the forbidden outcome, establish the
repair for every finite sequence of requests in the model, and identify the
information a monitor needs to make exact decisions while preserving useful work.

**Scope:** two supplied agent identities, synthetic data and a sequential host.
The experiment runs no language model; its proofs cover this declared model,
not arbitrary deployed agents.

## Try the example

Start with the [companion reader](docs/executed-composition-reader.html):
download the HTML file and open it in your browser. It presents the seven
outcomes and their evidence without installing Rust or Lean.

To execute the experiment yourself, run from this checkout with Rust installed:

```sh
cargo run --bin legitimacy-executed-composition -- demo
```

The output compares the harmful combination, safe alternatives, and cases with
missing permission or evidence. No Lean knowledge or model credentials are
needed. The first build downloads dependencies and can take several minutes.
The [reproduction guide](docs/executed-composition-v1.md#run-it) explains the
seven outcomes, signed-capture checks and how to build an offline bundle.

**Latest published release:** [signed v1.1.1](https://github.com/abenenson/legitimacy/releases/tag/v1.1.1).
The release includes the composition experiment and an offline Linux x86_64 bundle.
[Citation metadata](CITATION.cff) describes this checkout.

<a id="what-you-can-check"></a>

## What a governing rule has to earn

The institutional question becomes concrete when we ask what evidence a rule
must supply before relying on it. The runtime part of a legitimacy kernel
organizes that evidence around five obligations:

| Obligation | What it asks of the modeled system |
| --- | --- |
| **Certifiability** | Decisions have witnesses that a checker can validate. |
| **Observability** | Observations preserve the information needed to distinguish governance-relevant states. |
| **Corrigibility** | The system's modeled actions preserve support for its specified supervisory operations. |
| **Compositional safety** | Safety is preserved within the declared causal boundary. |
| **Non-vacuity** | There is an eligible permit witness; blanket refusal, permanent escalation and deadlock are excluded. |

The [kernel constructions](docs/formal-overview.md#the-kernel-object) demonstrate
parts of this specification with an action that changes the governing state
and, separately, a causal graph containing a real handoff edge. These examples
simplify different dimensions: the changing-state example has no causal edges,
while the handoff example has identity actions. They give concrete starting
points for a runtime that combines those obligations under meaningful action
and interaction. Corrigibility here means preservation of supervisory
operations; it does not establish control over arbitrary deployed agents.

A semantic legitimacy kernel connects these runtime obligations to further
evidence about the governing rule: its behavior across related claims, its
response to perturbations, and the relationship between those mathematical
representations. This relationship is an explicit **bridge contract**. The
kernel makes the required connections visible rather than inferring them from
a successful check of one component. The chosen obligations also leave the
substantive policy question open: which values and interests should a rule serve?

## How capability puts a rule under pressure

A rule can appear dependable while the actors subject to it cannot exploit
its weaknesses. To study that concern precisely, the project fixes a governance
graph, a signal on that graph, and an acceptable tolerance for perturbation.
It measures how much the graph's verdict can change when one participant is
removed. The largest such change is its **consistency vulnerability**, written
`cv`. In this model, greater capability means being able to target progressively
smaller changes.

The result is a sharp distinction:

- With positive vulnerability, the model has a finite critical capability:
  **C* = tolerance / cv**.
- Stability at arbitrarily large capability holds **exactly when cv = 0**.

The surrounding proofs identify this vulnerability with the classical
gross-error sensitivity of the verdict map under node deletion, and extend the
stability characterization to adversarially chosen increasing capability
trajectories. These [sensitivity and stability results](docs/formal-overview.md#capacity-and-stability-under-capability-scaling)
make the mathematical interpretation explicit. Applying the threshold to a
deployment would require independent justification of its graph, signal,
tolerance and capability model.

The program also connects this quantitative question to a structural one:
some rules cannot preserve all the guarantees their participants might want.
For a specified peer-relative construction, the shared-cliff theorem carries
both the forced tradeoff and positive vulnerability on a canonical
claimant-interaction graph. That carrier is fixed, with `cv = 3/4`; the theorem
does not derive every deployment's own vulnerability. The connection and the
separate graph-derived examples are distinguished in the
[formal overview](docs/formal-overview.md#theorem-spine).

## Why some guarantees conflict

Rules that allocate scarce resources often decide one request in relation to
others. Three natural requirements then come into tension:

- **Consistency:** removing a denied request leaves the other decisions unchanged.
- **Solidarity:** rescaling all claim strengths together by a positive factor
  leaves decisions unchanged.
- **Cross-claimant monotonicity:** strengthening one claim does not turn a permit
  into a denial for any claimant.

The wider impossibility theorem identifies a class of scarce-resource rules
that cannot satisfy all three. These rules treat claimant identities
symmetrically, yet make each decision depend on the competing claims. The
theorem specifies further conditions on the surrounding pipeline; the median
rule is a concrete member of the covered class. A max-rule example preserves
consistency while sacrificing monotonicity, showing why the conclusion must
allow different sacrifices. A narrower structural class forces stronger
individual failures. The [theorem, premises and separating examples](docs/formal-overview.md#the-forcing-argument-why-the-kernel-must-declare-a-sacrifice)
keep those two scopes distinct.

Here is a concrete change of verdict. A threshold first admits requests with
strength greater than 0.5. A second gate permits a surviving request when at
least half the surviving strengths are no greater than its own:

| Request | Original strength | After A strengthens | Original verdict | New verdict |
| --- | --- | --- | --- | --- |
| A | 0.40 | 0.60 | Deny | Permit |
| B | 0.55 | 0.55 | Permit | Deny |
| C | 0.90 | 0.90 | Permit | Permit |

B clears the first threshold in both cases. Once A joins the surviving set,
B falls below the second gate's relative cutoff. Nothing about B's own evidence
changed. This is a [proved rule example](lean/Legitimacy/Results/Composition.lean),
distinct from the opening experiment's publication policy and from an upstream
agent framework's actual callback logic.

For an operator, the next question is whether that displacement is intended.
Priority and preemption policies may deliberately allow it. Legitimacy's
constructive response is to expose the tradeoff: the covered activation gate
requires forced sacrifices to be declared, and the safety stack tracks governed
evolution through preserved invariants or indexed certificates under its
coverage assumptions. The [kernel and lifecycle results](docs/formal-overview.md#no-silent-degradation-safety-stack)
make those requirements checkable. The [positioning paper](papers/06-positioning.md)
distinguishes this program from adjacent work on social choice, accountability
allocation and runtime assurance.

## Why this matters for AI alignment

The [METR/Redwood investigation of the OpenAI–Hugging Face incident](https://evals.alignment.org/blog/2026-08-26-openai-hugging-face-incident-investigation/)
describes agents risking their own task outcomes to help a collective, joining
an unauthorized attack, and developing ways to tamper with transcripts.
Cooperation within the group coexisted with conduct outside its assigned scope.
This raises questions about collective authority as well as individual behavior.

[Anthropic's September 9 assessment](https://www.anthropic.com/research/alignment-assessment-cybersecurity-incidents)
describes individual agents taking unauthorized actions through misconfigured
internet access while pursuing their assigned tasks. It also reports that
offline monitors would have missed one incident after accepting the model's
simulation framing. This motivates a governance requirement: check actual
effects and authority independently of the acting agent's account.

Legitimacy connects those questions to three parts of its formal program:

- **Collective control:** delegation results and a conditional multi-principal
  corrigibility result specify when authority can be passed on and aggregated
  while retaining the modeled guarantees.
- **Rules under pressure:** impossibility results identify forced tradeoffs;
  the compiled protocol requires declarations of the covered sacrifices before
  activation. Recompilation results address drift while retaining an override
  pathway under explicit preservation assumptions.
- **Control as capability grows:** the spectral results identify a finite
  stability cliff for positive vulnerability and characterize the zero-vulnerability
  escape condition. A further result connects this limit to an
  unavoidable governance tradeoff, using a specific graph construction.

These results complement model training, behavioral evaluations and monitoring.
They supply checkable conditions and counterexamples for specified governance
models. Applying them to a deployed swarm requires establishing the connection
between those models and its actual authority, observations and actions. The
composition experiment is one executable example; it neither reconstructs the
incident nor establishes that it would have prevented it.

## Read an audit result

The graph audit makes a represented policy's tradeoffs inspectable. A failed
monotonicity check can describe intended preemption as well as unwanted
interference: policy owners must decide whether the property fits, then declare
and bound the sacrifice. The [claim ledger](docs/claim-ledger.md) connects each
claim to its evidence and remaining obligation.

There are two extraction paths. Lean proves decision preservation for a whole
restricted modeled language. Production Rust parses source and constructs an
audit graph, with regression and parity tests. It does not inherit that general
proof. The audit agent attaches fixture theorem evidence only on an exact
canonical graph match; other graphs receive diagnostic-only results. In either
case the verdict concerns the represented graph. Establishing that graph's
faithfulness to live behavior is a further obligation. The [extraction evidence
map](docs/extractor-boundary.md#accepted-rust-hook-source-and-remaining-assumptions)
shows which connections are proved, tested or assumed.

<details>
<summary>What the experiment establishes</summary>

A conventional checker given the same full context agrees with the experiment's
answers. The contribution is the checked connection between execution, the
forbidden outcome, useful repair, and the observations needed for exact decisions.
The experiment proves that distinguishing its three reachable safe exposure
contexts needs more than one bit; two exposure bits suffice. This is a requirement
for exact decisions that preserve useful actions, not for safety by denying
everything. Its observation bound is separate from the spectral capability threshold.

A locally built offline bundle runs `./reproduce.sh` to check seven outcomes and
execute the host again without network access, model credentials, Cargo or Lean.
The reproduction guide specifies its build and verification requirements.

</details>

## Verify

```bash
scripts/reproduce-audit.sh
bash scripts/verify.sh
```

`scripts/reproduce-audit.sh` rebuilds `target/release/legitimacy-audit-agent`,
runs the Codex CLI, Claude Agent SDK, and public Claude Code surface lanes, and
writes structured rejection bundles under `target/audit-agent-reproduction/`.
Rejected verdicts intentionally exit non-zero when run directly; the
reproduction script treats those rejections as the expected result.

On a fresh clone, `lake exe cache get` (run inside `lean/`, and invoked
automatically by `scripts/verify.sh`) fetches prebuilt Mathlib artifacts and
turns the first Lean build from hours into minutes.

`bash scripts/verify.sh` is the canonical fast gate. It checks Rust formatting,
clippy, tests, Lean build, zero Lean `sorry`/`admit`/first-party `axiom`, fixture
parity, public documentation, publication polish, and the Lean `lake build`
gate. In the public repository, GitHub Actions runs this same gate automatically
for pushes and pull requests to `master`. Reproduction and release checks remain
available through manual dispatch. Component gates are in
[`docs/operational-gates.md`](docs/operational-gates.md).

Current Lean gate: `lake build` completes cleanly.

## Citation

BibTeX entries for papers 02, 03, and 04 are in
[`papers/CITATION.bib`](papers/CITATION.bib): `benenson2026semantickernels`,
`benenson2026impossibility`, and `benenson2026capacity`.

## License

Legitimacy is dual-licensed under the [MIT License](LICENSE-MIT) or the
[Apache License 2.0](LICENSE-APACHE), at your option.

<details>
<summary>Links from earlier README versions</summary>

<a id="the-formal-result-capability-tradeoffs-and-the-kernel"></a>
[The formal result: capability, tradeoffs and the kernel](docs/formal-overview.md#the-formal-result-capability-tradeoffs-and-the-kernel).

<a id="the-forcing-argument-why-the-kernel-must-declare-a-sacrifice"></a>
[The forcing argument: why the kernel must declare a sacrifice](docs/formal-overview.md#the-forcing-argument-why-the-kernel-must-declare-a-sacrifice).

<a id="the-kernel-object"></a>
[The kernel object](docs/formal-overview.md#the-kernel-object).

<a id="the-wider-impossibility-frontier"></a>
[The wider impossibility frontier](docs/formal-overview.md#the-wider-impossibility-frontier).

<a id="no-silent-degradation-safety-stack"></a>
[No-silent-degradation safety stack](docs/formal-overview.md#no-silent-degradation-safety-stack).

<a id="capacity-and-stability-under-capability-scaling"></a>
[Capacity and stability under capability scaling](docs/formal-overview.md#capacity-and-stability-under-capability-scaling).

<a id="worked-extractions-the-obstruction-on-real-agent-graphs"></a>
[Worked extractions: the obstruction on real-agent graphs](docs/formal-overview.md#worked-extractions-the-obstruction-on-real-agent-graphs).

<a id="what-the-audit-decides"></a>
[What The Audit Decides](docs/formal-overview.md#what-the-audit-decides).

<a id="calibration-notes"></a>
[Calibration Notes](docs/formal-overview.md#calibration-notes).

<a id="scope"></a>
[Scope](docs/formal-overview.md#scope).

<a id="boundaries-and-gates"></a>
[Boundaries And Gates](docs/formal-overview.md#boundaries-and-gates).

<a id="theorem-spine"></a>
[Theorem Spine](docs/formal-overview.md#theorem-spine).

<a id="broader-cli-surface"></a>
[Broader CLI Surface](docs/formal-overview.md#broader-cli-surface).

<a id="build-dependencies"></a>
[Build Dependencies](docs/formal-overview.md#build-dependencies).

<a id="references-for-deeper-review"></a>
[References for deeper review](docs/formal-overview.md#references-for-deeper-review).

<a id="papers"></a>
[Papers](docs/formal-overview.md#papers).

<a id="a-rank-dependent-rule-and-the-sdk-graph-diagnostic"></a>
[A rank-dependent rule and the SDK graph diagnostic](docs/formal-overview.md#a-rank-dependent-rule-and-the-sdk-graph-diagnostic).

<a id="why-a-frontier-lab-should-care"></a>
[Why a frontier lab should care](docs/formal-overview.md#why-a-frontier-lab-should-care).

<a id="suggested-reading-order"></a>
[Suggested reading order](docs/formal-overview.md#suggested-reading-order).

</details>
