# What the Legitimacy Compiler Found

*Adam Benenson, 2026*

---

## Citation conventions

Backticked identifiers outside the following exemption categories are expected
to resolve to a first-party Lean/Rust/test declaration. Fixture field names and
probe label tokens such as `block_reason`, `hook_registration`,
`model_not_found`, `skillPrelude`, `bottleneck11_bi`, and `bottleneck13_bi`
denote literal governance-graph fixture data or probe-bottleneck identifiers,
not universal claims about upstream source semantics.

---

## The setup

A chatbot can be behaviorally aligned: judged on whether its answers are good.
An agent that allocates tool access, memory, escalation rights, or the one
scarce review slot is no longer just answering — it is deciding who gets a
limited resource. That is an institutional decision, and an institution has to
be legitimate, not just well-behaved. Alignment is therefore not only a
behavioral problem. It is also a legitimacy problem.

A concrete picture makes the failure mode visible. An agent decides whether to
permit a shell command or escalate it for human review, and there is one review
slot this cycle — that is the scarcity. The gate weighs all pending requests
together — that is the peer-relativity. Now Request A gathers stronger evidence
and is plainly worth approving; strengthening A consumes the scarce review slot,
and Request B, which would have been permitted, flips from Permit to Deny.
Making one decision more correct silently broke another. No model weight
changed; the governance rule did. That is monotonicity failing under scarcity,
and it is the structural pathology this project makes checkable.

The rules that govern durable state transitions — who gets permission, which
action runs, which override takes precedence — are mathematical objects. They
can be consistent or inconsistent. They can distribute shocks defensibly or
accidentally. They can reward the strengthening of a claim or punish it.

The formal paper supplies the mathematical object and the impossibility theorem
for a scoped class: reachable structural scarce peer-relative decisive
stages in binary governance pipelines under transparent-prefix and
non-denying-suffix hypotheses (with the older complete first-effective
peer-relative surface as a special case). It does not say that every system with a peer-relative component is
illegitimate, and it does not prove source-code facts by itself.

The compiler is the empirical side of the project. It extracts governance
graphs, runs graph diagnostics, records witnesses, and separates evidence by
tier. That separation is now part of the claim surface:

- **Theorem-backed** evidence is suitable for broad public claims when the
  checked theorem or witness binds the source, graph, and verdict.
- **Reviewed-ground-truth** evidence is suitable for benchmark evaluation after
  reviewers label the graph surface.
- **Heuristic** evidence is exploratory. It can guide engineering and review,
  but it is not a substitute for theorem-backed or reviewed claims.

This essay now uses the phrase "what the compiler found" in that narrower
sense. The compiler found exploratory structural evidence unless a row is
explicitly promoted to a stronger tier.

## What "silent sacrifice" means

The impossibility theorem does not say that governance is impossible. It says
that systems in the scoped reachable/first-effective peer-relative class, where
a transparent prefix reaches the allocator and a non-denying suffix preserves
its permits, cannot keep all the named properties at once. The engineering
requirement is therefore honesty:
declare which property is sacrificed, bound the magnitude, and monitor the
failure mode.

The current heuristic corpus does not prove that any upstream project has made
an undeclared sacrifice. It identifies extracted or pinned surfaces where that
question is worth reviewing. The stronger accusation requires a theorem-backed
or reviewed-ground-truth promotion.

## Current Evidence Lanes

Readers who want the argument rather than the benchmark machinery can skim this
section: the one load-bearing point is that every claim below is tagged
theorem-backed, reviewed-ground-truth, or heuristic, and broad claims wait for
the strongest tier.

### v1 governance corpus

The v1 corpus in `audits/corpus/` pins 20 harnesses with source commits,
license records, extractor reports, and placeholders for reviewed labels and
observed-runtime claims. Four rows reuse local frozen source slices and have
heuristic extractor reports. Sixteen rows are pointer-pinned to upstream commits
with pending extractor reports until redistributable source slices are added.

The corpus is a benchmark inventory first. Its heuristic rows are not broad
claims about the projects named in the manifest. They are structured inputs for
extractor hardening, adversarial evaluation, and reviewer-grade labeling.

### Frozen legacy fixtures

The older leaderboard fixtures for Codex, the public Claude Agent SDK Python
hook surface, CrewAI, AutoGen, and OpenClaw remain useful regression material.
They are byte-stable source slices with committed transcripts and extracted
graph snapshots. Some legacy fixture verdicts also have Lean rejection theorems
over the extracted graph.

Those theorems classify the finite graph inhabitants. They do not, by
themselves, prove that every behavior of the upstream project is faithfully
captured by the extractor. The source-to-graph boundary remains part of the
trusted base unless a corpus witness closes it.

### Observed runtime

Observed-runtime trace packs are a separate lane. The legacy Codex TUI runtime
example remains under `audits/observed-runtime/`, but the current release does
not promote runtime rows. Runtime trace packaging and ground-truth labeling are
reviewer-grade labeling work.

### Specification-level studies

Specification-level policy examples remain useful when the source extractor
does not reconstruct cross-boundary semantics. They should be cited as
specification studies, not automatic source findings.

## Exploratory Findings

The heuristic rows continue to show why the audit is worth building.

Codex, the public Claude Agent SDK Python hook surface, and CrewAI expose
hook-style structural patterns where the extracted graph flags monotonicity
under the current production diagnostic. Codex and CrewAI also flag nonvacuity
on the frozen structural probe. AutoGen is the methodological
counterexample: the hardened extractor currently finds a single approval hook
that passes the synthetic probe.

OpenClaw remains a legacy frozen fixture and specification-study surface, not a
new v1 corpus harness in this release. Its automatic fixture row flags
nonvacuity, while separate specification tests expose additional consistency
and solidarity pressure.

These findings are valuable, but their framing matters. They say:

- the extractor can produce stable, inspectable governance graphs for real
  source slices;
- the graph diagnostics find concrete witnesses on those extracted graphs;
- some results are robust enough to have Lean theorem coverage over the graph;
- the upstream-source claim is only as strong as the extraction-faithfulness
  evidence attached to that harness.

They do not say that the v1 corpus has already proved broad source-level
defects across all named projects.

## Why the Evidence Tiers Matter

Without tiers, benchmark work quietly mixes three different claims:

1. The extractor found a graph.
2. A reviewer agreed that the graph is the right ground truth.
3. A theorem binds the graph and verdict strongly enough to support a formal
   claim.

Those are different claims. The v1 corpus makes the differences explicit.
Building the schema, pinning the harnesses, generating the first reports, and
adding adversarial fixtures produces heuristic evidence. Reviewer labeling
produces reviewed ground truth and runtime trace packs. Theorem-backed
extractor witnesses close the source-to-graph gap for a row.

The resulting standard is intentionally stricter than the old essay. Broad
claims should wait for theorem-backed rows. Heuristic findings should be called
exploratory evidence.

## What the Compiler Does Not Do

The compiler does not audit natural-language constitutions without formal
translation. It does not judge whether encoded values are morally correct. It
does not evaluate model weights. It does not replace security review,
red-teaming, or runtime evals. It audits one specific object: the structure of a
governance rule once that rule has been represented as a graph.

That object is still load-bearing. Many safety arguments presuppose legitimate
governance without checking it. This project checks it, while keeping the
evidence tier visible.

## Where the Field Goes From Here

Short term: run the audit, but publish the tier. A heuristic extraction should
be labeled as heuristic. A reviewed reconstruction should name its reviewers and
label protocol. A theorem-backed finding should name the witness or theorem.

Medium term: declared sacrifices should become routine governance
documentation. The practical question is not "does the system have governance?"
but "which properties does the governance rule sacrifice, by how much, and how
is that monitored?"

Long term: source-to-graph faithfulness should be treated as a first-class
verification target. The end state is not a persuasive essay about AI
governance. It is a benchmark where broad claims are backed by reviewed labels,
runtime traces, and checked witnesses.

## Coda

The compiler does not need to be right about everything. It needs to be honest
about what it has actually checked. The v1 governance corpus is the next step in
that discipline: pinned harnesses, license manifests, extractor reports,
adversarial fixtures, and explicit promotion paths from heuristic evidence to
reviewed and theorem-backed claims.

The constitution needs a compiler. It also needs an evidence label.

---

*Legitimacy is an open-source project: machine-checked semantic legitimacy
kernel with a Rust extractor and Lean 4 proofs. Repository:
https://github.com/abenenson/legitimacy. Formal manuscripts: "Semantic Legitimacy Kernels: A Machine-Checked Compiler Target for the Governance Layer of AI Agents" (the kernel object), "A
Verified Impossibility Theorem for Peer-Relative Governance" (its forcing
argument), and "Which Governance Structures Survive Unbounded Capability?
Capacity and Stability Bounds for AI Governance Graphs" (the capacity and
stability companion).*
