# Papers

This directory contains the legitimacy program's papers, organized by the role
each one plays in the published package.

## Reading order

Start with **02** for the thesis. Read **03** for the formal backing. **04**
and **05** are technical companions. **01** and **06** are support material.

### Thesis and formal backing

- [02-semantic-legitimacy-kernels.md](02-semantic-legitimacy-kernels.md) — *Semantic Legitimacy Kernels: A Machine-Checked Compiler Target for the Governance Layer of AI Agents*. Names the formal object and why it must exist as a rule-layer audit target distinct from behavioral evaluation. The conceptual entry point.
- [03-impossibility-theorem.md](03-impossibility-theorem.md) — *A Verified Impossibility Theorem for Peer-Relative Governance*. The canonical formal manuscript: the reachable-scarce-peer-relative impossibility, the semantic kernel bridge, and the extractor contract.

### Technical companions

- [04-spectral-scaling.md](04-spectral-scaling.md) — *Which Governance Structures Survive Unbounded Capability? Capacity and Stability Bounds for AI Governance Graphs*. Capacity converse, Stackelberg asymptotic limit, bifurcation iff, multi-decision generalization, Shannon negative bridge, finite-family RG robustness.
- [05-structural-audits.md](05-structural-audits.md) — rule-layer audit methodology with worked case studies: AI Control, sleeper-agent monotonicity, Constitutional AI lineage, decomposition attacks, the Codex harness.

### Essay and positioning

- [01-what-the-compiler-found.md](01-what-the-compiler-found.md) — general-audience essay. Entry point for readers who want the program at one remove from the formal manuscript.
- [06-positioning.md](06-positioning.md) — prior art and adjacent programs (voting theory, GS-AI, the verification trilemma, ELK/ARC, three-axis triangulation). Reference dossier; informs paper introductions and related-work sections elsewhere.

## Section maps

Section anchors for the longer papers below; each entry is a direct link into
the manuscript.

### 03-impossibility-theorem.md

- [Abstract](03-impossibility-theorem.md#abstract)
- [§1 Formal Object: Legitimacy Kernels](03-impossibility-theorem.md#1-formal-object-legitimacy-kernels)
- [§2 Three-Diagnostic Obstruction Theorem](03-impossibility-theorem.md#2-three-diagnostic-obstruction-theorem)
- [§3 Tightness and Escape Characterization](03-impossibility-theorem.md#3-tightness-and-escape-characterization)
- [§4 Semantic Kernel Bridge](03-impossibility-theorem.md#4-semantic-kernel-bridge)
- [§5 Companion Scaling Consequences (Not Used in the Impossibility Proof)](03-impossibility-theorem.md#5-companion-scaling-consequences-not-used-in-the-impossibility-proof)
- [§6 Executable Artifact: Extractor Contract and Audit Demonstration](03-impossibility-theorem.md#6-executable-artifact-extractor-contract-and-audit-demonstration)
- [Appendix A: Formal-anchor and identifier conventions](03-impossibility-theorem.md#appendix-a-formal-anchor-and-identifier-conventions)

### 04-spectral-scaling.md

- [§1 Introduction](04-spectral-scaling.md#1-introduction)
- [§2 Setup](04-spectral-scaling.md#2-setup)
- [§3 Scope and Limitations](04-spectral-scaling.md#3-scope-and-limitations)
- [§4 Capacity Ceiling](04-spectral-scaling.md#4-capacity-ceiling)
- [§5 Stackelberg Stability Ceiling](04-spectral-scaling.md#5-stackelberg-stability-ceiling)
- [§6 Bifurcation Boundary](04-spectral-scaling.md#6-bifurcation-boundary)
- [§7 Multi-decision Generalization](04-spectral-scaling.md#7-multi-decision-generalization)
- [§8 Shannon Negative Bridge](04-spectral-scaling.md#8-shannon-negative-bridge)
- [§9 RG Family Coarse-Graining](04-spectral-scaling.md#9-rg-family-coarse-graining)
- [§10 Conclusion: Certification, Stability, and Coarse-Graining on One Represented Graph](04-spectral-scaling.md#10-conclusion-certification-stability-and-coarse-graining-on-one-represented-graph)

### 05-structural-audits.md

- [§1 Structural Audit Methodology](05-structural-audits.md#1-introduction-structural-audit-methodology)
- [§2 AI Control Case Study and Verdict](05-structural-audits.md#2-ai-control-case-study-and-verdict)
- [§3 Sleeper-agent Monotonicity Test](05-structural-audits.md#3-sleeper-agent-monotonicity-test)
- [§4 Constitutional AI Lineage](05-structural-audits.md#4-constitutional-ai-lineage)
- [§5 Decomposition Attack Bridge](05-structural-audits.md#5-decomposition-attack-bridge)
- [§6 Codex Harness Worked Example](05-structural-audits.md#6-codex-harness-worked-example)
- [§7 Self-Modification Boundary and Lifecycle](05-structural-audits.md#7-self-modification-boundary-and-lifecycle)
- [§8 Conclusion: Rule-layer Audits as a Program](05-structural-audits.md#8-conclusion-rule-layer-audits-as-a-program)

### 06-positioning.md

- [§1 Positioning the Program](06-positioning.md#1-introduction-positioning-the-program)
- [§2 Prior Art and Adjacent Programs](06-positioning.md#2-prior-art-and-adjacent-programs)
- [§3 ELK / ARC Alignment Positioning](06-positioning.md#3-elk--arc-alignment-program-positioning)
- [§4 GS-AI Verifier Positioning](06-positioning.md#4-gs-ai-verifier-positioning)
- [§5 Verification Trilemma](06-positioning.md#5-verification-trilemma)
- [§6 Two C* Notions](06-positioning.md#6-two-c-notions)
- [§7 Three-axis Triangulation](06-positioning.md#7-three-axis-triangulation)
- [§8 Where This Program Sits](06-positioning.md#8-conclusion-where-this-program-sits)

## Citation

BibTeX entries for the three primary papers are in [`CITATION.bib`](CITATION.bib): `benenson2026semantickernels`, `benenson2026impossibility`, and `benenson2026capacity`. Rendered PDFs are attached to
the public [release](https://github.com/abenenson/legitimacy/releases) for each
tagged version starting with `v1.0.0`; the canonical sources are the markdown
files in this directory.

The BibTeX notes reference the final `v1.0.0` release. arXiv identifiers are
added when assigned.
