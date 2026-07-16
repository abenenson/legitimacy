# Governance Corpus Ground-Truth Protocol

This protocol defines the review evidence required to promote governance-corpus
rows beyond the heuristic tier. It is corpus-scoped: reviewer labels describe the
pinned harness revision recorded in `source.lock`, not a floating upstream
branch.

## Review Roles

Every high-value harness requires two independent reviewers before promotion to
`reviewed`. If a corpus row uses duplicated reviewer files as a schema fixture
or seed answer key, it must be labeled as a curated answer key and must not be
described as independent inter-rater agreement.

- Reviewer A and Reviewer B label the harness without consulting each other.
- Each reviewer writes a separate graph file under
  `audits/corpus/<harness>/ground_truth/reviewer_a.graph.toml` or
  `audits/corpus/<harness>/ground_truth/reviewer_b.graph.toml`.
- The adjudicator writes
  `audits/corpus/<harness>/ground_truth/adjudication.toml` after comparing both
  label sets.
- The promoted consensus graph is copied to
  `audits/corpus/<harness>/ground_truth.graph.toml`.

Reviewers may inspect extractor output, but the label is the reviewer's source
reading of the pinned harness. Extractor output is evidence to audit, not the
answer key.

## Label Graph Schema

Each reviewer file uses TOML and must include:

```toml
[ground_truth]
status = "reviewed"
harness_id = "codex"
reviewer_id = "reviewer_a"
source_commit = "67849d950d843c954102adb0db0e11f993aefdb7"
reviewed_at = "2026-05-04T00:00:00Z"

[[node]]
id = "relative/path.py::approval_gate"
kind = "binary"
decision_fields = ["permissionDecision"]
default_decision = "permit"
source_span = "relative/path.py:10-24"
notes = "Why this source span is a governance node."

[[edge]]
from = "relative/path.py::registration::PreToolUse::approval_gate"
to = "relative/path.py::approval_gate"
kind = "dispatch"
source_span = "relative/path.py:5-8"
notes = "Registration dispatches this event to the callback."

[[decision]]
node = "relative/path.py::approval_gate"
predicate = "permissionDecision == deny"
decision = "deny"
source_span = "relative/path.py:14-15"
```

Node and edge ids must match the extractor's stable ids where possible. When a
reviewer finds a source-faithful concept that the extractor cannot name, the id
must be stable, path-relative, and documented in `notes`.

## Adjudication

The adjudication file records every disagreement:

```toml
[adjudication]
harness_id = "codex"
status = "resolved"
adjudicator_id = "adjudicator_1"
resolved_at = "2026-05-04T00:00:00Z"
cohen_kappa_nodes = 1.0
cohen_kappa_edges = 1.0

[[disagreement]]
kind = "edge"
item = "relative/path.py::registration::PreToolUse::approval_gate -> relative/path.py::approval_gate"
reviewer_a = "present"
reviewer_b = "absent"
resolution = "present"
rationale = "Registration table directly dispatches to the callback."
```

Promotion requires all disagreements to have a resolution and rationale.

## Inter-Rater Agreement

For each harness, compute agreement before adjudication.

- Nodes: compare the union of node ids from both reviewers as binary
  present/absent labels.
- Edges: compare the union of `(from, to, kind)` tuples as binary
  present/absent labels.
- Decisions: compare the union of `(node, predicate, decision)` tuples as
  binary present/absent labels.

The primary metric is Cohen's kappa per item family. A harness is eligible for
reviewed-ground-truth promotion when node kappa and edge kappa are both at
least `0.80` before adjudication and adjudicated node and edge precision/recall
against the extractor are both above `0.90`.

If a family has no positive or negative contrast because both reviewers made the
same empty label set, record `kappa = 1.0` and explain why the empty set is
source-faithful.

## Reviewed-Ground-Truth Promotion

Promotion to `reviewed` requires:

1. Two independent reviewer graph files.
2. An adjudication file with node and edge kappa.
3. A consensus `ground_truth.graph.toml`.
4. `review_notes.md` comparing extracted graph items against the consensus.
5. Node precision, node recall, edge precision, and edge recall all greater
   than `0.90`.
6. `manifest.toml` updated to `evidence_tier = "reviewed"`.

Reviewed promotion does not imply a theorem-backed modeled extractor proof. If
a checked PythonHookCore modeled witness exists and is included in the Lake
corpus theorem target, use `theorem-backed-modeled` instead of `reviewed`.

## Curated Answer-Key Files

Curated answer-key files may be useful as extractor smoke fixtures, but they are
not independent review evidence. Their review notes should say "curated answer
key", omit inter-rater claims, and treat kappa values as schema-agreement
checks only.

## Theorem-Backed Promotion

Theorem-backed rows must state which artifact the proof covers.

`theorem-backed-modeled` rows require a checked Lean `Program` model and a
witness tying that model to the extracted graph semantics. This tier proves the
extractor's behavior on the modeled source core; it is not, by itself, a
byte-level theorem that the model is complete for the pinned upstream harness.
Source-faithfulness for the model remains a separate reviewed-ground-truth or
byte-witness obligation unless the row explicitly records such a bridge.

`theorem-backed-source-walk` rows require a checked Lean theorem or witness over
the same graph artifact produced by the source-walk extraction row. The theorem
graph and source-walk graph must name the same source-relative node set.

`theorem-backed` is a deprecated alias retained only for older artifacts. New
corpus rows must use `theorem-backed-modeled` or
`theorem-backed-source-walk`.

For PythonHookCore rows:

1. Model the source surface as a Lean `Program`.
2. Use `extractPythonHookCore_decision_equivalent` or a fixture theorem derived
   from it.
3. Store the Lean witness under
   `audits/corpus/<harness>/theorem/PythonHookCoreProgram.lean`.
4. Ensure `cd lean && lake build` compiles the corpus theorem target; this also
   rejects `sorry`, `admit`, and local `axiom` declarations in corpus theorem
   witness files.
5. Run `legitimacy extract --mode theorem-backed` over the modeled source slice.
6. Store the graph and witness metadata under
   `audits/corpus/<harness>/theorem/`.
7. Update `manifest.toml` and `extractor_report.json` to
   `evidence_tier = "theorem-backed-modeled"`.

## Adversarial Fixtures

Each adversarial fixture must pair source with `<fixture>.expected.json`.

```json
{
  "schema_version": 1,
  "fixture_id": "dead-code/001_if_false_deny",
  "property": "dead_code_does_not_create_decision_gate",
  "should_hold": true,
  "evidence_tier": "heuristic",
  "expected_nodes": [],
  "expected_edges": [],
  "notes": "The unreachable branch must not affect extracted decisions."
}
```

`should_hold = true` means the extractor is expected to satisfy the fixture
property. `should_hold = false` means the fixture is an expected failure or
regression capture and must include a rationale in `notes`.
