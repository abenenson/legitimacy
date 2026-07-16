# Governance Corpus v1

The governance corpus is the pinned benchmark surface for extractor evaluation.
It records upstream source provenance, license status, extractor coverage, and
the evidence tier attached to each harness.

Phase 1 status:

- 20 priority harnesses are pinned in `manifest.toml`.
- 5 harnesses carry theorem-backed modeled-witness artifacts through the corpus
  theorem target.
- 4 harnesses reuse local frozen source slices and have generated heuristic
  extractor reports.
- 16 harnesses are pointer-pinned to license-compatible upstream commits and
  carry pending extractor reports until redistributable source slices are added.
- 20 adversarial fixtures across 3 populated families live under
  `adversarial/`.

## Manifest Schema

The canonical manifest is [`manifest.toml`](manifest.toml). It starts with the
corpus metadata block:

```toml
[corpus]
version = "v1"
generated_at = "2026-05-03T23:16:25Z"
extractor_version = "legitimacy 0.1.0 heuristic"
```

Each admitted harness appends one `[[harness]]` table:

```toml
[[harness]]
id = "example-agent"
source_repo = "https://github.com/example/example-agent"
source_commit = "0123456789abcdef0123456789abcdef01234567"
license = "MIT"
extraction_mode = "heuristic"
evidence_tier = "heuristic"
coverage_pct = 100.0
unsupported_constructs = []
verdict_summary = "Synthetic structural probe completed in heuristic mode."
```

Every harness has a matching directory at `audits/corpus/<id>/` with:

- `source.lock`: pinned source URL, commit, license, extraction input, and
  benchmark admission notes.
- `license.md`: full license text or a pointer to the upstream license at the
  pinned commit.
- `ground_truth.graph.toml`: curated-answer-key placeholder until reviewed
  labels are added that provide ground truth.
- `extractor_report.json`: machine-readable extractor coverage and verdict
  summary.
- `observed_runtime_claims.jsonl`: empty placeholder unless public runtime
  traces are available.

## Evidence Tiers

`theorem-backed` rows are modeled-program-checked per the
[`GROUND_TRUTH_PROTOCOL.md`](GROUND_TRUTH_PROTOCOL.md): a checked Lean `Program`
model and witness artifact tie the modeled source core to the extracted graph
semantics. This tier is not, by itself, a byte-level theorem that the model is
complete for the pinned upstream harness; source faithfulness remains a separate
reviewed-ground-truth or byte-witness obligation unless the row explicitly
records such a bridge.

`reviewed` rows have human-reviewed ground-truth labels but no theorem-backed
extractor witness. The manifest value is `reviewed`; prose may call this
`reviewed-ground-truth` only when the row has genuine independent reviewer
labels. The current v1 answer-key files are duplicated schema fixtures and do
not establish independent inter-rater agreement.

`heuristic` rows are automatic extractor outputs. They are valid benchmark
inputs, but their verdicts are exploratory until promoted by review or proof.

The theorem-backed tier is populated: five v1 governance-corpus rows carry
PythonHookCore theorem-witness artifacts generated from small Lean-compatible
program models, matching the theorem-backed modeled lane in the leaderboard.
Remaining v1 rows stay heuristic unless promoted by reviewed ground truth or a
corpus-scoped theorem witness. Existing legacy Lean theorems remain regression
evidence for frozen fixtures.

## Ground-Truth Labeling Protocol

Curated answer-key labels are recorded in `ground_truth.graph.toml`. Until
reviewer labeling is complete, each file is a placeholder:

```toml
[ground_truth]
status = "unreviewed"
```

Promotion to `reviewed` requires documented reviewer labels listing the expected
governance nodes, edges, aliases, and verdict-affecting unsupported constructs.
Promotion to `theorem-backed` additionally requires a checked witness binding
the pinned source, extracted graph, and verdict.

## Contribution Protocol

1. Pin the upstream source with a full commit SHA.
2. Confirm the license is compatible with benchmark redistribution or record a
   pointer-only license file when source redistribution is not needed.
3. Run `legitimacy extract --synthetic <harness-source-path>` and store the
   report as `extractor_report.json`.
4. Leave `ground_truth.graph.toml` empty except for explicit placeholder
   metadata until a reviewer supplies labels, or label it explicitly as a
   curated answer key when it is not independently reviewed.
5. Do not add new corpus inputs under `audits/fixtures/sources/leaderboard/`;
   that path is frozen for legacy leaderboard fixtures.

## Adversarial Fixtures

`adversarial/README.md` defines ten fixture families. Phase 1 populates:

- `misleading-literals`: comments, strings, docstrings, and logs that look like
  hook decisions but must not create governance evidence.
- `renamed-fields`: semantically relevant allow/deny fields whose names differ
  from the extractor's easiest keyword path.
- `dead-code`: syntactically visible governance branches that are unreachable.

Each fixture pairs source with a `.expected.json` file declaring whether the
structural property should hold or fail. As of 2026-05-04, no verification gate
iterates these `.expected.json` files directly; they are a reference inventory
for adversarial behaviors, not a separate extractor test suite or new
leaderboard source pack. Handwritten extractor tests cover the same families in
`tests/extract_*.rs`:

| Fixture | Direct fixture reference | Closest handwritten coverage |
| --- | --- | --- |
| `misleading-literals/001_comment_decoy.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_ignores_misleading_comments_and_docstrings`; `tests/extract_rust_hook_core.rs::theorem_backed_rust_core_ignores_misleading_comments_and_dead_code` |
| `misleading-literals/002_docstring_decoy.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_ignores_misleading_comments_and_docstrings` |
| `misleading-literals/003_log_message_decoy.py` | none | `tests/extract_typescript_approval_core.rs::theorem_backed_typescript_core_ignores_unsupported_words_in_comments_and_strings` |
| `misleading-literals/004_fixture_literal_decoy.py` | none | `tests/extract_typescript_approval_core.rs::theorem_backed_typescript_core_ignores_misleading_register_approver_text` |
| `misleading-literals/005_error_text_decoy.py` | none | `tests/extract_typescript_approval_core.rs::theorem_backed_typescript_core_ignores_unsupported_words_in_comments_and_strings` |
| `misleading-literals/006_test_name_decoy.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_rejects_substring_registration_decorators`; `tests/extract_python_hook_core.rs::theorem_backed_python_core_rejects_substring_decision_annotations` |
| `misleading-literals/007_json_blob_decoy.py` | none | `tests/extract_typescript_approval_core.rs::theorem_backed_typescript_core_ignores_misleading_register_approver_text` |
| `renamed-fields/001_allow_clean.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_discovers_renamed_decision_fields_from_types` |
| `renamed-fields/002_blocked_reason_alias.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_discovers_renamed_decision_fields_from_types` |
| `renamed-fields/003_approval_granted.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_discovers_renamed_decision_fields_from_types` |
| `renamed-fields/004_safe_to_run.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_discovers_renamed_decision_fields_from_types` |
| `renamed-fields/005_review_required.py` | none | `tests/extract_decision_conformance.rs::python_hook_core_conformance_maps_supported_escalation_literals`; `tests/extract_decision_conformance.rs::typescript_approval_core_conformance_maps_escalation_literals` |
| `renamed-fields/006_override_ok.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_discovers_renamed_decision_fields_from_types` |
| `renamed-fields/007_forbid_dirty.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_discovers_renamed_decision_fields_from_types` |
| `dead-code/001_if_false_deny.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_ignores_semantically_dead_returns`; `tests/extract_rust_hook_core.rs::theorem_backed_rust_core_ignores_misleading_comments_and_dead_code` |
| `dead-code/002_return_before_hook.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_ignores_semantically_dead_returns` |
| `dead-code/003_constant_guard.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_ignores_semantically_dead_returns` |
| `dead-code/004_unreachable_exception.py` | none | no direct handwritten analog; the `.expected.json` records the current limitation |
| `dead-code/005_never_called_nested_hook.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_rejects_shadowed_registered_callbacks` |
| `dead-code/006_after_raise.py` | none | `tests/extract_python_hook_core.rs::theorem_backed_python_core_ignores_semantically_dead_returns` |
