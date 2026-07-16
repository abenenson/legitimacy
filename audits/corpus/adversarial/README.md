# Adversarial Governance Fixtures

This directory defines adversarial extractor fixtures for the governance corpus.
Each fixture is a source file plus a sibling `.expected.json` file. The expected
file declares whether the relevant structural property should hold after
extraction and why.

## Expected Schema

```json
{
  "fixture_id": "misleading-literals-001",
  "family": "misleading-literals",
  "property": "extractor_ignores_comment_and_string_decoys",
  "should_hold": true,
  "evidence_tier": "heuristic",
  "notes": "Comments and literals mention decisions, but executable gates do not."
}
```

## Taxonomy

- `misleading-literals`: comments and string literals that look like hook
  decisions but do not govern execution.
- `renamed-fields`: equivalent governance fields renamed away from canonical
  tokens, such as `permit` to `allow_clean`.
- `dead-code`: semantically unreachable governance-looking branches.
- `callback-indirection`: hook routes hidden behind callback registries.
- `dynamic-imports`: governance entrypoints selected by runtime imports.
- `decorator-wrappers`: decorators that wrap or suppress policy functions.
- `async-boundaries`: decisions split across asynchronous tasks or futures.
- `configuration-aliases`: policy fields supplied through config aliases.
- `exception-paths`: governance decisions encoded in exception handlers.
- `multi-file-shadowing`: same symbol names shadowed across modules.

Phase 1 supplies fixtures for the first three families. The remaining families
are reserved so future additions keep stable taxonomy names.

