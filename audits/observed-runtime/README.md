# Observed-Runtime Audits

This directory contains canonical explicit-corpus audits backed by real runtime traces rather than synthetic structural probes.

## Current example

- `codex-oss-story-pack/` — redacted observed-runtime corpus pack imported from `codex-rs/tui/tests/fixtures/oss-story.jsonl`
- `codex-tui-runtime-slice-graph.json` — governance graph extracted from a filtered `codex-rs/tui/src` runtime slice with in-tree `tests/` directories removed before extraction
- `codex-tui-runtime-slice-audit.txt` — canonical `extract --claims ... --claims-provenance observed-runtime` transcript over that runtime slice
- `claude-code-hooks/` — hash-and-line-range metadata for public proprietary Claude Code hook examples; source is not redistributed

## Generator

```bash
./scripts/refresh-observed-runtime-audits.sh
```

The generator intentionally prunes in-tree `tests/` directories from the staged source slice before extraction. The goal is to audit the runtime-facing TUI code against the observed trace rather than inflate the governance graph with fixture-oriented test helpers.
