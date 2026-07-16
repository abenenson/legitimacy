# Public graph fixtures

These checked graph snapshots are stable public examples for the README and
CLI. They instantiate the diagnostic surface on source-walked governance graphs
derived from open-source agent harnesses, without requiring the broader
development audit archive to be present in the public repository.

- `codex-graph.json` — Codex hook-surface governance graph (16 nodes / 8 edges).
- `claude-agent-sdk-graph.json` — Claude Agent SDK hook-surface governance graph (22 nodes / 8 edges).
- `claude-code-graph.json` — Claude Code public hook/settings/command governance metadata graph (31 nodes / 14 edges).

## Fixture provenance

### `codex-graph.json`

- Source repo: `https://github.com/openai/codex`
- Source commit: `326e31ab65dcbdf70c4a034b7adc5c8bd335d996`
- Source surface: the `examples/codex-cli-fixture/` RustHookCore formal slice (see `examples/codex-cli-fixture/UPSTREAM.md`); this committed graph is a frozen `audit-agent` replay fixture, replayed rather than re-walked by the current grammar.
- Graph hash: `sha256:7eea523bb24362cb...` (16 nodes / 8 edges)
- License: Apache-2.0
- Note: the older `audits/leaderboard/codex-graph.json` (10 nodes / 5 edges, source commit `67849d95`, hash `0eedb5e9...`) is a separate synthetic-probe extract over the narrower `audits/fixtures/sources/leaderboard/codex-hooks` slice, used by the §6.3 leaderboard lane — not this panel fixture.

### `claude-agent-sdk-graph.json`

- Source repo: `https://github.com/anthropics/claude-agent-sdk-python`
- Source commit: `8348d1f882bc9033aba5d85ac005a2075f812389`
- Internal fixture extraction command: `legitimacy extract audits/fixtures/sources/leaderboard/claude-agent-sdk-hooks --emit-graph examples/graphs/claude-agent-sdk-graph.json`
- Graph hash: `sha256:ff2a3d4c539d8c9ad602dec9068db97d6bd63494dbbf7c09e67a8ec64820f929`
- License: MIT

### `claude-code-graph.json`

- Source surface: public Claude Code hook, settings, and slash-command metadata.
- Public repository: `https://github.com/anthropics/claude-code`
- Source commit: `8bdbb7296d3fa2217283d3ef94452dd64097393b`
- Fixture provenance: `examples/claude-code-fixture/UPSTREAM.md`
- Graph hash: `sha256:09daa4687eda7ef4b86b5055cc55f2a8f218a4252ea23732d5645dffd4e08671`
- Source redistribution: metadata-only; this repository does not redistribute proprietary Claude Code handler implementation.

## Public reconstruction from upstream

The commands above document how the checked snapshots were produced from the
internal fixture slices. External users can reconstruct the same public source
walk from upstream commits without the audit fixture archive:

```bash
git clone https://github.com/openai/codex /tmp/codex
git -C /tmp/codex checkout 67849d950d843c954102adb0db0e11f993aefdb7
legitimacy extract /tmp/codex/codex-rs/hooks/src/events --emit-graph codex-graph.json

git clone https://github.com/anthropics/claude-agent-sdk-python /tmp/claude-agent-sdk-python
git -C /tmp/claude-agent-sdk-python checkout 8348d1f882bc9033aba5d85ac005a2075f812389
legitimacy extract /tmp/claude-agent-sdk-python/src/claude_agent_sdk --emit-graph claude-agent-sdk-graph.json
```

Run either fixture with:

```bash
legitimacy audit-graph --graph examples/graphs/codex-graph.json --claims-synthetic
legitimacy audit-graph --graph examples/graphs/claude-agent-sdk-graph.json --claims-synthetic
legitimacy audit-graph --graph examples/graphs/claude-code-graph.json --claims-synthetic
```
