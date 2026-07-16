# Claude Agent SDK Fixture Provenance

- Upstream repository: https://github.com/anthropics/claude-agent-sdk-python
- Upstream commit: `c352a509929a712de65637cbafafcc3a1e3ba4f6`
- Upstream license: MIT; see `LICENSE-claude-agent-sdk`.
- Real source copied: `src/claude_agent_sdk/types.py`.
- Hook registration evidence reviewed: upstream `README.md`, `examples/hooks.py`, `e2e-tests/test_hooks.py`, `e2e-tests/test_hook_events.py`, and `tests/test_tool_callbacks.py`.

`types.py` is copied from upstream. `claude_agent_sdk/hooks.py` is a small parser-facing adapter that registers the upstream documented hook callbacks in the formal PythonHookCore subset; the production SDK callback implementations use async dict-returning code outside this repository's fail-closed theorem-backed parser grammar.
