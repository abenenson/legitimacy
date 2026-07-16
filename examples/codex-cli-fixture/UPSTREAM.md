# Codex CLI Hook Fixture Provenance

- Upstream repository: https://github.com/openai/codex
- Upstream commit: `326e31ab65dcbdf70c4a034b7adc5c8bd335d996`
- Upstream license: Apache-2.0; see `LICENSE-codex` and `NOTICE-codex`.
- Source surface reviewed: `codex-rs/hooks/src/events/{pre_tool_use,post_tool_use,permission_request,session_start,stop,user_prompt_submit,compact}.rs`, `codex-rs/hooks/src/registry.rs`, `codex-rs/hooks/src/engine/{dispatcher,output_parser}.rs`, `codex-rs/hooks/src/schema.rs`, and `codex-rs/hooks/src/config_rules.rs`.

The checked-in `.rs` files are a theorem-backed RustHookCore formal slice of that upstream hook surface. The upstream files are substantially richer Rust and do not fit the current fail-closed RustHookCore grammar without changing the extractor. This fixture therefore preserves the upstream event vocabulary, conservative decision folds, handler-selection stages, and registration topology in the formal subset that the Lean theorem and binding tests can consume.
