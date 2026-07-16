# Claude Code Hooks Observed-Runtime Metadata

This directory records public-source structural facts for Claude Code hook
examples without redistributing proprietary Anthropic source. The source files
are public-readable for reproducibility, but they are not copied into this repo
or used as redistributable fixtures.

## Source Snapshot

- Repository: https://github.com/anthropics/claude-code
- Commit: `c128568da0ecb75a5f17bbded2d558da5152ba8e`
- Security hook URL: https://github.com/anthropics/claude-code/blob/c128568da0ecb75a5f17bbded2d558da5152ba8e/plugins/security-guidance/hooks/security_reminder_hook.py
- Bash validator URL: https://github.com/anthropics/claude-code/blob/c128568da0ecb75a5f17bbded2d558da5152ba8e/examples/hooks/bash_command_validator_example.py

## Structural Facts

`plugins/security-guidance/hooks/security_reminder_hook.py`

- SHA-256: `a86fcbcf727d4b32d780c36697b595ae850d48e0ebd18d0d3784cad98fb0f64f`
- Line count: 280
- Lines 31-129 define 9 security-pattern records.
- Lines 187-200 scan command/content against those patterns.
- Lines 202-215 extract command/content from tool inputs.
- Lines 218-276 implement the hook entrypoint.
- Documented tool surface: `Bash`, `Edit`, `Write`, `MultiEdit`.
- Exit-code structure: `0` allows; `2` blocks with guidance.

`examples/hooks/bash_command_validator_example.py`

- SHA-256: `0d7a9468405bb614ebddfb56037217cd9282a8045ea87a42cf6ff4099a61820d`
- Line count: 83
- Lines 14-24 document `PreToolUse` / `Bash` hook configuration.
- Lines 36-45 define validation regexes.
- Lines 48-53 implement command validation.
- Lines 57-80 implement the hook entrypoint.
- Exit-code structure: `0` for clean/non-Bash/empty input; `1` for invalid JSON; `2` blocks invalid Bash commands.

## Verdict Scope

This row is structurally documented only. A runtime verdict requires either a
redistributable source/trace corpus or Anthropic-side audit collaboration. The
metadata is sufficient to reproduce the observed corpus shape and legal boundary,
but it is not claimed as a computed observed-runtime audit verdict.
