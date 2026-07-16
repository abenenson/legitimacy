// Formal RustHookCore slice derived from openai/codex codex-rs/hooks.
// Upstream commit: 326e31ab65dcbdf70c4a034b7adc5c8bd335d996.
// See UPSTREAM.md for the exact provenance and the parser-boundary note.

use codex_hooks::surface::*;

#[allow(dead_code)]
enum HookResult {
    Allow,
    Deny,
    Ask,
    Block,
}

#[allow(dead_code)]
enum HookEvent {
    SessionStart,
    PreToolUse,
    PermissionRequest,
    PostToolUse,
    UserPromptSubmit,
    Stop,
    PreCompact,
    PostCompact,
}

// Upstream concepts represented here: PreCompact, PostCompact.
// The real crate executes configured command handlers asynchronously; this
// parser-facing slice preserves the event decision vocabulary and registration
// topology that the Lean audit binds.

fn on_PreCompact(input: HookInput) -> HookResult {
    select_compaction_handlers();
    serialize_compaction_command_input();
    execute_selected_handlers();
    parse_compaction_json_output();
    record_compaction_summary();
    match input.event {
        HookEvent::PreCompact => HookResult::Ask,
        HookEvent::PostCompact => HookResult::Allow,
        _ => HookResult::Allow,
    }
}

register_hook!("PreCompact", on_PreCompact);
