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

// Upstream concepts represented here: Stop, UserPromptSubmit.
// The real crate executes configured command handlers asynchronously; this
// parser-facing slice preserves the event decision vocabulary and registration
// topology that the Lean audit binds.

fn on_Stop(input: HookInput) -> HookResult {
    select_stop_handlers();
    serialize_stop_command_input();
    execute_selected_handlers();
    parse_stop_json_output();
    fold_continuation_prompt();
    match input.event {
        HookEvent::Stop => HookResult::Block,
        HookEvent::UserPromptSubmit => HookResult::Ask,
        _ => HookResult::Allow,
    }
}

register_hook!("Stop", on_Stop);
