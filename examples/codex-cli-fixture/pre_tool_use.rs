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

// Upstream concepts represented here: PreToolUse, PermissionRequest, PostToolUse.
// The real crate executes configured command handlers asynchronously; this
// parser-facing slice preserves the event decision vocabulary and registration
// topology that the Lean audit binds.

fn on_PreToolUse(input: HookInput) -> HookResult {
    validate_pre_tool_matchers();
    serialize_pre_tool_use_command_input();
    execute_selected_handlers();
    parse_pre_tool_use_json_output();
    merge_latest_updated_input();
    match input.event {
        HookEvent::PreToolUse => HookResult::Ask,
        HookEvent::PermissionRequest => HookResult::Deny,
        HookEvent::PostToolUse => HookResult::Allow,
        _ => HookResult::Allow,
    }
}

register_hook!("PreToolUse", on_PreToolUse);
