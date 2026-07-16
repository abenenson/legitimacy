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

// Upstream concepts represented here: PostToolUse, PreToolUse, Stop.
// The real crate executes configured command handlers asynchronously; this
// parser-facing slice preserves the event decision vocabulary and registration
// topology that the Lean audit binds.

fn on_PostToolUse(input: HookInput) -> HookResult {
    validate_post_tool_matchers();
    serialize_post_tool_use_command_input();
    execute_selected_handlers();
    parse_post_tool_use_json_output();
    collect_feedback_messages();
    match input.event {
        HookEvent::PostToolUse => HookResult::Ask,
        HookEvent::Stop => HookResult::Deny,
        _ => HookResult::Allow,
    }
}

register_hook!("PostToolUse", on_PostToolUse);
