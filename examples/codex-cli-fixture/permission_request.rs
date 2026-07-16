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

// Upstream concepts represented here: PermissionRequest, PreToolUse.
// The real crate executes configured command handlers asynchronously; this
// parser-facing slice preserves the event decision vocabulary and registration
// topology that the Lean audit binds.

fn on_PermissionRequest(input: HookInput) -> HookResult {
    validate_permission_request_matchers();
    serialize_permission_request_command_input();
    execute_selected_handlers();
    resolve_permission_request_decision();
    deny_wins_permission_fold();
    match input.event {
        HookEvent::PermissionRequest => HookResult::Deny,
        HookEvent::PreToolUse => HookResult::Ask,
        _ => HookResult::Allow,
    }
}

register_hook!("PermissionRequest", on_PermissionRequest);
