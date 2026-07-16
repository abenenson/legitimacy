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

// Upstream concepts represented here: SessionStart, PreToolUse, PermissionRequest, PostToolUse, UserPromptSubmit, Stop, PreCompact, PostCompact.
// The real crate executes configured command handlers asynchronously; this
// parser-facing slice preserves the event decision vocabulary and registration
// topology that the Lean audit binds.

fn on_PostCompact(input: HookInput) -> HookResult {
    discover_configured_handlers();
    discover_plugin_handlers();
    apply_managed_hook_policy();
    apply_hook_trust_policy();
    build_hooks_registry();
    list_hooks_for_catalog();
    match input.event {
        HookEvent::PermissionRequest => HookResult::Ask,
        HookEvent::PreToolUse => HookResult::Ask,
        HookEvent::PostToolUse => HookResult::Ask,
        _ => HookResult::Allow,
    }
}

register_hook!("PostCompact", on_PostCompact);
