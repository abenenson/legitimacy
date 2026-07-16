enum HookResult {
    Allow,
    Deny,
    Ask,
    Block,
}

fn on_UserPromptSubmit(input: HookInput) -> HookResult {
    match input.event {
        "UserPromptSubmit" => HookResult::Block,
        _ => HookResult::Allow,
    }
}

register_hook!("UserPromptSubmit", on_UserPromptSubmit);
