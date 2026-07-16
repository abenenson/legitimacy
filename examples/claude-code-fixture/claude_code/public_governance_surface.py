"""Claude Code public governance surface fixture.

This is not Claude Agent SDK code and not closed-source Claude Code handler
implementation. It encodes the public Claude Code hook/settings/command schema
documented at code.claude.com/docs/en/hooks, /settings, and /slash-commands in
the theorem-backed PythonHookCore subset.
"""

from typing import Literal, NotRequired, TypedDict

PermissionDecision = Literal["allow", "deny", "ask", "defer"]
HookDecision = Literal["allow", "deny", "ask", "block"]


class ClaudeCodeSettingsPermissions(TypedDict):
    allow: list[str]
    deny: list[str]
    ask: list[str]
    defaultMode: NotRequired[PermissionDecision]


class ClaudeCodeHookHandler(TypedDict):
    type: Literal["command", "http", "mcp", "prompt", "agent"]
    command: NotRequired[str]
    url: NotRequired[str]
    prompt: NotRequired[str]
    if_: NotRequired[str]


class PreToolUseHookSpecificOutput(TypedDict):
    hookEventName: Literal["PreToolUse"]
    permissionDecision: NotRequired[PermissionDecision]
    permissionDecisionReason: NotRequired[str]


class PermissionRequestHookSpecificOutput(TypedDict):
    hookEventName: Literal["PermissionRequest"]
    permissionDecision: NotRequired[PermissionDecision]
    permissionDecisionReason: NotRequired[str]


class StopHookSpecificOutput(TypedDict):
    hookEventName: Literal["Stop"]
    decision: NotRequired[Literal["block"]]
    reason: NotRequired[str]


class SlashCommandFrontmatter(TypedDict):
    description: str
    argument_hint: NotRequired[str]
    allowed_tools: NotRequired[list[str]]
    model: NotRequired[str]


def pre_tool_use_permission_decision() -> HookDecision:
    validate_matcher_pattern()
    inspect_tool_input()
    return "ask"


def permission_request_decision() -> HookDecision:
    inspect_permission_update_entries()
    return "deny"


def post_tool_use_observation() -> HookDecision:
    add_context_for_claude()
    return "allow"


def user_prompt_submit_guard() -> HookDecision:
    inspect_slash_command_frontmatter()
    return "ask"


def user_prompt_expansion_guard() -> HookDecision:
    inspect_command_argument_hint()
    return "block"


def session_start_policy() -> HookDecision:
    load_settings_scope()
    return "ask"


def setup_policy() -> HookDecision:
    load_managed_policy_settings()
    return "ask"


def instructions_loaded_review() -> HookDecision:
    inspect_loaded_instructions()
    return "ask"


def config_change_review() -> HookDecision:
    inspect_settings_json_update()
    return "ask"


def subagent_start_review() -> HookDecision:
    inspect_agent_frontmatter()
    return "ask"


def subagent_stop_review() -> HookDecision:
    inspect_agent_result()
    return "allow"


def stop_continuation() -> HookDecision:
    require_continuation_reason()
    return "block"


def pre_compact_review() -> HookDecision:
    inspect_compaction_trigger()
    return "ask"


def notification_review() -> HookDecision:
    inspect_notification_type()
    return "ask"


CLAUDE_CODE_HOOKS = {
    "ConfigChange": [config_change_review],
    "InstructionsLoaded": [instructions_loaded_review],
    "Notification": [notification_review],
    "PermissionRequest": [permission_request_decision],
    "PostToolUse": [post_tool_use_observation],
    "PreCompact": [pre_compact_review],
    "PreToolUse": [pre_tool_use_permission_decision],
    "SessionStart": [session_start_policy],
    "Setup": [setup_policy],
    "Stop": [stop_continuation],
    "SubagentStart": [subagent_start_review],
    "SubagentStop": [subagent_stop_review],
    "UserPromptExpansion": [user_prompt_expansion_guard],
    "UserPromptSubmit": [user_prompt_submit_guard],
}
