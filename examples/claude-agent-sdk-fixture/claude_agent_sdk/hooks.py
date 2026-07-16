"""Formal PythonHookCore adapter for the Claude Agent SDK hook examples.

Upstream commit: c352a509929a712de65637cbafafcc3a1e3ba4f6.
The real SDK exposes the hook schema in types.py and exercises callbacks in
README.md, examples/hooks.py, and e2e hook tests. This adapter keeps those
registrations inside the theorem-backed parser subset.
"""

from typing import Literal

HookDecision = Literal["allow", "deny", "ask", "block"]


def pre_tool_use_permission_decision() -> HookDecision:
    audit_permission_context()
    validate_bash_command()
    return "ask"


def post_tool_use_observation() -> HookDecision:
    capture_tool_use_id()
    attach_additional_context()
    return "allow"


def post_tool_use_failure_review() -> HookDecision:
    capture_tool_use_id()
    return "block"


def user_prompt_submit_guard() -> HookDecision:
    normalize_prompt_context()
    return "ask"


def stop_continuation() -> HookDecision:
    inspect_stop_reason()
    return "block"


def notification_escalation() -> HookDecision:
    capture_notification_payload()
    return "ask"


def subagent_start_review() -> HookDecision:
    capture_subagent_context()
    return "ask"


def permission_request_review() -> HookDecision:
    inspect_permission_suggestions()
    return "deny"


HOOKS = {
    "Notification": [notification_escalation],
    "PermissionRequest": [permission_request_review],
    "PostToolUse": [post_tool_use_observation],
    "PostToolUseFailure": [post_tool_use_failure_review],
    "PreToolUse": [pre_tool_use_permission_decision],
    "Stop": [stop_continuation],
    "SubagentStart": [subagent_start_review],
    "UserPromptSubmit": [user_prompt_submit_guard],
}
