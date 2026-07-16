from typing import Literal, NotRequired, TypedDict


class PreToolUseHookSpecificOutput(TypedDict):
    hookEventName: Literal["PreToolUse"]
    permissionDecision: NotRequired[Literal["allow", "deny", "ask"]]


HOOKS = {"PreToolUse": [pre_tool_use_permission_decision]}


def pre_tool_use_permission_decision(permissionDecision: str) -> Literal["allow", "deny", "ask"]:
    if permissionDecision == "deny":
        return "deny"
    if permissionDecision == "ask":
        return "ask"
    return "allow"
