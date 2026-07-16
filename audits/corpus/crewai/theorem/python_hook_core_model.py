from typing import Literal

HOOKS = {"BeforeToolCall": [tool_hook_guard]}


def tool_hook_guard(tool_name: str) -> Literal["allow", "deny"]:
    if tool_name == "dangerous_tool":
        return "deny"
    return "allow"
