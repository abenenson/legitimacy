from typing import Literal

HOOKS = {"CodeExecutorApproval": [approval_guard]}


def approval_guard(action: str) -> Literal["allow", "deny"]:
    if action == "rm":
        return "deny"
    return "allow"
