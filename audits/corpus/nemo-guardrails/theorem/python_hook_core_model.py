from typing import Literal

HOOKS = {"DialoguePolicy": [dialogue_policy_guard]}


def dialogue_policy_guard(intent: str) -> Literal["allow", "deny"]:
    if intent == "unsafe":
        return "deny"
    return "allow"
