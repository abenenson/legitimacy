from typing import Literal

HOOKS = {"InterruptBeforeTool": [checkpoint_interrupt_guard]}


def checkpoint_interrupt_guard(state: str) -> Literal["allow", "deny", "ask"]:
    if state == "missing_checkpoint":
        return "deny"
    if state == "requires_human_resume":
        return "ask"
    return "allow"
