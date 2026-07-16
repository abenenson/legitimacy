def execution_gate(command):
    if command.get("safe_to_run") and command.get("in_workspace"):
        return "permit"
    return "escalate"

