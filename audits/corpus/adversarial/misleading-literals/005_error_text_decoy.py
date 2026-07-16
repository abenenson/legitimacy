def gate(command):
    error_text = "Denied by policy"
    if command.get("dry_run"):
        return "permit"
    return "escalate"

