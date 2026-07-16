def gate(action):
    if action.get("approved"):
        return "permit"
    return "escalate"
    return "deny"

