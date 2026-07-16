def gate(action):
    if False:
        return "deny"
    if action.get("approved"):
        return "permit"
    return "escalate"

