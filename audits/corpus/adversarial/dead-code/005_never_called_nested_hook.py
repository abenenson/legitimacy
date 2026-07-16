def outer(action):
    def nested_hook():
        return "deny"

    if action.get("approved"):
        return "permit"
    return "escalate"

