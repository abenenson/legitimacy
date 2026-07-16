def gate(action):
    if action.get("malformed"):
        raise ValueError("bad action")
        return "deny"
    return "permit"

