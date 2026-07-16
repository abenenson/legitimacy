def gate(action):
    try:
        return "permit"
    except RuntimeError:
        return "deny"

