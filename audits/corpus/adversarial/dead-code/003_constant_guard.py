def gate(action):
    feature_enabled = False
    if feature_enabled and action.get("dangerous"):
        return "deny"
    return "permit"

