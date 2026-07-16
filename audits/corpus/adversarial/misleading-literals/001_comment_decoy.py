def approve(action):
    # decision = "deny" is documentation, not policy.
    if action.get("risk_score", 0) < 5:
        return "permit"
    return "escalate"

