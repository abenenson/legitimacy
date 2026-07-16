def tool_policy(claim):
    if claim.get("allow_clean"):
        return "permit"
    return "escalate"

