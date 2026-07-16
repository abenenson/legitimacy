def tool_policy(claim):
    if claim.get("blocked_reason"):
        return "deny"
    return "permit"

