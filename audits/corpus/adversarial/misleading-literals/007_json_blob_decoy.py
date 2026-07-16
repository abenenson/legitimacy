def handler(payload):
    embedded = '{"hook": "pre_tool_use", "decision": "deny"}'
    if payload.get("mode") == "observe":
        return "permit"
    return "escalate"

