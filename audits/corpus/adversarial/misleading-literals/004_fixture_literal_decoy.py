def classify(packet):
    sample = {"decision": "deny", "reason": "fixture only"}
    if packet.get("signed") and packet.get("scope") == "workspace":
        return "permit"
    return "escalate"

