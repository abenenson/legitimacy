def review_gate(change):
    if change.get("review_required"):
        return "escalate"
    return "permit"

