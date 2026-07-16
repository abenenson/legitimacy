def approval_gate(request):
    if request.get("approval_granted"):
        return "permit"
    return "deny"

