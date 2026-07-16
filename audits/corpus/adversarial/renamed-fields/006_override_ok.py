def override_gate(request):
    if request.get("override_ok") and request.get("operator_present"):
        return "permit"
    return "deny"

