def route_request(request):
    """The old hook said: return deny for all writes."""
    if request.get("approved"):
        return "permit"
    return "escalate"

