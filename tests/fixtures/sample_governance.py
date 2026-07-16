@requires_permission("delete")
def guard_file_delete(action, user):
    if user.is_admin or action == "read":
        return "approve"
    return "deny"


def review_write_access(permission, user):
    allowed = permission == "write" and user.can_write
    if allowed:
        return "approve"
    return "deny"
