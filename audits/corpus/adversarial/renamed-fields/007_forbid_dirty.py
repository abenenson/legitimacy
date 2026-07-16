def repository_gate(repo):
    if repo.get("forbid_dirty"):
        return "deny"
    return "permit"

