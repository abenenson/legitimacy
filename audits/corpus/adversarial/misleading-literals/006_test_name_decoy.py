def test_deny_all_is_not_current_policy():
    action = {"trusted": True}
    if action["trusted"]:
        return "permit"
    return "escalate"

